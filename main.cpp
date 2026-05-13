#include <Arduino.h>
#include <WiFi.h>
#include <DNSServer.h>
#include <ESPAsyncWebServer.h>
#include <Preferences.h>
#include <math.h>
#include <Wire.h>
#include <RTClib.h> 

// ==========================================
// 1. PINOUT (SuperMini C3 Final v23)
// ==========================================
/*
const int VCC_MON = 0;
const int PWR_PIN = 1;       
const int TH1_PIN = 3;
const int TH2_PIN = 4;
const int QRD_SENS_PIN = 2;
const int FAN1_PWM_PIN = 6;
const int FAN2_PWM_PIN = 7;
const int FAN1_TACHO_PIN = 5;
const int FAN2_TACHO_PIN = 20;
const int RTC_SDA_PIN = 8;
const int RTC_SCL_PIN = 9;
const int LED_DIM_PIN = 21;
*/
const int PWR_PIN = 0;
const int VCC_MON = 1;  
const int QRD_SENS_PIN = 2;
const int TH1_PIN = 3;
const int TH2_PIN = 4;
const int LED_DIM_PIN = 5;
const int FAN2_PWM_PIN = 6;
const int FAN1_PWM_PIN = 7;
const int RTC_SDA_PIN = 8;
const int RTC_SCL_PIN = 9;
const int FAN2_TACHO_PIN = 20;
const int FAN1_TACHO_PIN = 21;
// 2. SYSTEM PARAMETERS
// ==========================================
// Thermistor: Standard 10k NTC / Beta 3950
const float R_FIXED = 10000.0;
const float B_COEFF = 3950.0; 
const float T0_KELVIN = 298.15;
const float R0 = 10000.0;

// Safety Defaults
const float MAX_TEMP_DIFF = 8.0;   
const float BALANCING_START_DIFF = 2.0;
const float SENSOR_MIN_T = -10.0;
const float SENSOR_MAX_T = 90.0;   
const int RPM_TOLERANCE = 20;
const int SAFE_DEFAULT_PWM = 51; // ~20% (Fallback for uncalibrated fans)

// QRD & Timings
const int QRD_THRESH_TRIGGER = 500; 
const int QRD_THRESH_RELEASE = 300;
const unsigned long LONG_PRESS_TIME = 500;
const unsigned long STEP_TIME = 50;
const unsigned long MULTI_TAP_TIMEOUT = 250;

// PWM Config
const int FAN_PWM_FREQ = 25000;
const int FAN_PWM_RES = 8;
const int FAN_CHAN1 = 0;
const int FAN_CHAN2 = 1;
const int LED_PWM_FREQ = 2000;
const int LED_PWM_RES = 8;
const int LED_CHAN = 2;
const float LED_GAMMA = 2.8;

// ==========================================
// 3. DATA STRUCTURES
// ==========================================
struct SchedProfile {
    char name[16];
    uint8_t daysMask;
    uint8_t wakeHour; uint8_t wakeMin; uint8_t dawnDur;    
    uint8_t sleepHour; uint8_t sleepMin; uint8_t duskDur;    
    uint8_t maxBri; bool active;        
};
enum SchedPhase { PHASE_UNKNOWN, PHASE_NIGHT, PHASE_DAWN, PHASE_DAY, PHASE_DUSK };

// ==========================================
// 4. GLOBALS
// ==========================================
AsyncWebServer server(80);
DNSServer dnsServer;
Preferences preferences;
RTC_DS3231 rtc;

// Measurements
float temp1_C = 0; float temp2_C = 0; float actualVCC_mV = 0;

// Fan State
int pwm1 = 0; int pwm2 = 0;
int rpm1 = 0; int rpm2 = 0;
int pwm1_target = 0; int pwm2_target = 0;
float pwm1_current = 0; float pwm2_current = 0;

// System Status
String safetyStatus = "OK";
String lastSafetyStatus = "OK"; 
bool safetyCoolingActive = false;
int maxAllowedBrightness = 255;
bool criticalError = false;
unsigned long fan1WearTimer = 0; unsigned long fan2WearTimer = 0;

// Configuration (Loaded from NVM)
float fanTempStart = 30.0; 
float fanTempMax = 55.0;     // Target Max Temp
float fanBalanceFactor = 5.0;
// Note: fanMinPwm removed. We derive it from calibration.
bool manualMode = false;
int manualSpeed1 = 0;
int manualSpeed2 = 0;
int ledActiveThresholdPct = 5; // Night Mode Threshold (0-15%)

// LED State
int ledBrightnessTarget = 255;
float ledBrightnessCurrent = 255.0;
int ledBrightness = 255;
int duskCeilingBrightness = -1; 
int ledMinPct = 10;
int ledMinPwm = 25;
bool ledAutoMode = true; 
SchedProfile profiles[4];
SchedPhase currentPhase = PHASE_UNKNOWN; 

// Timing & Flags
float timeGmt = 1.0;
bool timeDst = false;
String currentTimeStr = "--:--:--";
int currentDayOfWeek = 0; bool rtcPresent = false;
bool ledSettingsChanged = false;
unsigned long lastLedChangeTime = 0;
bool instantRampAction = false;
int qrdDelta = 0; bool isTouched = false;
unsigned long touchStartTime = 0;
unsigned long lastHoldStepTime = 0;
bool holdModeActive = false;
int lastOnBrightness = 255;
int consecutiveTaps = 0;
unsigned long lastTapReleaseTime = 0;
bool dimmingUp = false;

// Tacho & Calib
volatile int tachPulses1 = 0;
volatile int tachPulses2 = 0;
volatile unsigned long lastPulseTime1 = 0;
volatile unsigned long lastPulseTime2 = 0;
unsigned long lastRPMCalcTime = 0;
portMUX_TYPE timerMux = portMUX_INITIALIZER_UNLOCKED;

bool isCalibrating = false;
int calibStep = 0;
unsigned long calibStepStartTime = 0;
const int CALIB_POINTS_COUNT = 21;
// PWM Points: 0, 13, 25... 255
const int CALIB_POINTS[21] = {0, 13, 25, 38, 51, 64, 76, 89, 102, 115, 128, 140, 153, 166, 179, 191, 204, 217, 230, 242, 255};
int fan1Profile[21] = {0};
int fan2Profile[21] = {0};
String cachedMapJson = "";

// ==========================================
// 5. INTERRUPTS
// ==========================================
void IRAM_ATTR isrFan1() {
    unsigned long now = micros();
    if (now - lastPulseTime1 > 2000) { // 2ms filter
        portENTER_CRITICAL_ISR(&timerMux);
        tachPulses1++;
        portEXIT_CRITICAL_ISR(&timerMux);
        lastPulseTime1 = now;
    }
}
void IRAM_ATTR isrFan2() {
    unsigned long now = micros();
    if (now - lastPulseTime2 > 2000) {
        portENTER_CRITICAL_ISR(&timerMux);
        tachPulses2++;
        portEXIT_CRITICAL_ISR(&timerMux);
        lastPulseTime2 = now;
    }
}
void WiFiEvent(WiFiEvent_t event) {}

// ==========================================
// 6. HTML PAGE
// ==========================================
const char index_html[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html lang="pl">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Smart Lamp Control v23</title>
    <style>
        body { font-family: sans-serif; background: #121212; color: #eee; text-align: center; margin: 0; padding: 10px; }
        .grid { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; max-width: 600px; margin: 0 auto; }
        .card { background: #1e1e1e; padding: 10px; border-radius: 8px; border: 1px solid #333; }
        .full-width { grid-column: span 2; }
        .temp-val { font-size: 28px; font-weight: bold; margin: 5px 0; }
        .rpm-val { font-size: 14px; font-weight: bold; color: #4caf50; display: block; margin-top: 4px; }
        .ch1 { border-top: 3px solid #ff9800; }
        .ch2 { border-top: 3px solid #2196f3; }
        input[type=range] { width: 100%; height: 20px; background: #444; outline: none; -webkit-appearance: none; border-radius: 5px; }
        input[type=range]::-webkit-slider-thumb { -webkit-appearance: none; width: 25px; height: 25px; background: #2196f3; border-radius: 50%; cursor: pointer; }
        input[type=range].led-slider::-webkit-slider-thumb { background: #ffeb3b; }
        .slider-label { display: flex; justify-content: space-between; font-size: 14px; margin-bottom: 5px; }
        button { background: #3f51b5; color: white; border: none; padding: 12px; border-radius: 4px; cursor: pointer; width: 100%; font-size: 16px; margin-top: 5px; }
        button.danger { background: #e91e63; color: white; margin-top: 10px; }
        .btn-green { background: #4caf50; color: white; }
        .btn-grey { background: #555; color: #ccc; }
        .disabled { opacity: 0.8; pointer-events: none; filter: grayscale(30%); }
        .status-bar { padding: 10px; margin-bottom: 10px; font-weight: bold; border-radius: 4px; display: none; }
        .status-ok { background: #4caf50; color: white; }
        .status-warn { background: #ff9800; color: white; }
        .status-err { background: #d32f2f; color: white; animation: blink 1s infinite; }
        .clock-display { font-size: 24px; font-weight: bold; color: #03a9f4; margin-bottom: 10px; display: block; text-align: center;}
        .table-scroll { overflow-x: auto; margin-top: 10px; }
        table { width: 100%; border-collapse: collapse; font-size: 12px; color: #aaa; white-space: nowrap; }
        th, td { border: 1px solid #444; padding: 4px; text-align: center; }
        th { background: #333; }
        .calib-progress { width: 100%; height: 5px; background: #333; margin-top: 5px; }
        .calib-bar { height: 100%; background: #e91e63; width: 0%; transition: width 0.5s; }
        .sched-item { background: #2a2a2a; border: 1px solid #444; padding: 10px; margin-bottom: 8px; border-radius: 4px; text-align: left; }
        .sched-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 5px; }
        .sched-name { font-weight: bold; color: #ffeb3b; }
        .sched-days span { display: inline-block; width: 20px; height: 20px; line-height: 20px; text-align: center; font-size: 10px; background: #333; border-radius: 50%; margin-right: 2px; color: #777; }
        .sched-days span.active { background: #4caf50; color: #fff; }
        .sched-details { font-size: 12px; color: #bbb; display: flex; flex-wrap: wrap; gap: 8px; }
        .edit-form { display: none; background: #333; padding: 10px; margin-top: 5px; border-radius: 4px; }
        .form-row { display: flex; justify-content: space-between; align-items: center; margin-bottom: 5px; font-size: 12px; }
        .form-row input { background: #222; border: 1px solid #555; color: #fff; padding: 3px; border-radius: 3px; }
        .day-select input { display: none; }
        .day-select label { display: inline-block; width: 25px; height: 25px; line-height: 25px; text-align: center; background: #444; border-radius: 50%; cursor: pointer; font-size: 11px; margin: 1px;}
        .day-select input:checked + label { background: #4caf50; color: #fff; }
        .param-label { font-size: 12px; color: #aaa; display:block; margin-bottom: 2px; }
        .param-input { width: 60px; background: #333; border: 1px solid #555; color: #fff; padding: 5px; text-align: center; border-radius: 4px; }
        .chart-container { width: 100%; height: 120px; background: #111; border: 1px solid #333; margin-top: 5px; position:relative; }
        svg { width: 100%; height: 100%; display: block; }
        .chart-path { fill: rgba(255, 235, 59, 0.2); stroke: #ffeb3b; stroke-width: 1.5; vector-effect: non-scaling-stroke; }
        .chart-now { stroke: #03a9f4; stroke-width: 1; stroke-dasharray: 4; vector-effect: non-scaling-stroke; opacity: 0.8; }
        .chart-labels { display: flex; justify-content: space-between; font-size: 10px; color: #666; margin-top: 2px; padding: 0 5px; }
        .day-btn-row { display: flex; justify-content: center; gap: 5px; margin-bottom: 10px; }
        .day-btn { width: 30px; height: 30px; border: 1px solid #444; background: #222; color: #777; border-radius: 50%; font-size: 11px; cursor: pointer; padding: 0; }
        .day-btn.active { background: #2196f3; color: white; border-color: #2196f3; }
        .chart-peak-label { font-size: 12px; fill: #fff; font-weight: bold; text-anchor: middle; }
        @keyframes blink { 50% { opacity: 0.7; } }
        .prox-bar-bg { width: 100%; height: 8px; background: #333; border-radius: 4px; margin-top: 5px; overflow: hidden; }
        .prox-bar { height: 100%; background: #e91e63; width: 0%; transition: width 0.1s; }
        .prox-dot { height: 10px; width: 10px; background-color: #333; border-radius: 50%; display: inline-block; margin-right: 5px; }
        .prox-active { background-color: #e91e63; box-shadow: 0 0 8px #e91e63; }
    </style>
</head>
<body>
    <div id="status-display" class="status-bar">SYSTEM OK</div>
    <div class="grid">
        <div class="card full-width" style="border-top: 3px solid #ffeb3b;">
            <div class="slider-container">
                <div class="slider-label">
                    <span style="color:#ffeb3b; font-weight:bold;">JASNOŚĆ LED</span>
                    <div><span id="prox-ind" class="prox-dot"></span> <span id="led-txt">100%</span></div>
                </div>
                <button id="btn-led-auto" onclick="setLedAuto()" class="btn-green" style="display:none; margin-bottom:10px; font-size:12px; padding:5px;">PRZYWRÓĆ HARMONOGRAM (AUTO)</button>
                <input type="range" min="0" max="255" id="sl-led" class="led-slider"
                       oninput="onSlideLed()" onchange="sendLed()"
                       ontouchstart="dragStart()" ontouchend="dragEnd()" onmousedown="dragStart()" onmouseup="dragEnd()">
            </div>
        </div>

        <div class="card full-width" style="text-align:center;">
             <span id="clock" class="clock-display">--:--:--</span>
             <button onclick="syncTime()" style="padding:10px; font-size:14px; background:#333;">SYNCHRONIZUJ CZAS (TELEFON)</button>
             <div style="margin-top:10px; display:flex; justify-content:center; align-items:center; gap:10px; font-size:14px; color:#aaa;">
                <span>GMT:</span><input id="cfg_gmt" type="number" step="0.5" class="param-input" style="width:50px">
                <span>DST:</span><input id="cfg_dst" type="checkbox">
             </div>
        </div>

        <div class="card ch1">
            <div>TEMP 1</div>
            <div class="temp-val" id="t1">--</div>
            <span class="rpm-val" id="r1">-- RPM</span>
        </div>
        <div class="card ch2">
            <div>TEMP 2</div>
            <div class="temp-val" id="t2">--</div>
            <span class="rpm-val" id="r2">-- RPM</span>
        </div>

        <div class="card full-width" style="border-top: 3px solid #e91e63;">
             <div style="display:flex; justify-content:space-between; font-size:12px; color:#aaa;">
                <span>ZBLIŻENIE</span>
                <span id="prox-val">0</span>
            </div>
            <div class="prox-bar-bg"><div id="prox-bar" class="prox-bar"></div></div>
        </div>
        
        <div class="card full-width" style="border-top: 3px solid #03a9f4;">
             <div style="font-weight:bold; color:#03a9f4; margin-bottom:10px;">HARMONOGRAM (ROŚLINY / BUDZIK)</div>
             <div id="sched-list">Loading...</div>
        </div>

        <div class="card full-width" style="border-top: 3px solid #4caf50;">
            <div style="font-weight:bold; color:#4caf50; margin-bottom:10px;">SYMULACJA DNIA (1 min rozdz.)</div>
            <div class="day-btn-row" id="day-btns"></div>
            <div class="chart-container" id="chart-ctn">
                <svg id="svg-chart" viewBox="0 0 1440 100" preserveAspectRatio="none">
                    <path id="chart-path" class="chart-path" d="" />
                    <line id="chart-now" class="chart-now" x1="0" y1="0" x2="0" y2="100" style="display:none" />
                    <text id="chart-label" x="720" y="50" class="chart-peak-label"></text>
                </svg>
            </div>
            <div class="chart-labels">
                <span>00:00</span><span>06:00</span><span>12:00</span><span>18:00</span><span>24:00</span>
            </div>
        </div>

        <div class="card full-width" style="background:#252525; text-align:left;">
            <button id="btn-mode" onclick="toggleMode()">TRYB WENTYLATORA: AUTO</button>
            <div id="panel-manual" class="disabled">
                <div class="slider-container">
                    <div class="slider-label"><span>FAN 1</span><span id="sl1-txt">0%</span></div>
                    <input type="range" min="0" max="255" id="sl1" oninput="onSlide('sl1')" onchange="sendData()" ontouchstart="dragStart()" ontouchend="dragEnd()" onmousedown="dragStart()" onmouseup="dragEnd()">
                </div>
                <div class="slider-container">
                    <div class="slider-label"><span>FAN 2</span><span id="sl2-txt">0%</span></div>
                    <input type="range" min="0" max="255" id="sl2" oninput="onSlide('sl2')" onchange="sendData()" ontouchstart="dragStart()" ontouchend="dragEnd()" onmousedown="dragStart()" onmouseup="dragEnd()">
                </div>
            </div>
            
            <div id="panel-auto">
                <div style="margin-top:10px; font-size:14px; border-top:1px solid #444; padding-top:10px;">
                    Ustawienia Auto (Wentylatory):<br>
                    <form action="/save_auto" method="GET" style="display:flex; flex-direction: column; gap:15px; margin-top:10px;">
                        <div>
                            <span class="param-label">KRZYWA BAZOWA:</span>
                            <div style="display:flex; justify-content:space-between;">
                                <div><label class="param-label">Start [°C]</label><input type="number" name="t0" id="in_t0" class="param-input"></div>
                                <div><label class="param-label">Max [°C]</label><input type="number" name="tx" id="in_tx" class="param-input"></div>
                            </div>
                        </div>
                        
                        <div style="border-top:1px dashed #444; padding-top:5px;">
                            <span class="param-label" style="color:#2196f3">TRYB PASYWNY (NOC):</span>
                            <div style="display:flex; justify-content:space-between; align-items:center;">
                                <label class="param-label">Fan OFF poniżej LED [%]:</label>
                                <input type="number" name="lact" id="in_lact" class="param-input" min="0" max="15">
                            </div>
                        </div>

                        <div>
                            <span class="param-label">BALANSOWANIE T1 vs T2:</span>
                            <div style="display:flex; justify-content:space-between; align-items:flex-end;">
                                <div><label class="param-label">Korekta [%/°C]</label><input type="number" name="bf" id="in_bf" class="param-input" step="0.1"></div>
                                <input type="submit" value="ZAPISZ" class="btn-green" style="width:60px; padding:5px; font-size:11px;">
                            </div>
                        </div>
                    </form>
                    <hr style="border:0; border-top:1px solid #444; margin:10px 0;">
                    Ustawienia LED Hardware:<br>
                    <form action="/save_led_hw" method="GET" style="display:flex; justify-content:space-between; align-items:center; gap:10px; margin-top:5px;">
                        <div style="display:flex; align-items:center; gap:10px;">
                            <label class="param-label" style="font-size:13px;">Min LED PWM [%]:</label>
                            <input type="number" name="min_l" id="in_min_l" class="param-input" min="0" max="50">
                        </div>
                        <input type="submit" value="ZAPISZ" class="btn-green" style="width:60px; padding:5px; font-size:11px;">
                    </form>
                </div>
            </div>

            <div style="margin-top:20px; border-top:1px solid #444; padding-top:10px;">
                <div style="font-size:14px; font-weight:bold; color:#aaa;">ADVANCED SETUP</div>
                <button class="danger" id="btn-cal" onclick="startCalib()">WYCECHUJ WENTYLATORY (~3.5min)</button>
                <div id="cal-status" style="display:none; margin-top:5px; font-size:12px; color:#ff9800;">Trwa kalibracja...</div>
                <div class="calib-progress"><div id="cal-bar" class="calib-bar"></div></div>
                <div class="table-scroll"><table id="cal-table"></table></div>

                <div style="margin-top:20px; border-top:1px solid #444; padding-top:10px;">
                    <div style="font-size:14px; font-weight:bold; color:#e91e63;">BEZPIECZEŃSTWO WI-FI</div>
                    <form action="/save_wifi_pass" method="GET" style="display:flex; flex-direction:column; gap:5px; margin-top:5px;">
                        <label class="param-label">Hasło (min 8 znaków, puste=otwarta):</label>
                        <div style="display:flex; justify-content:space-between;">
                            <input type="text" name="pass" class="param-input" style="width:100%; margin-right:5px; text-align:left;">
                            <input type="submit" value="ZAPISZ" class="btn-green" style="width:60px; padding:5px; font-size:11px;">
                        </div>
                        <span style="font-size:10px; color:#777;">Zmiana wymaga restartu. Awaryjny reset: Włącz zasilanie trzymając palec na czujniku.</span>
                    </form>
                </div>

                <div style="margin-top:15px; font-size:14px; font-weight:bold; color:#aaa;">HISTORIA ZDARZEŃ</div>
                <button onclick="fetchLogs()" style="margin-top:5px; background:#444;">ODŚWIEŻ LOGI</button>
                <div class="table-scroll"><table id="log-table" style="text-align:left;"><tr><th>Time</th><th>Event</th><th>Parametry</th></tr></table></div>
                <button id="btn-clear-logs" class="danger" onclick="clearLogs()" style="display:none; margin-top:5px; background:#d32f2f;">SKASUJ WSZYSTKIE LOGI</button>
            </div>
            <div style="margin-top:10px; font-size:11px; color:#666">VCC: <span id="vcc">--</span> mV</div>
        </div>
    </div>

<script>
    let isManual = false; 
    let isDragging = false;
    let profiles = [];
    const dayNames = ['Nd','Pn','Wt','Śr','Cz','Pt','So'];
    let selectedChartDay = new Date().getDay(); 

    function dragStart() { isDragging = true; }
    function dragEnd() { isDragging = false; }

    function onSlideLed() { document.getElementById('led-txt').innerText = Math.round((document.getElementById('sl-led').value/255)*100) + '%'; }
    function sendLed() { 
        fetch('/set_led?v=' + document.getElementById('sl-led').value); 
        document.getElementById('btn-led-auto').style.display = 'block';
    }
    function setLedAuto() {
        fetch('/set_led_mode?auto=1').then(()=>{
            document.getElementById('btn-led-auto').style.display = 'none';
        });
    }
    function onSlide(id) { document.getElementById(id + '-txt').innerText = Math.round((document.getElementById(id).value/255)*100) + '%'; }
    function sendData() { fetch('/set_manual?f1=' + document.getElementById('sl1').value + '&f2=' + document.getElementById('sl2').value); }
    function toggleMode() { fetch('/set_mode?m=' + (isManual ? '0' : '1')).then(()=>fetchData()); }
    function startCalib() { fetch('/start_calib'); }
    function syncTime() {
        const d = new Date(); const ts = Math.floor(d.getTime() / 1000);
        const g = document.getElementById('cfg_gmt').value;
        const dst = document.getElementById('cfg_dst').checked ? 1 : 0;
        fetch('/save_time_cfg?gmt=' + g + '&dst=' + dst).then(() => {
            fetch('/set_time?ts=' + ts).then(r => alert("Zsynchronizowano!"));
        });
    }
    // --- FIXED: LOG PARSER (Handles Space Separator & Shows Clear Button) ---
    function fetchLogs() { 
        fetch('/get_logs')
        .then(r => r.json())
        .then(d => { 
            const t = document.getElementById('log-table'); 
            while(t.rows.length > 1) t.deleteRow(1); 
            d.logs.forEach(l => {
                const p = l.split(',');
                if(p.length >= 8) {
                    const r = t.insertRow();
                    r.insertCell(0).innerHTML = p[0].replace(' ', '<br>'); 
                    r.insertCell(1).innerText = p[1];
                    r.insertCell(2).innerHTML = 'T:'+p[2]+'/'+p[3]+'<br>P:'+p[4]+'/'+p[5]+'<br>R:'+p[6]+'/'+p[7]+'<br>V:'+p[8];
                }
            });
            if(d.logs.length > 0) document.getElementById('btn-clear-logs').style.display = 'block';
        })
        .catch(e => alert("Log Error: " + e)); 
    }
    function clearLogs() {
        if(confirm("Czy na pewno usunąć historię?")) {
            fetch('/clear_logs').then(()=>{
                alert("Logi usunięte.");
                const t = document.getElementById('log-table');
                while(t.rows.length > 1) t.deleteRow(1);
                document.getElementById('btn-clear-logs').style.display = 'none';
            });
        }
    }
    function renderCalibTable(m) { const t=document.getElementById('cal-table');t.innerHTML="";let h=t.insertRow();h.insertCell().outerHTML="<th>PWM</th>";for(let i=0;i<=20;i++)h.insertCell().outerHTML="<th>"+(i*5)+"%</th>";if(m&&m.f1.length==21){let r1=t.insertRow();r1.insertCell().innerText="F1";m.f1.forEach(v=>r1.insertCell().innerText=v);let r2=t.insertRow();r2.insertCell().innerText="F2";m.f2.forEach(v=>r2.insertCell().innerText=v);} }
    function fetchSchedules() { fetch('/get_schedules').then(r=>r.json()).then(d => { profiles = d.profs; renderSchedules(); renderDayButtons(); renderChartSVG(); }); }
    function renderSchedules() {
        const c = document.getElementById('sched-list'); c.innerHTML = "";
        profiles.forEach((p, idx) => {
            let daysHtml = "";
            for(let i=1; i<7; i++) daysHtml += `<span class="${(p.dm & (1<<i))?'active':''}">${dayNames[i]}</span>`;
            daysHtml += `<span class="${(p.dm & 1)?'active':''}">${dayNames[0]}</span>`; 
            const item = document.createElement('div'); item.className = 'sched-item';
            item.innerHTML = `
                <div class="sched-header"><span class="sched-name">${p.name}</span><button class="mini-btn btn-grey" onclick="toggleEdit(${idx})" style="width:auto; padding:2px 8px;">EDYTUJ</button></div>
                <div class="sched-days" style="margin-bottom:5px;">${daysHtml}</div>
                <div class="sched-details"><div>☀ Budzik: <b>${p.wh}:${p.wm<10?'0'+p.wm:p.wm}</b> (+${p.dd}min świt)</div><div>☾ Sen: <b>${p.sh}:${p.sm<10?'0'+p.sm:p.sm}</b> (-${p.kd}min zmierzch)</div><div>Max: <b>${Math.round(p.mb/2.55)}%</b></div></div>
                <div id="edit-${idx}" class="edit-form">
                    <div class="form-row">Nazwa: <input type="text" id="n-${idx}" value="${p.name}" maxlength="10" style="width:80px"></div>
                    <div class="form-row day-select">Dni: ${[1,2,3,4,5,6,0].map(d => `<input type="checkbox" id="d-${idx}-${d}" ${(p.dm&(1<<d))?'checked':''}><label for="d-${idx}-${d}">${dayNames[d]}</label>`).join('')}</div>
                    <div class="form-row">Budzik (ON max): <input type="time" id="wt-${idx}" value="${p.wh<10?'0'+p.wh:p.wh}:${p.wm<10?'0'+p.wm:p.wm}"></div>
                    <div class="form-row">Czas Świtu [min]: <input type="number" id="dd-${idx}" value="${p.dd}" style="width:50px"></div>
                    <div class="form-row">Sen (OFF): <input type="time" id="st-${idx}" value="${p.sh<10?'0'+p.sh:p.sh}:${p.sm<10?'0'+p.sm:p.sm}"></div>
                    <div class="form-row">Czas Zmierzchu [min]: <input type="number" id="kd-${idx}" value="${p.kd}" style="width:50px"></div>
                    <div class="form-row">Max Jasność [%]: <input type="number" id="mb-${idx}" min="0" max="100" value="${Math.round(p.mb/2.55)}" style="width:50px"></div>
                    <div style="text-align:right; margin-top:5px;"><button class="btn-green" onclick="saveProfile(${idx})" style="width:60px; padding:5px; font-size:11px;">ZAPISZ</button></div>
                </div>`;
            c.appendChild(item);
        });
    }
    function renderDayButtons() {
        const c = document.getElementById('day-btns'); if(c.innerHTML !== "") return; 
        let html = "";
        for(let i=1; i<7; i++) html += `<button class="day-btn ${i===selectedChartDay?'active':''}" onclick="selChartDay(${i})">${dayNames[i]}</button>`;
        html += `<button class="day-btn ${0===selectedChartDay?'active':''}" onclick="selChartDay(0)">${dayNames[0]}</button>`;
        c.innerHTML = html;
    }
    function selChartDay(d) { selectedChartDay = d; const c = document.getElementById('day-btns'); c.innerHTML = ""; let html = ""; for(let i=1; i<7; i++) html += `<button class="day-btn ${i===selectedChartDay?'active':''}" onclick="selChartDay(${i})">${dayNames[i]}</button>`; html += `<button class="day-btn ${0===selectedChartDay?'active':''}" onclick="selChartDay(0)">${dayNames[0]}</button>`; c.innerHTML = html; renderChartSVG(); }
    function renderChartSVG() {
        let pathStr = "M 0 100 "; let peakVal = 0; let peakX = 0;
        for(let i=0; i<1440; i++) {
            let maxVal = 0;
            profiles.forEach(p => {
                if((p.dm & (1 << selectedChartDay)) && p.dm !== 0) {
                    let wake = p.wh*60 + p.wm; let sleep = p.sh*60 + p.sm; let dawnS = wake - p.dd; let duskS = sleep - p.kd; let val = 0;
                    if(i < dawnS) val = 0; 
                    else if(i < wake) { let prog = (i - dawnS) / p.dd; val = Math.pow(prog, 2.8) * p.mb; } 
                    else if(i < duskS) { val = p.mb; } else if(i < sleep) { let prog = (i - duskS) / p.kd; val = Math.pow(1.0 - prog, 2.8) * p.mb; } else { val = 0; }
                    if(val > maxVal) maxVal = val;
                }
            });
            maxVal = Math.min(255, Math.max(0, maxVal)); if(maxVal > peakVal) { peakVal = maxVal; peakX = i; } 
            let y = 100 - (maxVal / 2.55); pathStr += `L ${i} ${y} `;
        }
        pathStr += "L 1440 100 Z";
        document.getElementById('chart-path').setAttribute('d', pathStr);
        const lbl = document.getElementById('chart-label');
        if(peakVal > 0) { lbl.setAttribute('x', peakX); lbl.setAttribute('y', 100 - (peakVal/2.55) - 5); lbl.textContent = "Max: " + Math.round(peakVal/2.55) + "%"; if(peakX < 100) lbl.setAttribute('x', 100); if(peakX > 1340) lbl.setAttribute('x', 1340); } else { lbl.textContent = ""; }
    }
    function toggleEdit(id) { const el = document.getElementById('edit-'+id); el.style.display = el.style.display === 'block' ? 'none' : 'block'; }
    function saveProfile(id) {
        const n = document.getElementById('n-'+id).value;
        const wtStr = document.getElementById('wt-'+id).value; const stStr = document.getElementById('st-'+id).value;
        let wt = wtStr.split(':'); let st = stStr.split(':');
        let startMin = parseInt(wt[0])*60 + parseInt(wt[1]); let endMin = parseInt(st[0])*60 + parseInt(st[1]);
        if(endMin <= startMin) { endMin = startMin + 1; let h = Math.floor(endMin/60); let m = endMin%60; if(h >= 24) h = 23; if(m > 59) m = 59; let newTime = (h<10?'0':'')+h + ':' + (m<10?'0':'')+m; document.getElementById('st-'+id).value = newTime; st = [h, m]; alert("Korekta: Czas OFF musi być później niż ON. Ustawiono +1 min."); }
        const ddVal = parseInt(document.getElementById('dd-'+id).value); if(ddVal < 0 || ddVal > 720) { alert("Błąd: Czas świtu musi być 0-720 min"); return; }
        const kdVal = parseInt(document.getElementById('kd-'+id).value); if(kdVal < 0 || kdVal > 720) { alert("Błąd: Czas zmierzchu musi być 0-720 min"); return; }
        let mbValStr = document.getElementById('mb-'+id).value; let mbVal = parseInt(mbValStr); if(isNaN(mbVal)) mbVal = 100; if(mbVal < 0 || mbVal > 100) { alert("Błąd: Jasność musi być 0-100%"); return; }
        const mb = Math.round(mbVal * 2.55); let mask = 0;
        for(let i=0; i<7; i++) { if(document.getElementById(`d-${id}-${i}`).checked) mask |= (1<<i); }
        const url = `/save_profile?id=${id}&n=${encodeURIComponent(n)}&dm=${mask}&wh=${wt[0]}&wm=${wt[1]}&dd=${ddVal}&sh=${st[0]}&sm=${st[1]}&kd=${kdVal}&mb=${mb}`;
        fetch(url).then(r=>r.text()).then(res => { fetchSchedules(); });
    }

    function scheduleNextFetch() { fetchData(); }
    
    function fetchData() {
        fetch('/data')
        .then(r => r.json())
        .then(d => {
            document.getElementById('t1').innerText = d.t1.toFixed(1) + '°'; document.getElementById('t2').innerText = d.t2.toFixed(1) + '°';
            document.getElementById('r1').innerText = d.rpm1 + ' RPM'; document.getElementById('r2').innerText = d.rpm2 + ' RPM'; document.getElementById('vcc').innerText = Math.round(d.vcc);
            document.getElementById('prox-val').innerText = d.prx;
            if(d.day !== undefined) {
                 document.getElementById('clock').innerText = dayNames[d.day] + " " + d.time;
                 const parts = d.time.split(':'); if(parts.length >= 2) { const h = parseInt(parts[0]); const m = parseInt(parts[1]); const currentMin = h * 60 + m; const line = document.getElementById('chart-now'); if(line) { if(d.day == selectedChartDay) { line.style.display = 'block'; line.setAttribute('x1', currentMin); line.setAttribute('x2', currentMin); } else { line.style.display = 'none'; } } }
            } else { document.getElementById('clock').innerText = d.time; }
            document.getElementById('prox-bar').style.width = Math.min(100,(d.prx/3000)*100)+'%';
            if(d.tch) document.getElementById('prox-ind').classList.add('prox-active'); else document.getElementById('prox-ind').classList.remove('prox-active');
            const sBar = document.getElementById('status-display'); sBar.innerText = "STATUS: " + d.stat; sBar.className = "status-bar"; sBar.style.display = 'block'; if(d.stat==="OK"||d.stat==="BALANCING") sBar.classList.add('status-ok'); else if(d.stat.includes("WARN")||d.stat.includes("IMBALANCE")) sBar.classList.add('status-warn'); else sBar.classList.add('status-err');
            if(d.cal){ document.getElementById('cal-status').style.display='block'; document.getElementById('cal-status').innerText="Kalibracja: "+(d.cstp+1)+"/21"; document.getElementById('cal-bar').style.width=((d.cstp/20)*100)+'%'; document.getElementById('btn-cal').disabled=true; } else { document.getElementById('cal-status').style.display='none'; document.getElementById('cal-bar').style.width='0%'; document.getElementById('btn-cal').disabled=false; }
            if(d.cmap) renderCalibTable(d.cmap);
            if(!isDragging) { 
                document.getElementById('sl-led').value = d.led; 
                document.getElementById('led-txt').innerText = Math.round(d.led/2.55) + '%'; 
                document.getElementById('sl1').value = d.pwm1; document.getElementById('sl1-txt').innerText = Math.round((d.pwm1/255)*100) + '%'; 
                document.getElementById('sl2').value = d.pwm2; document.getElementById('sl2-txt').innerText = Math.round((d.pwm2/255)*100) + '%'; 
            }
            if(d.lauto) document.getElementById('btn-led-auto').style.display = 'none'; else document.getElementById('btn-led-auto').style.display = 'block';
            isManual = d.man; const btn = document.getElementById('btn-mode'); const pMan = document.getElementById('panel-manual'); const pAuto = document.getElementById('panel-auto');
            if(isManual) { btn.innerText = "TRYB: RĘCZNY"; btn.className = "manual"; pMan.classList.remove('disabled'); pAuto.classList.add('disabled'); } else { btn.innerText = "TRYB: AUTO"; btn.className = ""; pMan.classList.add('disabled'); pAuto.classList.remove('disabled'); }
            if(document.activeElement.tagName !== 'INPUT') { 
                document.getElementById('cfg_gmt').value = d.gmt;
                document.getElementById('cfg_dst').checked = d.dst; 
                if(d.set_t0 !== undefined) { 
                    document.getElementById('in_t0').value = d.set_t0; document.getElementById('in_tx').value = d.set_tx; document.getElementById('in_bf').value = d.set_bf; document.getElementById('in_min_l').value = d.min_l; 
                    document.getElementById('in_lact').value = d.set_lact;
                } 
            }
            setTimeout(scheduleNextFetch, 200);
        })
        .catch(e => { console.log("Comms Error, retrying slower..."); setTimeout(scheduleNextFetch, 2000); });
    }
    setTimeout(scheduleNextFetch, 1000);
    setTimeout(fetchSchedules, 1000);
</script>
</body>
</html>
)rawliteral";

// ==========================================
// 7. CORE LOGIC
// ==========================================

void setLedBrightness(int newBrightness);
void updateLedControl(int brightness); 

int applyGamma(float progress, int maxVal) {
    if (progress <= 0.0) return 0;
    if (progress >= 1.0) return maxVal;
    float gamma = pow(progress, LED_GAMMA);
    int res = (int)(gamma * maxVal);
    return constrain(res, 0, 255);
}

void ledcWriteHardware(int brightnessLogic) {
    int pwm = 0;
    if (brightnessLogic <= 0) {
        pwm = 0;
    } else {
        pwm = map(brightnessLogic, 1, 255, ledMinPwm, 255);
        pwm = constrain(pwm, 0, 255);
    }
    if (pwm > maxAllowedBrightness) pwm = maxAllowedBrightness;
    int dutyCycle = 255 - pwm;
    ledcWrite(LED_CHAN, dutyCycle);
}

// Thermistor Math
float calculateSteinhart(float mv, float vcc) {
    if (mv < 50 || mv > vcc - 50) return -999.0;
    float r = R_FIXED * (mv / (vcc - mv));
    float s = log(r / R0) / B_COEFF + 1.0 / T0_KELVIN;
    return (1.0 / s) - 273.15;
}

int readAvgMV(int pin) {
    long sum = 0;
    for(int i=0; i<8; i++) sum += analogReadMilliVolts(pin);
    return sum / 8;
}

void calculateRPM() {
    unsigned long now = millis();
    if (now - lastRPMCalcTime >= 1000) {
        portENTER_CRITICAL(&timerMux);
        int p1 = tachPulses1; tachPulses1 = 0;
        int p2 = tachPulses2; tachPulses2 = 0;
        portEXIT_CRITICAL(&timerMux);
        
        int raw_rpm1 = p1 * 30;
        int raw_rpm2 = p2 * 30;
        
        // RPM Filtering
        if (raw_rpm1 == 0) { rpm1 = 0; } else { if (rpm1 == 0) rpm1 = raw_rpm1; else rpm1 = (rpm1 * 3 + raw_rpm1 * 7) / 10; }
        if (raw_rpm2 == 0) { rpm2 = 0; } else { if (rpm2 == 0) rpm2 = raw_rpm2; else rpm2 = (rpm2 * 3 + raw_rpm2 * 7) / 10; }
        lastRPMCalcTime = now;
    }
}

// --- FIXED: Use SPACE as separator to avoid JSON crash ---
String getFormattedTime() {
    if (!rtcPresent) return "NO RTC";
    DateTime now = rtc.now();
    time_t utc = now.unixtime();
    time_t local = utc + (long)(timeGmt * 3600) + (timeDst ? 3600 : 0);
    DateTime localDt(local);
    char buf[20];
    snprintf(buf, sizeof(buf), "%02d:%02d:%02d %02d-%02d", 
             localDt.hour(), localDt.minute(), localDt.second(), 
             localDt.day(), localDt.month());
    return String(buf);
}

void logEvent(String eventType) {
    String timestamp = rtcPresent ? getFormattedTime() : (String(millis()/1000) + "s");
    char buf[128];
    snprintf(buf, sizeof(buf), "%s,%s,%.1f,%.1f,%d,%d,%d,%d,%.0f", 
             timestamp.c_str(), eventType.c_str(), temp1_C, temp2_C, pwm1, pwm2, rpm1, rpm2, actualVCC_mV);
    String logEntry = String(buf);
    int head = preferences.getInt("log_head", 0);
    preferences.putString(("log_" + String(head)).c_str(), logEntry);
    preferences.putInt("log_head", (head + 1) % 10);
}

void loadProfiles() {
    for(int i=0; i<4; i++) {
        String key = "p" + String(i);
        if(preferences.isKey(key.c_str())) {
            preferences.getBytes(key.c_str(), &profiles[i], sizeof(SchedProfile));
        } else {
            if(i==0) {
                strlcpy(profiles[i].name, "Robocze", sizeof(profiles[i].name));
                profiles[i].daysMask = 0b0111110; 
                profiles[i].wakeHour = 7; profiles[i].wakeMin = 0; profiles[i].dawnDur = 30;
                profiles[i].sleepHour = 22; profiles[i].sleepMin = 0; profiles[i].duskDur = 60;
                profiles[i].maxBri = 255; profiles[i].active = true;
            } else {
                strlcpy(profiles[i].name, "Empty", sizeof(profiles[i].name));
                profiles[i].daysMask = 0;
            }
        }
    }
}

void updateScheduleLogic() {
    if (!rtcPresent) return;
    DateTime now = rtc.now();
    time_t utc = now.unixtime();
    time_t local = utc + (long)(timeGmt * 3600) + (timeDst ? 3600 : 0);
    DateTime locDt(local);
    int currentDay = locDt.dayOfTheWeek(); currentDayOfWeek = currentDay; 
    long currentSecOfDay = locDt.hour() * 3600L + locDt.minute() * 60L + locDt.second();
    int globalTargetBri = 0; SchedPhase globalNewPhase = PHASE_NIGHT; 
    int activeProfileMax = 255;

    for(int i=0; i<4; i++) {
        if((profiles[i].daysMask & (1 << currentDay)) && profiles[i].daysMask != 0) {
            SchedProfile p = profiles[i];
            long wakeSec = (long)(p.wakeHour * 60 + p.wakeMin) * 60L;
            long sleepSec = (long)(p.sleepHour * 60 + p.sleepMin) * 60L;
            long dawnDurSec = (long)p.dawnDur * 60L;
            long duskDurSec = (long)p.duskDur * 60L;
            long dawnStartSec = wakeSec - dawnDurSec;
            long duskStartSec = sleepSec - duskDurSec;
            
            int localBri = 0; SchedPhase localPhase = PHASE_NIGHT;
            if (currentSecOfDay < dawnStartSec) { localPhase = PHASE_NIGHT; localBri = 0; } 
            else if (currentSecOfDay < wakeSec) {
                localPhase = PHASE_DAWN;
                if (dawnDurSec > 0) { float progress = (float)(currentSecOfDay - dawnStartSec) / (float)dawnDurSec; localBri = applyGamma(progress, p.maxBri); } else { localBri = p.maxBri; }
            }
            else if (currentSecOfDay < duskStartSec) { localPhase = PHASE_DAY; localBri = p.maxBri; }
            else if (currentSecOfDay < sleepSec) {
                localPhase = PHASE_DUSK; activeProfileMax = p.maxBri; 
                int scheduledBri = 0;
                if (duskDurSec > 0) { float progress = (float)(currentSecOfDay - duskStartSec) / (float)duskDurSec; scheduledBri = applyGamma(1.0 - progress, p.maxBri); } else { scheduledBri = 0; }
                localBri = scheduledBri;
            }
            else { localPhase = PHASE_NIGHT; localBri = 0; }

            if (localBri > globalTargetBri) { globalTargetBri = localBri; globalNewPhase = localPhase; }
            else if (localBri == globalTargetBri && localBri > 0) { globalNewPhase = localPhase; }
        }
    }

    if (globalNewPhase != currentPhase) {
        if (globalNewPhase == PHASE_DUSK) {
            if (!ledAutoMode || ledBrightnessCurrent < (activeProfileMax - 5)) {
                duskCeilingBrightness = (int)ledBrightnessCurrent;
                if (duskCeilingBrightness < 5) duskCeilingBrightness = 0; 
            } else { duskCeilingBrightness = -1; }
            ledAutoMode = true;
        }
        else if (globalNewPhase == PHASE_DAWN || globalNewPhase == PHASE_DAY) {
            duskCeilingBrightness = -1;
            if (!ledAutoMode) { ledAutoMode = true; }
        }
        currentPhase = globalNewPhase;
    }

    if (ledAutoMode) {
        int finalBri = globalTargetBri;
        if (currentPhase == PHASE_DUSK && duskCeilingBrightness != -1 && activeProfileMax > 0) {
            float scheduleRatio = (float)globalTargetBri / (float)activeProfileMax;
            finalBri = (int)(scheduleRatio * duskCeilingBrightness);
        }
        setLedBrightness(constrain(finalBri, 0, 255));
    }
}

void checkFanHealth() {
    if (isCalibrating) return;
    if (safetyStatus != "OK" && safetyStatus != "BALANCING") return;
    int maxIdx = CALIB_POINTS_COUNT - 1;
    if (pwm1 > 250 && fan1Profile[maxIdx] > 0) {
        if (rpm1 < (fan1Profile[maxIdx] * (100 - RPM_TOLERANCE) / 100)) {
            if (fan1WearTimer == 0) fan1WearTimer = millis();
            else if (millis() - fan1WearTimer > 5000) safetyStatus = "WARN: FAN1 WEAR"; 
        } else fan1WearTimer = 0;
    } else fan1WearTimer = 0;
    if (pwm2 > 250 && fan2Profile[maxIdx] > 0) {
        if (rpm2 < (fan2Profile[maxIdx] * (100 - RPM_TOLERANCE) / 100)) {
            if (fan2WearTimer == 0) fan2WearTimer = millis();
            else if (millis() - fan2WearTimer > 5000) { if (safetyStatus == "OK" || safetyStatus == "BALANCING") safetyStatus = "WARN: FAN2 WEAR"; else safetyStatus += " / FAN2"; }
        } else fan2WearTimer = 0;
    } else fan2WearTimer = 0;
}

void rebuildCachedMapJson() {
    cachedMapJson = "\"cmap\":{";
    cachedMapJson += "\"f1\":[";
    for(int i=0; i<CALIB_POINTS_COUNT; i++) { cachedMapJson += String(fan1Profile[i]); if(i<CALIB_POINTS_COUNT-1) cachedMapJson += ","; }
    cachedMapJson += "],\"f2\":[";
    for(int i=0; i<CALIB_POINTS_COUNT; i++) { cachedMapJson += String(fan2Profile[i]); if(i<CALIB_POINTS_COUNT-1) cachedMapJson += ","; }
    cachedMapJson += "]},";
}

// Function to find the physical start PWM (0-255) from the calibration table
int getAutoMinPwm(int* profile) {
    // Scan table to find first index where fan RPM > 300
    for(int i=1; i<CALIB_POINTS_COUNT; i++) { 
        if(profile[i] > 300) { 
            return CALIB_POINTS[i]; // Return the PWM value for this step
        }
    }
    return 0; // Fallback (Fan broken or not connected)
}

int getPwmFromProfile(float temp, int* profile) {
    if (temp <= fanTempStart) return 0;
    if (temp >= fanTempMax) return 255;
    
    // Fallback: If uncalibrated (max PWM yields 0 RPM), use linear scaling with safe default
    if (profile[CALIB_POINTS_COUNT-1] == 0) { 
        float demand = (temp - fanTempStart) / (fanTempMax - fanTempStart);
        return SAFE_DEFAULT_PWM + (int)(demand * (255 - SAFE_DEFAULT_PWM)); 
    }

    float demand = (temp - fanTempStart) / (fanTempMax - fanTempStart);
    int minRPM = (profile[0] > 300) ? profile[0] : 0;
    int targetRPM = minRPM + (int)(demand * (profile[CALIB_POINTS_COUNT-1] - minRPM));
    
    if (targetRPM <= profile[0] && profile[0] > 300) return 0;
    
    for(int i=0; i<CALIB_POINTS_COUNT-1; i++) {
        int rpmA = profile[i]; int rpmB = profile[i+1];
        if (rpmB <= rpmA) continue; // Skip Valleys
        if (targetRPM >= rpmA && targetRPM <= rpmB) { return map(targetRPM, rpmA, rpmB, CALIB_POINTS[i], CALIB_POINTS[i+1]); }
    }
    return 255;
}

// --- FIXED: Instant Update Logic for Manual/Safety ---
void updateFanControl() {
    if (isCalibrating && !criticalError) return;

    // --- 1. CONFIGURATION & AUTO-CALCULATIONS ---
    int activeThresholdPwm = (ledActiveThresholdPct * 255) / 100;
    int minPwm1 = getAutoMinPwm(fan1Profile);
    int minPwm2 = getAutoMinPwm(fan2Profile);

    // --- 2. INPUT ANALYSIS ---
    float maxTemp = max(temp1_C, temp2_C);
    
    // SAFETY LOGIC
    float safetyTrigger = fanTempMax + 5.0;
    float safetyReset = safetyTrigger - 10.0;
    
    if (maxTemp > safetyTrigger) safetyCoolingActive = true; 
    else if (maxTemp < safetyReset) safetyCoolingActive = false;

    bool ledIsActive = (ledBrightnessTarget > activeThresholdPwm);

    // --- 3. CONTROL LOOP ---
    if (criticalError || safetyCoolingActive) {
        // [EMERGENCY MODE]
        pwm1_target = 255; 
        pwm2_target = 255;
    } 
    else if (manualMode) {
        pwm1_target = manualSpeed1;
        pwm2_target = manualSpeed2;
    }
    else if (ledIsActive) {
        // [ACTIVE COOLING MODE]
        int p1 = getPwmFromProfile(temp1_C, fan1Profile);
        int p2 = getPwmFromProfile(temp2_C, fan2Profile);

        if (minPwm1 > 0) p1 = max(p1, minPwm1);
        else if (p1 > 0) p1 = max(p1, SAFE_DEFAULT_PWM);

        if (minPwm2 > 0) p2 = max(p2, minPwm2);
        else if (p2 > 0) p2 = max(p2, SAFE_DEFAULT_PWM);
        
        if (maxTemp > 45.0) {
             float diff = temp1_C - temp2_C;
             if (abs(diff) > BALANCING_START_DIFF) {
                 int correction = (int)round(diff * fanBalanceFactor * 2.55);
                 p1 += correction;
             }
        }
        
        pwm1_target = constrain(p1, 0, 255);
        pwm2_target = constrain(p2, 0, 255);
    } 
    else {
        // [PASSIVE / NIGHT MODE]
        pwm1_target = 0;
        pwm2_target = 0;
    }

    // --- 4. EXECUTION (FIXED: INSTANT WRITE FOR MANUAL/CRITICAL) ---
    // If we are in manual or safety mode, we bypass the slow ramp loop
    // and write to hardware immediately for responsiveness.
    if (manualMode || criticalError || safetyCoolingActive) {
        pwm1_current = (float)pwm1_target;
        pwm2_current = (float)pwm2_target;
        pwm1 = pwm1_target;
        pwm2 = pwm2_target;
        ledcWrite(FAN_CHAN1, pwm1);
        ledcWrite(FAN_CHAN2, pwm2);
    }

    checkFanHealth();
}

void processFanRamp() {
    if (isCalibrating) { pwm1_current = pwm1_target; pwm2_current = pwm2_target; pwm1 = pwm1_target; pwm2 = pwm2_target; ledcWrite(FAN_CHAN1, pwm1); ledcWrite(FAN_CHAN2, pwm2); return; }
    static unsigned long lastRamp = 0;
    if (millis() - lastRamp >= 100) { 
        lastRamp = millis();
        // Slow ramp only applies to AUTO mode now (Manual/Safety bypass this)
        if (pwm1_current < pwm1_target) pwm1_current += 1.0; else if (pwm1_current > pwm1_target) pwm1_current -= 1.0;
        if (pwm2_current < pwm2_target) pwm2_current += 1.0; else if (pwm2_current > pwm2_target) pwm2_current -= 1.0;
        pwm1 = (int)pwm1_current; pwm2 = (int)pwm2_current;
        if (!manualMode && !criticalError && !safetyCoolingActive) { ledcWrite(FAN_CHAN1, pwm1); ledcWrite(FAN_CHAN2, pwm2); }
    }
}

void processLedRamp() {
    float step = 0.5;
    if (instantRampAction) { step = 30.0; } else { if (abs(ledBrightnessTarget - ledBrightnessCurrent) > 50) step = 2.0; }
    if (ledBrightnessCurrent < ledBrightnessTarget) { 
        ledBrightnessCurrent += step;
        if (ledBrightnessCurrent > ledBrightnessTarget) { ledBrightnessCurrent = ledBrightnessTarget; instantRampAction = false; }
    } 
    else if (ledBrightnessCurrent > ledBrightnessTarget) { 
        ledBrightnessCurrent -= step;
        if (ledBrightnessCurrent < ledBrightnessTarget) { ledBrightnessCurrent = ledBrightnessTarget; instantRampAction = false; }
    } else { instantRampAction = false; }
    
    int outVal = (int)ledBrightnessCurrent;
    ledcWriteHardware(outVal);
    ledBrightness = outVal;
}

void setLedBrightness(int newBrightness) {
    if (ledBrightnessTarget != newBrightness) { 
        if (abs(newBrightness - (int)ledBrightnessCurrent) > 100) { instantRampAction = true; } else { instantRampAction = false; }
        ledBrightnessTarget = newBrightness;
        ledSettingsChanged = true; lastLedChangeTime = millis(); 
    }
}

void checkFlashCommit() {
    if (ledSettingsChanged && (millis() - lastLedChangeTime > 3000)) { preferences.putInt("led", ledBrightnessTarget); ledSettingsChanged = false; }
}

void runCalibrationLogic() {
    if (!isCalibrating) return;
    if (temp1_C > fanTempMax || temp2_C > fanTempMax) {
        isCalibrating = false;
        ledcWrite(FAN_CHAN1, 255); ledcWrite(FAN_CHAN2, 255); pwm1_target = 255; pwm2_target = 255; pwm1_current = 255; pwm2_current = 255; Serial.println("CALIB ABORTED: OVERHEAT DETECTED!");
        return;
    }
    unsigned long now = millis();
    if (now - calibStepStartTime >= 10000) {
        fan1Profile[calibStep] = rpm1; fan2Profile[calibStep] = rpm2;
        calibStep++;
        if (calibStep >= CALIB_POINTS_COUNT) {
            isCalibrating = false;
            pwm1_target = 0; pwm2_target = 0; pwm1_current = 0; pwm2_current = 0; ledcWrite(FAN_CHAN1, 0); ledcWrite(FAN_CHAN2, 0);
            preferences.putBytes("f1_map", fan1Profile, sizeof(fan1Profile));
            preferences.putBytes("f2_map", fan2Profile, sizeof(fan2Profile)); rebuildCachedMapJson(); 
        } else {
            calibStepStartTime = now;
            int nextPWM = CALIB_POINTS[calibStep]; pwm1 = nextPWM; pwm2 = nextPWM; pwm1_current = nextPWM; pwm2_current = nextPWM; ledcWrite(FAN_CHAN1, nextPWM); ledcWrite(FAN_CHAN2, nextPWM);
            pwm1_target = nextPWM; pwm2_target = nextPWM;
        }
    }
}

void handleGestures(int delta) {
    unsigned long now = millis();
    if (delta > QRD_THRESH_TRIGGER && !isTouched) {
        isTouched = true; touchStartTime = now; holdModeActive = false; 
        if(ledAutoMode) { ledAutoMode = false; Serial.println("Auto Mode Disabled by Touch"); }
        if (ledBrightnessTarget < (ledMinPct + 1)) { dimmingUp = true; } 
        else if (ledBrightnessTarget >= 255) { dimmingUp = false; } 
        else { dimmingUp = !dimmingUp; }
    }
    else if (delta < QRD_THRESH_RELEASE && isTouched) {
        isTouched = false; unsigned long duration = now - touchStartTime;
        if (duration < LONG_PRESS_TIME && !holdModeActive) {
            unsigned long timeSinceLastTap = now - lastTapReleaseTime;
            if (timeSinceLastTap < MULTI_TAP_TIMEOUT) { consecutiveTaps++; } else { consecutiveTaps = 1; }
            lastTapReleaseTime = now;
            if (consecutiveTaps == 1) {
                if (ledBrightnessTarget > 0) { lastOnBrightness = ledBrightnessTarget; setLedBrightness(0); } 
                else { int val = (lastOnBrightness >= 15) ? lastOnBrightness : 255; setLedBrightness(val); }
            }
            else if (consecutiveTaps == 2) { setLedBrightness(ledMinPwm > 10 ? ledMinPwm : 10); }
            else if (consecutiveTaps == 3) { setLedBrightness(255); }
        }
        if (holdModeActive) {
             ledBrightnessTarget = (int)ledBrightnessCurrent;
             if(ledBrightnessTarget > 0) lastOnBrightness = ledBrightnessTarget;
             if (currentPhase == PHASE_DUSK) { duskCeilingBrightness = ledBrightnessTarget; }
        }
    }
    if (isTouched) {
        unsigned long duration = now - touchStartTime;
        if (duration > LONG_PRESS_TIME) {
            holdModeActive = true; consecutiveTaps = 0; 
            if (now - lastHoldStepTime >= STEP_TIME) {
                lastHoldStepTime = now;
                float current = ledBrightnessCurrent;
                if (current < 1.0 && dimmingUp) { current = (float)ledMinPct; }
                float speedFactor = 1.0 + (current / 40.0);
                if (dimmingUp) { current += speedFactor; if (current >= 255.0) { current = 255.0; dimmingUp = false; } } 
                else { current -= speedFactor; if (current <= ledMinPct) { current = (float)ledMinPct; dimmingUp = true; } }
                ledBrightnessCurrent = current; ledBrightnessTarget = (int)current; ledBrightness = (int)current; ledcWriteHardware((int)current);
            }
        } else { lastHoldStepTime = now; }
    }
}

void performSensorsCycle() {
    static int tempCycleCounter = 0;
    bool doTempMeasure = (++tempCycleCounter >= 30);
    digitalWrite(PWR_PIN, LOW); delayMicroseconds(100);
    long qrdOff = 0; for(int i=0; i<4; i++) qrdOff += analogRead(QRD_SENS_PIN); qrdOff /= 4;
    digitalWrite(PWR_PIN, HIGH);
    if (doTempMeasure) delay(80); else delayMicroseconds(200);
    long qrdOn = 0; for(int i=0; i<4; i++) qrdOn += analogRead(QRD_SENS_PIN); qrdOn /= 4;
    
    if (doTempMeasure) {
        int rv = readAvgMV(VCC_MON); int rt1 = readAvgMV(TH1_PIN); int rt2 = readAvgMV(TH2_PIN);
        actualVCC_mV = rv * 2.0; temp1_C = calculateSteinhart(rt1, actualVCC_mV); temp2_C = calculateSteinhart(rt2, actualVCC_mV);
        criticalError = false; maxAllowedBrightness = 255; safetyStatus = "OK";
        float tDiff = abs(temp1_C - temp2_C);
        bool t1_out = (temp1_C < SENSOR_MIN_T || temp1_C > SENSOR_MAX_T); bool t2_out = (temp2_C < SENSOR_MIN_T || temp2_C > SENSOR_MAX_T);
        if ((t1_out || t2_out) && tDiff > MAX_TEMP_DIFF) { criticalError = true; maxAllowedBrightness = 0; safetyStatus = "SENSOR FAIL"; }
        else if (tDiff > MAX_TEMP_DIFF) { maxAllowedBrightness = 127; safetyStatus = "IMBALANCE (>8C)"; }
        else if (tDiff > BALANCING_START_DIFF) { safetyStatus = "BALANCING"; }
        
        updateFanControl(); 
        
        if (safetyStatus != lastSafetyStatus) { if (safetyStatus != "OK" && safetyStatus != "BALANCING") logEvent(safetyStatus); lastSafetyStatus = safetyStatus; }
        tempCycleCounter = 0;
    }
    digitalWrite(PWR_PIN, LOW);
    qrdDelta = qrdOff - qrdOn; if (qrdDelta < 0) qrdDelta = 0;
    handleGestures(qrdDelta);
}

void checkBootReset() {
    digitalWrite(PWR_PIN, LOW); delay(10); long qrdOff = analogRead(QRD_SENS_PIN);
    digitalWrite(PWR_PIN, HIGH); delay(10); long qrdOn = analogRead(QRD_SENS_PIN);
    digitalWrite(PWR_PIN, LOW);
    int delta = qrdOff - qrdOn;
    if (delta > QRD_THRESH_TRIGGER) {
        Serial.println("BOOT: Touch detected. Waiting for reset request...");
        for(int i=0; i<30; i++) { 
            ledcWrite(LED_CHAN, (i%4 < 2) ? 0 : 255); delay(100);
            digitalWrite(PWR_PIN, LOW); delayMicroseconds(100); long off = analogRead(QRD_SENS_PIN);
            digitalWrite(PWR_PIN, HIGH); delayMicroseconds(100); long on = analogRead(QRD_SENS_PIN);
            digitalWrite(PWR_PIN, LOW);
            if (off - on < QRD_THRESH_RELEASE) { Serial.println("BOOT: Touch released. Continuing normal boot."); ledcWrite(LED_CHAN, 255); return; }
        }
        Serial.println("BOOT: FACTORY RESET TRIGGERED!");
        preferences.begin("fan_cfg", false); preferences.remove("ap_pass"); preferences.end();
        for(int i=0; i<3; i++) { ledcWrite(LED_CHAN, 0); delay(300); ledcWrite(LED_CHAN, 255); delay(300); }
        ESP.restart();
    }
}

void setup() {
    Serial.begin(115200); 
    digitalWrite(LED_DIM_PIN, HIGH); pinMode(LED_DIM_PIN, OUTPUT);
    gpio_reset_pin((gpio_num_t)LED_DIM_PIN); pinMode(LED_DIM_PIN, OUTPUT); digitalWrite(LED_DIM_PIN, HIGH);
    pinMode(PWR_PIN, OUTPUT); digitalWrite(PWR_PIN, LOW);
    pinMode(QRD_SENS_PIN, INPUT);
    ledcSetup(LED_CHAN, LED_PWM_FREQ, LED_PWM_RES); ledcAttachPin(LED_DIM_PIN, LED_CHAN);
    ledcWrite(LED_CHAN, 255); 
    checkBootReset();
    delay(2000); 
    Wire.begin(RTC_SDA_PIN, RTC_SCL_PIN);
    if(rtc.begin()) { Serial.println("RTC Found"); rtcPresent = true; if(rtc.lostPower()) Serial.println("RTC lost power!"); } else Serial.println("RTC NOT FOUND");
    
    preferences.begin("fan_cfg", false);
    fanTempStart = preferences.getFloat("t0", 30.0);
    fanTempMax = preferences.getFloat("tx", 55.0);
    fanBalanceFactor = preferences.getFloat("bf_pct", 5.0);
    // fanMinPwm = preferences.getInt("min_p", 20); // DELETED
    timeGmt = preferences.getFloat("gmt", 1.0);
    timeDst = preferences.getBool("dst", false);
    ledMinPct = preferences.getInt("min_l_pct", 10);
    ledMinPwm = (ledMinPct * 255) / 100;
    
    // LOAD NIGHT MODE THRESHOLD
    ledActiveThresholdPct = preferences.getInt("lact", 5);

    loadProfiles();
    if (esp_reset_reason() == ESP_RST_POWERON) ledBrightnessTarget = 255; else ledBrightnessTarget = preferences.getInt("led", 255);
    if (ledBrightnessTarget > 0) lastOnBrightness = ledBrightnessTarget; else lastOnBrightness = 255;
    ledBrightnessCurrent = (float)ledBrightnessTarget; ledBrightness = ledBrightnessTarget;
    if (preferences.isKey("f1_map")) preferences.getBytes("f1_map", fan1Profile, sizeof(fan1Profile));
    if (preferences.isKey("f2_map")) preferences.getBytes("f2_map", fan2Profile, sizeof(fan2Profile));
    rebuildCachedMapJson(); 

    analogReadResolution(12); analogSetAttenuation(ADC_11db);
    ledcSetup(FAN_CHAN1, FAN_PWM_FREQ, FAN_PWM_RES); ledcAttachPin(FAN1_PWM_PIN, FAN_CHAN1);
    ledcSetup(FAN_CHAN2, FAN_PWM_FREQ, FAN_PWM_RES); ledcAttachPin(FAN2_PWM_PIN, FAN_CHAN2);
    ledcWriteHardware(ledBrightnessTarget);

    pinMode(FAN1_TACHO_PIN, INPUT); attachInterrupt(digitalPinToInterrupt(FAN1_TACHO_PIN), isrFan1, FALLING);
    pinMode(FAN2_TACHO_PIN, INPUT); attachInterrupt(digitalPinToInterrupt(FAN2_TACHO_PIN), isrFan2, FALLING);

    WiFi.disconnect(true); WiFi.mode(WIFI_AP); WiFi.setTxPower(WIFI_POWER_11dBm); WiFi.onEvent(WiFiEvent);
    String apPass = preferences.getString("ap_pass", "");
    if (apPass.length() >= 8) { WiFi.softAP("Smart Lamp Control", apPass.c_str()); } else { WiFi.softAP("Smart Lamp Control", NULL); }
    dnsServer.start(53, "*", WiFi.softAPIP());

    server.on("/", HTTP_GET, [](AsyncWebServerRequest *r){ r->send(200, "text/html", index_html); });
    
    // --- ROBUST LOG HANDLER (Fixes "Poisoned" Data) ---
    server.on("/get_logs", HTTP_GET, [](AsyncWebServerRequest *r){ 
        String json; 
        json.reserve(2048); // Increased from 512 to prevent fragmentation
        json = "{\"logs\":["; 
        
        int head = preferences.getInt("log_head", 0); 
        for(int i=0; i<10; i++) { 
            int idx = (head - 1 - i + 10) % 10; 
            String l = preferences.getString(("log_" + String(idx)).c_str(), ""); 
            
            if(l != "") { 
                // SANITIZATION: Remove characters that break JSON
                l.replace("\n", " ");  // Kill the newline from v21
                l.replace("\r", "");   // Kill carriage returns
                l.replace("\"", "'");  // Safety for quotes
                
                if(json.length() > 9) json += ","; 
                json += "\"" + l + "\""; 
            } 
        } 
        json += "]}"; 
        r->send(200, "application/json", json); 
    });

    // --- NEW: CLEAR LOGS ENDPOINT ---
    server.on("/clear_logs", HTTP_GET, [](AsyncWebServerRequest *r){ 
        // Clear all 10 slots
        for(int i=0; i<10; i++) {
            String key = "log_" + String(i);
            if(preferences.isKey(key.c_str())) preferences.remove(key.c_str());
        }
        preferences.putInt("log_head", 0);
        r->send(200, "text/plain", "OK"); 
    });

    server.on("/data", HTTP_GET, [](AsyncWebServerRequest *r){
        String j; j.reserve(1024); j = "{";
        j.concat("\"vcc\":"); j.concat(String(actualVCC_mV, 0)); j.concat(",\"t1\":"); j.concat(String(temp1_C, 1)); j.concat(",\"t2\":"); j.concat(String(temp2_C, 1));
        j.concat(",\"pwm1\":"); j.concat(pwm1); j.concat(",\"pwm2\":"); j.concat(pwm2); j.concat(",\"rpm1\":"); j.concat(rpm1); j.concat(",\"rpm2\":"); j.concat(rpm2);
        
        int effective = (int)ledBrightnessCurrent;
        if(effective > maxAllowedBrightness) effective = maxAllowedBrightness;
        j.concat(",\"led\":"); j.concat(effective); 
        
        j.concat(",\"prx\":"); j.concat(qrdDelta); j.concat(",\"tch\":"); j.concat(isTouched?"true":"false");
        j.concat(",\"stat\":\""); j.concat(safetyStatus); j.concat("\","); j.concat("\"man\":"); j.concat(manualMode?"true":"false"); j.concat(",\"lauto\":"); j.concat(ledAutoMode?"true":"false"); 
        j.concat(",\"cal\":"); j.concat(isCalibrating?"true":"false"); j.concat(",\"cstp\":"); j.concat(calibStep);
        j.concat(",\"gmt\":"); j.concat(timeGmt); j.concat(",\"dst\":"); j.concat(timeDst?"true":"false"); j.concat(",\"day\":"); j.concat(currentDayOfWeek);
        j.concat(",\"set_t0\":"); j.concat(fanTempStart); j.concat(",\"set_tx\":"); j.concat(fanTempMax); j.concat(",\"set_bf\":"); j.concat(fanBalanceFactor); j.concat(",\"set_mp\":"); j.concat(0); 
        j.concat(",\"min_l\":"); j.concat(ledMinPct);
        
        j.concat(",\"set_lact\":"); j.concat(ledActiveThresholdPct);
        
        j.concat(","); j.concat(cachedMapJson); j.concat("\"time\":\""); j.concat(currentTimeStr); j.concat("\","); j.concat("\"err\":"); j.concat(criticalError?"true":"false");
        j += "}";
        r->send(200, "application/json", j);
    });
    
    server.on("/get_schedules", HTTP_GET, [](AsyncWebServerRequest *r){ String j = "{\"profs\":["; for(int i=0; i<4; i++) { j += "{"; j += "\"name\":\"" + String(profiles[i].name) + "\","; j += "\"dm\":" + String(profiles[i].daysMask) + ","; j += "\"wh\":" + String(profiles[i].wakeHour) + ",\"wm\":" + String(profiles[i].wakeMin) + ","; j += "\"dd\":" + String(profiles[i].dawnDur) + ","; j += "\"sh\":" + String(profiles[i].sleepHour) + ",\"sm\":" + String(profiles[i].sleepMin) + ","; j += "\"kd\":" + String(profiles[i].duskDur) + ","; j += "\"mb\":" + String(profiles[i].maxBri); j += "}"; if(i<3) j+=","; } j += "]}"; r->send(200, "application/json", j); });
    server.on("/save_profile", HTTP_GET, [](AsyncWebServerRequest *r){
        if(r->hasParam("id")) {
            int id = r->getParam("id")->value().toInt();
            if(id >= 0 && id < 4) {
                if(r->hasParam("n")) strlcpy(profiles[id].name, r->getParam("n")->value().c_str(), sizeof(profiles[id].name));
                if(r->hasParam("dm")) profiles[id].daysMask = r->getParam("dm")->value().toInt();
                if(r->hasParam("wh")) profiles[id].wakeHour = r->getParam("wh")->value().toInt();
                if(r->hasParam("wm")) profiles[id].wakeMin = r->getmit(); 
    processFanRamp();
    
    static unsigned long lastLedRamp = 0;
    if (millis() - lastLedRamp >= 20) { lastLedRamp = millis(); processLedRamp(); }
    
    if (isCalibrating) runCalibrationLogic();

    static unsigned long lastCycle = 0;
    if (millis() - lastCycle >= 30) { lastCycle = millis(); performSensorsCycle(); }

    static unsigned long lastClock = 0;
    if (millis() - lastClock >= 1000) {
        lastClock = millis();
        if(rtcPresent) {
            DateTime now = rtc.now();
            time_t utc = now.unixtime();
            time_t local = utc + (long)(timeGmt * 3600) + (timeDst ? 3600 : 0);
            DateTime localDt(local);
            char buf[10]; snprintf(buf, sizeof(buf), "%02d:%02d:%02d", localDt.hour(), localDt.minute(), localDt.second());
            currentTimeStr = String(buf);
            updateScheduleLogic();
        }
    }
    
    static unsigned long lastLog = 0;
    if (millis() - lastLog > 500) { lastLog = millis(); logToSerial(); }
}