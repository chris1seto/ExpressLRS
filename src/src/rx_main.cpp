#include "targets.h"
#include "common.h"
#include "LowPassFilter.h"

#if defined(Regulatory_Domain_AU_915) || defined(Regulatory_Domain_EU_868) || defined(Regulatory_Domain_IN_866) || defined(Regulatory_Domain_FCC_915) || defined(Regulatory_Domain_AU_433) || defined(Regulatory_Domain_EU_433)
#include "SX127xDriver.h"
SX127xDriver Radio;
#elif defined(Regulatory_Domain_ISM_2400)
#include "SX1280Driver.h"
SX1280Driver Radio;
#else
#error "Radio configuration is not valid!"
#endif

#include "crc.h"
#include "CRSF.h"
#include "telemetry_protocol.h"
#include "telemetry.h"
#include "stubborn_sender.h"
#include "stubborn_receiver.h"

#include "FHSS.h"
#include "logging.h"
#include "OTA.h"
#include "msp.h"
#include "msptypes.h"
#include "hwTimer.h"
#include "PFD.h"
#include "LQCALC.h"
#include "elrs_eeprom.h"
#include "config.h"
#include "options.h"
#include "POWERMGNT.h"

#include "device.h"
#include "helpers.h"
#include "devLED.h"
#include "devWIFI.h"
#include "devButton.h"

//// CONSTANTS ////
#define SEND_LINK_STATS_TO_FC_INTERVAL 100
#define DIVERSITY_ANTENNA_INTERVAL 5
#define DIVERSITY_ANTENNA_RSSI_TRIGGER 5
#define PACKET_TO_TOCK_SLACK 200 // Desired buffer time between Packet ISR and Tock ISR
///////////////////

device_t *ui_devices[] = {
#ifdef HAS_LED
  &LED_device,
#endif
#ifdef HAS_RGB
  &RGB_device,
#endif
#ifdef HAS_WIFI
  &WIFI_device,
#endif
#ifdef HAS_BUTTON
  &Button_device
#endif
};

uint8_t antenna = 0;    // which antenna is currently in use

hwTimer hwTimer;
POWERMGNT POWERMGNT;
PFD PFDloop;
GENERIC_CRC14 ota_crc(ELRS_CRC14_POLY);
ELRS_EEPROM eeprom;
RxConfig config;
Telemetry telemetry;

#ifdef PLATFORM_ESP8266
unsigned long rebootTime = 0;
extern bool webserverPreventAutoStart;
#endif

StubbornSender TelemetrySender(ELRS_TELEMETRY_MAX_PACKAGES);
static uint8_t telemetryBurstCount;
static uint8_t telemetryBurstMax;
// Maximum ms between LINK_STATISTICS packets for determining burst max
#define TELEM_MIN_LINK_INTERVAL 512U

StubbornReceiver MspReceiver(ELRS_MSP_MAX_PACKAGES);
uint8_t MspData[ELRS_MSP_BUFFER];

static uint8_t NextTelemetryType = ELRS_TELEMETRY_TYPE_LINK;
static bool telemBurstValid;
/// Filters ////////////////
LPF LPF_Offset(2);
LPF LPF_OffsetDx(4);

// LPF LPF_UplinkRSSI(5);
LPF LPF_UplinkRSSI0(5);  // track rssi per antenna
LPF LPF_UplinkRSSI1(5);


/// LQ Calculation //////////
LQCALC<100> LQCalc;
uint8_t uplinkLQ;

uint8_t scanIndex = RATE_DEFAULT;

int32_t RawOffset;
int32_t prevRawOffset;
int32_t Offset;
int32_t OffsetDx;
int32_t prevOffset;
RXtimerState_e RXtimerState;
uint32_t GotConnectionMillis = 0;
bool connectionHasModelMatch;
const uint32_t ConsiderConnGoodMillis = 1000; // minimum time before we can consider a connection to be 'good'

///////////////////////////////////////////////

volatile uint8_t NonceRX = 0; // nonce that we THINK we are up to.

bool alreadyFHSS = false;
bool alreadyTLMresp = false;

uint32_t beginProcessing;
uint32_t doneProcessing;

//////////////////////////////////////////////////////////////

///////Variables for Telemetry and Link Quality///////////////
uint32_t LastValidPacket = 0;           //Time the last valid packet was recv
uint32_t LastSyncPacket = 0;            //Time the last valid packet was recv

uint32_t SendLinkStatstoFCintervalLastSent = 0;

int16_t RFnoiseFloor; //measurement of the current RF noise floor
#if defined(DEBUG_RX_SCOREBOARD)
static bool lastPacketCrcError;
#endif
///////////////////////////////////////////////////////////////

/// Variables for Sync Behaviour ////
uint32_t cycleInterval; // in ms
uint32_t RFmodeLastCycled = 0;
#define RFmodeCycleMultiplierSlow 10
uint8_t RFmodeCycleMultiplier;
bool LockRFmode = false;
///////////////////////////////////////

#if defined(BF_DEBUG_LINK_STATS)
// Debug vars
uint8_t debug1 = 0;
uint8_t debug2 = 0;
uint8_t debug3 = 0;
int8_t debug4 = 0;
///////////////////////////////////////
#endif

bool InBindingMode = false;

OtaSwitchMode_e OtaSwitchModeCurrent;

crsfLinkStatistics_t link_stats = {0};

void reset_into_bootloader(void);
void EnterBindingMode();
void ExitBindingMode();
void UpdateModelMatch(uint8_t model);
void OnELRSBindMSP(uint8_t* packet);

float channel_data[CRSF_NUM_CHANNELS] = {0};

#define INTERNAL_CONTROL_MIN -1000.0f
#define INTERNAL_CONTROL_MAX 1000.0f

float map(float x, float in_min, float in_max, float out_min, float out_max)
{
  return (x - in_min) * (out_max - out_min) / (in_max - in_min) + out_min;
}

float Constrain(const float x, const float min, const float max)
{
  if (x < min)
  {
    return min;
  }
  else if (x > max)
  {
    return max;
  }
  
  return x;
}

float CenterMap(const float x,
  const float in_min, const float in_center, const float in_max,
  const float out_min, const float out_center, const float out_max)
{
  if (x > in_center)
  {
    return map(x, in_center, in_max, out_center, out_max);
  }
  else if (x < in_center)
  {
    return map(x, in_center, in_min, out_center, out_min);
  }
  else
  {
    return out_center;
  }
}

void OutputSpektrum(void)
{
  uint16_t remapped_channel_data[7];
  uint8_t tx_buffer[2 + 14];
  uint32_t packet_ptr = 0;
  uint32_t i;
  uint16_t temp;

  remapped_channel_data[0] = channel_data[0]; // 1 Throttle
  remapped_channel_data[1] = channel_data[1]; // 2 Steering
  remapped_channel_data[2] = channel_data[8]; // 3 Blank
  remapped_channel_data[3] = channel_data[2]; // 4 Waypoint add/delete
  remapped_channel_data[4] = channel_data[8]; // 5 Blank
  remapped_channel_data[5] = channel_data[5]; // 6 Mode
  remapped_channel_data[6] = channel_data[4]; // 7 Arm

  /*
    0x03
    0x01
    (7 channels, 2 bytes each = 14 total bytes of channel data)
      * First byte contains the channel ID
      * Second byte contains the channel data
  */

  tx_buffer[packet_ptr++] = 0x03;
  tx_buffer[packet_ptr++] = 0x01;

  // From the Pathpoint code
  //uint16_t result = (channelData.ChannelItem[channel-1].Value * 0.586 + 900);

  for (i = 0; i < 7; i++)
  {
    /*
    Spektrum mapping values generated by using the eq above and setting up
      1000 = x * .586 + 900
      1500 = x * .586 + 900
      2000 = x * .586 + 900
    */
    
    temp = (uint16_t)CenterMap(remapped_channel_data[i],
      INTERNAL_CONTROL_MIN, 0, INTERNAL_CONTROL_MAX,
      170.648f, 1023.89f, 1877.13);
    
    tx_buffer[packet_ptr++] = ((i + 1) << 3) | ((temp >> 8) & 0b00000111);
    tx_buffer[packet_ptr++] = temp;
  }

  Serial.write(tx_buffer, sizeof(tx_buffer));
}

void ProcessRcData(const uint8_t* ota)
{
  uint16_t raw_channel_data[CRSF_NUM_CHANNELS];
  uint32_t i;
  uint8_t switchByte;
  uint8_t switchIndex;
  uint16_t switchValue;
  float temp_channel;

  // The analog channels
  // 172 to 1810, center = 992
  // 820 lower
  // 818
  raw_channel_data[0] = (ota[1] << 3) | ((ota[5] & 0b11000000) >> 5);
  raw_channel_data[1]  = (ota[2] << 3) | ((ota[5] & 0b00110000) >> 3);
  raw_channel_data[2]  = (ota[3] << 3) | ((ota[5] & 0b00001100) >> 1);
  raw_channel_data[3] = (ota[4] << 3) | ((ota[5] & 0b00000011) << 1);

  switch (OtaSwitchModeCurrent)
  {
    case sm1Bit:
      break;
    case smHybrid:
      switchByte = ota[6];

      // The low latency switch
      raw_channel_data[4] = BIT_to_CRSF((switchByte & 0b01000000) >> 6);

      // The round-robin switch, switchIndex is actually index-1
      // to leave the low bit open for switch 7 (sent as 0b11x)
      // where x is the high bit of switch 7
      switchIndex = (switchByte & 0b111000) >> 3;
      switchValue = SWITCH3b_to_CRSF(switchByte & 0b111);

      switch (switchIndex)
      {
        case 0:
            raw_channel_data[5] = switchValue;
            break;
        case 1:
            raw_channel_data[6] = switchValue;
            break;
        case 2:
            raw_channel_data[7] = switchValue;
            break;
        case 3:
            raw_channel_data[8] = switchValue;
            break;
        case 4:
            raw_channel_data[9] = switchValue;
            break;
        case 5:
            raw_channel_data[10] = switchValue;
            break;
        case 6:   // Because AUX1 (index 0) is the low latency switch, the low bit
        case 7:   // of the switchIndex can be used as data, and arrives as index "6"
            raw_channel_data[11] = N_to_CRSF(switchByte & 0b1111, 15);
            break;
      }

      break;
    case smHybridWide:
      break;
    default:
      break;
  }
  
  for (i = 0; i < CRSF_NUM_CHANNELS; i++)
  {
    temp_channel = CenterMap(raw_channel_data[i],
      CRSF_CHANNEL_VALUE_1000, CRSF_CHANNEL_VALUE_MID, CRSF_CHANNEL_VALUE_2000,
      INTERNAL_CONTROL_MIN, 0, INTERNAL_CONTROL_MAX);

    channel_data[i] = Constrain(temp_channel, INTERNAL_CONTROL_MIN, INTERNAL_CONTROL_MAX);
  }

  OutputSpektrum();
}


static uint8_t minLqForChaos()
{
    // Determine the most number of CRC-passing packets we could receive on
    // a single channel out of 100 packets that fill the LQcalc span.
    // The LQ must be GREATER THAN this value, not >=
    // The amount of time we coexist on the same channel is
    // 100 divided by the total number of packets in a FHSS loop (rounded up)
    // and there would be 4x packets received each time it passes by so
    // FHSShopInterval * ceil(100 / FHSShopInterval * numfhss) or
    // FHSShopInterval * trunc((100 + (FHSShopInterval * numfhss) - 1) / (FHSShopInterval * numfhss))
    // With a interval of 4 this works out to: 2.4=4, FCC915=4, AU915=8, EU868=8, EU/AU433=36
    const uint32_t numfhss = FHSSgetChannelCount();
    const uint8_t interval = ExpressLRS_currAirRate_Modparams->FHSShopInterval;
    return interval * ((interval * numfhss + 99) / (interval * numfhss));
}

void ICACHE_RAM_ATTR getRFlinkInfo()
{
    int32_t rssiDBM0 = LPF_UplinkRSSI0.SmoothDataINT;
    int32_t rssiDBM1 = LPF_UplinkRSSI1.SmoothDataINT;
    switch (antenna) {
        case 0:
            rssiDBM0 = LPF_UplinkRSSI0.update(Radio.LastPacketRSSI);
            break;
        case 1:
            rssiDBM1 = LPF_UplinkRSSI1.update(Radio.LastPacketRSSI);
            break;
    }

    int32_t rssiDBM = (antenna == 0) ? rssiDBM0 : rssiDBM1;

    if (rssiDBM0 > 0) rssiDBM0 = 0;
    if (rssiDBM1 > 0) rssiDBM1 = 0;

    // BetaFlight/iNav expect positive values for -dBm (e.g. -80dBm -> sent as 80)
    link_stats.uplink_RSSI_1 = -rssiDBM0;
    link_stats.active_antenna = antenna;
    link_stats.uplink_SNR = Radio.LastPacketSNR;
    link_stats.rf_Mode = (uint8_t)RATE_4HZ - (uint8_t)ExpressLRS_currAirRate_Modparams->enum_rate;
    link_stats.downlink_RSSI = 0;
    link_stats.downlink_Link_quality = 0;
    link_stats.downlink_SNR = 0;
    link_stats.uplink_RSSI_2 = -rssiDBM1;
}


void SetRFLinkRate(uint8_t index) // Set speed of RF link
{
    expresslrs_mod_settings_s *const ModParams = get_elrs_airRateConfig(index);
    expresslrs_rf_pref_params_s *const RFperf = get_elrs_RFperfParams(index);
    bool invertIQ = UID[5] & 0x01;

    hwTimer.updateInterval(ModParams->interval);
    Radio.Config(ModParams->bw, ModParams->sf, ModParams->cr, GetInitialFreq(), ModParams->PreambleLen, invertIQ, ModParams->PayloadLength);

    // Wait for (11/10) 110% of time it takes to cycle through all freqs in FHSS table (in ms)
    cycleInterval = ((uint32_t)11U * FHSSgetChannelCount() * ModParams->FHSShopInterval * ModParams->interval) / (10U * 1000U);

    ExpressLRS_currAirRate_Modparams = ModParams;
    ExpressLRS_currAirRate_RFperfParams = RFperf;
    ExpressLRS_nextAirRateIndex = index; // presumably we just handled this
    telemBurstValid = false;
}

bool ICACHE_RAM_ATTR HandleFHSS()
{
    uint8_t modresultFHSS = (NonceRX + 1) % ExpressLRS_currAirRate_Modparams->FHSShopInterval;

    if ((ExpressLRS_currAirRate_Modparams->FHSShopInterval == 0) || alreadyFHSS == true || InBindingMode || (modresultFHSS != 0) || (connectionState == disconnected))
    {
        return false;
    }

    alreadyFHSS = true;
    Radio.SetFrequencyReg(FHSSgetNextFreq());

    uint8_t modresultTLM = (NonceRX + 1) % (TLMratioEnumToValue(ExpressLRS_currAirRate_Modparams->TLMinterval));

    if (modresultTLM != 0 || ExpressLRS_currAirRate_Modparams->TLMinterval == TLM_RATIO_NO_TLM) // if we are about to send a tlm response don't bother going back to rx
    {
        Radio.RXnb();
    }
    return true;
}

bool ICACHE_RAM_ATTR HandleSendTelemetryResponse()
{
    uint8_t *data;
    uint8_t maxLength;
    uint8_t packageIndex;
    uint8_t modresult = (NonceRX + 1) % TLMratioEnumToValue(ExpressLRS_currAirRate_Modparams->TLMinterval);

    if ((connectionState == disconnected) || (ExpressLRS_currAirRate_Modparams->TLMinterval == TLM_RATIO_NO_TLM) || (alreadyTLMresp == true) || (modresult != 0))
    {
        return false; // don't bother sending tlm if disconnected or TLM is off
    }

    alreadyTLMresp = true;
    Radio.TXdataBuffer[0] = TLM_PACKET;

    if (NextTelemetryType == ELRS_TELEMETRY_TYPE_LINK || !TelemetrySender.IsActive())
    {
        Radio.TXdataBuffer[1] = ELRS_TELEMETRY_TYPE_LINK;
        // The value in linkstatistics is "positivized" (inverted polarity)
        // and must be inverted on the TX side. Positive values are used
        // so save a bit to encode which antenna is in use
        Radio.TXdataBuffer[2] = link_stats.uplink_RSSI_1 | (antenna << 7);
        Radio.TXdataBuffer[3] = link_stats.uplink_RSSI_2 | (connectionHasModelMatch << 7);
        Radio.TXdataBuffer[4] = link_stats.uplink_SNR;
        Radio.TXdataBuffer[5] = link_stats.uplink_Link_quality;
        Radio.TXdataBuffer[6] = MspReceiver.GetCurrentConfirm() ? 1 : 0;

        NextTelemetryType = ELRS_TELEMETRY_TYPE_DATA;
        // Start the count at 1 because the next will be DATA and doing +1 before checking
        // against Max below is for some reason 10 bytes more code
        telemetryBurstCount = 1;
    }
    else
    {
        if (telemetryBurstCount < telemetryBurstMax)
        {
            telemetryBurstCount++;
        }
        else
        {
            NextTelemetryType = ELRS_TELEMETRY_TYPE_LINK;
        }

        TelemetrySender.GetCurrentPayload(&packageIndex, &maxLength, &data);
        Radio.TXdataBuffer[1] = (packageIndex << ELRS_TELEMETRY_SHIFT) + ELRS_TELEMETRY_TYPE_DATA;
        Radio.TXdataBuffer[2] = maxLength > 0 ? *data : 0;
        Radio.TXdataBuffer[3] = maxLength >= 1 ? *(data + 1) : 0;
        Radio.TXdataBuffer[4] = maxLength >= 2 ? *(data + 2) : 0;
        Radio.TXdataBuffer[5] = maxLength >= 3 ? *(data + 3): 0;
        Radio.TXdataBuffer[6] = maxLength >= 4 ? *(data + 4): 0;
    }

    uint16_t crc = ota_crc.calc(Radio.TXdataBuffer, 7, CRCInitializer);
    Radio.TXdataBuffer[0] |= (crc >> 6) & 0b11111100;
    Radio.TXdataBuffer[7] = crc & 0xFF;

    Radio.TXnb();
    return true;
}

void ICACHE_RAM_ATTR HandleFreqCorr(bool value)
{
    //DBGVLN(FreqCorrection);
    if (!value)
    {
        if (FreqCorrection < FreqCorrectionMax)
        {
            FreqCorrection += 1; //min freq step is ~ 61hz but don't forget we use FREQ_HZ_TO_REG_VAL so the units here are not hz!
        }
        else
        {
            FreqCorrection = FreqCorrectionMax;
            FreqCorrection = 0; //reset because something went wrong
            DBGLN("Max +FreqCorrection reached!");
        }
    }
    else
    {
        if (FreqCorrection > FreqCorrectionMin)
        {
            FreqCorrection -= 1; //min freq step is ~ 61hz
        }
        else
        {
            FreqCorrection = FreqCorrectionMin;
            FreqCorrection = 0; //reset because something went wrong
            DBGLN("Max -FreqCorrection reached!");
        }
    }
}

void ICACHE_RAM_ATTR updatePhaseLock()
{
    if (connectionState != disconnected)
    {
        PFDloop.calcResult();
        PFDloop.reset();
        RawOffset = PFDloop.getResult();
        Offset = LPF_Offset.update(RawOffset);
        OffsetDx = LPF_OffsetDx.update(RawOffset - prevRawOffset);

        if (RXtimerState == tim_locked && LQCalc.currentIsSet())
        {
            if (NonceRX % 8 == 0) //limit rate of freq offset adjustment slightly
            {
                if (Offset > 0)
                {
                    hwTimer.incFreqOffset();
                }
                else if (Offset < 0)
                {
                    hwTimer.decFreqOffset();
                }
            }
        }

        if (connectionState != connected)
        {
            hwTimer.phaseShift(RawOffset >> 1);
        }
        else
        {
            hwTimer.phaseShift(Offset >> 2);
        }

        prevOffset = Offset;
        prevRawOffset = RawOffset;
    }

    DBGVLN("%d:%d:%d:%d:%d", Offset, RawOffset, OffsetDx, hwTimer.FreqOffset, uplinkLQ);
}

void ICACHE_RAM_ATTR HWtimerCallbackTick() // this is 180 out of phase with the other callback, occurs mid-packet reception
{
    updatePhaseLock();
    NonceRX++;

    // if (!alreadyTLMresp && !alreadyFHSS && !LQCalc.currentIsSet()) // packet timeout AND didn't DIDN'T just hop or send TLM
    // {
    //     Radio.RXnb(); // put the radio cleanly back into RX in case of garbage data
    // }

    // Save the LQ value before the inc() reduces it by 1
    uplinkLQ = LQCalc.getLQ();
    link_stats.uplink_Link_quality = uplinkLQ;
    // Only advance the LQI period counter if we didn't send Telemetry this period
    if (!alreadyTLMresp)
        LQCalc.inc();

    alreadyTLMresp = false;
    alreadyFHSS = false;
}

//////////////////////////////////////////////////////////////
// flip to the other antenna
// no-op if GPIO_PIN_ANTENNA_SELECT not defined
static inline void switchAntenna()
{
#if defined(GPIO_PIN_ANTENNA_SELECT) && defined(USE_DIVERSITY)
    antenna = !antenna;
    (antenna == 0) ? LPF_UplinkRSSI0.reset() : LPF_UplinkRSSI1.reset(); // discard the outdated value after switching
    digitalWrite(GPIO_PIN_ANTENNA_SELECT, antenna);
#endif
}

static void ICACHE_RAM_ATTR updateDiversity()
{
#if defined(GPIO_PIN_ANTENNA_SELECT) && defined(USE_DIVERSITY)
    static int32_t prevRSSI;        // saved rssi so that we can compare if switching made things better or worse
    static int32_t antennaLQDropTrigger;
    static int32_t antennaRSSIDropTrigger;
    int32_t rssi = (antenna == 0) ? LPF_UplinkRSSI0.SmoothDataINT : LPF_UplinkRSSI1.SmoothDataINT;
    int32_t otherRSSI = (antenna == 0) ? LPF_UplinkRSSI1.SmoothDataINT : LPF_UplinkRSSI0.SmoothDataINT;

    //if rssi dropped by the amount of DIVERSITY_ANTENNA_RSSI_TRIGGER
    if ((rssi < (prevRSSI - DIVERSITY_ANTENNA_RSSI_TRIGGER)) && antennaRSSIDropTrigger >= DIVERSITY_ANTENNA_INTERVAL)
    {
        switchAntenna();
        antennaLQDropTrigger = 1;
        antennaRSSIDropTrigger = 0;
    }
    else if (rssi > prevRSSI || antennaRSSIDropTrigger < DIVERSITY_ANTENNA_INTERVAL)
    {
        prevRSSI = rssi;
        antennaRSSIDropTrigger++;
    }

    // if we didn't get a packet switch the antenna
    if (!LQCalc.currentIsSet() && antennaLQDropTrigger == 0)
    {
        switchAntenna();
        antennaLQDropTrigger = 1;
        antennaRSSIDropTrigger = 0;
    }
    else if (antennaLQDropTrigger >= DIVERSITY_ANTENNA_INTERVAL)
    {
        // We switched antenna on the previous packet, so we now have relatively fresh rssi info for both antennas.
        // We can compare the rssi values and see if we made things better or worse when we switched
        if (rssi < otherRSSI)
        {
            // things got worse when we switched, so change back.
            switchAntenna();
            antennaLQDropTrigger = 1;
            antennaRSSIDropTrigger = 0;
        }
        else
        {
            // all good, we can stay on the current antenna. Clear the flag.
            antennaLQDropTrigger = 0;
        }
    }
    else if (antennaLQDropTrigger > 0)
    {
        antennaLQDropTrigger ++;
    }
#endif
}

void ICACHE_RAM_ATTR HWtimerCallbackTock()
{
    PFDloop.intEvent(micros()); // our internal osc just fired

    updateDiversity();
    bool didFHSS = HandleFHSS();
    bool tlmSent = HandleSendTelemetryResponse();

    #if !defined(Regulatory_Domain_ISM_2400)
    if (!didFHSS && !tlmSent && LQCalc.currentIsSet())
    {
        HandleFreqCorr(Radio.GetFrequencyErrorbool());      // Adjusts FreqCorrection for RX freq offset
        Radio.SetPPMoffsetReg(FreqCorrection);
    }
    #else
        (void)didFHSS;
        (void)tlmSent;
    #endif /* Regulatory_Domain_ISM_2400 */

    #if defined(DEBUG_RX_SCOREBOARD)
    static bool lastPacketWasTelemetry = false;
    if (!LQCalc.currentIsSet() && !lastPacketWasTelemetry)
        DBGW(lastPacketCrcError ? '.' : '_');
    lastPacketCrcError = false;
    lastPacketWasTelemetry = tlmSent;
    #endif
}

void LostConnection()
{
    DBGLN("lost conn fc=%d fo=%d", FreqCorrection, hwTimer.FreqOffset);

    RFmodeCycleMultiplier = 1;
    connectionStatePrev = connectionState;
    connectionState = disconnected; //set lost connection
    RXtimerState = tim_disconnected;
    hwTimer.resetFreqOffset();
    FreqCorrection = 0;
    #if !defined(Regulatory_Domain_ISM_2400)
    Radio.SetPPMoffsetReg(0);
    #endif
    Offset = 0;
    OffsetDx = 0;
    RawOffset = 0;
    prevOffset = 0;
    GotConnectionMillis = 0;
    uplinkLQ = 0;
    LQCalc.reset();
    LPF_Offset.init(0);
    LPF_OffsetDx.init(0);
    alreadyTLMresp = false;
    alreadyFHSS = false;

    if (!InBindingMode)
    {
        while(micros() - PFDloop.getIntEventTime() > 250); // time it just after the tock()
        hwTimer.stop();
        SetRFLinkRate(ExpressLRS_nextAirRateIndex); // also sets to initialFreq
        Radio.RXnb();
    }
}

void ICACHE_RAM_ATTR TentativeConnection(unsigned long now)
{
    PFDloop.reset();
    connectionStatePrev = connectionState;
    connectionState = tentative;
    connectionHasModelMatch = false;
    RXtimerState = tim_disconnected;
    DBGLN("tentative conn");
    FreqCorrection = 0;
    Offset = 0;
    prevOffset = 0;
    LPF_Offset.init(0);
    RFmodeLastCycled = now; // give another 3 sec for lock to occur

    // The caller MUST call hwTimer.resume(). It is not done here because
    // the timer ISR will fire immediately and preempt any other code
}

void GotConnection(unsigned long now)
{
    if (connectionState == connected)
    {
        return; // Already connected
    }

#ifdef LOCK_ON_FIRST_CONNECTION
    LockRFmode = true;
#endif

    connectionStatePrev = connectionState;
    connectionState = connected; //we got a packet, therefore no lost connection
    RXtimerState = tim_tentative;
    GotConnectionMillis = now;
    #if defined(PLATFORM_ESP32) || defined(PLATFORM_ESP8266)
    webserverPreventAutoStart = true;
    #endif

    DBGLN("got conn");
}

static void ICACHE_RAM_ATTR ProcessRfPacket_RC()
{
    // Must be fully connected to process RC packets, prevents processing RC
    // during sync, where packets can be received before connection
    if (connectionState != connected)
        return;

  ProcessRcData((uint8_t*)&Radio.RXdataBuffer);
}

/**
 * Process the assembled MSP packet in MspData[]
 **/
static void ICACHE_RAM_ATTR MspReceiveComplete()
{
    if (MspData[7] == MSP_SET_RX_CONFIG && MspData[8] == MSP_ELRS_MODEL_ID)
    {
        UpdateModelMatch(MspData[9]);
    }
    else if (MspData[0] == MSP_ELRS_SET_RX_WIFI_MODE)
    {
        connectionState = wifiUpdate;
    }
    else
    {
        // No MSP data to the FC if no model match
        if (connectionHasModelMatch)
        {
            crsf_ext_header_t *receivedHeader = (crsf_ext_header_t *) MspData;

            if ((receivedHeader->dest_addr == CRSF_ADDRESS_BROADCAST || receivedHeader->dest_addr == CRSF_ADDRESS_CRSF_RECEIVER))
            {
                if (MspData[CRSF_TELEMETRY_TYPE_INDEX] == CRSF_FRAMETYPE_DEVICE_PING)
                {
                    uint8_t deviceInformation[DEVICE_INFORMATION_LENGTH];
                    telemetry.AppendTelemetryPackage(deviceInformation);
                }
            }
        }
    }

    MspReceiver.Unlock();
}

static void ICACHE_RAM_ATTR ProcessRfPacket_MSP()
{
    // Always examine MSP packets for bind information if in bind mode
    // [1] is the package index, first packet of the MSP
    if (InBindingMode && Radio.RXdataBuffer[1] == 1 && Radio.RXdataBuffer[2] == MSP_ELRS_BIND)
    {
        OnELRSBindMSP((uint8_t *)&Radio.RXdataBuffer[2]);
        return;
    }

    // Must be fully connected to process MSP, prevents processing MSP
    // during sync, where packets can be received before connection
    if (connectionState != connected)
        return;

    bool currentMspConfirmValue = MspReceiver.GetCurrentConfirm();
    MspReceiver.ReceiveData(Radio.RXdataBuffer[1], Radio.RXdataBuffer + 2);
    if (currentMspConfirmValue != MspReceiver.GetCurrentConfirm())
    {
        NextTelemetryType = ELRS_TELEMETRY_TYPE_LINK;
    }
    if (MspReceiver.HasFinishedData())
    {
        MspReceiveComplete();
    }
}

static bool ICACHE_RAM_ATTR ProcessRfPacket_SYNC(uint32_t now)
{
    // Verify the first two of three bytes of the binding ID, which should always match
    if (Radio.RXdataBuffer[4] != UID[3] || Radio.RXdataBuffer[5] != UID[4])
        return false;

    // The third byte will be XORed with inverse of the ModelId if ModelMatch is on
    // Only require the first 18 bits of the UID to match to establish a connection
    // but the last 6 bits must modelmatch before sending any data to the FC
    if ((Radio.RXdataBuffer[6] & ~MODELMATCH_MASK) != (UID[5] & ~MODELMATCH_MASK))
        return false;

    LastSyncPacket = now;
#if defined(DEBUG_RX_SCOREBOARD)
    DBGW('s');
#endif

    // Will change the packet air rate in loop() if this changes
    ExpressLRS_nextAirRateIndex = (Radio.RXdataBuffer[3] & 0b11000000) >> 6;
    // Update switch mode encoding immediately
    OtaSwitchModeCurrent = ((OtaSwitchMode_e)((Radio.RXdataBuffer[3] & 0b00000110) >> 1));
    // Update TLM ratio
    expresslrs_tlm_ratio_e TLMrateIn = (expresslrs_tlm_ratio_e)((Radio.RXdataBuffer[3] & 0b00111000) >> 3);
    if (ExpressLRS_currAirRate_Modparams->TLMinterval != TLMrateIn)
    {
        DBGLN("New TLMrate: %d", TLMrateIn);
        ExpressLRS_currAirRate_Modparams->TLMinterval = TLMrateIn;
        telemBurstValid = false;
    }

    // modelId = 0xff indicates modelMatch is disabled, the XOR does nothing in that case
    uint8_t modelXor = (~config.GetModelId()) & MODELMATCH_MASK;
    bool modelMatched = Radio.RXdataBuffer[6] == (UID[5] ^ modelXor);
    DBGVLN("MM %u=%u %d", Radio.RXdataBuffer[6], UID[5], modelMatched);

    if (connectionState == disconnected
        || NonceRX != Radio.RXdataBuffer[2]
        || FHSSgetCurrIndex() != Radio.RXdataBuffer[1]
        || connectionHasModelMatch != modelMatched)
    {
        //DBGLN("\r\n%ux%ux%u", NonceRX, Radio.RXdataBuffer[2], Radio.RXdataBuffer[1]);
        FHSSsetCurrIndex(Radio.RXdataBuffer[1]);
        NonceRX = Radio.RXdataBuffer[2];
        TentativeConnection(now);
        // connectionHasModelMatch must come after TentativeConnection, which resets it
        connectionHasModelMatch = modelMatched;
        return true;
    }

    return false;
}

void ICACHE_RAM_ATTR ProcessRFPacket()
{
    beginProcessing = micros();

    uint8_t type = Radio.RXdataBuffer[0] & 0b11;
    uint16_t inCRC = (((uint16_t)(Radio.RXdataBuffer[0] & 0b11111100)) << 6) | Radio.RXdataBuffer[7];

    // For smHybrid the CRC only has the packet type in byte 0
    // For smHybridWide the FHSS slot is added to the CRC in byte 0 on RC_DATA_PACKETs
    if (type != RC_DATA_PACKET || OtaSwitchModeCurrent != smHybridWide)
    {
        Radio.RXdataBuffer[0] = type;
    }
    else
    {
        uint8_t NonceFHSSresult = NonceRX % ExpressLRS_currAirRate_Modparams->FHSShopInterval;
        Radio.RXdataBuffer[0] = type | (NonceFHSSresult << 2);
    }
    uint16_t calculatedCRC = ota_crc.calc(Radio.RXdataBuffer, 7, CRCInitializer);

    if (inCRC != calculatedCRC)
    {
        DBGV("CRC error: ");
        for (int i = 0; i < 8; i++)
        {
            DBGV("%x,", Radio.RXdataBuffer[i]);
        }
        DBGVCR;
        #if defined(DEBUG_RX_SCOREBOARD)
            lastPacketCrcError = true;
        #endif
        return;
    }
    PFDloop.extEvent(beginProcessing + PACKET_TO_TOCK_SLACK);

    bool doStartTimer = false;
    unsigned long now = millis();

    LastValidPacket = now;

    switch (type)
    {
    case RC_DATA_PACKET: //Standard RC Data Packet
        ProcessRfPacket_RC();
        break;
    case MSP_DATA_PACKET:
        ProcessRfPacket_MSP();
        break;
    case TLM_PACKET: //telemetry packet from master
        // not implimented yet
        break;
    case SYNC_PACKET: //sync packet from master
        doStartTimer = ProcessRfPacket_SYNC(now) && !InBindingMode;
        break;
    default: // code to be executed if n doesn't match any cases
        break;
    }

    // Store the LQ/RSSI/Antenna
    getRFlinkInfo();
    // Received a packet, that's the definition of LQ
    LQCalc.add();
    // Extend sync duration since we've received a packet at this rate
    // but do not extend it indefinitely
    RFmodeCycleMultiplier = RFmodeCycleMultiplierSlow;

    doneProcessing = micros();
#if defined(DEBUG_RX_SCOREBOARD)
    if (type != SYNC_PACKET) DBGW(connectionHasModelMatch ? 'R' : 'r');
#endif
    if (doStartTimer)
        hwTimer.resume(); // will throw an interrupt immediately
}

void ICACHE_RAM_ATTR RXdoneISR()
{
    ProcessRFPacket();
}

void ICACHE_RAM_ATTR TXdoneISR()
{
    Radio.RXnb();
#if defined(DEBUG_RX_SCOREBOARD)
    DBGW('T');
#endif
}

static void setupSerial()
{
  Serial.begin(115200);
}

static void setupConfigAndPocCheck()
{
    eeprom.Begin();
    config.SetStorageProvider(&eeprom); // Pass pointer to the Config class for access to storage
    config.Load();

    DBGLN("ModelId=%u", config.GetModelId());

#ifndef MY_UID
    // Increment the power on counter in eeprom
    config.SetPowerOnCounter(config.GetPowerOnCounter() + 1);
    config.Commit();

    // If we haven't reached our binding mode power cycles
    // and we've been powered on for 2s, reset the power on counter
    if (config.GetPowerOnCounter() < 3)
    {
        delay(2000);
        config.SetPowerOnCounter(0);
        config.Commit();
    }
#endif
}

static void setupGpio()
{
#if defined(GPIO_PIN_ANTENNA_SELECT)
    pinMode(GPIO_PIN_ANTENNA_SELECT, OUTPUT);
    digitalWrite(GPIO_PIN_ANTENNA_SELECT, LOW);
#endif
#if defined(TARGET_RX_FM30_MINI)
    pinMode(GPIO_PIN_UART1TX_INVERT, OUTPUT);
    digitalWrite(GPIO_PIN_UART1TX_INVERT, LOW);
#endif
}

static void setupBindingFromConfig()
{
// Use the user defined binding phase if set,
// otherwise use the bind flag and UID in eeprom for UID
#if !defined(MY_UID)
    // Check the byte that indicates if RX has been bound
    if (config.GetIsBound())
    {
        DBGLN("RX has been bound previously, reading the UID from eeprom...");
        const uint8_t* storedUID = config.GetUID();
        for (uint8_t i = 0; i < UID_LEN; ++i)
        {
            UID[i] = storedUID[i];
        }
        DBGLN("UID = %d, %d, %d, %d, %d, %d", UID[0], UID[1], UID[2], UID[3], UID[4], UID[5]);
        CRCInitializer = (UID[4] << 8) | UID[5];
    }
#endif
}

static void setupRadio()
{
    Radio.currFreq = GetInitialFreq();
#if !defined(Regulatory_Domain_ISM_2400)
    //Radio.currSyncWord = UID[3];
#endif
    bool init_success = Radio.Begin();
    POWERMGNT.init();
    if (!init_success)
    {
        DBGLN("Failed to detect RF chipset!!!");
        connectionState = radioFailed;
        return;
    }

    // Set transmit power to maximum
    POWERMGNT.setPower(MaxPower);

    Radio.RXdoneCallback = &RXdoneISR;
    Radio.TXdoneCallback = &TXdoneISR;

    SetRFLinkRate(RATE_DEFAULT);
    RFmodeCycleMultiplier = 1;
}

static void updateTelemetryBurst()
{
    if (telemBurstValid)
        return;
    telemBurstValid = true;

    uint32_t hz = RateEnumToHz(ExpressLRS_currAirRate_Modparams->enum_rate);
    uint32_t ratiodiv = TLMratioEnumToValue(ExpressLRS_currAirRate_Modparams->TLMinterval);
    // telemInterval = 1000 / (hz / ratiodiv);
    // burst = TELEM_MIN_LINK_INTERVAL / telemInterval;
    // This ^^^ rearranged to preserve precision vvv
    telemetryBurstMax = TELEM_MIN_LINK_INTERVAL * hz / ratiodiv / 1000U;

    // Reserve one slot for LINK telemetry
    if (telemetryBurstMax > 1)
        --telemetryBurstMax;
    else
        telemetryBurstMax = 1;
    //DBGLN("TLMburst: %d", telemetryBurstMax);

    // Notify the sender to adjust its expected throughput
    TelemetrySender.UpdateTelemetryRate(hz, ratiodiv, telemetryBurstMax);
}

/* If not connected will rotate through the RF modes looking for sync
 * and blink LED
 */
static void cycleRfMode(unsigned long now)
{
    if (connectionState == connected || connectionState == wifiUpdate || InBindingMode)
        return;

    // Actually cycle the RF mode if not LOCK_ON_FIRST_CONNECTION
    if (LockRFmode == false && (now - RFmodeLastCycled) > (cycleInterval * RFmodeCycleMultiplier))
    {
        RFmodeLastCycled = now;
        LastSyncPacket = now;           // reset this variable
        SetRFLinkRate(scanIndex % RATE_MAX); // switch between rates
        SendLinkStatstoFCintervalLastSent = now;
        LQCalc.reset();
        // Display the current air rate to the user as an indicator something is happening
        INFOLN("%d", ExpressLRS_currAirRate_Modparams->interval);
        scanIndex++;
        delay(100);
        Radio.RXnb();

        // Switch to FAST_SYNC if not already in it (won't be if was just connected)
        RFmodeCycleMultiplier = 1;
    } // if time to switch RF mode
}

static void servosUpdate(unsigned long now)
{
}

static void updateBindingMode()
{
    // If the eeprom is indicating that we're not bound
    // and we're not already in binding mode, enter binding
    if (!config.GetIsBound() && !InBindingMode)
    {
        INFOLN("RX has not been bound, enter binding mode...");
        EnterBindingMode();
    }
    // If in binding mode and the bind packet has come in, leave binding mode
    else if (config.GetIsBound() && InBindingMode)
    {
        ExitBindingMode();
    }

#ifndef MY_UID
    // If the power on counter is >=3, enter binding and clear counter
    if (config.GetPowerOnCounter() >= 3)
    {
        config.SetPowerOnCounter(0);
        config.Commit();

        INFOLN("Power on counter >=3, enter binding mode...");
        EnterBindingMode();
    }
#endif
}

#if defined(PLATFORM_ESP8266)
// Called from core's user_rf_pre_init() function (which is called by SDK) before setup()
RF_PRE_INIT()
{
    // Set whether the chip will do RF calibration or not when power up.
    // I believe the Arduino core fakes this (byte 114 of phy_init_data.bin)
    // to be 1, but the TX power calibration can pull over 300mA which can
    // lock up receivers built with a underspeced LDO (such as the EP2 "SDG")
    // Option 2 is just VDD33 measurement
    #if defined(RF_CAL_MODE)
    system_phy_set_powerup_option(RF_CAL_MODE);
    #else
    system_phy_set_powerup_option(2);
    #endif
}
#endif

void setup()
{
    setupGpio();
    // serial setup must be done before anything as some libs write
    // to the serial port and they'll block if the buffer fills
    setupSerial();
    // Init EEPROM and load config, checking powerup count
    setupConfigAndPocCheck();

    devicesInit(ui_devices, ARRAY_SIZE(ui_devices));
    setupBindingFromConfig();

    FHSSrandomiseFHSSsequence(uidMacSeedGet());

    setupRadio();

    if (connectionState != radioFailed)
    {
        // RFnoiseFloor = MeasureNoiseFloor(); //TODO move MeasureNoiseFloor to driver libs
        // DBGLN("RF noise floor: %d dBm", RFnoiseFloor);

        hwTimer.callbackTock = &HWtimerCallbackTock;
        hwTimer.callbackTick = &HWtimerCallbackTick;

        MspReceiver.SetDataToReceive(ELRS_MSP_BUFFER, MspData, ELRS_MSP_BYTES_PER_CALL);
        Radio.RXnb();
        hwTimer.init();
    }

    devicesStart();
}

void loop()
{
    unsigned long now = millis();

    devicesUpdate(now);

    #if defined(PLATFORM_ESP8266) && defined(AUTO_WIFI_ON_INTERVAL)
    // If the reboot time is set and the current time is past the reboot time then reboot.
    if (rebootTime != 0 && now > rebootTime) {
        ESP.restart();
    }
    #endif

    if (connectionState > MODE_STATES)
    {
        return;
    }

    if ((connectionState != disconnected) && (ExpressLRS_currAirRate_Modparams->index != ExpressLRS_nextAirRateIndex)){ // forced change
        DBGLN("Req air rate change %u->%u", ExpressLRS_currAirRate_Modparams->index, ExpressLRS_nextAirRateIndex);
        LostConnection();
        LastSyncPacket = now;           // reset this variable to stop rf mode switching and add extra time
        RFmodeLastCycled = now;         // reset this variable to stop rf mode switching and add extra time
    }

    if (connectionState == tentative && (now - LastSyncPacket > ExpressLRS_currAirRate_RFperfParams->RxLockTimeoutMs))
    {
        LostConnection();
        DBGLN("Bad sync, aborting");
        RFmodeLastCycled = now;
        LastSyncPacket = now;
    }

    cycleRfMode(now);
    servosUpdate(now);

    uint32_t localLastValidPacket = LastValidPacket; // Required to prevent race condition due to LastValidPacket getting updated from ISR
    if ((connectionState == disconnectPending) ||
        ((connectionState == connected) && ((int32_t)ExpressLRS_currAirRate_RFperfParams->DisconnectTimeoutMs < (int32_t)(now - localLastValidPacket)))) // check if we lost conn.
    {
        LostConnection();
    }

    if ((connectionState == tentative) && (abs(OffsetDx) <= 10) && (Offset < 100) && (LQCalc.getLQRaw() > minLqForChaos())) //detects when we are connected
    {
        GotConnection(now);
    }


    if ((RXtimerState == tim_tentative) && ((now - GotConnectionMillis) > ConsiderConnGoodMillis) && (abs(OffsetDx) <= 5))
    {
        RXtimerState = tim_locked;
        DBGLN("Timer locked");
    }

    uint8_t *nextPayload = 0;
    uint8_t nextPlayloadSize = 0;
    if (!TelemetrySender.IsActive() && telemetry.GetNextPayload(&nextPlayloadSize, &nextPayload))
    {
        TelemetrySender.SetDataToTransmit(nextPlayloadSize, nextPayload, ELRS_TELEMETRY_BYTES_PER_CALL);
    }
    updateTelemetryBurst();
    updateBindingMode();
}

struct bootloader {
    uint32_t key;
    uint32_t reset_type;
};

void reset_into_bootloader(void)
{

#if defined(PLATFORM_STM32)
    delay(100);
    DBGLN("Jumping to Bootloader...");
    delay(100);

    /** Write command for firmware update.
     *
     * Bootloader checks this memory area (if newer enough) and
     * perpare itself for fw update. Otherwise it skips the check
     * and starts ELRS firmware immediately
     */
    extern __IO uint32_t _bootloader_data;
    volatile struct bootloader * blinfo = ((struct bootloader*)&_bootloader_data) + 0;
    blinfo->key = 0x454c5253; // ELRS
    blinfo->reset_type = 0xACDC;

    HAL_NVIC_SystemReset();
#elif defined(PLATFORM_ESP8266)
    delay(100);
    ESP.rebootIntoUartDownloadMode();
#endif
}

void EnterBindingMode()
{
    if ((connectionState == connected) || InBindingMode) {
        // Don't enter binding if:
        // - we're already connected
        // - we're already binding
        DBGLN("Cannot enter binding mode!");
        return;
    }

    // Set UID to special binding values
    UID[0] = BindingUID[0];
    UID[1] = BindingUID[1];
    UID[2] = BindingUID[2];
    UID[3] = BindingUID[3];
    UID[4] = BindingUID[4];
    UID[5] = BindingUID[5];

    CRCInitializer = 0;
    config.SetIsBound(false);
    InBindingMode = true;

    // Start attempting to bind
    // Lock the RF rate and freq while binding
    SetRFLinkRate(RATE_BINDING);
    Radio.SetFrequencyReg(GetInitialFreq());
    // If the Radio Params (including InvertIQ) parameter changed, need to restart RX to take effect
    Radio.RXnb();

    DBGLN("Entered binding mode at freq = %d", Radio.currFreq);
    devicesTriggerEvent();
}

void ExitBindingMode()
{
    if (!InBindingMode)
    {
        // Not in binding mode
        DBGLN("Cannot exit binding mode, not in binding mode!");
        return;
    }

    // Prevent any new packets from coming in
    Radio.SetTxIdleMode();
    LostConnection();
    // Write the values to eeprom
    config.Commit();

    CRCInitializer = (UID[4] << 8) | UID[5];
    FHSSrandomiseFHSSsequence(uidMacSeedGet());

    #if defined(PLATFORM_ESP32) || defined(PLATFORM_ESP8266)
    webserverPreventAutoStart = true;
    #endif

    // Force RF cycling to start at the beginning immediately
    scanIndex = RATE_MAX;
    RFmodeLastCycled = 0;

    // Do this last as LostConnection() will wait for a tock that never comes
    // if we're in binding mode
    InBindingMode = false;
    DBGLN("Exiting binding mode");
    devicesTriggerEvent();
}

void ICACHE_RAM_ATTR OnELRSBindMSP(uint8_t* packet)
{
    for (int i = 1; i <=4; i++)
    {
        UID[i + 1] = packet[i];
    }

    DBGLN("New UID = %d, %d, %d, %d, %d, %d", UID[0], UID[1], UID[2], UID[3], UID[4], UID[5]);

    // Set new UID in eeprom
    config.SetUID(UID);

    // Set eeprom byte to indicate RX is bound
    config.SetIsBound(true);

    // EEPROM commit will happen on the main thread in ExitBindingMode()
}

void UpdateModelMatch(uint8_t model)
{
    DBGLN("Set ModelId=%u", model);

    config.SetModelId(model);
    if (config.IsModified())
    {
        config.Commit();
        // This will be called from ProcessRFPacket(), schedule a disconnect
        // in the main loop once the ISR has exited
        connectionState = disconnectPending;
    }
}
