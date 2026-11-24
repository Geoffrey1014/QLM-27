/* QLM seed slice: drivers/staging/rtl8192u/r8192U_core.c @ 09acf29c8246^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef struct rt_firmware_s { int dummy; } rt_firmware;

struct Stats { int dummy; };

struct sk_buff_head { int dummy; };

struct ieee80211_network {
    int beacon_interval;
};

struct ieee80211_device {
    int mode;
    int iw_mode;
    int ieee_up;
    int rts;
    int rate;
    int short_slot;
    int FwRWRF;
    struct ieee80211_network current_network;
    unsigned int softmac_features;
    int active_scan;
    unsigned int modulation;
    int host_encrypt;
    int host_decrypt;
    void *start_send_beacons;
    void *stop_send_beacons;
    void *softmac_hard_start_xmit;
    void *set_chan;
    void *link_change;
    void *softmac_data_hard_start_xmit;
    void *data_hard_stop;
    void *data_hard_resume;
    int init_wmmparam_flag;
    int fts;
    void *check_nic_enough_desc;
    int tx_headroom;
    int qos_support;
    void *SetBWModeHandler;
    void *handle_assoc_response;
    void *handle_beacon;
    void *GetNmodeSupportBySecCfg;
    void *GetHalfNmodeSupportByAPsHandler;
    void *SetWirelessMode;
    void *InitialGainHandler;
    struct sk_buff_head skb_waitQ[16];
    struct sk_buff_head skb_aggQ[16];
    struct sk_buff_head skb_drv_aggQ[16];
};

struct timer_list_x { int dummy; };

struct r8192_priv {
    int card_8192;
    int chan;
    struct ieee80211_device *ieee80211;
    int retry_rts;
    int retry_data;
    int promisc;
    int CckPwEnl;
    int IrpPendingCount;
    int ResetProgress;
    bool bForcedSilentReset;
    bool bDisableNormalResetCheck;
    bool force_reset;
    int card_type;
    int ShortRetryLimit;
    int LongRetryLimit;
    int EarlyRxThreshold;
    int enable_gpio0;
    u32 TransmitConfig;
    u32 ReceiveConfig;
    int AcmControl;
    void *pFirmware;
    struct sk_buff_head rx_queue;
    struct sk_buff_head skb_queue;
    void *rf_set_chan;
    struct Stats stats;
    u8 txqueue_to_outpipemap[9];
    struct timer_list_x watch_dog_timer;
};

struct net_device {
    unsigned int flags;
};

extern void *ieee80211_priv(struct net_device *dev);

#define NIC_8192U 0
#define WIRELESS_MODE_AUTO 0
#define IW_MODE_INFRA 0
#define DEFAULT_RETRY_RTS 0
#define DEFAULT_RETRY_DATA 0
#define DEFAULT_RTS_THRESHOLD 2347
#define IFF_PROMISC 0x100
#define RESET_TYPE_NORESET 0
#define DEFAULT_BEACONINTERVAL 100
#define IEEE_SOFTMAC_SCAN 0x1
#define IEEE_SOFTMAC_ASSOCIATE 0x2
#define IEEE_SOFTMAC_PROBERQ 0x4
#define IEEE_SOFTMAC_PROBERS 0x8
#define IEEE_SOFTMAC_TX_QUEUE 0x10
#define IEEE_SOFTMAC_BEACONS 0x20
#define IEEE80211_CCK_MODULATION 0x1
#define IEEE80211_OFDM_MODULATION 0x2
#define DEFAULT_FRAG_THRESHOLD 2342
#define TX_PACKET_SHIFT_BYTES 0
#define TCR_MXDMA_OFFSET 21
#define TCR_MXDMA_2048 7
#define TCR_SRL_OFFSET 8
#define TCR_LRL_OFFSET 0
#define TCR_SAT 0x80000000
#define RCR_AMF 0x02000000
#define RCR_ADF 0x00800000
#define RCR_ACF 0x00080000
#define RCR_AB 0x00000008
#define RCR_AM 0x00000004
#define RCR_APM 0x00000002
#define RCR_MXDMA_OFFSET 8
#define RX_FIFO_THRESHOLD_SHIFT 13
#define RCR_ONLYERLPKT 0x80000000
#define USB 1
#define MAX_QUEUE_SIZE 16
#define GFP_KERNEL 0
#define ENOMEM 12

extern void *kzalloc(unsigned long size, int flags);
extern void skb_queue_head_init(struct sk_buff_head *list);
extern void *memset(void *s, int c, unsigned long n);
extern void *memcpy(void *dest, const void *src, unsigned long n);

extern int rtl8192_hard_start_xmit(void);
extern int rtl8192_set_chan(void);
extern int rtl8192_link_change(void);
extern int rtl8192_hard_data_xmit(void);
extern int rtl8192_data_hard_stop(void);
extern int rtl8192_data_hard_resume(void);
extern int check_nic_enough_desc(void);
extern int rtl8192_SetBWMode(void);
extern int rtl8192_handle_assoc_response(void);
extern int rtl8192_handle_beacon(void);
extern int GetNmodeSupportBySecCfg8192(void);
extern int GetHalfNmodeSupportByAPs819xUsb(void);
extern int rtl8192_SetWirelessMode(void);
extern int InitialGain819xUsb(void);
extern int rtl8192_phy_SwChnl(void);

extern void rtl8192_init_priv_lock(struct r8192_priv *priv);
extern void rtl8192_init_priv_task(struct net_device *dev);
extern void rtl8192_get_eeprom_size(struct net_device *dev);
extern int rtl8192_read_eeprom_info(struct net_device *dev);
extern void rtl8192_get_channel_map(struct net_device *dev);
extern void init_hal_dm(struct net_device *dev);
extern void watch_dog_timer_callback(struct timer_list_x *t);
extern int rtl8192_usb_initendpoints(struct net_device *dev);

#define timer_setup(timer, callback, flags) do { (void)(timer); (void)(callback); (void)(flags); } while (0)
#define DMESG(fmt, ...) do { } while (0)

/* ---- verbatim kernel code ---- */
static void rtl8192_init_priv_variable(struct net_device *dev)
{
	struct r8192_priv *priv = ieee80211_priv(dev);
	u8 i;

	priv->card_8192 = NIC_8192U;
	priv->chan = 1; /* set to channel 1 */
	priv->ieee80211->mode = WIRELESS_MODE_AUTO; /* SET AUTO */
	priv->ieee80211->iw_mode = IW_MODE_INFRA;
	priv->ieee80211->ieee_up = 0;
	priv->retry_rts = DEFAULT_RETRY_RTS;
	priv->retry_data = DEFAULT_RETRY_DATA;
	priv->ieee80211->rts = DEFAULT_RTS_THRESHOLD;
	priv->ieee80211->rate = 110; /* 11 mbps */
	priv->ieee80211->short_slot = 1;
	priv->promisc = (dev->flags & IFF_PROMISC) ? 1 : 0;
	priv->CckPwEnl = 6;
	/* for silent reset */
	priv->IrpPendingCount = 1;
	priv->ResetProgress = RESET_TYPE_NORESET;
	priv->bForcedSilentReset = false;
	priv->bDisableNormalResetCheck = false;
	priv->force_reset = false;

	/* we don't use FW read/write RF until stable firmware is available. */
	priv->ieee80211->FwRWRF = 0;
	priv->ieee80211->current_network.beacon_interval =
		DEFAULT_BEACONINTERVAL;
	priv->ieee80211->softmac_features  = IEEE_SOFTMAC_SCAN |
		IEEE_SOFTMAC_ASSOCIATE | IEEE_SOFTMAC_PROBERQ |
		IEEE_SOFTMAC_PROBERS | IEEE_SOFTMAC_TX_QUEUE |
		IEEE_SOFTMAC_BEACONS;

	priv->ieee80211->active_scan = 1;
	priv->ieee80211->modulation =
		IEEE80211_CCK_MODULATION | IEEE80211_OFDM_MODULATION;
	priv->ieee80211->host_encrypt = 1;
	priv->ieee80211->host_decrypt = 1;
	priv->ieee80211->start_send_beacons = NULL;
	priv->ieee80211->stop_send_beacons = NULL;
	priv->ieee80211->softmac_hard_start_xmit = rtl8192_hard_start_xmit;
	priv->ieee80211->set_chan = rtl8192_set_chan;
	priv->ieee80211->link_change = rtl8192_link_change;
	priv->ieee80211->softmac_data_hard_start_xmit = rtl8192_hard_data_xmit;
	priv->ieee80211->data_hard_stop = rtl8192_data_hard_stop;
	priv->ieee80211->data_hard_resume = rtl8192_data_hard_resume;
	priv->ieee80211->init_wmmparam_flag = 0;
	priv->ieee80211->fts = DEFAULT_FRAG_THRESHOLD;
	priv->ieee80211->check_nic_enough_desc = check_nic_enough_desc;
	priv->ieee80211->tx_headroom = TX_PACKET_SHIFT_BYTES;
	priv->ieee80211->qos_support = 1;

	priv->ieee80211->SetBWModeHandler = rtl8192_SetBWMode;
	priv->ieee80211->handle_assoc_response = rtl8192_handle_assoc_response;
	priv->ieee80211->handle_beacon = rtl8192_handle_beacon;

	priv->ieee80211->GetNmodeSupportBySecCfg = GetNmodeSupportBySecCfg8192;
	priv->ieee80211->GetHalfNmodeSupportByAPsHandler =
		GetHalfNmodeSupportByAPs819xUsb;
	priv->ieee80211->SetWirelessMode = rtl8192_SetWirelessMode;

	priv->ieee80211->InitialGainHandler = InitialGain819xUsb;
	priv->card_type = USB;
#ifdef TO_DO_LIST
	if (Adapter->bInHctTest) {
		pHalData->ShortRetryLimit = 7;
		pHalData->LongRetryLimit = 7;
	}
#endif
	priv->ShortRetryLimit = 0x30;
	priv->LongRetryLimit = 0x30;
	priv->EarlyRxThreshold = 7;
	priv->enable_gpio0 = 0;
	priv->TransmitConfig =
		/* Max DMA Burst Size per Tx DMA Burst, 7: reserved. */
		(TCR_MXDMA_2048 << TCR_MXDMA_OFFSET)	  |
		/* Short retry limit */
		(priv->ShortRetryLimit << TCR_SRL_OFFSET) |
		/* Long retry limit */
		(priv->LongRetryLimit << TCR_LRL_OFFSET)  |
		/* FALSE: HW provides PLCP length and LENGEXT
		 * TRUE: SW provides them
		 */
		(false ? TCR_SAT : 0);
#ifdef TO_DO_LIST
	if (Adapter->bInHctTest)
		pHalData->ReceiveConfig =
			pHalData->CSMethod |
			/* accept management/data */
			RCR_AMF | RCR_ADF |
			/* accept control frame for SW
			 * AP needs PS-poll
			 */
			RCR_ACF |
			/* accept BC/MC/UC */
			RCR_AB | RCR_AM | RCR_APM |
			/* accept ICV/CRC error
			 * packet
			 */
			RCR_AICV | RCR_ACRC32 |
			/* Max DMA Burst Size per Tx
			 * DMA Burst, 7: unlimited.
			 */
			((u32)7 << RCR_MXDMA_OFFSET) |
			/* Rx FIFO Threshold,
			 * 7: No Rx threshold.
			 */
			(pHalData->EarlyRxThreshold << RCR_FIFO_OFFSET) |
			(pHalData->EarlyRxThreshold == 7 ? RCR_OnlyErlPkt : 0);
	else

#endif
	priv->ReceiveConfig	=
		/* accept management/data */
		RCR_AMF | RCR_ADF |
		/* accept control frame for SW AP needs PS-poll */
		RCR_ACF |
		/* accept BC/MC/UC */
		RCR_AB | RCR_AM | RCR_APM |
		/* Max DMA Burst Size per Rx DMA Burst, 7: unlimited. */
		((u32)7 << RCR_MXDMA_OFFSET) |
		/* Rx FIFO Threshold, 7: No Rx threshold. */
		(priv->EarlyRxThreshold << RX_FIFO_THRESHOLD_SHIFT) |
		(priv->EarlyRxThreshold == 7 ? RCR_ONLYERLPKT : 0);

	priv->AcmControl = 0;
	priv->pFirmware = kzalloc(sizeof(rt_firmware), GFP_KERNEL);

	/* rx related queue */
	skb_queue_head_init(&priv->rx_queue);
	skb_queue_head_init(&priv->skb_queue);

	/* Tx related queue */
	for (i = 0; i < MAX_QUEUE_SIZE; i++)
		skb_queue_head_init(&priv->ieee80211->skb_waitQ[i]);
	for (i = 0; i < MAX_QUEUE_SIZE; i++)
		skb_queue_head_init(&priv->ieee80211->skb_aggQ[i]);
	for (i = 0; i < MAX_QUEUE_SIZE; i++)
		skb_queue_head_init(&priv->ieee80211->skb_drv_aggQ[i]);
	priv->rf_set_chan = rtl8192_phy_SwChnl;
}

static short rtl8192_init(struct net_device *dev)
{
	struct r8192_priv *priv = ieee80211_priv(dev);
	int err;

	memset(&(priv->stats), 0, sizeof(struct Stats));
	memset(priv->txqueue_to_outpipemap, 0, 9);
#ifdef PIPE12
	{
		int i = 0;
		u8 queuetopipe[] = {3, 2, 1, 0, 4, 8, 7, 6, 5};

		memcpy(priv->txqueue_to_outpipemap, queuetopipe, 9);
	}
#else
	{
		u8 queuetopipe[] = {3, 2, 1, 0, 4, 4, 0, 4, 4};

		memcpy(priv->txqueue_to_outpipemap, queuetopipe, 9);
	}
#endif
	rtl8192_init_priv_variable(dev);
	rtl8192_init_priv_lock(priv);
	rtl8192_init_priv_task(dev);
	rtl8192_get_eeprom_size(dev);
	err = rtl8192_read_eeprom_info(dev);
	if (err) {
		DMESG("Reading EEPROM info failed");
		return err;
	}
	rtl8192_get_channel_map(dev);
	init_hal_dm(dev);
	timer_setup(&priv->watch_dog_timer, watch_dog_timer_callback, 0);
	if (rtl8192_usb_initendpoints(dev) != 0) {
		DMESG("Endopoints initialization failed");
		return -ENOMEM;
	}

	return 0;
}
