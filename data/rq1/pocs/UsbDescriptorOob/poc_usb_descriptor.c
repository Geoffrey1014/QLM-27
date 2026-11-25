/*
 * PoC for the "USB descriptor blob-walk OOB" pattern (CWE-125 / CWE-787).
 *
 * NOTE: this file must live under sound/usb/ (or drivers/usb/, ...) relative to the
 * CodeQL source root, because UsbDescriptorOob.ql restricts itself to USB driver paths.
 *
 * Mirrors the shapes of the ground-truth fixes:
 *   fb4e2a6e8f28a  ALSA: usb-audio: Fix out-of-bounds read in snd_usb_get_audioformat_uac3()
 *                  (device-supplied wLength used as a size without checking it is large enough)
 *   a3dd4d63eeb45, 5570ad1423ee6, fe7f7ac8e0c70  (same descriptor-length family)
 *
 * And the in-tree finding it must flag (RQ1 #49):
 *   sound/usb/midi.c::find_usb_ijack
 *     sz = USB_DT_MIDI_OUT_SIZE(outjd->bNrInputPins);
 *     if (outjd->bLength < sz) goto next;   <- compares against ANOTHER device field
 *     return *(extra + sz - 1);             <- can read past extralen
 *
 * *_buggy : device-controlled length/count used as index / ptr offset / copy size without a
 *          check against the bytes remaining in the blob             -> MUST be flagged.
 * *_fixed : the same use, bounded by extralen / buflen / an end pointer -> MUST be spared.
 */
#include <stddef.h>

typedef unsigned char u8;
typedef unsigned short u16;

void *memcpy(void *dst, const void *src, size_t n);

/* ---- minimal USB core fakes ---- */
struct usb_host_interface {
	int desc;
	unsigned char *extra;	/* raw descriptor blob supplied by the device */
	int extralen;		/* number of bytes actually in the blob */
};

struct usb_descriptor_header {
	u8 bLength;
	u8 bDescriptorType;
};

#define USB_DT_CS_INTERFACE 0x24
#define UAC_MIDI_OUT_JACK 0x03

struct usb_midi_out_jack_descriptor {
	u8 bLength;
	u8 bDescriptorType;
	u8 bDescriptorSubtype;
	u8 bJackType;
	u8 bJackID;
	u8 bNrInputPins;	/* device-controlled count */
	u8 pins[];
};

#define USB_DT_MIDI_OUT_SIZE(p) (7 + 2 * (p))

struct uac3_cluster_header {
	u8 bLength;
	u8 bDescriptorType;
	u16 wLength;		/* device-controlled total length */
	u8 bNrChannels;		/* device-controlled count */
	u8 data[];
};

/* ================================================================== *
 *  BUG cases
 * ================================================================== */

/* Finding #49: pin count bounded only by another device field (bLength). */
int find_ijack_buggy(struct usb_host_interface *hostif, u8 jack_id)
{
	unsigned char *extra = hostif->extra;
	int extralen = hostif->extralen;
	struct usb_midi_out_jack_descriptor *outjd;
	size_t sz;

	while (extralen > 4) {
		outjd = (struct usb_midi_out_jack_descriptor *)extra;
		if (outjd->bDescriptorSubtype == UAC_MIDI_OUT_JACK &&
		    outjd->bJackID == jack_id) {
			sz = USB_DT_MIDI_OUT_SIZE(outjd->bNrInputPins);
			if (outjd->bLength < sz)
				goto next;
			return *(extra + sz - 1);	/* OOB read past extralen */
		}
next:
		extralen -= extra[0];
		extra += extra[0];
	}
	return -1;
}

/* Seed fb4e2a6e8f28a shape: device wLength used as copy size, unchecked. */
int copy_cluster_buggy(struct usb_host_interface *hostif, unsigned char *dst)
{
	struct uac3_cluster_header *hc = (struct uac3_cluster_header *)hostif->extra;
	int len = hc->wLength;

	memcpy(dst, hostif->extra, len);	/* reads wLength bytes, blob may be shorter */
	return len;
}

/* Device channel count used as an index into the blob, unchecked. */
u8 last_channel_buggy(struct usb_host_interface *hostif)
{
	struct uac3_cluster_header *hc = (struct uac3_cluster_header *)hostif->extra;
	int n = hc->bNrChannels;

	return hc->data[n];
}

/* ================================================================== *
 *  SAFE cases
 * ================================================================== */

/* Fixed find_ijack: sz checked against the bytes remaining in the blob. */
int find_ijack_fixed(struct usb_host_interface *hostif, u8 jack_id)
{
	unsigned char *extra = hostif->extra;
	int extralen = hostif->extralen;
	struct usb_midi_out_jack_descriptor *outjd;
	size_t sz;

	while (extralen > 4) {
		outjd = (struct usb_midi_out_jack_descriptor *)extra;
		if (outjd->bDescriptorSubtype == UAC_MIDI_OUT_JACK &&
		    outjd->bJackID == jack_id) {
			sz = USB_DT_MIDI_OUT_SIZE(outjd->bNrInputPins);
			if (sz > extralen)
				goto next;
			return *(extra + sz - 1);
		}
next:
		extralen -= extra[0];
		extra += extra[0];
	}
	return -1;
}

/* Copy size bounded by the blob length. */
int copy_cluster_fixed(struct usb_host_interface *hostif, unsigned char *dst)
{
	struct uac3_cluster_header *hc = (struct uac3_cluster_header *)hostif->extra;
	int extralen = hostif->extralen;
	int len = hc->wLength;

	if (len > extralen)
		return -1;
	memcpy(dst, hostif->extra, len);
	return len;
}

/* Index bounded by the blob length. */
u8 last_channel_fixed(struct usb_host_interface *hostif)
{
	struct uac3_cluster_header *hc = (struct uac3_cluster_header *)hostif->extra;
	int buflen = hostif->extralen - (int)sizeof(*hc);
	int n = hc->bNrChannels;

	if (n >= buflen)
		return 0;
	return hc->data[n];
}
