/* QLM seed slice: drivers/rpmsg/qcom_glink_native.c @ 26594c6bbb60 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef uint32_t u32;
typedef uint16_t u16;
typedef uint32_t __le32;
typedef uint16_t __le16;

#define GFP_ATOMIC 0
#define EAGAIN 11
#define ENOMEM 12
#define ENOENT 2
#define RPMSG_ADDR_ANY 0xFFFFFFFF

#define __packed __attribute__((packed))

#define ALIGN(x, a) (((x) + ((a) - 1)) & ~((a) - 1))

#define le32_to_cpu(x) ((u32)(x))
#define le16_to_cpu(x) ((u16)(x))

#define dev_dbg(dev, fmt, ...) do { (void)(dev); } while (0)
#define dev_err(dev, fmt, ...) do { (void)(dev); } while (0)

typedef struct { int counter; } spinlock_t;

struct device;
struct rpmsg_device;

struct idr {
    int dummy;
};

struct glink_msg {
    __le16 cmd;
    __le16 param1;
    __le32 param2;
} __packed;

struct glink_core_rx_intent {
    void *data;
    u32 id;
    size_t size;
    size_t offset;
    bool reuse;
    bool in_use;
    u32 iid;
};

struct rpmsg_endpoint {
    struct rpmsg_device *rpdev;
    void *priv;
    int (*cb)(struct rpmsg_device *rpdev, void *data, int len, void *priv, u32 addr);
};

struct glink_channel {
    struct rpmsg_endpoint ept;
    struct glink_core_rx_intent *buf;
    struct idr liids;
    spinlock_t intent_lock;
    spinlock_t recv_lock;
    const char *name;
};

struct qcom_glink {
    struct device *dev;
    struct idr rcids;
    spinlock_t idr_lock;
    bool intentless;
};

extern void spin_lock_irqsave(spinlock_t *lock, unsigned long flags);
extern void spin_unlock_irqrestore(spinlock_t *lock, unsigned long flags);
#define spin_lock_irqsave(lock, flags) do { (void)(lock); (flags) = 0; } while (0)
#define spin_unlock_irqrestore(lock, flags) do { (void)(lock); (void)(flags); } while (0)

extern void spin_lock(spinlock_t *lock);
extern void spin_unlock(spinlock_t *lock);

extern void *idr_find(struct idr *idr, int id);
extern void *kzalloc(size_t size, unsigned int flags);
extern void *kmalloc(size_t size, unsigned int flags);
extern void kfree(const void *ptr);

extern void qcom_glink_rx_peak(struct qcom_glink *glink, void *data, size_t offset, size_t count);
extern void qcom_glink_rx_advance(struct qcom_glink *glink, size_t count);
extern void qcom_glink_rx_done(struct qcom_glink *glink, struct glink_channel *channel, struct glink_core_rx_intent *intent);

/* ---- verbatim kernel code ---- */
static int qcom_glink_rx_data(struct qcom_glink *glink, size_t avail)
{
	struct glink_core_rx_intent *intent;
	struct glink_channel *channel;
	struct {
		struct glink_msg msg;
		__le32 chunk_size;
		__le32 left_size;
	} __packed hdr;
	unsigned int chunk_size;
	unsigned int left_size;
	unsigned int rcid;
	unsigned int liid;
	int ret = 0;
	unsigned long flags;

	if (avail < sizeof(hdr)) {
		dev_dbg(glink->dev, "Not enough data in fifo\n");
		return -EAGAIN;
	}

	qcom_glink_rx_peak(glink, &hdr, 0, sizeof(hdr));
	chunk_size = le32_to_cpu(hdr.chunk_size);
	left_size = le32_to_cpu(hdr.left_size);

	if (avail < sizeof(hdr) + chunk_size) {
		dev_dbg(glink->dev, "Payload not yet in fifo\n");
		return -EAGAIN;
	}

	rcid = le16_to_cpu(hdr.msg.param1);
	spin_lock_irqsave(&glink->idr_lock, flags);
	channel = idr_find(&glink->rcids, rcid);
	spin_unlock_irqrestore(&glink->idr_lock, flags);
	if (!channel) {
		dev_dbg(glink->dev, "Data on non-existing channel\n");

		/* Drop the message */
		goto advance_rx;
	}

	if (glink->intentless) {
		/* Might have an ongoing, fragmented, message to append */
		if (!channel->buf) {
			intent = kzalloc(sizeof(*intent), GFP_ATOMIC);
			if (!intent)
				return -ENOMEM;

			intent->data = kmalloc(chunk_size + left_size,
					       GFP_ATOMIC);
			if (!intent->data) {
				kfree(intent);
				return -ENOMEM;
			}

			intent->id = 0xbabababa;
			intent->size = chunk_size + left_size;
			intent->offset = 0;

			channel->buf = intent;
		} else {
			intent = channel->buf;
		}
	} else {
		liid = le32_to_cpu(hdr.msg.param2);

		spin_lock_irqsave(&channel->intent_lock, flags);
		intent = idr_find(&channel->liids, liid);
		spin_unlock_irqrestore(&channel->intent_lock, flags);

		if (!intent) {
			dev_err(glink->dev,
				"no intent found for channel %s intent %d",
				channel->name, liid);
			ret = -ENOENT;
			goto advance_rx;
		}
	}

	if (intent->size - intent->offset < chunk_size) {
		dev_err(glink->dev, "Insufficient space in intent\n");

		/* The packet header lied, drop payload */
		goto advance_rx;
	}

	qcom_glink_rx_peak(glink, intent->data + intent->offset,
			   sizeof(hdr), chunk_size);
	intent->offset += chunk_size;

	/* Handle message when no fragments remain to be received */
	if (!left_size) {
		spin_lock(&channel->recv_lock);
		if (channel->ept.cb) {
			channel->ept.cb(channel->ept.rpdev,
					intent->data,
					intent->offset,
					channel->ept.priv,
					RPMSG_ADDR_ANY);
		}
		spin_unlock(&channel->recv_lock);

		intent->offset = 0;
		channel->buf = NULL;

		qcom_glink_rx_done(glink, channel, intent);
	}

advance_rx:
	qcom_glink_rx_advance(glink, ALIGN(sizeof(hdr) + chunk_size, 8));

	return ret;
}
