/* QLM seed slice: net/rfkill/core.c @ 6fc232db9e8c^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define __must_check
#define __init
#define EINVAL 22
#define EALREADY 114
#define RFKILL_BLOCK_SW 0x02
#define POLL_INTERVAL 1000

#define BUG_ON(x) do { if (x) {} } while (0)
#define INIT_DELAYED_WORK(w, f) do { (void)(w); (void)(f); } while (0)
#define INIT_WORK(w, f) do { (void)(w); (void)(f); } while (0)

struct list_head {
    struct list_head *next, *prev;
};

typedef struct {
    int counter;
} atomic_t;

struct mutex {
    int dummy;
};

struct device {
    void *parent;
    char name[64];
};

struct workqueue_struct;

struct work_struct {
    unsigned long data;
    struct list_head entry;
    void (*func)(struct work_struct *work);
};

struct delayed_work {
    struct work_struct work;
    unsigned long timer;
};

enum rfkill_type {
    RFKILL_TYPE_ALL = 0,
};

enum rfkill_operation {
    RFKILL_OP_ADD = 0,
    RFKILL_OP_DEL,
    RFKILL_OP_CHANGE,
    RFKILL_OP_CHANGE_ALL,
};

struct rfkill_ops {
    void (*poll)(struct rfkill *rfkill, void *data);
    void (*query)(struct rfkill *rfkill, void *data);
    int (*set_block)(void *data, bool blocked);
};

struct rfkill {
    struct device dev;
    const struct rfkill_ops *ops;
    void *data;
    enum rfkill_type type;
    unsigned long state;
    unsigned long idx;
    bool registered;
    bool persistent;
    bool polling_paused;
    bool suspended;
    bool need_sync;
    const char *name;
    struct list_head node;
    struct delayed_work poll_work;
    struct work_struct uevent_work;
    struct work_struct sync_work;
    char led_trigger_name[64];
};

extern struct mutex rfkill_global_mutex;
extern struct list_head rfkill_list;
extern bool rfkill_epo_lock_active;
extern atomic_t rfkill_input_disabled;
extern struct workqueue_struct *system_power_efficient_wq;

extern void mutex_lock(struct mutex *lock);
extern void mutex_unlock(struct mutex *lock);
extern int dev_set_name(struct device *dev, const char *fmt, ...);
extern void list_add_tail(struct list_head *new, struct list_head *head);
extern void list_del_init(struct list_head *entry);
extern int device_add(struct device *dev);
extern void device_del(struct device *dev);
extern int rfkill_led_trigger_register(struct rfkill *rfkill);
extern void rfkill_poll(struct work_struct *work);
extern void rfkill_uevent_work(struct work_struct *work);
extern void rfkill_sync_work(struct work_struct *work);
extern bool queue_delayed_work(struct workqueue_struct *wq, struct delayed_work *dwork, unsigned long delay);
extern bool schedule_work(struct work_struct *work);
extern unsigned long round_jiffies_relative(unsigned long j);
extern int atomic_read(const atomic_t *v);
extern void __rfkill_switch_all(enum rfkill_type type, bool blocked);
extern void rfkill_global_led_trigger_event(void);
extern void rfkill_send_events(struct rfkill *rfkill, enum rfkill_operation op);
#undef CONFIG_RFKILL_INPUT
#define CONFIG_RFKILL_INPUT 1

/* ---- verbatim kernel code ---- */
int __must_check rfkill_register(struct rfkill *rfkill)
{
	static unsigned long rfkill_no;
	struct device *dev = &rfkill->dev;
	int error;

	BUG_ON(!rfkill);

	mutex_lock(&rfkill_global_mutex);

	if (rfkill->registered) {
		error = -EALREADY;
		goto unlock;
	}

	rfkill->idx = rfkill_no;
	dev_set_name(dev, "rfkill%lu", rfkill_no);
	rfkill_no++;

	list_add_tail(&rfkill->node, &rfkill_list);

	error = device_add(dev);
	if (error)
		goto remove;

	error = rfkill_led_trigger_register(rfkill);
	if (error)
		goto devdel;

	rfkill->registered = true;

	INIT_DELAYED_WORK(&rfkill->poll_work, rfkill_poll);
	INIT_WORK(&rfkill->uevent_work, rfkill_uevent_work);
	INIT_WORK(&rfkill->sync_work, rfkill_sync_work);

	if (rfkill->ops->poll)
		queue_delayed_work(system_power_efficient_wq,
			&rfkill->poll_work,
			round_jiffies_relative(POLL_INTERVAL));

	if (!rfkill->persistent || rfkill_epo_lock_active) {
		schedule_work(&rfkill->sync_work);
	} else {
#ifdef CONFIG_RFKILL_INPUT
		bool soft_blocked = !!(rfkill->state & RFKILL_BLOCK_SW);

		if (!atomic_read(&rfkill_input_disabled))
			__rfkill_switch_all(rfkill->type, soft_blocked);
#endif
	}

	rfkill_global_led_trigger_event();
	rfkill_send_events(rfkill, RFKILL_OP_ADD);

	mutex_unlock(&rfkill_global_mutex);
	return 0;

 devdel:
	device_del(&rfkill->dev);
 remove:
	list_del_init(&rfkill->node);
 unlock:
	mutex_unlock(&rfkill_global_mutex);
	return error;
}
