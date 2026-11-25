/*
 * PoC for the "sysfs show() unbounded concatenation into buf" pattern (CWE-787).
 *
 * Mirrors the overflow shape of the ground-truth fixes:
 *   80ccd40568bcd  platform/mellanox: mlxbf-pmc: Fix potential buffer overflows
 *                  (len += sprintf(...); strcat(buf, e_info); check AFTER write)
 *   711d41ab4a0e4  usb: core: Use sysfs_emit_at() (concat with scnprintf -> sysfs_emit_at)
 *   e74a1c6a8e8af  zram: pass buffer offset to zcomp_available_show() (offset accounting)
 *
 * And the in-tree hand-confirmed examples it must flag:
 *   drivers/usb/typec/altmodes/displayport.c::pin_assignment_show
 *   drivers/leds/led-class-multicolor.c::multi_intensity_show
 *
 * *_buggy : unbounded loop concat into buf, no PAGE_SIZE-len cap  -> MUST be flagged.
 * *_fixed : sysfs_emit / single bounded write / PAGE_SIZE-capped concat -> MUST be spared.
 */
#include <stddef.h>

#define PAGE_SIZE 4096

/* ---- minimal libc/kernel fakes (declarations are enough for extraction) ---- */
int sprintf(char *buf, const char *fmt, ...);
int snprintf(char *buf, size_t size, const char *fmt, ...);
int scnprintf(char *buf, size_t size, const char *fmt, ...);
char *strcat(char *dst, const char *src);
int sysfs_emit(char *buf, const char *fmt, ...);
int sysfs_emit_at(char *buf, int at, const char *fmt, ...);

/* sysfs callback signature fakes */
struct device;
struct device_attribute;
struct kobject;
struct kobj_attribute;
typedef long ssize_t;

/* device-/firmware-influenced count and string table (the dangerous source) */
struct mydev {
	int num_items;             /* device-reported count: can be large */
	const char *names[256];    /* firmware-provided names: unbounded length */
	int values[256];
};
static struct mydev *to_mydev(struct device *dev);

/* ===================================================================== */
/* ============================ BUGGY ================================== */
/* ===================================================================== */

/* BUG 1: pin_assignment_show shape -- len += sprintf(buf+len, "%s ", str), no cap. */
static ssize_t loop_sprintf_offset_show_buggy(struct device *dev,
					    struct device_attribute *attr,
					    char *buf)
{
	struct mydev *d = to_mydev(dev);
	int len = 0;
	int i;

	for (i = 0; i < d->num_items; i++)
		len += sprintf(buf + len, "%s ", d->names[i]);

	buf[len - 1] = '\n';
	return len;
}

/* BUG 2: mlxbf-pmc shape -- per-item snprintf into scratch, strcat(buf,...) in loop,
 *        size check AFTER the write (the historically-confirmed overflow). */
static ssize_t loop_strcat_show_buggy(struct device *dev,
				    struct device_attribute *attr,
				    char *buf)
{
	struct mydev *d = to_mydev(dev);
	char e_info[128];
	int len = 0;
	int i;

	for (i = 0, buf[0] = '\0'; i < d->num_items; ++i) {
		len += snprintf(e_info, sizeof(e_info), "0x%x: %s\n",
				d->values[i], d->names[i]);
		strcat(buf, e_info);          /* <-- unbounded concat into buf */
	}
	return len;
}

/* BUG 3: multi_intensity_show shape -- len += sprintf(buf+len, "%d", v), no cap. */
static ssize_t loop_sprintf_num_show_buggy(struct device *dev,
					 struct device_attribute *attr,
					 char *buf)
{
	struct mydev *d = to_mydev(dev);
	int len = 0;
	int i;

	for (i = 0; i < d->num_items; i++) {
		len += sprintf(buf + len, "%d", d->values[i]);
		if (i < d->num_items - 1)
			len += sprintf(buf + len, " ");
	}
	buf[len++] = '\n';
	return len;
}

/* BUG 4: kobj_attribute variant of the unbounded concat (different signature). */
static ssize_t kobj_loop_show_buggy(struct kobject *kobj,
				  struct kobj_attribute *attr,
				  char *buf)
{
	struct mydev *d = to_mydev((struct device *)kobj);
	int len = 0;
	int i;

	for (i = 0; i < d->num_items; i++)
		len += sprintf(buf + len, "%s\n", d->names[i]);
	return len;
}

/* ===================================================================== */
/* ============================= SAFE ================================== */
/* ===================================================================== */

/* SAFE 1: already migrated -- sysfs_emit_at in the concat loop (zram/usb-core fix). */
static ssize_t sysfs_emit_at_show_fixed(struct device *dev,
				       struct device_attribute *attr,
				       char *buf)
{
	struct mydev *d = to_mydev(dev);
	int at = 0;
	int i;

	for (i = 0; i < d->num_items; i++)
		at += sysfs_emit_at(buf, at, "%s ", d->names[i]);
	return at;
}

/* SAFE 2: single bounded write -- the overwhelming benign majority. */
static ssize_t single_sysfs_emit_show_fixed(struct device *dev,
					   struct device_attribute *attr,
					   char *buf)
{
	struct mydev *d = to_mydev(dev);
	return sysfs_emit(buf, "%d\n", d->num_items);
}

/* SAFE 3: single plain sprintf, one small value (cosmetic at worst, not a bug). */
static ssize_t single_sprintf_show_fixed(struct device *dev,
					struct device_attribute *attr,
					char *buf)
{
	struct mydev *d = to_mydev(dev);
	return sprintf(buf, "%d\n", d->num_items);
}

/* SAFE 4: PAGE_SIZE-capped concat loop -- bounded by construction (scnprintf cap). */
static ssize_t capped_scnprintf_show_fixed(struct device *dev,
					  struct device_attribute *attr,
					  char *buf)
{
	struct mydev *d = to_mydev(dev);
	int len = 0;
	int i;

	for (i = 0; i < d->num_items; i++)
		len += scnprintf(buf + len, PAGE_SIZE - len, "%s ", d->names[i]);
	return len;
}

/* SAFE 5: mutually-exclusive single-write branches (NOT concatenation). */
static ssize_t branch_single_show_fixed(struct device *dev,
				       struct device_attribute *attr,
				       char *buf)
{
	struct mydev *d = to_mydev(dev);

	if (d->num_items > 0)
		return sprintf(buf, "on\n");
	else
		return sprintf(buf, "off\n");
}
