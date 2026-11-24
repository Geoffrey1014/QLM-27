/* QLM seed slice: drivers/hwmon/lm80.c @ c9c63915519b^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef long ssize_t;
typedef unsigned char u8;

#define EINVAL 22

struct device;
struct device_attribute;
struct i2c_client;

struct mutex { int _x; };

enum { f_input = 0, f_min = 1 };

struct lm80_data {
    struct i2c_client *client;
    struct mutex update_lock;
    u8 fan[2][4];
    u8 fan_div[4];
};

struct sensor_device_attribute {
    struct device_attribute *dev_attr;
    int index;
};

#define to_sensor_dev_attr(x) ((struct sensor_device_attribute *)(x))

#define LM80_REG_FANDIV 0x5
#define LM80_REG_FAN_MIN(nr) (0x3b + (nr))

#define FAN_FROM_REG(val, div) ((val) * (div))
#define FAN_TO_REG(val, div)   ((val) / (div))
#define DIV_FROM_REG(val)      (1 << (val))

extern void *dev_get_drvdata(const struct device *dev);
extern int kstrtoul(const char *s, unsigned int base, unsigned long *res);
extern void mutex_lock(struct mutex *lock);
extern void mutex_unlock(struct mutex *lock);
extern int lm80_read_value(struct i2c_client *client, u8 reg);
extern int lm80_write_value(struct i2c_client *client, u8 reg, u8 value);
extern int dev_err(const struct device *dev, const char *fmt, ...);

/* ---- verbatim kernel code ---- */
static ssize_t set_fan_div(struct device *dev, struct device_attribute *attr,
	const char *buf, size_t count)
{
	int nr = to_sensor_dev_attr(attr)->index;
	struct lm80_data *data = dev_get_drvdata(dev);
	struct i2c_client *client = data->client;
	unsigned long min, val;
	u8 reg;
	int err = kstrtoul(buf, 10, &val);
	if (err < 0)
		return err;

	/* Save fan_min */
	mutex_lock(&data->update_lock);
	min = FAN_FROM_REG(data->fan[f_min][nr],
			   DIV_FROM_REG(data->fan_div[nr]));

	switch (val) {
	case 1:
		data->fan_div[nr] = 0;
		break;
	case 2:
		data->fan_div[nr] = 1;
		break;
	case 4:
		data->fan_div[nr] = 2;
		break;
	case 8:
		data->fan_div[nr] = 3;
		break;
	default:
		dev_err(dev,
			"fan_div value %ld not supported. Choose one of 1, 2, 4 or 8!\n",
			val);
		mutex_unlock(&data->update_lock);
		return -EINVAL;
	}

	reg = (lm80_read_value(client, LM80_REG_FANDIV) &
	       ~(3 << (2 * (nr + 1)))) | (data->fan_div[nr] << (2 * (nr + 1)));
	lm80_write_value(client, LM80_REG_FANDIV, reg);

	/* Restore fan_min */
	data->fan[f_min][nr] = FAN_TO_REG(min, DIV_FROM_REG(data->fan_div[nr]));
	lm80_write_value(client, LM80_REG_FAN_MIN(nr + 1),
			 data->fan[f_min][nr]);
	mutex_unlock(&data->update_lock);

	return count;
}
