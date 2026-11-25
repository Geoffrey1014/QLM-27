/*
 * PoC for "Unbounded accumulating copy into a fixed-size buffer" (CWE-120/787).
 *
 * Models four GT kernel commits:
 *   1214bf28 gb-beagleplay  : accumulating memcpy(buf + len, data, count) w/o remaining check
 *   30fe3f5f pn533          : skb_put_u8() in a loop without skb_tailroom() check
 *   3c34471c dell-wmi-sysman: raw strcat() aggregation into fixed buffer, no space check
 *   5ec1d1e9 tracing        : repeated strcat() into a static buffer
 *
 * Detection target: a write op (memcpy, skb_put family, strcat/strncat/strlcat)
 * that accumulates into a fixed-size buffer, where the write is either inside a loop
 * or the same destination is written by another such op (accumulation), and
 * there is NO remaining-space comparison (off/len/size relational check) nor a
 * size-aware safe API (snprintf/strscpy/strlcpy) in the function.
 *
 * Naming: *_buggy must be reported; *_fixed must NOT.
 */

#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <sys/types.h>

/* ---- minimal skb stubs (mirror kernel skb_put family) ---- */
struct sk_buff {
	unsigned char *data;
	unsigned int tail;
	unsigned int end;
};
extern void *skb_put(struct sk_buff *skb, unsigned int len);
extern void skb_put_u8(struct sk_buff *skb, unsigned char val);
extern void *skb_put_data(struct sk_buff *skb, const void *data, unsigned int len);
extern int skb_tailroom(const struct sk_buff *skb);
extern void skb_trim(struct sk_buff *skb, unsigned int len);

#define RX_BUF_SIZE 256
#define DEST_SIZE   512

struct ctx {
	unsigned char rx_buffer[RX_BUF_SIZE];
	unsigned int rx_buffer_len;
	struct sk_buff *recv_skb;
};

/* ========================= BUG cases ========================= */

/* memcpy_accum_buggy: memcpy into buf+len, no check that count fits remaining.  (1214bf28) */
size_t memcpy_accum_buggy(struct ctx *bg, const unsigned char *data, size_t count)
{
	memcpy(bg->rx_buffer + bg->rx_buffer_len, data, count);
	bg->rx_buffer_len += count;
	return count;
}

/* skb_put_loop_buggy: skb_put_u8 in a loop, never checks skb_tailroom.  (30fe3f5f) */
size_t skb_put_loop_buggy(struct ctx *dev, const unsigned char *data, size_t count)
{
	size_t i;
	for (i = 0; i < count; i++)
		skb_put_u8(dev->recv_skb, *data++);
	return count;
}

/* strcat_aggregate_buggy: raw strcat aggregation into fixed buffer, no space check. (3c34471c) */
int strcat_aggregate_buggy(char *dest, const char **values, int n)
{
	int i;
	for (i = 0; i < n; i++) {
		strcat(dest, values[i]);
		strcat(dest, ";");
	}
	return 0;
}

/* strcat_repeated_buggy: repeated strcat into a static buffer, no rebuild/size check. (5ec1d1e9) */
const char *strcat_repeated_buggy(const char *system, const char *event, const char *name)
{
	static char full_name[256];
	strcat(full_name, system);
	strcat(full_name, ".");
	strcat(full_name, event);
	strcat(full_name, ".");
	strcat(full_name, name);
	return full_name;
}

/* skb_put_data_loop_buggy: skb_put_data of variable len in a loop, no tailroom check. */
void skb_put_data_loop_buggy(struct sk_buff *skb, const unsigned char *chunks[],
			   const unsigned int *lens, int n)
{
	int i;
	for (i = 0; i < n; i++)
		skb_put_data(skb, chunks[i], lens[i]);
}

/* strncat_accum_buggy: strncat aggregation in loop into fixed buf, no remaining check. */
void strncat_accum_buggy(char *dest, const char **values, int n)
{
	int i;
	for (i = 0; i < n; i++)
		strncat(dest, values[i], 32);
}

/* ========================= OK cases (checked, should NOT fire) ========================= */

/* memcpy_checked_fixed: checks count fits remaining space before memcpy.  (1214bf28 fix) */
size_t memcpy_checked_fixed(struct ctx *bg, const unsigned char *data, size_t count)
{
	if (count > sizeof(bg->rx_buffer) - bg->rx_buffer_len) {
		bg->rx_buffer_len = 0;
		return count;
	}
	memcpy(bg->rx_buffer + bg->rx_buffer_len, data, count);
	bg->rx_buffer_len += count;
	return count;
}

/* skb_put_checked_fixed: checks skb_tailroom before skb_put_u8 in loop.  (30fe3f5f fix) */
size_t skb_put_checked_fixed(struct ctx *dev, const unsigned char *data, size_t count)
{
	size_t i;
	for (i = 0; i < count; i++) {
		if (!skb_tailroom(dev->recv_skb))
			skb_trim(dev->recv_skb, 0);
		skb_put_u8(dev->recv_skb, *data++);
	}
	return count;
}

/* strcat_checked_fixed: checks remaining space (len comparison) before strcat. */
int strcat_checked_fixed(char *dest, const char **values, int n)
{
	int i;
	for (i = 0; i < n; i++) {
		size_t dest_len = strlen(dest);
		if (dest_len + strlen(values[i]) >= DEST_SIZE)
			return -1;
		strcat(dest, values[i]);
	}
	return 0;
}

/* skb_put_data_checked_fixed: tailroom relational check before skb_put_data loop. */
void skb_put_data_checked_fixed(struct sk_buff *skb, const unsigned char *chunks[],
			     const unsigned int *lens, int n)
{
	int i;
	for (i = 0; i < n; i++) {
		if (skb_tailroom(skb) < (int)lens[i])
			return;
		skb_put_data(skb, chunks[i], lens[i]);
	}
}

/* ========================= SAFE cases (size-aware API, should NOT fire) ========================= */

/* snprintf_fixed: builds name with snprintf each call.  (5ec1d1e9 fix) */
const char *snprintf_fixed(const char *system, const char *event, const char *name)
{
	static char full_name[256];
	int len = snprintf(full_name, sizeof(full_name), "%s.%s.%s", system, event, name);
	if (len >= (int)sizeof(full_name))
		return NULL;
	return full_name;
}

/* strscpy_fixed: bounded append via strscpy with remaining size.  (3c34471c fix) */
extern ssize_t strscpy(char *dest, const char *src, size_t count);
int strscpy_fixed(char *dest, const char **values, int n)
{
	int i;
	for (i = 0; i < n; i++) {
		size_t dest_len = strlen(dest);
		ssize_t copied = strscpy(dest + dest_len, values[i], DEST_SIZE - dest_len);
		if (copied < 0)
			return -1;
	}
	return 0;
}

/* single_memcpy_fixed: a single, non-accumulating memcpy (not in loop, not repeated). */
void single_memcpy_fixed(unsigned char *dst, const unsigned char *src, size_t n)
{
	memcpy(dst, src, n);
}
