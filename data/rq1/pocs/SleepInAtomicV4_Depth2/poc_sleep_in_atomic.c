/*
 * POC for Linux commit 3dfd520c
 * Bug: sleep-in-atomic-context
 * CWE-764: Multiple Locks of a Critical Resource
 */

#include <stddef.h>

#define __iomem
#define __user

typedef struct { int locked; } spinlock_t;

static inline void spin_lock(spinlock_t *lock) { lock->locked = 1; }
static inline void spin_unlock(spinlock_t *lock) { lock->locked = 0; }

extern void usleep_range(unsigned long min, unsigned long max);
extern void udelay(unsigned long usecs);

static spinlock_t my_lock;

/* BUGGY - sleeps while holding spinlock */
static void func_buggy(void) {
    spin_lock(&my_lock);
    usleep_range(1000, 2000);  /* BUG: sleeping in atomic context */
    spin_unlock(&my_lock);
}

/* FIXED - uses non-sleeping alternative */
static void func_fixed(void) {
    spin_lock(&my_lock);
    udelay(1500);  /* FIXED: busy-wait instead of sleep */
    spin_unlock(&my_lock);
}

int main(void) {
    func_buggy();
    func_fixed();
    return 0;
}
