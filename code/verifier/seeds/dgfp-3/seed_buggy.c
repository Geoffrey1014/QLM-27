/* QLM seed slice: net/tipc/bcast.c @ a0732548ba03^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef struct { int counter; } spinlock_t;

struct sk_buff_head {
    void *next;
    void *prev;
    unsigned int qlen;
    spinlock_t lock;
};

struct net;
struct tipc_link;

struct tipc_bc_base {
    struct tipc_link *link;
    struct sk_buff_head inputq;
    int rc_ratio;
    bool rcast_support;
};

struct tipc_net {
    struct tipc_bc_base *bcbase;
    struct tipc_link *bcl;
    spinlock_t bclock;
};

#define GFP_ATOMIC    0x20u
#define GFP_KERNEL    0xcc0u
#define FB_MTU        3744
#define BCLINK_WIN_DEFAULT 50
#define ENOMEM        12

extern struct tipc_net *tipc_net(struct net *net);
extern void *kzalloc(size_t size, unsigned int flags);
extern void kfree(const void *ptr);
extern void spin_lock_init(spinlock_t *lock);
extern bool tipc_link_bc_create(struct net *net, int a, int b,
                                int mtu, int win, int c,
                                struct sk_buff_head *inputq,
                                void *p1, void *p2,
                                struct tipc_link **l);

/* ---- verbatim kernel code ---- */
int tipc_bcast_init(struct net *net)
{
	struct tipc_net *tn = tipc_net(net);
	struct tipc_bc_base *bb = NULL;
	struct tipc_link *l = NULL;

	bb = kzalloc(sizeof(*bb), GFP_ATOMIC);
	if (!bb)
		goto enomem;
	tn->bcbase = bb;
	spin_lock_init(&tipc_net(net)->bclock);

	if (!tipc_link_bc_create(net, 0, 0,
				 FB_MTU,
				 BCLINK_WIN_DEFAULT,
				 0,
				 &bb->inputq,
				 NULL,
				 NULL,
				 &l))
		goto enomem;
	bb->link = l;
	tn->bcl = l;
	bb->rc_ratio = 25;
	bb->rcast_support = true;
	return 0;
enomem:
	kfree(bb);
	kfree(l);
	return -ENOMEM;
}
