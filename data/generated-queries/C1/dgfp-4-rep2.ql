/**
 * @name Unnecessary GFP_ATOMIC in sleepable kernel context
 * @description Detects allocator / URB-submission calls that pass GFP_ATOMIC
 *              while the enclosing function clearly executes in sleepable
 *              (process) context — e.g. probe/remove/init/exit/open/release/
 *              ioctl/suspend/resume/work/thread callbacks. GFP_ATOMIC is
 *              reserved for true atomic regions (IRQ handlers, spinlock-held
 *              code, RCU read-side); using it elsewhere needlessly restricts
 *              the allocator and may cause spurious allocation failures.
 *              The fix is normally to switch the flag to GFP_KERNEL.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-4
 */

import cpp

/**
 * Functions whose last argument is a gfp_t / "mem_flags" allocation flag
 * that the caller may legitimately want to be GFP_KERNEL in sleepable
 * context. We recognise the common Linux allocation / submission APIs by
 * name; this is the same convention DCNS / delay-gfp queries use.
 */
predicate isGfpConsumer(string name) {
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "krealloc" or
  name = "kmalloc_array" or
  name = "vmalloc" or
  name = "vzalloc" or
  name = "kmem_cache_alloc" or
  name = "kmem_cache_zalloc" or
  name = "alloc_skb" or
  name = "__alloc_skb" or
  name = "dev_alloc_skb" or
  name = "netdev_alloc_skb" or
  name = "usb_alloc_urb" or
  name = "usb_submit_urb" or
  name = "usb_alloc_coherent" or
  name = "dma_alloc_coherent" or
  name = "request_irq"
}

/**
 * An expression that names the GFP_ATOMIC flag (either as the macro
 * identifier or the raw integer value the macro expands to in the POC
 * stub). We match by displayed text so we work both on real kernel DBs
 * (where the macro expands during preprocessing and the literal value
 * is what survives) and on stubs that #define GFP_ATOMIC.
 */
predicate isGfpAtomicExpr(Expr e) {
  // Macro use: the expression's text after preprocessing is the constant.
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  // Fallback: the source-level text contains GFP_ATOMIC (defensive).
  e.toString() = "GFP_ATOMIC"
}

/**
 * Heuristics for "this enclosing function definitely runs in sleepable
 * (process) context". We approximate via well-known callback name
 * suffixes pervasive in Linux kernel drivers and core subsystems.
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    // Driver model: probe / remove / shutdown — process context.
    n.matches("%_probe") or
    n.matches("%_remove") or
    n.matches("%_shutdown") or
    // Module init / exit and "init_xfer", "init_usb_xfer" style helpers.
    n.matches("%_init") or
    n.matches("%_exit") or
    n.matches("%_init_%") or
    n.matches("%_setup") or
    n.matches("%_setup_%") or
    // Power-management callbacks — process context.
    n.matches("%_resume") or
    n.matches("%_suspend") or
    n.matches("%_freeze") or
    n.matches("%_thaw") or
    n.matches("%_poweroff") or
    n.matches("%_restore") or
    // file_operations / chardev callbacks — process context.
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_ioctl") or
    n.matches("%_read") or
    n.matches("%_write") or
    // Workqueue / kthread / async — sleepable.
    n.matches("%_work") or
    n.matches("%_worker") or
    n.matches("%_workfn") or
    n.matches("%_thread") or
    n.matches("%_kthread")
  )
}

/**
 * Exclusions: name-based hints that the enclosing function is itself
 * an atomic-context callback (IRQ handlers, tasklets, timers).
 */
predicate looksAtomicContext(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq") or
    n.matches("%_irq_%") or
    n.matches("%_handler") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_callback") or
    n.matches("%_poll") or
    n.matches("%_napi")
  )
}

from FunctionCall call, Function enclosing, string apiName, Expr flagArg
where
  apiName = call.getTarget().getName() and
  isGfpConsumer(apiName) and
  enclosing = call.getEnclosingFunction() and
  isSleepableContextFunction(enclosing) and
  not looksAtomicContext(enclosing) and
  // The gfp flag is conventionally the last argument of the call.
  flagArg = call.getArgument(call.getNumberOfArguments() - 1) and
  isGfpAtomicExpr(flagArg)
select call,
  "Call to '" + apiName + "' uses GFP_ATOMIC inside sleepable function '" +
    enclosing.getName() + "' — GFP_KERNEL would be appropriate."
