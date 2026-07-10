/**
 * @name Unnecessary GFP_ATOMIC in non-atomic init/setup function
 * @description Kernel allocators (kzalloc/kmalloc/kcalloc/kmem_cache_alloc)
 *              called with GFP_ATOMIC in functions that look like one-shot
 *              initialization paths (probe/init/setup/start/create) are
 *              typically called from process context where GFP_KERNEL is
 *              preferred. GFP_ATOMIC stresses the atomic reserves and can
 *              fail under memory pressure. Replace with GFP_KERNEL unless
 *              the call site is truly in atomic context.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-3
 */

import cpp

/**
 * Holds if `fc` passes a constant flag named GFP_ATOMIC (recognised
 * either via macro expansion or as an enum/macro identifier with that
 * spelling) in argument position `idx`.
 */
predicate passesGfpAtomic(FunctionCall fc, int idx) {
  exists(Expr a | a = fc.getArgument(idx) |
    // The argument expression was produced by expanding a macro named
    // GFP_ATOMIC (or whose expansion contains the GFP_ATOMIC token).
    exists(MacroInvocation mi |
      mi.getMacroName() = "GFP_ATOMIC" and
      mi.getExpr() = a
    )
    or
    // Argument location is inside a GFP_ATOMIC macro invocation (handles
    // cases where the expanded expression isn't directly the MI's getExpr()
    // due to wrapping conversions / parenthesisation in the AST).
    exists(MacroInvocation mi, Location ml, Location al |
      mi.getMacroName() = "GFP_ATOMIC" and
      ml = mi.getLocation() and
      al = a.getLocation() and
      al.getFile() = ml.getFile() and
      al.getStartLine() = ml.getStartLine() and
      al.getStartColumn() >= ml.getStartColumn() and
      al.getEndColumn() <= ml.getEndColumn()
    )
    or
    // Fallback: textual token at the argument position is GFP_ATOMIC
    // (covers enum-constant spellings and post-#define numeric literals
    // whose source-text label is preserved).
    a.toString() = "GFP_ATOMIC"
  )
}

/**
 * Allocator functions whose `gfp_t flags` argument is the one we want
 * to inspect, paired with the argument index of `flags`.
 */
predicate isAllocator(string name, int gfpIdx) {
  (name = "kmalloc" or name = "kzalloc" or name = "kcalloc" or
   name = "krealloc" or name = "kmalloc_array" or name = "kmemdup" or
   name = "vmalloc" or name = "kvmalloc" or name = "kvzalloc")
  and
  // For kmalloc/kzalloc/krealloc/vmalloc/kvmalloc/kvzalloc the gfp flag
  // is at index 1; for kcalloc/kmalloc_array/kmemdup it is at index 2.
  (
    (name = "kmalloc" or name = "kzalloc" or name = "krealloc" or
     name = "vmalloc" or name = "kvmalloc" or name = "kvzalloc")
    and gfpIdx = 1
    or
    (name = "kcalloc" or name = "kmalloc_array" or name = "kmemdup")
    and gfpIdx = 2
  )
}

/**
 * Heuristic: a function name pattern that suggests one-shot
 * initialisation in process context — probe, init, setup, start,
 * create, open, alloc. These are the call sites where GFP_KERNEL is
 * almost always appropriate.
 */
predicate looksLikeProcessContextInit(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%init%") or
    n.matches("%probe%") or
    n.matches("%setup%") or
    n.matches("%create%") or
    n.matches("%start%") or
    n.matches("%open%") or
    n.matches("%alloc%") or
    n = "main"
  )
}

/**
 * Conservative atomic-context filter: function names that strongly
 * suggest interrupt/atomic context where GFP_ATOMIC is legitimate.
 * We use this to avoid double-reporting; the looksLikeProcessContextInit
 * filter is the primary positive signal.
 */
predicate looksLikeAtomicContext(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_isr") or
    n.matches("%_irq%") or
    n.matches("%_handler") or
    n.matches("%_nmi%") or
    n.matches("%_interrupt") or
    n.matches("%_callback") or
    n.matches("%_timer") or
    n.matches("%_softirq") or
    n.matches("%_tasklet%")
  )
}

from FunctionCall fc, Function callee, Function enclosing, string callee_name, int gfpIdx
where
  callee = fc.getTarget() and
  callee_name = callee.getName() and
  isAllocator(callee_name, gfpIdx) and
  passesGfpAtomic(fc, gfpIdx) and
  enclosing = fc.getEnclosingFunction() and
  looksLikeProcessContextInit(enclosing) and
  not looksLikeAtomicContext(enclosing)
select fc,
  callee_name +
  "() called with GFP_ATOMIC in process-context-looking function '" +
  enclosing.getName() +
  "'; GFP_KERNEL is preferable unless this is truly atomic context."
