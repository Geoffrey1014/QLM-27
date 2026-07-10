/**
 * @name Unnecessary GFP_ATOMIC in non-atomic context
 * @description Allocator call (kzalloc/kmalloc/kcalloc/krealloc) that
 *              passes GFP_ATOMIC from a function which is unlikely to
 *              ever execute in atomic context (e.g. an `_init`, `_probe`,
 *              or similar one-shot setup helper). GFP_ATOMIC restricts
 *              the allocator unnecessarily and should be GFP_KERNEL.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-3
 */

import cpp

/**
 * Allocator-style functions whose last parameter is a gfp_t flag.
 * Conservative whitelist, mirrors the set inspected by the
 * delay-gfp pattern across the kernel.
 */
predicate isGfpAllocator(string name) {
  name = "kzalloc" or
  name = "kmalloc" or
  name = "kcalloc" or
  name = "krealloc" or
  name = "kmalloc_array" or
  name = "kzalloc_node" or
  name = "kmalloc_node" or
  name = "kcalloc_node" or
  name = "vmalloc" or
  name = "vzalloc"
}

/**
 * Holds if `e` is syntactically the GFP_ATOMIC token (or its raw
 * numeric value 0x20 / 32 when the macro is already expanded by the
 * extractor). We accept either form so the check works on both the
 * full kernel DB and stub-based POCs.
 */
predicate isGfpAtomic(Expr e) {
  // Macro-form: GFP_ATOMIC expands here.
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  // Numeric-form fallback (mirrors GFP_ATOMIC = __GFP_HIGH = 0x20).
  e.getValue().toInt() = 32
}

/**
 * Holds if `f` looks like a one-shot, sleepable setup helper: init /
 * probe / open / setup / start handlers, module __init paths, etc.
 * Atomic-context helpers (ISR/IRQ/spin/tasklet/NMI/atomic) are
 * explicitly excluded. Name-based heuristic on purpose: we want a
 * decision rule that travels with the function definition and does not
 * require whole-program call-graph reasoning.
 */
predicate isLikelyNonAtomicSetup(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    (
      n.matches("%_init") or
      n.matches("%_init\\_%") or
      n.matches("%_probe") or
      n.matches("%_open") or
      n.matches("%_setup") or
      n.matches("%_start") or
      n.matches("%_attach") or
      n.matches("%_bind") or
      n.matches("%_create") or
      n.matches("%_register") or
      n.matches("%_resume") or
      n.matches("%_suspend") or
      n.matches("init_%") or
      n.matches("probe_%")
    ) and
    not (
      n.matches("%_isr") or
      n.matches("%_irq%") or
      n.matches("%_handler") or
      n.matches("%_nmi%") or
      n.matches("%_interrupt") or
      n.matches("%spin_%") or
      n.matches("%_atomic%") or
      n.matches("%_tasklet%")
    )
  )
}

from FunctionCall fc, Function callee, Function enclosing, Expr flag
where
  callee = fc.getTarget() and
  isGfpAllocator(callee.getName()) and
  // The gfp flag is the LAST argument of every API in `isGfpAllocator`.
  flag = fc.getArgument(fc.getNumberOfArguments() - 1) and
  isGfpAtomic(flag) and
  enclosing = fc.getEnclosingFunction() and
  isLikelyNonAtomicSetup(enclosing)
select fc,
  "Allocator '" + callee.getName() +
  "' called with GFP_ATOMIC inside non-atomic setup function '" +
  enclosing.getName() + "'; consider GFP_KERNEL."
