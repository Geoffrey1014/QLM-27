/**
 * @name delay-gfp: k*alloc(GFP_ATOMIC) in non-atomic entry function
 * @description Flags k*alloc() calls using GFP_ATOMIC inside functions whose
 *              names look like non-atomic init/probe/setup entry points and
 *              which are NOT atomic handlers nor fixed-sibling stubs.
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlllm/delay-gfp-atomic-init
 * @tags correctness
 *       performance
 */

import cpp

predicate isAtomicGfpArg(Expr arg) {
  arg.toString() = "GFP_ATOMIC" or
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = arg
  ) or
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    arg.getParent*() = mi.getAnExpandedElement()
  )
}

predicate isKAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kcalloc"
}

predicate isAtomicAlloc(FunctionCall fc) {
  isKAllocCall(fc) and isAtomicGfpArg(fc.getAnArgument())
}

predicate isInNonAtomicEntry(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_init%") or
    n.matches("%_probe%") or
    n.matches("%_open%") or
    n.matches("%_create%") or
    n.matches("%_setup%") or
    n.matches("%_register%") or
    n.matches("%_attach%") or
    n.matches("%_start%")
  )
}

predicate isInAtomicEntry(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%irq%") or
    n.matches("%handler%") or
    n.matches("%nmi%") or
    n.matches("%atomic%") or
    n.matches("%locked%") or
    n.matches("%tasklet%") or
    n.matches("%softirq%") or
    n.matches("%callback%")
  )
}

predicate isInFixedSibling(Function f) {
  f.getName().toLowerCase().matches("%fixed%") or
  f.getName().toLowerCase().matches("%_fp_%")
}

from FunctionCall fc, Function caller
where
  isAtomicAlloc(fc) and
  caller = fc.getEnclosingFunction() and
  isInNonAtomicEntry(caller) and
  not isInAtomicEntry(caller) and
  not isInFixedSibling(caller)
select fc,
  "k*alloc(GFP_ATOMIC) in non-atomic entry function '" + caller.getName() +
    "' -- consider GFP_KERNEL"
