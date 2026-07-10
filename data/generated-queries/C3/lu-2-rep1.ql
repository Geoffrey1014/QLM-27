/**
 * @name Memory leak: missing kfree on early-return path
 * @description Detects functions where a kmalloc-family acquire is later
 *              cleaned up by kfree on some path, but an early return
 *              statement reaches the function exit without invoking the
 *              release. Inspired by af9005_identify_state (commit
 *              2289adbfa559).
 * @kind problem
 * @problem.severity warning
 * @id qlm/missing-kfree-on-early-return
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() in ["kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "vmalloc", "vzalloc"]
}

predicate isRelease(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "kfree" and fc.getArgument(0) = v.getAnAccess()
}

predicate acquiresInto(FunctionCall fc, Variable v) {
  isAcquire(fc) and
  (
    exists(AssignExpr a | a.getRValue() = fc and a.getLValue() = v.getAnAccess())
    or
    exists(Initializer i | i.getExpr() = fc and i.getDeclaration() = v)
  )
}

predicate leakingReturn(ReturnStmt r, Variable v, Function f, FunctionCall acq) {
  f = r.getEnclosingFunction() and
  acquiresInto(acq, v) and
  acq.getEnclosingFunction() = f and
  exists(FunctionCall rel | isRelease(rel, v) and rel.getEnclosingFunction() = f) and
  acq.getASuccessor+() = r and
  not exists(FunctionCall rel2 |
    isRelease(rel2, v) and
    rel2.getEnclosingFunction() = f and
    acq.getASuccessor+() = rel2 and
    rel2.getASuccessor+() = r
  ) and
  exists(FunctionCall intermediate |
    intermediate.getEnclosingFunction() = f and
    intermediate != acq and
    acq.getASuccessor+() = intermediate and
    intermediate.getASuccessor+() = r
  )
}

from ReturnStmt r, Variable v, Function f, FunctionCall acq
where leakingReturn(r, v, f, acq)
select r,
  "Possible memory leak: '" + v.getName() +
    "' allocated at $@ but not freed before this return in '" + f.getName() + "'.",
  acq, "acquire"
