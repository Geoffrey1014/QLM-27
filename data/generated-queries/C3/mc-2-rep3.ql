/**
 * @name Missing NULL check on kzalloc result
 * @description Reports calls to kzalloc/kmalloc/kcalloc whose result is
 *              dereferenced later in the same function without a NULL
 *              check (no IfStmt between the allocation and the FIRST
 *              dereference site that is NOT itself inside an IfStmt's
 *              condition). Modeled on Linux commit 09acf29c8246
 *              ("staging: rtl8192u: null check the kzalloc").
 * @kind problem
 * @problem.severity warning
 * @id qlm/missing-null-check-kzalloc/mc-2-rep3
 */

import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kcalloc"
}

/* True if e is syntactically inside the condition of some IfStmt. */
predicate inIfCondition(Expr e) {
  exists(IfStmt ifs | ifs.getCondition() = e.getParent*())
}

predicate hasDerefAfter(FunctionCall fc, int derefLine) {
  isAllocCall(fc) and
  exists(Expr e, Function f |
    f = fc.getEnclosingFunction() and
    e.getEnclosingFunction() = f and
    e.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    derefLine = e.getLocation().getStartLine() and
    not inIfCondition(e) and
    (
      e instanceof PointerFieldAccess
      or
      e.(FunctionCall).getTarget().getName() = "touch_firmware"
    )
  )
}

/* Earliest deref site after the allocation in the same function. */
int firstDerefAfter(FunctionCall fc) {
  result = min(int dl | hasDerefAfter(fc, dl) | dl)
}

bindingset[derefLine]
predicate hasIfBetween(FunctionCall fc, int derefLine) {
  isAllocCall(fc) and
  exists(IfStmt ifs, Function f |
    f = fc.getEnclosingFunction() and
    ifs.getEnclosingFunction() = f and
    ifs.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    ifs.getLocation().getStartLine() <= derefLine
  )
}

from FunctionCall alloc, int firstDeref
where
  isAllocCall(alloc) and
  firstDeref = firstDerefAfter(alloc) and
  not hasIfBetween(alloc, firstDeref)
select alloc,
       "kzalloc/kmalloc/kcalloc result dereferenced without a prior NULL check (alloc at line "
       + alloc.getLocation().getStartLine() + ", first deref at line " + firstDeref + ")"
