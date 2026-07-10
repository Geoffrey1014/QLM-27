/**
 * @name Memory leak on early return without cleanup goto
 * @description Detects functions that allocate memory with kmalloc-family
 *              APIs and then have an early `return` statement that
 *              bypasses the cleanup path (kfree via goto err;). Modeled
 *              after commit 2289adbfa559 (af9005_identify_state).
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1/lu-2-rep5
 */
import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kmalloc", "kzalloc", "kcalloc", "kmalloc_array",
    "kmemdup", "kstrdup", "kstrndup",
    "vmalloc", "vzalloc", "kvmalloc", "kvzalloc"
  ]
}

predicate freesVariable(FunctionCall fc, Variable v) {
  fc.getTarget().getName() in [
    "kfree", "vfree", "kvfree", "kzfree", "kfree_sensitive"
  ] and
  fc.getArgument(0) = v.getAnAccess()
}

from FunctionCall alloc, LocalVariable v, ReturnStmt rs, Function f
where
  isAllocCall(alloc) and
  f = alloc.getEnclosingFunction() and
  // v is assigned the (possibly casted) result of alloc
  exists(Expr e | e = alloc or e.getAChild*() = alloc |
    v.getAnAssignedValue() = e
  ) and
  // the return happens in the same function, strictly after the alloc
  rs.getEnclosingFunction() = f and
  rs.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  // the return returns an expression (not "return;")
  exists(rs.getExpr()) and
  // no kfree of v appears before this return in source order
  not exists(FunctionCall rel |
    freesVariable(rel, v) and
    rel.getEnclosingFunction() = f and
    rel.getLocation().getStartLine() < rs.getLocation().getStartLine()
  ) and
  // there IS a kfree of v somewhere in the function (i.e. cleanup is
  // known to be required by the author — not an ownership-transfer case)
  exists(FunctionCall rel |
    freesVariable(rel, v) and
    rel.getEnclosingFunction() = f
  ) and
  // the function uses goto-based cleanup: at least one goto sits
  // between the alloc and this return
  exists(GotoStmt g |
    g.getEnclosingFunction() = f and
    g.getLocation().getStartLine() < rs.getLocation().getStartLine() and
    g.getLocation().getStartLine() > alloc.getLocation().getStartLine()
  )
select rs, "Possible memory leak: variable " + v.getName() +
  " allocated by " + alloc.getTarget().getName() +
  " at line " + alloc.getLocation().getStartLine() +
  " is not freed before this early return."
