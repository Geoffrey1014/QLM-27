/**
 * @name  rq3-c2-lu-5-rep4
 * @id    cpp/rq3/c2/lu-5-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate is_alloc_call(FunctionCall fc) {
  fc.getTarget().hasName("kstrdup") or
  fc.getTarget().hasName("kmalloc") or
  fc.getTarget().hasName("kzalloc") or
  fc.getTarget().hasName("kcalloc") or
  fc.getTarget().hasName("kmemdup") or
  fc.getTarget().hasName("kstrndup") or
  fc.getTarget().hasName("vmalloc") or
  fc.getTarget().hasName("vzalloc")
}

predicate is_free_call_on(FunctionCall fc, Variable v) {
  (fc.getTarget().hasName("kfree") or
   fc.getTarget().hasName("kvfree") or
   fc.getTarget().hasName("vfree") or
   fc.getTarget().hasName("kzfree") or
   fc.getTarget().hasName("kfree_sensitive")) and
  fc.getArgument(0).(VariableAccess).getTarget() = v
}

predicate alloc_assigned_to(FunctionCall fc, Variable v) {
  is_alloc_call(fc) and
  (
    exists(AssignExpr ae |
      ae.getRValue() = fc and
      ae.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(Initializer init |
      init.getExpr() = fc and
      init.getDeclaration() = v
    )
  )
}

predicate return_without_free(FunctionCall alloc, Variable v, ReturnStmt rs) {
  alloc_assigned_to(alloc, v) and
  alloc.getEnclosingFunction() = rs.getEnclosingFunction() and
  rs.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  not exists(FunctionCall freeCall |
    is_free_call_on(freeCall, v) and
    freeCall.getEnclosingFunction() = rs.getEnclosingFunction() and
    freeCall.getLocation().getStartLine() >= alloc.getLocation().getStartLine() and
    freeCall.getLocation().getStartLine() <= rs.getLocation().getStartLine()
  ) and
  v instanceof LocalScopeVariable
}

from FunctionCall alloc, Variable v, ReturnStmt rs
where return_without_free(alloc, v, rs)
select rs, "Possible memory leak: allocation of $@ stored in '" + v.getName() + "' may not be freed before this return.", alloc, alloc.toString()
