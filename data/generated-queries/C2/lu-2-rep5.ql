/**
 * @name  rq3-c2-lu-2-rep5
 * @id    cpp/rq3/c2/lu-2-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect early returns from a function that allocated memory via
 *              kmalloc but failed to call kfree on the resource before
 *              returning, while the function has a separate cleanup path that
 *              does free the resource (typical "missing goto to err label" bug).
 */
import cpp

predicate allocates_resource(FunctionCall alloc, Variable v) {
  alloc.getTarget().hasName("kmalloc") and
  exists(AssignExpr a |
    a.getRValue() = alloc and
    a.getLValue() = v.getAnAccess())
}

predicate frees_variable(FunctionCall freeCall, Variable v) {
  freeCall.getTarget().hasName("kfree") and
  freeCall.getArgument(0) = v.getAnAccess()
}

predicate function_has_cleanup_free(Function f, Variable v) {
  exists(FunctionCall freeCall |
    frees_variable(freeCall, v) and
    freeCall.getEnclosingFunction() = f)
}

predicate early_return_skips_free(Function f, Variable v, ReturnStmt ret) {
  exists(FunctionCall alloc |
    allocates_resource(alloc, v) and
    alloc.getEnclosingFunction() = f) and
  ret.getEnclosingFunction() = f and
  function_has_cleanup_free(f, v) and
  not exists(FunctionCall freeCall |
    frees_variable(freeCall, v) and
    freeCall.getEnclosingFunction() = f and
    freeCall.getLocation().getStartLine() < ret.getLocation().getStartLine())
}

from Function f, Variable v, ReturnStmt ret
where early_return_skips_free(f, v, ret)
select ret, "Early return from $@ skips kfree of allocated variable '" + v.getName() + "'.", f, f.getName()
