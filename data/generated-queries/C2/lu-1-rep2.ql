/**
 * @name  rq3-c2-lu-1-rep2
 * @id    cpp/rq3/c2/lu-1-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects resource allocation followed by an error-return path
 *              without a release call on the allocated variable.
 */
import cpp

predicate is_alloc_call(FunctionCall fc, Variable v) {
  fc.getTarget().getName().regexpMatch("(?i).*(alloc|create|new|make|temp_asoc|kmalloc|kzalloc).*") and
  exists(AssignExpr ae | ae.getRValue() = fc and ae.getLValue() = v.getAnAccess())
  or
  fc.getTarget().getName().regexpMatch("(?i).*(alloc|create|new|make|temp_asoc|kmalloc|kzalloc).*") and
  exists(Initializer i | i.getExpr() = fc and i.getDeclaration() = v)
}

predicate is_free_call_on(FunctionCall fc, Variable v) {
  fc.getTarget().getName().regexpMatch("(?i).*(free|release|put|destroy|kfree|cleanup).*") and
  exists(Expr arg | arg = fc.getAnArgument() and arg = v.getAnAccess())
}

predicate is_error_return(ReturnStmt r) {
  exists(Expr e | e = r.getExpr() |
    e.getValue().toInt() < 0
    or
    e.(FunctionCall).getTarget().getName().regexpMatch("(?i).*(pdiscard|err|fail|discard).*")
    or
    exists(Variable v | v.getAnAccess() = e and v.getName().regexpMatch("(?i).*(err|ret|rc).*"))
  )
  or
  not exists(r.getExpr())
}

predicate reaches_return_without_free(FunctionCall alloc, Variable v, ReturnStmt r) {
  is_alloc_call(alloc, v) and
  is_error_return(r) and
  alloc.getEnclosingFunction() = r.getEnclosingFunction() and
  alloc.getASuccessor*() = r and
  not exists(FunctionCall freeCall |
    is_free_call_on(freeCall, v) and
    alloc.getASuccessor*() = freeCall and
    freeCall.getASuccessor*() = r
  )
}

predicate leaked_alloc(FunctionCall alloc, Variable v, ReturnStmt r) {
  reaches_return_without_free(alloc, v, r)
}

from FunctionCall alloc, Variable v, ReturnStmt r
where leaked_alloc(alloc, v, r)
select r, "Possible leak of '" + v.getName() + "' allocated at $@ on this return path.",
       alloc, alloc.toString()
