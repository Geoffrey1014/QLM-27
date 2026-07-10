/**
 * @name  rq3-c2-lu-5-rep2
 * @id    cpp/rq3/c2/lu-5-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects memory leaks of resources acquired via kstrdup-family
 *              allocators that are not released on all return paths.
 */

import cpp

predicate is_alloc_call_to_var(Call c, Variable v) {
  c.getTarget().hasName("kstrdup") and
  (
    exists(AssignExpr a |
      a.getRValue() = c and
      a.getLValue() = v.getAnAccess())
    or
    exists(Initializer i |
      i.getExpr() = c and
      i.getDeclaration() = v)
  )
}

predicate is_free_call_on_var(Call c, Variable v) {
  c.getTarget().hasName("kfree") and
  c.getArgument(0) = v.getAnAccess()
}

predicate function_frees_var(Function f, Variable v) {
  exists(Call free |
    is_free_call_on_var(free, v) and
    free.getEnclosingFunction() = f)
}

predicate function_returns_var(Function f, Variable v) {
  exists(ReturnStmt r |
    r.getEnclosingFunction() = f and
    r.getExpr() = v.getAnAccess())
}

predicate alloc_in_function_without_full_release(Call alloc, Variable v, Function f) {
  is_alloc_call_to_var(alloc, v) and
  alloc.getEnclosingFunction() = f and
  // The variable is local to the function (not returned-out, not stored into a struct field)
  v instanceof LocalScopeVariable and
  // Function does not return the variable (so it's not an ownership transfer)
  not function_returns_var(f, v) and
  // There exists at least one return statement in this function that is reachable
  // from the alloc but with no kfree on v on the path. Approximate: function has a
  // return path while the variable is never freed at all, OR the number of frees is
  // strictly less than the number of returns reachable from alloc.
  (
    not function_frees_var(f, v)
    or
    exists(ReturnStmt r |
      r.getEnclosingFunction() = f and
      not exists(Call free |
        is_free_call_on_var(free, v) and
        free.getEnclosingFunction() = f and
        free.getLocation().getStartLine() < r.getLocation().getStartLine()))
  )
}

from Call alloc, Variable v, Function f
where alloc_in_function_without_full_release(alloc, v, f)
select alloc, "Potential memory leak: '" + v.getName() + "' allocated via " +
       alloc.getTarget().getName() + " in function '" + f.getName() +
       "' may not be released on all return paths (no kfree dominates a return)."
