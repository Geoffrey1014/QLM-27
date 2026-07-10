/**
 * @name  rq3-c2-lu-2-rep1
 * @id    cpp/rq3/c2/lu-2-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects a memory leak where a kmalloc-family allocation is
 *              followed by an early return path that does not flow through
 *              the corresponding kfree.
 */

import cpp

predicate is_alloc(FunctionCall c, Variable v) {
  c.getTarget().getName().regexpMatch("k[mz]alloc|kmalloc_array|kcalloc|kzalloc_node|kmalloc_node|kvmalloc|kvzalloc|vmalloc") and
  exists(AssignExpr a |
    a.getRValue() = c and
    a.getLValue() = v.getAnAccess()
  )
}

predicate is_free_of(FunctionCall c, Variable v) {
  c.getTarget().getName().regexpMatch("kfree|kvfree|vfree|kzfree") and
  c.getArgument(0) = v.getAnAccess()
}

predicate function_has_alloc_and_free(Function f, Variable v) {
  exists(FunctionCall ac | is_alloc(ac, v) and ac.getEnclosingFunction() = f) and
  exists(FunctionCall fc | is_free_of(fc, v) and fc.getEnclosingFunction() = f)
}

predicate return_bypasses_free(ReturnStmt r, Variable v) {
  exists(Function f, FunctionCall ac |
    r.getEnclosingFunction() = f and
    function_has_alloc_and_free(f, v) and
    is_alloc(ac, v) and
    ac.getEnclosingFunction() = f and
    ac.getLocation().getStartLine() < r.getLocation().getStartLine() and
    not exists(FunctionCall fc |
      is_free_of(fc, v) and
      fc.getEnclosingFunction() = f and
      fc.getASuccessor*() = r
    )
  )
}

from ReturnStmt r, Variable v, Function f
where
  return_bypasses_free(r, v) and
  r.getEnclosingFunction() = f
select r, "Potential memory leak: early return in $@ bypasses kfree of '" + v.getName() + "'.",
  f, f.getName()
