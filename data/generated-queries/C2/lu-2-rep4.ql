/**
 * @name  rq3-c2-lu-2-rep4
 * @id    cpp/rq3/c2/lu-2-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects memory allocated via kmalloc-family that is leaked
 *              on an early-return path within a function that elsewhere
 *              frees the same variable (i.e., the cleanup path was skipped).
 */
import cpp

predicate is_alloc_call(FunctionCall fc, Variable v) {
  fc.getTarget().getName().regexpMatch("k[mz]alloc|kmalloc_array|kcalloc|kzalloc_node|kmalloc_node|vmalloc|vzalloc") and
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = v.getAnAccess()
  )
}

predicate is_free_call_on(FunctionCall fc, Variable v) {
  fc.getTarget().getName().regexpMatch("kfree|vfree|kvfree|kzfree|kfree_sensitive") and
  fc.getAnArgument() = v.getAnAccess()
}

predicate function_has_free_for(Function f, Variable v) {
  exists(FunctionCall fc |
    is_free_call_on(fc, v) and
    fc.getEnclosingFunction() = f
  )
}

predicate early_return_after_alloc(FunctionCall alloc, Variable v, ReturnStmt rs) {
  is_alloc_call(alloc, v) and
  rs.getEnclosingFunction() = alloc.getEnclosingFunction() and
  alloc.(ControlFlowNode).getASuccessor*() = rs and
  not exists(FunctionCall freec |
    is_free_call_on(freec, v) and
    freec.getEnclosingFunction() = alloc.getEnclosingFunction() and
    alloc.(ControlFlowNode).getASuccessor*() = freec and
    freec.(ControlFlowNode).getASuccessor*() = rs
  )
}

predicate leaks_on_return(FunctionCall alloc, Variable v, ReturnStmt rs) {
  is_alloc_call(alloc, v) and
  function_has_free_for(alloc.getEnclosingFunction(), v) and
  early_return_after_alloc(alloc, v, rs)
}

from FunctionCall alloc, Variable v, ReturnStmt rs
where leaks_on_return(alloc, v, rs)
select rs,
  "Possible memory leak: '" + v.getName() + "' allocated at $@ is not freed on this return path.",
  alloc, alloc.toString()
