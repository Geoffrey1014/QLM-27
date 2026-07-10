/**
 * @name Missing error return code on allocation-failure goto
 * @description An allocation function returns NULL and the code branches to a
 *              cleanup/error label via goto, but the function's error-return
 *              variable is not assigned a negative errno before the goto. The
 *              function then silently returns 0 (success) despite the failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-on-alloc-failure-goto
 * @tags reliability
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * Allocation-like functions whose NULL return indicates failure.
 */
predicate isAllocFunction(Function f) {
  f.getName() =
    [
      "vzalloc", "vmalloc", "kmalloc", "kzalloc", "kcalloc", "kmalloc_array",
      "kvmalloc", "kvzalloc", "kvcalloc", "kvmalloc_array", "krealloc",
      "kmemdup", "kstrdup", "kstrndup", "alloc_pages", "__get_free_pages",
      "devm_kmalloc", "devm_kzalloc", "devm_kcalloc",
      "of_node_get", "of_parse_phandle", "of_find_node_by_name",
      "of_find_node_by_path", "of_get_child_by_name", "of_get_next_child",
      "of_get_parent",
      "kmem_cache_alloc", "kmem_cache_zalloc", "mempool_alloc"
    ]
}

/**
 * The local variable used to hold the function's error return code.
 * Heuristic: an int-typed local named "ret", "err", "rc", or "error"
 * that is returned from the enclosing function.
 */
predicate isErrorReturnVar(LocalVariable v, Function enclosing) {
  v.getFunction() = enclosing and
  v.getName() = ["ret", "err", "rc", "error", "status"] and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = enclosing and
    va = rs.getExpr().(VariableAccess) and
    va.getTarget() = v
  )
}

from
  FunctionCall allocCall, LocalVariable resultVar, IfStmt ifs, GotoStmt g,
  Function enclosing, LocalVariable errVar
where
  isAllocFunction(allocCall.getTarget()) and
  enclosing = allocCall.getEnclosingFunction() and
  // resultVar receives the allocation
  (
    exists(AssignExpr ae |
      ae.getRValue() = allocCall and
      ae.getLValue().(VariableAccess).getTarget() = resultVar
    )
    or
    exists(Initializer init |
      init.getExpr() = allocCall and init.getDeclaration() = resultVar
    )
  ) and
  // an if(!resultVar) (or equivalent NULL-check) guards the goto
  ifs.getEnclosingFunction() = enclosing and
  exists(Expr cond | cond = ifs.getCondition() |
    cond.(NotExpr).getOperand().(VariableAccess).getTarget() = resultVar
    or
    exists(EQExpr eq | eq = cond |
      eq.getAnOperand().(VariableAccess).getTarget() = resultVar and
      eq.getAnOperand() instanceof NullValue
    )
  ) and
  g.getEnclosingStmt+() = ifs.getThen() and
  // function has an error-return variable that IS returned
  isErrorReturnVar(errVar, enclosing) and
  // resultVar is NOT the same as errVar
  resultVar != errVar and
  // the then-branch does not assign errVar before the goto
  not exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = errVar
  )
select g,
  "Missing error code assignment to '" + errVar.getName() +
    "' before goto on failure of allocation call to '" +
    allocCall.getTarget().getName() + "'; function may return success despite failure."
