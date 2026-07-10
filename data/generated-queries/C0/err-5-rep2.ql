/**
 * @name Missing error code assignment on allocation failure before goto
 * @description An allocation function returns NULL, and the failure branch jumps to
 *              a cleanup label via goto without first assigning a negative error
 *              code to the function's return-value variable. The function may then
 *              return 0 (success) despite the allocation failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-errno-before-goto-on-alloc-failure
 * @tags correctness
 *       reliability
 */

import cpp

/** Common kernel allocator functions whose NULL return indicates failure. */
predicate isAllocFunction(Function f) {
  f.getName() in [
      "vzalloc", "vmalloc", "kmalloc", "kzalloc", "kcalloc", "kmalloc_array",
      "kmem_cache_alloc", "kmem_cache_zalloc", "krealloc", "kvmalloc", "kvzalloc",
      "kvcalloc", "kstrdup", "kmemdup", "devm_kmalloc", "devm_kzalloc",
      "devm_kcalloc", "alloc_pages", "__get_free_pages", "alloc_skb",
      "kasprintf", "kvasprintf", "vmalloc_user", "vmalloc_node", "vzalloc_node"
    ]
}

/** A NULL-check on a variable: `if (!v)` or `if (v == NULL)`. */
predicate nullCheckOn(IfStmt ifs, Variable v) {
  exists(Expr cond | cond = ifs.getCondition() |
    cond.(NotExpr).getOperand() = v.getAnAccess()
    or
    exists(EQExpr eq |
      eq = cond and
      eq.getAnOperand() = v.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
  )
}

/** Holds if `body` (transitively) contains the given goto statement. */
predicate gotoIn(Stmt body, GotoStmt gs) {
  gs.getParentStmt*() = body
}

/**
 * Holds if `branch` does NOT contain an assignment to `retVar` of a negative
 * integer (i.e. error code such as -ENOMEM, -EINVAL) or a known err-producing
 * helper.
 */
predicate noErrAssign(Stmt branch, Variable retVar) {
  not exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = branch and
    ae.getLValue() = retVar.getAnAccess() and
    (
      ae.getRValue() instanceof UnaryMinusExpr
      or
      exists(FunctionCall fc |
        fc = ae.getRValue() and
        fc.getTarget().getName() in ["PTR_ERR", "ERR_PTR"]
      )
      or
      ae.getRValue().getValue().regexpMatch("-[0-9]+")
    )
  )
}

/**
 * The enclosing function's "return variable": a local int-typed variable that
 * is eventually returned, conventionally named `ret`, `rc`, `err`, etc.
 */
predicate isReturnVar(Function f, Variable v) {
  v.(LocalVariable).getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  v.getName().regexpMatch("ret|rc|err|error|status") and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = v.getAnAccess()
  )
}

from
  Function f, AssignExpr allocAssign, FunctionCall allocCall,
  IfStmt ifs, Variable allocVar, Variable retVar, GotoStmt gs, Stmt branch
where
  // allocation: lvar = alloc(...)
  allocCall = allocAssign.getRValue() and
  isAllocFunction(allocCall.getTarget()) and
  allocAssign.getLValue() = allocVar.getAnAccess() and
  allocAssign.getEnclosingFunction() = f and
  // null-check on the allocated variable
  ifs.getEnclosingFunction() = f and
  nullCheckOn(ifs, allocVar) and
  // then-branch contains a goto
  branch = ifs.getThen() and
  gotoIn(branch, gs) and
  // function has a designated return variable
  isReturnVar(f, retVar) and
  retVar != allocVar and
  // no error code is assigned to retVar in the then-branch before the goto
  noErrAssign(branch, retVar) and
  // there exists a `return retVar;` somewhere in the function
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = retVar.getAnAccess()
  )
select ifs,
  "Allocation '" + allocVar.getName() +
    "' may fail, but '" + retVar.getName() +
    "' is not set to an error code before jumping to cleanup; function may return 0."
