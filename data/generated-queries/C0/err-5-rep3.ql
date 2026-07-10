/**
 * @name Missing error code assignment before cleanup goto on allocation failure
 * @description An allocation function returns NULL and control flows to a cleanup label
 *              via `goto`, but the function's return-code variable is not set to a
 *              negative errno value first. The function therefore returns whatever
 *              prior value (often 0/success) was in the return variable, masking the
 *              failure to the caller.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-errno-before-goto-cleanup
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.dataflow.DataFlow

/**
 * Functions that allocate kernel memory / resources and return NULL on failure.
 * Generalizes beyond `vzalloc` to the whole k*alloc / v*alloc family + a few
 * common siblings.
 */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "vzalloc" or n = "vmalloc" or n = "vmalloc_node" or n = "vzalloc_node" or
    n = "kmalloc" or n = "kzalloc" or n = "kcalloc" or n = "kmalloc_array" or
    n = "krealloc" or n = "kmemdup" or n = "kstrdup" or n = "kstrndup" or
    n = "kmalloc_node" or n = "kzalloc_node" or
    n = "alloc_pages" or n = "alloc_pages_node" or n = "__get_free_pages" or
    n = "devm_kzalloc" or n = "devm_kmalloc" or n = "devm_kcalloc"
  )
}

/**
 * Holds if `v` is the function-scope variable that holds the integer return
 * status (the typical `int ret` / `int err` / `int rc`).
 */
predicate isErrVar(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnderlyingType() instanceof IntType and
  (v.getName() = "ret" or v.getName() = "err" or v.getName() = "rc" or
   v.getName() = "error" or v.getName() = "result")
}

/**
 * Holds if `f` returns `v` (directly or via an expression containing only `v`).
 */
predicate returnsErrVar(Function f, LocalVariable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v
  )
}

/**
 * The `if (!alloc_call()) goto label;` shape (or `if (alloc_call() == NULL)`).
 * Captures the IfStmt, the goto, and the allocation call.
 */
predicate nullCheckGoto(IfStmt ifs, GotoStmt gs, FunctionCall alloc) {
  isAllocCall(alloc) and
  // condition tests the allocation result for NULL
  (
    ifs.getCondition().(NotExpr).getOperand() = alloc
    or
    exists(EQExpr eq | eq = ifs.getCondition() and
      (eq.getLeftOperand() = alloc or eq.getRightOperand() = alloc))
    or
    exists(VariableAccess va, LocalVariable lv |
      DataFlow::localFlow(DataFlow::exprNode(alloc), DataFlow::exprNode(va)) and
      va.getTarget() = lv and
      (
        ifs.getCondition().(NotExpr).getOperand() = va
        or
        exists(EQExpr eq | eq = ifs.getCondition() and
          (eq.getLeftOperand() = va or eq.getRightOperand() = va))
      )
    )
  ) and
  // the then-branch contains the goto
  gs.getParentStmt*() = ifs.getThen()
}

/**
 * Holds if there is an assignment to `v` of a non-zero (typically negative
 * errno) expression somewhere in the then-branch reachable before `gs`.
 * We approximate "set to error code" by: any assignment to v whose RHS is not
 * a literal zero.
 */
predicate setsErrInThen(Stmt thenBranch, LocalVariable v) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = thenBranch and
    ae.getLValue().(VariableAccess).getTarget() = v and
    not ae.getRValue().getValue() = "0"
  )
}

from
  Function f, LocalVariable retVar, IfStmt ifs, GotoStmt gs, FunctionCall alloc
where
  f = ifs.getEnclosingFunction() and
  isErrVar(retVar, f) and
  returnsErrVar(f, retVar) and
  nullCheckGoto(ifs, gs, alloc) and
  alloc.getEnclosingFunction() = f and
  // no error-code assignment in the failing branch
  not setsErrInThen(ifs.getThen(), retVar) and
  // exclude functions whose retVar is initialized to a non-zero value at decl
  not exists(Expr init |
    init = retVar.getInitializer().getExpr() and
    not init.getValue() = "0"
  )
select ifs,
  "Allocation '" + alloc.getTarget().getName() +
    "()' failure path goes to '" + gs.getName() +
    "' without setting return variable '" + retVar.getName() +
    "' to an error code; function may return success on failure."
