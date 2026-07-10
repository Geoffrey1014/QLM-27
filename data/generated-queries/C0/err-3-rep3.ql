/**
 * @name Missing error code assignment before goto cleanup
 * @description An error-handling branch logs an error (e.g. via dev_err/pr_err/printk(KERN_ERR))
 *              and then jumps to a cleanup/return label via `goto`, but does not assign a
 *              non-zero (negative) error code to the function's return variable. The function
 *              ends up returning success (0 or a stale prior value) even though an error was
 *              detected and logged.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Kernel-style error-logging calls. The presence of one of these on an error branch
 * is a strong signal that the branch is the error path.
 */
predicate isErrorLogCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "dev_err" or
    n = "dev_err_ratelimited" or
    n = "dev_err_probe" or
    n = "dev_warn" or
    n = "pr_err" or
    n = "pr_err_ratelimited" or
    n = "pr_warn" or
    n = "printk" or
    n = "netdev_err" or
    n = "netdev_warn"
  )
}

/**
 * `v` is the function's "return code" local variable: an int-typed local whose value
 * is returned by at least one `return` statement and whose name suggests it
 * (`ret`, `err`, `rc`, `status`, `error`).
 */
predicate isReturnCodeVar(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  (
    v.getName() = "ret" or
    v.getName() = "err" or
    v.getName() = "rc" or
    v.getName() = "status" or
    v.getName() = "error"
  ) and
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = f and
    va = rs.getExpr().(VariableAccess) and
    va.getTarget() = v
  )
}

/**
 * A `goto` statement that follows shortly after an error log call within the same
 * basic block / same enclosing block, on the same error branch.
 */
predicate gotoAfterErrorLog(GotoStmt g, FunctionCall logCall) {
  isErrorLogCall(logCall) and
  g.getEnclosingFunction() = logCall.getEnclosingFunction() and
  exists(Stmt b |
    b = g.getParentStmt+() and
    b = logCall.getEnclosingStmt().getParentStmt+() and
    logCall.getLocation().getStartLine() < g.getLocation().getStartLine() and
    g.getLocation().getStartLine() - logCall.getLocation().getStartLine() <= 5
  )
}

/**
 * Holds if there exists, between (and including) `logCall` and `g`, an assignment
 * of the form `retVar = <expr>;` in the same enclosing block. We use this to RULE
 * OUT the case where the developer did set the error code.
 */
predicate assignsReturnCodeBetween(LocalVariable retVar, FunctionCall logCall, GotoStmt g) {
  exists(AssignExpr ae, VariableAccess lhs |
    lhs = ae.getLValue() and
    lhs.getTarget() = retVar and
    ae.getEnclosingFunction() = g.getEnclosingFunction() and
    ae.getLocation().getStartLine() >= logCall.getLocation().getStartLine() and
    ae.getLocation().getStartLine() <= g.getLocation().getStartLine()
  )
}

/**
 * The target label of `goto` is a cleanup/exit label (heuristic: name contains
 * a typical cleanup token, OR the label is followed by a return statement reachable
 * from it). We use the name-based heuristic to keep the query simple/portable.
 */
predicate isCleanupLabel(GotoStmt g) {
  exists(string n | n = g.getName().toLowerCase() |
    n.matches("%out%") or
    n.matches("%err%") or
    n.matches("%fail%") or
    n.matches("%unlock%") or
    n.matches("%free%") or
    n.matches("%cleanup%") or
    n.matches("%exit%") or
    n.matches("%done%") or
    n.matches("%advance%") or
    n.matches("%release%")
  )
}

from Function f, LocalVariable retVar, FunctionCall logCall, GotoStmt g
where
  isReturnCodeVar(retVar, f) and
  logCall.getEnclosingFunction() = f and
  g.getEnclosingFunction() = f and
  gotoAfterErrorLog(g, logCall) and
  isCleanupLabel(g) and
  not assignsReturnCodeBetween(retVar, logCall, g) and
  // Exclude functions that have no notion of a non-zero return code path (void or pointer return)
  f.getType().getUnspecifiedType() instanceof IntegralType
select g,
  "Error path logs via $@ and jumps to cleanup label '" + g.getName() +
    "' without assigning an error code to '" + retVar.getName() + "'.",
  logCall, logCall.getTarget().getName()
