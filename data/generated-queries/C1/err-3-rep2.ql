/**
 * @name Error path forgets to set negative errno before goto / return
 * @description Detects functions that declare a local error-code
 *              variable (e.g. `int ret = 0;`), log an error via
 *              dev_err/pr_err on an error path, then `goto` a common
 *              cleanup label whose body returns the variable, but
 *              never assign a negative errno to that variable
 *              between the log and the return. The caller therefore
 *              receives 0 (success) and silently proceeds. This is
 *              the QLM "error-return" pattern.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-3
 * @tags correctness
 *       kernel
 */

import cpp

/* Kernel error-logging APIs that strongly indicate an error path. */
predicate isErrorLogApi(string name) {
  name = "dev_err" or
  name = "dev_err_once" or
  name = "dev_err_ratelimited" or
  name = "pr_err" or
  name = "pr_err_once" or
  name = "pr_err_ratelimited" or
  name = "netdev_err" or
  name = "WARN" or
  name = "WARN_ON" or
  name = "WARN_ONCE"
}

/* Local int-typed variable initialised to a compile-time zero. */
predicate isZeroInitErrnoLocal(LocalVariable v) {
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(Expr init | init = v.getInitializer().getExpr() |
    init.getValue().toInt() = 0
  )
}

/* Conventional kernel names for an error-return holder. */
predicate hasErrnoLikeName(LocalVariable v) {
  exists(string n | n = v.getName() |
    n = "ret" or n = "err" or n = "rc" or n = "error" or n = "status"
  )
}

/* Negative-looking RHS: literal negative or unary-minus of a macro
 * expansion (e.g. -ENOENT). */
predicate isNegativeExpr(Expr e) {
  e.getValue().toInt() < 0
  or
  e instanceof UnaryMinusExpr
}

/* Assignment of a negative value to `v` somewhere in `f`. */
predicate assignsNegative(Function f, LocalVariable v, AssignExpr a) {
  a.getEnclosingFunction() = f and
  a.getLValue() = v.getAnAccess() and
  isNegativeExpr(a.getRValue())
}

from Function f, LocalVariable v, FunctionCall logCall, GotoStmt g,
     ReturnStmt rs
where
  v.getFunction() = f and
  isZeroInitErrnoLocal(v) and
  hasErrnoLikeName(v) and
  /* An error-log call lives in f. */
  logCall.getEnclosingFunction() = f and
  isErrorLogApi(logCall.getTarget().getName()) and
  /* A goto in f that the log can reach. */
  g.getEnclosingFunction() = f and
  logCall.getASuccessor+() = g and
  /* The goto's target eventually reaches a `return v;`. */
  rs.getEnclosingFunction() = f and
  exists(VariableAccess retAcc |
    retAcc = rs.getExpr() and retAcc.getTarget() = v
  ) and
  g.getTarget().getASuccessor*() = rs and
  /* CRITICAL BUG CONDITION: there is NO assignment of a negative value
   * to v anywhere on the path from the log to the return. We approximate
   * "on the path" by: any negative assignment to v in f must either
   * happen before the log call or after the return — i.e. it cannot be
   * "between" log and return in the control flow. */
  not exists(AssignExpr a |
    assignsNegative(f, v, a) and
    logCall.getASuccessor+() = a and
    a.getASuccessor+() = rs
  )
select logCall,
  "Error path in '" + f.getName() + "' logs an error and goto/returns '" +
  v.getName() + "' without assigning a negative errno; caller receives 0."
