/**
 * @name Missing error code assignment before goto on error path
 * @description Detects functions that, on a detected error condition, log an error
 *              (via dev_err / pr_err / printk(KERN_ERR ...) / dev_warn) and then
 *              `goto` a cleanup label without first assigning a negative error code
 *              to the return-status variable. The function therefore returns 0
 *              (success) even though an error was diagnosed.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A kernel error-logging call. */
class KernelErrorLog extends FunctionCall {
  KernelErrorLog() {
    exists(string n | n = this.getTarget().getName() |
      n = "dev_err" or
      n = "dev_err_ratelimited" or
      n = "dev_err_once" or
      n = "dev_warn" or
      n = "pr_err" or
      n = "pr_err_ratelimited" or
      n = "pr_warn" or
      n = "netdev_err" or
      n = "netdev_warn"
    )
  }
}

/** A goto that targets a "cleanup-ish" label (heuristic). */
class CleanupGoto extends GotoStmt {
  CleanupGoto() {
    exists(string lname | lname = this.getName().toLowerCase() |
      lname.matches("%out%") or
      lname.matches("%err%") or
      lname.matches("%fail%") or
      lname.matches("%exit%") or
      lname.matches("%cleanup%") or
      lname.matches("%unlock%") or
      lname.matches("%free%") or
      lname.matches("%release%") or
      lname.matches("%done%") or
      lname.matches("%advance%") or
      lname.matches("%drop%") or
      lname.matches("%discard%")
    )
  }
}

/** A local variable that looks like an error-return holder. */
class RetVar extends LocalVariable {
  RetVar() {
    exists(string n | n = this.getName() |
      n = "ret" or n = "err" or n = "rc" or n = "error" or n = "status" or n = "result"
    ) and
    this.getType().getUnspecifiedType() instanceof IntegralType
  }
}

/**
 * Holds if `goto_stmt` is in a function that has a local return-holder `ret`
 * which the function ultimately returns, and on the basic block path that
 * leads up to `goto_stmt` (starting from the immediately preceding error
 * log call), there is NO assignment of a (negative or non-zero) error code
 * to `ret`.
 */
predicate missingErrorAssign(KernelErrorLog logCall, CleanupGoto gotoStmt, RetVar ret) {
  // Both in the same function.
  logCall.getEnclosingFunction() = gotoStmt.getEnclosingFunction() and
  ret.getFunction() = gotoStmt.getEnclosingFunction() and
  // The enclosing function returns `ret`.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = gotoStmt.getEnclosingFunction() and
    rs.getExpr().(VariableAccess).getTarget() = ret
  ) and
  // Same basic block: log call then goto, no statement between them assigns ret.
  logCall.getEnclosingStmt().getBasicBlock() = gotoStmt.getBasicBlock() and
  logCall.getLocation().getStartLine() < gotoStmt.getLocation().getStartLine() and
  // No assignment to `ret` between the log call and the goto.
  not exists(Assignment a |
    a.getLValue().(VariableAccess).getTarget() = ret and
    a.getEnclosingFunction() = gotoStmt.getEnclosingFunction() and
    a.getLocation().getStartLine() >= logCall.getLocation().getStartLine() and
    a.getLocation().getStartLine() <= gotoStmt.getLocation().getStartLine()
  ) and
  // And `ret` has been initialized to 0 (or never reassigned to negative)
  // somewhere earlier in the function — heuristic: there exists an
  // initializer / assignment of 0 to ret earlier in the function.
  exists(Expr zeroInit |
    (
      ret.getInitializer().getExpr() = zeroInit
      or
      exists(Assignment a0 |
        a0.getLValue().(VariableAccess).getTarget() = ret and
        a0.getRValue() = zeroInit and
        a0.getEnclosingFunction() = gotoStmt.getEnclosingFunction() and
        a0.getLocation().getStartLine() < logCall.getLocation().getStartLine()
      )
    ) and
    zeroInit.getValue().toInt() = 0
  )
}

from KernelErrorLog logCall, CleanupGoto gotoStmt, RetVar ret
where missingErrorAssign(logCall, gotoStmt, ret)
select gotoStmt,
  "On error path, '" + ret.getName() + "' is not assigned a negative error code before 'goto " +
    gotoStmt.getName() + "' (preceding error log at $@); function may return 0 on failure.",
  logCall, logCall.getTarget().getName()
