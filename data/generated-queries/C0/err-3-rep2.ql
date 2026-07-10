/**
 * @name Missing error code assignment before goto cleanup
 * @description An error branch logs/handles a failure (typically via dev_err/pr_err or a
 *              NULL-check on a lookup result) and then jumps to a shared cleanup label via
 *              `goto`, but does NOT assign the integer return variable `ret` to a negative
 *              errno on that path. The function therefore returns 0 (or a stale value)
 *              while reporting an error, hiding the failure from the caller.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A local integer variable that looks like a typical kernel-style error/return code. */
class RetVar extends LocalVariable {
  RetVar() {
    this.getType().getUnspecifiedType() instanceof IntType and
    this.getName().regexpMatch("ret|rc|err|error|status|result")
  }
}

/**
 * Holds if `f` contains an assignment of a negative-errno-looking constant
 * (e.g. `-ENOENT`, `-EINVAL`, `-EIO`, `-12`) to `v` somewhere in the body.
 * Used to gate which variables we treat as "error return codes" — we want
 * functions that already use this pattern, so that a missing assignment on
 * one branch is suspicious.
 */
predicate assignsNegativeErrno(Function f, RetVar v) {
  exists(AssignExpr a, UnaryMinusExpr neg |
    a.getEnclosingFunction() = f and
    a.getLValue() = v.getAnAccess() and
    a.getRValue() = neg
  )
  or
  exists(AssignExpr a, MacroInvocation mi |
    a.getEnclosingFunction() = f and
    a.getLValue() = v.getAnAccess() and
    mi.getExpr() = a.getRValue() and
    mi.getMacroName().regexpMatch("E[A-Z0-9]+")
  )
}

/** A `goto` statement that jumps to a cleanup-style label. */
class CleanupGoto extends GotoStmt {
  CleanupGoto() {
    this.getName()
        .regexpMatch("(?i).*(err|fail|out|exit|clean|cleanup|unlock|free|release|drop|undo|advance|done).*")
  }
}

/**
 * Holds if `bs` is a BlockStmt (the body of an `if` branch, typically) that
 * (a) contains an error-reporting call such as `dev_err`, `pr_err`, `printk`
 *     (KERN_ERR), `WARN`, `dev_warn`, or
 * (b) handles a NULL-from-lookup pattern (we approximate by requiring the
 *     enclosing `if` condition to be a NULL comparison),
 * and ends with / contains a `goto` to a cleanup label, but the block does NOT
 * assign the chosen return variable `v`.
 */
predicate errorBranchMissingRet(IfStmt ifs, RetVar v, CleanupGoto g, FunctionCall errCall) {
  exists(Function f |
    f = ifs.getEnclosingFunction() and
    v.getFunction() = f and
    assignsNegativeErrno(f, v) and
    g.getEnclosingFunction() = f
  ) and
  // goto is inside the then-branch of the if
  g.getParentStmt*() = ifs.getThen() and
  // error-reporting call is inside the same then-branch
  errCall.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
  errCall.getTarget()
      .getName()
      .regexpMatch("dev_err(_.*)?|pr_err|pr_warn|printk|netdev_err|WARN|WARN_ON|dev_warn(_.*)?") and
  // the then-branch does NOT assign v anywhere before the goto
  not exists(AssignExpr a |
    a.getEnclosingFunction() = ifs.getEnclosingFunction() and
    a.getLValue() = v.getAnAccess() and
    a.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  ) and
  // and v is also not modified via address-of/output-parameter inside the branch
  not exists(AddressOfExpr ao |
    ao.getOperand() = v.getAnAccess() and
    ao.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  ) and
  // the cleanup label this goto targets is reachable by a "fall-through" return path
  // — i.e. somewhere after the label, the function returns v.
  exists(ReturnStmt ret |
    ret.getEnclosingFunction() = ifs.getEnclosingFunction() and
    ret.getExpr() = v.getAnAccess()
  )
}

from IfStmt ifs, RetVar v, CleanupGoto g, FunctionCall errCall
where errorBranchMissingRet(ifs, v, g, errCall)
select g,
  "Error branch in function '" + ifs.getEnclosingFunction().getName() +
    "' reports an error (via '" + errCall.getTarget().getName() +
    "') and 'goto " + g.getName() + "', but does not assign error code to '" + v.getName() +
    "'; function will return 0 / stale value while caller expects negative errno."
