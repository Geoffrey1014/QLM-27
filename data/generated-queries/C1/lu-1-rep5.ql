/**
 * @name Missing release of resource on error path after security/validation check
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-1
 * @description A function allocates a resource via an allocator API, then on
 *              an error branch (guarded by a security/validation/check call)
 *              executes an error-handling action (a discard/pdiscard-style
 *              call) without invoking the matching release function on the
 *              critical variable. This is the missing-free-on-error-path
 *              pattern fixed by the lu-1 seed commit.
 */

import cpp

/**
 * A call that allocates / acquires a resource and binds its result into a
 * local variable.
 */
predicate isAllocCall(FunctionCall fc, LocalVariable v) {
  exists(string n | n = fc.getTarget().getName() |
    n.regexpMatch("(?i).*(alloc|kmalloc|kzalloc|kcalloc|vmalloc|kmemdup|" +
                  "make_temp_asoc|create|new|acquire|grab|get_temp).*")
  ) and
  (
    fc = v.getInitializer().getExpr()
    or
    exists(AssignExpr ae |
      ae.getRValue() = fc and
      ae.getLValue() = v.getAnAccess()
    )
  )
}

/** A release / free call on the critical variable v. */
predicate isReleaseCallOn(FunctionCall rc, LocalVariable v) {
  exists(string n | n = rc.getTarget().getName() |
    n.regexpMatch("(?i).*(free|release|put|destroy|kfree|vfree|drop|" +
                  "dealloc|unref|cleanup).*")
  ) and
  rc.getAnArgument() = v.getAnAccess()
}

/** A "check" call (security/validation) that gates an error path. */
predicate isCheckCall(FunctionCall cc) {
  cc.getTarget().getName()
    .regexpMatch("(?i).*(security_|check_|verify_|validate_|_request).*")
}

/**
 * A call modelling the error-handling action taken on the error path
 * (discard/pdiscard/error/abort/reject). Used both to identify the
 * error branch and to anchor the leak report.
 */
predicate isErrorHandlerCall(FunctionCall ec) {
  ec.getTarget().getName()
    .regexpMatch("(?i).*(pdiscard|discard|_error|reject|abort|drop_|fail).*")
}

from Function f, LocalVariable v, FunctionCall alloc, IfStmt errIf,
     FunctionCall checkCall, FunctionCall errHandler
where
  v.getFunction() = f and
  isAllocCall(alloc, v) and
  alloc.getEnclosingFunction() = f and
  // The if's condition is a check call.
  errIf.getEnclosingFunction() = f and
  (
    errIf.getCondition() = checkCall
    or
    errIf.getCondition().(UnaryLogicalOperation).getOperand() = checkCall
    or
    errIf.getCondition().(BinaryLogicalOperation).getAnOperand() = checkCall
  ) and
  isCheckCall(checkCall) and
  // The then-branch contains an error-handler call (this is the bug's
  // error-handling action).
  errHandler.getEnclosingFunction() = f and
  isErrorHandlerCall(errHandler) and
  errHandler.getEnclosingStmt().getParentStmt*() = errIf.getThen() and
  // The alloc precedes the if (source-order proxy).
  alloc.getLocation().getStartLine() < errIf.getLocation().getStartLine() and
  // No release of v inside the error branch.
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    isReleaseCallOn(rel, v) and
    rel.getEnclosingStmt().getParentStmt*() = errIf.getThen()
  ) and
  // No release of v between alloc and error-handler (covers single-return
  // shapes where release would precede the if).
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    isReleaseCallOn(rel, v) and
    rel.getLocation().getStartLine() >= alloc.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= errHandler.getLocation().getStartLine()
  )
select errHandler,
  "Possible resource leak: '" + v.getName() + "' allocated by '" +
  alloc.getTarget().getName() +
  "' is not released before this error-handling call on the failure path of '" +
  checkCall.getTarget().getName() + "'."
