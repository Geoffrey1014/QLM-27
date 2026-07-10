/**
 * @name  rq3-c2-lu-1-rep4
 * @id    cpp/rq3/c2/lu-1-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing sctp_association_free on the
 *              security_sctp_assoc_request error path, generalized to
 *              acquire/release lifecycle bugs around a guard call.
 */

import cpp

/**
 * The resource-acquisition call: returns/produces a critical association
 * pointer. We approximate by looking at functions whose name contains
 * "asoc" and "new" or "make_temp", producing a Variable later released.
 */
predicate acquiresAssociation(FunctionCall acq, Variable v) {
  exists(string n | n = acq.getTarget().getName() |
    n.matches("%make_temp_asoc%") or
    n.matches("%make%asoc%") or
    n.matches("sctp_association_new%")
  ) and
  (
    exists(AssignExpr a | a.getRValue() = acq and a.getLValue() = v.getAnAccess())
    or
    exists(Initializer i | i.getExpr() = acq and i.getDeclaration() = v)
  )
}

/**
 * Guard call: a function call whose return value is tested as a condition
 * that, when non-zero, takes an error-exit path. Specifically targets
 * security_* hook checks (LSM pattern) but kept general.
 */
predicate isGuardCall(FunctionCall guard) {
  guard.getTarget().getName().matches("security_%") and
  exists(IfStmt ifs | ifs.getCondition().getAChild*() = guard)
}

/**
 * A return statement is reachable from the true-branch of a guard-call IfStmt
 * without any intervening release call on `v`.
 */
predicate guardedErrorReturn(FunctionCall guard, Variable v, ReturnStmt ret) {
  exists(IfStmt ifs |
    ifs.getCondition().getAChild*() = guard and
    ret.getEnclosingStmt*() = ifs.getThen() and
    not exists(FunctionCall rel |
      rel.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
      rel.getTarget().getName().matches("%association_free%") and
      rel.getAnArgument() = v.getAnAccess()
    )
  )
}

/**
 * The buggy pattern: an acquisition of variable v in function f, followed
 * by a guard call whose error-return path does not release v.
 */
predicate buggyMissingRelease(Function f, Variable v, FunctionCall acq, FunctionCall guard, ReturnStmt ret) {
  acquiresAssociation(acq, v) and
  acq.getEnclosingFunction() = f and
  isGuardCall(guard) and
  guard.getEnclosingFunction() = f and
  guardedErrorReturn(guard, v, ret) and
  ret.getEnclosingFunction() = f and
  // ordering: acquisition lexically before guard
  acq.getLocation().getStartLine() < guard.getLocation().getStartLine()
}

from Function f, Variable v, FunctionCall acq, FunctionCall guard, ReturnStmt ret
where buggyMissingRelease(f, v, acq, guard, ret)
select ret,
  "Possible missing sctp_association_free of '" + v.getName() +
  "' on error return after guard call '" + guard.getTarget().getName() + "'."
