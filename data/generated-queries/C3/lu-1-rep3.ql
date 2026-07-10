/**
 * @name Missing release of acquired SCTP association before error return
 * @description Detects functions that call an acquire-style API (e.g.
 *              sctp_unpack_cookie) storing the result in a local variable,
 *              then take an error-return path guarded by an if-statement
 *              without first invoking the matching release function on
 *              that variable. Inspired by the fix b6631c6031c7.
 * @kind problem
 * @problem.severity warning
 * @id qlm/missing-sctp-association-free-on-error
 * @tags reliability security correctness
 */

import cpp

/* --- Predicates (compositional, POC-validated) --- */

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "sctp_unpack_cookie"
}

predicate isReleaseCall(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "sctp_association_free" and
  fc.getArgument(0) = v.getAnAccess()
}

predicate isErrorReturnAfter(FunctionCall acquire, ReturnStmt ret) {
  isAcquireCall(acquire) and
  exists(Function f, IfStmt ifs |
    acquire.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    ifs.getEnclosingFunction() = f and
    acquire.getLocation().getStartLine() < ifs.getLocation().getStartLine() and
    ifs.getThen().getAChild*() = ret
  )
}

predicate noReleaseBetween(FunctionCall acquire, ReturnStmt ret, Variable v) {
  not exists(FunctionCall rel |
    isReleaseCall(rel, v) and
    rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rel.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

/* --- Final assembly --- */

predicate acquireBindsVar(FunctionCall acquire, LocalVariable v) {
  v.getInitializer().getExpr() = acquire
  or
  exists(AssignExpr ae |
    ae.getRValue() = acquire and ae.getLValue() = v.getAnAccess()
  )
}

from FunctionCall acquire, ReturnStmt ret, LocalVariable v
where
  isAcquireCall(acquire) and
  acquireBindsVar(acquire, v) and
  isErrorReturnAfter(acquire, ret) and
  noReleaseBetween(acquire, ret, v)
select acquire,
  "Possible missing release of '" + v.getName() + "' before error return on line " +
  ret.getLocation().getStartLine().toString()
