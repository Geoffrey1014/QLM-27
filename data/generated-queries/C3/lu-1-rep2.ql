/**
 * @name Missing sctp_association_free on error path
 * @description Detects an allocated sctp_association from sctp_make_temp_asoc
 *              that is not released on an early error-return path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/lu-1-rep2
 */
import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "sctp_make_temp_asoc"
}

Variable getAcquiredVar(FunctionCall fc) {
  result.getAnAssignedValue() = fc and isAcquire(fc)
}

predicate isReleaseOf(FunctionCall rc, Variable v) {
  rc.getTarget().getName() = "sctp_association_free" and
  rc.getAnArgument().(VariableAccess).getTarget() = v
}

predicate errorReturnAfterAcquire(FunctionCall fc, ReturnStmt ret) {
  isAcquire(fc) and
  ret.getEnclosingFunction() = fc.getEnclosingFunction() and
  ret.getLocation().getStartLine() > fc.getLocation().getStartLine() and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = fc.getEnclosingFunction() and
    ifs.getThen() = ret and
    ifs.getCondition().getAChild*() instanceof FunctionCall
  )
}

from FunctionCall acquire, Variable v, ReturnStmt ret
where
  isAcquire(acquire) and
  v = getAcquiredVar(acquire) and
  errorReturnAfterAcquire(acquire, ret) and
  not exists(FunctionCall rc |
    isReleaseOf(rc, v) and
    rc.getEnclosingFunction() = acquire.getEnclosingFunction()
  )
select acquire,
  "Possible missing sctp_association_free for variable $@ before early return on line " +
    ret.getLocation().getStartLine().toString(),
  v, v.getName()
