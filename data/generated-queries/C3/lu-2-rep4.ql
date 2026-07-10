/**
 * @name Memory leak: kmalloc with early-return bypassing kfree
 * @description Detects kmalloc-family allocations whose enclosing function
 *              contains a ReturnStmt that is not preceded on its CFG path
 *              by a kfree on the allocated variable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-c3-lu2-rep4
 */
import cpp
import semmle.code.cpp.controlflow.StackVariableReachability

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kcalloc"
}

predicate isReleaseCall(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "kfree" and
  fc.getArgument(0) = v.getAnAccess()
}

/* `v` is assigned the result of an acquire call inside function f. */
predicate acquiredInto(Variable v, FunctionCall acq, Function f) {
  isAcquireCall(acq) and
  acq.getEnclosingFunction() = f and
  exists(AssignExpr ae |
    ae.getRValue() = acq and
    ae.getLValue() = v.getAnAccess()
  )
}

/* A ReturnStmt `r` in function f that is NOT preceded (on any control-flow
 * path from acq) by a kfree of v. We approximate using a forward reachability
 * walk on the CFG that stops at any release of v. */
predicate returnLeaks(FunctionCall acq, Variable v, ReturnStmt r) {
  acquiredInto(v, acq, r.getEnclosingFunction()) and
  exists(ControlFlowNode n |
    n = r and
    acq.getASuccessor+() = n and
    not exists(FunctionCall rel |
      isReleaseCall(rel, v) and
      acq.getASuccessor+() = rel and
      rel.getASuccessor+() = r
    )
  )
}

from FunctionCall acq, Variable v, ReturnStmt r
where returnLeaks(acq, v, r)
select acq,
  "Possible memory leak: '" + v.getName() +
  "' allocated by " + acq.getTarget().getName() +
  "() may be leaked at return on line " + r.getLocation().getStartLine() + "."
