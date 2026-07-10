/**
 * @name  rq3-c2-lu-5-rep1
 * @id    cpp/rq3/c2/lu-5-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects kstrdup allocations whose result variable is not
 *              released by kfree on some path to function exit.
 */
import cpp
import semmle.code.cpp.controlflow.Guards

/** A call to kstrdup whose return value is stored into a local variable. */
predicate isAllocCall(FunctionCall fc, Variable v) {
  fc.getTarget().hasName("kstrdup") and
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = v.getAnAccess()
  )
}

/** A call to kfree on the given variable. */
predicate isReleaseCall(FunctionCall fc, Variable v) {
  fc.getTarget().hasName("kfree") and
  fc.getArgument(0) = v.getAnAccess()
}

/** Holds if there is a control-flow path from `alloc` to function exit
 *  along which no `kfree(v)` is executed. */
predicate allocReachesExitWithoutRelease(FunctionCall alloc, Variable v) {
  isAllocCall(alloc, v) and
  exists(Function f |
    f = alloc.getEnclosingFunction() and
    // exists at least one path where no release happens
    exists(ControlFlowNode exit |
      exit = f and
      alloc.getASuccessor+() = exit and
      not exists(FunctionCall rel |
        isReleaseCall(rel, v) and
        rel.getEnclosingFunction() = f and
        alloc.getASuccessor+() = rel and
        rel.getASuccessor+() = exit
      )
    )
  )
}

/** Variable v is local to the enclosing function of `alloc`. */
predicate isLocalToCaller(FunctionCall alloc, Variable v) {
  v instanceof LocalVariable and
  v.(LocalVariable).getFunction() = alloc.getEnclosingFunction()
}

from FunctionCall alloc, Variable v
where
  isAllocCall(alloc, v) and
  isLocalToCaller(alloc, v) and
  allocReachesExitWithoutRelease(alloc, v)
select alloc,
  "Potential memory leak: kstrdup result assigned to '" + v.getName() +
    "' may not be released by kfree on all paths."
