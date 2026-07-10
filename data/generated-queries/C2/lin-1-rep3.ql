/**
 * @name  rq3-c2-lin-1-rep3
 * @id    cpp/rq3/c2/lin-1-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing of_node_put() on device_node references
 *              obtained via of_parse_phandle() before control leaves the
 *              acquiring loop iteration via continue/break/return.
 */
import cpp

/** A call that acquires a device_node reference via of_parse_phandle. */
predicate acquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

/** A call that releases a device_node reference (post-operation). */
predicate releaseCall(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "of_node_put" and
  arg = fc.getArgument(0)
}

/**
 * `v` is the critical variable that holds the resource acquired by `acq`.
 * Matches the common pattern: `v = of_parse_phandle(...)`.
 */
predicate criticalVariable(Variable v, FunctionCall acq) {
  acquireCall(acq) and
  exists(AssignExpr ae |
    ae.getRValue() = acq and
    ae.getLValue() = v.getAnAccess()
  )
}

/**
 * A statement that exits the current loop iteration without continuing through
 * the natural fall-through (i.e. `continue`, `break`, `return`, or `goto`).
 */
predicate earlyExitStmt(Stmt s) {
  s instanceof ContinueStmt or
  s instanceof BreakStmt or
  s instanceof ReturnStmt or
  s instanceof GotoStmt
}

/**
 * `exit` is an early-exit statement reachable from the acquiring call `acq`
 * (storing into `v`) along the CFG, and no `of_node_put(v)` is invoked between
 * `acq` and `exit`.
 */
predicate missingReleaseBeforeExit(FunctionCall acq, Variable v, Stmt exit) {
  criticalVariable(v, acq) and
  earlyExitStmt(exit) and
  exit.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getASuccessor+() = exit and
  not exists(FunctionCall rel, Expr arg |
    releaseCall(rel, arg) and
    arg = v.getAnAccess() and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = exit
  )
}

from FunctionCall acq, Variable v, Stmt exit
where missingReleaseBeforeExit(acq, v, exit)
select acq,
  "Missing of_node_put() on $@ before early exit at $@.",
  v, v.getName(), exit, "this statement"
