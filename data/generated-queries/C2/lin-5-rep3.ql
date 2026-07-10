/**
 * @name  rq3-c2-lin-5-rep3
 * @id    cpp/rq3/c2/lin-5-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing put_device after of_find_device_by_node.
 */
import cpp

/** Holds if `fc` is a call to of_find_device_by_node whose result is
 *  assigned to variable `v`. */
predicate isAcquireCall(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_find_device_by_node" and
  (
    exists(AssignExpr ae |
      ae.getRValue() = fc and
      ae.getLValue() = v.getAnAccess())
    or
    exists(Initializer init |
      init.getExpr() = fc and
      init.getDeclaration() = v)
  )
}

/** Holds if `fc` is a put_device call that releases the device referenced
 *  by `v` (i.e. argument is &v->dev or similar). */
predicate isReleaseCall(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "put_device" and
  exists(Expr arg | arg = fc.getArgument(0) |
    arg.(AddressOfExpr).getOperand().(FieldAccess).getQualifier().(VariableAccess).getTarget() = v
    or
    arg.(VariableAccess).getTarget() = v
  )
}

/** Holds if function `f` contains an acquire call binding variable `v`. */
predicate functionHasAcquire(Function f, Variable v, FunctionCall acq) {
  isAcquireCall(acq, v) and
  acq.getEnclosingFunction() = f
}

/** Holds if `rs` is a return statement reachable from the acquire-call
 *  basic block without an intervening release of `v`. */
predicate returnLeaksDevice(Function f, Variable v, FunctionCall acq, ReturnStmt rs) {
  functionHasAcquire(f, v, acq) and
  rs.getEnclosingFunction() = f and
  acq.getBasicBlock().getASuccessor+() = rs.getBasicBlock() and
  not exists(FunctionCall rel |
    isReleaseCall(rel, v) and
    rel.getEnclosingFunction() = f and
    acq.getBasicBlock().getASuccessor*() = rel.getBasicBlock() and
    rel.getBasicBlock().getASuccessor*() = rs.getBasicBlock()
  )
}

from Function f, Variable v, FunctionCall acq, ReturnStmt rs
where returnLeaksDevice(f, v, acq, rs)
select rs, "Possible refcount leak: device acquired by of_find_device_by_node into $@ is not released by put_device before this return.",
  v, v.getName()
