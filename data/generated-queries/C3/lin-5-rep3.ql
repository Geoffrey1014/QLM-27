/**
 * @name Refcount leak after of_find_device_by_node
 * @description of_find_device_by_node() takes a reference on the returned
 *              platform_device; callers must release it via put_device on
 *              every exit path. This query reports enclosing functions
 *              where no put_device call references the acquired variable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c3-lin-5-rep3
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

predicate isRelease(FunctionCall fc, Expr dev) {
  fc.getTarget().getName() = "put_device" and
  dev = fc.getArgument(0)
}

Variable getAcquiredVar(FunctionCall acq) {
  isAcquire(acq) and
  (
    acq.getParent().(AssignExpr).getLValue() = result.getAnAccess()
    or
    result.getInitializer().getExpr() = acq
  )
}

predicate leaksAcquired(FunctionCall acq, Variable v, Function f) {
  isAcquire(acq) and
  v = getAcquiredVar(acq) and
  f = acq.getEnclosingFunction() and
  not exists(FunctionCall rel, Expr dev, VariableAccess va |
    isRelease(rel, dev) and
    rel.getEnclosingFunction() = f and
    va = dev.getAChild*() and
    va.getTarget() = v
  )
}

from FunctionCall acq, Variable v, Function f
where leaksAcquired(acq, v, f)
select acq,
  "Refcount leak: " + v.getName() + " acquired via " +
    acq.getTarget().getName() + "() never released in " + f.getName()
