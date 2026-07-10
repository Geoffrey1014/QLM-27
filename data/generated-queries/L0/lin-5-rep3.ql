/**
 * @name Missing put_device after of_find_device_by_node (refcount leak)
 * @description of_find_device_by_node() takes a reference on the returned
 *              platform_device. The caller must release it via
 *              put_device(&pdev->dev) on every exit path. Missing this call
 *              causes a device-refcount leak.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0/lin-5-rep3/refcount-leak-of-find-device-by-node
 * @tags reliability
 *       correctness
 *       cwe-772
 */

import cpp

predicate acquiresPlatformDevice(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_find_device_by_node" and
  (
    exists(AssignExpr ae |
      ae.getRValue() = fc and
      ae.getLValue() = v.getAnAccess()
    )
    or
    exists(Initializer init |
      init.getExpr() = fc and
      init.getDeclaration() = v
    )
  )
}

from FunctionCall acquire, Variable v, Function containing
where
  acquiresPlatformDevice(acquire, v) and
  containing = acquire.getEnclosingFunction() and
  not exists(FunctionCall release |
    release.getEnclosingFunction() = containing and
    release.getTarget().getName() = "put_device" and
    exists(AddressOfExpr ao, FieldAccess fa |
      ao = release.getArgument(0) and
      fa = ao.getOperand() and
      fa.getQualifier() = v.getAnAccess() and
      fa.getTarget().getName() = "dev"
    )
  )
select acquire,
  "of_find_device_by_node result stored in $@ is not released by put_device(&" +
    v.getName() + "->dev) on any path in " + containing.getName(),
  v, v.getName()
