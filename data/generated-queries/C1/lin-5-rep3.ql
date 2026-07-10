/**
 * @name Missing put_device on platform_device acquired via of_find_device_by_node
 * @description Detects calls to refcount-bumping device-lookup APIs (e.g.
 *              of_find_device_by_node, bus_find_device, driver_find_device,
 *              class_find_device) whose returned struct device* / struct
 *              platform_device* leaves the enclosing function on one or more
 *              return / break paths without a corresponding put_device() on
 *              the device member. Generic over the acquire API and the
 *              variable holding the returned device.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-5
 * @tags correctness
 *       resource-leak
 */

import cpp

/** Device-lookup APIs that take an additional reference on the returned device. */
predicate refAcquiringDeviceLookup(FunctionCall fc) {
  fc.getTarget().getName() in [
      "of_find_device_by_node",
      "bus_find_device",
      "bus_find_device_by_name",
      "bus_find_device_by_of_node",
      "bus_find_device_by_fwnode",
      "driver_find_device",
      "driver_find_device_by_name",
      "driver_find_device_by_of_node",
      "class_find_device",
      "class_find_device_by_name",
      "class_find_device_by_of_node",
      "device_find_child",
      "get_device"
    ]
}

/** Is `e` syntactically `&v.dev` or `&v->dev` where v has the same target as `vd`? */
predicate addrOfDevMember(Expr e, Variable vd) {
  exists(AddressOfExpr ao, FieldAccess fa |
    ao = e and
    fa = ao.getOperand() and
    fa.getTarget().getName() = "dev" and
    fa.getQualifier().(VariableAccess).getTarget() = vd
  )
}

/** A `put_device(...)` call whose argument refers to variable `vd`. */
predicate putsDevice(FunctionCall put, Variable vd) {
  put.getTarget().getName() = "put_device" and
  (
    // put_device(&vd->dev) or put_device(&vd.dev)
    addrOfDevMember(put.getArgument(0), vd)
    or
    // put_device(vd) when vd itself is a struct device*
    put.getArgument(0).(VariableAccess).getTarget() = vd
  )
}

from FunctionCall acq, Variable v, ReturnStmt ret, Function f
where
  refAcquiringDeviceLookup(acq) and
  f = acq.getEnclosingFunction() and
  // v captures the acquired device pointer
  (
    exists(AssignExpr a |
      a.getRValue() = acq and
      a.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(DeclStmt ds |
      ds.getADeclaration() = v and
      v.getInitializer().getExpr() = acq
    )
  ) and
  // a return statement reachable from acq
  ret.getEnclosingFunction() = f and
  acq.getASuccessor+() = ret and
  // no put_device on v between acq and ret
  not exists(FunctionCall put |
    put.getEnclosingFunction() = f and
    putsDevice(put, v) and
    acq.getASuccessor+() = put and
    put.getASuccessor*() = ret
  )
select acq,
  "Device reference acquired here may leak: $@ leaves function without put_device() before return.",
  v, v.getName()
