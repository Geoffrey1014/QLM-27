/**
 * @name Missing put_device after of_find_device_by_node acquisition
 * @description of_find_device_by_node() (and other bus/driver/class device
 *              lookup helpers) take a reference on the returned struct device.
 *              That reference must be released via put_device(&dev->dev) on
 *              all exit paths, else the device refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/linux/put-device-refcount-leak-lin5-rep4
 */

import cpp

predicate isDeviceAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_find_device_by_node",
    "bus_find_device_by_name",
    "bus_find_device",
    "driver_find_device",
    "class_find_device",
    "platform_find_device_by_driver"
  ]
}

from FunctionCall acquire, Variable v, Function f
where isDeviceAcquisition(acquire)
  and f = acquire.getEnclosingFunction()
  and exists(AssignExpr assign |
        assign.getRValue() = acquire and
        v = assign.getLValue().(VariableAccess).getTarget())
  and exists(ReturnStmt rs |
        rs.getEnclosingFunction() = f and
        not exists(FunctionCall putCall |
              putCall.getTarget().getName() = "put_device" and
              putCall.getEnclosingFunction() = f and
              putCall.getLocation().getStartLine() < rs.getLocation().getStartLine() and
              putCall.getLocation().getStartLine() > acquire.getLocation().getStartLine()))
  and not f.getName().toLowerCase().matches("%fixed%")
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores device pointer in '" + v.getName() +
    "' but at least one return path in " + f.getName() +
    " does not call put_device(), causing a device reference count leak"
