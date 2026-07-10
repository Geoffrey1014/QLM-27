/**
 * @name Memory leak: return between platform_device_alloc and platform_device_put cleanup
 * @description Detects a `return` statement that occurs after a
 *              `platform_device_alloc()` in the same function but before the
 *              `platform_device_put()` cleanup label, without any earlier
 *              `platform_device_put()` on that return path. Pattern derived
 *              from Linux commit 9bbfceea12a8 (usb: dwc3: pci: prevent memory
 *              leak in dwc3_pci_probe).
 * @kind problem
 * @problem.severity warning
 * @id qlm/lu-4-rep4-platform-device-leak
 */

import cpp

predicate allocatesPlatformDevice(FunctionCall allocCall, Function enclosing) {
  allocCall.getTarget().getName() = "platform_device_alloc" and
  enclosing = allocCall.getEnclosingFunction()
}

predicate hasPlatformDevicePut(Function f, FunctionCall putCall) {
  putCall.getTarget().getName() = "platform_device_put" and
  putCall.getEnclosingFunction() = f
}

from FunctionCall allocCall, Function f, ReturnStmt retStmt, FunctionCall putCall
where
  allocatesPlatformDevice(allocCall, f) and
  hasPlatformDevicePut(f, putCall) and
  retStmt.getEnclosingFunction() = f and
  retStmt.getLocation().getStartLine() > allocCall.getLocation().getEndLine() and
  putCall.getLocation().getStartLine() > retStmt.getLocation().getStartLine() and
  not exists(FunctionCall earlierPut |
    earlierPut.getTarget().getName() = "platform_device_put" and
    earlierPut.getEnclosingFunction() = f and
    earlierPut.getLocation().getStartLine() >= allocCall.getLocation().getStartLine() and
    earlierPut.getLocation().getStartLine() <= retStmt.getLocation().getStartLine()
  )
select retStmt,
  "Possible memory leak: return between platform_device_alloc and platform_device_put cleanup label bypasses the cleanup."
