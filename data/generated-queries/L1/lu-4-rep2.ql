/**
 * @name Missing platform_device_put on error path after platform_device_alloc
 * @description Detects functions that call platform_device_alloc but return
 *              on an error path without calling platform_device_put to release
 *              the acquired platform_device.
 *              Pattern derived from linux kernel commit 9bbfceea12a8
 *              "usb: dwc3: pci: prevent memory leak in dwc3_pci_probe".
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1/lu-4-rep2/platform-device-alloc-leak
 */

import cpp

predicate isPlatformDeviceAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

from FunctionCall alloc, ReturnStmt leakRet, Function fn
where
  isPlatformDeviceAllocCall(alloc) and
  fn = alloc.getEnclosingFunction() and
  leakRet.getEnclosingFunction() = fn and
  alloc.getASuccessor+() = leakRet and
  not exists(FunctionCall rel |
    rel.getTarget().getName() = "platform_device_put" and
    rel.getEnclosingFunction() = fn and
    alloc.getASuccessor+() = rel and
    rel.getASuccessor+() = leakRet
  )
select alloc,
  "platform_device_alloc here may leak: return at $@ is reachable without an intervening platform_device_put.",
  leakRet, "this return"
