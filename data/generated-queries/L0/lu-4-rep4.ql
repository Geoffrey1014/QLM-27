/**
 * @name Missing platform_device_put after platform_device_alloc on error path
 * @description Detects functions that call platform_device_alloc and have at
 *              least one return path following the acquire that does not
 *              release the device via platform_device_put beforehand.
 *              Pattern derived from Linux commit 9bbfceea12a8
 *              ("usb: dwc3: pci: prevent memory leak in dwc3_pci_probe").
 * @kind problem
 * @problem.severity warning
 * @id qlm-l0-lu-4-rep4
 * @tags correctness
 *       memory-leak
 */
import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

from FunctionCall acquire, Function enclosing, ReturnStmt r
where
  isAcquireCall(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  r.getEnclosingFunction() = enclosing and
  r.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    rel.getTarget().getName() = "platform_device_put" and
    rel.getEnclosingFunction() = enclosing and
    rel.getLocation().getStartLine() < r.getLocation().getStartLine() and
    rel.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  )
select acquire,
  "platform_device_alloc without matching platform_device_put on some return path in "
    + enclosing.getName()
