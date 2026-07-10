/**
 * @name Missing resource release on error path after platform_device_alloc
 * @description After platform_device_alloc succeeds, a subsequent failing call must
 *              go through the common error-cleanup path that calls platform_device_put
 *              (or similar release). Returning directly without releasing leaks the
 *              allocated platform_device. Generalized to common acquire/release
 *              pairs in kernel resource APIs.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-release-on-error-after-acquire
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A function that acquires a resource and returns a pointer that needs an explicit release. */
class AcquireCall extends FunctionCall {
  AcquireCall() {
    this.getTarget().getName() =
      [
        "platform_device_alloc", "platform_device_register_simple",
        "of_find_device_by_node", "of_find_node_by_name", "of_find_node_by_path",
        "of_parse_phandle", "of_get_child_by_name", "of_get_parent",
        "of_get_next_child", "of_get_next_available_child",
        "usb_get_dev", "usb_get_intf", "pci_get_device", "pci_get_class",
        "get_device", "class_find_device", "driver_find_device",
        "kobject_get", "device_link_add", "fwnode_handle_get",
        "spi_alloc_master", "i2c_get_adapter", "iio_device_alloc",
        "input_allocate_device", "rtc_allocate_device",
        "alloc_netdev_mqs", "alloc_etherdev_mqs",
        "blk_alloc_queue", "blk_mq_alloc_request",
        "clk_get", "regulator_get", "gpio_request", "pinctrl_get",
        "request_firmware", "kmalloc", "kzalloc", "kcalloc"
      ]
  }
}

/** A function that releases a resource (matched loosely by name family). */
predicate isReleaseName(string name) {
  name =
    [
      "platform_device_put", "platform_device_unregister",
      "of_node_put", "of_dev_put",
      "usb_put_dev", "usb_put_intf", "pci_dev_put",
      "put_device", "kobject_put", "device_link_del", "fwnode_handle_put",
      "spi_master_put", "i2c_put_adapter", "iio_device_free",
      "input_free_device", "rtc_free_device",
      "free_netdev", "blk_cleanup_queue", "blk_mq_free_request",
      "clk_put", "regulator_put", "gpio_free", "pinctrl_put",
      "release_firmware", "kfree"
    ]
}

class ReleaseCall extends FunctionCall {
  ReleaseCall() { isReleaseName(this.getTarget().getName()) }
}

/**
 * A call C that returns an error (assigned to a variable then checked < 0 or != 0,
 * with a return inside the if-body) — i.e., a check-and-return pattern on error.
 */
class CheckedFailingCall extends FunctionCall {
  IfStmt ifStmt;
  ReturnStmt ret;

  CheckedFailingCall() {
    exists(Variable v, Expr cond |
      // ret = some_call(...);
      exists(AssignExpr a |
        a.getLValue() = v.getAnAccess() and
        a.getRValue() = this
      ) and
      // if (ret < 0) { return ret; } or similar
      cond = ifStmt.getCondition() and
      cond.getAChild*() = v.getAnAccess() and
      ret.getEnclosingStmt().getParentStmt*() = ifStmt.getThen() and
      // the return value comes from v (or just bare return)
      (ret.getExpr().(VariableAccess).getTarget() = v or not exists(ret.getExpr()))
    )
  }

  ReturnStmt getReturn() { result = ret }
  IfStmt getIfStmt() { result = ifStmt }
}

/**
 * A "common error label" predicate: in the same function, there exists at least one
 * other error site that uses `goto err...` or otherwise reaches a release call,
 * which the offending site fails to use.
 */
predicate hasErrorReleaseElsewhere(Function f, AcquireCall acq) {
  exists(ReleaseCall rel |
    rel.getEnclosingFunction() = f and
    // release operates on something derived from the acquire (heuristic: same
    // function and any release of a matching family).
    acq.getEnclosingFunction() = f
  )
}

from AcquireCall acq, CheckedFailingCall bad, Function f
where
  f = acq.getEnclosingFunction() and
  f = bad.getEnclosingFunction() and
  // The failing-and-returning call happens AFTER the acquire (in source order
  // as a proxy for control-flow order).
  acq.getLocation().getStartLine() < bad.getLocation().getStartLine() and
  // The bad call is not itself a release call.
  not bad instanceof ReleaseCall and
  // The bad call is not the acquire itself.
  not bad = acq and
  // There exists release logic in the function (i.e. an error-cleanup path),
  // which the offending site bypasses.
  hasErrorReleaseElsewhere(f, acq) and
  // The return inside the if-body does NOT have a release call dominating it
  // in the same block.
  not exists(ReleaseCall rel |
    rel.getEnclosingFunction() = f and
    rel.getLocation().getStartLine() < bad.getReturn().getLocation().getStartLine() and
    rel.getLocation().getStartLine() > bad.getLocation().getStartLine() and
    rel.getEnclosingStmt().getParentStmt*() = bad.getIfStmt().getThen()
  )
select bad,
  "Possible resource leak: after '" + acq.getTarget().getName() +
    "' in function '" + f.getName() +
    "', this failing call returns directly without invoking the function's release path."
