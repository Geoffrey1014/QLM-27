/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() returns a struct platform_device with
 *              incremented reference count. Every path that obtains such a
 *              reference must release it with put_device(&pdev->dev), otherwise
 *              the device refcount leaks. This query detects calls to
 *              of_find_device_by_node (and sibling node-to-device lookup APIs)
 *              whose result is later not released on at least one reachable
 *              path that returns from the enclosing function.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-find-device-refcount-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions that acquire a device reference whose result must be released via
 * `put_device()`. The OF-tree family `of_find_device_by_node` is the direct
 * sibling of the patched call; `of_find_*_by_*` siblings have identical
 * semantics (they all call `bus_find_device` under the hood, which bumps the
 * refcount).
 */
predicate isDeviceAcquireApi(Function f) {
  f.getName() = "of_find_device_by_node" or
  f.getName() = "bus_find_device" or
  f.getName() = "bus_find_device_by_name" or
  f.getName() = "bus_find_device_by_of_node" or
  f.getName() = "driver_find_device" or
  f.getName() = "class_find_device" or
  f.getName() = "class_find_device_by_name" or
  f.getName() = "class_find_device_by_of_node"
}

/** A call that acquires a `struct device *` reference. */
class DeviceAcquireCall extends FunctionCall {
  DeviceAcquireCall() { isDeviceAcquireApi(this.getTarget()) }
}

/**
 * Holds if `e` is an expression that, syntactically, releases the reference
 * obtained for `v` via `put_device(&v->dev)` (or `put_device(v)` if `v` is
 * already a `device *`). We match loosely on the called function name so that
 * inline wrappers count.
 */
predicate releasesDevice(FunctionCall release, Variable v) {
  release.getTarget().getName() = "put_device" and
  exists(Expr arg | arg = release.getArgument(0) |
    // put_device(&var->dev) — address of a member access on `v`
    exists(AddressOfExpr ao, FieldAccess fa |
      ao = arg and
      fa = ao.getOperand() and
      fa.getQualifier().(VariableAccess).getTarget() = v
    )
    or
    // put_device(var) — direct
    arg.(VariableAccess).getTarget() = v
    or
    // put_device(&var.dev)
    exists(AddressOfExpr ao, FieldAccess fa |
      ao = arg and
      fa = ao.getOperand() and
      fa.getQualifier().(VariableAccess).getTarget() = v
    )
  )
}

/**
 * Holds if the function `f` ever calls `put_device` on variable `v`.
 * Used as a cheap proxy: if the variable is *never* released anywhere in the
 * function body, that is the strongest signal of a leak.
 */
predicate everReleasesInFunction(Function f, Variable v) {
  exists(FunctionCall release |
    release.getEnclosingFunction() = f and
    releasesDevice(release, v)
  )
}

/**
 * Holds if there is a control-flow path from `acquire` to a return statement
 * `ret` in the same function without passing through any `put_device` call on
 * `v`.
 */
predicate leaksOnPath(DeviceAcquireCall acquire, Variable v, ReturnStmt ret) {
  acquire.getEnclosingFunction() = ret.getEnclosingFunction() and
  exists(ControlFlowNode n |
    n = ret and
    acquire.getASuccessor+() = n
  ) and
  not exists(FunctionCall release |
    release.getEnclosingFunction() = acquire.getEnclosingFunction() and
    releasesDevice(release, v) and
    acquire.getASuccessor+() = release and
    release.getASuccessor+() = ret
  )
}

from DeviceAcquireCall acquire, Variable v, ReturnStmt ret, Function f
where
  f = acquire.getEnclosingFunction() and
  // The acquired reference is stored into `v`.
  exists(Expr lhsTarget |
    // v = of_find_device_by_node(...);
    exists(AssignExpr a |
      a.getRValue() = acquire and
      a.getLValue().(VariableAccess).getTarget() = v
    )
    or
    // struct platform_device *v = of_find_device_by_node(...);
    exists(Initializer init |
      init.getExpr() = acquire and
      init.getDeclaration() = v
    )
    or
    lhsTarget = acquire // fallback to make the disjunction non-empty
    and v.getAnAssignedValue() = acquire
  ) and
  leaksOnPath(acquire, v, ret) and
  // Drop functions that never call put_device on v at all OR that DO call it
  // on some path: we still report because at least one return path lacks it.
  // (Keeping both buggy-only and partially-buggy is intentional for recall.)
  not ret.getEnclosingFunction().getName().matches("%_release%") and
  not ret.getEnclosingFunction().getName().matches("%_remove%")
select acquire,
  "Reference acquired by $@ may leak: at least one return path in '" +
    f.getName() + "' is reachable without a matching put_device() on '" +
    v.getName() + "'.",
  acquire, acquire.getTarget().getName()
