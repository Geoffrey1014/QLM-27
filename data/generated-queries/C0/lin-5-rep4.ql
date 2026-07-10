/**
 * @name Missing put_device after of_find_device_by_node on error path
 * @description of_find_device_by_node() takes a reference on the returned
 *              struct platform_device. Every error/early-return path between
 *              the call and the success cleanup must release the reference via
 *              put_device(&dev->dev). Missing put_device() on such a path is a
 *              refcount leak.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-put-device-of-find-device-by-node
 * @tags correctness
 *       reliability
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.controlflow.StackVariableReachability

/**
 * A call to a kernel helper that takes a reference on a `struct device`
 * (or `struct platform_device`) and returns it.  The returned pointer must
 * eventually be released with `put_device()` (possibly via the `&pdev->dev`
 * embedded device).
 */
class RefAcquiringCall extends FunctionCall {
  RefAcquiringCall() {
    this.getTarget().hasName([
        "of_find_device_by_node",
        "of_find_device_by_phandle",
        "bus_find_device",
        "bus_find_device_by_name",
        "bus_find_device_by_of_node",
        "driver_find_device",
        "class_find_device",
        "get_device"
      ])
  }
}

/**
 * A call that releases a `struct device` reference.  We accept either
 * `put_device(...)` directly or wrappers known to internally call it
 * (`platform_device_put`).
 */
class RefReleasingCall extends FunctionCall {
  RefReleasingCall() {
    this.getTarget().hasName(["put_device", "platform_device_put"])
  }
}

/**
 * Holds if `v` is the local variable that receives the result of the
 * reference-acquiring call `acq`.
 */
predicate acquiresInto(RefAcquiringCall acq, LocalVariable v) {
  exists(DeclStmt ds |
    ds.getADeclaration() = v and
    v.getInitializer().getExpr() = acq
  )
  or
  exists(AssignExpr a |
    a.getRValue() = acq and
    a.getLValue() = v.getAnAccess()
  )
}

/**
 * Holds if some expression in `s` (or its descendants) references `v` as an
 * argument to a release call (directly `put_device(&v->dev)` or
 * `platform_device_put(v)`).
 */
predicate releasesVar(Stmt s, LocalVariable v) {
  exists(RefReleasingCall rel, Expr arg |
    rel.getEnclosingStmt().getParentStmt*() = s and
    arg = rel.getAnArgument() and
    (
      // platform_device_put(v) — v passed directly
      arg = v.getAnAccess()
      or
      // put_device(&v->dev) — address of a device field of v
      exists(AddressOfExpr a, FieldAccess fa |
        a = arg and
        fa = a.getOperand() and
        fa.getQualifier().(PointerFieldAccess).getQualifier() = v.getAnAccess()
      )
      or
      exists(AddressOfExpr a, FieldAccess fa |
        a = arg and
        fa = a.getOperand() and
        fa.getQualifier() = v.getAnAccess()
      )
    )
  )
}

/**
 * Holds if `ret` is a `return` statement that the control-flow can reach from
 * just after `acq` without going through a release of `v`.
 */
predicate reachesReturnWithoutRelease(RefAcquiringCall acq, LocalVariable v, ReturnStmt ret) {
  acquiresInto(acq, v) and
  acq.getEnclosingFunction() = ret.getEnclosingFunction() and
  // The return must be control-flow reachable from the acquiring call
  acq.getASuccessor+() = ret and
  // No release of v on any path in the enclosing function before the return,
  // i.e. no release call between acq and ret in CFG order.
  not exists(RefReleasingCall rel |
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    acq.getASuccessor+() = rel and
    rel.getASuccessor*() = ret and
    (
      // platform_device_put(v)
      rel.getAnArgument() = v.getAnAccess()
      or
      // put_device(&v->dev)
      exists(AddressOfExpr a, FieldAccess fa |
        a = rel.getAnArgument() and
        fa = a.getOperand() and
        (
          fa.getQualifier() = v.getAnAccess()
          or
          fa.getQualifier().(PointerFieldAccess).getQualifier() = v.getAnAccess()
        )
      )
    )
  )
}

from RefAcquiringCall acq, LocalVariable v, ReturnStmt ret
where
  acquiresInto(acq, v) and
  reachesReturnWithoutRelease(acq, v, ret) and
  // Only flag returns of error codes (negative int constants) or any non-success
  // return.  We approximate: flag any return reachable from acq that does not
  // release v.  To prune obvious successful exits, require that this return is
  // textually after the acquire in the same function.
  ret.getLocation().getStartLine() > acq.getLocation().getStartLine()
select acq,
  "Reference acquired here by $@ may leak on the return at $@: variable '" + v.getName() +
    "' is not released with put_device() on this path.",
  acq, acq.getTarget().getName(), ret, ret.getLocation().toString()
