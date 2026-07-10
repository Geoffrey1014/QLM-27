/**
 * @name Missing resource cleanup on early return after platform_device_alloc
 * @description Detects functions that allocate a platform_device via
 *              platform_device_alloc (or similar resource-acquiring API) and
 *              then on a subsequent error path return directly without
 *              executing the goto-based cleanup chain (e.g. platform_device_put),
 *              causing a memory/reference leak.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-cleanup-after-platform-device-alloc
 * @tags correctness
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Resource-acquiring APIs whose returned pointer requires an explicit
 * release call (platform_device_put / put_device / kfree) on error paths.
 */
predicate isResourceAcquireCall(FunctionCall fc, Variable v) {
  exists(string name | name = fc.getTarget().getName() |
    name = "platform_device_alloc" or
    name = "platform_device_register_full" or
    name = "platform_device_register_simple"
  ) and
  (
    // v = func(...)
    exists(AssignExpr a |
      a.getRValue() = fc and
      a.getLValue() = v.getAnAccess())
    or
    // T *v = func(...)
    v.getInitializer().getExpr() = fc
    or
    // struct.field = func(...) — track the field via enclosing variable
    exists(AssignExpr a, FieldAccess fa |
      a.getRValue() = fc and
      a.getLValue() = fa and
      fa.getQualifier() = v.getAnAccess())
  )
}

/**
 * A call that releases the resource (platform_device_put etc.).
 */
predicate isResourceReleaseCall(FunctionCall fc) {
  exists(string name | name = fc.getTarget().getName() |
    name = "platform_device_put" or
    name = "platform_device_unregister" or
    name = "put_device" or
    name = "kfree"
  )
}

/**
 * An ErrorReturn: a `return <expr>;` statement that returns a value
 * (typically a negative errno) and is guarded by an `if (ret < 0)` /
 * `if (ret)` style check on a value produced by a call that follows
 * the resource acquisition.
 */
class EarlyErrorReturn extends ReturnStmt {
  EarlyErrorReturn() {
    exists(IfStmt ifs |
      ifs.getThen() = this or
      ifs.getThen().(BlockStmt).getStmt(0) = this
    )
  }
}

/**
 * Holds if the function `f` has, on the control-flow path between the
 * acquire call `acquire` and the early-error-return `ret`, NO call to
 * any resource-release function for the acquired variable.
 */
predicate noReleaseBetween(Function f, FunctionCall acquire, EarlyErrorReturn ret) {
  acquire.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  not exists(FunctionCall rel |
    isResourceReleaseCall(rel) and
    rel.getEnclosingFunction() = f and
    // release lies textually between acquire and the return
    rel.getLocation().getStartLine() > acquire.getLocation().getEndLine() and
    rel.getLocation().getEndLine() < ret.getLocation().getStartLine()
  )
}

/**
 * Holds if there is at least one `goto` label-style cleanup in this
 * function, meaning the canonical pattern is goto-based and a plain
 * `return` therefore skips cleanup.
 */
predicate hasCleanupGoto(Function f) {
  exists(GotoStmt g | g.getEnclosingFunction() = f)
}

from Function f, FunctionCall acquire, Variable v, EarlyErrorReturn ret
where
  isResourceAcquireCall(acquire, v) and
  acquire.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  // the return is textually after the acquire
  ret.getLocation().getStartLine() > acquire.getLocation().getEndLine() and
  hasCleanupGoto(f) and
  noReleaseBetween(f, acquire, ret) and
  // exclude returns of 0 (success) — only care about error returns
  not ret.getExpr().getValue() = "0" and
  // exclude the special case where the function actually returns the
  // acquired variable (ownership transfer)
  not ret.getExpr() = v.getAnAccess()
select ret,
  "Possible resource leak: function $@ allocates a resource via $@ but this early return bypasses the goto-based cleanup chain, leaving the resource leaked.",
  f, f.getName(), acquire, acquire.getTarget().getName()
