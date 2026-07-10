/**
 * @name Missing platform_device cleanup on error path after platform_device_alloc
 * @description After a successful call to platform_device_alloc (or similar
 *              resource-allocating sibling), subsequent failures that occur
 *              before the device is registered or transferred to a consumer
 *              must release the allocated device via platform_device_put (or
 *              an equivalent cleanup). A direct return from such an error
 *              branch leaks the allocation.
 * @kind problem
 * @id cpp/missing-platform-device-put-on-error
 * @problem.severity warning
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions that allocate a resource which must be explicitly released
 * on the error path of its caller. The matched pattern is
 *   var = ALLOC(...);
 *   ...
 *   ret = SOMETHING(..., var, ...);
 *   if (ret < 0 / ret) return ret;   // leak: var not released
 */
class AllocCall extends FunctionCall {
  AllocCall() {
    this.getTarget().getName() = "platform_device_alloc"
  }
}

/**
 * Functions whose presence on an error path indicates the resource was
 * properly released or ownership was transferred. We treat
 * platform_device_put / platform_device_unregister / platform_device_del
 * as releasing, and platform_device_add as ownership transfer (after which
 * platform_device_put is still the correct cleanup, but the developer
 * usually adds an unregister path; we keep it conservative and treat add
 * as transfer-of-ownership too).
 */
predicate isReleaseCall(FunctionCall fc, Expr resource) {
  (
    fc.getTarget().getName() = "platform_device_put" or
    fc.getTarget().getName() = "platform_device_unregister" or
    fc.getTarget().getName() = "platform_device_del" or
    fc.getTarget().getName() = "platform_device_add" or
    fc.getTarget().getName() = "put_device"
  ) and
  fc.getAnArgument() = resource
}

/**
 * Holds if `e` syntactically refers to the same local variable as `v`.
 */
predicate refsLocal(Expr e, LocalScopeVariable v) {
  e.(VariableAccess).getTarget() = v
}

/**
 * Holds if function `f` allocates into local variable `v` via an AllocCall.
 */
predicate allocatesInto(Function f, LocalScopeVariable v, AllocCall ac) {
  ac.getEnclosingFunction() = f and
  (
    // v = platform_device_alloc(...)
    exists(AssignExpr ae |
      ae.getRValue() = ac and
      refsLocal(ae.getLValue(), v)
    )
    or
    // struct field assignment such as dwc->dwc3 = platform_device_alloc(...)
    exists(AssignExpr ae, FieldAccess fa |
      ae.getRValue() = ac and
      ae.getLValue() = fa and
      refsLocal(fa.getQualifier(), v)
    )
    or
    // declaration with initializer: struct platform_device *p = platform_device_alloc(...)
    exists(Variable vv |
      vv = v and
      vv.getInitializer().getExpr() = ac
    )
  )
}

/**
 * A return statement `rs` inside function `f` that returns an error
 * (negative or non-zero ret) without first releasing `v`.
 *
 * We look for: a call C that takes `v` (or a field reached through `v`)
 * as argument; an if-statement testing the result of C with the form
 *   if (ret < 0) return ret;  or  if (ret) return ret;
 * and we require that NO release call on `v` dominates `rs` between
 * the alloc and the return.
 */
predicate leakingReturn(
  Function f, LocalScopeVariable v, AllocCall ac, ReturnStmt rs, FunctionCall trigger
) {
  allocatesInto(f, v, ac) and
  rs.getEnclosingFunction() = f and
  trigger.getEnclosingFunction() = f and
  // trigger is a call that uses the allocated resource as an argument
  // (directly or via a field of the surrounding container)
  (
    refsLocal(trigger.getAnArgument(), v)
    or
    exists(FieldAccess fa |
      fa = trigger.getAnArgument() and
      refsLocal(fa.getQualifier(), v)
    )
  ) and
  // there is no release of v anywhere between the alloc and the return
  not exists(FunctionCall rel, Expr resArg |
    rel.getEnclosingFunction() = f and
    isReleaseCall(rel, resArg) and
    (
      refsLocal(resArg, v)
      or
      exists(FieldAccess fa |
        fa = resArg and refsLocal(fa.getQualifier(), v)
      )
    ) and
    // release is reachable on the path to the return
    rel.getASuccessor*() = rs
  ) and
  // the return is reached from the trigger (error path)
  trigger.getASuccessor*() = rs and
  // the alloc dominates the trigger
  ac.getASuccessor*() = trigger and
  // exclude the case where the return value itself is the alloc (transfer)
  not rs.getExpr() = ac
}

from Function f, LocalScopeVariable v, AllocCall ac, ReturnStmt rs, FunctionCall trigger
where
  leakingReturn(f, v, ac, rs, trigger) and
  // The trigger should not itself be a release/transfer of v
  not isReleaseCall(trigger, _) and
  // Reduce noise: only report when trigger's return is what is being returned,
  // i.e. typical "ret = foo(...); if (ret) return ret;" idiom
  rs.getExpr().(VariableAccess).getTarget().getType().getName().regexpMatch("int|long|.*_t")
select rs,
  "Possible leak of resource allocated by '" + ac.getTarget().getName() +
    "' at $@: error return on call to '" + trigger.getTarget().getName() +
    "' does not release the allocated device.",
  ac, ac.getTarget().getName()
