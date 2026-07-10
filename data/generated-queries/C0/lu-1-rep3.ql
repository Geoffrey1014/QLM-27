/**
 * @name Missing release of allocated object on security-hook error path
 * @description An object obtained from an allocation/constructor helper (e.g.
 *              sctp_association_new, sctp_make_*, kmalloc family, etc.) is
 *              referenced by a local pointer. If a subsequent guard call
 *              (such as security_*_request or another validation hook) returns
 *              non-zero, control commonly leaves the function through an early
 *              return. On those error paths the allocated object must be
 *              released with its matching free helper (e.g. sctp_association_free,
 *              kfree). Missing the free on that path is a memory leak —
 *              the bug pattern fixed by commit b6631c6031c7 ("sctp: Fix memory
 *              leak in sctp_sf_do_5_2_4_dupcook").
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-free-on-security-error-path
 * @tags reliability
 *       security
 *       resource-leak
 *       kernel
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A call that allocates / constructs an owned object that must be freed. */
predicate allocFuncName(string n) {
  // SCTP family (closest siblings of the patched call site)
  n = "sctp_association_new" or
  n = "sctp_make_init" or
  n = "sctp_make_init_ack" or
  n = "sctp_make_cookie_echo" or
  n = "sctp_make_cookie_ack" or
  n = "sctp_make_chunk" or
  n = "sctp_chunkify" or
  n = "sctp_make_datafrag_empty" or
  // generic kernel allocators that return an owned pointer
  n = "kmalloc" or
  n = "kzalloc" or
  n = "kcalloc" or
  n = "kmalloc_array" or
  n = "vmalloc" or
  n = "vzalloc" or
  n = "kmemdup"
}

/** A call that releases an owned object. */
predicate freeFuncName(string n) {
  n = "sctp_association_free" or
  n = "sctp_association_put" or
  n = "sctp_chunk_free" or
  n = "kfree" or
  n = "kzfree" or
  n = "kvfree" or
  n = "vfree"
}

class AllocCall extends FunctionCall {
  AllocCall() { allocFuncName(this.getTarget().getName()) }
}

/** A "guard" call whose non-zero return triggers an error-path early return. */
class GuardCall extends FunctionCall {
  GuardCall() {
    this.getTarget().getName().matches("security\\_%")
    or
    this.getTarget().getName() = "security_sctp_assoc_request"
    or
    this.getTarget().getName() = "security_sctp_bind_connect"
    or
    this.getTarget().getName() = "security_sk_classify_flow"
  }
}

class FreeCall extends FunctionCall {
  FreeCall() { freeFuncName(this.getTarget().getName()) }
}

/** A local pointer variable that is initialised or assigned from an allocation. */
class AllocedVar extends LocalVariable {
  AllocCall alloc;

  AllocedVar() {
    (
      this.getInitializer().getExpr() = alloc
      or
      exists(AssignExpr a |
        a.getLValue().(VariableAccess).getTarget() = this and
        a.getRValue() = alloc
      )
    ) and
    this.getType().getUnspecifiedType() instanceof PointerType
  }

  AllocCall getAlloc() { result = alloc }
}

/** Holds if `fc` frees variable `v` (passes `v` directly as argument 0). */
predicate freesVar(FreeCall fc, LocalVariable v) {
  fc.getArgument(0).(VariableAccess).getTarget() = v
}

/**
 * Holds if `ret` is a return statement reachable from `guard` such that no
 * free of `v` occurs on a path from `guard` to `ret`. The return must be
 * control-dependent on the guard's outcome (i.e. inside its `if`-branch).
 */
predicate missingFreeAfterGuard(GuardCall guard, AllocedVar v, ReturnStmt ret) {
  // guard and ret share enclosing function with the allocation
  v.getAlloc().getEnclosingFunction() = guard.getEnclosingFunction() and
  guard.getEnclosingFunction() = ret.getEnclosingFunction() and
  // ret reachable from guard
  guard.getASuccessor+() = ret and
  // the guard's result actually drives the path (guard appears in the
  // condition of an IfStmt whose body contains ret)
  exists(IfStmt ifs |
    ifs.getCondition().getAChild*() = guard and
    ifs.getThen().getAChild*() = ret
  ) and
  // no free of v between guard and the return
  not exists(FreeCall fc |
    freesVar(fc, v) and
    guard.getASuccessor+() = fc and
    fc.getASuccessor*() = ret
  ) and
  // sanity: v was allocated before the guard
  v.getAlloc().getASuccessor+() = guard
}

from AllocCall alloc, AllocedVar v, GuardCall guard, ReturnStmt ret, Function f
where
  alloc = v.getAlloc() and
  f = alloc.getEnclosingFunction() and
  missingFreeAfterGuard(guard, v, ret) and
  // Filter: there must exist *somewhere* in the same function a free of v,
  // otherwise it's likely a caller-owned pointer (returned to caller).
  exists(FreeCall fc | freesVar(fc, v) and fc.getEnclosingFunction() = f)
select guard,
  "Object allocated by $@ into '" + v.getName() +
    "' is not freed on the error path returning via $@ in " + f.getName() + "().",
  alloc, alloc.getTarget().getName(),
  ret, "this return"
