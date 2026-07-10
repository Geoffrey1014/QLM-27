/**
 * @name Missing free on security hook error path leaks allocated resource
 * @description A resource (e.g. SCTP association, struct, buffer) is allocated
 *              by an allocator-style call and assigned to a local variable.
 *              A subsequent security/permission/validation check returns
 *              non-zero (failure), and control flow returns from the function
 *              without calling the corresponding release routine on that
 *              variable. This is the bug class fixed by commit b6631c6031c7
 *              ("sctp: Fix memory leak in sctp_sf_do_5_2_4_dupcook").
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-free-on-security-hook-error-path
 * @tags security
 *       correctness
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Allocator-style calls whose return value (or out-parameter) owns memory
 * that the caller must release. We focus on the common kernel families
 * that pair with an explicit free routine.
 */
predicate isAllocatorCall(FunctionCall fc, string family) {
  exists(string n | n = fc.getTarget().getName() |
    // SCTP association / endpoint / chunk lifetime (the patch's family)
    (n = "sctp_association_new" and family = "sctp_assoc") or
    (n = "sctp_make_temp_asoc" and family = "sctp_assoc") or
    (n = "sctp_endpoint_new" and family = "sctp_endpoint") or
    (n = "sctp_chunkify" and family = "sctp_chunk") or
    (n = "sctp_make_chunk" and family = "sctp_chunk") or
    // Generic kernel allocators
    (n = "kmalloc" and family = "kfree") or
    (n = "kzalloc" and family = "kfree") or
    (n = "kcalloc" and family = "kfree") or
    (n = "kmemdup" and family = "kfree") or
    (n = "kstrdup" and family = "kfree") or
    (n = "vmalloc" and family = "vfree") or
    (n = "vzalloc" and family = "vfree") or
    // Skb / socket-buffer family
    (n = "alloc_skb" and family = "kfree_skb") or
    (n = "skb_clone" and family = "kfree_skb") or
    (n = "skb_copy" and family = "kfree_skb") or
    // Netlink / netdev
    (n = "alloc_netdev" and family = "free_netdev") or
    (n = "alloc_etherdev" and family = "free_netdev")
  )
}

/** A release routine that pairs with the allocator family. */
predicate isReleaseCall(FunctionCall fc, string family) {
  exists(string n | n = fc.getTarget().getName() |
    (n = "sctp_association_free" and family = "sctp_assoc") or
    (n = "sctp_association_put" and family = "sctp_assoc") or
    (n = "sctp_endpoint_free" and family = "sctp_endpoint") or
    (n = "sctp_endpoint_put" and family = "sctp_endpoint") or
    (n = "sctp_chunk_free" and family = "sctp_chunk") or
    (n = "kfree" and family = "kfree") or
    (n = "kvfree" and family = "kfree") or
    (n = "vfree" and family = "vfree") or
    (n = "kfree_skb" and family = "kfree_skb") or
    (n = "consume_skb" and family = "kfree_skb") or
    (n = "free_netdev" and family = "free_netdev")
  )
}

/**
 * A "security/validation hook" call whose non-zero return triggers an error
 * path. We focus on the security_* family that the patched commit involves,
 * plus a couple of close siblings frequently misused the same way.
 */
predicate isSecurityHookCall(FunctionCall fc) {
  fc.getTarget().getName().matches("security\\_%")
}

/**
 * Holds if `v` is assigned the result of an allocator call `alloc` of
 * the given family.
 */
predicate allocatedInto(LocalVariable v, FunctionCall alloc, string family) {
  isAllocatorCall(alloc, family) and
  (
    v.getInitializer().getExpr() = alloc
    or
    exists(AssignExpr a |
      a.getRValue() = alloc and
      a.getLValue().(VariableAccess).getTarget() = v
    )
  )
}

/**
 * Holds if `ret` is a ReturnStmt reachable inside the "then" branch of an
 * if-stmt whose condition is (or contains) a call to a security hook.
 */
predicate inSecurityHookErrorReturn(ReturnStmt ret, FunctionCall hook) {
  isSecurityHookCall(hook) and
  exists(IfStmt ifs |
    ifs.getCondition().getAChild*() = hook and
    ret.getParent*() = ifs.getThen()
  )
}

/**
 * Holds if there is some call to a release function of `family` whose
 * argument is a reference to `v`, located in the same function as `ret`.
 * (Used as a "is the release at least sometimes performed" filter so we
 * don't flag totally unrelated cases.)
 */
predicate releaseSomewhere(LocalVariable v, string family, Function f) {
  exists(FunctionCall rel |
    isReleaseCall(rel, family) and
    rel.getEnclosingFunction() = f and
    rel.getAnArgument().(VariableAccess).getTarget() = v
  )
}

/**
 * Holds if there is a release of `v` on the path from the start of the
 * `then`-branch to `ret` (i.e. the error path *does* free). We use a simple
 * syntactic check: a release call whose argument is `v` is the parent or
 * a previous statement of `ret` inside the same block.
 */
predicate errorPathFrees(ReturnStmt ret, LocalVariable v, string family) {
  exists(FunctionCall rel, Stmt enclosing |
    isReleaseCall(rel, family) and
    rel.getAnArgument().(VariableAccess).getTarget() = v and
    enclosing = ret.getParent() and
    rel.getEnclosingStmt().getParent*() = enclosing
  )
}

from
  Function f, LocalVariable v, FunctionCall alloc, string family,
  FunctionCall hook, ReturnStmt ret
where
  allocatedInto(v, alloc, family) and
  alloc.getEnclosingFunction() = f and
  v.getFunction() = f and
  inSecurityHookErrorReturn(ret, hook) and
  ret.getEnclosingFunction() = f and
  // Allocation dominates the hook syntactically (allocation appears before
  // the if-stmt in source order in the same function).
  alloc.getLocation().getStartLine() < hook.getLocation().getStartLine() and
  // The function does know how to release this family for v (otherwise we'd
  // flag e.g. helpers that hand ownership off to a caller).
  releaseSomewhere(v, family, f) and
  // The error-path return does NOT itself free v.
  not errorPathFrees(ret, v, family)
select ret,
  "Possible leak of $@ (allocated by " + alloc.getTarget().getName() +
    ") on error path of security hook $@: missing call to a " + family + " release routine.",
  v, v.getName(), hook, hook.getTarget().getName()
