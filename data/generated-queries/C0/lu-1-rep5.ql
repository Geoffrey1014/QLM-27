/**
 * @name Missing resource release on security check failure
 * @description Detects functions where an object (often an association, context, or
 *              control block) is allocated/created, then a security_* / validation
 *              hook is invoked, and on its failure path the function returns without
 *              releasing the previously allocated object. Mirrors the sctp
 *              dupcook leak fixed by releasing new_asoc via sctp_association_free()
 *              when security_sctp_assoc_request() fails.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-free-on-security-hook-failure
 * @tags correctness
 *       security
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/** A call that allocates / creates a resource that subsequently needs explicit release. */
class AllocCall extends FunctionCall {
  AllocCall() {
    exists(string n | n = this.getTarget().getName() |
      // SCTP / networking association-like allocators
      n.matches("%_new") or
      n.matches("%_create") or
      n.matches("%_alloc%") or
      n.matches("sctp_make_%") or
      n.matches("sctp_association_new") or
      n.matches("%_init_assoc%") or
      n = "kmalloc" or
      n = "kzalloc" or
      n = "kcalloc" or
      n = "kmem_cache_alloc" or
      n = "kmem_cache_zalloc"
    )
  }
}

/** A security/permission/validation hook that returns non-zero on failure. */
class SecurityCheckCall extends FunctionCall {
  SecurityCheckCall() {
    exists(string n | n = this.getTarget().getName() |
      n.matches("security\\_%") or
      n.matches("%_permission") or
      n.matches("%check_permission%") or
      n.matches("%assoc_request%") or
      n.matches("selinux\\_%") or
      n.matches("apparmor\\_%") or
      n.matches("smack\\_%")
    )
  }
}

/** A call that looks like a release for a resource (free / put / destroy / release). */
class ReleaseCall extends FunctionCall {
  ReleaseCall() {
    exists(string n | n = this.getTarget().getName() |
      n.matches("%_free") or
      n.matches("%_free_%") or
      n = "kfree" or
      n = "vfree" or
      n = "kvfree" or
      n.matches("%_put") or
      n.matches("%_destroy") or
      n.matches("%_release") or
      n.matches("%_dispose")
    )
  }
}

/** Holds if `e` could be the same resource as `v` (same variable directly or a field of it). */
predicate refersToVar(Expr e, Variable v) {
  e.(VariableAccess).getTarget() = v
  or
  e.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v
  or
  e.(PointerDereferenceExpr).getOperand().(VariableAccess).getTarget() = v
}

/**
 * Holds if `ret` is a ReturnStmt that is reachable from `sec` along a CFG path
 * representing the failure branch of `sec`, without an intervening release of `v`.
 */
predicate failureReturnNoRelease(SecurityCheckCall sec, Variable v, ReturnStmt ret) {
  ret.getEnclosingFunction() = sec.getEnclosingFunction() and
  // The security call's result is consumed by a controlling condition.
  exists(IfStmt ifs |
    ifs.getCondition().getAChild*() = sec and
    // The return is inside the "then" branch (failure branch when condition truthy).
    ret.getParentStmt*() = ifs.getThen()
  ) and
  // No release of v lexically between the security call's enclosing IfStmt and the return.
  not exists(ReleaseCall rel |
    rel.getEnclosingFunction() = sec.getEnclosingFunction() and
    refersToVar(rel.getAnArgument(), v) and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    rel.getLocation().getStartLine() >= sec.getLocation().getStartLine()
  )
}

from
  Function f, AllocCall alloc, Variable v, SecurityCheckCall sec, ReturnStmt ret
where
  f = alloc.getEnclosingFunction() and
  f = sec.getEnclosingFunction() and
  f = ret.getEnclosingFunction() and
  // The allocation result is assigned to (or initialises) v.
  (
    exists(AssignExpr ae |
      ae.getRValue() = alloc and ae.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(Initializer init |
      init.getExpr() = alloc and init.getDeclaration() = v
    )
  ) and
  // Security check occurs after allocation (lexically).
  sec.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  // Return on the failure branch with no release of v.
  failureReturnNoRelease(sec, v, ret) and
  // The function does release v somewhere else (success / cleanup path), proving
  // v is a resource whose contract requires release.
  exists(ReleaseCall rel |
    rel.getEnclosingFunction() = f and
    refersToVar(rel.getAnArgument(), v)
  )
select sec,
  "Security/permission hook '" + sec.getTarget().getName() +
    "' may fail and the function returns without releasing resource '" + v.getName() +
    "' allocated at $@.", alloc, alloc.getTarget().getName()
