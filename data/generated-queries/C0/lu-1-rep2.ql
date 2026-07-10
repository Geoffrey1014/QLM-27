/**
 * @name Missing resource release on error path after allocation
 * @description Detects functions that allocate a resource (e.g. via *_new(),
 *              *_alloc(), *_create()) and then perform a fallible operation
 *              (e.g. security_*, validation) whose failure branch returns early
 *              without releasing the previously-allocated resource. Modeled on
 *              the sctp_sf_do_5_2_4_dupcook leak where new_asoc was not freed
 *              when security_sctp_assoc_request() failed.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-release-on-error-after-alloc
 * @tags reliability
 *       security
 *       external/cwe/cwe-401
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.controlflow.Guards

/**
 * Heuristic: a call that produces a resource that the caller owns and
 * must release. We look at the function name suffix/prefix family used
 * pervasively in the kernel (e.g. sctp_association_new, kzalloc,
 * of_parse_phandle, kobject_create, ...).
 */
bindingset[n]
predicate isAllocLikeName(string n) {
  n.matches("%\\_new") or
  n.matches("%\\_alloc") or
  n.matches("%\\_alloc\\_%") or
  n.matches("%\\_create") or
  n.matches("%\\_dup") or
  n = "kmalloc" or
  n = "kzalloc" or
  n = "kcalloc" or
  n = "vmalloc" or
  n = "vzalloc" or
  n = "kmemdup" or
  n = "kstrdup" or
  n.matches("kobject\\_create%") or
  n.matches("of\\_parse\\_phandle%") or
  n.matches("of\\_get\\_%") or
  n.matches("of\\_find\\_%")
}

/**
 * Function call that allocates / acquires a resource whose result is
 * stored in `v`. We require the result to be assigned to a local-ish
 * variable so we can later check whether that variable is freed on
 * the failing error path.
 */
class AllocCall extends FunctionCall {
  AllocCall() {
    exists(string n | n = this.getTarget().getName() | isAllocLikeName(n))
  }
}

/**
 * Heuristic: a call whose name suggests a release/free operation that
 * matches the allocator family above.
 */
bindingset[n]
predicate isReleaseLikeName(string n) {
  n.matches("%\\_free") or
  n.matches("%\\_free\\_%") or
  n.matches("%\\_put") or
  n.matches("%\\_release") or
  n.matches("%\\_destroy") or
  n.matches("%\\_delete") or
  n = "kfree" or
  n = "vfree" or
  n = "kvfree" or
  n = "of_node_put" or
  n = "kobject_put"
}

class ReleaseCall extends FunctionCall {
  ReleaseCall() {
    exists(string n | n = this.getTarget().getName() | isReleaseLikeName(n))
  }

  Expr getReleasedExpr() { result = this.getAnArgument() }
}

/**
 * A fallible "gatekeeper" call: kernel idioms where a non-zero (or
 * negative) return signals an error path that must clean up. This
 * covers security_*, validation helpers and the kind of LSM hook
 * involved in the seed commit.
 */
bindingset[n]
predicate isGatekeeperName(string n) {
  n.matches("security\\_%") or
  n.matches("%\\_check") or
  n.matches("%\\_verify") or
  n.matches("%\\_validate") or
  n = "copy_from_user" or
  n = "copy_to_user" or
  n.matches("%\\_register") or
  n.matches("%\\_setup")
}

class GatekeeperCall extends FunctionCall {
  GatekeeperCall() {
    exists(string n | n = this.getTarget().getName() | isGatekeeperName(n))
  }
}

/**
 * Return statement reachable from the error-branch of a gatekeeper
 * call, without an intervening release call that takes `v` as an
 * argument.
 */
predicate isEarlyReturnOnError(ReturnStmt ret, GatekeeperCall gk, Variable v) {
  // Same enclosing function
  ret.getEnclosingFunction() = gk.getEnclosingFunction() and
  // The return happens after the gatekeeper call lexically
  ret.getLocation().getStartLine() > gk.getLocation().getStartLine() and
  ret.getLocation().getStartLine() - gk.getLocation().getStartLine() < 8 and
  // No release of v between gk and ret
  not exists(ReleaseCall rel |
    rel.getEnclosingFunction() = gk.getEnclosingFunction() and
    rel.getLocation().getStartLine() >= gk.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= ret.getLocation().getStartLine() and
    rel.getReleasedExpr().(VariableAccess).getTarget() = v
  )
}

from Function f, AllocCall ac, Variable v, GatekeeperCall gk, ReturnStmt ret
where
  // v is assigned the result of ac inside f
  ac.getEnclosingFunction() = f and
  exists(AssignExpr ae |
    ae.getRValue() = ac and
    ae.getLValue().(VariableAccess).getTarget() = v
  )
  or
  // or v is initialized with ac
  exists(Variable vv, Initializer init |
    vv = v and
    init = vv.getInitializer() and
    init.getExpr() = ac and
    f = ac.getEnclosingFunction()
  )
and
  gk.getEnclosingFunction() = f and
  // gatekeeper call appears after the allocator
  gk.getLocation().getStartLine() > ac.getLocation().getStartLine() and
  // there exists an early return on the failing branch with no release of v
  isEarlyReturnOnError(ret, gk, v) and
  // and v is never released ANYWHERE between ac and ret in f
  not exists(ReleaseCall rel |
    rel.getEnclosingFunction() = f and
    rel.getReleasedExpr().(VariableAccess).getTarget() = v and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    rel.getLocation().getStartLine() > ac.getLocation().getStartLine()
  )
select ret,
  "Possible resource leak: '" + v.getName() + "' allocated by '" +
    ac.getTarget().getName() + "' is not released on the error path after '" +
    gk.getTarget().getName() + "' before this return."
