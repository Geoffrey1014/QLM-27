/**
 * @name Missing release of allocated resource on error-check return path
 * @description Detects a function call that allocates / acquires a resource
 *              (returns a pointer assigned to a local variable), followed
 *              later by an error check whose then-branch returns without
 *              releasing the previously-allocated resource. Pattern derived
 *              from CVE-style "missing free on error path" memory leaks.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-1
 * @tags correctness
 *       resource-leak
 */

import cpp

/** Heuristic: function call that returns a pointer and is naming-consistent
 *  with resource acquisition (alloc/new/make/create/get/acquire/parse). */
predicate acquiringCall(FunctionCall fc) {
  fc.getType().getUnspecifiedType() instanceof PointerType and
  exists(string n | n = fc.getTarget().getName().toLowerCase() |
    n.matches("%alloc%") or
    n.matches("%kmalloc%") or
    n.matches("%kzalloc%") or
    n.matches("%new%") or
    n.matches("%make%") or
    n.matches("%create%") or
    n.matches("%_get_%") or
    n.matches("get\\_%") or
    n.matches("%acquire%") or
    n.matches("%parse%") or
    n.matches("%dup%") or
    n.matches("%build%") or
    n.matches("%open%")
  )
}

/** Heuristic: function call that releases a resource. */
predicate releasingCall(FunctionCall fc, Variable v) {
  exists(string n | n = fc.getTarget().getName().toLowerCase() |
    n.matches("%free%") or
    n.matches("%release%") or
    n.matches("%put%") or
    n.matches("%destroy%") or
    n.matches("%close%") or
    n.matches("%delete%") or
    n.matches("%dispose%") or
    n.matches("%cleanup%") or
    n.matches("%unref%") or
    n = "kfree" or n = "vfree"
  ) and
  fc.getAnArgument().(VariableAccess).getTarget() = v
}

/** A statement is an "error return" if it is a ReturnStmt inside the then-branch
 *  of an `if` whose then-branch does not also release v. */
predicate isErrorReturnLeakingVar(ReturnStmt ret, Variable v, Function f, IfStmt ifs) {
  ret.getEnclosingFunction() = f and
  ifs.getEnclosingFunction() = f and
  ret.getParent*() = ifs.getThen() and
  // No release of v within the then-branch
  not exists(FunctionCall rel |
    rel.getParent*() = ifs.getThen() and
    releasingCall(rel, v)
  )
}

from FunctionCall acq, Variable v, Function f, ReturnStmt errRet, IfStmt errIf
where
  f = acq.getEnclosingFunction() and
  acquiringCall(acq) and
  // v gets the result of acq (assignment or initializer).
  (
    exists(AssignExpr a |
      a.getRValue() = acq and
      a.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(Initializer init |
      v.getInitializer() = init and
      init.getExpr() = acq
    )
  ) and
  // The error return is reachable from the acquire (control-flow successor).
  acq.getASuccessor+() = errRet and
  isErrorReturnLeakingVar(errRet, v, f, errIf) and
  // Exclude the trivial null-check that *immediately* follows the acquire
  // (e.g. `if (!v) return ...;`) — that's not a leak, v is null.
  not exists(VariableAccess va |
    va = errIf.getCondition().getAChild*() and
    va.getTarget() = v and
    not exists(FunctionCall other |
      other.getEnclosingFunction() = f and
      other != acq and
      acq.getASuccessor+() = other and
      other.getASuccessor+() = errIf
    )
  ) and
  // There exists at least one path from acq to errRet on which v is never released.
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    releasingCall(rel, v) and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = errRet
  )
select errRet,
  "Possible memory/refcount leak: resource acquired by call to $@ (stored in $@) is not released on this error-return path.",
  acq, acq.getTarget().getName(), v, v.getName()
