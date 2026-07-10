/**
 * @name Path-specific missing of_node_put on device_node reference
 * @description An of_*-family API call returns a `struct device_node *` whose
 *              refcount is incremented; the enclosing function must call
 *              of_node_put() on every exit path. This detector reports an
 *              acquire site for which there exists a ReturnStmt reachable in
 *              control-flow from the acquire without any intervening
 *              of_node_put() on the receiving variable (CWE-401 / CWE-772).
 *              Monolithic detector for the C1 cell.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-4
 */

import cpp

/* ----- Acquire / release API surface ------------------------------- */

predicate isOfAcquireApi(string n) {
  n = "of_parse_phandle" or
  n = "of_parse_phandle_with_args" or
  n = "of_parse_phandle_with_fixed_args" or
  n = "of_find_node_by_name" or
  n = "of_find_node_by_path" or
  n = "of_find_node_opts_by_path" or
  n = "of_find_node_by_phandle" or
  n = "of_find_matching_node" or
  n = "of_find_matching_node_and_match" or
  n = "of_find_compatible_node" or
  n = "of_get_child_by_name" or
  n = "of_get_next_child" or
  n = "of_get_next_available_child" or
  n = "of_get_parent" or
  n = "of_get_next_parent" or
  n = "of_get_cpu_node" or
  n = "of_irq_find_parent"
}

predicate isOfReleaseApi(string n) {
  n = "of_node_put"
}

/* Receiver Variable of acq: declaration-with-initializer OR assignment. */
Variable receiverOf(FunctionCall acq) {
  exists(Variable v |
    v.getInitializer().getExpr() = acq and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = acq and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/* A release-call on variable v inside function f. */
predicate isReleaseOf(FunctionCall put, Variable v) {
  isOfReleaseApi(put.getTarget().getName()) and
  put.getArgument(0).(VariableAccess).getTarget() = v
}

/* A ReturnStmt that is guarded by `if (!v)` (or equivalent null check on v)
 * — i.e. on the null-pointer path; releasing is unnecessary on this path. */
predicate guardedByNullCheckOf(ReturnStmt r, Variable v) {
  exists(IfStmt ifs, Expr cond |
    cond = ifs.getCondition() and
    r.getParentStmt*() = ifs.getThen() and
    (
      cond.(NotExpr).getOperand().(VariableAccess).getTarget() = v
      or
      exists(EQExpr eq |
        eq = cond and
        eq.getAnOperand().(VariableAccess).getTarget() = v and
        eq.getAnOperand().getValue() = "0"
      )
    )
  )
}

/* There exists a control-flow path from `acq` to ReturnStmt `r`
 * (both in function f) that contains no release on v, AND the return is
 * not on the null-pointer-check branch of v. */
predicate leakyReturnReachable(FunctionCall acq, Variable v, ReturnStmt r) {
  exists(Function f |
    f = acq.getEnclosingFunction() and
    f = r.getEnclosingFunction() and
    acq.getASuccessor+() = r and
    not guardedByNullCheckOf(r, v) and
    not exists(FunctionCall put |
      put.getEnclosingFunction() = f and
      isReleaseOf(put, v) and
      acq.getASuccessor+() = put and
      put.getASuccessor+() = r
    )
  )
}

from FunctionCall acq, Variable v, ReturnStmt r, string apiName
where
  apiName = acq.getTarget().getName() and
  isOfAcquireApi(apiName) and
  v = receiverOf(acq) and
  leakyReturnReachable(acq, v, r)
select acq,
  "Call to " + apiName + " stores a refcounted device_node in '" + v.getName() +
    "'; a return at $@ is reachable without of_node_put() — possible reference leak.",
  r, "this exit path"
