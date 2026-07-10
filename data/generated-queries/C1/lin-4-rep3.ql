/**
 * @name Device-tree node refcount leak on early return (missing of_node_put)
 * @description An of_*-family accessor returns a struct device_node*
 *              whose refcount has been incremented. The caller must
 *              balance this with of_node_put() along every path that
 *              leaves the enclosing function. When a return statement is
 *              reachable from the acquisition without any intervening
 *              of_node_put() on the receiving variable, the device-tree
 *              node reference leaks on that path (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-4
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Names of of_*-family routines whose return value carries an
 * incremented device_node refcount that the caller owns.
 */
predicate ofRefcountAcquireApi(string n) {
  n = "of_parse_phandle" or
  n = "of_find_node_by_name" or
  n = "of_find_node_by_path" or
  n = "of_find_node_opts_by_path" or
  n = "of_find_compatible_node" or
  n = "of_find_matching_node" or
  n = "of_find_matching_node_and_match" or
  n = "of_get_child_by_name" or
  n = "of_get_next_child" or
  n = "of_get_next_available_child" or
  n = "of_get_parent" or
  n = "of_get_next_parent" or
  n = "of_get_cpu_node" or
  n = "of_irq_find_parent"
}

/** A call that acquires an of_*-managed device_node refcount. */
class OfAcquireCall extends FunctionCall {
  OfAcquireCall() { ofRefcountAcquireApi(this.getTarget().getName()) }
}

/** A call to of_node_put — the matching refcount release. */
class OfNodePutCall extends FunctionCall {
  OfNodePutCall() { this.getTarget().getName() = "of_node_put" }
}

/**
 * The variable into which `call` flows directly, via either an
 * initializer (`T *v = call(...)`) or a top-level assignment
 * (`v = call(...)`).
 */
Variable captureSink(OfAcquireCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = call and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/** An of_node_put call inside `f` whose first arg is a read of `v`. */
predicate isReleaseOf(OfNodePutCall p, Variable v) {
  exists(VariableAccess r |
    r = p.getArgument(0) and
    r.getTarget() = v
  )
}

/**
 * `ret` is a ReturnStmt that is reachable in the CFG from `acq` without
 * passing through any of_node_put(`sink`) call.
 */
/**
 * `ret` belongs to the null-check arm `if (!sink) return ...;` immediately
 * following acquisition of `sink`. Releasing a null pointer is unnecessary,
 * so such returns should not be flagged.
 */
predicate isNullCheckReturn(Variable sink, ReturnStmt ret) {
  exists(IfStmt ifs, NotExpr ne, VariableAccess va |
    ifs.getCondition() = ne and
    ne.getOperand() = va and
    va.getTarget() = sink and
    ret.getParent*() = ifs.getThen()
  )
  or
  exists(IfStmt ifs, EQExpr eq, VariableAccess va |
    ifs.getCondition() = eq and
    eq.getAnOperand() = va and
    va.getTarget() = sink and
    eq.getAnOperand() instanceof Literal and
    ret.getParent*() = ifs.getThen()
  )
}

predicate leakingReturn(OfAcquireCall acq, Variable sink, ReturnStmt ret) {
  sink = captureSink(acq) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  not isNullCheckReturn(sink, ret) and
  exists(ControlFlowNode node |
    node = acq.getASuccessor+() and
    node = ret and
    not exists(OfNodePutCall p, ControlFlowNode mid |
      isReleaseOf(p, sink) and
      mid = p and
      mid = acq.getASuccessor+() and
      ret = mid.getASuccessor+()
    )
  )
}

from OfAcquireCall acq, Variable sink, ReturnStmt ret
where leakingReturn(acq, sink, ret)
select ret,
  "Return reachable from of_*-acquire of '" + sink.getName() +
  "' (via " + acq.getTarget().getName() +
  ") without an intervening of_node_put() -- device_node refcount leaks on this path."
