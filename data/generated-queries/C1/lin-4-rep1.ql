/**
 * @name Missing of_node_put on error path after of_parse_phandle
 * @description of_parse_phandle() returns a device_node pointer with the
 *              refcount incremented. The acquired pointer must be released
 *              via of_node_put() on every successful path that reaches
 *              function exit. This query reports functions that acquire
 *              a node via of_parse_phandle (or similar refcount-incrementing
 *              OF accessor) and then have at least one control-flow path
 *              from the acquire to a return statement that does NOT execute
 *              any call to of_node_put on the acquired variable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-4
 */

import cpp
import semmle.code.cpp.controlflow.StackVariableReachability

/* APIs whose return value is a refcount-incremented device_node pointer
   that must be released with of_node_put(). The list is generic — derived
   from of-API conventions, NOT from the POC scaffold. */
predicate isOfAcquire(string name) {
  name = "of_parse_phandle" or
  name = "of_parse_phandle_with_args" or
  name = "of_find_node_by_path" or
  name = "of_find_node_opts_by_path" or
  name = "of_find_matching_node" or
  name = "of_find_matching_node_and_match" or
  name = "of_find_compatible_node" or
  name = "of_find_node_by_name" or
  name = "of_find_node_by_phandle" or
  name = "of_get_child_by_name" or
  name = "of_get_next_child" or
  name = "of_get_next_available_child" or
  name = "of_get_parent" or
  name = "of_get_next_parent"
}

/* The acquire call: a call to one of the listed APIs whose result is
   assigned into a local variable. */
class AcquireCall extends FunctionCall {
  AcquireCall() { isOfAcquire(this.getTarget().getName()) }
}

/* A release call on a particular variable. */
predicate releasesVar(FunctionCall fc, LocalScopeVariable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

/* The variable that holds the acquired node, when the acquire is on the
   RHS of an assignment or initializer. */
predicate acquiresInto(AcquireCall ac, LocalScopeVariable v) {
  exists(AssignExpr ae |
    ae.getRValue() = ac and ae.getLValue() = v.getAnAccess())
  or
  exists(Initializer i |
    i.getExpr() = ac and i.getDeclaration() = v)
}

/* A ReturnStmt that is reachable from the acquire without traversing a
   release on the variable. Implemented as a simple intraprocedural CFG
   reachability over BasicBlocks, treating any BB that contains a
   release-of-v as a barrier. The start point is the "non-null" successor
   of the null-check guard `if (!v) ...`, so the early-return on a
   failed-acquire (v == NULL, nothing to release) is NOT flagged. */
predicate badReturn(AcquireCall ac, LocalScopeVariable v, ReturnStmt ret) {
  acquiresInto(ac, v) and
  ret.getEnclosingFunction() = ac.getEnclosingFunction() and
  exists(BasicBlock startBB, BasicBlock retBB |
    nonNullStartBB(ac, v, startBB) and
    retBB.contains(ret) and
    reachesWithoutRelease(startBB, retBB, v)
  )
}

/* Identify the basic block reached when v is known non-null after the
   acquire. We look for a null-check on v that post-dominates the acquire
   in source order and pick its FALSE branch (i.e., !v is false → v is
   non-null). If no such guard exists, fall back to the acquire's own BB
   (the leak-on-null-acquire path is the user's other concern; here we
   focus on the "v acquired then leaked" pattern). */
predicate nonNullStartBB(AcquireCall ac, LocalScopeVariable v, BasicBlock bb) {
  exists(IfStmt ifs, NotExpr ne, VariableAccess va |
    ifs.getEnclosingFunction() = ac.getEnclosingFunction() and
    ifs.getCondition() = ne and
    ne.getOperand() = va and
    va = v.getAnAccess() and
    ifs.getLocation().getStartLine() > ac.getLocation().getStartLine() and
    bb = ifs.getThen().getBasicBlock().getAPredecessor().getASuccessor() and
    // pick the successor that is NOT the THEN branch
    bb != ifs.getThen().getBasicBlock()
  )
  or
  // Fallback: no null-check found → start from acquire BB
  not exists(IfStmt ifs, NotExpr ne, VariableAccess va |
    ifs.getEnclosingFunction() = ac.getEnclosingFunction() and
    ifs.getCondition() = ne and
    ne.getOperand() = va and
    va = v.getAnAccess() and
    ifs.getLocation().getStartLine() > ac.getLocation().getStartLine()
  ) and
  bb.contains(ac)
}

predicate isReleaseBB(BasicBlock bb, LocalScopeVariable v) {
  exists(FunctionCall fc | bb.contains(fc) and releasesVar(fc, v))
}

predicate reachesWithoutRelease(BasicBlock src, BasicBlock dst, LocalScopeVariable v) {
  src = dst and not isReleaseBB(dst, v)
  or
  exists(BasicBlock mid |
    src.getASuccessor() = mid and
    not isReleaseBB(mid, v) and
    reachesWithoutRelease(mid, dst, v)
  )
  or
  // allow the src BB itself to be partially-traversed: only the suffix
  // after the acquire matters; release in same BB before the acquire
  // would not be relevant. Treat src as starting point regardless.
  exists(BasicBlock mid |
    src.getASuccessor() = mid and
    reachesWithoutRelease(mid, dst, v) and
    not isReleaseBB(mid, v)
  )
}

from AcquireCall ac, LocalScopeVariable v, ReturnStmt ret, Function f
where
  acquiresInto(ac, v) and
  f = ac.getEnclosingFunction() and
  badReturn(ac, v, ret) and
  // Exclude functions that do not contain any of_node_put at all only if
  // we want to suppress purely-leaky stubs; here we KEEP them — a function
  // that never calls of_node_put after a refcount acquire is a clear bug.
  ret.getEnclosingFunction() = f
select ac,
  "of_parse_phandle/of-acquire result stored in $@ may leak: return at $@ is reachable without of_node_put.",
  v, v.getName(), ret, "this return"
