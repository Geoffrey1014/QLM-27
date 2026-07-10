/**
 * @name Missing of_node_put on early exit from for_each_*_child_of_node loop
 * @description The for_each_*_child_of_node family of iterator macros
 *              (for_each_child_of_node, for_each_available_child_of_node,
 *              for_each_compatible_node, etc.) take a reference to each child
 *              device_node on every iteration and drop it implicitly when the
 *              loop advances. When the loop body exits early (return, goto,
 *              break) the reference on the current child is leaked unless
 *              of_node_put() is called explicitly on it.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-iter-refcount-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * The set of OF iterator macros that implicitly take a reference on the
 * loop variable.  Any early exit out of one of these without an explicit
 * of_node_put() on the loop child leaks a refcount.
 */
predicate isOfChildIterMacro(Macro m) {
  m.getName() = "for_each_child_of_node" or
  m.getName() = "for_each_available_child_of_node" or
  m.getName() = "for_each_compatible_node" or
  m.getName() = "for_each_matching_node" or
  m.getName() = "for_each_matching_node_and_match" or
  m.getName() = "for_each_node_by_name" or
  m.getName() = "for_each_node_by_type" or
  m.getName() = "for_each_node_with_property" or
  m.getName() = "for_each_of_cpu_node" or
  m.getName() = "for_each_of_allnodes" or
  m.getName() = "for_each_of_allnodes_from"
}

/** A macro invocation of one of the OF child iterators. */
class OfChildIterInvocation extends MacroInvocation {
  OfChildIterInvocation() { isOfChildIterMacro(this.getMacro()) }

  /**
   * The name of the loop variable as written at the invocation site
   * (e.g. `child`, `np`, ...). This is the first macro argument.
   */
  string getChildName() { result = this.getUnexpandedArgument(0) }
}

/**
 * A statement that lexically lies inside the body of an OF child iterator
 * invocation, paired with the name of that invocation's loop variable.
 */
predicate inOfIterBody(Stmt s, OfChildIterInvocation inv, string childName) {
  s.getLocation().getFile() = inv.getFile() and
  s.getLocation().getStartLine() > inv.getLocation().getStartLine() and
  s.getLocation().getEndLine() <= inv.getLocation().getEndLine() and
  childName = inv.getChildName()
}

/**
 * Holds if `exit` is a statement that causes an early exit out of the
 * `for_each_*_child_of_node` loop body (return, goto out of the loop,
 * or break that leaves the loop). For our purposes any of these prevents
 * the implicit `of_node_put` from running on the current child.
 *
 * `goto` and `return` are over-approximated as "early exit". `break` is
 * also flagged: breaking out of the iterator loop body equally leaks the
 * current child reference.
 */
predicate isEarlyExit(Stmt exit) {
  exit instanceof ReturnStmt or
  exit instanceof GotoStmt or
  exit instanceof BreakStmt
}

/**
 * Holds if there is a call to `of_node_put(childName)` that is
 * "sufficiently near" the exit statement and dominates it textually
 * within the same enclosing block (same file, on a line at or before the
 * exit, after the loop header, and within ~5 lines of the exit).
 *
 * This is a syntactic heuristic; CFG-based analysis would be more precise
 * but the bug pattern is local enough that the lexical check suffices.
 */
predicate hasOfNodePutNearExit(OfChildIterInvocation inv, string childName, Stmt exit) {
  exists(FunctionCall fc |
    fc.getTarget().getName() = "of_node_put" and
    fc.getArgument(0).toString() = childName and
    fc.getLocation().getFile() = exit.getLocation().getFile() and
    fc.getLocation().getStartLine() > inv.getLocation().getStartLine() and
    fc.getLocation().getStartLine() <= exit.getLocation().getStartLine() and
    fc.getLocation().getStartLine() >= exit.getLocation().getStartLine() - 5
  )
}

/**
 * Holds if the loop body contains an assignment of the form
 * `childName = NULL` near the exit. Some code uses the convention of
 * NULLing the iterator before goto so that a shared cleanup label calls
 * of_node_put on it; the cleanup label is then responsible. To avoid
 * those false positives, treat such assignments as a put-equivalent.
 */
predicate childNulledNearExit(string childName, Stmt exit) {
  exists(AssignExpr a |
    a.getLValue().toString() = childName and
    a.getRValue().getValue() = "0" and
    a.getLocation().getFile() = exit.getLocation().getFile() and
    a.getLocation().getStartLine() <= exit.getLocation().getStartLine() and
    a.getLocation().getStartLine() >= exit.getLocation().getStartLine() - 5
  )
}

from OfChildIterInvocation inv, Stmt exit, string childName
where
  inOfIterBody(exit, inv, childName) and
  isEarlyExit(exit) and
  not hasOfNodePutNearExit(inv, childName, exit) and
  not childNulledNearExit(childName, exit) and
  // Don't flag the `break` immediately at the end of the loop with no
  // intervening statement (rare but reduces noise on tight idioms).
  not (
    exit instanceof BreakStmt and
    exit.getLocation().getStartLine() = inv.getLocation().getEndLine()
  ) and
  childName != ""
select exit,
  "Early exit from " + inv.getMacroName() + " loop without of_node_put(" + childName +
    "); the iterator macro takes a reference on each child that must be released on early exit."
