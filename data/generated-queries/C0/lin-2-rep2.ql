/**
 * @name Missing of_node_put on early exit from for_each_available_child_of_node
 * @description Inside a for_each_*_child_of_node iterator macro, an early
 *              return/goto/break that does not call of_node_put on the loop
 *              iterator leaks the device-node refcount.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-leak-iter-early-exit
 * @tags correctness
 *       reliability
 *       refcount
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Macro invocations whose name is one of the of_*-child iterator macros.
 * These expand to a for-loop whose loop variable is a `struct device_node *`
 * with an incremented refcount that must be released with `of_node_put` if
 * the loop is exited early.
 */
class OfChildIterMacroInvocation extends MacroInvocation {
  OfChildIterMacroInvocation() {
    exists(string n | n = this.getMacroName() |
      n = "for_each_child_of_node" or
      n = "for_each_available_child_of_node" or
      n = "for_each_node_by_name" or
      n = "for_each_node_by_type" or
      n = "for_each_compatible_node" or
      n = "for_each_matching_node" or
      n = "for_each_matching_node_and_match" or
      n = "for_each_node_with_property"
    )
  }

  /** The loop iterator child node variable name (2nd macro argument). */
  string getChildArg() { result = this.getUnexpandedArgument(1) }
}

/** A call to of_node_put. */
class OfNodePutCall extends FunctionCall {
  OfNodePutCall() { this.getTarget().hasName("of_node_put") }
}

/**
 * Holds if `stmt` lexically sits inside the body of `iter` (i.e. between
 * the start and end source locations of the macro invocation's expansion
 * region in the same file).
 */
predicate stmtInsideIter(Stmt stmt, OfChildIterMacroInvocation iter) {
  stmt.getLocation().getFile() = iter.getLocation().getFile() and
  stmt.getLocation().getStartLine() >= iter.getLocation().getStartLine() and
  stmt.getLocation().getEndLine() <= iter.getLocation().getEndLine() and
  // exclude the macro line itself
  stmt.getLocation().getStartLine() > iter.getLocation().getStartLine()
}

/**
 * Holds if `e` is an early-exit statement (return/goto/break) inside the
 * body of the iterator macro `iter`.
 */
predicate earlyExitInIter(Stmt exit, OfChildIterMacroInvocation iter) {
  stmtInsideIter(exit, iter) and
  (
    exit instanceof ReturnStmt
    or
    exit instanceof GotoStmt
    or
    exit instanceof BreakStmt
  )
}

/**
 * Holds if there is an of_node_put call on a variable whose name matches the
 * iterator's child-arg, lexically preceding `exit` in the same enclosing
 * block (a coarse proxy for "released before this early-exit").
 */
predicate hasPrecedingOfNodePut(Stmt exit, OfChildIterMacroInvocation iter) {
  exists(OfNodePutCall put, string childName |
    childName = iter.getChildArg() and
    put.getEnclosingFunction() = exit.getEnclosingFunction() and
    put.getLocation().getFile() = exit.getLocation().getFile() and
    put.getLocation().getStartLine() < exit.getLocation().getStartLine() and
    put.getLocation().getStartLine() >= iter.getLocation().getStartLine() and
    exists(VariableAccess va |
      va = put.getArgument(0).getAChild*() and
      va.getTarget().getName() = childName
    )
  )
}

/**
 * Holds if `exit` is on a control-flow path that breaks/returns out of the
 * iteration but is preceded in the same basic-block siblings by an
 * `of_node_put(child)` whose argument is the iterator variable. We use a
 * conservative "same-block siblings" check.
 */
predicate hasSiblingOfNodePut(Stmt exit, OfChildIterMacroInvocation iter) {
  exists(OfNodePutCall put, string childName, BlockStmt b, int iExit, int iPut |
    childName = iter.getChildArg() and
    put.getEnclosingFunction() = exit.getEnclosingFunction() and
    b.getStmt(iExit) = exit and
    b.getStmt(iPut).getAChild*() = put and
    iPut < iExit and
    exists(VariableAccess va |
      va = put.getArgument(0).getAChild*() and
      va.getTarget().getName() = childName
    )
  )
}

from OfChildIterMacroInvocation iter, Stmt exit, string childName
where
  earlyExitInIter(exit, iter) and
  childName = iter.getChildArg() and
  not hasPrecedingOfNodePut(exit, iter) and
  not hasSiblingOfNodePut(exit, iter)
select exit,
  "Early exit from " + iter.getMacroName() + " without of_node_put(" + childName +
    ") leaks the OF device-node refcount."
