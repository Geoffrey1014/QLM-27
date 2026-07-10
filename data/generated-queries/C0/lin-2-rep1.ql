/**
 * @name Missing of_node_put on early exit from for_each_*_child_of_node loop
 * @description The for_each_available_child_of_node() / for_each_child_of_node()
 *              family iterates device-tree nodes and increments the refcount of
 *              the loop variable on each iteration. The macro decrements the
 *              refcount automatically on normal loop continuation, but on an
 *              early `goto`, `return`, or `break` that exits the loop, callers
 *              must explicitly call of_node_put() on the loop variable, or the
 *              child node refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-put-missing-on-early-exit
 * @tags correctness
 *       reliability
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A macro invocation of one of the for_each_*_child_of_node family.
 * The second argument of the macro is the loop variable that holds the
 * current child node.
 */
class ForEachChildOfNodeMacro extends MacroInvocation {
  ForEachChildOfNodeMacro() {
    exists(string n | n = this.getMacroName() |
      n = "for_each_child_of_node" or
      n = "for_each_available_child_of_node" or
      n = "for_each_compatible_node" or
      n = "for_each_matching_node" or
      n = "for_each_matching_node_and_match" or
      n = "for_each_node_by_name" or
      n = "for_each_node_by_type" or
      n = "for_each_node_with_property"
    )
  }

  /** The loop variable (child node pointer). */
  Variable getChildVariable() {
    exists(VariableAccess va |
      va = this.getAnExpandedElement() and
      va.getTarget() = result and
      result.getType().getUnspecifiedType() instanceof PointerType
    )
  }
}

/**
 * A statement inside the body of the loop macro that causes an early
 * exit (goto, return, break) without first calling of_node_put on the
 * child variable.
 */
predicate earlyExitStmt(Stmt s) {
  s instanceof GotoStmt or
  s instanceof ReturnStmt or
  s instanceof BreakStmt
}

/**
 * A call to of_node_put(child) where `child` is `v`.
 */
predicate isOfNodePutCallOn(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  exists(VariableAccess va |
    va = fc.getArgument(0).getAChild*() and
    va.getTarget() = v
  )
}

/**
 * Holds if `exit` is an early-exit statement contained inside the
 * expansion of `loop`, and the loop's child variable `v` is not put
 * before that exit (within the same basic-block chain leading to exit).
 */
predicate missingPut(ForEachChildOfNodeMacro loop, Stmt exit, Variable v) {
  v = loop.getChildVariable() and
  earlyExitStmt(exit) and
  // exit is lexically inside the loop body
  exists(Location lloc, Location eloc |
    lloc = loop.getLocation() and
    eloc = exit.getLocation() and
    lloc.getFile() = eloc.getFile() and
    eloc.getStartLine() >= lloc.getStartLine() and
    eloc.getEndLine() <= lloc.getStartLine() + 200
  ) and
  // No of_node_put(v) call appears between the loop start and the exit
  // in the same function.
  exists(Function f |
    f = exit.getEnclosingFunction() and
    not exists(FunctionCall fc |
      isOfNodePutCallOn(fc, v) and
      fc.getEnclosingFunction() = f and
      fc.getLocation().getFile() = exit.getLocation().getFile() and
      fc.getLocation().getStartLine() >= loop.getLocation().getStartLine() and
      fc.getLocation().getStartLine() <= exit.getLocation().getStartLine()
    )
  )
}

from ForEachChildOfNodeMacro loop, Stmt exit, Variable v
where missingPut(loop, exit, v)
select exit,
  "Possible refcount leak: early exit (" + exit.toString() +
  ") from " + loop.getMacroName() +
  " without of_node_put on '" + v.getName() + "'."
