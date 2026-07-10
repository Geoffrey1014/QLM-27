/**
 * @name Missing of_node_put on early exit from for_each_*_child_of_node loop
 * @description The for_each_child_of_node / for_each_available_child_of_node family of
 *              macros increments the refcount of the iteration variable on each loop
 *              entry. When the loop is exited early (via return, goto, or break) the
 *              child node must be released explicitly with of_node_put(), otherwise the
 *              device-tree node refcount is leaked.
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
 * A call to a for_each_*_child_of_node-style iteration macro.
 * These macros expand into a for-loop that increments the refcount of the
 * `child` iteration variable each iteration.
 */
class ForEachChildOfNodeMacro extends Macro {
  ForEachChildOfNodeMacro() {
    this.getName() =
      [
        "for_each_child_of_node", "for_each_available_child_of_node",
        "for_each_compatible_node", "for_each_matching_node",
        "for_each_matching_node_and_match", "for_each_node_by_name",
        "for_each_node_by_type", "for_each_node_with_property",
        "for_each_of_allnodes", "for_each_of_allnodes_from",
        "for_each_available_child_of_node_scoped"
      ]
  }
}

/** An invocation (expansion) of a for_each_*_child_of_node macro. */
class ForEachChildInvocation extends MacroInvocation {
  ForEachChildInvocation() { this.getMacro() instanceof ForEachChildOfNodeMacro }

  /**
   * The textual name of the child-node iteration variable, parsed out of the
   * second comma-separated argument of the macro invocation (`for_each_*(parent, child)`).
   */
  string getChildName() {
    exists(string args |
      args = this.getExpandedArgument(1) and
      result = args.trim()
    )
    or
    // Fallback: parse from full expansion if getExpandedArgument(1) is unavailable.
    not exists(this.getExpandedArgument(1)) and
    result = this.getExpandedArgument(0).trim()
  }
}

/**
 * A `goto` or `return` statement that exits the body of a
 * for_each_*_child_of_node loop early.
 */
class EarlyExitStmt extends Stmt {
  ForEachChildInvocation invocation;

  EarlyExitStmt() {
    (
      this instanceof ReturnStmt or
      this instanceof GotoStmt or
      this instanceof BreakStmt
    ) and
    // The statement is inside the source range of the macro invocation's enclosing loop body.
    exists(Function f, Location lExit, Location lMacro |
      f = this.getEnclosingFunction() and
      lExit = this.getLocation() and
      lMacro = invocation.getLocation() and
      f = invocation.getEnclosingFunction() and
      lExit.getStartLine() > lMacro.getStartLine() and
      // Heuristic: within roughly the next ~60 lines of the macro (i.e. its loop body).
      lExit.getStartLine() < lMacro.getStartLine() + 80
    )
  }

  ForEachChildInvocation getLoop() { result = invocation }
}

/**
 * Holds if `s` (or a statement near it within the same basic block run before exit)
 * contains a call to of_node_put on an expression that textually contains `name`.
 */
bindingset[name]
predicate hasOfNodePutCallNearby(Stmt s, string name) {
  exists(FunctionCall fc, Function f, string arg |
    fc.getTarget().getName() = "of_node_put" and
    f = s.getEnclosingFunction() and
    f = fc.getEnclosingFunction() and
    fc.getLocation().getStartLine() <= s.getLocation().getStartLine() and
    fc.getLocation().getStartLine() >= s.getLocation().getStartLine() - 6 and
    arg = fc.getArgument(0).toString() and
    arg.matches("%" + name + "%")
  )
}

from EarlyExitStmt exit, ForEachChildInvocation loop, string childName
where
  loop = exit.getLoop() and
  childName = loop.getChildName() and
  childName != "" and
  // No of_node_put on the child variable right before the early exit.
  not hasOfNodePutCallNearby(exit, childName) and
  // Exclude break inside switch (not iteration break).
  not exists(SwitchStmt sw |
    sw.getEnclosingFunction() = exit.getEnclosingFunction() and
    exit instanceof BreakStmt and
    sw.getLocation().getStartLine() < exit.getLocation().getStartLine() and
    sw.getLocation().getEndLine() >= exit.getLocation().getStartLine()
  )
select exit,
  "Possible of_node_put refcount leak: early exit from " + loop.getMacroName() +
    " loop without releasing child node '" + childName + "'."
