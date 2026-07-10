/**
 * @name  rq3-c2-lin-2-rep4
 * @id    cpp/rq3/c2/lin-2-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing of_node_put on early-exit paths inside
 *              for_each_available_child_of_node (and siblings) loops.
 */

import cpp

/* Macro names that implicitly take a refcount on the iteration variable. */
predicate isOfIterMacroName(string n) {
  n = "for_each_available_child_of_node" or
  n = "for_each_child_of_node" or
  n = "for_each_node_by_name" or
  n = "for_each_node_by_type" or
  n = "for_each_compatible_node" or
  n = "for_each_matching_node" or
  n = "for_each_matching_node_and_match"
}

/* A macro invocation that is one of the of_node iteration macros. */
predicate isOfIterMacroInvocation(MacroInvocation mi) {
  isOfIterMacroName(mi.getMacroName())
}

/* The iteration variable name (textually) of an of_node iteration macro
 * invocation. Heuristic: the second comma-separated macro argument. */
predicate ofIterChildName(MacroInvocation mi, string name) {
  isOfIterMacroInvocation(mi) and
  name = mi.getExpandedArgument(1).trim()
}

/* A statement that lives within the textual expansion of an of_node
 * iteration macro. */
predicate stmtInOfIterLoop(Stmt s, MacroInvocation mi) {
  isOfIterMacroInvocation(mi) and
  s.getLocation().getFile() = mi.getFile() and
  s.getLocation().getStartLine() >= mi.getLocation().getStartLine() and
  s.getLocation().getEndLine() <= mi.getLocation().getEndLine() + 50
}

/* An "early exit" statement inside the of_node iteration loop body:
 * a goto, return, or break. */
predicate earlyExitInOfIterLoop(Stmt exit, MacroInvocation mi) {
  stmtInOfIterLoop(exit, mi) and
  (
    exit instanceof GotoStmt or
    exit instanceof ReturnStmt or
    exit instanceof BreakStmt
  )
}

/* A call to of_node_put on the iteration variable that textually precedes
 * the early-exit statement (within the same loop expansion region). */
predicate hasOfNodePutBeforeExit(Stmt exit, MacroInvocation mi, string childName) {
  exists(FunctionCall fc |
    fc.getTarget().getName() = "of_node_put" and
    fc.getLocation().getFile() = exit.getLocation().getFile() and
    fc.getLocation().getStartLine() >= mi.getLocation().getStartLine() and
    fc.getLocation().getEndLine() <= exit.getLocation().getStartLine() and
    fc.getArgument(0).toString() = childName
  )
}

/* Top-level: an early-exit statement inside an of_node iteration loop
 * whose iteration variable is not released before the exit. */
predicate missingOfNodePutOnEarlyExit(Stmt exit, MacroInvocation mi, string childName) {
  earlyExitInOfIterLoop(exit, mi) and
  ofIterChildName(mi, childName) and
  not hasOfNodePutBeforeExit(exit, mi, childName)
}

from Stmt exit, MacroInvocation mi, string childName
where missingOfNodePutOnEarlyExit(exit, mi, childName)
select exit,
  "Early exit from " + mi.getMacroName() + " without of_node_put(" + childName + ")."
