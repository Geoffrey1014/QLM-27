/**
 * @name  rq3-c2-lin-2-rep3
 * @id    cpp/rq3/c2/lin-2-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects refcount leaks of device-tree child nodes when an
 *              early exit (return/goto/break) is taken inside a
 *              for_each_available_child_of_node() (or sibling) loop without
 *              calling of_node_put() on the iterator variable first.
 */

import cpp

/** A macro invocation of one of the OF iterator macros that takes a
 *  refcount on each child node and expects of_node_put() on early exit. */
predicate isOfIterMacro(MacroInvocation mi) {
  exists(string n | n = mi.getMacroName() |
    n = "for_each_available_child_of_node" or
    n = "for_each_child_of_node" or
    n = "for_each_available_child_of_node_scoped" or
    n = "for_each_node_by_type" or
    n = "for_each_node_by_name" or
    n = "for_each_compatible_node"
  )
}

/** The iterator (child) Variable used by the OF iterator macro `mi`. We
 *  approximate by looking for a local Variable whose declaration or use is
 *  textually within the macro invocation extent. */
predicate iteratorVarOf(MacroInvocation mi, Variable v) {
  exists(VariableAccess va |
    va = v.getAnAccess() and
    va.getEnclosingFunction() = mi.getEnclosingFunction() and
    va.getLocation().getStartLine() = mi.getLocation().getStartLine() and
    va.getLocation().getFile() = mi.getLocation().getFile()
  )
}

/** A call to of_node_put(v). */
predicate isOfNodePutCall(FunctionCall c, Variable v) {
  c.getTarget().getName() = "of_node_put" and
  c.getArgument(0) = v.getAnAccess()
}

/** The body Stmt covered by the OF iterator macro `mi`: the loop body the
 *  macro expands to. We pick the smallest enclosing Stmt of the macro
 *  invocation that contains other statements following it on subsequent
 *  lines (i.e. the for-loop's body). */
predicate macroLoopBody(MacroInvocation mi, Stmt body) {
  exists(Function f | f = mi.getEnclosingFunction() |
    body.getEnclosingFunction() = f and
    body.getLocation().getStartLine() >= mi.getLocation().getStartLine() and
    body.getLocation().getEndLine() >= mi.getLocation().getStartLine() and
    body.getLocation().getFile() = mi.getLocation().getFile() and
    (body instanceof BlockStmt or body instanceof ForStmt)
  )
}

/** Heuristic: an "early-exit" statement inside the loop body of `mi` that
 *  abandons the iteration without of_node_put(v) appearing on the same
 *  basic block earlier. We look for ReturnStmt or GotoStmt syntactically
 *  inside the macro's enclosing function and lexically after the macro,
 *  for which no of_node_put(v) call exists between the macro line and the
 *  exit statement's line in the same function. */
predicate earlyExitInLoopMissingPut(MacroInvocation mi, Variable v, Stmt exit) {
  iteratorVarOf(mi, v) and
  exists(Function f |
    f = mi.getEnclosingFunction() and
    exit.getEnclosingFunction() = f and
    exit.getLocation().getFile() = mi.getLocation().getFile() and
    exit.getLocation().getStartLine() > mi.getLocation().getStartLine() and
    (exit instanceof ReturnStmt or exit instanceof GotoStmt) and
    // No of_node_put(v) appears between the macro and the exit statement
    not exists(FunctionCall put |
      isOfNodePutCall(put, v) and
      put.getEnclosingFunction() = f and
      put.getLocation().getStartLine() >= mi.getLocation().getStartLine() and
      put.getLocation().getStartLine() <= exit.getLocation().getStartLine()
    )
  )
}

from MacroInvocation mi, Variable v, Stmt exit
where
  isOfIterMacro(mi) and
  iteratorVarOf(mi, v) and
  earlyExitInLoopMissingPut(mi, v, exit)
select exit,
  "Possible refcount leak: early exit from " + mi.getMacroName() +
    "() loop without calling of_node_put() on iterator '" + v.getName() + "'."
