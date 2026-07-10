/**
 * @name Missing of_node_put on early exit from for_each_available_child_of_node
 * @description When breaking, returning, or jumping (goto) out of a
 *              for_each_*_child_of_node iteration macro early, the loop's
 *              child iterator holds a reference that must be released with
 *              of_node_put(). Failure to do so leaks a device_node refcount.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-iter-refcount-leak
 * @tags reliability
 *       correctness
 *       refcount
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * The family of OF (open-firmware / device-tree) iteration macros that take
 * an implicit reference on the iterator variable on each step and require an
 * of_node_put() when the loop is exited prematurely.
 */
predicate isOfChildIterMacroName(string name) {
  name = "for_each_child_of_node" or
  name = "for_each_available_child_of_node" or
  name = "for_each_node_by_name" or
  name = "for_each_node_by_type" or
  name = "for_each_compatible_node" or
  name = "for_each_matching_node" or
  name = "for_each_matching_node_and_match"
}

class OfChildIterInvocation extends MacroInvocation {
  OfChildIterInvocation() { isOfChildIterMacroName(this.getMacroName()) }

  /** The child iterator variable expression text (first macro arg). */
  string getIterArgText() { result = this.getUnexpandedArgument(0) }
}

/**
 * A statement lexically inside the body of an of_* child iteration macro.
 */
predicate inOfChildIterBody(Stmt s, OfChildIterInvocation inv) {
  exists(Location il, Location sl |
    il = inv.getLocation() and
    sl = s.getLocation() and
    il.getFile() = sl.getFile() and
    sl.getStartLine() >= il.getStartLine() and
    sl.getStartLine() <= il.getEndLine()
  )
}

/**
 * An exit statement (return / goto / break) inside an of_* iter body that
 * leaves the loop. We exclude `continue` since it does not abandon the
 * iterator (the macro keeps stepping).
 */
class IterEarlyExit extends Stmt {
  OfChildIterInvocation inv;

  IterEarlyExit() {
    inOfChildIterBody(this, inv) and
    (
      this instanceof ReturnStmt or
      this instanceof GotoStmt or
      this instanceof BreakStmt
    )
  }

  OfChildIterInvocation getIter() { result = inv }
}

/**
 * A call to of_node_put. We recognise the function by name (it may be a
 * macro-expanded inline or a direct extern call).
 */
class OfNodePutCall extends FunctionCall {
  OfNodePutCall() { this.getTarget().getName() = "of_node_put" }
}

/**
 * Heuristic: a release of the iterator variable. We check that some
 * of_node_put() call appears in the same function before the exit AND
 * mentions the iterator name in its argument text (since the iterator is
 * a macro arg, exact dataflow may be obscured by macro expansion).
 */
predicate releasesIter(IterEarlyExit exit) {
  exists(OfNodePutCall call, string iterTxt |
    iterTxt = exit.getIter().getIterArgText() and
    call.getEnclosingFunction() = exit.getEnclosingFunction() and
    call.getLocation().getFile() = exit.getLocation().getFile() and
    // call appears on or before the exit (statement-level approximation)
    call.getLocation().getStartLine() <= exit.getLocation().getStartLine() and
    call.getLocation().getStartLine() >=
      exit.getIter().getLocation().getStartLine() and
    call.getArgument(0).toString().regexpMatch(".*\\b" + iterTxt + "\\b.*")
  )
}

from IterEarlyExit exit, OfChildIterInvocation inv
where
  inv = exit.getIter() and
  not releasesIter(exit) and
  // ignore the trivial fall-through end of the loop (no exit stmt there)
  exists(exit.getLocation().getFile())
select exit,
  "Early exit from " + inv.getMacroName() +
    " without of_node_put() on the child iterator '" + inv.getIterArgText() +
    "' — leaks the device_node reference held by the loop."
