/**
 * @name of_node refcount leak on early exit from for_each_available_child_of_node
 * @description Detects functions that iterate device-tree children via
 *              for_each_available_child_of_node and have an early exit (goto)
 *              without ever calling of_node_put on the iterator child node.
 * @kind problem
 * @problem.severity warning
 * @id qlm/of-node-refcount-leak-l0-lin2-rep3
 */

import cpp

predicate hasEarlyExitWithoutRelease(Function f) {
  exists(FunctionCall fc |
    fc.getTarget().getName() = "for_each_available_child_of_node_helper" and
    fc.getEnclosingFunction() = f
  ) and
  exists(GotoStmt g | g.getEnclosingFunction() = f) and
  not exists(FunctionCall rel |
    rel.getTarget().getName() = "of_node_put" and
    rel.getEnclosingFunction() = f
  )
}

from Function f
where hasEarlyExitWithoutRelease(f)
select f, "Possible of_node refcount leak: early exit from for_each_available_child_of_node in '" + f.getName() + "' without of_node_put"
