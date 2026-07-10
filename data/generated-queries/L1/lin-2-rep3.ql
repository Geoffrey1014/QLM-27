/**
 * @name of_node refcount leak on early exit from for_each_available_child_of_node
 * @description Detects functions that iterate device-tree children via
 *              for_each_available_child_of_node and have an early exit (goto)
 *              without ever calling of_node_put on the iterator child node.
 * @kind problem
 * @problem.severity warning
 * @id qlm/of-node-refcount-leak-l1-lin2-rep3
 */

import cpp

predicate usesForEachAvailChild(Function f) {
  exists(FunctionCall fc |
    fc.getTarget().getName() = "for_each_available_child_of_node_helper" and
    fc.getEnclosingFunction() = f
  )
}

predicate lacksOfNodePut(Function f) {
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    (
      rel.getTarget().getName() = "of_node_put" or
      rel.getTarget().getName() = "OF_NODE_PUT" or
      rel.getTarget().getName() = "of_node_put_alias"
    )
  )
}

from Function f
where
  usesForEachAvailChild(f) and
  lacksOfNodePut(f) and
  exists(GotoStmt g | g.getEnclosingFunction() = f)
select f,
  "Possible of_node refcount leak: for_each_available_child_of_node iterator with early exit in '" +
    f.getName() + "' without matching of_node_put on the child iterator"
