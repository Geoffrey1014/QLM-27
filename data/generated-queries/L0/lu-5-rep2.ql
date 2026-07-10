/**
 * @name Memory leak: kstrdup result not freed on all return paths
 * @description Detects local variables assigned the result of kstrdup where
 *              the enclosing function has more return statements than
 *              matching kfree calls on that variable, indicating at least
 *              one leaking control-flow path (e.g. affs_remount pattern).
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu5-kstrdup-leak
 */
import cpp

predicate isKstrdupCall(FunctionCall fc) {
  fc.getTarget().getName() = "kstrdup"
}

from FunctionCall acq, LocalVariable v, Function enclosing
where isKstrdupCall(acq)
  and enclosing = acq.getEnclosingFunction()
  and v.getAnAssignedValue() = acq
  and count(ReturnStmt r | r.getEnclosingFunction() = enclosing) >
      count(FunctionCall rel |
        rel.getTarget().getName() = "kfree"
        and rel.getEnclosingFunction() = enclosing
        and rel.getAnArgument().(VariableAccess).getTarget() = v)
select acq,
  "kstrdup result assigned to '" + v.getName() +
  "' may leak: some return paths in '" + enclosing.getName() +
  "' lack a matching kfree."
