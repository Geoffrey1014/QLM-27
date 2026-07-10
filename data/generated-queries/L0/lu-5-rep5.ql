/**
 * @name Missing kfree after kstrdup (four-features-Lu / lu-5 rep5, L0)
 * @description Detects functions where kstrdup allocates a string into a local variable
 *              but there is no kfree call on that same variable in the same function
 *              (an intra-procedural leak of the allocated buffer).
 * @kind problem
 * @problem.severity warning
 * @id cpp/lu-5-rep5-l0/missing-kfree-after-kstrdup
 */

import cpp

predicate isAllocByKstrdup(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "kstrdup" and
  exists(VariableAccess va | va = v.getAnAccess() and
    (
      exists(AssignExpr ae | ae.getRValue() = fc and ae.getLValue() = va)
      or
      exists(Initializer ini | ini.getExpr() = fc and ini.getDeclaration() = v)
    )
  )
}

from Function f, FunctionCall alloc, Variable v
where
  isAllocByKstrdup(alloc, v) and
  alloc.getEnclosingFunction() = f and
  not exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    fc.getTarget().getName() = "kfree" and
    fc.getAnArgument().(VariableAccess).getTarget() = v
  )
select alloc, "kstrdup result stored in $@ leaks: no kfree in the same function.", v, v.getName()
