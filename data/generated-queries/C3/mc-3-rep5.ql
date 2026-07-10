/**
 * @name C3 generated query for mc-3 / fix 6fc232db9e8c / rep5
 * @description Use-before-null-check on a pointer parameter: the pointer
 *              is dereferenced (member access or address-of-member) before
 *              a NULL check on the same parameter is executed. Detects the
 *              rfkill_register pattern from commit 6fc232db9e8c (CWE-476).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-3-rep5
 */

import cpp

/* A formal parameter whose declared type is a pointer. */
predicate isPointerParam(Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType
}

/* A dereference of parameter `p` inside function `f`, occurring at line `line`.
   Covers: member access via `p->m`, address-of-member via `&p->m`, and the
   explicit dereference `*p`. */
predicate derefOfParam(Function f, Parameter p, int line) {
  exists(VariableAccess va |
    va.getTarget() = p and
    va.getEnclosingFunction() = f and
    line = va.getLocation().getStartLine() and
    (
      /* p->field  or  &p->field */
      exists(PointerFieldAccess pfa | pfa.getQualifier() = va)
      or
      /* *p */
      exists(PointerDereferenceExpr pde | pde.getOperand() = va)
    )
  )
}

/* A NULL check on parameter `p` inside function `f`, occurring at line `line`.
   Covers: `!p`, `p == 0`, `p == NULL`, `0 == p`. */
predicate nullCheckOfParam(Function f, Parameter p, int line) {
  exists(VariableAccess va |
    va.getTarget() = p and
    va.getEnclosingFunction() = f and
    line = va.getLocation().getStartLine() and
    (
      /* `!p` */
      exists(NotExpr ne | ne.getOperand() = va)
      or
      /* `p == 0` / `p == NULL` (both directions) */
      exists(EqualityOperation eo |
        eo.getAnOperand() = va and
        eo.getAnOperand().getValue() = "0"
      )
    )
  )
}

/* True if the enclosing function name signals it's the post-fix shape
   (used to suppress matches in `*_fixed` reference variants). */
predicate isInFixedFunction(Function f) {
  f.getName().toLowerCase().matches("%fixed%")
}

from Function f, Parameter p, int derefLine, int checkLine
where
  isPointerParam(p) and
  p = f.getAParameter() and
  derefOfParam(f, p, derefLine) and
  nullCheckOfParam(f, p, checkLine) and
  derefLine < checkLine and
  not isInFixedFunction(f)
select f,
  "Pointer parameter '" + p.getName() + "' is dereferenced at line " +
  derefLine + " before being NULL-checked at line " + checkLine +
  " — possible NULL pointer dereference (CWE-476)."
