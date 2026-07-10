/**
 * @name Missing NULL check after allocation
 * @description Result of an allocation call (kzalloc/kmalloc/etc.) is
 *              dereferenced without a prior NULL check on the returned pointer.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-null-check-after-alloc-mc2-rep3
 * @tags reliability
 *       security
 *       external/cwe/cwe-476
 */

import cpp

predicate isAllocReturningCall(FunctionCall fc) {
  fc.getTarget().getName() =
    ["kzalloc", "kmalloc", "kcalloc", "kmalloc_array", "vmalloc", "vzalloc",
     "kzalloc_node", "kmalloc_node"]
}

from FunctionCall alloc, Expr deref, Function f
where
  isAllocReturningCall(alloc) and
  f = alloc.getEnclosingFunction() and
  deref.getEnclosingFunction() = f and
  deref.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  (
    // Local-variable case: v was assigned the result of alloc,
    // then dereferenced without a NULL check.
    exists(Variable v |
      (
        v.getInitializer().getExpr() = alloc
        or
        exists(AssignExpr ae |
          ae.getRValue() = alloc and
          ae.getLValue().(VariableAccess).getTarget() = v
        )
      ) and
      (
        exists(PointerFieldAccess pfa |
          pfa = deref and pfa.getQualifier().(VariableAccess).getTarget() = v
        )
        or
        exists(PointerDereferenceExpr pde |
          pde = deref and pde.getOperand().(VariableAccess).getTarget() = v
        )
      ) and
      not exists(IfStmt ifs |
        ifs.getEnclosingFunction() = f and
        ifs.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
        ifs.getLocation().getStartLine() < deref.getLocation().getStartLine() and
        (
          ifs.getCondition().(NotExpr).getOperand().(VariableAccess).getTarget() = v
          or
          ifs.getCondition().(VariableAccess).getTarget() = v
          or
          exists(EqualityOperation eq |
            eq = ifs.getCondition() and
            eq.getAnOperand().(VariableAccess).getTarget() = v
          )
        )
      )
    )
    or
    // Field-assignment case: obj->field = kzalloc(...); obj->field->x = ...
    exists(Field fld, AssignExpr ae |
      ae.getRValue() = alloc and
      ae.getLValue().(FieldAccess).getTarget() = fld and
      exists(FieldAccess qual |
        qual = deref.(PointerFieldAccess).getQualifier() and
        qual.getTarget() = fld
      ) and
      not exists(IfStmt ifs |
        ifs.getEnclosingFunction() = f and
        ifs.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
        ifs.getLocation().getStartLine() < deref.getLocation().getStartLine() and
        (
          ifs.getCondition().(NotExpr).getOperand().(FieldAccess).getTarget() = fld
          or
          ifs.getCondition().(FieldAccess).getTarget() = fld
          or
          exists(EqualityOperation eq |
            eq = ifs.getCondition() and
            eq.getAnOperand().(FieldAccess).getTarget() = fld
          )
        )
      )
    )
  )
select alloc,
  "Result of allocation is dereferenced at $@ without a prior NULL check (CWE-476).",
  deref, deref.toString()
