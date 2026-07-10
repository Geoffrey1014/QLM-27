/**
 * @name  rq3-c2-mc-2-rep4
 * @id    cpp/rq3/c2/mc-2-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing NULL check after kzalloc allocation.
 */
import cpp
import semmle.code.cpp.controlflow.Guards

/** Holds if `fc` is a call to an allocation function whose result must be NULL-checked. */
predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().hasName("kzalloc") or
  fc.getTarget().hasName("kmalloc") or
  fc.getTarget().hasName("kcalloc") or
  fc.getTarget().hasName("kzalloc_node") or
  fc.getTarget().hasName("kmalloc_node")
}

/** Holds if the result of `fc` is stored into the variable referred to by `va` (via assignment). */
predicate assignsResultTo(FunctionCall fc, VariableAccess va) {
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = va
  )
}

/** Holds if `va2` is a later access to the same variable accessed by `va1`,
 *  reachable in control flow. */
predicate laterAccessOfSameVar(VariableAccess va1, VariableAccess va2) {
  va1.getTarget() = va2.getTarget() and
  va1 != va2 and
  va1.getASuccessor+() = va2
}

/** Holds if there is some NULL/non-NULL check on the variable accessed by `va`
 *  (any access to the same variable participates in a guard comparing it with 0/NULL). */
predicate hasNullCheck(VariableAccess va) {
  exists(VariableAccess vchk, EqualityOperation eq |
    vchk.getTarget() = va.getTarget() and
    eq.getAnOperand() = vchk and
    eq.getAnOperand().getValue() = "0"
  )
  or
  exists(VariableAccess vchk, GuardCondition gc |
    vchk.getTarget() = va.getTarget() and
    (gc = vchk or gc.(UnaryLogicalOperation).getOperand() = vchk)
  )
}

from FunctionCall fc, VariableAccess va
where
  isAllocCall(fc) and
  assignsResultTo(fc, va) and
  not hasNullCheck(va)
select fc, "Missing NULL check after allocation; result assigned to $@ is used without verification.", va, va.getTarget().getName()
