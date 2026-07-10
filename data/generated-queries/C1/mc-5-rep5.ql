/**
 * @name Missing NULL check on allocator return value
 * @description Memory allocators in the kernel (kmalloc/kzalloc/kcalloc,
 *              devm_kmalloc/devm_kzalloc/devm_kcalloc/devm_kmemdup,
 *              vmalloc/kvmalloc, krealloc, kstrdup, ...) return NULL on
 *              failure.  Callers MUST guard the result against NULL
 *              before storing it long-term or using it.  When the
 *              returned pointer is stored into a local variable or
 *              struct field and that storage is never compared against
 *              NULL anywhere in the same function, an allocation
 *              failure leaves the pointer NULL, and any later
 *              dereference (in the same function or in callers that
 *              consume the same field) will crash (CWE-476, CWE-690).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-5
 */

import cpp

/* Kernel allocators that return NULL on failure. */
predicate isAllocApi(string n) {
  n = "kmalloc" or
  n = "kzalloc" or
  n = "kcalloc" or
  n = "kmalloc_array" or
  n = "krealloc" or
  n = "kmemdup" or
  n = "kstrdup" or
  n = "kstrndup" or
  n = "vmalloc" or
  n = "vzalloc" or
  n = "kvmalloc" or
  n = "kvzalloc" or
  n = "kvcalloc" or
  n = "kvmalloc_array" or
  n = "devm_kmalloc" or
  n = "devm_kzalloc" or
  n = "devm_kcalloc" or
  n = "devm_kmalloc_array" or
  n = "devm_kmemdup" or
  n = "devm_kstrdup"
}

/* The Declaration (local Variable or struct Field) that receives the
 * return value of an allocator call.  Covers declaration-with-
 * initializer and plain assignment to either a variable or a field. */
Declaration receiverOf(FunctionCall acq) {
  exists(Variable v |
    v.getInitializer().getExpr() = acq and result = v
  )
  or
  exists(AssignExpr a | a.getRValue() = acq |
    result = a.getLValue().(VariableAccess).getTarget() or
    result = a.getLValue().(FieldAccess).getTarget()
  )
}

/* An access expression on `d` (variable or field access). */
Expr accessOf(Declaration d) {
  result.(VariableAccess).getTarget() = d or
  result.(FieldAccess).getTarget() = d
}

/* Holds if function `f` contains any syntactic NULL-ish check on the
 * storage `d`:
 *   - `!d`  (NotExpr around an access to d)
 *   - `d == NULL` / `d != NULL` / `NULL == d` / `NULL != d`
 *   - `d` used directly as the condition of an `if` / `?:` /
 *     `&&` / `||` (truthiness check).
 * Any of these mean the developer considered the NULL case. */
predicate hasNullCheck(Function f, Declaration d) {
  exists(Expr acc |
    acc = accessOf(d) and
    acc.getEnclosingFunction() = f and
    (
      // !d
      exists(NotExpr ne | ne.getOperand() = acc)
      or
      // d == NULL  /  d != NULL  /  NULL == d  /  NULL != d
      exists(EqualityOperation eq | eq.getAnOperand() = acc)
      or
      // if (d) ...
      exists(IfStmt ifs | ifs.getCondition() = acc)
      or
      // d ? ... : ...
      exists(ConditionalExpr ce | ce.getCondition() = acc)
      or
      // d && ...  /  ... && d
      exists(LogicalAndExpr la | la.getAnOperand() = acc)
      or
      // d || ...  /  ... || d
      exists(LogicalOrExpr lo | lo.getAnOperand() = acc)
      or
      // while (d) / for(;d;)
      exists(WhileStmt ws | ws.getCondition() = acc)
      or
      exists(ForStmt fs | fs.getCondition() = acc)
    )
  )
}

from FunctionCall acq, Function f, Declaration d, string apiName
where
  apiName = acq.getTarget().getName() and
  isAllocApi(apiName) and
  f = acq.getEnclosingFunction() and
  d = receiverOf(acq) and
  not hasNullCheck(f, d)
select acq,
  "Call to " + apiName + " stores its result into '" + d.getName() +
    "' but '" + d.getName() +
    "' is never NULL-checked in '" + f.getName() +
    "' — possible NULL pointer dereference on allocation failure."
