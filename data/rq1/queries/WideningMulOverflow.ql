/**
 * @name Widening integer overflow flowing into an allocation/copy size or wide size field (CWE-190/680)
 * @description An arithmetic operation (multiply, add, or left shift) is computed in a small
 *              (<=4 byte) integer type and its result is then widened to a >4 byte type, and that
 *              widened result is used as a DANGER SINK: the size argument of an allocation, the
 *              length argument of a memcpy/memset/copy_*_user, or stored into a wider size/len/
 *              offset/count/width-like field. In C the arithmetic is performed in the small operand
 *              type, so it can overflow/wrap *before* being widened, leading to an undersized
 *              allocation or out-of-bounds copy (the classic CWE-190 -> CWE-680 chain). Casting an
 *              operand to the wide type before the operation (`(u64)a * b`) avoids this and acts as a
 *              barrier. Models commits 9b458e8b (mtd diskonchip part size), 5a4510c7 (dm-unstripe
 *              offset/width).
 * @kind problem
 * @problem.severity warning
 * @security-severity 8.1
 * @precision medium
 * @id cpp/widening-overflow-into-size-sink
 * @tags security
 *       external/cwe/cwe-190
 *       external/cwe/cwe-680
 */

import cpp

/** Size (in bytes) of `e`'s own (unconverted) integral type, if it has one. */
pragma[inline]
int operandWidth(Expr e) { result = e.getType().getUnspecifiedType().(IntegralType).getSize() }

/** A binary arithmetic op (`*`, `+`, `<<`) computed in a small (<=4B) integer type but whose
 *  fully-converted (context) type is wider (>4B). */
class WideningArith extends BinaryOperation {
  WideningArith() {
    (this instanceof MulExpr or this instanceof AddExpr or this instanceof LShiftExpr) and
    this.getType().getUnspecifiedType().(IntegralType).getSize() <= 4 and
    this.getFullyConverted().getType().getUnspecifiedType().(IntegralType).getSize() > 4
  }

  /** The operand whose width drives the op type (the value side, not the shift amount). */
  Expr getValueOperand() {
    if this instanceof LShiftExpr
    then result = this.getLeftOperand()
    else result = this.getAnOperand()
  }

  /** Holds if the op is "guarded" by a cast: at least one value operand is already wide (>4B). */
  predicate isCastGuarded() { operandWidth(this.getValueOperand()) > 4 }
}

/** Holds if `e`'s subtree contains an access to variable/field `v`. */
pragma[inline]
predicate refersTo(Expr e, Variable v) {
  exists(VariableAccess va | va = e.getAChild*() and va.getTarget() = v)
}

/** Holds if `e`'s subtree contains the arithmetic op `arith`. */
pragma[inline]
predicate subtreeContains(Expr e, WideningArith arith) { arith = e.getAChild*() }

/** Holds if `arith`'s widened result reaches `e` (lexically, same function): either directly in
 *  `e`'s subtree, or via a wide local variable assigned from `arith`. */
pragma[inline]
predicate resultReaches(WideningArith arith, Expr e) {
  subtreeContains(e, arith)
  or
  exists(Variable v |
    v.getAnAssignedValue() = arith and
    v.getType().getUnspecifiedType().(IntegralType).getSize() > 4 and
    refersTo(e, v) and
    not v instanceof Field
  )
}

/** Function names whose *size/length* argument (at `sizeArgIndex`) is a danger sink. */
class SinkCall extends FunctionCall {
  int sizeArgIndex;

  SinkCall() {
    exists(string n | n = this.getTarget().getName() |
      n.regexpMatch("(?i)(__)?(kmalloc|kzalloc|kvmalloc|kvzalloc|vmalloc|vzalloc|kmalloc_node|" +
          "kzalloc_node|kvmalloc_node|devm_kmalloc|devm_kzalloc)") and
      sizeArgIndex = 0
      or
      n.regexpMatch("(?i)(krealloc|kmemdup|vmemdup_user|memdup_user|memdup_user_nul)") and
      sizeArgIndex = 1
      or
      n.regexpMatch("(?i)(memcpy|memmove|memset|copy_from_user|copy_to_user|__copy_from_user|" +
          "__copy_to_user|memcpy_fromio|memcpy_toio)") and
      sizeArgIndex = 2
    )
  }

  /** The size/length argument expression that must not overflow. */
  Expr getSizeArg() { result = this.getArgument(sizeArgIndex) }
}

/** A store into a wide (>4B) size/len/offset/count/width-like field (the field-store sink). */
class WideSizeFieldStore extends AssignExpr {
  Field field;

  WideSizeFieldStore() {
    exists(FieldAccess fa |
      fa = this.getLValue() and
      field = fa.getTarget() and
      field.getType().getUnspecifiedType().(IntegralType).getSize() > 4 and
      field.getName()
          .regexpMatch("(?i).*(size|len|length|offset|count|num|width|height|bytes|nbytes|" +
              "sectors?|blocks?|total|capacity|nr_).*")
    )
  }

  Field getField() { result = field }
}

/** Test / sample / tooling code: not shippable bugs. */
predicate inNonShippable(WideningArith arith) {
  arith.getFile().getRelativePath().regexpMatch("(?i).*(/test|_test|/kunit|/selftest|/tests/).*")
  or
  arith.getFile().getRelativePath().regexpMatch("^(scripts|tools|samples)/.*")
}

from WideningArith arith, Expr sinkLoc, string reason
where
  // barrier: an operand already widened -> arithmetic done in the wide type, no overflow
  not arith.isCastGuarded() and
  not inNonShippable(arith) and
  // the widened result must reach a danger sink
  (
    exists(SinkCall sc |
      sc.getEnclosingFunction() = arith.getEnclosingFunction() and
      resultReaches(arith, sc.getSizeArg()) and
      sinkLoc = sc and
      reason = "size/len argument of " + sc.getTarget().getName() + "()"
    )
    or
    exists(WideSizeFieldStore st |
      st.getRValue() = arith and
      sinkLoc = st and
      reason = "store into wide field '" + st.getField().getName() + "'"
    )
  )
select arith,
  arith.getLocation().getFile().getRelativePath() + ":" +
    arith.getLocation().getStartLine().toString() + " CWE-190/680: '" + arith.getOperator() +
    "' computed in " + arith.getType().getUnspecifiedType().toString() +
    " (<=4B), widened to " + arith.getFullyConverted().getType().getUnspecifiedType().toString() +
    " (>4B), then used as " + reason + "; cast an operand to the wide type before the op."
