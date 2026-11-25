/**
 * @name Unvalidated array index from external data (CWE-129)
 * @description A non-constant index into a small fixed-size array, where the index is parsed
 *              from external/untrusted data (an endianness/unaligned buffer read, or a field of
 *              a hardware/protocol message struct), the index is not masked into range, its type
 *              can exceed the array bound, and no relational comparison in the enclosing function
 *              bounds it. Models the array-index-validation pattern from Linux commits
 *              a402532 (usb bdc), 129fa60 (btusb), 0fd56fa (wl1251), 95dffe3 (aiptek),
 *              304950a (brcmfmac).
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/unvalidated-array-index
 * @tags security
 *       external/cwe/cwe-129
 */

import cpp

/** A subscript into a fixed-size array (<=256 elements) whose count is statically known. */
class FixedArrayAccess extends ArrayExpr {
  int bound;

  FixedArrayAccess() {
    bound = this.getArrayBase().getType().getUnspecifiedType().(ArrayType).getArraySize() and
    bound <= 256
  }

  int getBound() { result = bound }
}

/** Holds if `e`'s subtree contains an access to variable/field `d`. (FieldAccess <: VariableAccess) */
pragma[inline]
predicate refersTo(Expr e, Variable d) {
  exists(VariableAccess va | va = e.getAChild*() and va.getTarget() = d)
}

/** The most specific variable/field that determines the index value: a variable/field accessed
 *  in `idx` that is NOT merely the struct pointer being dereferenced to reach a field. So for
 *  `result->id` the seed is field `id`, not the pointer `result`. */
pragma[inline]
predicate indexSeed(Expr idx, Variable d) {
  exists(VariableAccess va |
    va = idx.getAChild*() and
    va.getTarget() = d and
    not va = any(FieldAccess fa).getQualifier()
  )
}

/** Strong signal: `e` parses a value out of a raw buffer (endianness / unaligned read). */
pragma[inline]
predicate parsedFromBuffer(Expr e) {
  exists(FunctionCall fc | fc = e.getAChild*() |
    fc.getTarget().getName().regexpMatch("(?i)(le|be)(16|32|64)_to_cpup?|get_unaligned.*|ntoh.*")
  )
}

/** Weaker signal: `e` reads a field that looks like part of a hardware/firmware/protocol message. */
pragma[inline]
predicate readsProtocolField(Expr e) {
  exists(FieldAccess fa, Field f | fa = e.getAChild*() and f = fa.getTarget() |
    f.getName()
        .regexpMatch("(?i).*(resp|report|rsp|result|event|evt|hdr|header|desc|msg|cmd|frame|" +
            "packet|pkt|payload|completion|bsscfg|sco_num|macro|ifidx|^id$|_id$).*")
  )
}

/** Holds if `e` reads external/untrusted data (strong or protocol-field signal). */
pragma[inline]
predicate readsExternal(Expr e) { parsedFromBuffer(e) or readsProtocolField(e) }

/** Holds if the index value originates from external data, directly or via a local var. */
pragma[inline]
predicate externalIndex(Expr idx) {
  readsExternal(idx)
  or
  exists(Variable v | indexSeed(idx, v) and readsExternal(v.getAnAssignedValue()))
}

/** A masking constant `x & C` reachable from `idx` directly or via its variable. */
pragma[inline]
int maskConstant(Expr idx) {
  exists(BitwiseAndExpr a | a = idx.getAChild*() and result = a.getValue().toInt())
  or
  exists(BitwiseAndExpr a, Variable v |
    indexSeed(idx, v) and a = v.getAnAssignedValue().getAChild*() and result = a.getValue().toInt()
  )
}

/** Cheap proxy for "bounds-checked": some relational comparison in the same function
 *  references the index seed (the specific variable/field that determines the index). */
pragma[inline]
predicate isBoundsChecked(FixedArrayAccess ae, Expr idx) {
  exists(RelationalOperation rel, Variable d |
    indexSeed(idx, d) and
    refersTo(rel, d) and
    rel.getEnclosingFunction() = ae.getEnclosingFunction()
  )
}

/** KUnit / test / selftest code — not shippable bugs. */
predicate inTestCode(FixedArrayAccess ae) {
  ae.getFile().getRelativePath().regexpMatch("(?i).*(/test|_test|/kunit|/selftest|/tests/).*")
  or
  ae.getEnclosingFunction().getName().regexpMatch("(?i).*_test.*")
  or
  ae.getArrayBase().toString().regexpMatch("(?i).*_test_.*")
}

/** Arrays of locks are designed to be hash-indexed; not the CWE-129 target. */
predicate isLockArray(FixedArrayAccess ae) {
  ae.getArrayBase()
      .getType()
      .getUnspecifiedType()
      .(ArrayType)
      .getBaseType()
      .getUnspecifiedType()
      .(Struct)
      .getName()
      .regexpMatch("(?i).*(mutex|spinlock|rwlock|semaphore|rwsem).*")
}

from FixedArrayAccess ae, Expr idx, int bound
where
  idx = ae.getArrayOffset() and
  bound = ae.getBound() and
  not idx.isConstant() and
  externalIndex(idx) and
  not exists(int c | c = maskConstant(idx) and c < bound) and
  // index's integral type cannot exceed the bound (e.g. u8 into an array of >=256) -> safe
  not exists(IntegralType t | t = idx.getType().getUnspecifiedType() and t.getSize() = 1 |
    t.isUnsigned() and bound >= 256
    or
    not t.isUnsigned() and bound >= 128
  ) and
  not isBoundsChecked(ae, idx) and
  not inTestCode(ae) and
  not isLockArray(ae) and
  // non-shippable build/host tooling
  not ae.getFile().getRelativePath().regexpMatch("^(scripts|tools|samples)/.*") and
  // crypto S-box / permutation tables: large fixed lookup tables indexed by masked bytes (safe by construction)
  not (ae.getFile().getRelativePath().matches("crypto/%") and bound >= 64)
select ae,
  ae.getLocation().getFile().getRelativePath() + ":" + ae.getLocation().getStartLine().toString() +
    " CWE-129: external index into '" + ae.getArrayBase().toString() + "[" + bound.toString() +
    "]' with no bounds check."
