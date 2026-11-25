/**
 * @name Unbounded accumulating copy into a fixed-size buffer (CWE-120/787)
 * @description A write into a fixed-size buffer via an accumulating copy primitive
 *              (memcpy at an offset, skb_put / skb_put_u8 / skb_put_data, or
 *              strcat / strncat / strlcat) where the write either sits inside a loop
 *              or the same destination is written by more than one such primitive,
 *              and the enclosing function performs no remaining-space check
 *              (a relational comparison on the buffer / length / offset, a
 *              skb_tailroom() query, or a size-aware safe API). Repeated/looped
 *              appends can then run past the end of the buffer. Models Linux commits
 *              1214bf28 (gb-beagleplay), 30fe3f5f (pn533), 3c34471c (dell-wmi-sysman),
 *              5ec1d1e9 (tracing).
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/unbounded-accumulating-copy
 * @tags security
 *       external/cwe/cwe-120
 *       external/cwe/cwe-787
 */

import cpp

/** A call to an accumulating copy primitive: appends/grows into a destination buffer. */
class AccumWrite extends FunctionCall {
  AccumWrite() {
    this.getTarget().getName().regexpMatch(
      "memcpy|__memcpy|memmove|" +
      "skb_put|skb_put_u8|skb_put_data|skb_put_zero|" +
      "strcat|strncat|strlcat|__strcat|__strncat")
  }
}

/** Holds if `e`'s subtree contains an access to variable/field `d`. (FieldAccess <: VariableAccess) */
pragma[inline]
predicate refersTo(Expr e, Variable d) {
  exists(VariableAccess va | va = e.getAChild*() and va.getTarget() = d)
}

/**
 * The "destination seed": the most specific variable/field naming the buffer this write
 * targets. For memcpy/strcat etc. the destination is argument 0. We take the field/variable
 * accessed in arg0 that is NOT merely a struct pointer dereferenced to reach a field, so for
 * `dev->recv_skb` the seed is field `recv_skb`, and for `bg->rx_buffer + len` the seed is
 * field `rx_buffer`.
 */
pragma[inline]
predicate destSeed(AccumWrite w, Variable d) {
  exists(VariableAccess va |
    va = w.getArgument(0).getAChild*() and
    va.getTarget() = d and
    not va = any(FieldAccess fa).getQualifier()
  )
}

/** Holds if the write is lexically inside a loop body (in the body, not the condition). */
pragma[inline]
predicate inLoop(AccumWrite w) {
  exists(Loop l | w.getEnclosingStmt() = l.getStmt().getAChild*())
}

/**
 * Holds if the destination of `w` is `base + offset` style pointer arithmetic where the
 * offset is a non-constant value (an accumulating write position, e.g. `buf + len`).
 * This is the single-statement accumulation signal (a memcpy at a running offset).
 */
pragma[inline]
predicate accumulatingOffset(AccumWrite w) {
  exists(PointerAddExpr add, Expr off |
    add = w.getArgument(0) and
    off = add.getAnOperand() and
    off.getType().getUnspecifiedType() instanceof IntegralType and
    not off.isConstant()
  )
}

/**
 * Holds if the same destination buffer is written by more than one accumulating
 * primitive in the same function (lexical accumulation, e.g. repeated strcat()).
 */
pragma[inline]
predicate repeatedDest(AccumWrite w) {
  exists(AccumWrite w2, Variable d |
    w2 != w and
    w2.getEnclosingFunction() = w.getEnclosingFunction() and
    destSeed(w, d) and
    destSeed(w2, d)
  )
}

/**
 * Holds if `rel` is merely the controlling condition of a loop (e.g. `i < count`),
 * which is iteration bookkeeping and NOT a remaining-space check.
 */
pragma[inline]
predicate isLoopCondition(RelationalOperation rel) {
  exists(Loop l | l.getCondition() = rel.getParent*())
}

/**
 * Cheap proxy for "remaining-space checked": a relational comparison (that is NOT just a
 * loop counter) in the same function that genuinely relates capacity to a write length.
 * Mirrors `if (count > sizeof(buf) - len)`, `if (dest_len + n >= SIZE)`,
 * `if (skb_tailroom(skb) < len)`. Signals: the comparison references the destination
 * buffer, or it involves a sizeof / a length subtraction / a strlen length computation.
 */
pragma[inline]
predicate hasSpaceCheck(AccumWrite w) {
  exists(RelationalOperation rel |
    rel.getEnclosingFunction() = w.getEnclosingFunction() and
    not isLoopCondition(rel)
  |
    exists(Variable d | destSeed(w, d) and refersTo(rel, d))
    or
    rel.getAChild*() instanceof SizeofOperator
    or
    rel.getAChild*() instanceof SubExpr
    or
    exists(FunctionCall fc | fc = rel.getAChild*() and fc.getTarget().getName() = "strlen")
  )
}

/** Holds if the function queries the skb tailroom (the skb-specific space check). */
pragma[inline]
predicate hasTailroomCheck(AccumWrite w) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = w.getEnclosingFunction() and
    fc.getTarget().getName().regexpMatch("skb_tailroom|skb_availroom|skb_trim")
  )
}

/**
 * Holds if the function uses a size-aware safe API writing the same destination buffer
 * (snprintf/scnprintf/strscpy/strlcpy), i.e. the accumulation is actually bounded.
 */
pragma[inline]
predicate usesSafeApi(AccumWrite w) {
  exists(FunctionCall fc, Variable d |
    fc.getEnclosingFunction() = w.getEnclosingFunction() and
    fc.getTarget().getName().regexpMatch(
      "snprintf|scnprintf|vsnprintf|strscpy|strscpy_pad|strlcpy|__sprintf_chk") and
    destSeed(w, d) and
    refersTo(fc.getArgument(0), d)
  )
}

/** KUnit / test / selftest code, and build-time host tooling — not shippable kernel bugs. */
predicate inTestCode(AccumWrite w) {
  w.getFile().getRelativePath().regexpMatch("(?i).*(/test|_test|/kunit|/selftest|/tests/).*")
  or
  w.getEnclosingFunction().getName().regexpMatch("(?i).*_test.*")
  or
  w.getFile().getRelativePath().regexpMatch("^(scripts|tools|samples|usr)/.*")
}

from AccumWrite w
where
  (inLoop(w) or repeatedDest(w) or accumulatingOffset(w)) and
  not hasSpaceCheck(w) and
  not hasTailroomCheck(w) and
  not usesSafeApi(w) and
  not inTestCode(w)
select w,
  w.getLocation().getFile().getRelativePath() + ":" + w.getLocation().getStartLine().toString() +
    " CWE-120: accumulating '" + w.getTarget().getName() +
    "' into fixed buffer with no remaining-space check."
