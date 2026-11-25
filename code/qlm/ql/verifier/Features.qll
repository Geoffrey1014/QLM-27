/**
 * Structural features for the per-pattern seed<->PoC fidelity check.
 *
 * A feature is counted inside one *subject* function, identified by the file it is
 * written in and its name, so that a seed slice and a PoC can share one database even
 * when they define functions with the same name.
 *
 * Counting rule: a statement counts when it is written literally in the function, or is
 * the outermost statement produced by a macro invocation written there. Statements
 * nested inside a macro expansion, compiler-generated statements and `do { } while (0)`
 * wrappers are not counted. This keeps counts independent of how stub macros in a seed
 * slice or PoC happen to be defined.
 */

import cpp

/**
 * Parameters supplied by the driver (`verifier.py`) as CSV files:
 *  - subject(file basename, function name, role), role in seed_buggy / seed_fixed /
 *    poc_buggy / poc_fixed;
 *  - api(kind, name): seed-derived API names, kind in acquire / release / release_patch /
 *    producer / producer_var.
 */
external predicate subject(string file, string fn, string role);

external predicate api(string kind, string name);

/** `e` lies in the body of function `fn` as written in `file`. */
predicate inSubject(Element e, string file, string fn) {
  subject(file, fn, _) and
  e.getLocation().getFile().getBaseName() = file and
  (
    fn = e.(Stmt).getEnclosingFunction().getName() or
    fn = e.(Expr).getEnclosingFunction().getName()
  )
}

/** Line span of the body of `fn` in `file`. */
predicate subjectSpan(string file, string fn, int start, int end) {
  exists(BlockStmt b |
    inSubject(b, file, fn) and
    not exists(b.getParentStmt()) and
    start = b.getLocation().getStartLine() and
    end = b.getLocation().getEndLine()
  )
}

predicate isDoWhileZero(DoStmt d) { d.getCondition().getValue() = "0" }

predicate counted(Stmt s) {
  not s.isInMacroExpansion() and
  not s.isCompilerGenerated() and
  not isDoWhileZero(s)
}

/** Occurrences of `name` in the subject: literal calls plus top-level macro invocations. */
int nameUses(string file, string fn, string name) {
  subject(file, fn, _) and
  name = any(string n | apiLike(n)) and
  result =
    count(FunctionCall c |
        inSubject(c, file, fn) and not c.isInMacroExpansion() and c.getTarget().getName() = name
      ) +
      count(MacroInvocation mi, int s, int e |
        subjectSpan(file, fn, s, e) and
        mi.getLocation().getFile().getBaseName() = file and
        mi.getLocation().getStartLine() in [s .. e] and
        not exists(mi.getParentInvocation()) and
        mi.getMacroName() = name
      )
}

/** Every name any feature asks about; bounds `nameUses`. */
predicate apiLike(string n) {
  api(_, n) or
  busyWait(n) or
  sleepCall(n) or
  atomicContextEnter(n) or
  n = ["GFP_ATOMIC", "GFP_KERNEL", "GFP_NOWAIT"]
}

int countNames(string file, string fn, string kind) {
  subject(file, fn, _) and
  kind = ["acquire", "release"] and
  result = sum(string n | api(kind, n) | nameUses(file, fn, n))
}

/* ---------------------------------------------------------------- common */
int nGoto(string file, string fn) {
  subject(file, fn, _) and result = count(GotoStmt s | inSubject(s, file, fn) and counted(s))
}

int nReturn(string file, string fn) {
  subject(file, fn, _) and result = count(ReturnStmt s | inSubject(s, file, fn) and counted(s))
}

int nIf(string file, string fn) {
  subject(file, fn, _) and result = count(IfStmt s | inSubject(s, file, fn) and counted(s))
}

int nLoop(string file, string fn) {
  subject(file, fn, _) and result = count(Loop s | inSubject(s, file, fn) and counted(s))
}

int nSwitch(string file, string fn) {
  subject(file, fn, _) and result = count(SwitchStmt s | inSubject(s, file, fn) and counted(s))
}

/* -------------------------------------------------------- four-features */
/** A literal call in the subject to an API of `kind`. */
predicate apiCall(string file, string fn, string kind, FunctionCall c) {
  inSubject(c, file, fn) and not c.isInMacroExpansion() and api(kind, c.getTarget().getName())
}

/**
 * Returns reached (in line order) after an acquire with none of the patch's releases in
 * between. Fixes that move a release before an early return, turn `return` into
 * `goto err`, or add a release on an error branch all change this count.
 */
int nLeakyExit(string file, string fn) {
  subject(file, fn, _) and
  result =
    count(ReturnStmt r |
      inSubject(r, file, fn) and
      counted(r) and
      exists(FunctionCall a, int la, int lr |
        apiCall(file, fn, "acquire", a) and
        la = a.getLocation().getStartLine() and
        lr = r.getLocation().getStartLine() and
        la < lr and
        not exists(FunctionCall rel |
          apiCall(file, fn, "release_patch", rel) and
          rel.getLocation().getStartLine() in [la .. lr]
        )
      )
    )
}

/* ------------------------------------------------------- missing-check */
/**
 * A producer is a call (api "producer") or a variable/field name (api "producer_var")
 * whose value the fix starts to check. `value` is the expression carrying it.
 */
predicate producerValue(string file, string fn, Expr value) {
  inSubject(value, file, fn) and
  (
    exists(FunctionCall c | c = value and not c.isInMacroExpansion() |
      api("producer", c.getTarget().getName())
    )
    or
    api("producer_var", value.(VariableAccess).getTarget().getName())
  )
}

/** The variable a producer call's result is stored into, if any. */
Variable storedInto(FunctionCall c) {
  exists(AssignExpr a | a.getRValue() = c and result = a.getLValue().(VariableAccess).getTarget())
  or
  exists(Initializer i | i.getExpr() = c and result = i.getDeclaration())
}

/** `v` is tested by a condition of `fn` (if / loop / ?: / logical operand), anywhere in the subject. */
predicate testedIn(string file, string fn, Variable v) {
  exists(Expr cond, VariableAccess va |
    inSubject(cond, file, fn) and
    (
      cond = any(IfStmt s).getCondition() or
      cond = any(Loop l).getCondition() or
      cond = any(ConditionalExpr ce).getCondition()
    ) and
    va.getTarget() = v and
    va.getParent*() = cond
  )
}

predicate callTested(string file, string fn, FunctionCall c) {
  inSubject(c, file, fn) and
  exists(Expr cond |
    (
      cond = any(IfStmt s).getCondition() or
      cond = any(Loop l).getCondition() or
      cond = any(ConditionalExpr ce).getCondition()
    ) and
    c.getParent*() = cond
  )
  or
  testedIn(file, fn, storedInto(c))
}

/** Producer calls whose result is never tested in the subject. */
int nUncheckedCalls(string file, string fn) {
  subject(file, fn, _) and
  result =
    count(FunctionCall c |
      producerValue(file, fn, c) and
      not callTested(file, fn, c)
    )
}

/** Producer variables dereferenced at least once on a line before their first test. */
int nDerefBeforeCheck(string file, string fn) {
  subject(file, fn, _) and
  result =
    count(string name |
      api("producer_var", name) and
      exists(VariableAccess deref |
        producerValue(file, fn, deref) and
        deref.getTarget().getName() = name and
        (
          deref = any(PointerFieldAccess pfa).getQualifier() or
          deref = any(PointerDereferenceExpr pde).getOperand() or
          deref = any(ArrayExpr ae).getArrayBase()
        ) and
        not exists(VariableAccess t, Expr cond |
          t.getTarget() = deref.getTarget() and
          inSubject(t, file, fn) and
          cond = any(IfStmt s).getCondition() and
          t.getParent*() = cond and
          t.getLocation().getStartLine() < deref.getLocation().getStartLine()
        )
      )
    )
}

/* ---------------------------------------------------------- delay-gfp */
predicate busyWait(string n) { n = ["mdelay", "udelay", "ndelay"] }

predicate sleepCall(string n) {
  n = ["msleep", "msleep_interruptible", "ssleep", "usleep_range", "fsleep"]
}

predicate atomicContextEnter(string n) {
  (n = any(Function f).getName() or n = any(Macro m).getName()) and
  atomicContextEnterName(n)
}

bindingset[n]
predicate atomicContextEnterName(string n) {
  n.matches("spin_lock%") or
  n.matches("raw_spin_lock%") or
  n.matches("read_lock%") or
  n.matches("write_lock%") or
  n = ["local_irq_disable", "local_irq_save", "preempt_disable", "rcu_read_lock", "local_bh_disable"]
}

int sumUses(string file, string fn, string group) {
  subject(file, fn, _) and
  (
    group = "busy" and result = sum(string n | busyWait(n) | nameUses(file, fn, n))
    or
    group = "sleep" and result = sum(string n | sleepCall(n) | nameUses(file, fn, n))
    or
    group = "atomic" and result = sum(string n | atomicContextEnter(n) | nameUses(file, fn, n))
  )
}

/* ------------------------------------------------------- error-return */
/** A local variable or parameter returned by `return v;` in the subject. */
predicate returnVar(string file, string fn, Variable v) {
  exists(ReturnStmt r |
    inSubject(r, file, fn) and
    r.getExpr().(VariableAccess).getTarget() = v and
    (v instanceof LocalVariable or v instanceof Parameter)
  )
}

/** An if whose then-branch leaves the function (goto, or return of the return variable). */
predicate exitBranch(string file, string fn, IfStmt i) {
  inSubject(i, file, fn) and
  counted(i) and
  exists(Stmt exit | exit.getParentStmt*() = i.getThen() and counted(exit) |
    exit instanceof GotoStmt
    or
    exists(Variable v |
      returnVar(file, fn, v) and exit.(ReturnStmt).getExpr().(VariableAccess).getTarget() = v
    )
  )
}

/** Exit branches that leave without setting any return variable. */
predicate unsetExit(string file, string fn, IfStmt i) {
  exitBranch(file, fn, i) and
  exists(Variable v | returnVar(file, fn, v)) and
  not exists(Variable v | returnVar(file, fn, v) |
    exists(Assignment a |
      a.getLValue().(VariableAccess).getTarget() = v and
      (a.getEnclosingStmt().getParentStmt*() = i.getThen() or a.getParent*() = i.getCondition())
    )
    or
    // `if (ret) goto out;` already carries the error
    exists(VariableAccess va | va.getTarget() = v and va.getParent*() = i.getCondition())
  )
}

int nExitBranch(string file, string fn) {
  subject(file, fn, _) and result = count(IfStmt i | exitBranch(file, fn, i))
}

int nUnsetExit(string file, string fn) {
  subject(file, fn, _) and result = count(IfStmt i | unsetExit(file, fn, i))
}

/* -------------------------------------------------------------- table */
/** All features of one subject function, as (dimension, count). */
predicate feature(string file, string fn, string dim, int n) {
  subject(file, fn, _) and
  (
    dim = "cf.goto" and n = nGoto(file, fn)
    or
    dim = "cf.return" and n = nReturn(file, fn)
    or
    dim = "cf.if" and n = nIf(file, fn)
    or
    dim = "cf.loop" and n = nLoop(file, fn)
    or
    dim = "cf.switch" and n = nSwitch(file, fn)
    or
    dim = "ff.acquire" and n = countNames(file, fn, "acquire")
    or
    dim = "ff.release" and n = countNames(file, fn, "release")
    or
    dim = "ff.leaky_exit" and n = nLeakyExit(file, fn)
    or
    dim = "mc.producer" and n = count(Expr e | producerValue(file, fn, e) and e instanceof FunctionCall)
    or
    dim = "mc.unchecked" and n = nUncheckedCalls(file, fn)
    or
    dim = "mc.deref_before_check" and n = nDerefBeforeCheck(file, fn)
    or
    dim = "dg.busy_wait" and n = sumUses(file, fn, "busy")
    or
    dim = "dg.sleep" and n = sumUses(file, fn, "sleep")
    or
    dim = "dg.gfp_atomic" and n = nameUses(file, fn, "GFP_ATOMIC")
    or
    dim = "dg.gfp_kernel" and n = nameUses(file, fn, "GFP_KERNEL")
    or
    dim = "dg.atomic_ctx" and n = sumUses(file, fn, "atomic")
    or
    dim = "er.exit_branch" and n = nExitBranch(file, fn)
    or
    dim = "er.unset_exit" and n = nUnsetExit(file, fn)
  )
}
