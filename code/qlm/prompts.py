"""Prompt templates for cells C0-C3 (the stages are described in code/prompts/*.md).

So that code can check each step:
  * PoCs name their mirror functions exactly `<fn>_buggy` / `<fn>_fixed`, and C3 variants
    `<fn>_tpN` / `<fn>_tnN` / `<fn>_fpN`;
  * the PoC prompt shows the verbatim buggy and fixed functions and states which counts the
    fidelity check compares;
  * C3 plans carry a machine-checkable `expect` per predicate next to the free-text
    `expected_on_poc`, and `test_query` is only the from-where-select part.
Placeholders are written {name} and filled with str.format; literal braces are doubled.
"""

# ---------------------------------------------------------------- shared (C0 preamble)
QUERY_PREAMBLE = """\
You are a senior Linux-kernel static-analysis engineer. You write CodeQL queries that
detect bug PATTERNS (not single-bug regressions) across the entire mainline kernel
source.

Working assumptions about the CodeQL DB you target:
- language: cpp
- built from a mainline-ish Linux source tree with KCFLAGS='-Dasm=__asm__'
- DB version: CodeQL 2.25.6 (`codeql/cpp-all` stdlib)

Output discipline:
- When asked for a `.ql` file, output ONLY the file body. No prose. No code fences.
- Every `.ql` must start with a doc comment containing @name, @description, @kind,
  @problem.severity, @id (use kind=problem unless the task specifically asks for
  path-problem).
- Imports: at minimum `import cpp`. Add any `import semmle.code.cpp.*` you need.
- No `.qll` files. No external library imports beyond `import cpp` + the cpp stdlib.
- Single `from-where-select`. Aim for <=200 LOC total.
- Predicates inside the same file are FINE; multiple files are NOT.

Pattern-generalization guidance:
- The provided patch is one INSTANCE of a class of bugs. Your query must find
  OTHER instances across the kernel - not just this one commit.
- Generalize the acquire/release pair where applicable (e.g. of_parse_phandle has
  a whole family of of_* siblings; spin_lock pairs with spin_unlock variants).
- Avoid hard-coding file names, line numbers, or specific identifiers from the
  patched file unless they are the API name itself.

You may use any of the standard cpp stdlib modules:
- `semmle.code.cpp.controlflow.ControlFlowGraph`
- `semmle.code.cpp.dataflow.DataFlow` / `DataFlow2`
- `semmle.code.cpp.dataflow.TaintTracking`
- `semmle.code.cpp.controlflow.Guards`
- `semmle.code.cpp.controlflow.SSA`"""

# ---------------------------------------------------------------- C0 (mono, no PoC)
KNIGHTER_CHECKER = """\
Bug-fix commit you are reverse-engineering into a checker:

== commit sha ==
{sha}

== commit subject ==
{subject}

== full commit message ==
{message}

== patch diff (this is the entire input - there is no separate "plan" turn) ==
{patch}

== task ==
Write ONE CodeQL .ql file (<=200 LOC) that detects the BUG PATTERN this commit
fixes, across the whole Linux kernel CodeQL database. The query should fire on
the buggy version of `{c_file}` (and on analogous bugs in other files), and stay
silent on the fixed version.

Constraints:
  - single from-where-select clause
  - imports: `import cpp` plus any stdlib modules you need
  - top of file: @kind problem, @id (use form `cpp/<short-slug>`), @name,
    @description, @problem.severity
  - generalize beyond the single API in the patch where the pattern obviously
    has siblings (e.g. of_parse_phandle -> of_* node-acquiring family)
  - do NOT hard-code the patched filename or line numbers

Output ONLY the .ql file body. No markdown fences. No commentary."""

COMPILE_REPAIR = """\
The CodeQL query below failed to compile.

== current .ql ==
{query}

== `codeql query compile` stderr ==
{stderr}

== task ==
Produce a corrected .ql file body. Fix ONLY what the diagnostic complains about,
and keep the original detection logic intact unless the diagnostic forces a
structural change. Output ONLY the .ql file body. No commentary, no fences."""

# ---------------------------------------------------------------- features (C2, C3)
FEATURES_SYSTEM = """\
You are analyzing a Linux kernel bug-fix commit for a CodeQL query generator.
The pattern under study is {pattern}. Use the QLM four-features schema:
target_api / post_operation / critical_variable / path_conditions.
For patterns that are not resource lifecycles, read the schema generically: target_api is
the operation at fault (e.g. the unchecked call, the busy-wait or GFP flag, the failing
call whose error is dropped), post_operation is what the fix adds or changes, and
path_conditions are the paths on which the bug manifests."""

FEATURES_USER = """\
Commit:        {sha}
Subject:       {subject}
Affected file: {c_file}

Buggy version of the touched function(s) (fix^):
{buggy_fn}

Fixed version:
{fixed_fn}

Patch (unified diff):
{patch}

Task: emit ONE JSON document with keys
  {{target_api, post_operation, critical_variable, path_conditions,
   fits_pattern, bug_type, cwe}}
Apply the 4-question fit test. If fits_pattern=false, set bug_type to a
human description. Output ONLY the JSON."""

# ---------------------------------------------------------------- PoC (C1, C3)
POC_SYSTEM = """\
You are writing a minimal, self-contained C proof-of-concept that demonstrates
the bug fixed by the given commit. The PoC is compiled with `gcc -std=gnu11 -O0 -w -c`
into a CodeQL mini-database and used as the oracle for a CodeQL detector.

Hard requirements (NON-NEGOTIABLE):
  R1. Define `{fn}_buggy` and `{fn}_fixed` with identical parameter lists.
      `{fn}_buggy` contains the bug the patch removes; `{fn}_fixed` the fixed code.
  R2. `{fn}_buggy` must mirror the control flow of the buggy function: the same
      number of goto, return, if, loop and switch statements, and the same pattern
      features. `{fn}_fixed` must carry the fix the same way the fixed function does.
      A deterministic structural fidelity check compares these counts.
  R3. Stub kernel APIs and types with extern prototypes or declarations; no kernel
      headers. Allowed includes: <stddef.h>, <stdint.h>, <stdbool.h>, <stdlib.h>, <stdio.h>.
  R4. Must compile cleanly. Provide a trivial `int main(void)`.
{variants}
Output ONLY the C source. No markdown, no commentary."""

POC_VARIANTS_C3 = """\
  R5. Also define 3-5 variants that the detector should generalize to:
      `{fn}_tp1`..`{fn}_tp3` (other buggy shapes), `{fn}_tn1`..`{fn}_tn3` (other fixed
      shapes), `{fn}_fp1`..`{fn}_fp3` (look-alike safe shapes). No other function name
      may end in `_buggy` or `_fixed`.
"""

POC_USER = """\
Commit subject:  {subject}
Affected file:   {c_file}
Pattern:         {pattern}
{features}
--- PATCH ---
{patch}

--- BUGGY VERSION OF THE AFFECTED FUNCTION(S) ---
{buggy_fn}

--- FIXED VERSION OF THE AFFECTED FUNCTION(S) ---
{fixed_fn}"""

POC_REGEN = """\

--- PREVIOUS POC (failed) ---
{prev}

--- WHY IT FAILED ---
{why}

Regenerate honoring the failed dimension(s). Keep the `{fn}_buggy` / `{fn}_fixed` names."""

# ---------------------------------------------------------------- C1 (mono + PoC)
MONO_POC_SYSTEM = """\
You write ONE monolithic CodeQL query (CodeQL CLI 2.25.6, language cpp) that
detects the bug pattern shown by the patch and the POC. Output ONLY the .ql
body - no markdown fences, no commentary, no extra files.

Hard requirements:
  Q1. <=200 LOC, single `from - where - select`.
  Q2. The .ql must compile cleanly under `codeql query compile`.
  Q3. When run on the POC mini-DB it MUST report a result whose location is
      inside the function whose name ends with `_buggy`, and MUST NOT report
      any result inside the function whose name ends with `_fixed`.
  Q4. Standard query header (@name, @kind problem, @problem.severity warning,
      @id qlm/c1-<seed_id>) is mandatory.
  Q5. Use only library imports that ship with cpp-all (e.g., `import cpp`).
  Q6. Do NOT hard-code file paths, function names containing `_buggy` /
      `_fixed`, or any artifact of the POC scaffolding. The query must be
      generic over the bug pattern - it has to work later on the full Linux
      DB, not just this POC."""

MONO_POC_USER = """\
Patch:
{patch}

POC.c (frozen, sha256={sha256}):
{poc}

POC oracle:
  - MUST fire on a location inside `{fn}_buggy` (any one row suffices).
  - MUST NOT fire on any location inside `{fn}_fixed`.

Write the .ql now."""

MONO_POC_REFINE = """\
The previous query failed validation.
--- PREVIOUS QUERY ---
{query}
--- DIAGNOSTIC ---
{diag}
--- POC ORACLE (unchanged) ---
fire on {fn}_buggy ; silent on {fn}_fixed.
The POC is FIXED (sha256={sha256}). Modify only the query.
Output ONLY the corrected .ql body."""

# ---------------------------------------------------------------- C2 / C3 planning
PLAN_SYSTEM = FEATURES_SYSTEM + """
You design CodeQL queries (CodeQL 2.25.6, `import cpp`) as a set of named predicates.
No custom .qll libraries: everything lives in one .ql file."""

PLAN_USER_C3 = """\
Features:   {features}
POC source:
{poc}

Task: emit ONE JSON QueryPlan:
  {{
    "imports": ["cpp"],
    "predicates": [
      {{
        "name": "isAcquire",
        "signature": "predicate isAcquire(FunctionCall fc)",
        "body": "predicate isAcquire(FunctionCall fc) {{ fc.getTarget().getName() in [\\"of_parse_phandle\\"] }}",
        "depends_on": [],
        "test_query": "from FunctionCall fc where isAcquire(fc) select fc, \\"t\\"",
        "expected_on_poc": "fires on the acquire calls in every variant",
        "expect": {{"rows": "some", "must_hit": ["buggy", "fixed"], "only_in": []}}
      }}
    ],
    "assembly": "from ... where ... select <element>, \\"<message>\\""
  }}

Rules:
  - `body` is the complete predicate definition (signature included), <= 30 lines.
  - Predicates in `depends_on` appear earlier in the list (topological order).
  - `test_query` is only a from-where-select whose first column is a program element;
    it is evaluated on the POC database with this predicate and its dependencies.
  - `expect` is checked by code: "rows" is "some" or "none"; "must_hit" lists the PoC
    function classes that must contain a result; "only_in" (if non-empty) lists the only
    classes allowed to contain one. Classes: "buggy" (`_buggy`, `_tpN`), "fixed"
    (`_fixed`, `_tnN`), "fp" (`_fpN`), "other".
  - The assembled query must fire inside `_buggy` and the tp variants, and stay silent
    in `_fixed`, tn and fp variants.
Output ONLY the JSON."""

PLAN_USER_C2 = """\
commit:   {sha}
features: {features}

Task: emit ONE JSON object QueryPlan with the schema:
{{
  "imports": ["cpp"],
  "predicates": [
    {{ "name": "<snake_case>",
      "signature": "predicate <name>(<params>)",
      "body": "",
      "depends_on": ["<other predicate names>"] }}
  ],
  "assembly": "from <decls> where <conjunction of predicates> select <expr>, \\"<msg>\\""
}}

Constraints:
- 3 to 6 predicates total.
- Each predicate <= 30 lines when filled.
- depends_on must be a DAG (topological).
- Predicate names must be unique and the assembly's `where` clause must reference them.
- You may rely on `import cpp` and optionally `import semmle.code.cpp.controlflow.Guards`.
Output ONLY the JSON."""

FILL_PRED_C2 = """\
You will fill the body of ONE CodeQL predicate.

Plan context:
{plan}

Predicate to fill:
name:        {name}
signature:   {signature}
depends_on:  {depends_on}

Constraints:
- Body <= 30 lines.
- Use only AST nodes/predicates from the plan's imports.
- Refer to parent predicates by name when needed.
- Do NOT redeclare imports or other predicates.
- Output ONLY the predicate block (signature included), no prose."""

REFINE_PRED = """\
Predicate {name} failed.
Current code:
{code}
Failure:
{failure}
{poc_part}
Task: emit a corrected definition of {name} ONLY (the `predicate {name}(...) {{ ... }}`
form, same signature). Do not re-emit other predicates. Output ONLY the predicate block."""

ASSEMBLE_REFINE = """\
The assembled query failed:
{query}
Failure:
{failure}
{poc_part}
Task: emit a corrected complete `.ql` file (imports + all predicates + final
from-where-select). Keep the predicate names and the assembly intent; no `.qll`
imports. Output ONLY the file body."""
