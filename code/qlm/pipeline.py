"""One generation = one (cell, seed, repeat): seed patch -> CodeQL query + audit.json.

Cells of the RQ3 2x2 ablation, selected by two switches:
    C0  compositional=off  poc=off   monolithic query, compile-repair only
    C1  compositional=off  poc=on    PoC + fidelity check, monolithic query, PoC oracle
    C2  compositional=on   poc=off   plan -> per-predicate fill, compile-only validation
    C3  compositional=on   poc=on    plan -> per-predicate validation on the PoC, oracle
The LLM only produces text (features, PoC, plan, predicate bodies, queries). Everything
else is code: patch and function extraction, seed slices, gcc, databases, the fidelity
check, compilation, running on the PoC, expectation and oracle checks, iteration caps.
"""

import hashlib
import json
import re
import shutil
import subprocess
import threading
import time
from dataclasses import dataclass
from pathlib import Path

from . import codeql, config, oracle, prompts, verifier
from .kernel import bug_functions, load_commit
from .llm import LLM, strip_fences
from .seed import SeedSlices, build_seed_slices

CELLS = {"C0": (False, False), "C1": (False, True), "C2": (True, False), "C3": (True, True)}
_seed_locks: dict[str, threading.Lock] = {}


@dataclass
class Seed:
    seed_id: str
    pattern: str
    fix_sha: str
    c_file: str
    subject: str = ""


class Fail(Exception):
    def __init__(self, stage: str, why: str = ""):
        super().__init__(f"{stage}: {why}")
        self.stage, self.why = stage, why


class Generation:
    def __init__(self, cell: str, seed: Seed, repeat: int, out_root: Path, backend: str = "auto"):
        self.cell, self.seed, self.repeat = cell, seed, repeat
        self.compositional, self.use_poc = CELLS[cell]
        self.dir = out_root / cell / f"{seed.seed_id}-rep{repeat}"
        self.out_root = out_root
        self.llm = LLM(trace_dir=self.dir / "llm-trace", backend=backend)
        self.audit: dict = {
            "cell": cell, "seed_id": seed.seed_id, "repeat": repeat, "pattern": seed.pattern,
            "fix_sha": seed.fix_sha, "c_file": seed.c_file, "model": self.llm.model,
            "backend": self.llm.backend, "llm_calls": 0, "compile_iters": 0, "poc_regens": 0,
            "verifier_passes": None, "verifier_rows": None, "predicate_iters": {},
            "final_compiles": False, "final_runs_on_poc": None, "buggy_fires": None,
            "fixed_fires": None, "fp_fires": None, "status": "fail", "fail_stage": None,
        }

    # ------------------------------------------------------------------ driver
    def run(self) -> dict:
        t0 = time.time()
        if self.dir.exists():
            shutil.rmtree(self.dir)
        self.dir.mkdir(parents=True)
        codeql.ensure_pack(self.dir, f"qlm/{self.cell.lower()}-{self.seed.seed_id}-rep{self.repeat}")
        try:
            self.commit = load_commit(self.seed.fix_sha, self.seed.c_file)
            buggy, fixed = bug_functions(self.commit)
            if not buggy or not fixed:
                raise Fail("extract", "bug-touched function not found")
            self.fn = buggy[0].name
            self.buggy_fn = "\n".join(s.text for s in buggy)
            self.fixed_fn = "\n".join(s.text for s in fixed)
            features = self.features() if self.compositional else None
            poc = self.poc(features) if self.use_poc else None
            if self.compositional:
                query = self.compositional_query(features, poc)
            else:
                query = self.monolithic_query(poc)
            self.audit["status"] = "pass"
        except Fail as f:
            self.audit["fail_stage"], self.audit["fail_reason"] = f.stage, f.why[-2000:]
            query = self.dir / "final.ql" if (self.dir / "final.ql").exists() else None
        except Exception as e:  # infrastructure error: keep the run, mark it
            self.audit["fail_stage"], self.audit["fail_reason"] = "error", repr(e)[-2000:]
            query = None
        self.audit["llm_calls"] = self.llm.calls
        self.audit["wall_seconds"] = round(time.time() - t0, 1)
        (self.dir / "audit.json").write_text(json.dumps(self.audit, indent=2))
        # flat copies <out>/<cell>/<seed>-rep<N>.ql / .audit.json, the layout code/scoring reads
        flat = self.out_root / self.cell
        if query and query.exists():
            shutil.copy(query, flat / f"{self.seed.seed_id}-rep{self.repeat}.ql")
        shutil.copy(self.dir / "audit.json", flat / f"{self.seed.seed_id}-rep{self.repeat}.audit.json")
        return self.audit

    def ask(self, stage: str, system: str, user: str) -> str:
        return strip_fences(self.llm(stage, system, user))

    # ------------------------------------------------------------------ stage 1
    def features(self) -> dict:
        s = self.seed
        text = self.ask("features", prompts.FEATURES_SYSTEM.format(pattern=s.pattern),
                        prompts.FEATURES_USER.format(sha=s.fix_sha, subject=self.commit.subject,
                                                     c_file=s.c_file, buggy_fn=self.buggy_fn,
                                                     fixed_fn=self.fixed_fn, patch=self.commit.patch))
        feats = parse_json(text, "features")
        (self.dir / "features.json").write_text(json.dumps(feats, indent=2))
        # Seeds are drawn from a benchmark pattern, so a "does not fit" answer is recorded
        # but does not stop the run.
        self.audit["fits_pattern"] = feats.get("fits_pattern")
        return feats

    # ------------------------------------------------------------------ stage 2: PoC
    def seed_slices(self) -> SeedSlices:
        """Seed slices are infrastructure, identical for every cell and repeat of a seed:
        build once under <out>/_seed-slices/<seed_id>/ and reuse."""
        d = self.out_root / "_seed-slices" / self.seed.seed_id
        meta = d / "slices.json"
        with _seed_locks.setdefault(self.seed.seed_id, threading.Lock()):
            if not meta.exists():
                sl = build_seed_slices(self.commit, d, LLM(trace_dir=d / "llm-trace", backend=self.llm.backend))
                meta.write_text(json.dumps({"buggy_c": str(sl.buggy_c), "fixed_c": str(sl.fixed_c),
                                            "buggy_fns": sl.buggy_fns, "fixed_fns": sl.fixed_fns,
                                            "stub_iters": sl.stub_iters}))
            m = json.loads(meta.read_text())
        return SeedSlices(Path(m["buggy_c"]), Path(m["fixed_c"]), m["buggy_fns"], m["fixed_fns"], m["stub_iters"])

    def poc(self, features: dict | None) -> Path:
        s = self.seed
        slices = self.seed_slices()
        variants = prompts.POC_VARIANTS_C3.format(fn=self.fn) if self.cell == "C3" else ""
        feats = f"Features: {json.dumps(features)}\n" if features else ""
        system = prompts.POC_SYSTEM.format(fn=self.fn, variants=variants)
        user = prompts.POC_USER.format(
            subject=self.commit.subject, c_file=s.c_file, pattern=s.pattern, features=feats,
            patch=self.commit.patch, buggy_fn=self.buggy_fn, fixed_fn=self.fixed_fn)
        regen = prompts.POC_REGEN
        poc_c = self.dir / "poc.c"
        prev = why = None
        history = []
        for attempt in range(config.POC_MAX_REGEN + 1):
            self.audit["poc_regens"] = attempt
            extra = regen.format(prev=prev, why=why, fn=self.fn) if prev else ""
            text = self.ask("poc" if not prev else "poc-regen", system, user + extra)
            if poc_c.exists():
                poc_c.chmod(0o644)
            poc_c.write_text(text)
            (self.dir / f"poc.attempt{attempt}.c").write_text(text)
            err = gcc(poc_c)
            if err:
                history.append({"attempt": attempt, "gcc": err.splitlines()[:5]})
                prev, why = text, "gcc errors:\n" + "\n".join(err.splitlines()[:60])
                continue
            ok, rows, feedback = self.guard(slices, poc_c)
            history.append({"attempt": attempt, "guard": rows})
            self.audit["verifier_rows"], self.audit["guard_history"] = rows, history
            if ok:
                self.audit["verifier_passes"] = True
                break
            prev, why = text, feedback
        else:
            self.audit["verifier_passes"] = False
            raise Fail("verifier", why or "")
        poc_c.chmod(0o444)
        self.poc_sha = hashlib.sha256(poc_c.read_bytes()).hexdigest()
        self.audit["poc_sha256"] = self.poc_sha
        src = self.dir / "poc-src"
        src.mkdir(exist_ok=True)
        shutil.copy(poc_c, src / "poc.c")
        ok, log = codeql.create_db(src, self.dir / "poc-db", ["gcc -std=gnu11 -O0 -w -c poc.c -o poc.o"])
        if not ok:
            raise Fail("poc-db", log)
        self.spans = oracle.spans(self.dir / "poc-db", self.dir)
        return poc_c

    def guard(self, slices: SeedSlices, poc_c: Path) -> tuple[bool, list[str], str]:
        """Structural fidelity check on a compiled PoC: (passes, rows for the audit, feedback
        for a regen). Infrastructure errors raise; a PoC the checker cannot read is the PoC's fault."""
        s = self.seed
        v = verifier.run(s.pattern, self.commit, slices.buggy_c, slices.fixed_c,
                         slices.buggy_fns, slices.fixed_fns, poc_c, self.dir / "verifier")
        if v.error:  # infrastructure, not the PoC: regenerating would not help
            raise RuntimeError("fidelity check could not run: " + "; ".join(v.rows))
        return v.ok, v.rows, "structural fidelity check:\n" + v.feedback()

    def run_on_poc(self, ql: Path) -> tuple[bool, oracle.Hits | None, str]:
        ok, tuples, err = codeql.run_query(ql, self.dir / "poc-db", out_dir=ql.parent)
        return ok, (oracle.locate(tuples, self.spans) if ok else None), err

    # ------------------------------------------------------------------ monolithic (C0, C1)
    def monolithic_query(self, poc: Path | None) -> Path:
        s, ql = self.seed, self.dir / "final.ql"
        if poc is None:
            text = self.ask("query", prompts.QUERY_PREAMBLE, prompts.KNIGHTER_CHECKER.format(
                sha=s.fix_sha, subject=self.commit.subject, message=self.commit.message,
                patch=self.commit.patch, c_file=s.c_file))
        else:
            system = prompts.MONO_POC_SYSTEM.replace("<seed_id>", s.seed_id)
            text = self.ask("query", system, prompts.MONO_POC_USER.format(
                patch=self.commit.patch, sha256=self.poc_sha, poc=poc.read_text(), fn=self.fn))
        for it in range(1, config.ASSEMBLE_MAX_ITERS + 1):
            ql.write_text(text)
            self.audit["compile_iters"] += 1
            ok, err = codeql.compile_query(ql)
            if ok:
                self.audit["final_compiles"] = True
                if poc is None:
                    return ql
                diag = self.oracle_diag(ql)
                if diag is None:
                    return ql
            else:
                self.audit["final_compiles"] = False
                diag = "compile error:\n" + head(err)
            if it == config.ASSEMBLE_MAX_ITERS:
                break
            if poc is None:
                text = self.ask("compile-repair", prompts.QUERY_PREAMBLE,
                                prompts.COMPILE_REPAIR.format(query=text, stderr=head(err)))
            else:
                text = self.ask("refine", system, prompts.MONO_POC_REFINE.format(
                    query=text, diag=diag, fn=self.fn, sha256=self.poc_sha))
        raise Fail("assemble", diag)

    def oracle_diag(self, ql: Path) -> str | None:
        ok, hits, err = self.run_on_poc(ql)
        self.audit["final_runs_on_poc"] = ok
        if not ok:
            return "run on PoC database failed:\n" + head(err)
        accepted, flags, diag = oracle.final_oracle(hits)
        self.audit.update(flags)
        if self.cell == "C1":  # C1's PoC has no fp variants; its oracle is buggy vs fixed only
            accepted = flags["buggy_fires"] and not flags["fixed_fires"]
        return None if accepted else diag

    # ------------------------------------------------------------------ compositional (C2, C3)
    def compositional_query(self, features: dict, poc: Path | None) -> Path:
        s = self.seed
        system = prompts.PLAN_SYSTEM.format(pattern=s.pattern)
        if poc is None:
            user = prompts.PLAN_USER_C2.format(sha=s.fix_sha, features=json.dumps(features, indent=1))
        else:
            user = prompts.PLAN_USER_C3.format(features=json.dumps(features, indent=1), poc=poc.read_text())
        plan = parse_json(self.ask("plan", system, user), "plan")
        preds = topo_order(plan.get("predicates", []))
        plan["predicates"] = preds
        (self.dir / "plan.json").write_text(json.dumps(plan, indent=2))
        imports = "\n".join(f"import {i}" for i in plan.get("imports", ["cpp"]))
        preds_dir = self.dir / "preds"
        preds_dir.mkdir(exist_ok=True)
        poc_part = f"POC source (read-only):\n{poc.read_text()}" if poc else ""

        for p in preds:
            if poc is None:
                p["body"] = self.ask("fill-" + p["name"], system, prompts.FILL_PRED_C2.format(
                    plan=json.dumps(plan, indent=1), name=p["name"], signature=p["signature"],
                    depends_on=p.get("depends_on", [])))
            for it in range(1, config.PRED_MAX_ITERS + 1):
                self.audit["predicate_iters"][p["name"]] = it
                ql = preds_dir / f"{p['name']}.ql"
                deps = [d for d in preds if d["name"] in transitive_deps(p, preds)]
                test = p.get("test_query") or harness(p)
                code = imports + "\n\n" + "\n\n".join(d["body"] for d in deps + [p]) + "\n\n" + test + "\n"
                ql.write_text(code)
                self.audit["compile_iters"] += 1
                ok, err = codeql.compile_query(ql)
                failure = None if ok else "compile error:\n" + head(err)
                if ok and poc is not None:
                    ran, hits, rerr = self.run_on_poc(ql)
                    if not ran:
                        failure = "test query failed to run:\n" + head(rerr)
                    else:
                        why = oracle.check_expect(hits, p.get("expect", {}))
                        if why:
                            failure = f"wrong test_query output ({p.get('expected_on_poc', '')}): {why}"
                if failure is None:
                    break
                if it == config.PRED_MAX_ITERS:
                    raise Fail(f"predicate:{p['name']}", failure)
                p["body"] = self.ask("refine-" + p["name"], system, prompts.REFINE_PRED.format(
                    name=p["name"], code=code, failure=failure, poc_part=poc_part))
        (self.dir / "plan.json").write_text(json.dumps(plan, indent=2))

        ql = self.dir / "final.ql"
        header = (f"/**\n * @name qlm-{self.cell.lower()}-{s.seed_id}-rep{self.repeat}\n"
                  f" * @description Generated by QLM ({self.cell}) from {s.fix_sha}.\n"
                  f" * @kind problem\n * @problem.severity warning\n"
                  f" * @id qlm/{self.cell.lower()}/{s.seed_id}-rep{self.repeat}\n */\n")
        text = header + imports + "\n\n" + "\n\n".join(p["body"] for p in preds) + \
            "\n\n" + plan["assembly"] + "\n"
        for it in range(1, config.ASSEMBLE_MAX_ITERS + 1):
            ql.write_text(text)
            self.audit["compile_iters"] += 1
            ok, err = codeql.compile_query(ql)
            self.audit["final_compiles"] = ok
            failure = None if ok else "compile error:\n" + head(err)
            if ok and poc is not None:
                failure = self.oracle_diag(ql)
            if failure is None:
                return ql
            if it == config.ASSEMBLE_MAX_ITERS:
                break
            text = self.ask("assemble-refine", system, prompts.ASSEMBLE_REFINE.format(
                query=text, failure=failure, poc_part=poc_part))
        raise Fail("assemble", failure)


# ---------------------------------------------------------------------- helpers
def head(text: str, n: int = 80) -> str:
    return "\n".join(text.strip().splitlines()[:n])


def gcc(path: Path) -> str:
    r = subprocess.run(["gcc", "-std=gnu11", "-O0", "-w", "-c", str(path), "-o", "/dev/null"],
                       capture_output=True, text=True)
    return "" if r.returncode == 0 else r.stderr


def parse_json(text: str, what: str) -> dict:
    m = re.search(r"\{.*\}", text, re.S)
    try:
        return json.loads(m.group(0) if m else text)
    except json.JSONDecodeError as e:
        raise Fail(what, f"response is not JSON: {e}")


def referenced(p: dict, preds: list[dict]) -> set[str]:
    """Plan predicates `p` actually calls (body or test query), plus its declared deps.
    Plans often under-declare `depends_on`, so declared deps alone are not enough."""
    text = p.get("body", "") + "\n" + p.get("test_query", "")
    used = {q["name"] for q in preds if q is not p and re.search(rf"\b{re.escape(q['name'])}\s*\(", text)}
    return used | set(p.get("depends_on", []))


def topo_order(preds: list[dict]) -> list[dict]:
    """Order predicates so the ones they call come first; reject unknown deps. A cycle
    (mutual recursion) keeps the plan's order for the predicates involved."""
    by_name = {p["name"]: p for p in preds}
    out, state = [], {}

    def visit(name):
        if state.get(name):
            return
        if name not in by_name:
            raise Fail("plan", f"unknown dependency {name!r}")
        state[name] = "active"
        for d in sorted(referenced(by_name[name], preds)):
            visit(d)
        state[name] = "done"
        out.append(by_name[name])

    for p in preds:
        visit(p["name"])
    return out


def transitive_deps(p: dict, preds: list[dict]) -> set[str]:
    by_name = {q["name"]: q for q in preds}
    seen, todo = set(), list(referenced(p, preds))
    while todo:
        d = todo.pop()
        if d not in seen and d != p["name"]:
            seen.add(d)
            todo += referenced(by_name[d], preds)
    return seen


def harness(p: dict) -> str:
    """C2 has no test queries: a trivial select that forces the predicate to type-check."""
    params = re.search(r"\((.*)\)", p["signature"]).group(1).strip()
    if not params:
        return f"select 1, \"harness\"\n// {p['name']}()"
    decls = [x.strip() for x in params.split(",")]
    names = [d.split()[-1] for d in decls]
    sig = p["signature"]
    if not sig.lstrip().startswith("predicate"):  # a predicate with a result
        return f"from {', '.join(decls)} select {p['name']}({', '.join(names)}), \"harness\""
    return f"from {', '.join(decls)} where {p['name']}({', '.join(names)}) select {names[0]}, \"harness\""


def run_generation(cell: str, seed: dict, repeat: int, out_root: Path, backend: str = "auto") -> dict:
    out_root = Path(out_root).resolve()
    (out_root / cell).mkdir(parents=True, exist_ok=True)
    s = Seed(**{k: seed[k] for k in ("seed_id", "pattern", "fix_sha", "c_file")},
             subject=seed.get("subject", ""))
    return Generation(cell, s, repeat, out_root, backend).run()
