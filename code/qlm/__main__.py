"""Command line.

    python3 -m qlm run    --cell C3 --seed lin-1 --repeat 1
    python3 -m qlm batch  --cells C0,C1,C2,C3 --repeats 5 --jobs 4
    python3 -m qlm verify --seed lin-1 --poc path/to/poc.c --work /tmp/v

Run from code/. Seeds come from data/seeds/seeds.json unless --seeds points elsewhere;
outputs go to out/ unless --out is given.
"""

import argparse
import json
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from . import config, verifier
from .kernel import load_commit
from .llm import LLM
from .pipeline import CELLS, run_generation
from .seed import build_seed_slices


def load_seeds(path: str | None) -> dict[str, dict]:
    p = Path(path) if path else config.SEEDS
    return {s["seed_id"]: s for s in json.loads(p.read_text())}


def main() -> None:
    ap = argparse.ArgumentParser(prog="qlm")
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("run", "batch", "verify"):
        p = sub.add_parser(name)
        p.add_argument("--seeds")
        p.add_argument("--backend", default="auto", choices=["auto", "api", "cli"])
    r = sub.choices["run"]
    r.add_argument("--cell", required=True, choices=sorted(CELLS))
    r.add_argument("--seed", required=True)
    r.add_argument("--repeat", type=int, default=1)
    r.add_argument("--out", type=Path, default=config.OUT)
    b = sub.choices["batch"]
    b.add_argument("--cells", default="C0,C1,C2,C3")
    b.add_argument("--only", help="comma-separated seed ids (default: all)")
    b.add_argument("--repeats", type=int, default=5)
    b.add_argument("--jobs", type=int, default=4)
    b.add_argument("--out", type=Path, default=config.OUT)
    b.add_argument("--skip-done", action="store_true", help="skip generations that already have an audit")
    v = sub.choices["verify"]
    v.add_argument("--seed", required=True)
    v.add_argument("--poc", type=Path, required=True)
    v.add_argument("--work", type=Path, required=True)
    a = ap.parse_args()
    seeds = load_seeds(a.seeds)

    if a.cmd == "run":
        print(json.dumps(run_generation(a.cell, seeds[a.seed], a.repeat, a.out, a.backend), indent=2))
    elif a.cmd == "batch":
        ids = a.only.split(",") if a.only else list(seeds)
        jobs = [(c, seeds[i], r) for c in a.cells.split(",") for i in ids for r in range(1, a.repeats + 1)
                if not (a.skip_done and (a.out / c / f"{i}-rep{r}.audit.json").exists())]
        with ThreadPoolExecutor(a.jobs) as ex:
            futs = {ex.submit(run_generation, c, s, r, a.out, a.backend): (c, s["seed_id"], r)
                    for c, s, r in jobs}
            for f in as_completed(futs):
                c, sid, r = futs[f]
                res = f.result()
                print(f"{c} {sid}-rep{r}: {res['status']} {res.get('fail_stage') or ''}", flush=True)
    else:
        s = seeds[a.seed]
        commit = load_commit(s["fix_sha"], s["c_file"])
        sl = build_seed_slices(commit, a.work / "seed", LLM(trace_dir=a.work / "llm-trace", backend=a.backend))
        vd = verifier.run(s["pattern"], commit, sl.buggy_c, sl.fixed_c, sl.buggy_fns, sl.fixed_fns,
                          a.poc, a.work / "verifier")
        print("\n".join(vd.rows))


if __name__ == "__main__":
    main()
