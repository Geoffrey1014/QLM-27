#!/usr/bin/env python3
"""
D4 scorer — runs ONE (cell, pattern) combination end-to-end.

For each of the 25 queries in d3/<cell>/<pattern_prefix>-{1..5}-rep{1..5}.ql:
  1. Run on every pair-wise mini-DB pair (buggy + fixed) for the pattern
     → pair_wise = (fires_buggy ∧ silent_fixed) / total_pairs
  2. Run on the pattern's KBH-Bench DB (linux-vX.Y-arm-am[-legacy])
     → recall_in_db = hits / (bugs_in_db - own_seed_bug if held out)

Output: JSON with per-query metrics + cell-pattern aggregates.

Usage (inside container):
  score-cell-pattern.py --cell C3 --pattern four-features-Lin [--workers 4] [--out /tmp/out.json]
"""
import argparse
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

# Container paths (this script runs INSIDE the qlllm container)
QLLLM_ROOT = Path('<REPO_ROOT>')
CODEQL = QLLLM_ROOT / 'codeql-2.25.6' / 'codeql'
D3_DIR = QLLLM_ROOT / 'experiments/rq3/d3'
PAIRWISE_DIR = QLLLM_ROOT / 'experiments/rq3/pairwise-dbs'
GT_DIR = QLLLM_ROOT / 'scripts/kbh-bench/gt'
KBH_SCORE = QLLLM_ROOT / 'scripts/kbh-bench/score_v2.py'
DB_DIR = QLLLM_ROOT / 'codeql-dbs'

# Pattern → (seed_id_prefix, KBH-Bench DB name, GT file, funcs CSV)
PATTERN_CONFIG = {
    'four-features-Lin': {
        'prefix': 'lin',
        'kbh_db': 'linux-v5.15-arm-am',
        'gt_file': 'aphp-lin-v5.15.json',
        'funcs_csv': 'funcs-v5.15-am.csv',
    },
    'four-features-Lu': {
        'prefix': 'lu',
        'kbh_db': 'linux-v5.0-arm-am-legacy',
        'gt_file': 'crix-lu-v5.0.json',
        'funcs_csv': 'funcs-v5.0-am-legacy.csv',
    },
    'missing-check': {
        'prefix': 'mc',
        'kbh_db': 'linux-v4.19-arm-am-legacy',
        'gt_file': 'crix-missing-check-v4.19.json',
        'funcs_csv': 'funcs-v4.19-am-legacy.csv',
    },
    'delay-gfp': {
        'prefix': 'dgfp',
        'kbh_db': 'linux-v4.14-arm-am-legacy',
        'gt_file': 'bai-delay-gfp-v4.14.json',
        'funcs_csv': 'funcs-v4.14-am-legacy.csv',
    },
    'error-return': {
        'prefix': 'err',
        'kbh_db': 'linux-v5.10-arm-am',
        'gt_file': 'bai-error-retcode-v5.10.json',
        'funcs_csv': 'funcs-v5.10-am.csv',
    },
}


def find_db_root(bug_dir: Path) -> Path | None:
    """Pair-wise pattern dbs have 2 layouts: direct or nested in db/."""
    if (bug_dir / 'codeql-database.yml').exists():
        return bug_dir
    if (bug_dir / 'db' / 'codeql-database.yml').exists():
        return bug_dir / 'db'
    return None


def setup_qlpack(workdir: Path, query_path: Path) -> Path:
    """Create a qlpack temp dir containing the query and a qlpack.yml that pulls cpp-all."""
    workdir.mkdir(parents=True, exist_ok=True)
    qlpack_yml = workdir / 'qlpack.yml'
    qlpack_yml.write_text(
        'name: score-temp\nversion: 0.0.1\ndependencies:\n  codeql/cpp-all: "*"\n'
    )
    target = workdir / 'query.ql'
    shutil.copyfile(query_path, target)
    return target


def run_codeql_analyze(db: Path, query: Path, out_csv: Path, threads: int = 2,
                       fmt: str = 'csv', timeout: int = 600) -> tuple[bool, str]:
    """Run codeql database analyze; return (ok, stderr_tail)."""
    cmd = [
        str(CODEQL), 'database', 'analyze',
        str(db), str(query),
        '--format', fmt, '--output', str(out_csv),
        '--threads', str(threads),
        '--rerun',
    ]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        if r.returncode != 0:
            tail = (r.stderr or r.stdout)[-400:]
            return (False, tail)
        return (True, '')
    except subprocess.TimeoutExpired:
        return (False, f'TIMEOUT after {timeout}s')


def count_csv_rows(path: Path) -> int:
    """Number of result rows in codeql --format=csv output (skip header? csv has no header)."""
    if not path.exists() or path.stat().st_size == 0:
        return 0
    with open(path) as f:
        return sum(1 for _ in f if _.strip())


def score_pair(workdir: Path, query_path: Path, pair_dir: Path) -> dict:
    """Run query on (buggy, fixed) pair; return verdict."""
    sha = pair_dir.name
    buggy_db = find_db_root(PAIRWISE_DIR / 'four-features-Lin' / f'{sha}-buggy') or \
               find_db_root(pair_dir.parent / f'{sha}-buggy')
    # find via the pair_dir itself
    parent = pair_dir.parent if pair_dir.name.endswith(('-buggy', '-fixed')) else pair_dir
    base_sha = sha.replace('-buggy', '').replace('-fixed', '')
    buggy_dir = parent / f'{base_sha}-buggy' if not pair_dir.name.endswith('-buggy') else pair_dir
    fixed_dir = parent / f'{base_sha}-fixed'

    buggy_db = find_db_root(buggy_dir)
    fixed_db = find_db_root(fixed_dir)

    if buggy_db is None or fixed_db is None:
        return {'sha': base_sha, 'status': 'missing_db', 'buggy_fires': None, 'fixed_fires': None}

    buggy_csv = workdir / f'{base_sha}-buggy.csv'
    fixed_csv = workdir / f'{base_sha}-fixed.csv'

    ok_b, err_b = run_codeql_analyze(buggy_db, query_path, buggy_csv)
    ok_f, err_f = run_codeql_analyze(fixed_db, query_path, fixed_csv)

    if not ok_b or not ok_f:
        return {'sha': base_sha, 'status': 'analyze_fail',
                'buggy_err': err_b if not ok_b else None,
                'fixed_err': err_f if not ok_f else None}

    bf = count_csv_rows(buggy_csv) > 0
    ff = count_csv_rows(fixed_csv) > 0
    return {
        'sha': base_sha,
        'status': 'ok',
        'buggy_fires': bf,
        'fixed_fires': ff,
        'pair_wise_pass': bf and not ff,
    }


def score_query_pairwise(workdir: Path, query_path: Path, pattern: str, pairs: list[Path]) -> dict:
    """Score one query against all pair-wise pairs of a pattern."""
    results = []
    for pair_dir in pairs:
        r = score_pair(workdir, query_path, pair_dir)
        results.append(r)
    oks = [r for r in results if r['status'] == 'ok']
    passes = [r for r in oks if r['pair_wise_pass']]
    buggy_fires_count = sum(1 for r in oks if r['buggy_fires'])
    fixed_fires_count = sum(1 for r in oks if r['fixed_fires'])
    return {
        'total_pairs': len(pairs),
        'analyze_ok': len(oks),
        'analyze_fail': len(results) - len(oks),
        'pair_wise_passes': len(passes),
        'pair_wise_pass_rate': (len(passes) / len(oks)) if oks else 0.0,
        'fires_buggy_count': buggy_fires_count,
        'fires_buggy_rate': (buggy_fires_count / len(oks)) if oks else 0.0,
        'fires_fixed_count': fixed_fires_count,
        'fires_fixed_rate': (fixed_fires_count / len(oks)) if oks else 0.0,
        'per_pair': results,
    }


def score_query_kbh(workdir: Path, query_path: Path, pattern: str,
                    held_out_sha: str) -> dict:
    """Score one query against KBH-Bench DB, with seed hold-out."""
    cfg = PATTERN_CONFIG[pattern]
    db = DB_DIR / cfg['kbh_db']
    gt_path = GT_DIR / cfg['gt_file']
    funcs_path = GT_DIR / cfg['funcs_csv']

    if not db.exists():
        return {'status': 'db_missing', 'db': str(db)}
    if not gt_path.exists():
        return {'status': 'gt_missing', 'gt': str(gt_path)}

    sarif = workdir / 'kbh.sarif'
    ok, err = run_codeql_analyze(db, query_path, sarif, threads=4,
                                 fmt='sarif-latest', timeout=1200)
    if not ok:
        return {'status': 'analyze_fail', 'err': err}

    # Build hold-out GT (exclude bug whose fix_sha matches held_out_sha)
    full_gt = json.load(open(gt_path))
    held_out_full = [b for b in full_gt if not b['fix_sha'].startswith(held_out_sha)]
    excluded = len(full_gt) - len(held_out_full)
    ho_gt_path = workdir / 'kbh-holdout-gt.json'
    json.dump(held_out_full, open(ho_gt_path, 'w'))

    # Run score_v2.py
    score_out = workdir / 'kbh.score.json'
    score_cmd = [
        'python3', str(KBH_SCORE),
        '--sarif', str(sarif),
        '--gt', str(ho_gt_path),
        '--funcs', str(funcs_path),
        '--out', str(score_out),
    ]
    sr = subprocess.run(score_cmd, capture_output=True, text=True, timeout=120)
    if sr.returncode != 0:
        return {'status': 'score_fail', 'err': sr.stderr[-400:]}

    score = json.load(open(score_out))
    return {
        'status': 'ok',
        'gt_total': len(full_gt),
        'gt_after_holdout': len(held_out_full),
        'gt_excluded': excluded,
        'bugs_in_db': score.get('bugs_in_db'),
        'hits': score.get('hits'),
        'recall_raw': score.get('recall_raw'),
        'recall_in_db': score.get('recall_in_db'),
        'coverage_in_db': score.get('coverage_in_db'),
        'fires_total': score.get('fires_total', score.get('fires')),
    }


def score_one_query(query_path: Path, pattern: str, pairs: list[Path],
                    base_workdir: Path, skip_pairwise: bool = False) -> dict:
    """Per-query orchestration: (optional) pair-wise + KBH-Bench."""
    # Each query gets its own workdir
    seed_rep = query_path.stem  # e.g. "lin-1-rep1"
    workdir = base_workdir / seed_rep
    workdir.mkdir(parents=True, exist_ok=True)
    qlocal = setup_qlpack(workdir / 'pack', query_path)

    seed_id = seed_rep.rsplit('-rep', 1)[0]  # "lin-1"
    # Look up the seed's fix_sha for hold-out
    seeds = json.load(open('<REPO_ROOT>/experiments/rq3/seeds.json'))
    seed_meta = next((s for s in seeds if s['seed_id'] == seed_id), None)
    held_out_sha = seed_meta['fix_sha'][:12] if seed_meta else ''

    if skip_pairwise:
        pair_res = {'skipped': True, 'total_pairs': len(pairs), 'analyze_ok': 0,
                    'analyze_fail': 0, 'pair_wise_passes': 0,
                    'pair_wise_pass_rate': None, 'fires_buggy_count': 0,
                    'fires_buggy_rate': None, 'fires_fixed_count': 0,
                    'fires_fixed_rate': None, 'per_pair': []}
        t_pair = 0.0
    else:
        t0 = time.time()
        pair_res = score_query_pairwise(workdir, qlocal, pattern, pairs)
        t_pair = time.time() - t0

    t1 = time.time()
    kbh_res = score_query_kbh(workdir, qlocal, pattern, held_out_sha)
    t_kbh = time.time() - t1

    # Clean up large workdir contents (keep summary)
    # (kept for now; agent can clean later)

    return {
        'query': seed_rep,
        'seed_id': seed_id,
        'held_out_sha': held_out_sha,
        'pair_wise': pair_res,
        'kbh': kbh_res,
        'wall_pair_s': round(t_pair, 1),
        'wall_kbh_s': round(t_kbh, 1),
    }


def find_queries(cell: str, prefix: str) -> list[Path]:
    cell_dir = D3_DIR / cell
    out = []
    for sid in range(1, 6):
        for rep in range(1, 6):
            p = cell_dir / f'{prefix}-{sid}-rep{rep}.ql'
            if p.exists():
                out.append(p)
    return out


def find_pairs(pattern: str) -> list[Path]:
    """Return list of pair-base dirs (one per pair, containing -buggy and -fixed)."""
    pdir = PAIRWISE_DIR / pattern
    if not pdir.exists():
        return []
    seen = set()
    out = []
    for sub in sorted(pdir.iterdir()):
        if sub.is_dir() and sub.name.endswith('-buggy'):
            base_sha = sub.name[:-len('-buggy')]
            fixed = pdir / f'{base_sha}-fixed'
            if fixed.exists() and base_sha not in seen:
                seen.add(base_sha)
                out.append(sub)
    return out


def aggregate(per_query: list[dict]) -> dict:
    """Per-cell × pattern aggregates."""
    n = len(per_query)
    # Skip pair-wise stats when the field is None (skip_pairwise mode).
    pair_pass_rates = [r['pair_wise']['pair_wise_pass_rate']
                       for r in per_query
                       if r.get('pair_wise', {}).get('pair_wise_pass_rate') is not None]
    recall_in_db = [r['kbh'].get('recall_in_db') for r in per_query if r['kbh'].get('status') == 'ok']
    recall_in_db = [x for x in recall_in_db if x is not None]
    fires_buggy_rates = [r['pair_wise'].get('fires_buggy_rate', 0)
                         for r in per_query
                         if r.get('pair_wise', {}).get('fires_buggy_rate') is not None]

    # Cell-level union recall: union of all bugs hit across queries
    # Need to re-run scoring with unioned SARIFs OR collect bug IDs from kbh.score.json
    # For simplicity, report mean and best; union requires extra pass

    def mean(xs):
        return round(sum(xs) / len(xs), 4) if xs else 0.0
    def best(xs):
        return round(max(xs), 4) if xs else 0.0

    return {
        'n_queries': n,
        'pair_wise_mean': mean(pair_pass_rates),
        'pair_wise_best': best(pair_pass_rates),
        'recall_in_db_mean': mean(recall_in_db),
        'recall_in_db_best': best(recall_in_db),
        'fires_buggy_rate_mean': mean(fires_buggy_rates),
        'n_kbh_ok': len(recall_in_db),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cell', required=True,
                    help='C0/C1/C2/C3 for D4; L0/L1/L3 for D6 RQ4')
    ap.add_argument('--pattern', required=True, choices=list(PATTERN_CONFIG))
    ap.add_argument('--workers', type=int, default=2)
    ap.add_argument('--workdir', default=None)
    ap.add_argument('--out', default=None)
    ap.add_argument('--skip-pairwise', action='store_true',
                    help='Skip the 16-30 pair-wise mini-DB analyzes; only run KBH-Bench. '
                         'Cuts per-query wall by ~60%. Used for RQ4 D6 scoring where only '
                         'recall_in_db matters. Pair-wise fields set to None in output.')
    ap.add_argument('--d3-dir', default=None,
                    help='Override D3 dir (default experiments/rq3/d3/); use experiments/rq3/d5/ for RQ4 gens.')
    args = ap.parse_args()

    cfg = PATTERN_CONFIG[args.pattern]
    global D3_DIR
    if args.d3_dir:
        D3_DIR = Path(args.d3_dir)
    queries = find_queries(args.cell, cfg['prefix'])
    pairs = find_pairs(args.pattern) if not args.skip_pairwise else []

    print(f"[score] cell={args.cell} pattern={args.pattern} skip_pairwise={args.skip_pairwise}", file=sys.stderr)
    print(f"     queries={len(queries)} pairs={len(pairs)}", file=sys.stderr)
    print(f"     kbh_db={cfg['kbh_db']}", file=sys.stderr)

    base_workdir = Path(args.workdir or f'/tmp/d4-{args.cell}-{args.pattern}')
    base_workdir.mkdir(parents=True, exist_ok=True)

    t0 = time.time()
    results = []

    if args.workers > 1:
        with ThreadPoolExecutor(max_workers=args.workers) as ex:
            futs = {ex.submit(score_one_query, q, args.pattern, pairs, base_workdir, args.skip_pairwise): q for q in queries}
            for fut in as_completed(futs):
                q = futs[fut]
                try:
                    results.append(fut.result())
                    print(f"  done: {q.stem}", file=sys.stderr)
                except Exception as e:
                    print(f"  FAIL: {q.stem}: {e}", file=sys.stderr)
                    results.append({'query': q.stem, 'error': str(e)})
    else:
        for q in queries:
            try:
                r = score_one_query(q, args.pattern, pairs, base_workdir, args.skip_pairwise)
                results.append(r)
                print(f"  done: {q.stem}", file=sys.stderr)
            except Exception as e:
                print(f"  FAIL: {q.stem}: {e}", file=sys.stderr)
                results.append({'query': q.stem, 'error': str(e)})

    elapsed = time.time() - t0
    agg = aggregate([r for r in results if 'error' not in r])

    summary = {
        'cell': args.cell,
        'pattern': args.pattern,
        'kbh_db': cfg['kbh_db'],
        'gt_file': cfg['gt_file'],
        'n_queries_found': len(queries),
        'n_pairs': len(pairs),
        'skip_pairwise': args.skip_pairwise,
        'wall_seconds': round(elapsed, 1),
        'aggregate': agg,
        'per_query': sorted(results, key=lambda r: r.get('query', '')),
    }

    out_path = args.out or f'{base_workdir}/d4-{args.cell}-{args.pattern}.json'
    json.dump(summary, open(out_path, 'w'), indent=2)
    print(f"[score] DONE in {elapsed:.0f}s — wrote {out_path}", file=sys.stderr)
    print(json.dumps(agg, indent=2))


if __name__ == '__main__':
    main()
