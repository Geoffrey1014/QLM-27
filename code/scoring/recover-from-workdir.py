#!/usr/bin/env python3
"""Recover D4 (cell, pattern) summary JSON from /tmp workdirs after the
score-cell-pattern.py process was killed mid-run.

Reads /tmp/d4-<cell>-<pattern>/<query>/kbh.score.json and *-{buggy,fixed}.csv
to reconstruct what score-cell-pattern.py would have written.

Usage:
  recover-from-workdir.py --cell C0 --pattern error-return \\
    --out <REPO_ROOT>/experiments/rq3/d4/C0-error-return.json
"""
import argparse
import csv
import json
import os
import sys
from pathlib import Path

QLLLM_ROOT = Path('<REPO_ROOT>')
PAIRWISE_DIR = QLLLM_ROOT / 'experiments/rq3/pairwise-dbs'

PATTERN_PREFIX = {
    'four-features-Lin': 'lin',
    'four-features-Lu': 'lu',
    'missing-check': 'mc',
    'delay-gfp': 'dgfp',
    'error-return': 'err',
}
PATTERN_DB = {
    'four-features-Lin': 'linux-v5.15-arm-am',
    'four-features-Lu': 'linux-v5.0-arm-am-legacy',
    'missing-check': 'linux-v4.19-arm-am-legacy',
    'delay-gfp': 'linux-v4.14-arm-am-legacy',
    'error-return': 'linux-v5.10-arm-am',
}


def count_csv_rows(path):
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return 0
    with open(path) as f:
        return sum(1 for line in f if line.strip())


def recover_pair(workdir, sha):
    buggy_csv = workdir / f'{sha}-buggy.csv'
    fixed_csv = workdir / f'{sha}-fixed.csv'
    if not buggy_csv.exists() or not fixed_csv.exists():
        return {'sha': sha, 'status': 'analyze_fail'}
    bf = count_csv_rows(buggy_csv) > 0
    ff = count_csv_rows(fixed_csv) > 0
    return {
        'sha': sha, 'status': 'ok',
        'buggy_fires': bf, 'fixed_fires': ff,
        'pair_wise_pass': bf and not ff,
    }


def recover_query_pairwise(workdir, pairs):
    results = []
    for pair_base_sha in pairs:
        results.append(recover_pair(workdir, pair_base_sha))
    oks = [r for r in results if r['status'] == 'ok']
    passes = [r for r in oks if r['pair_wise_pass']]
    buggy_count = sum(1 for r in oks if r['buggy_fires'])
    fixed_count = sum(1 for r in oks if r['fixed_fires'])
    return {
        'total_pairs': len(pairs),
        'analyze_ok': len(oks),
        'analyze_fail': len(results) - len(oks),
        'pair_wise_passes': len(passes),
        'pair_wise_pass_rate': (len(passes) / len(oks)) if oks else 0.0,
        'fires_buggy_count': buggy_count,
        'fires_buggy_rate': (buggy_count / len(oks)) if oks else 0.0,
        'fires_fixed_count': fixed_count,
        'fires_fixed_rate': (fixed_count / len(oks)) if oks else 0.0,
        'per_pair': results,
    }


def recover_query_kbh(workdir):
    score_path = workdir / 'kbh.score.json'
    if not score_path.exists():
        return {'status': 'analyze_fail', 'err': 'recover: no kbh.score.json (likely killed mid-KBH)'}
    score = json.load(open(score_path))
    return {
        'status': 'ok',
        'bugs_in_db': score.get('bugs_in_db'),
        'hits': score.get('hits'),
        'recall_raw': score.get('recall_raw'),
        'recall_in_db': score.get('recall_in_db'),
        'coverage_in_db': score.get('coverage_in_db'),
        'fires_total': score.get('fires_total', score.get('fires')),
    }


def find_pair_base_shas(pattern):
    pdir = PAIRWISE_DIR / pattern
    if not pdir.exists():
        return []
    bases = set()
    for sub in pdir.iterdir():
        if sub.is_dir() and sub.name.endswith('-buggy'):
            base = sub.name[:-len('-buggy')]
            if (pdir / f'{base}-fixed').exists():
                bases.add(base)
    return sorted(bases)


def aggregate(per_query):
    pair_rates = [r['pair_wise']['pair_wise_pass_rate']
                  for r in per_query if 'pair_wise_pass_rate' in r.get('pair_wise', {})]
    recall = [r['kbh']['recall_in_db'] for r in per_query
              if r['kbh'].get('status') == 'ok' and r['kbh'].get('recall_in_db') is not None]
    fires_b = [r['pair_wise'].get('fires_buggy_rate', 0) for r in per_query]
    mean = lambda xs: round(sum(xs)/len(xs), 4) if xs else 0.0
    best = lambda xs: round(max(xs), 4) if xs else 0.0
    return {
        'n_queries': len(per_query),
        'pair_wise_mean': mean(pair_rates),
        'pair_wise_best': best(pair_rates),
        'recall_in_db_mean': mean(recall),
        'recall_in_db_best': best(recall),
        'fires_buggy_rate_mean': mean(fires_b),
        'n_kbh_ok': len(recall),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cell', required=True)
    ap.add_argument('--pattern', required=True, choices=list(PATTERN_PREFIX))
    ap.add_argument('--workdir-root', default=None)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    prefix = PATTERN_PREFIX[args.pattern]
    workdir_root = Path(args.workdir_root or f'/tmp/d4-{args.cell}-{args.pattern}')
    pairs = find_pair_base_shas(args.pattern)
    print(f"[recover] cell={args.cell} pattern={args.pattern} workdir_root={workdir_root}", file=sys.stderr)
    print(f"[recover] {len(pairs)} pair base SHAs discovered", file=sys.stderr)

    results = []
    for sid in range(1, 6):
        for rep in range(1, 6):
            qname = f'{prefix}-{sid}-rep{rep}'
            wd = workdir_root / qname
            if not wd.exists():
                results.append({'query': qname, 'seed_id': f'{prefix}-{sid}',
                                'pair_wise': {'pair_wise_pass_rate': 0.0,
                                              'analyze_ok': 0, 'analyze_fail': len(pairs),
                                              'fires_buggy_rate': 0.0, 'per_pair': []},
                                'kbh': {'status': 'no_workdir'},
                                'recovered_reason': 'no_workdir'})
                continue
            pair_res = recover_query_pairwise(wd, pairs)
            kbh_res = recover_query_kbh(wd)
            results.append({
                'query': qname,
                'seed_id': f'{prefix}-{sid}',
                'pair_wise': pair_res,
                'kbh': kbh_res,
                'recovered_from_workdir': True,
            })
            print(f"  {qname}: pair_passes={pair_res['pair_wise_passes']}/{pair_res['analyze_ok']} kbh={kbh_res['status']}", file=sys.stderr)

    agg = aggregate(results)
    summary = {
        'cell': args.cell,
        'pattern': args.pattern,
        'kbh_db': PATTERN_DB[args.pattern],
        'n_queries_found': sum(1 for r in results if r.get('kbh', {}).get('status') != 'no_workdir'),
        'n_pairs': len(pairs),
        'wall_seconds': None,
        'aggregate': agg,
        'per_query': sorted(results, key=lambda r: r['query']),
        'recovered': True,
        'note': f'Recovered from /tmp workdirs after kill; queries without kbh.score.json are marked analyze_fail',
    }
    json.dump(summary, open(args.out, 'w'), indent=2)
    print(f"[recover] wrote {args.out}", file=sys.stderr)
    print(json.dumps(agg, indent=2))


if __name__ == '__main__':
    main()
