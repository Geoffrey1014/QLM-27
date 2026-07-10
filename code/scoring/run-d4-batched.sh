#!/usr/bin/env bash
# Run all 20 cell×pattern D4 scoring jobs with bounded parallelism.
# Avoids the agent-timeout + OOM issues from the per-agent approach.
#
# Usage:
#   run-d4-batched.sh [max_jobs=6]
#
# Outputs:
#   experiments/rq3/d4/<cell>-<pattern>.json (per combo)
#   experiments/rq3/d4/logs/<cell>-<pattern>.log
#   experiments/rq3/d4/run-summary.json (final aggregate)

set -uo pipefail

MAX_JOBS="${1:-6}"
HOST_QLLLM=<REPO_ROOT>
PROJ=$HOST_QLLLM/workspace/QLLLM
D4_DIR=$PROJ/experiments/rq3/d4
LOG_DIR=$D4_DIR/logs

mkdir -p "$D4_DIR" "$LOG_DIR"

CELLS=(C0 C1 C2 C3)
PATTERNS=(four-features-Lin four-features-Lu missing-check delay-gfp error-return)

# Master log
MASTER=$LOG_DIR/_master.log
echo "[$(date +%H:%M:%S)] D4 batched dispatch starting; max_jobs=$MAX_JOBS" | tee -a "$MASTER"
echo "[$(date +%H:%M:%S)] cells=${CELLS[*]}  patterns=${PATTERNS[*]}" | tee -a "$MASTER"

cd "$HOST_QLLLM"

run_one() {
    local cell="$1" pattern="$2"
    local log="$LOG_DIR/${cell}-${pattern}.log"
    local out="$D4_DIR/${cell}-${pattern}.json"
    local t0=$(date +%s)
    echo "[$(date +%H:%M:%S)] START $cell/$pattern → $out" >> "$MASTER"
    docker compose exec -T qlllm bash -c "
        python3 <REPO_ROOT>/scripts/d4-scoring/score-cell-pattern.py \
          --cell '$cell' --pattern '$pattern' --workers 1 \
          --out <REPO_ROOT>/experiments/rq3/d4/${cell}-${pattern}.json
    " > "$log" 2>&1
    local rc=$?
    local t1=$(date +%s)
    local elapsed=$((t1 - t0))
    if [ -f "$out" ]; then
        echo "[$(date +%H:%M:%S)] DONE  $cell/$pattern in ${elapsed}s rc=$rc" >> "$MASTER"
    else
        echo "[$(date +%H:%M:%S)] FAIL  $cell/$pattern in ${elapsed}s rc=$rc (no JSON)" >> "$MASTER"
    fi
}

# Per-pattern serial queues running in parallel.
# Reason: CodeQL refuses concurrent analyze on the same DB (cache lock).
# Each pattern uses one KBH-Bench DB → run its 4 cells (C0..C3) serially,
# but run all 5 patterns in parallel.
# This guarantees zero cache-lock collisions while keeping 5x parallelism.
# MAX_JOBS arg is ignored under this dispatch model; effective concurrency = 5.

echo "[$(date +%H:%M:%S)] dispatch model: per-pattern serial, ${#PATTERNS[@]} patterns parallel" | tee -a "$MASTER"
echo "[$(date +%H:%M:%S)] total jobs: $(( ${#PATTERNS[@]} * ${#CELLS[@]} ))" | tee -a "$MASTER"

declare -a PIDS
for pat in "${PATTERNS[@]}"; do
    (
        for cell in "${CELLS[@]}"; do
            run_one "$cell" "$pat"
        done
    ) &
    PIDS+=($!)
done

# Wait for all per-pattern queues to drain
wait
echo "[$(date +%H:%M:%S)] ALL DONE" | tee -a "$MASTER"

# Aggregate
python3 << PYEOF
import json, os
from pathlib import Path
d4 = Path('$D4_DIR')
out = {'completed': [], 'missing': [], 'matrix': []}
for cell in ['C0','C1','C2','C3']:
    for pat in ['four-features-Lin','four-features-Lu','missing-check','delay-gfp','error-return']:
        p = d4 / f'{cell}-{pat}.json'
        if p.exists():
            try:
                d = json.load(open(p))
                a = d.get('aggregate', {})
                out['matrix'].append({
                    'cell': cell, 'pattern': pat,
                    'n_queries': a.get('n_queries'),
                    'pair_wise_mean': a.get('pair_wise_mean'),
                    'pair_wise_best': a.get('pair_wise_best'),
                    'recall_in_db_mean': a.get('recall_in_db_mean'),
                    'recall_in_db_best': a.get('recall_in_db_best'),
                    'fires_buggy_rate_mean': a.get('fires_buggy_rate_mean'),
                    'wall_s': d.get('wall_seconds'),
                })
                out['completed'].append(f'{cell}/{pat}')
            except Exception as e:
                out['missing'].append(f'{cell}/{pat} (parse err: {e})')
        else:
            out['missing'].append(f'{cell}/{pat}')
out['completed_count'] = len(out['completed'])
out['missing_count'] = len(out['missing'])
json.dump(out, open(d4 / 'run-summary.json', 'w'), indent=2)
print(f"completed: {out['completed_count']}, missing: {out['missing_count']}")
PYEOF

echo "[$(date +%H:%M:%S)] aggregate at $D4_DIR/run-summary.json" | tee -a "$MASTER"
