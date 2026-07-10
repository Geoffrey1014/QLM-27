#!/usr/bin/env bash
# Orphan codeql java sweeper. Runs every 5min, kills any java process whose
# ppid=1 (= adopted by init = grandparent died = subprocess.run timeout
# but codeql env_argv chainer's java grandchild survived).
#
# Why ppid=1 (not etime > N): a fresh orphan can have small etime but is
# still leaking RSS. ppid=1 catches the actual condition (parent dead).
#
# Usage: bash orphan-watchdog.sh
# Stop:  Ctrl-C or kill the bash pid
#
# Logs:  $LOG_FILE
set -u

INTERVAL="${INTERVAL:-300}"  # 5 min
LOG_FILE="${LOG_FILE:-<REPO_ROOT>/experiments/rq3/d4/logs/orphan-watchdog.log}"
HOST_QLLLM=<REPO_ROOT>

mkdir -p "$(dirname "$LOG_FILE")"

trap 'echo "[$(date +%F\ %H:%M:%S)] watchdog stopping" | tee -a "$LOG_FILE"; exit 0' INT TERM

echo "[$(date +%F\ %H:%M:%S)] watchdog start; interval=${INTERVAL}s; log=$LOG_FILE" | tee -a "$LOG_FILE"

while true; do
  # ps inside container; awk picks java processes whose ppid is 1.
  # Print pid+etime+rss per orphan so the log is forensically useful.
  orphan_info=$(docker compose -f "$HOST_QLLLM/docker-compose.yml" exec -T qlllm bash -c \
    'ps -eo pid,ppid,etime,rss,comm 2>/dev/null | awk "/java/ && \$2==1 {printf \"%s %s %sKB\\n\", \$1, \$3, \$4}"' \
    2>/dev/null)

  if [ -n "$orphan_info" ]; then
    ts=$(date +%F\ %H:%M:%S)
    pids=$(echo "$orphan_info" | awk '{print $1}' | xargs)
    total_kb=$(echo "$orphan_info" | awk '{s+=$3} END {print s+0}')
    total_gb=$(awk "BEGIN {printf \"%.1f\", $total_kb/1024/1024}")
    echo "[$ts] KILL orphans: $pids   freed=${total_gb}GB" | tee -a "$LOG_FILE"
    echo "$orphan_info" | sed "s/^/    /" >> "$LOG_FILE"
    docker compose -f "$HOST_QLLLM/docker-compose.yml" exec -T qlllm bash -c \
      "echo '$pids' | xargs kill -9 2>&1" >> "$LOG_FILE" 2>&1
  fi
  # Silent on no-orphan rounds; just sleep and check again.
  sleep "$INTERVAL"
done
