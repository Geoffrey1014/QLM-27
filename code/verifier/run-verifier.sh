#!/bin/bash
# JAWS seed<->POC consistency verifier — v1 calibration runner.
#
# Usage:
#   run-verifier.sh <scenario_name> <seed_src.c> <poc_src.c>
#
# Effect:
#   1. Stages the two source files into a workdir as `seed_<scenario>.c`
#      and `poc_<scenario>.c` so the QL query can identify them by name.
#   2. Builds a 2-TU mini-DB with gcc.
#   3. Runs verifier-v1.ql and prints the verdict rows.
#
# Designed to be invoked inside the qlllm container.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CODEQL="${CODEQL:-<REPO_ROOT>/codeql-2.25.6/codeql}"

if [ $# -ne 3 ]; then
  echo "usage: $0 <scenario_name> <seed_src.c> <poc_src.c>" >&2
  exit 2
fi

SCEN="$1"
SEED_SRC="$2"
POC_SRC="$3"

if [ ! -f "$SEED_SRC" ] || [ ! -f "$POC_SRC" ]; then
  echo "missing input file(s)" >&2
  exit 2
fi

WORK="$SCRIPT_DIR/calibration-work/$SCEN"
DB="$WORK/db"
mkdir -p "$WORK"
rm -rf "$DB" "$WORK/seed_${SCEN}.c" "$WORK/poc_${SCEN}.c"

cp "$SEED_SRC" "$WORK/seed_${SCEN}.c"
cp "$POC_SRC"  "$WORK/poc_${SCEN}.c"

# Build 2-TU DB. Use -O0 -w to disable optimisation and silence warnings.
# CodeQL splits --command on whitespace, so we wrap the two compile
# steps in a tiny shell script that CodeQL can execute as a single
# token.
BUILD_SH="$WORK/build.sh"
cat > "$BUILD_SH" <<EOF
#!/bin/bash
set -e
gcc -O0 -w -c seed_${SCEN}.c -o /tmp/seed_${SCEN}.o
gcc -O0 -w -c poc_${SCEN}.c -o /tmp/poc_${SCEN}.o
EOF
chmod +x "$BUILD_SH"

(
  cd "$WORK" || exit 1
  $CODEQL database create "$DB" --language=cpp \
    --command="$BUILD_SH" \
    --source-root=. --overwrite > "$WORK/build.log" 2>&1
) || { echo "BUILD FAILED for $SCEN (see $WORK/build.log)"; exit 1; }

OUT="$WORK/verdict.csv"
$CODEQL database analyze "$DB" "$SCRIPT_DIR/verifier-v1.ql" \
  --format=csv --output="$OUT" --rerun > "$WORK/analyze.log" 2>&1
rc=$?
if [ $rc -ne 0 ]; then
  echo "ANALYZE FAILED for $SCEN (see $WORK/analyze.log)"
  exit 1
fi

# Print scenario header + verdict rows. CSV columns from a `problem`
# query are: name,description,severity,message,path,startLine,...
# We extract the `message` column (4) using Python's csv module for
# correct quoting.
echo "===== $SCEN ====="
if [ -s "$OUT" ]; then
  python3 -c "
import csv, sys
with open('$OUT') as fh:
    rdr = csv.reader(fh)
    for row in rdr:
        if len(row) >= 4:
            print(row[3])
"
else
  echo "(no verdict rows — empty result; treat as VERIFIER ERROR)"
fi
