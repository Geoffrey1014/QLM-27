"""Paths, model settings and iteration caps. Paths can be overridden through the environment."""

import os
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LINUX = Path(os.environ.get("QLM_LINUX", REPO / "linux"))      # Linux git tree holding the seed commits
CODEQL = os.environ.get("QLM_CODEQL", "codeql")                 # CodeQL CLI (tested with 2.25.6)
SEEDS = REPO / "data" / "seeds" / "seeds.json"
OUT = REPO / "out"
QL_DIR = Path(__file__).resolve().parent / "ql"

# Iteration caps (code/prompts/*.md)
POC_MAX_REGEN = 3          # PoC regenerations after the first attempt
PRED_MAX_ITERS = 4         # compile/expectation repair rounds per predicate
ASSEMBLE_MAX_ITERS = 4     # compile/oracle repair rounds for the final query
SEED_STUB_MAX_ITERS = 3    # rounds to make the verbatim seed slice compile

MODEL = os.environ.get("QLM_MODEL", "claude-opus-4-7")
TEMPERATURE = float(os.environ.get("QLM_TEMPERATURE", "0.2"))
MAX_TOKENS = int(os.environ.get("QLM_MAX_TOKENS", "8192"))
