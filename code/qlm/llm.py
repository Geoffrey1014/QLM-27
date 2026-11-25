"""LLM access. The pipeline only ever sends one system prompt plus one user message and
reads back text; every call is traced to <trace_dir>/NN-<stage>.json."""

import json
import os
import shutil
import subprocess
import time
from pathlib import Path

from . import config


class LLM:
    """Backend "cli" (default) runs `claude -p` with tools disabled on the claude.ai
    subscription login. Backend "api" uses the Anthropic SDK and ANTHROPIC_API_KEY (billed
    API credit; lets temperature be set). "auto" picks cli when the `claude` CLI exists."""

    def __init__(self, trace_dir: Path | None = None, backend: str = "auto",
                 model: str = config.MODEL, temperature: float = config.TEMPERATURE,
                 max_tokens: int = config.MAX_TOKENS):
        if backend == "auto":
            backend = "cli" if shutil.which("claude") else "api"
        if backend == "cli" and not shutil.which("claude"):
            raise RuntimeError("no ANTHROPIC_API_KEY and no `claude` CLI on PATH")
        self.backend, self.model = backend, model
        self.temperature, self.max_tokens = temperature, max_tokens
        self.trace_dir = trace_dir
        self.calls = 0
        if backend == "api":
            import anthropic
            self._client = anthropic.Anthropic()

    def __call__(self, stage: str, system: str, user: str) -> str:
        self.calls += 1
        t0 = time.time()
        text = self._api(system, user) if self.backend == "api" else self._cli(system, user)
        if self.trace_dir:
            self.trace_dir.mkdir(parents=True, exist_ok=True)
            (self.trace_dir / f"{self.calls:02d}-{stage}.json").write_text(json.dumps({
                "stage": stage, "backend": self.backend, "model": self.model,
                "temperature": self.temperature if self.backend == "api" else None,
                "seconds": round(time.time() - t0, 1),
                "system": system, "user": user, "response": text,
            }, indent=1))
        return text

    def _api(self, system: str, user: str) -> str:
        msg = self._client.messages.create(
            model=self.model, max_tokens=self.max_tokens, temperature=self.temperature,
            system=system, messages=[{"role": "user", "content": user}])
        return "".join(b.text for b in msg.content if b.type == "text")

    def _cli(self, system: str, user: str) -> str:
        # The CLI does not expose temperature; the trace records it as null. Drop the API
        # key so the CLI uses its own login instead of the (possibly unfunded) key.
        env = {k: v for k, v in os.environ.items() if k != "ANTHROPIC_API_KEY"}
        out = subprocess.run(
            ["claude", "-p", "--model", self.model, "--system-prompt", system,
             "--tools", "", "--strict-mcp-config", "--no-session-persistence",
             "--output-format", "json"],
            input=user, capture_output=True, text=True, timeout=1800, env=env)
        if out.returncode != 0:
            # usage-limit errors come back on stdout (JSON with is_error), not stderr
            raise RuntimeError(f"claude -p failed (rc={out.returncode}): "
                               f"{out.stderr[-1000:]} {out.stdout[-1000:]}")
        res = json.loads(out.stdout)
        if res.get("is_error"):
            raise RuntimeError(f"claude -p error: {res.get('result')}")
        return res["result"]


def strip_fences(text: str) -> str:
    """Drop a surrounding ``` fence if the model added one despite instructions."""
    t = text.strip()
    if t.startswith("```"):
        t = t.split("\n", 1)[1] if "\n" in t else ""
        if t.rstrip().endswith("```"):
            t = t.rstrip()[:-3]
    return t.strip() + "\n"
