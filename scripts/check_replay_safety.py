#!/usr/bin/env python3
"""Check assertion preservation and rejection of one malformed fusion fixture.

The malformed case exists only in memory. The frozen fixture and original
Phase II script are never edited. This is a regression for the replay runner,
not an additional mathematical certificate.
"""

from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


PROBE = r'''
import copy
import json
from pathlib import Path
import runpy
import sys

scope = runpy.run_path(sys.argv[1], run_name="fusion_replay_probe")
fixture = json.loads(Path(sys.argv[2]).read_text())
case = copy.deepcopy(fixture["cases"][0])
# Replace the valid 3-to-2 node with 1-to-2 and reuse the first source slot.
case["pairs"][0][0] = [0, 0]
if sys.flags.optimize:
    raise RuntimeError("The replay runner did not disable Python optimization")
try:
    scope["check_tuple_case"](case)
except AssertionError:
    print(json.dumps({"malformed_fixture": "rejected", "optimize": sys.flags.optimize}))
else:
    raise RuntimeError("Malformed fusion fixture was accepted")
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    runner = ROOT / "scripts/replay_certificates.py"
    fusion = ROOT / "scripts/check_fusion.py"
    fixture = ROOT / "scripts/fixtures/fusion_cases.json"
    preserved = [fixture, ROOT / "legacy/certificates/phase_II_certificate.py"]
    before = {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
              for path in preserved}

    spec = importlib.util.spec_from_file_location("hodge_replay_under_test", runner)
    require(spec is not None and spec.loader is not None, "Cannot load replay runner")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    rows = []
    with tempfile.TemporaryDirectory(prefix="hodge-replay-safety-") as temporary:
        scratch = Path(temporary)
        probe = scratch / "malformed_fusion_probe.py"
        probe.write_text(PROBE)
        previous = os.environ.get("PYTHONOPTIMIZE")
        try:
            for label, optimization in (("normal_environment", None),
                                        ("optimized_environment", "1")):
                if optimization is None:
                    os.environ.pop("PYTHONOPTIMIZE", None)
                else:
                    os.environ["PYTHONOPTIMIZE"] = optimization
                output = scratch / (label + ".json")
                module.execute(probe, scratch, output, str(fusion), str(fixture))
                result = json.loads(output.with_suffix(".stdout.txt").read_text())
                require(result == {"malformed_fixture": "rejected", "optimize": 0},
                        f"Unexpected probe result for {label}: {result}")
                rows.append({"case": label, **result})
        finally:
            if previous is None:
                os.environ.pop("PYTHONOPTIMIZE", None)
            else:
                os.environ["PYTHONOPTIMIZE"] = previous

        for label, flags, optimization in (
            ("direct_optimized_flag", ["-O"], None),
            ("direct_optimized_environment", [], "1"),
        ):
            environment = os.environ.copy()
            environment.pop("PYTHONOPTIMIZE", None)
            if optimization is not None:
                environment["PYTHONOPTIMIZE"] = optimization
            destination = scratch / (label + ".json")
            result = subprocess.run(
                [sys.executable, *flags, str(fusion), "--output", str(destination)],
                env=environment, text=True, capture_output=True, check=False,
            )
            require(result.returncode != 0, f"{label} incorrectly succeeded")
            require("cannot run with optimized Python" in result.stderr,
                    f"{label} did not explain why optimized execution is rejected")
            require(not destination.exists(), f"{label} wrote a misleading report")
            rows.append({"case": label, "optimized_execution": "rejected"})

    after = {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest()
             for path in preserved}
    require(after == before, "Safety regression changed a preserved source")
    report = {"status": "PASS", "scope": "Replay assertion-preservation regression",
              "cases": rows, "preserved_sources_unchanged": before}
    serialized = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
    else:
        print(serialized, end="")


if __name__ == "__main__":
    main()
