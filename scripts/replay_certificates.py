#!/usr/bin/env python3
"""Replay the available certificates without changing preserved sources.

The old Phase I core is still missing. Its original full report is never
described as reproduced. New repair checks are separate from the byte-exact
Phase II replay and never substitute for a geometric proof.
"""

from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.metadata
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FROZEN = {
    "manuscripts/phase_I_complete.tex": "6aef90d94b6184f610df91936977d2ef7737e9a90dd28c2e92c657694c9c3662",
    "manuscripts/phase_II_complete.tex": "9c9811c8ed8fa081b1849abce431df54eb28d8fded55c3d981e7cf737425ed12",
    "manuscripts/phase_I_proof_ledger.md": "787e12ed477f77f0ba62ba4dbd10eed249e43750d1169f6536d10eeb995ddcbd",
    "manuscripts/phase_II_proof_ledger.md": "e090d54aff66d96330eaeef3602078b356a2e4a1d046b528b845f1b8790aab60",
    "legacy/certificates/phase_I_certificate.py": "adf12fc99e1f045294f8172024faa60b488400d5a068819855c5698d6d0cad99",
    "legacy/certificates/phase_I_certificate_report.json": "a1d02b2058c4cc7af70d6083ed7e003a06bf453c2c842f62160a80bfce0ac297",
    "legacy/certificates/phase_II_certificate.py": "7e5358c2fb23eee6751bcbe1e178dc7d3b6bbb6b7a9b5c4805cee5535e99ee9e",
    "legacy/certificates/phase_II_certificate_report.json": "7aeb9663f9faf53345eefc2a5c8699e36e9a442fd4b4186cd72f87058f833b85",
}


def digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def verify_pdf_manifest() -> dict:
    path = ROOT / "output/pdf/manifest.json"
    data = json.loads(path.read_text())
    artifacts = data["artifacts"]
    required_sources = {"manuscripts/phase_I_revised.tex", "manuscripts/fusion_revised.tex"}
    if not artifacts or not required_sources.issubset(
        {artifact["source"] for artifact in artifacts}
    ):
        raise RuntimeError("PDF manifest must include both revised manuscripts")
    for artifact in artifacts:
        for kind in ("source", "pdf"):
            relative = artifact[kind]
            if digest(ROOT / relative) != artifact[kind + "_sha256"]:
                raise RuntimeError(f"PDF manifest hash mismatch: {relative}; rebuild the review PDFs")
    return {"status": "source and PDF hashes verified", "manifest_sha256": digest(path),
            "artifacts": artifacts}


def execute(script: Path, cwd: Path, output: Path, *arguments: str) -> None:
    result = subprocess.run(
        [sys.executable, "-E", str(script), *arguments], cwd=cwd,
        text=True, capture_output=True, check=False,
    )
    output.with_suffix(".stdout.txt").write_text(result.stdout)
    output.with_suffix(".stderr.txt").write_text(result.stderr)
    if result.returncode:
        # Keep the decisive failure visible in CI as well as the local logs.
        if result.stdout:
            print(result.stdout[-8000:], file=sys.stderr)
        if result.stderr:
            print(result.stderr[-8000:], file=sys.stderr)
        raise RuntimeError(
            f"{script.name} failed with exit code {result.returncode}; "
            f"see {output.with_suffix('.stderr.txt')}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "build" / "audit")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest_path = output / "replay_manifest.json"
    # A failed replay must not leave an old successful manifest in place.
    manifest_path.unlink(missing_ok=True)

    versions = {name: importlib.metadata.version(name) for name in ("sympy", "mpmath")}
    if versions != {"sympy": "1.14.0", "mpmath": "1.3.0"}:
        raise RuntimeError("Install the pinned requirements-audit.txt before replaying")
    for relative, expected in FROZEN.items():
        if digest(ROOT / relative) != expected:
            raise RuntimeError(f"Preserved source hash changed: {relative}")
    pdf_artifacts = verify_pdf_manifest()

    legacy_report = output / "phase_II_certificate_report.json"
    with tempfile.TemporaryDirectory(prefix="hodge-phase-II-") as temporary:
        scratch = Path(temporary)
        original_script = ROOT / "legacy/certificates/phase_II_certificate.py"
        shutil.copy2(original_script, scratch / original_script.name)
        for name in ("phase_I_complete.tex", "phase_II_complete.tex"):
            shutil.copy2(ROOT / "manuscripts" / name, scratch / name)
        execute(scratch / original_script.name, scratch, legacy_report)
        regenerated = scratch / "phase_II_certificate_report.json"
        if digest(regenerated) != FROZEN["legacy/certificates/phase_II_certificate_report.json"]:
            shutil.copy2(regenerated, output / "phase_II_mismatched_report.json")
            raise RuntimeError("Phase II replay differs from the preserved report")
        shutil.copy2(regenerated, legacy_report)

    repair_reports = []
    for name in ("check_phase_i.py", "check_fusion.py", "check_replay_safety.py"):
        script = ROOT / "scripts" / name
        destination = output / (script.stem + ".json")
        destination.unlink(missing_ok=True)
        execute(script, ROOT, destination, "--output", str(destination))
        # Require a readable result, not merely a zero process status.
        json.loads(destination.read_text())
        repair_reports.append({
            "script": str(script.relative_to(ROOT)), "script_sha256": digest(script),
            "report": destination.name, "report_sha256": digest(destination),
        })

    manifest = {
        "python": platform.python_version(), "dependencies": versions,
        "preserved_sources": FROZEN,
        "pdf_artifacts": pdf_artifacts,
        "phase_II": {"status": "byte-identical replay", "sha256": digest(legacy_report)},
        "phase_I_original": {
            "status": "not reproduced: imported original core is absent",
            "missing_core_sha256": "dd58de8adfae482319ccbfab2164bee2b5393ce27f0dbbef1c055a5784a67fff",
        },
        "repair_checks": repair_reports,
        "scope": "Exact bounded arithmetic and source integrity; no geometric proof certification",
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "manifest": str(manifest_path)}, indent=2))


if __name__ == "__main__":
    main()
