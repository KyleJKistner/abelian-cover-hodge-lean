# Legacy certificates

These four Python/JSON files are unchanged provenance artifacts.

- The original Phase II report is now reproduced byte for byte with pinned
  SymPy 1.14.0 and mpmath 1.3.0; the first successful local replay used Python
  3.14.6.
- Phase I's wrapper still imports a missing core source. Its frozen report is
  not claimed as reproduced. The rewritten split-family argument bypasses the
  missing core and has a separate new checker.

Run `python scripts/replay_certificates.py` from the repository root in the
pinned environment. It stages the original Phase II inputs in a temporary
folder, checks all source hashes and leaves these originals unchanged.
Current reports go to `build/audit/`. See
[provenance](../../docs/PROVENANCE.md) for exact hashes and
[the repair overview](../../docs/REPAIR_STATUS.md) for the new checks.

The Lean verified layer is independent of these scripts. A finite report does
not prove the full manuscript theorem.
