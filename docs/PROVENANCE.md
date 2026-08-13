# Provenance and reproducibility

The files under `manuscripts/` and `legacy/certificates/` are unmodified copies
of the recovered source package. The Lean files are a new, narrower artifact.

## Source hashes

| File | SHA-256 |
|---|---|
| `manuscripts/phase_I_complete.tex` | `6aef90d94b6184f610df91936977d2ef7737e9a90dd28c2e92c657694c9c3662` |
| `manuscripts/phase_II_complete.tex` | `9c9811c8ed8fa081b1849abce431df54eb28d8fded55c3d981e7cf737425ed12` |
| `manuscripts/phase_I_proof_ledger.md` | `787e12ed477f77f0ba62ba4dbd10eed249e43750d1169f6536d10eeb995ddcbd` |
| `manuscripts/phase_II_proof_ledger.md` | `e090d54aff66d96330eaeef3602078b356a2e4a1d046b528b845f1b8790aab60` |
| `legacy/certificates/phase_I_certificate.py` | `adf12fc99e1f045294f8172024faa60b488400d5a068819855c5698d6d0cad99` |
| `legacy/certificates/phase_I_certificate_report.json` | `a1d02b2058c4cc7af70d6083ed7e003a06bf453c2c842f62160a80bfce0ac297` |
| `legacy/certificates/phase_II_certificate.py` | `7e5358c2fb23eee6751bcbe1e178dc7d3b6bbb6b7a9b5c4805cee5535e99ee9e` |
| `legacy/certificates/phase_II_certificate_report.json` | `7aeb9663f9faf53345eefc2a5c8699e36e9a442fd4b4186cd72f87058f833b85` |

## Reproducibility classes

- **Lean layer:** pinned to Lean `v4.33.0` and mathlib commit
  `db584cd6d46c92f209a44c0f1c829460d327499d` (the `v4.33.0` tag). The legacy
  finite kernel is `Std`-only; newer concrete algebra uses focused mathlib
  imports. The resolved transitive revisions are recorded in
  `lake-manifest.json`, and CI builds plus independently checks the result.
- **Phase II Python layer:** its source is present, but it requires SymPy and
  the recovered package did not record an exact Python/SymPy environment. Its
  frozen JSON report should be treated as provenance until a lockfile is
  reconstructed and the report is regenerated.
- **Phase I Python layer:** not reproducible from this package because the
  imported core source is missing. See AF-3 in `AUDIT_FINDINGS.md`.

The missing Phase I core is expected to have SHA-256
`dd58de8adfae482319ccbfab2164bee2b5393ce27f0dbbef1c055a5784a67fff`.
If recovered, verify the hash before running it and record the interpreter and
dependency versions used.
