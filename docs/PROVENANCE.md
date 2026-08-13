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
  The workflow also pins `actions/checkout` to
  `11d5960a326750d5838078e36cf38b85af677262` (`v4`) and
  `leanprover/lean-action` to
  `38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9` (`v1`). The independent
  checker script pins `lean4export` to its `v4.33.0` commit
  `15f6055e299ad5b89345e533cc2192f4cc00f659`, `nanoda_lib` to
  `418320295890faed83a96fd97907b12a3b6728c2`, and Rust to `1.97.1`; Cargo's
  locked dependency checksums supply the remaining Rust package pins. This
  repository-owned step avoids the stale `nanoda_lib/debug` clone in
  [`lean-action` issue 169](https://github.com/leanprover/lean-action/issues/169);
  the pinned checker includes the merged NDJSON parser from
  [`nanoda_lib` PR 7](https://github.com/ammkrn/nanoda_lib/pull/7). Its config
  also requires the headline scaffold declaration to occur in the exported
  environment, so an empty or wrong-module export cannot pass vacuously.
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

## External source pins introduced by the Lean audit

The Phase I full-projection interface and its arithmetic hypothesis match are
pinned to Menet--Nguyen, *Representations of braid groups via cyclic covers of
the sphere: Zariski closure and arithmeticity*,
[`arXiv:2310.10401v3`](https://arxiv.org/abs/2310.10401v3), 16 November 2024,
Definition 1.1(a) (p. 3), Theorems 2.1--2.2 (p. 8), Theorem 2.5, its following
reflection discussion, and Corollary 2.7 (p. 9), Theorem 2.8 (p. 10), Lemma
3.9 (pp. 14--15), Corollary 3.11 (p. 16), and Theorem 5.1 with its standing
Section 5 assumptions (p. 24). `External/MenetNguyen.lean` currently models
the row data and the 2.5/2.7/2.8/5.1 interfaces; exact Theorem 2.2 Gram data and
the Lemma 3.9/Corollary 3.11 subset-eigenspace package remain to be added. The
repository takes sourced implications only as explicit parameter data;
`Mathlib/MenetNguyenGood.lean` proves the separate case-(a) inequality match.

Menet--Nguyen uses `q = exp(-2*pi*i*k/d)`, whereas the Phase I manuscript writes
positive-exponent `t_i`. Their root/sign conversion is a project-side proof
obligation, not a citation. The printed final branch of Theorem 2.8 contains an
undefined `q_l`; the interface records the inferred `g_l` correction and
restricts to `r < n`, where the displayed cases do not overlap.

The Aoki interface is pinned to Theorem A, pp. 23--24 of
[*On some arithmetic problems related to the Hodge cycles on the Fermat
varieties*](https://doi.org/10.1007/BF01458703), with the even-length premise
retained. Its one-page erratum, Math. Ann. 267 (1984), p. 572, was checked: it
corrects only the statement of Theorem B in the introduction, so Theorem A is
unaffected. Stable copies are indexed by
[EuDML](https://eudml.org/doc/163917) and the
[Göttingen resolver](http://resolver.sub.uni-goettingen.de/purl?GDZPPN002325268).
The Schoen interface is pinned to Section 2, Theorem 2.0, p. 11 and
the Section 3 setup and Corollary 3.1, pp. 24--25 of
[*Hodge classes on self-products of a variety with an
automorphism*](https://www.numdam.org/item/CM_1988__65_1_3_0.pdf).

Still pending exact primary-source locators are the particular forms used for
Chevalley--Weil, Deligne fixed part, Andre normality, Weyl invariant theory,
ACV smoothing, compact-type Picard, smooth-proper comparison, Chow
specialization, and the weight-one realization package. Their current Lean
contexts are prospective interfaces, not a completed or wired trust boundary.
