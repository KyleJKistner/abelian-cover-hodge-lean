# Current manuscripts and historical sources

Start with these current revisions:

| Source | Review PDF | Exact scope |
|---|---|---|
| [phase_I_revised.tex](phase_I_revised.tex) | [PDF](../output/pdf/phase_I_revised.pdf) | The restricted split odd-prime family: exact generic decomposition, endomorphisms, Hodge group and divisor generation on all powers. Also corrects the rational moving-part criterion. |
| [fusion_revised.tex](fusion_revised.tex) | [PDF](../output/pdf/fusion_revised.pdf) | Algebraicity of the explicitly defined balanced mixed determinant space for products of prime cyclic-cover Jacobians. A universal all-powers application retains a separate generator hypothesis. |

These are written proof drafts with named source inputs, not externally
refereed or Lean-formalized geometric theorems. See the
[repair overview](../docs/REPAIR_STATUS.md) and
[controlling claim matrix](../docs/CLAIMS.md).

The two `phase_*_complete.tex` files and two `phase_*_proof_ledger.md` files
are unchanged provenance copies. Their old completeness claims are superseded
by the current claim matrix and [audit findings](../docs/AUDIT_FINDINGS.md).
The [source manifest](../docs/PROVENANCE.md) records their hashes.

To compile a revision from the repository root with Tectonic:

```bash
mkdir -p build/tex
tectonic --outdir build/tex manuscripts/phase_I_revised.tex
tectonic --outdir build/tex manuscripts/fusion_revised.tex
```

The sources also use ordinary LaTeX packages and can be compiled with a
standard TeX installation. No license is inferred for the manuscript files
by their presence here.
