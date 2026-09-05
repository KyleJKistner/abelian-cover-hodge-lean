# Current manuscripts and historical sources

Start with these current revisions:

| Source | Review PDF | Exact scope |
|---|---|---|
| [general_all_powers.tex](general_all_powers.tex) | [PDF](../output/pdf/general_all_powers.pdf) | Every prime, every full elementary abelian branch family over P1, all powers of the very general Jacobian. Uses the Fermat transfer companion for odd primes and independent symplectic factors for p=2. |
| [fermat_determinant_transfer.tex](fermat_determinant_transfer.tex) | [PDF](../output/pdf/fermat_determinant_transfer.pdf) | Explicit algebraic direct summand of Fermat cohomology; Shioda's product theorem gives the mixed determinant classes by a classical-construction consequence. |
| [structural_extensions.tex](structural_extensions.tex) | [PDF](../output/pdf/structural_extensions.pdf) | Odd-exponent transfer criterion; unconditional all-powers HC for abelian covers of exponent dividing p^e (p odd), 3^a5^b or 3^a7^b. Also exact prime-family Hodge groups, exceptional classes, ring generators, distinct-prime products and degree-seven generalized HC. |
| [phase_I_revised.tex](phase_I_revised.tex) | [PDF](../output/pdf/phase_I_revised.pdf) | The restricted split odd-prime family: exact generic decomposition, endomorphisms, Hodge group and divisor generation on all powers. Also corrects the rational moving-part criterion. |
| [fusion_revised.tex](fusion_revised.tex) | [PDF](../output/pdf/fusion_revised.pdf) | Algebraicity of the explicitly defined balanced mixed determinant space for products of prime cyclic-cover Jacobians. The new general manuscript proves the generator hypothesis in its final all-powers application. |

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
tectonic --outdir build/tex manuscripts/general_all_powers.tex
tectonic --outdir build/tex manuscripts/phase_I_revised.tex
tectonic --outdir build/tex manuscripts/fusion_revised.tex
tectonic --outdir build/tex manuscripts/fermat_determinant_transfer.tex
tectonic --outdir build/tex manuscripts/structural_extensions.tex
```

The sources also use ordinary LaTeX packages and can be compiled with a
standard TeX installation. No license is inferred for the manuscript files
by their presence here.
