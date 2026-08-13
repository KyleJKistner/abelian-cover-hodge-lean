# Phase II complete package

This package completes the elementary-abelian prime-exponent programme begun in the supplied Phase I manuscript.

## Main result

For the very general Jacobian in every full family of connected \((\mathbf Z/p)^m\)-covers of \(\mathbf P^1\), with \(p\) an odd prime, the package:

- computes the complete connected generic Hodge and Mumford-Tate groups, including the central torus, directly from the branch code;
- classifies every contraction and determinant/Weil Hodge tensor on every power;
- constructs compact-type fusion cycles representing every determinant relation;
- proves the rational Hodge conjecture for every power of the very general Jacobian.

The binary case follows from the full symplectic Phase I theorem.

## Files

- `phase_II_complete.pdf` - integrated Phase II paper.
- `phase_II_complete.tex` - LaTeX source.
- `phase_II_proof_ledger.md` - claim-by-claim proof and dependency ledger.
- `phase_II_certificate.py` - exact-arithmetic regression certificate.
- `phase_II_certificate_report.json` - frozen certificate output.
- `phase_I_complete.pdf`, `phase_I_complete.tex` - the Phase I theorem used by Phase II.
- `phase_I_proof_ledger.md`, `phase_I_certificate.py`, `phase_I_certificate_report.json` - Phase I audit material.

## Reproduction

Compile the paper with:

```bash
pdflatex -interaction=nonstopmode -halt-on-error phase_II_complete.tex
pdflatex -interaction=nonstopmode -halt-on-error phase_II_complete.tex
```

Run the certificate with:

```bash
python phase_II_certificate.py
```

The script requires Python 3 and SymPy. It rewrites `phase_II_certificate_report.json` and prints a compact summary.

## Frozen scope

Included: full families, very general fibers, elementary abelian deck group of prime exponent, full generic Hodge/Mumford-Tate group, all powers, and rational Hodge classes.

Excluded: composite exponent, special-fiber Mumford-Tate jumps, arbitrary nonabelian deck groups, and integral Hodge statements.

## Status

Complete working theorem package. The manuscript and certificates have been internally checked and the PDF has been compiled, rendered, and preflighted. It has not undergone external specialist peer review.
