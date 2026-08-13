# Phase I proof ledger

**Project:** Finite-abelian and elementary-p branch codes, exact generic monodromy blocks, and algebraic endomorphism defects  
**Date:** 10 August 2026  
**Status:** Complete self-contained **working theorem package** for the Phase I scope stated below. The manuscript has not undergone external specialist peer review.

## 1. Frozen scope

Phase I is complete in the following precise sense.

For every full family of connected finite abelian covers of $\mathbf P^1$ with fixed local monodromy, the package:

1. encodes the datum by its finite additive branch code;
2. determines the connected generic monodromy on the moving part of $H^1$;
3. classifies every diagonal relation between distinct character coordinates;
4. proves that every such cross-character relation is represented by an explicit algebraic quotient correspondence;
5. identifies connected monodromy with the derived centralizer of the saturated correspondence algebra and with the generic derived Hodge group.

For the split elementary-$p$ family
$$
X_{p,t}:\quad u^p=\frac{x}{x-t},\qquad v^p=x-1,
$$
the global Kummer involutions also saturate the internal standard-dual corners. The package therefore determines the complete generic endomorphism algebra, isogeny decomposition, Neron-Severi rank, derived Hodge group, and the rational Hodge ring of every power.

The following are not claimed in Phase I: the general Mumford-Tate central torus, an unsaturated internal standard-dual corner of an isolated disk factor, higher determinant/Weil tensors, special-fiber jumps, or arbitrary nonabelian deck groups.

## 2. Main theorem ledger

| Item | Result | Proof basis | Status / qualification |
|---|---|---|---|
| 1 | Branch-code anti-equivalence | Pontryagin duality and coordinate evaluation | Complete elementary proof. Every finite abelian datum is encoded by a finite subgroup of the sum-zero hyperplane with nonzero coordinate projections; elementary $p$-covers give full-support $p$-ary codes in $\mathbf 1^\perp$. |
| 2 | Moving-factor criterion | Chevalley-Weil, compact-integral monodromy, fixed part | Complete proof. Nonpositive character sectors become constant after finite etale base change; positive sectors are exactly the moving sectors. |
| 3 | Full simple projection | Published genus-zero cyclic-cover monodromy theorem of Rohde, as stated in Spelta-Tamborini; compatible Menet-Nguyen formulation | Imported published theorem with hypotheses matched in the manuscript: positivity is exactly the condition that both Hodge multiplicities are nonzero. |
| 4 | Semisimple block reduction | Lie-algebra Goursat argument | Complete proof in the manuscript. A connected semisimple subdirect product of adjoint simple groups is a product of graph diagonals. |
| 5 | Different-support separation | Pure braid forgotten on one quotient and nontrivial on the other | Complete proof. A graph relation cannot identify an identity action with a nontrivial reflection/unipotent action. |
| 6 | Same-support high-rank separation | Menet-Nguyen pair- and subset-twist spectra plus the standard/dual classification for $\mathfrak{sl}_n$ | Complete written proof. For support at least five, graph-related characters are equal or inverse, hence represent one PEL coordinate rather than a product defect. |
| 7 | Reduction to four-point rank two | Items 3-6 plus Lie-type comparison | Complete. No product-monodromy defect remains outside the four-point $A_1=C_1$ sector. |
| 8 | Exact Fricke fingerprint | Hypergeometric local exponents, Fricke identity, and an independent Fox-Gassner derivation | Complete proof. The fourth trace coordinate removes the apparent uniform half-period ambiguity. |
| 9 | Kummer rigidity | Exact fingerprint plus the half-shift lemma | Complete proof. Two dense disk local systems are projectively isomorphic exactly when their residue words differ by sign and a Klein-four double transposition. |
| 10 | Exact connected monodromy blocks | Goursat plus items 5-9 | Complete. Disk blocks are exactly Kummer orbits; the manuscript gives the closed defect formula and proves there are no other generic product defects. |
| 11 | Algebraization of every nontrivial disk intertwiner | Isomorphism of cyclic quotient covers after finite etale base change; pull-graph-push and character projection | Complete. The correct theorem is quotient-wise. A whole-code automorphism is not required and is false in general. |
| 12 | Exact cross-character Hodge-Hom corners | Schur's lemma, exact block theorem, Kummer matrix units, Galois descent | Complete. For distinct character coordinates, every very-general Hodge homomorphism is exactly an algebraic Kummer correspondence. |
| 13 | Saturated derived centralizer | Blockwise double-centralizer computation | Complete. The derived symplectic centralizer of the saturated algebra is exactly connected monodromy. |
| 14 | Generic derived Hodge group | Algebraicity of the saturated algebra and Andre normality | Complete. $\operatorname{Hg}^{\mathrm{der}}=\operatorname{Mon}^0$ on the moving part. This does not assert the full central torus. |
| 15 | Binary and ternary consequences | Exact Kummer-orbit classification | Complete. Binary codes have no diagonal merger; ternary disks have geometric self-conjugation but no merger of distinct coordinates. |
| 16 | Split-family Kummer geometry | Six exact rational-function identities and the explicit maps $\Phi,\Psi,\Omega$ | Complete. The maps are involutions, satisfy $\Phi\Psi=\Psi\Phi=\Omega$, and realize every oriented Kummer matrix unit. |
| 17 | Split-family endomorphism algebra | Crossed product $K\rtimes\operatorname{Gal}(K/K^+)$, exact rational monodromy blocks, double centralizer | Complete. The algebraic correspondence algebra equals the entire monodromy commutant, forcing equality with the very-general Hodge endomorphism algebra. |
| 18 | Split-family isogeny decomposition and simplicity | Primitive matrix idempotents and the exact endomorphism product | Complete. The simple factors have endomorphism field $K^+$, are absolutely simple, and are pairwise non-isogenous. |
| 19 | Neron-Severi formula | Rosati-fixed subspaces of $M_2(K^+)$ and $M_4(K^+)$ | Complete. The result is $\rho=(p-1)(5p-9)/2$. |
| 20 | All-powers rational Hodge theorem | First fundamental theorem for $\mathrm{SL}_2$, exact multiplicity algebra, Poincare divisor classes, faithful descent | Complete for the split family. Every derived-group invariant is in the divisor algebra; every Hodge class is therefore algebraic, and the Hodge ring equals the divisor algebra. |

## 3. The correction that made the theorem exact

An earlier formulation implicitly identified the full general Hodge endomorphism algebra with the saturated correspondence algebra. That was too strong without first computing the Mumford-Tate center: an isolated four-point disk coordinate may have an internal standard-dual corner that is invisible to the derived monodromy calculation.

The completed theorem makes the exact distinction:

- **General finite-abelian theorem:** complete classification and algebraization of all **cross-character** defects, together with the exact derived centralizer and derived Hodge group.
- **Split elementary-$p$ theorem:** the explicit global Kummer involutions saturate the internal corners as well, so the complete endomorphism algebra and all-powers Hodge theorem are unconditional.

This correction is substantive. It prevents the Phase I result from importing the Phase II central-torus problem through an unstated equality.

## 4. Exact certificate results

The two scripts are:

- `phase_I_certificate.py`
- `phase1src/p_ary_mt_defect_certificate.py`

They independently verify:

- the rank-two sphere quotient of the four-strand Gassner representation from Fox calculus;
- the exact commutator-trace half-shift formula;
- **7,077,120** active disk vectors through even denominator 96, with **0** failures of the Kummer conclusion;
- all full-support two-dimensional length-four codes at $p=3,5$, finding 0 defective $p=3$ orbits and 2 defective $p=5$ orbits;
- the six split-family rational-function identities;
- the full involution, composition, and deck-conjugation relations for $\Phi,\Psi,\Omega$;
- the block, genus, decomposition-dimension, endomorphism-dimension, and Neron-Severi formulas for every odd prime through 101.

Frozen hashes recorded in `phase_I_certificate_report.json`:

- manuscript SHA-256: `6aef90d94b6184f610df91936977d2ef7737e9a90dd28c2e92c657694c9c3662`;
- core certificate SHA-256: `dd58de8adfae482319ccbfab2164bee2b5393ce27f0dbbef1c055a5784a67fff`;
- wrapper certificate SHA-256: `adf12fc99e1f045294f8172024faa60b488400d5a068819855c5698d6d0cad99`.

The computation is a regression certificate. It does not replace the written projection, Goursat, high-rank reconstruction, descent, double-centralizer, or invariant-theory arguments.

## 5. Remaining review risk

The package is self-contained at the theorem level, but it is not peer reviewed. The highest-value external checks are:

1. the projective-lift and pair/triple-twist reconstruction in the high-rank separation lemma;
2. the passage from Kummer quotient isomorphisms to rational descended correspondence corners;
3. the rational double-centralizer calculation in the split family;
4. the invariant-theory-to-divisor-algebra passage for all powers.

These are review targets, not unfilled dependencies: each is proved in the integrated manuscript.
