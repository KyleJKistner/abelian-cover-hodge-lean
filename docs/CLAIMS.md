# Claim matrix

This is the controlling claim ledger for the repository. Status words mean:

- **FORMALIZED:** proved by Lean in `Verified/` without project postulates.
- **PARTIAL FORMALIZED:** a stated finite/arithmetic subclaim is proved, not the
  full geometric ledger item.
- **PUBLISHED INPUT:** represented by a named field of `PublishedInputs`.
- **MANUSCRIPT INPUT:** represented by a named field of
  `UnformalizedDeductions` or is
  otherwise still part of the unformalized research bridge.
- **SCAFFOLD ONLY:** Lean checks the logical composition, but the statement uses
  abstract propositions that erase the mathematics an auditor must inspect.
- **REGRESSION ONLY:** checked for an explicitly bounded finite sample; it must
  not be read as a universal theorem.
- **BLOCKED:** the supplied formulation contains a known defect.

## Lean headline declarations

| Declaration | Status | Exact content |
|---|---|---|
| `pairResidues_opposite` | FORMALIZED | A list built as `(x,-x)` pairs has symmetric residue multiplicities. |
| `pairResidues_balanced` | FORMALIZED | Nonzero explicit opposite pairs satisfy the doubled balance equation. This is the easy direction, not Aoki's converse. |
| `splitWord_rowSignature_zero` | FORMALIZED | A nonzero row `(u,v,-u,-v)` has zero row signature for every nonzero modulus. |
| `fusion_rank_identity` | FORMALIZED | Tree-edge deletion preserves the stated compact-type `K`-rank arithmetic. |
| `mixed_relation_all_embeddings` | FORMALIZED | The two frozen `p=5` signature columns cancel exactly. |
| `mixed_galois_balance` | FORMALIZED | The frozen mixed `p=5` concatenation passes every nonzero Galois-row balance check. |
| `mixed_fusion_rank` | FORMALIZED | The frozen two-component fusion has rank four. |
| `split_regression_p3/p5/p7` | REGRESSION ONLY | Exact enumeration for the three stated primes. |
| `rationalHodge_allPowers_of_inputs` | SCAFFOLD ONLY | Pure composition along the direct zero-signature/fusion route; its abstract manuscript-specific arrows are not formalized mathematics. |

## Phase I ledger

| Item | Repository status | Audit interpretation |
|---|---|---|
| I.1 Branch-code anti-equivalence | PARTIAL FORMALIZED | `spanCode`, modular word operations, support, and branch-sum predicates are executable. The categorical/finite Pontryagin-dual equivalence is not formalized. |
| I.2 Moving-factor criterion | PUBLISHED INPUT + MANUSCRIPT INPUT | Chevalley–Weil/fixed-part ingredients and their exact geometric application are not in Lean. |
| I.3 Full simple projection | PUBLISHED INPUT | Must be pinned to the exact cyclic-cover monodromy theorem and hypotheses. |
| I.4 Semisimple block reduction | MANUSCRIPT INPUT | Lie-algebra Goursat and integration are not formalized. |
| I.5 Different-support separation | MANUSCRIPT INPUT | Geometric local-system argument absent. |
| I.6 Same-support high-rank separation | MANUSCRIPT INPUT | Twist spectra and standard/dual classification absent. |
| I.7 Reduction to four-point rank two | MANUSCRIPT INPUT | Depends on I.3–I.6. |
| I.8 Exact Fricke fingerprint | MANUSCRIPT INPUT | Legacy Phase I core certificate is missing; no Lean theorem. |
| I.9 Kummer rigidity | MANUSCRIPT INPUT | Exact local-system identification is not formalized. |
| I.10 Exact connected monodromy blocks | MANUSCRIPT INPUT | Exposed through `phaseIExactBlocks`. |
| I.11 Algebraization of disk intertwiners | MANUSCRIPT INPUT | Quotient-cover isomorphism, graph nonvanishing, and descent absent. |
| I.12 Cross-character Hodge-Hom corners | MANUSCRIPT INPUT | Schur/Kummer/Galois application absent. |
| I.13 Saturated derived centralizer | MANUSCRIPT INPUT | Abstract and geometric double-centralizer work absent. |
| I.14 Generic derived Hodge group | MANUSCRIPT INPUT | André normality application absent. |
| I.15 Binary/ternary consequences | REGRESSION ONLY | Some finite word behavior is executable; the monodromy consequence is not Lean proved. |
| I.16 Split-family Kummer geometry | PARTIAL FORMALIZED | Split-row signature arithmetic is proved. The six rational maps and their extension to projective covers are not. |
| I.17 Split endomorphism algebra | MANUSCRIPT INPUT | Crossed product and exact geometric commutant absent. |
| I.18 Split isogeny decomposition | MANUSCRIPT INPUT | Idempotent, simplicity, and non-isogeny claims absent. |
| I.19 Néron–Severi formula | REGRESSION ONLY | Any surviving integer checks do not prove the Rosati/endomorphism inputs. |
| I.20 Split all-powers Hodge theorem | MANUSCRIPT INPUT | Not claimed as Lean verified. |

## Phase II ledger

| Item | Repository status | Audit interpretation |
|---|---|---|
| P2.1 Signature formulas | PARTIAL FORMALIZED + PUBLISHED INPUT | `qValue`, `signatureAt`, and exact columns are defined and computed; identifying them with Hodge multiplicities is `chevalleyWeil`. |
| P2.2 `K`-rank `s(c)-2` | PARTIAL FORMALIZED | Support/rank arithmetic is represented, but the rational Hodge factor identification is not. |
| P2.3 Toric-factor exclusion | MANUSCRIPT INPUT | Torelli/dominance argument absent. |
| P2.4 Derived group equality | MANUSCRIPT INPUT | Carried by `phaseIExactBlocks`. |
| P2.5 Determinant quotient lattice | BLOCKED | Unsaturated relation lattice can have torsion; see AF-1. |
| P2.6 Kummer relations in signature kernel | MANUSCRIPT INPUT | Geometric variation isomorphisms absent. |
| P2.7 Central torus annihilator | MANUSCRIPT INPUT | Carried by `hodgeCircleAndCentralizer`; downstream of AF-1. |
| P2.8 Full Hodge group | MANUSCRIPT INPUT | Depends on P2.4/P2.7. |
| P2.9 Isolated disk criterion | BLOCKED | Character is `±ε_c`, not `2ε_c`; also downstream of AF-1. See AF-2. |
| P2.10 Tensor invariant generators | PUBLISHED INPUT + MANUSCRIPT INPUT | `weylInvariantTheory` is explicit; exact multiplicity/Kummer identification still uses Phase I. |
| P2.11 Determinant word criterion | PARTIAL FORMALIZED / REGRESSION ONLY | Exact signed words and finite signature checks exist; the universal direct Hodge-bidegree criterion is not proved. It need not depend on P2.7. |
| P2.12 Prime relations are opposite-paired | PARTIAL FORMALIZED + PUBLISHED INPUT | Opposite-paired implies balance is proved; balanced implies opposite-paired is `aokiPrime`. The general relation-to-balance reduction remains to be formalized. |
| P2.13 Compact-type gluing | PARTIAL FORMALIZED + MANUSCRIPT INPUT | Pair/rank bookkeeping is proved; global admissible-cover construction is `fusionGluing`. |
| P2.14 Smoothing and rank | PARTIAL FORMALIZED + PUBLISHED INPUT | Rank identity is proved; deformation is `acvSmoothing` and must match the exact global datum. |
| P2.15 Schoen cycles | PUBLISHED INPUT + MANUSCRIPT INPUT | `schoenSimpleCurve` is separate from the extra `primitiveEqWholeForPrimeP1` bridge. |
| P2.16 Specialization | PUBLISHED INPUT + MANUSCRIPT INPUT | General cycle specialization is separate from exact determinant compatibility. |
| P2.17 Determinant relations algebraic | CONDITIONAL | Follows only after P2.12–P2.16 interfaces are discharged. Mixed `p=5` is arithmetic regression, not cycle construction. |
| P2.18 All rational Hodge classes algebraic | SCAFFOLD ONLY | The direct route avoids P2.5/P2.7/P2.9, but Phase I, tensor reduction, fusion geometry, and specialization still require concrete formal proofs. |
| P2.19 Binary divisor generation | MANUSCRIPT INPUT | Depends on the binary Phase I theorem and symplectic invariant theory. |

## Explicit nonclaims

The repository does not establish the integral Hodge conjecture, composite
exponent, special-fiber jumps, nonabelian deck groups, computable Chow-cycle
formulas, or the separate PEL/Weil-eightfold deformation claim.
