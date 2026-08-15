# Claim matrix

This is the controlling claim ledger for the repository. Status words mean:

- **FORMALIZED:** proved by Lean without project postulates, whether the
  declaration lives in `Verified/`, `Mathlib/`, or another project module.
- **PARTIAL FORMALIZED:** a stated finite/arithmetic subclaim is proved, not the
  full geometric ledger item.
- **TYPED SOURCE INTERFACE:** represented by a named assumption type rather
  than a global declaration. The row states whether its primary-source
  locator and mathematical model are pinned or still prospective. This status
  is not a Lean proof and does not imply peer review.
- **EXPLICIT INPUT TYPE:** a published theorem is represented as data that a
  caller must supply, with no global declaration asserting it.
- **MANUSCRIPT INPUT:** represented by a named field of
  `UnformalizedDeductions` or is
  otherwise still part of the unformalized research bridge.
- **SCAFFOLD ONLY:** Lean checks the logical composition, but the statement uses
  abstract propositions that erase the mathematics an auditor must inspect.
- **CONDITIONAL:** follows once the separately named citation and project
  obligations in that row are supplied.
- **REGRESSION ONLY:** checked for an explicitly bounded finite sample; it must
  not be read as a universal theorem.
- **BLOCKED:** the supplied formulation contains a known defect.

## Lean headline declarations

| Declaration | Status | Exact content |
|---|---|---|
| `pairResidues_opposite` | FORMALIZED | A list built as `(x,-x)` pairs has symmetric residue multiplicities. |
| `pairResidues_balanced` | FORMALIZED | Nonzero explicit opposite pairs satisfy the doubled balance equation. This is the easy direction, not Aoki's converse. |
| `integralDeterminantSignatureAt_eq_zero_iff_galoisBalanced` | FORMALIZED | The additive integer signature vanishes exactly when the literal concatenated residue word satisfies the division-free balance equation, under explicit per-word divisibility. |
| `integralRowSignature_negativeWord` | FORMALIZED | Negating a branch row negates its integer signature. |
| `pairResidues_aokiBalanced` | FORMALIZED | For prime modulus, an explicit list of nonzero opposite pairs is balanced at every nonzero Galois row. |
| `aokiBalanced_length_even_of_prime_ne_two` | FORMALIZED | For every prime modulus other than two, the doubled all-row balance equation forces the even-length premise required by Aoki. |
| `OppositePairingWitness.aokiBalanced` | FORMALIZED | The all-row balance result is invariant under an explicit list permutation witness. |
| `External.AokiPrimeBalanceInput` | EXPLICIT INPUT TYPE | Focused proposition-valued leaf for the prime `B = D` statement on Aoki p. 24, credited there to W. Parry. It exposes prime modulus, branch sum, nonzero entries, even length at least four, unit-row balance, and an existential opposite-pairing conclusion. The checked 1984 erratum affects only Theorem B. |
| `Bridge.determinantResidues_isAokiBalanced` | FORMALIZED | Branch validity of the unsigned signed-word terms proves every scaled divisibility premise; all-row zero integral signature therefore makes the literal filtered determinant residue tuple Aoki-balanced. |
| `Bridge.determinantResidues_oppositePairing_of_aokiPrime` | FORMALIZED + EXPLICIT INPUT TYPE | For prime modulus other than two, Lean proves literal residue nonzeroness, branch sum, even length, and the unit-row restriction. Empty and two-entry tuples are paired directly; only the length-at-least-four branch uses `External.AokiPrimeBalanceInput`, followed by explicit `Classical.choice`. This does not identify a Hodge tensor with the signed-word input. |
| `PrimeBranchDatum.evaluationLinearMap_injective` | FORMALIZED | Spanning prime inertia vectors make the concrete character-evaluation map injective. |
| `PrimeBranchDatum.finrank_evaluationCode` | FORMALIZED | The mathlib-native evaluation code has dimension `m`; zero-sum containment and full support are also proved. |
| `FullSupportZeroSumCode.evaluationCode_toPrimeBranchDatum` | FORMALIZED | Restricting ambient coordinates reconstructs intrinsic inertia functionals from any full-support zero-sum code; every deck-coordinate choice recovers exactly that code. |
| `PrimeBranchDatum.reconstructed_inertia` | FORMALIZED | The coordinate/code round trip recovers every original inertia vector. This is finite linear algebra, not a classification of covers. |
| `PrimeBranchDatum.evaluation_isBranchWord` | FORMALIZED | Every evaluated character obeys the product-one branch-sum relation, so exact numerator divisibility and signature negation apply. |
| `MenetNguyenGood.positiveHodgePair_iff_goodSequenceCaseA` | FORMALIZED | On nonzero support and at a unit row, positivity of both arithmetic Hodge multiplicities is equivalent to Definition 1.1(a)'s strict rational sum bounds. It proves no monodromy conclusion. |
| `MenetNguyen.SourceInputs` | TYPED SOURCE INTERFACE | Bundles `Theorem2_5Input`, `NontrivialPairReflectionSpectrumInput`, `Corollary2_7Input`, `Theorem2_8Input`, and `Theorem5_1CaseAInput`. Concrete labels, unit row, root-row alignment, and geometric operator-identification premises are exposed and the locators are pinned. Theorem 2.8's printed undefined `q_l` is represented by the inferred `g_l` correction and remains a source-clarification item; Theorem 2.2 and the subset-eigenspace package remain unmodeled. |
| `MenetNguyen.ManuscriptBridgeObligations` | MANUSCRIPT INPUT | Keeps the positive/negative root convention and pair/prefix nonidentity-unipotent claims out of the source bundle. These must become Lean proofs, not final assumptions. |
| `MenetNguyen.theorem5_1_caseA_of_positiveHodgePair` | FORMALIZED + TYPED SOURCE INTERFACE | The proved arithmetic bridge supplies exactly Definition 1.1(a); every other Theorem 5.1 premise and the source input remain explicit arguments. |
| `Signature.p_dvd_qNumerator` / `Signature.delta_neg_word` | FORMALIZED | Genuine `ZMod p` branch sums give exact numerator divisibility and negation of the integral signature. |
| `Signature.determinantSignatureMap` | FORMALIZED | Determinant exponent signature is bundled as a `ℤ`-linear map. |
| `Submodule.quotient_zSaturation_isTorsionFree` | FORMALIZED | Quotienting an integral module by the explicit saturation of a submodule produces a torsion-free quotient. |
| `kummerSaturatedSubmodule_le_signatureKernel` | FORMALIZED | A signature map to a torsion-free lattice that kills raw Kummer generators also kills their saturation. |
| `range_signatureOnSaturatedDeterminantLattice` | FORMALIZED | The descended map from the saturated quotient has exactly the same image as the original signature map. |
| `KummerRelation.allRowsSignature_vector_eq_zero` | FORMALIZED | Standard and dual branch words, up to a coordinate permutation, give difference/sum relations that vanish at every unit Galois row, including self-dual `2ε` relations. |
| `kummerSaturatedSubmodule_le_allRowsSignatureKernel` | FORMALIZED | The concrete all-row determinant signature kills the saturation of any explicitly compatible Kummer relations. |
| `splitWord_rowSignature_zero` | FORMALIZED | A nonzero row `(u,v,-u,-v)` has zero row signature for every nonzero modulus. |
| `fusion_rank_identity` / `FusionComponent.rank_preserved` | FORMALIZED | Tree-edge deletion preserves the stated aggregate numerical expression, with the nontruncation premise explicit. The source-local sum theorem is listed separately below. |
| `OppositePairingWitness.exists_componentOccurrencePairing` | FORMALIZED | An unlabelled opposite-pair permutation lifts to actual component-labelled occurrences without losing repeated residues. |
| `IsAttachmentSpanningTree.*` | FORMALIZED | An attachment-order certificate proves vertex nonduplication, cross-edge selection, endpoint containment, and `|E|+1=|V|`. |
| `FusionForestWitness.residue_partition` / `rankExpression_preserved` | FORMALIZED | A multiplicity-exact forest certificate partitions node/smooth pairs, leaves a simple tuple, and preserves the aggregate integer rank expression without truncation. |
| `FusionForestWitness.sourceRankSum_eq_fusedComponentRankSum` | FORMALIZED | For a `SourceBranchFamily` with distinct source labels and at least two markings per source, the actual sum of local natural-number ranks equals the fused componentwise sum when every fused component also has at least two surviving markings. |
| `mixed_relation_all_embeddings` | FORMALIZED | The two frozen `p=5` signature columns cancel exactly. |
| `mixed_galois_balance` | FORMALIZED | The frozen mixed `p=5` concatenation passes every nonzero Galois-row balance check. |
| `mixed_fusion_rank` | FORMALIZED | The frozen two-component fusion has rank four. |
| `split_regression_p3/p5/p7` | REGRESSION ONLY | Exact enumeration for the three stated primes. |
| `rationalHodge_allPowers_of_inputs` | SCAFFOLD ONLY | Pure composition along the direct zero-signature/fusion route; its abstract manuscript-specific arrows are not formalized mathematics. |

## Phase I ledger

| Item | Repository status | Audit interpretation |
|---|---|---|
| I.1 Branch-code anti-equivalence | PARTIAL FORMALIZED | Both directions of the finite-linear-algebra dictionary, its coordinate independence, injectivity, dimension, zero-sum containment, and full support are formalized. The passage to actual covers and a categorical anti-equivalence is not. |
| I.2 Moving-factor criterion | TYPED SOURCE INTERFACE + MANUSCRIPT INPUT | Prospective Chevalley–Weil/fixed-part interfaces exist, but their exact source locators and geometric application are not yet pinned in Lean. |
| I.3 Full simple projection | PARTIAL FORMALIZED + TYPED SOURCE INTERFACE | The case-(a) positivity-to-good-sequence arithmetic match is formalized. Menet--Nguyen Theorem 5.1 remains an explicit input with degree, branch-range/count, connectedness, root-row alignment, primitive-root, and good-sequence premises separated. |
| I.4 Semisimple block reduction | MANUSCRIPT INPUT | Lie-algebra Goursat and integration are not formalized. |
| I.5 Different-support separation | MANUSCRIPT INPUT | Geometric local-system argument absent. |
| I.6 Same-support high-rank separation | TYPED SOURCE INTERFACE + MANUSCRIPT INPUT | Source-scoped pair/prefix action and spectrum interfaces exist. The exact Theorem 2.2 Gram data, subset eigenspace inputs, sign-orientation bridge, standard/dual classification, and reconstruction deduction remain absent. |
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
| P2.1 Signature formulas | PARTIAL FORMALIZED + TYPED SOURCE INTERFACE | `qValue`, `signatureAt`, and exact columns are defined and computed; identifying them with Hodge multiplicities uses the still-prospective `External.ChevalleyWeilInput`. |
| P2.2 `K`-rank `s(c)-2` | PARTIAL FORMALIZED | Support/rank arithmetic is represented, but the rational Hodge factor identification is not. |
| P2.3 Toric-factor exclusion | MANUSCRIPT INPUT | Torelli/dominance argument absent. |
| P2.4 Derived group equality | MANUSCRIPT INPUT | Carried by `phaseIExactBlocks`. |
| P2.5 Determinant quotient lattice | PARTIAL FORMALIZED + BLOCKED AS WRITTEN | The manuscript's raw quotient is wrong; the saturated integral quotient and its torsion-freeness are formalized. Identifying that quotient with the connected determinant torus still requires a new geometric proof. |
| P2.6 Kummer relations in signature kernel | PARTIAL FORMALIZED + MANUSCRIPT INPUT | Given explicit equal/dual branch-word compatibility, raw generators and their saturation lie in the concrete all-row signature kernel. Producing those compatibilities from geometric variation isomorphisms remains absent. |
| P2.7 Central torus annihilator | MANUSCRIPT INPUT | Carried by `hodgeCircleAndCentralizer`; downstream of AF-1. |
| P2.8 Full Hodge group | MANUSCRIPT INPUT | Depends on P2.4/P2.7. |
| P2.9 Isolated disk criterion | BLOCKED | Character is `±ε_c`, not `2ε_c`; also downstream of AF-1. See AF-2. |
| P2.10 Tensor invariant generators | TYPED SOURCE INTERFACE + MANUSCRIPT INPUT | `External.WeylStandardDualFFTInput` is prospective; the current Bridge field is abstract, and exact multiplicity/Kummer identification still uses Phase I. |
| P2.11 Determinant word criterion | PARTIAL FORMALIZED | The universal integer signature-to-residue-balance equivalence is proved under explicit divisibility, and branch-valid signed terms now discharge the divisibility conditions at every row. Identifying zero signature with Hodge bidegree still uses Chevalley--Weil and the tensor model. It need not depend on P2.7. |
| P2.12 Prime relations are opposite-paired | PARTIAL FORMALIZED + EXPLICIT INPUT TYPE | On the concrete signed-word model, all-row zero signature gives a literal nonzero balanced tuple. Lean derives branch sum, odd-prime parity, and unit-row balance, handles lengths zero and two directly, and uses the exact prime `B = D` leaf only from length four onward. The remaining project bridge is from actual determinant exponent/tensor data to this signed-word model. The 1984 erratum changes only Theorem B. |
| P2.13 Compact-type gluing | PARTIAL FORMALIZED + MANUSCRIPT INPUT | Pairings lift to labelled occurrences. An explicit attachment-forest certificate gives exact multiplicities, simple survivors, branch counts, and an integer rank-expression identity. A distinct source-family wrapper prevents repeated positions from collapsing. General forest-certificate existence, persistent marking-slot identifiers, and admissible-cover realization remain unproved. |
| P2.14 Smoothing and rank | PARTIAL FORMALIZED + TYPED SOURCE INTERFACE | Equality of actual source and fused local-rank sums is proved only under explicit per-source and per-fused-component lower bounds; `External.ACVBalancedSmoothingInput` is prospective and must match the exact global datum. |
| P2.15 Schoen cycles | TYPED SOURCE INTERFACE + MANUSCRIPT INPUT | `External.SchoenSimpleTupleInput` stops at the primitive factor; `Bridge.schoenSimpleCurve` is still abstract, and primitive-equals-whole remains project-side. |
| P2.16 Specialization | TYPED SOURCE INTERFACE + MANUSCRIPT INPUT | `External.ChowSpecializationInput` is prospective and separate from exact determinant compatibility; the current Bridge field remains abstract. |
| P2.17 Determinant relations algebraic | CONDITIONAL | Follows only after P2.12–P2.16 interfaces are discharged. Mixed `p=5` is arithmetic regression, not cycle construction. |
| P2.18 All rational Hodge classes algebraic | SCAFFOLD ONLY | The direct route avoids P2.5/P2.7/P2.9, but Phase I, tensor reduction, fusion geometry, and specialization still require concrete formal proofs. |
| P2.19 Binary divisor generation | MANUSCRIPT INPUT | Depends on the binary Phase I theorem and symplectic invariant theory. |

## Explicit nonclaims

The repository does not establish the integral Hodge conjecture, composite
exponent, special-fiber jumps, nonabelian deck groups, computable Chow-cycle
formulas, or the separate PEL/Weil-eightfold deformation claim.
