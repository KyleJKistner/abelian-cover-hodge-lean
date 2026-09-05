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
- **WRITTEN PROOF:** a current manuscript supplies the argument with named
  source inputs. This is neither a Lean proof nor external referee validation.
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
- **LEGACY ROUTE BYPASSED / WRITTEN PROOF OF REPLACEMENT:** the original
  argument is not repaired or imported; the named new argument supplies the
  necessary conclusion within its stated scope.

## General all-powers written proof

The current mathematical statement is Theorem 1.1 of
[`general_all_powers.tex`](../manuscripts/general_all_powers.tex), with the
standalone Fermat-transfer companion and Shioda's classical product theorem.
The earlier fusion proof remains an alternative. It covers every prime, fixed
spanning zero-sum elementary abelian branch datum, and all powers of the
very general Jacobian in the full branch family. Its rational diagram and
Hodge-lifting proof closes the previously separate generator hypothesis.
[GENERAL_ALL_POWERS.md](GENERAL_ALL_POWERS.md) records source coverage,
regression ranges, and exact nonclaims. **This does not upgrade the Lean
headline:** that declaration remains scaffold only.

Structural companion Section 7 extends the written result to finite abelian
groups of exponent dividing p^e (p odd), 3^a5^b or 3^a7^b. For arbitrary odd
N it gives a criterion conditional on HC for every power of the degree-N
Fermat Jacobian. The full P1 branch-family and very-general hypotheses
remain. Aoki's published theorem supplies the listed unconditional cases.

The [novelty assessment](NOVELTY.md) distinguishes the classical determinant
algebraicity and cyclic all-powers consequence from the candidate uniform
joint-group contribution. A written proof status below is not a priority claim.

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
| `FusionForestWitness.sourceRankSum_eq_fusedComponentRankSum_of_source_family` | FORMALIZED | A supplied forest and a distinct `SourceBranchFamily` with at least two markings per source suffice for equality of actual natural-number rank sums. Every fused-component bound is derived. |
| `FusionForestWitness.four_le_component_remainingBranchCount` / `component_fused_rank_positive_even` | FORMALIZED | At least three markings on each source imply every fused component has at least four surviving markings and positive even rank. |
| `exists_attachmentSpanningTree_of_connected` | FORMALIZED | Every finite connected graph of actual opposite pairs has an attachment spanning tree. |
| `exists_fusionComponent_of_connected` / `exists_fusionForest_of_connected` | FORMALIZED | The connected pairing graph admits a complete fusion component with exact original-pairs = node-pairs + smooth-pairs multiplicities. A one-component forest follows when every ambient vertex occurs. |
| `SourceBranchFamily.exists_fusionForest_of_preconnected` | FORMALIZED | A source family and occurrence pairing whose actual source labels are mutually reachable admit a full forest witness, including the empty family. This works directly with distinct natural-number labels. |
| `Bridge.determinantSourceFamily_residues` | FORMALIZED | Distinct labels preserve repeated determinant factors and recover the literal effective residue concatenation. |
| `Bridge.determinant_fusion_rank_and_bounds` | FORMALIZED + EXPLICIT INPUT TYPE | Branch-valid zero-signature determinant sources with support at least three produce labelled pairings from the exact Aoki leaf; any supplied forest preserves total rank and has positive even fused ranks. |
| `RankTwoDeterminant.congruence_eq_det_smul` / `congruence_coefficient_unique` | FORMALIZED | Over any commutative ring the alternating two-tensor has precisely the determinant multiplier, not its square. |
| `mixed_relation_all_embeddings` | FORMALIZED | The two frozen `p=5` signature columns cancel exactly. |
| `mixed_galois_balance` | FORMALIZED | The frozen mixed `p=5` concatenation passes every nonzero Galois-row balance check. |
| `mixed_fusion_rank` | FORMALIZED | The frozen two-component fusion has rank four. |
| `split_regression_p3/p5/p7` | REGRESSION ONLY | Exact enumeration for the three stated primes. |
| `rationalHodge_allPowers_of_inputs` | SCAFFOLD ONLY | Pure composition along the direct zero-signature/fusion route; its abstract manuscript-specific arrows are not formalized mathematics. |

## Phase I ledger

| Item | Repository status | Audit interpretation |
|---|---|---|
| I.1 Branch-code anti-equivalence | PARTIAL FORMALIZED | Both directions of the finite-linear-algebra dictionary, its coordinate independence, injectivity, dimension, zero-sum containment, and full support are formalized. The passage to actual covers and a categorical anti-equivalence is not. |
| I.2 Moving-factor criterion | WRITTEN PROOF; NOT FORMALIZED | The general manuscript proves a mixed embedding exists on every rational orbit with support at least four, retains all definite conjugates, and identifies the support-three constant factors. The old per-embedding compactness argument remains false. |
| I.3 Full simple projection | WRITTEN PROOF + PARTIAL FORMALIZED | The general manuscript matches MN case (a), normalizes affine configurations with finite scalar fiber monodromy, and transports the K-defined closure to every embedding. The positivity-to-good-sequence arithmetic match is Lean proved; the geometry is not. |
| I.4 Semisimple block reduction | WRITTEN PROOF; NOT FORMALIZED | General manuscript Section 3 proves semisimplicity, the graph normalizer gate and Goursat product decomposition. |
| I.5 Different-support separation | WRITTEN PROOF; NOT FORMALIZED | The spanning-vector/rank-one argument proves active pair twists nonidentity, including zero pair sums. Forgetting an inactive point separates supports. |
| I.6 Same-support high-rank separation | WRITTEN PROOF; NOT FORMALIZED | One global inner/outer sign in PGL_h and labelled pair sums reconstruct c or -c for h≥3. The new proof does not use the old prefix/half-shift argument. |
| I.7 Reduction to four-point rank two | WRITTEN PROOF; NOT FORMALIZED | All moving factors have h=s-2; h=2 is exactly active support four, after the full-projection and support arguments. |
| I.8 Exact Fricke fingerprint | LEGACY ROUTE BYPASSED | The old core is still missing. General manuscript Section 3 supplies a different universal proof: labelled pair eigenratios give precisely the ±V4 sign cube. No finite Fricke replay is claimed. |
| I.9 Kummer rigidity | WRITTEN PROOF OF REPLACEMENT; NOT FORMALIZED | Explicit Möbius/Kummer graphs prove the converse to the new ±V4 classification. The old rigidity route is not imported. |
| I.10 Exact connected monodromy blocks | WRITTEN PROOF; NOT FORMALIZED | The general manuscript determines all complex connected blocks and actual oriented occurrences. The abstract Lean phaseIExactBlocks field is still not a concrete theorem. |
| I.11 Algebraization of disk intertwiners | WRITTEN PROOF WITH ORIENTED SCOPE | Deck-equivariant graphs and quotient pullback/norm give actual oriented arrows on (V4.c)∩C; negative components are polarized duals. Arbitrary monodromy intertwiners are not called Hodge maps. |
| I.12 Cross-character Hodge-Hom corners | BLOCKED AS WRITTEN | The general oriented-corner saturation assertion is withdrawn (AF-9/AF-10). The restricted split case is separately proved with inverse graph maps. |
| I.13 Saturated derived centralizer | WRITTEN PROOF OF REPLACEMENT; NOT FORMALIZED | Structural companion Section 2 calculates the actual oriented graph centralizer over K and proves its derived group equals connected monodromy. It does not import the invalid blanket commutant assertion. |
| I.14 Generic derived Hodge group | WRITTEN PROOF; NOT FORMALIZED | The structural ambient-group sandwich gives Hg^der=M without requiring the missing legacy normality argument. |
| I.15 Binary/ternary consequences | WRITTEN PROOF + REGRESSION ONLY | The general manuscript proves binary independent symplectic factors and all-powers divisor generation. Finite word calculations remain regressions, not formal monodromy proofs. |
| I.16 Split-family Kummer geometry | WRITTEN PROOF + PARTIAL FORMALIZED | Six explicit cover isomorphisms and their relations are written and symbolically checked; only split-row signature arithmetic is Lean proved. |
| I.17 Split endomorphism algebra | WRITTEN PROOF | The revision constructs the crossed product, inverse matrix units and full generic commutant. It is not Lean formalized. |
| I.18 Split isogeny decomposition | WRITTEN PROOF | The restricted split-family revision deduces the isogeny decomposition, simplicity and non-isogeny from its exact rational algebra. Not Lean formalized. |
| I.19 Néron–Severi formula | WRITTEN PROOF | The revision deduces the dimension from the corrected positive Rosati algebra. Bounded arithmetic checks alone are not its proof. |
| I.20 Split all-powers Hodge theorem | WRITTEN PROOF | The restricted split-family revision identifies the generic Hodge group and applies symplectic invariant theory to all powers. Not Lean verified or externally refereed. |

## Phase II ledger

| Item | Repository status | Audit interpretation |
|---|---|---|
| P2.1 Signature formulas | PARTIAL FORMALIZED + TYPED SOURCE INTERFACE | `qValue`, `signatureAt`, and exact columns are defined and computed; identifying them with Hodge multiplicities uses the still-prospective `External.ChevalleyWeilInput`. |
| P2.2 `K`-rank `s(c)-2` | WRITTEN PROOF + PARTIAL FORMALIZED | The general and fusion manuscripts identify the rational cyclic factor and its K-rank. Lean supplies only finite support/rank arithmetic. |
| P2.3 Toric-factor exclusion | WRITTEN PROOF OF REPLACEMENT | The mixed-embedding carry lemma and three-point isotriviality account for all rational factors directly. No higher-rank all-definite rational factor is dropped, and no Torelli argument is needed here. |
| P2.4 Derived group equality | WRITTEN PROOF; NOT FORMALIZED | Structural companion Section 2 proves M=L^der=Hg^der in the actual representation. The Lean field remains abstract. |
| P2.5 Determinant quotient lattice | LEGACY ROUTE BYPASSED + PARTIAL FORMALIZED | The old raw quotient remains wrong. Structural Section 2 proves a free determinant-quotient lattice from actual GL and self-negative SL2 factors over K. The saturation arithmetic is Lean formalized; the geometric identification is written only. |
| P2.6 Kummer relations in signature kernel | PARTIAL FORMALIZED + MANUSCRIPT INPUT | Given explicit equal/dual branch-word compatibility, raw generators and their saturation lie in the concrete all-row signature kernel. Producing those compatibilities from geometric variation isomorphisms remains absent. |
| P2.7 Central torus annihilator | WRITTEN PROOF; NOT FORMALIZED | Structural Section 2 supplies the geometric premise and obtains X*(T)=E/ker(Sigma). The image is not claimed saturated in the auxiliary row lattice, nor identified integrally with an isogenous center. |
| P2.8 Full Hodge group | WRITTEN PROOF; NOT FORMALIZED | Structural Section 2 proves Hg=q^-1(T) by minimality of the rational Hodge group. |
| P2.9 Isolated disk criterion | PARTIAL FORMALIZED + BLOCKED AS WRITTEN | The character is `±ε_c`, not `2ε_c`; the correcting matrix identity is now Lean proved. Its Hodge-Hom interpretation and geometric torus hypotheses remain separate. |
| P2.10 Tensor invariant generators | WRITTEN PROOF; NOT FORMALIZED | General manuscript Section 5 proves the Schur–Weyl reduction and algebraic rational diagram realization, with actual orientations, all effective words, and the empty-word Vandermonde step. The Lean source interface is still prospective. |
| P2.11 Determinant word criterion | WRITTEN PROOF + PARTIAL FORMALIZED | The general manuscript constructs rational K-line word sources and proves zero-or-full Hodge subspace iff all embeddings balance. Lean proves the residue signature equivalence and divisibility adapters, not the Hodge realization. |
| P2.12 Prime relations are opposite-paired | PARTIAL FORMALIZED + EXPLICIT INPUT TYPE | On the concrete signed-word model, all-row zero signature gives a literal nonzero balanced tuple. Lean derives branch sum, odd-prime parity, and unit-row balance, handles lengths zero and two directly, and uses the exact prime `B = D` leaf only from length four onward. The remaining project bridge is from actual determinant exponent/tensor data to this signed-word model. The 1984 erratum changes only Theorem B. |
| P2.13 Compact-type gluing | WRITTEN PROOF + PARTIAL FORMALIZED | The fusion revision constructs the balanced admissible cover with inverse tangent characters. Lean constructs connected attachment trees, exact pair partitions and distinct repeated-source labels. Disconnected component assembly and the geometric realization are not formalized. |
| P2.14 Smoothing and rank | WRITTEN PROOF + PARTIAL FORMALIZED | Lean derives fused lower bounds from source data and proves equality of actual local-rank sums. The manuscript supplies stable algebraic ACV smoothing and connectedness; the corresponding Lean geometric interface remains prospective. |
| P2.15 Schoen cycles | WRITTEN PROOF; NOT FORMALIZED | The fusion revision verifies the primitive-equals-whole prime case, source tuple hypotheses and scope of the 1998 addendum. The Lean source interface and abstract bridge remain unconnected. |
| P2.16 Specialization | WRITTEN PROOF; NOT FORMALIZED | The fusion revision supplies finite-extension descent, a compact-type abelian scheme, rational matching-slot projectors and cycle-class specialization. The Lean geometric bridge remains abstract. |
| P2.17 Determinant relations algebraic | WRITTEN PROOF; NOT FORMALIZED | The Fermat companion realizes all determinant spaces as algebraic summands; Shioda gives their product Hodge classes. This is a classical consequence. Fusion supplies an alternative. General Sections 5–6 prove exhaustive rational generation using Hodge lifting. |
| P2.18 All rational Hodge classes algebraic | WRITTEN PROOF; LEAN SCAFFOLD ONLY | General Theorem 1.1 uses Fermat transfer, Shioda and the stated group/invariant inputs. It bypasses P2.5/P2.7/P2.9. The separate Lean composition still has abstract unformalized deductions. Novelty of the full assembly is unverified. |
| P2.19 Binary divisor generation | WRITTEN PROOF; NOT FORMALIZED | General manuscript Section 7 matches A’Campo including genus one, separates supports with nonidentity pair twists, and applies symplectic tensor invariants to all powers. |

## Structural development

| Item | Status | Exact scope |
|---|---|---|
| Determinant Fermat summand | WRITTEN PROOF; NOT FORMALIZED | Fermat companion Theorem 1.1: arbitrary cyclic prime P1 cover, any smooth fiber, explicit finite-quotient Chow projectors and normalized Jacobian transfer. Classical mechanism, not asserted new. |
| First exceptional degree | WRITTEN PROOF + REGRESSION ONLY | Structural Section 3: odd-subgroup branch words with added opposite pairs, full family, genus (p−1)h/2, first exceptional codimension h, quotient dimension (p−1)(m−1)/2. The 152 arithmetic cases do not prove the geometry. |
| All-powers ring generators | WRITTEN PROOF; NOT FORMALIZED | Structural Section 4: divisors and homomorphism pullbacks of that first exceptional space generate every power. The proof handles all placements and rational descent. |
| Distinct-prime products | WRITTEN PROOF; NOT FORMALIZED | Structural Section 5: independent or shared full configurations, isogeny factors and all powers; Hodge rings factor across primes. This product statement is separate from the exponent extension in Section 7. |
| Degree-seven generalized HC | WRITTEN PROOF; NOT FORMALIZED | Structural Section 6: every power of the very general Jacobian for (1,2,4,(1,−1)^k), k≥1. The proof supplies every CM partner and ordinary-HC product required by Abdulali's domination criterion. An attributed classical corollary, not a general-prime statement. |
| Odd-conductor projections and finite exception | WRITTEN PROOF; NOT FORMALIZED | Structural Section 7 matches MN's good-sequence hypotheses at every odd conductor. The unique all-definite support-at-least-four primitive type is (1,2,4,8) at conductor 15, with primitive factor E^8 for CM by Q(sqrt(−15)); its full H1 is retained. |
| Odd-exponent transfer and Aoki cases | WRITTEN PROOF; NOT FORMALIZED | Structural Section 7: conditional for any odd N on all-powers HC for the Fermat-N Jacobian; unconditional for N=p^e (p odd), 3^a5^b,3^a7^b. Every finite abelian group of exponent dividing N, full ordered P1 branch family, very general Jacobian, every power. Primitive projectors, exact graph blocks, controlled Fermat blowups and full rational invariant sources are supplied. |

## Explicit nonclaims

The repository does not establish the integral Hodge conjecture, arbitrary
even composite exponent, unrestricted odd exponent without the Fermat
premise, arbitrary special fibers or restricted subfamilies, nonabelian deck
groups, computable equations for all Chow cycles, or the separate
PEL/Weil-eightfold deformation claim. All cover theorems here have base P1.
