# Target audit boundary

## Decision

The finished formalization should state every imported theorem with its exact
hypotheses and conclusion, prove every deduction specific to these manuscripts,
and leave the final all-powers theorem conditional on only a short list of
source-auditable inputs.

The current repository does **not** yet meet that boundary.
`Verified/Core.lean`, `Verified/IntegralSignature.lean`, and
`Verified/AokiFusion.lean` check the finite arithmetic through the exact
zero-signature/balance reduction and the basic fusion expression identity.
`Bridge/DeterminantAoki.lean` now closes the concrete odd-prime finite chain
from branch-valid all-row zero signed determinant terms to an explicit
opposite-pairing witness, consuming only the exact prime `B = D` source input
in `External/Aoki.lean` for tuples of length at least four. The shorter cases
and every source-side adapter are proved in Lean.
The `Mathlib/` modules now prove both directions of the finite branch-code
dictionary, the case-(a) Menet--Nguyen arithmetic hypothesis match, a genuine
integral signature linear map, and the corrected saturated determinant
relation quotient with its concrete all-row signature. These are concrete
algebraic foundations, not geometric substitutes for covers, Hodge
structures, or Chow groups.
`External/Inputs.lean` exposes the citation-level assumptions as typed data,
but several contexts are necessarily erased until the corresponding Hodge,
Chow, and admissible-cover objects are defined. `Bridge/Assembly.lean` remains
only a logical dependency scaffold: its abstract propositions erase too much
mathematical content to count as a formalization of the geometric proof. In
particular, `External.ProspectiveCitationInputs` is not yet consumed by
`Bridge.rationalHodge_allPowers_of_inputs`; the latter uses the unrelated
abstract `Bridge.PublishedInputs`.

## Shortest headline route

The written proof in `manuscripts/general_all_powers.tex`, with the standalone
fusion companion, now supplies the general mathematical route. Its geometric
and Hodge objects are **not yet formalized**. The correct route is:

1. Prove a mixed embedding exists, retain all rational conjugates, and classify
   connected monodromy blocks using Goursat, pair twists and actual oriented
   graph correspondences.
2. Use Schur–Weyl to span invariants by volume and coevaluation diagrams.
3. Construct a finite rational algebraic source map from matching-embedding
   determinant words and Tate summands onto those invariants. Empty words
   require deck translates spanning their whole Galois orbit.
4. At a very general point, lift each rational Hodge class through this map
   using semisimplicity. Only the forward map must be algebraic.
5. A nonzero source Hodge vector in a K-line forces all-row middle bidegree,
   hence the literal balance condition.
6. The prime `B = D` theorem, pairing forests, ACV smoothing, Schoen cycles and
   specialization prove the standalone balanced fusion theorem.
7. Forward algebraic diagram maps transfer these cycles to the target power.

This route bypasses the complete determinant-torus calculation and never
identifies arbitrary monodromy-Hom corners with Hodge-Hom corners. The earlier
AF-8 through AF-10 defects remain defects of the historical arguments; the new
universal proof replaces their needed steps. AF-11 is handled by the standalone
fusion revision. Exact source coverage is in `GENERAL_ALL_POWERS.md` and
`FUSION_REPAIR.md`.

## Citation-level leaves to state exactly

The expected external boundary is roughly the following. Some items may split
after their hypotheses are pinned to primary sources.

1. Chevalley--Weil multiplicities for prime cyclic covers.
2. Deligne semisimplicity and fixed part.
3. Full monodromy projection for one positive cyclic eigenspace. The present
   source candidate is Menet--Nguyen, not Spelta--Tamborini Theorem 4.4, whose
   no-repeated-factors hypothesis is stronger than the factorwise use here.
4. Menet--Nguyen pair-twist formula and spanning-vector relation. The new
   proof avoids the old subset-twist and half-shift route.
5. Generic connected-monodromy inclusion and CDK algebraicity of exceptional
   Hodge loci. Equality with the derived Hodge group is not required.
6. Schur–Weyl duality for standard/dual special-linear tensor invariants;
   symplectic tensor invariants and A’Campo for the binary case.
7. The prime `B = D` statement recorded on Aoki p. 24 and credited there to
   W. Parry, with the source's branch, nonzero-entry, unit-row, and even-length
   at least four premises, in the form used by Schoen.
8. ACV deformation of the precise balanced tame cyclic admissible cover.
9. Schoen's theorem for a simple tuple and its primitive determinant space.
10. Compact-type Picard, smooth proper comparison, and Chow specialization
    compatibility.
11. Standard weight-one Hodge realization, Poincare correspondences, and
    algebraic alternating projectors.

Torelli and the finiteness statement used to classify support-three toric
factors are needed only for the full-group refinement, not for the shortest
all-powers route if Phase I is formulated directly on every relevant block.

## Manuscript-specific obligations

The following are formalization obligations, even where a current manuscript
now supplies a written proof. They must not remain bundled as hypotheses:

- the finite-linear-algebra branch-datum/code equivalence, including
  coordinate independence, is formalized; cover classification and the
  identification with geometric monodromy data are not;
- the Menet--Nguyen case-(a) positivity-to-good-sequence arithmetic match is
  formalized on nonzero support; positivity-to-moving, the geometric factor
  identification, root/sign orientation bridge, and discharge of Theorem
  5.1's other standing hypotheses remain. Source-scoped action interfaces are
  present, but the Theorem 2.2 spanning relation and its nonzero-vector
  consequence still need formal models. The new route does not require
  Lemma 3.9/Corollary 3.11 subset-eigenspace inputs or a Gram computation;
- semisimple subdirect-product reduction, support separation, and high-rank
  character reconstruction;
- the new labelled pair-sum sign cube, global-sign reconstruction and
  explicit oriented Kummer graphs; the old fingerprint certificate and
  half-shift/rigidity route are no longer required;
- quotient-cover oriented graph construction, nonvanishing, scalar descent
  and connected block assembly; no general Hodge/monodromy double-centralizer
  equality may be assumed;
- the rational algebraic diagram-source surjection, empty-word orbit span,
  and semisimple Hodge lifting argument;
- determinant-word zero-signature iff balanced is formalized at the residue
  level under explicit branch-divisibility hypotheses. For branch-valid signed
  terms, Lean now proves every divisibility and nonzero-entry side condition,
  derives odd-prime parity and the branch condition, restricts all-row balance
  to the source's unit rows, proves the length-zero and length-two cases, and
  applies the exact prime `B = D` leaf only at length at least four. Identifying
  a concrete Hodge determinant monomial and its bidegrees with this signed-word
  model remains;
- occurrence-labelled pairing, connected attachment-tree existence and the
  finite consequences of an attachment forest are formalized. Distinct source
  positions preserve repeated determinant factors. Source bounds alone imply
  the required fused bounds and exact equality of actual local-rank sums.
  The disconnected graph partition and assembly remain to be formalized, as
  do the geometric inverse-inertia realization, smoothing and compact type.
  The fusion revision supplies written arguments for the geometric steps;
- prime primitive-factor equals whole-Jacobian application of Schoen;
- determinant of a direct sum, specialization to component determinants,
  quotient pull--push/projectors, and final tensor-to-cohomology assembly.

The correcting rank-two determinant identity is now formalized over an
arbitrary commutative ring. The integral algebra of the corrected determinant
lattice is also formalized:
it quotients by the saturation, proves the quotient torsion-free, proves the
explicit standard/dual word generators up to branch-coordinate permutation
vanish in every unit row (including self-dual `2 epsilon` relations), descends the
compatible signature map, and proves the first-isomorphism statement. The
full-group refinement remains a separate work stream because it must identify
this algebraic quotient with the connected geometric torus and use central
character `+/- epsilon_c`, not `2 epsilon_c`.

## Completion test

The audit-ready milestone is reached only when:

- the abstract `Stages` scaffold is no longer on the headline theorem path;
- the exact `External.*` citation inputs are actually wired into that theorem,
  rather than merely declared in a parallel prospective bundle;
- the theorem type names concrete branch data, covers, eigenspaces, tensor
  spaces, cycle classes, and comparison maps;
- erased carrier/predicate contexts are replaced by concrete objects or are
  independently justified as faithful theorem interfaces;
- every manuscript-specific arrow above has a Lean proof;
- the final theorem's dependency report and theorem signature expose only the
  exact citation-level leaves;
- CI builds from the pinned toolchain, runs `leanchecker` and `nanoda`, rejects
  proof placeholders/project postulates, and prints the dependency report.
