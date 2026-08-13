# Target audit boundary

## Decision

The finished formalization should state every imported theorem with its exact
hypotheses and conclusion, prove every deduction specific to these manuscripts,
and leave the final all-powers theorem conditional on only a short list of
source-auditable inputs.

The current repository does **not** yet meet that boundary. `Verified/Core.lean`
checks a finite arithmetic/combinatorial layer. `Bridge/Assembly.lean` is only a
logical dependency scaffold: its abstract propositions erase too much
mathematical content to count as a formalization of the geometric proof.

## Shortest headline route

The rational Hodge conclusion does not require the full determinant-torus
calculation:

1. Phase I identifies the derived Hodge-group blocks and supplies algebraic
   Kummer matrix units.
2. Weyl invariant theory reduces derived invariants to contractions and
   determinant monomials.
3. Chevalley--Weil bidegrees show directly that a determinant monomial is Hodge
   exactly when every signature sum is zero.
4. The manuscript-specific arithmetic reduction turns zero signature into an
   Aoki-balanced residue tuple.
5. Aoki's prime theorem supplies opposite-residue pairs.
6. The pairing graph and spanning forest give the compact-type fusion datum.
7. ACV smoothing, Schoen's simple-tuple theorem, and Chow specialization
   algebraize the determinant space.
8. Algebraic contractions and determinant spaces generate every rational Hodge
   class on every power.

This route quarantines audit findings AF-1 and AF-2. They still block the
separate claims computing the complete Hodge group and all endomorphism
corners, but they are not premises of the direct all-powers argument.

## Citation-level leaves to state exactly

The expected external boundary is roughly the following. Some items may split
after their hypotheses are pinned to primary sources.

1. Chevalley--Weil multiplicities for prime cyclic covers.
2. Deligne semisimplicity and fixed part.
3. Full monodromy projection for one positive cyclic eigenspace. The present
   source candidate is Menet--Nguyen, not Spelta--Tamborini Theorem 4.4, whose
   no-repeated-factors hypothesis is stronger than the factorwise use here.
4. Menet--Nguyen pair- and subset-twist spectra.
5. Andre normality for the derived generic Hodge group.
6. Weyl's invariant theorem for standard/dual special-linear blocks.
7. Aoki's prime balanced-tuple theorem, in the form used by Schoen.
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

The largest proof obligations that must not remain bundled as hypotheses are:

- branch-datum/code equivalence and exact integral signature identities;
- positivity-to-moving and positivity-to-good-sequence hypothesis matching;
- semisimple subdirect-product reduction, support separation, and high-rank
  character reconstruction;
- symbolic Fricke/Gassner fingerprint, half-shift exclusion, and Kummer
  rigidity, replacing the missing legacy Phase I core certificate;
- quotient-cover graph construction, nonvanishing, descent, matrix units,
  double centralizer, and Phase I block assembly;
- determinant-word zero-signature iff balanced;
- pairing graph, spanning forest, remaining simple tuple, branch count, rank,
  inverse inertia, connectedness, and compact type;
- prime primitive-factor equals whole-Jacobian application of Schoen;
- determinant of a direct sum, specialization to component determinants,
  quotient pull--push/projectors, and final tensor-to-cohomology assembly.

The corrected determinant-lattice/full-group refinement is a separate work
stream. It must quotient by the saturation of the Kummer relation lattice and
use central character `+/- epsilon_c`, not `2 epsilon_c`.

## Completion test

The audit-ready milestone is reached only when:

- the abstract `Stages` scaffold is no longer on the headline theorem path;
- the theorem type names concrete branch data, covers, eigenspaces, tensor
  spaces, cycle classes, and comparison maps;
- every manuscript-specific arrow above has a Lean proof;
- the final theorem's dependency report and theorem signature expose only the
  exact citation-level leaves;
- CI builds from the pinned toolchain, runs `leanchecker`, rejects proof
  placeholders/project postulates, and prints the dependency report.
