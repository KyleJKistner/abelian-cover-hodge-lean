# Abelian-cover Hodge arithmetic in Lean

[![Lean audit](https://github.com/KyleJKistner/abelian-cover-hodge-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/KyleJKistner/abelian-cover-hodge-lean/actions/workflows/lean.yml)

This repository does **not** yet claim a Lean proof of the Hodge conjecture.
The current checkpoint kernel-checks a growing arithmetic/combinatorial core,
states the citation-level inputs as explicit typed interfaces, and contains a
machine-checked dependency scaffold. The scaffold is not the final audit
boundary: its abstract propositions still hide manuscript-specific geometric
deductions, and the concrete `External.*` interfaces are not yet wired into
its theorem. [`docs/AUDIT_BOUNDARY.md`](docs/AUDIT_BOUNDARY.md) records the
completion standard and exact remaining proof obligations.

## Status at a glance

| Layer | Status | What an auditor can conclude |
|---|---|---|
| Residue arithmetic, branch-code enumeration, signatures | **Lean verified** | Definitions and exact computations are checked by Lean. |
| Prime inertia data and evaluation code | **Lean verified finite linear algebra** | Evaluation is injective from spanning, and full-support zero-sum codes reconstruct the intrinsic inertia functionals up to coordinate change. No cover classification is claimed. |
| Menet--Nguyen case-(a) hypothesis match | **Lean verified arithmetic** | Positive Chevalley--Weil-style multiplicities imply the exact rational good-sequence inequalities on nonzero support. The monodromy theorem remains an explicit source input. |
| Integral determinant signature iff Galois balance | **Lean verified** | General theorem under explicit branch-divisibility hypotheses. |
| Zero determinant signature to opposite pairing | **Lean verified deduction + exact source leaf** | For branch-valid signed determinant terms at an odd prime, all-row signature vanishing gives the literal nonzero Aoki-balanced residue tuple. The source-pinned prime `B = D` input then yields an opposite-pairing witness; Lean proves the branch, unit-row, parity, and short-tuple adapters. |
| Saturated Kummer-relation lattice | **Lean verified algebra** | The corrected quotient is torsion-free and has the same signature image when raw relations lie in the signature kernel; no geometric torus identification is claimed. |
| Compatible Kummer words and all-row signature | **Lean verified algebra** | Standard/dual word generators, allowing branch-coordinate permutations and self-dual `2ε` relations, vanish in every unit Galois row; so does their saturated lattice. Geometric Kummer identifications remain outside this result. |
| Opposite-pair witnesses imply all-row balance | **Lean verified** | Constructive theorem, not an invocation of Aoki. |
| Occurrence pairing and certified fusion forests | **Lean verified conditional combinatorics** | Aoki pairings lift without losing multiplicity; a certified attachment forest gives simple survivors and exact branch counts. Integer rank expressions agree unconditionally; actual sums of local ranks agree for a distinct source family under explicit source- and fused-component lower bounds. Forest existence and geometric realization remain open. |
| Mixed `p = 5` and split `p = 3,5,7` examples | **Lean verified** | Exact kernel-reduced regressions. |
| Prime balanced-tuple source leaf and geometric inputs | **Explicit hypotheses** | The exact prime `B = D` leaf is isolated and source-pinned; several geometric source interfaces remain prospective or need exact locators. |
| Phase I blocks, tensor reduction, gluing, and exact specialization | **Unformalized deductions** | Manuscript-specific arrows remain to be replaced by concrete proofs. |
| Rational Hodge conjecture on all powers | **Scaffold only** | The direct assembly bypasses the blocked torus claims, but still has abstract unformalized deductions. |

Seven mathematical/source-interface findings from this conversion are recorded
in [`docs/AUDIT_FINDINGS.md`](docs/AUDIT_FINDINGS.md). The two defects bypassed
by the direct all-powers route are the unsaturated Phase II Kummer relation
lattice and the misnormalized internal rank-two determinant character. The
legacy manuscripts are preserved unchanged for provenance.

## Fast audit

Lean and mathlib are pinned to exact revisions. The legacy finite core remains
`Std`-only; the concrete branch-code, signature, and lattice layers use
focused mathlib imports.

```bash
./scripts/audit.sh
```

The audit file uses `Lean.collectAxioms`, the same kernel query behind the
legacy `#print axioms` command (which Lean now disallows inside modules). CI
additionally runs Lean's environment replay checker (`leanchecker`) and the
independent Rust `nanoda` implementation through
[`scripts/run_nanoda.sh`](scripts/run_nanoda.sh), with the exporter, checker,
and Rust toolchain pinned explicitly. This repository-owned step avoids the
stale parser integration tracked in upstream
[`lean-action` issue 169](https://github.com/leanprover/lean-action/issues/169).
The source audit rejects `sorry`,
`admit`, and global `axiom` declarations; the curated dependency report rejects
`sorryAx` and any dependency other than `propext`, `Quot.sound`, or
`Classical.choice`. `nanoda` independently rejects declarations which depend
on an unpermitted axiom; its full-environment configuration additionally
permits `Lean.trustCompiler` and enables the standard natural-number and string
kernel extensions. The external check is CI-only in the fast path because the
full transitive export is resource intensive.

## Where to look

- [`AbelianCoverHodge/Verified/Core.lean`](AbelianCoverHodge/Verified/Core.lean)
  is the unconditional kernel-checked layer.
- [`AbelianCoverHodge/Verified/IntegralSignature.lean`](AbelianCoverHodge/Verified/IntegralSignature.lean)
  proves the additive integer signature and exact balance bridge.
- [`AbelianCoverHodge/Verified/AokiFusion.lean`](AbelianCoverHodge/Verified/AokiFusion.lean)
  proves the all-row easy direction and packages the fusion rank premises;
  it asserts no published converse.
- [`AbelianCoverHodge/Verified/FusionForest.lean`](AbelianCoverHodge/Verified/FusionForest.lean)
  lifts opposite residues to labelled occurrences and verifies attachment-tree,
  multiplicity, simplicity, and branch-count consequences of a concrete
  fusion-forest certificate. Its source-family API prevents repeated source
  positions from collapsing and states every local rank bound explicitly.
- [`AbelianCoverHodge/Mathlib/PrimeBranchDatum.lean`](AbelianCoverHodge/Mathlib/PrimeBranchDatum.lean)
  constructs the prime inertia evaluation code in genuine mathlib `ZMod` linear algebra.
- [`AbelianCoverHodge/Mathlib/BranchCodeEquivalence.lean`](AbelianCoverHodge/Mathlib/BranchCodeEquivalence.lean)
  reconstructs intrinsic inertia functionals from a full-support zero-sum code and proves coordinate independence.
- [`AbelianCoverHodge/Mathlib/BranchSignature.lean`](AbelianCoverHodge/Mathlib/BranchSignature.lean)
  connects evaluated characters to the exact integral branch-signature identities.
- [`AbelianCoverHodge/Mathlib/MenetNguyenGood.lean`](AbelianCoverHodge/Mathlib/MenetNguyenGood.lean)
  proves the manuscript-specific case-(a) good-sequence hypothesis match.
- [`AbelianCoverHodge/External/MenetNguyen.lean`](AbelianCoverHodge/External/MenetNguyen.lean)
  gives concrete source-scoped interfaces for the Menet--Nguyen row data,
  action formulas, reflection spectrum, and case-(a) monodromy theorem. Root,
  eigenspace, and geometric monodromy identifications remain explicit inputs.
- [`AbelianCoverHodge/External/Aoki.lean`](AbelianCoverHodge/External/Aoki.lean)
  isolates the prime `B = D` statement recorded on Aoki p. 24 and credited
  there to W. Parry. Its branch-sum, unit-row, nonzero-entry, even-length, and
  minimum-length premises are all explicit, and its conclusion is existential.
- [`AbelianCoverHodge/Mathlib/Signature.lean`](AbelianCoverHodge/Mathlib/Signature.lean)
  defines the integral signature as a genuine `ℤ`-linear map.
- [`AbelianCoverHodge/Mathlib/DeterminantLattice.lean`](AbelianCoverHodge/Mathlib/DeterminantLattice.lean)
  proves the saturation and torsion-free quotient correction independently of geometry.
- [`AbelianCoverHodge/Mathlib/DeterminantSignature.lean`](AbelianCoverHodge/Mathlib/DeterminantSignature.lean)
  proves compatible Kummer generators, and therefore their saturation, lie in the concrete all-row signature kernel.
- [`AbelianCoverHodge/External/Inputs.lean`](AbelianCoverHodge/External/Inputs.lean)
  gives the prospective citation-level trust boundary as typed interfaces
  rather than global postulates. It is not yet the input type of the headline
  scaffold theorem.
- [`AbelianCoverHodge/Bridge/DeterminantAoki.lean`](AbelianCoverHodge/Bridge/DeterminantAoki.lean)
  proves the concrete manuscript deduction from a branch-valid all-row zero
  integral determinant signature to an explicit opposite-pairing witness,
  using the source-pinned prime `B = D` leaf only in the
  length-at-least-four branch.
- [`AbelianCoverHodge/Bridge/Assembly.lean`](AbelianCoverHodge/Bridge/Assembly.lean)
  is the temporary direct-route dependency scaffold.
- [`docs/CLAIMS.md`](docs/CLAIMS.md) maps every manuscript ledger item to its
  formal status.
- [`docs/DEPENDENCIES.md`](docs/DEPENDENCIES.md) shows the target assembly DAG
  and the citation/project-obligation split.
- [`docs/AUDIT_BOUNDARY.md`](docs/AUDIT_BOUNDARY.md) states the target external
  trust boundary and every manuscript-specific obligation still to formalize.
- [`docs/PROVENANCE.md`](docs/PROVENANCE.md) records source hashes and the legacy
  certificate reproducibility gap.
- [`manuscripts/`](manuscripts/) contains unmodified source copies and ledgers.

## Exact verified scope

The legacy dependency-light layer represents `ZMod p` by `Fin p`, with modular
operations defined transparently.  The newer algebraic modules use mathlib's
genuine `ZMod`. Together the verified layers provide:

- executable spans of `p`-ary generator matrices;
- support, residue sums, Chevalley–Weil-style `q` values, and signature columns;
- signed determinant-word expansion and balance checks;
- a proof that explicit nonzero opposite pairs have symmetric multiplicities
  and satisfy the doubled balance equation at every nonzero row for prime
  modulus;
- an additive `Int`-valued determinant signature and a proof that its
  vanishing is equivalent to the literal concatenated-residue balance
  equation under explicit divisibility hypotheses;
- a proof that branch-valid signed determinant terms discharge those
  divisibility hypotheses at every row, that their literal determinant
  residues are nonzero, and that all-row zero signature implies Aoki balance;
- for prime modulus other than two, a concrete deduction from that balance to
  a permutation-valued opposite-pairing witness, conditional only on the
  explicitly supplied, source-pinned prime `B = D` leaf; Lean proves the
  source adapters and handles the empty and two-entry cases directly;
- the fusion identity
  `branches - 2 * vertices = (branches - 2 * treeEdges) - 2` for a tree;
- occurrence-level opposite pairings and certified spanning-forest
  bookkeeping, including loops, exact multiplicities, simple survivors, and
  an unconditional integer rank-expression identity; for distinct source
  positions, equality of actual local rank sums follows under separate lower
  bounds for every source word and fused component;
- the exact mixed `p = 5` cancellation and fused rank-four witness;
- a symbolic zero-signature calculation for a nonzero split row
  `(u,v,-u,-v)`, plus exact split-family regressions for `p = 3,5,7`.

This release does not yet formalize algebraic tori, Hodge structures, Chow
groups, admissible covers, or Schoen's cycles. It also makes no claim about the
separate unresolved PEL/Weil-eightfold deformation problem.

## Citation and review

Please cite the source manuscripts for the mathematical claims and this
repository only for the Lean formalization layer. Specialist review should
start with the audit findings, then the claim matrix, then the verified core.
Issues that identify a theorem/source mismatch or shrink a research interface
are especially valuable.
