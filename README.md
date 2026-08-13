# Abelian-cover Hodge arithmetic in Lean

[![Lean audit](https://github.com/KyleJKistner/abelian-cover-hodge-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/KyleJKistner/abelian-cover-hodge-lean/actions/workflows/lean.yml)

This repository does **not** yet claim a Lean proof of the Hodge conjecture.
The current checkpoint kernel-checks a growing arithmetic/combinatorial core,
states the citation-level inputs as explicit typed interfaces, and contains a
machine-checked dependency scaffold. The scaffold is not the final audit
boundary: its abstract propositions still hide manuscript-specific geometric
deductions. [`docs/AUDIT_BOUNDARY.md`](docs/AUDIT_BOUNDARY.md) records the
completion standard and exact remaining proof obligations.

## Status at a glance

| Layer | Status | What an auditor can conclude |
|---|---|---|
| Residue arithmetic, branch-code enumeration, signatures | **Lean verified** | Definitions and exact computations are checked by Lean. |
| Prime inertia data and evaluation code | **Lean verified** | Concrete `ZMod p` evaluation is injective from spanning, has dimension `m`, lies in the zero-sum hyperplane, and has full support. |
| Integral determinant signature iff Galois balance | **Lean verified** | General theorem under explicit branch-divisibility hypotheses. |
| Saturated Kummer-relation lattice | **Lean verified algebra** | The corrected quotient is torsion-free and has the same signature image when raw relations lie in the signature kernel; no geometric torus identification is claimed. |
| Opposite-pair witnesses imply all-row balance | **Lean verified** | Constructive theorem, not an invocation of Aoki. |
| Fusion rank bookkeeping | **Lean verified** | The compact-type rank identity is integer arithmetic. |
| Mixed `p = 5` and split `p = 3,5,7` examples | **Lean verified** | Exact kernel-reduced regressions. |
| General Aoki converse and geometric inputs | **Explicit hypotheses** | Typed source-scoped interfaces; several exact source locators remain to be pinned. |
| Phase I blocks, tensor reduction, gluing, and exact specialization | **Unformalized deductions** | Manuscript-specific arrows remain to be replaced by concrete proofs. |
| Rational Hodge conjecture on all powers | **Scaffold only** | The direct assembly bypasses the blocked torus claims, but still has abstract unformalized deductions. |

Two mathematical defects found during this conversion are recorded in
[`docs/AUDIT_FINDINGS.md`](docs/AUDIT_FINDINGS.md): the Phase II Kummer relation
lattice needs saturation, and an internal rank-two determinant character is
misnormalized. The legacy manuscripts are preserved unchanged for provenance;
the direct all-powers dependency route does not use either defective step.

## Fast audit

Lean and mathlib are pinned to exact revisions. The legacy finite core remains
`Std`-only; the concrete branch-code, signature, and lattice layers use
focused mathlib imports.

```bash
lake build
./scripts/audit.sh
lake env lean AbelianCoverHodge/Audit/PrintAxioms.lean
```

The audit file uses `Lean.collectAxioms`, the same kernel query behind the
legacy `#print axioms` command (which Lean now disallows inside modules). CI
additionally runs Lean's independent environment checker. The optional
`nanoda` action is not claimed: its current parser rejects Lean 4.33 exports
after a successful export, before checking any declaration. The source audit
rejects `sorry`, `admit`, `axiom`, and `sorryAx`.

## Where to look

- [`AbelianCoverHodge/Verified/Core.lean`](AbelianCoverHodge/Verified/Core.lean)
  is the unconditional kernel-checked layer.
- [`AbelianCoverHodge/Verified/IntegralSignature.lean`](AbelianCoverHodge/Verified/IntegralSignature.lean)
  proves the additive integer signature and exact balance bridge.
- [`AbelianCoverHodge/Verified/AokiFusion.lean`](AbelianCoverHodge/Verified/AokiFusion.lean)
  proves the all-row easy direction, exposes Aoki as supplied theorem data,
  and packages the fusion rank premises.
- [`AbelianCoverHodge/Mathlib/PrimeBranchDatum.lean`](AbelianCoverHodge/Mathlib/PrimeBranchDatum.lean)
  constructs the prime inertia evaluation code in genuine mathlib `ZMod` linear algebra.
- [`AbelianCoverHodge/Mathlib/Signature.lean`](AbelianCoverHodge/Mathlib/Signature.lean)
  defines the integral signature as a genuine `ℤ`-linear map.
- [`AbelianCoverHodge/Mathlib/DeterminantLattice.lean`](AbelianCoverHodge/Mathlib/DeterminantLattice.lean)
  proves the saturation and torsion-free quotient correction independently of geometry.
- [`AbelianCoverHodge/External/Inputs.lean`](AbelianCoverHodge/External/Inputs.lean)
  gives the citation-level trust boundary as typed interfaces rather than
  global postulates.
- [`AbelianCoverHodge/Bridge/Assembly.lean`](AbelianCoverHodge/Bridge/Assembly.lean)
  is the temporary direct-route dependency scaffold.
- [`docs/CLAIMS.md`](docs/CLAIMS.md) maps every manuscript ledger item to its
  formal status.
- [`docs/DEPENDENCIES.md`](docs/DEPENDENCIES.md) shows the assembly DAG and the
  published/research split.
- [`docs/AUDIT_BOUNDARY.md`](docs/AUDIT_BOUNDARY.md) states the target external
  trust boundary and every manuscript-specific obligation still to formalize.
- [`docs/PROVENANCE.md`](docs/PROVENANCE.md) records source hashes and the legacy
  certificate reproducibility gap.
- [`manuscripts/`](manuscripts/) contains unmodified source copies and ledgers.

## Exact verified scope

At this dependency-light layer, `ZMod p` is represented by `Fin p`, with
modular addition, multiplication, and negation defined transparently. The core
provides:

- executable spans of `p`-ary generator matrices;
- support, residue sums, Chevalley–Weil-style `q` values, and signature columns;
- signed determinant-word expansion and balance checks;
- a proof that explicit nonzero opposite pairs have symmetric multiplicities
  and satisfy the doubled balance equation at every nonzero row for prime
  modulus;
- an additive `Int`-valued determinant signature and a proof that its
  vanishing is equivalent to the literal concatenated-residue balance
  equation under explicit divisibility hypotheses;
- a permutation-valued opposite-pairing witness and a parameterized interface
  for the published Aoki converse;
- the fusion identity
  `branches - 2 * vertices = (branches - 2 * treeEdges) - 2` for a tree;
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
