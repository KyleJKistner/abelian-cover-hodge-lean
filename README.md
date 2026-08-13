# Abelian-cover Hodge arithmetic in Lean

[![Lean audit](https://github.com/KyleJKistner/abelian-cover-hodge-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/KyleJKistner/abelian-cover-hodge-lean/actions/workflows/lean.yml)

This repository does **not** claim a Lean proof of the Hodge conjecture. The
current checkpoint kernel-checks a finite arithmetic/combinatorial core and
contains a machine-checked dependency scaffold. The scaffold is not the final
audit boundary: its abstract propositions still hide manuscript-specific
deductions. [`docs/AUDIT_BOUNDARY.md`](docs/AUDIT_BOUNDARY.md) records the
stronger completion standard and exact remaining proof obligations.

## Status at a glance

| Layer | Status | What an auditor can conclude |
|---|---|---|
| Residue arithmetic, branch-code enumeration, signatures | **Lean verified** | Definitions and exact computations are checked by Lean. |
| Opposite-pair witnesses imply balance | **Lean verified** | Constructive theorem, not an invocation of Aoki. |
| Fusion rank bookkeeping | **Lean verified** | The compact-type rank identity is integer arithmetic. |
| Mixed `p = 5` and split `p = 3,5,7` examples | **Lean verified** | Exact kernel-reduced regressions. |
| General Aoki converse and geometric inputs | **Explicit hypotheses** | Named citation-level interfaces, not yet exact source-scoped statements. |
| Phase I blocks, tensor reduction, gluing, and exact specialization | **Unformalized deductions** | Manuscript-specific arrows remain to be replaced by concrete proofs. |
| Rational Hodge conjecture on all powers | **Scaffold only** | The direct assembly bypasses the blocked torus claims, but still has abstract unformalized deductions. |

Two mathematical defects found during this conversion are recorded in
[`docs/AUDIT_FINDINGS.md`](docs/AUDIT_FINDINGS.md): the Phase II Kummer relation
lattice needs saturation, and an internal rank-two determinant character is
misnormalized. The legacy manuscripts are preserved unchanged for provenance;
the direct all-powers dependency route does not use either defective step.

## Fast audit

The project deliberately depends only on Lean's `Std` library. Lean is pinned
in `lean-toolchain`; there is no mathlib or package-resolution surface.

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
  and satisfy the doubled balance equation;
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
