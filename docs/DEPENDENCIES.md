# Target dependency graph

The diagram below is the target mathematical DAG, not a claim that every solid
arrow is already a Lean theorem. The core never imports the bridge. The current
bridge is explicitly a temporary logical scaffold; the concrete replacement
criteria are in `AUDIT_BOUNDARY.md`.

```mermaid
flowchart TD
  CODE["Full-support zero-sum code"] <--> BD["Prime inertia evaluation data"]
  BD --> A["Lean-verified integral signature"]
  POS["Positive CW arithmetic pair"] --> GOOD["Lean-verified MN case-(a) good sequence"]
  GOOD --> MN["Menet--Nguyen Theorem 5.1"]
  MN -->|"one source input"| P1
  TW["MN twist inputs + further source leaves"] --> P1
  DEL["Deligne fixed part + Andre normality"] --> P1
  PM["Project proofs: Goursat, reconstruction, Kummer geometry, descent"] --> P1
  A --> CW["Chevalley--Weil bidegrees"]
  P1["Phase I exact blocks + algebraic matrix units"] --> FFT["Weyl invariant theory"]
  CW --> ZS["Determinant Hodge iff zero signature"]
  FFT --> ZS
  ZS --> BAL["Zero signature iff Aoki balance"]
  BAL --> AO["Aoki prime theorem"]
  AO --> PAIR["Opposite matching"]
  PAIR --> FUS["Pairing graph / compact-type fusion datum"]
  FUS --> ACV["ACV smoothing"]
  ACV --> SCH["Schoen simple-tuple cycles"]
  SCH --> PW["Primitive equals whole for prime cyclic P1 cover"]
  PW --> SP["Chow specialization + determinant compatibility"]
  SP --> DET["Algebraic determinant spaces"]
  P1 --> CON["Algebraic contractions"]
  FFT --> GEN["Algebraic tensor generators"]
  DET --> GEN
  CON --> GEN
  GEN --> HR["Weight-one Hodge realization"]
  HR --> GOAL["All-powers rational Hodge conclusion"]

  LAT["Lean-verified saturated relation lattice"] -->|"explicit compatible-word hypotheses"| ASIG["Concrete all-row signature quotient"]
  LAT --> TOR["Geometric torus identification"]
  TOR -. "separate refinement" .-> FULL["Full Hodge group / endomorphisms"]
```

## Why the direct route matters

The all-powers conclusion uses determinant Hodge bidegrees directly. It does
not require a prior computation of the complete central torus. Consequently,
the unsaturated quotient and rank-two character errors recorded as AF-1 and
AF-2 do not enter this headline path.

The full-group branch now starts from a proved algebraic correction: the
saturated quotient is torsion-free and compatible signature maps descend.
Only its identification with the geometric connected central torus remains on
that branch.

## Current interfaces and scaffold

`External/Inputs.lean` now separates the prospective citation-level
assumptions into typed
interfaces for Chevalley--Weil, Deligne, Menet--Nguyen, Andre, Weyl, Aoki, ACV,
Schoen, compact-type Picard, smooth-proper comparison, Chow specialization,
and weight-one realization. These are assumption *types*, not global
postulates; contexts still using erased carrier types advertise that fact.

`External.ProspectiveCitationInputs` is not consumed by the headline scaffold.
The separate `Bridge.PublishedInputs` has seven logical arrows and
`UnformalizedDeductions` has eight manuscript-specific arrows. Both structures
remain scaffolding. Every manuscript-specific field must disappear from the
final theorem and be replaced by a proof over concrete objects. In particular,
`phaseIExactBlocks` currently hides most of Phase I and is not an acceptable
final assumption.

See `AUDIT_BOUNDARY.md` for the exact leaf inventory, hidden obligations, and
completion test.
