module

public import AbelianCoverHodge.Verified.Core
public import AbelianCoverHodge.Bridge.Assembly
public meta import Lean.Elab.Command

/-!
Run with:

`lake env lean AbelianCoverHodge/Audit/PrintAxioms.lean`

Lean's module system rejects the legacy `#print axioms` command inside a module,
so this file invokes the same `Lean.collectAxioms` kernel query through
`run_cmd`. The conditional theorem should also report no project-defined
postulates: all geometric inputs are explicit arguments rather than global
declarations.
-/

open Lean Elab Command

elab "#audit_axioms " declaration:ident : command => do
  let declarationName := declaration.getId
  unless (← getEnv).contains declarationName do
    throwError m!"unknown declaration {declarationName}"
  let dependencies ← Lean.collectAxioms declarationName
  logInfo m!"AXIOM AUDIT {declarationName}: {dependencies.toList}"

#audit_axioms AbelianCoverHodge.Verified.pairResidues_opposite
#audit_axioms AbelianCoverHodge.Verified.pairResidues_balanced
#audit_axioms AbelianCoverHodge.Verified.splitWord_rowSignature_zero
#audit_axioms AbelianCoverHodge.Verified.fusion_rank_identity
#audit_axioms AbelianCoverHodge.Verified.mixed_relation_all_embeddings
#audit_axioms AbelianCoverHodge.Verified.mixed_galois_balance
#audit_axioms AbelianCoverHodge.Verified.mixed_fusion_rank
#audit_axioms AbelianCoverHodge.Verified.split_regression_p3
#audit_axioms AbelianCoverHodge.Verified.split_regression_p5
#audit_axioms AbelianCoverHodge.Verified.split_regression_p7
#audit_axioms AbelianCoverHodge.Bridge.rationalHodge_allPowers_of_inputs
