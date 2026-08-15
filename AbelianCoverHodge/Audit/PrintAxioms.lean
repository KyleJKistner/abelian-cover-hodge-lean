module

public import AbelianCoverHodge.Verified.Core
public import AbelianCoverHodge.Verified.IntegralSignature
public import AbelianCoverHodge.Verified.AokiFusion
public import AbelianCoverHodge.Verified.FusionForest
public import AbelianCoverHodge.Mathlib.Signature
public import AbelianCoverHodge.Mathlib.PrimeBranchDatum
public import AbelianCoverHodge.Mathlib.BranchCodeEquivalence
public import AbelianCoverHodge.Mathlib.BranchSignature
public import AbelianCoverHodge.Mathlib.MenetNguyenGood
public import AbelianCoverHodge.Mathlib.DeterminantLattice
public import AbelianCoverHodge.Mathlib.DeterminantSignature
public import AbelianCoverHodge.External.Aoki
public import AbelianCoverHodge.External.MenetNguyen
public import AbelianCoverHodge.External.Inputs
public import AbelianCoverHodge.Bridge.DeterminantAoki
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
  for dependency in dependencies.toList do
    unless dependency == ``propext ||
        dependency == ``Quot.sound ||
        dependency == ``Classical.choice do
      throwError m!"unexpected kernel dependency in {declarationName}: {dependency}"
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
#audit_axioms AbelianCoverHodge.Verified.defectIsZero_eq_true_iff
#audit_axioms AbelianCoverHodge.Verified.integralDeterminantSignatureAt_lappend
#audit_axioms AbelianCoverHodge.Verified.integralDeterminantSignatureAt_eq_zero_iff_galoisBalanced
#audit_axioms AbelianCoverHodge.Verified.integralRowSignature_negativeWord
#audit_axioms AbelianCoverHodge.Verified.integralRowSignature_pairResidues_zero
#audit_axioms AbelianCoverHodge.Verified.nonzero_row_invertible_of_prime
#audit_axioms AbelianCoverHodge.Verified.pairResidues_aokiBalanced
#audit_axioms AbelianCoverHodge.Verified.aokiBalanced_length_even_of_prime_ne_two
#audit_axioms AbelianCoverHodge.Verified.OppositePairingWitness.aokiBalanced
#audit_axioms AbelianCoverHodge.Bridge.scaleWord_isBranchWord
#audit_axioms AbelianCoverHodge.Bridge.determinantResidues_allResiduesNonzero
#audit_axioms AbelianCoverHodge.Bridge.determinantResidues_isAokiBalanced
#audit_axioms AbelianCoverHodge.Bridge.isBranchWord_of_aokiBalanced_even
#audit_axioms AbelianCoverHodge.Bridge.aokiUnitBalanced_of_aokiBalanced_prime
#audit_axioms AbelianCoverHodge.Bridge.oppositePairingWitness_of_short_aokiBalanced
#audit_axioms AbelianCoverHodge.Bridge.determinantResidues_oppositePairing_of_aokiPrime
#audit_axioms AbelianCoverHodge.Verified.FusionComponent.rank_preserved
#audit_axioms AbelianCoverHodge.Verified.OppositePairingWitness.exists_componentOccurrencePairing
#audit_axioms AbelianCoverHodge.Verified.IsAttachmentSpanningTree.edge_count_add_one_eq_vertex_count
#audit_axioms AbelianCoverHodge.Verified.FusionForestWitness.residue_partition
#audit_axioms AbelianCoverHodge.Verified.FusionForestComponent.rankExpression_preserved
#audit_axioms AbelianCoverHodge.Verified.FusionForestWitness.rankExpression_preserved
#audit_axioms AbelianCoverHodge.Verified.FusionForestWitness.sourceRankSum_eq_fusedComponentRankSum
#audit_axioms AbelianCoverHodge.Mathlib.Signature.p_dvd_qNumerator
#audit_axioms AbelianCoverHodge.Mathlib.Signature.delta_neg_word
#audit_axioms AbelianCoverHodge.Mathlib.Signature.determinantSignatureMap_zsmul
#audit_axioms AbelianCoverHodge.Mathlib.PrimeBranchDatum.evaluationLinearMap_injective
#audit_axioms AbelianCoverHodge.Mathlib.PrimeBranchDatum.finrank_evaluationCode
#audit_axioms AbelianCoverHodge.Mathlib.PrimeBranchDatum.evaluationCode_hasFullSupport
#audit_axioms AbelianCoverHodge.Mathlib.FullSupportZeroSumCode.evaluationCode_toPrimeBranchDatum
#audit_axioms AbelianCoverHodge.Mathlib.PrimeBranchDatum.reconstructed_inertia
#audit_axioms AbelianCoverHodge.Mathlib.PrimeBranchDatum.p_dvd_qNumerator_evaluation
#audit_axioms AbelianCoverHodge.Mathlib.PrimeBranchDatum.delta_evaluation_neg_character
#audit_axioms AbelianCoverHodge.Mathlib.MenetNguyenGood.positiveHodgePair_iff_goodSequenceCaseA
#audit_axioms AbelianCoverHodge.External.MenetNguyen.goodSequenceCaseA_of_positiveHodgePair
#audit_axioms AbelianCoverHodge.External.MenetNguyen.theorem5_1_caseA_of_positiveHodgePair
#audit_axioms Submodule.quotient_zSaturation_isTorsionFree
#audit_axioms AbelianCoverHodge.Mathlib.kummerSaturatedSubmodule_le_signatureKernel
#audit_axioms AbelianCoverHodge.Mathlib.range_signatureOnSaturatedDeterminantLattice
#audit_axioms AbelianCoverHodge.Mathlib.signatureQuotientEquivRange
#audit_axioms AbelianCoverHodge.Mathlib.KummerRelation.allRowsSignature_vector_eq_zero
#audit_axioms AbelianCoverHodge.Mathlib.kummerSaturatedSubmodule_le_allRowsSignatureKernel
#audit_axioms AbelianCoverHodge.Bridge.rationalHodge_allPowers_of_inputs
