module

public import AbelianCoverHodge.Verified.Core

/-!
# Direct conditional assembly for the all-powers conclusion

This file is a logical dependency scaffold, not the finished audit-boundary
formalization. Its propositions are deliberately abstract, so the theorem
below checks only composition. `docs/AUDIT_BOUNDARY.md` records the concrete
interfaces that must replace them.

The route here is nevertheless mathematically important: it does not use the
blocked determinant-torus quotient or the misnormalized internal-disk claim.
Once Phase I identifies the derived invariants, Hodge bidegrees directly select
the zero-signature determinant words. Aoki, fusion, Schoen, and specialization
then algebraize those words.
-/

namespace AbelianCoverHodge.Bridge

public section

@[expose] section

/-- Abstract checkpoints in the direct all-powers route. These are temporary
placeholders for concrete structures, maps, covers, Hodge spaces, and cycle
classes; no field is itself presented as a formalized mathematical theorem. -/
structure Stages where
  verifiedArithmetic : Prop
  chevalleyWeilBidegrees : Prop
  phaseIBlockDescription : Prop
  derivedInvariantGenerators : Prop
  zeroSignatureDeterminants : Prop
  balancedRelations : Prop
  oppositePairings : Prop
  fusionDatum : Prop
  smoothedCover : Prop
  simpleCurveCycle : Prop
  wholeJacobianCycle : Prop
  specializedCycle : Prop
  algebraicDeterminants : Prop
  algebraicContractions : Prop
  algebraicHodgeTensors : Prop
  rationalHodgeAllPowers : Prop

/-- Citation-level inputs. The final version will replace each arrow by its
exact source-scoped theorem statement and all of its hypotheses. -/
structure PublishedInputs (S : Stages) where
  chevalleyWeil : S.verifiedArithmetic → S.chevalleyWeilBidegrees
  aokiPrime : S.balancedRelations → S.oppositePairings
  acvSmoothing : S.fusionDatum → S.smoothedCover
  schoenSimpleCurve : S.smoothedCover → S.simpleCurveCycle
  chowSpecialization : S.wholeJacobianCycle → S.specializedCycle
  weylInvariantTheory :
    S.phaseIBlockDescription → S.derivedInvariantGenerators
  weightOneHodgeRealization :
    S.algebraicHodgeTensors → S.rationalHodgeAllPowers

/-- Argument-specific deductions still to be replaced by proofs over concrete
objects. Keeping them separate prevents manuscript claims from being mistaken
for published inputs. -/
structure UnformalizedDeductions (S : Stages) where
  phaseIExactBlocks : S.phaseIBlockDescription
  determinantBidegreeCriterion :
    S.chevalleyWeilBidegrees →
    S.derivedInvariantGenerators →
    S.zeroSignatureDeterminants
  zeroSignatureIffBalanced :
    S.zeroSignatureDeterminants → S.balancedRelations
  fusionGluing : S.oppositePairings → S.fusionDatum
  primitiveEqWholeForPrimeP1 :
    S.simpleCurveCycle → S.wholeJacobianCycle
  specializationCompatibility :
    S.specializedCycle → S.algebraicDeterminants
  contractionsFromPhaseI :
    S.phaseIBlockDescription → S.algebraicContractions
  assembleAlgebraicTensorGenerators :
    S.derivedInvariantGenerators →
    S.algebraicContractions →
    S.algebraicDeterminants →
    S.algebraicHodgeTensors

/-- Direct all-powers assembly. This theorem does not depend on a central
torus, its character lattice, or the internal rank-two disk calculation. At
this checkpoint it remains only a machine-checked dependency sketch. -/
theorem rationalHodge_allPowers_of_inputs
    (S : Stages)
    (published : PublishedInputs S)
    (deductions : UnformalizedDeductions S)
    (arithmetic : S.verifiedArithmetic) :
    S.rationalHodgeAllPowers := by
  have bidegrees : S.chevalleyWeilBidegrees :=
    published.chevalleyWeil arithmetic
  have generators : S.derivedInvariantGenerators :=
    published.weylInvariantTheory deductions.phaseIExactBlocks
  have zeroSignature : S.zeroSignatureDeterminants :=
    deductions.determinantBidegreeCriterion bidegrees generators
  have balanced : S.balancedRelations :=
    deductions.zeroSignatureIffBalanced zeroSignature
  have paired : S.oppositePairings := published.aokiPrime balanced
  have fusion : S.fusionDatum := deductions.fusionGluing paired
  have smoothed : S.smoothedCover := published.acvSmoothing fusion
  have simpleCycle : S.simpleCurveCycle :=
    published.schoenSimpleCurve smoothed
  have wholeCycle : S.wholeJacobianCycle :=
    deductions.primitiveEqWholeForPrimeP1 simpleCycle
  have specialized : S.specializedCycle :=
    published.chowSpecialization wholeCycle
  have determinants : S.algebraicDeterminants :=
    deductions.specializationCompatibility specialized
  have contractions : S.algebraicContractions :=
    deductions.contractionsFromPhaseI deductions.phaseIExactBlocks
  have algebraicTensors : S.algebraicHodgeTensors :=
    deductions.assembleAlgebraicTensorGenerators
      generators contractions determinants
  exact published.weightOneHodgeRealization algebraicTensors

end

end

end AbelianCoverHodge.Bridge
