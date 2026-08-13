module

public import AbelianCoverHodge.Verified.Core

/-!
# Conditional geometric assembly

This file is a dependency interface, not a proof of its geometric inputs.
Every published theorem and every manuscript-specific bridge appears as an
ordinary theorem parameter.  There are no project-level global postulates.

The separation matters: `Verified.Core` can be audited without importing this
file, while this module makes the remaining route to the all-powers rational
Hodge conclusion machine-readable.
-/

namespace AbelianCoverHodge.Bridge

public section

@[expose] section

/-- Abstract propositions at the successive interfaces of the Phase II
argument.  A future geometric formalization can replace each field with a
concrete mathlib definition without changing the dependency graph below. -/
structure Stages where
  verifiedArithmetic : Prop
  hodgeSignatureCriterion : Prop
  balancedRelations : Prop
  oppositePairings : Prop
  fusionDatum : Prop
  smoothedCover : Prop
  simpleCurveCycle : Prop
  wholeJacobianCycle : Prop
  specializedCycle : Prop
  algebraicDeterminants : Prop
  algebraicContractions : Prop
  invariantGenerators : Prop
  rationalHodgeAllPowers : Prop

/-- Published inputs used by the assembly.  The field names are intentionally
theorem-specific so source scope can be audited one edge at a time. -/
structure PublishedInputs (S : Stages) where
  chevalleyWeil : S.verifiedArithmetic → S.hodgeSignatureCriterion
  aokiPrime : S.balancedRelations → S.oppositePairings
  acvSmoothing : S.fusionDatum → S.smoothedCover
  schoenSimpleCurve : S.smoothedCover → S.simpleCurveCycle
  chowSpecialization : S.wholeJacobianCycle → S.specializedCycle
  weylInvariantTheory :
    S.algebraicContractions → S.algebraicDeterminants → S.invariantGenerators
  abelianHodgeRealization :
    S.invariantGenerators → S.rationalHodgeAllPowers

/-- Manuscript-specific bridges.  These are separated from published inputs
because they carry the main unresolved proof burden in the present package. -/
structure ResearchInputs (S : Stages) where
  phaseIExactBlocks : S.algebraicContractions
  hodgeCircleAndCentralizer :
    S.hodgeSignatureCriterion → S.balancedRelations
  fusionGluing : S.oppositePairings → S.fusionDatum
  primitiveEqWholeForPrimeP1 :
    S.simpleCurveCycle → S.wholeJacobianCycle
  specializationCompatibility :
    S.specializedCycle → S.algebraicDeterminants

/-- The all-powers conclusion, conditional on the seven named published
interfaces, the five named research interfaces, and the verified arithmetic
premise.  The proof merely composes those arrows; it does not hide any input. -/
theorem rationalHodge_allPowers_of_inputs
    (S : Stages)
    (published : PublishedInputs S)
    (research : ResearchInputs S)
    (arithmetic : S.verifiedArithmetic) :
    S.rationalHodgeAllPowers := by
  have signatureCriterion : S.hodgeSignatureCriterion :=
    published.chevalleyWeil arithmetic
  have balanced : S.balancedRelations :=
    research.hodgeCircleAndCentralizer signatureCriterion
  have paired : S.oppositePairings := published.aokiPrime balanced
  have fusion : S.fusionDatum := research.fusionGluing paired
  have smoothed : S.smoothedCover := published.acvSmoothing fusion
  have simpleCycle : S.simpleCurveCycle :=
    published.schoenSimpleCurve smoothed
  have wholeCycle : S.wholeJacobianCycle :=
    research.primitiveEqWholeForPrimeP1 simpleCycle
  have specialized : S.specializedCycle :=
    published.chowSpecialization wholeCycle
  have determinants : S.algebraicDeterminants :=
    research.specializationCompatibility specialized
  have generators : S.invariantGenerators :=
    published.weylInvariantTheory research.phaseIExactBlocks determinants
  exact published.abelianHodgeRealization generators

end

end

end AbelianCoverHodge.Bridge
