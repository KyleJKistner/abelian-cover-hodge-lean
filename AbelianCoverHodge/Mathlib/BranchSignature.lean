module

public import AbelianCoverHodge.Mathlib.PrimeBranchDatum
public import AbelianCoverHodge.Mathlib.Signature

/-!
# Evaluation codes as branch words

This file connects the prime inertia/evaluation-code model to the integral
signature kernel.  It contains no cover classification: it proves that every
evaluated character satisfies the branch-sum relation required by the exact
Chevalley--Weil numerator calculation.
-/

open scoped BigOperators

namespace AbelianCoverHodge.Mathlib

public section

@[expose] section

open Signature

variable {p m r : Nat} [Fact p.Prime]

/-- Membership in the concrete zero-sum hyperplane is exactly the branch-word
condition used by the signature module. -/
theorem mem_coordinateSumZero_iff_isBranchWord
    (word : CodeSpace p r) :
    word ∈ (PrimeBranchDatum.coordinateSumZero (p := p) (r := r)) ↔
      IsBranchWord word := by
  simp [PrimeBranchDatum.coordinateSumZero, IsBranchWord, coordinateSum,
    PrimeBranchDatum.coordinateSumLinearMap]

namespace PrimeBranchDatum

variable (datum : PrimeBranchDatum p m r)

/-- Every character evaluated on product-one inertia data is a branch word. -/
theorem evaluation_isBranchWord (character : CoordinateDual p m) :
    IsBranchWord (datum.evaluationLinearMap character) := by
  have inCode : datum.evaluationLinearMap character ∈ datum.evaluationCode :=
    ⟨character, rfl⟩
  exact (mem_coordinateSumZero_iff_isBranchWord _).mp
    (datum.evaluationCode_le_coordinateSumZero inCode)

/-- The numerator division defining `qValue` is exact on every evaluated
character and every Galois row. -/
theorem p_dvd_qNumerator_evaluation (row : _root_.ZMod p)
    (character : CoordinateDual p m) :
    p ∣ qNumerator row (datum.evaluationLinearMap character) :=
  p_dvd_qNumerator row _ (datum.evaluation_isBranchWord character)

/-- Evaluation detects a nonzero coordinate character because the inertia
vectors span the deck space. -/
theorem evaluation_ne_zero_iff (character : CoordinateDual p m) :
    datum.evaluationLinearMap character ≠ 0 ↔ character ≠ 0 := by
  constructor
  · intro evaluationNonzero characterZero
    apply evaluationNonzero
    simp [characterZero]
  · intro characterNonzero evaluationZero
    apply characterNonzero
    apply datum.evaluationLinearMap_injective
    simpa using evaluationZero

/-- Negating a character negates the integral signature of its evaluated
branch word at every unit row. -/
theorem delta_evaluation_neg_character (row : _root_.ZMod p)
    (rowUnit : IsUnit row) (character : CoordinateDual p m) :
    delta row (datum.evaluationLinearMap (-character)) =
      -delta row (datum.evaluationLinearMap character) := by
  rw [map_neg]
  exact delta_neg_word row rowUnit _
    (datum.evaluation_isBranchWord character)

end PrimeBranchDatum

end


end


end AbelianCoverHodge.Mathlib
