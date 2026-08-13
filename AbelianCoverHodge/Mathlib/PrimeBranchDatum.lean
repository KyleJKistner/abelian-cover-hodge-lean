module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Prime elementary branch data and its evaluation code

This module formalizes only the finite linear algebra attached to branch data
for a putative elementary `(Z/p)^m`-cover.  It does not construct a cover and
does not invoke a classification or an anti-equivalence with covers.

For a prime `p`, branch data consist of inertia vectors

`inertia : Fin r → (Fin m → ZMod p)`

which are nonzero, sum to zero, and span the deck vector space.  Coordinates
identify the dual of `(ZMod p)^m` with another copy of `(ZMod p)^m` through
the standard dot product.  Evaluating such a character on every inertia
vector gives the branch code in `(ZMod p)^r`.
-/

namespace AbelianCoverHodge.Mathlib

public section

@[expose] section

open scoped BigOperators

variable {p m r : Nat} [Fact p.Prime]

/-- The elementary deck vector space `(Z/p)^m`. -/
abbrev DeckSpace (p m : Nat) := Fin m → _root_.ZMod p

/-- Coordinate model of the dual of `DeckSpace p m`, using the standard
perfect dot product. -/
abbrev CoordinateDual (p m : Nat) := Fin m → _root_.ZMod p

/-- The ambient length-`r` branch-code space. -/
abbrev CodeSpace (p r : Nat) := Fin r → _root_.ZMod p

/-- Concrete prime branch data.  The three proof fields are exactly the
nontrivial local inertia, product-one, and connectedness/spanning conditions
used by the code construction. -/
structure PrimeBranchDatum (p m r : Nat) [Fact p.Prime] where
  inertia : Fin r → DeckSpace p m
  inertia_ne_zero : ∀ i, inertia i ≠ 0
  sum_inertia : ∑ i, inertia i = 0
  span_inertia :
    Submodule.span (_root_.ZMod p) (Set.range inertia) = ⊤

namespace PrimeBranchDatum

variable (datum : PrimeBranchDatum p m r)

/-- The linear functional represented by dual coordinates via the standard
dot product. -/
def dotFunctional (character : CoordinateDual p m) :
    DeckSpace p m →ₗ[_root_.ZMod p] _root_.ZMod p where
  toFun vector := dotProduct character vector
  map_add' left right := by
    exact dotProduct_add character left right
  map_smul' scalar vector := by
    exact dotProduct_smul scalar character vector

@[simp]
theorem dotFunctional_apply (character : CoordinateDual p m)
    (vector : DeckSpace p m) :
    dotFunctional (p := p) character vector =
      dotProduct character vector := rfl

/-- Evaluate a coordinate character on all inertia vectors. -/
def evaluationLinearMap :
    CoordinateDual p m →ₗ[_root_.ZMod p] CodeSpace p r where
  toFun character i := dotProduct character (datum.inertia i)
  map_add' left right := by
    funext i
    exact add_dotProduct left right (datum.inertia i)
  map_smul' scalar character := by
    funext i
    exact smul_dotProduct scalar character (datum.inertia i)

@[simp]
theorem evaluationLinearMap_apply (character : CoordinateDual p m)
    (i : Fin r) :
    datum.evaluationLinearMap character i =
      dotProduct character (datum.inertia i) := rfl

/-- The evaluation code is the linear range of the evaluation map. -/
def evaluationCode : Submodule (_root_.ZMod p) (CodeSpace p r) :=
  LinearMap.range datum.evaluationLinearMap

/-- Equivalently, the evaluation code is the span of all evaluated
characters. -/
theorem evaluationCode_eq_span_range :
    datum.evaluationCode =
      Submodule.span (_root_.ZMod p)
        (Set.range datum.evaluationLinearMap) := by
  apply le_antisymm
  · rintro codeword ⟨character, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self character)
  · rw [Submodule.span_le]
    rintro codeword ⟨character, rfl⟩
    exact ⟨character, rfl⟩

/-- Sum all coordinates of an ambient codeword. -/
def coordinateSumLinearMap :
    CodeSpace p r →ₗ[_root_.ZMod p] _root_.ZMod p where
  toFun codeword := ∑ i, codeword i
  map_add' left right := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' scalar codeword := by
    change (∑ i, scalar * codeword i) = scalar * ∑ i, codeword i
    exact (Finset.mul_sum Finset.univ codeword scalar).symm

@[simp]
theorem coordinateSumLinearMap_apply (codeword : CodeSpace p r) :
    coordinateSumLinearMap (p := p) (r := r) codeword =
      ∑ i, codeword i := rfl

/-- The coordinate-sum-zero hyperplane containing every branch code. -/
def coordinateSumZero : Submodule (_root_.ZMod p) (CodeSpace p r) :=
  LinearMap.ker (coordinateSumLinearMap (p := p) (r := r))

@[simp]
theorem sum_inertia_apply (coordinate : Fin m) :
    ∑ i, datum.inertia i coordinate = 0 := by
  have equality := congrFun datum.sum_inertia coordinate
  simpa only [Finset.sum_apply, Pi.zero_apply] using equality

/-- The product-one relation on inertia vectors makes every evaluated
character have coordinate sum zero. -/
theorem coordinateSum_evaluation (character : CoordinateDual p m) :
    coordinateSumLinearMap (p := p) (r := r)
        (datum.evaluationLinearMap character) = 0 := by
  change (∑ i, ∑ coordinate, character coordinate *
    datum.inertia i coordinate) = 0
  rw [Finset.sum_comm]
  calc
    (∑ coordinate, ∑ i, character coordinate * datum.inertia i coordinate) =
        ∑ coordinate, character coordinate *
          (∑ i, datum.inertia i coordinate) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [Finset.mul_sum]
    _ = 0 := by simp

/-- The entire evaluation code lies in the coordinate-sum-zero hyperplane. -/
theorem evaluationCode_le_coordinateSumZero :
    datum.evaluationCode ≤ coordinateSumZero (p := p) (r := r) := by
  rintro codeword ⟨character, rfl⟩
  exact datum.coordinateSum_evaluation character

/-- If a character evaluates to zero on the spanning inertia vectors, its dot
product functional vanishes on the entire deck space. -/
theorem dotFunctional_eq_zero_of_evaluation_eq_zero
    (character : CoordinateDual p m)
    (evaluationZero : datum.evaluationLinearMap character = 0) :
    dotFunctional (p := p) character = 0 := by
  apply LinearMap.ext_on_range datum.span_inertia
  intro i
  have atCoordinate := congrFun evaluationZero i
  simpa using atCoordinate

/-- Spanning inertia makes the evaluation map injective. -/
theorem evaluationLinearMap_injective :
    Function.Injective datum.evaluationLinearMap := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro character inKernel
  have evaluationZero : datum.evaluationLinearMap character = 0 :=
    LinearMap.mem_ker.mp inKernel
  have functionalZero : dotFunctional (p := p) character = 0 :=
    datum.dotFunctional_eq_zero_of_evaluation_eq_zero
      character evaluationZero
  have everyPairingZero :
      ∀ vector : DeckSpace p m,
        dotProduct character vector = 0 := by
    intro vector
    have atVector := LinearMap.congr_fun functionalZero vector
    simpa using atVector
  exact dotProduct_eq_zero character everyPairingZero

/-- The evaluation code has the expected dimension `m`. -/
theorem finrank_evaluationCode :
    Module.finrank (_root_.ZMod p) datum.evaluationCode = m := by
  rw [evaluationCode, LinearMap.finrank_range_of_inj
    datum.evaluationLinearMap_injective]
  simpa only [Fintype.card_fin] using
    (Module.finrank_pi (_root_.ZMod p) (ι := Fin m))

/-- Consequently the evaluation code has exactly `p^m` codewords. -/
theorem natCard_evaluationCode :
    Nat.card datum.evaluationCode = p ^ m := by
  rw [Module.natCard_eq_pow_finrank (K := _root_.ZMod p),
    Nat.card_zmod, datum.finrank_evaluationCode]

/-- A code has full support if no ambient coordinate vanishes identically on
the code. -/
def HasFullSupport
    (code : Submodule (_root_.ZMod p) (CodeSpace p r)) : Prop :=
  ∀ i : Fin r, ∃ codeword : code, codeword.1 i ≠ 0

/-- Nonzero inertia at every branch point makes the evaluation code
full-support. -/
theorem evaluationCode_hasFullSupport :
    HasFullSupport datum.evaluationCode := by
  intro i
  have componentExists : ∃ coordinate : Fin m,
      datum.inertia i coordinate ≠ 0 := by
    by_contra noComponent
    apply datum.inertia_ne_zero i
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp noComponent coordinate)
  obtain ⟨coordinate, componentNonzero⟩ := componentExists
  let character : CoordinateDual p m := Pi.single coordinate 1
  refine ⟨⟨datum.evaluationLinearMap character,
    ⟨character, rfl⟩⟩, ?_⟩
  simpa [character] using componentNonzero

end PrimeBranchDatum

end

end


end AbelianCoverHodge.Mathlib
