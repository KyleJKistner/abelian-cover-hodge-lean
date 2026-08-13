module

public import AbelianCoverHodge.Mathlib.PrimeBranchDatum
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The finite-linear-algebra branch-code dictionary

This module proves the coordinate-free part of ledger item I.1.  It relates
spanning elementary prime inertia data to its evaluation code, and constructs
inertia functionals back from a full-support sum-zero linear code.

Nothing here asserts that either datum comes from an algebraic or topological
cover.  In particular, the module proves no cover-classification or
categorical anti-equivalence statement.
-/

namespace AbelianCoverHodge.Mathlib

public section

@[expose] section

open scoped BigOperators

variable {p m r : Nat} [Fact p.Prime]

/-- The standard dot product identifies coordinate vectors with their linear
duals.  This focused local definition avoids importing the broader matrix-dual
API merely for one equivalence. -/
def coordinateDualEquiv (p n : Nat) [Fact p.Prime] :
    (Fin n → _root_.ZMod p) ≃ₗ[_root_.ZMod p]
      Module.Dual (_root_.ZMod p) (Fin n → _root_.ZMod p) where
  toFun vector :=
    { toFun := dotProduct vector
      map_add' := dotProduct_add vector
      map_smul' := fun scalar other => dotProduct_smul scalar vector other }
  invFun functional i := functional (LinearMap.single (_root_.ZMod p) _ i 1)
  left_inv vector := by simp
  right_inv functional := by ext; simp
  map_add' left right := by ext; simp
  map_smul' scalar vector := by ext; simp

@[simp]
theorem coordinateDualEquiv_apply (vector other : Fin n → _root_.ZMod p) :
    coordinateDualEquiv p n vector other = dotProduct vector other := rfl

namespace PrimeBranchDatum

variable (datum : PrimeBranchDatum p m r)

/-- Evaluation is a linear equivalence from coordinate characters onto its
code, because the inertia vectors span the deck vector space. -/
noncomputable def evaluationEquiv :
    CoordinateDual p m ≃ₗ[_root_.ZMod p] datum.evaluationCode :=
  LinearEquiv.ofInjective datum.evaluationLinearMap
    datum.evaluationLinearMap_injective

@[simp]
theorem coe_evaluationEquiv_apply (character : CoordinateDual p m) :
    (datum.evaluationEquiv character : CodeSpace p r) =
      datum.evaluationLinearMap character := rfl

end PrimeBranchDatum

/-! ## The intrinsic code-to-inertia construction -/

/-- Exact finite-linear-algebra hypotheses for the converse direction.

`sumZero` is the product-one relation and `fullSupport` says that every branch
coordinate is detected by at least one codeword.  No geometric existence
hypothesis is included. -/
structure FullSupportZeroSumCode (p r : Nat) [Fact p.Prime] where
  carrier : Submodule (_root_.ZMod p) (CodeSpace p r)
  sumZero : carrier ≤
    PrimeBranchDatum.coordinateSumZero (p := p) (r := r)
  fullSupport : PrimeBranchDatum.HasFullSupport carrier

namespace FullSupportZeroSumCode

variable (code : FullSupportZeroSumCode p r)

/-- The inertia functional at branch coordinate `i`: restrict the `i`th
ambient coordinate to the code.  Thus the intrinsic deck vector space is the
linear dual of the code. -/
def inertiaFunctional (i : Fin r) :
    Module.Dual (_root_.ZMod p) code.carrier where
  toFun codeword := codeword.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem inertiaFunctional_apply (i : Fin r) (codeword : code.carrier) :
    code.inertiaFunctional i codeword = codeword.1 i := rfl

/-- Full support is exactly what makes every intrinsic inertia functional
nonzero. -/
theorem inertiaFunctional_ne_zero (i : Fin r) :
    code.inertiaFunctional i ≠ 0 := by
  obtain ⟨codeword, nonzeroAtI⟩ := code.fullSupport i
  intro functionalZero
  have atCodeword := LinearMap.congr_fun functionalZero codeword
  exact nonzeroAtI (by simpa using atCodeword)

/-- The coordinate-sum-zero hypothesis becomes the product-one relation for
the reconstructed inertia functionals. -/
theorem sum_inertiaFunctional :
    ∑ i, code.inertiaFunctional i = 0 := by
  apply LinearMap.ext
  intro codeword
  have membership : (codeword.1 : CodeSpace p r) ∈
      PrimeBranchDatum.coordinateSumZero (p := p) (r := r) :=
    code.sumZero codeword.2
  have sumZero : ∑ i, codeword.1 i = 0 :=
    LinearMap.mem_ker.mp membership
  simpa only [LinearMap.sum_apply, inertiaFunctional_apply,
    LinearMap.zero_apply] using sumZero

/-- Linear combinations of coordinate restrictions.  This is the dual of
the code inclusion, written using the standard dot-product coordinates on
the ambient space. -/
noncomputable def coordinateCombination :
    CodeSpace p r →ₗ[_root_.ZMod p]
      Module.Dual (_root_.ZMod p) code.carrier :=
  Module.piEquiv (Fin r) (_root_.ZMod p)
    (Module.Dual (_root_.ZMod p) code.carrier) code.inertiaFunctional

@[simp]
theorem coordinateCombination_apply (coefficients : CodeSpace p r)
    (codeword : code.carrier) :
    code.coordinateCombination coefficients codeword =
      dotProduct coefficients codeword.1 := by
  rw [coordinateCombination, Module.piEquiv_apply_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    inertiaFunctional_apply, smul_eq_mul, dotProduct]

/-- Coordinate restrictions span the entire dual of an arbitrary subspace of
the ambient finite product.  This statement itself does not use full support
or sum zero. -/
theorem coordinateCombination_surjective :
    Function.Surjective code.coordinateCombination := by
  intro functional
  obtain ⟨ambientFunctional, restriction⟩ :=
    LinearMap.dualMap_surjective_of_injective
      code.carrier.injective_subtype functional
  obtain ⟨coefficients, coefficientsRepresent⟩ :=
    (coordinateDualEquiv p r).surjective ambientFunctional
  refine ⟨coefficients, ?_⟩
  apply LinearMap.ext
  intro codeword
  rw [code.coordinateCombination_apply]
  have restrictionAt := LinearMap.congr_fun restriction codeword
  have coefficientsAt :=
    LinearMap.congr_fun coefficientsRepresent (codeword.1 : CodeSpace p r)
  exact coefficientsAt.trans restrictionAt

/-- The intrinsic inertia functionals span the dual code. -/
theorem span_inertiaFunctional :
    Submodule.span (_root_.ZMod p)
        (Set.range code.inertiaFunctional) = ⊤ := by
  rw [← Module.range_piEquiv]
  exact LinearMap.range_eq_top.mpr code.coordinateCombination_surjective

/-- Evaluate an element of the double dual on all intrinsic inertia
functionals. -/
def intrinsicEvaluation :
    Module.Dual (_root_.ZMod p)
        (Module.Dual (_root_.ZMod p) code.carrier) →ₗ[_root_.ZMod p]
      CodeSpace p r where
  toFun bidual i := bidual (code.inertiaFunctional i)
  map_add' left right := by
    funext i
    exact LinearMap.add_apply left right (code.inertiaFunctional i)
  map_smul' scalar bidual := by
    funext i
    exact LinearMap.smul_apply scalar bidual (code.inertiaFunctional i)

@[simp]
theorem intrinsicEvaluation_apply (bidual :
    Module.Dual (_root_.ZMod p)
      (Module.Dual (_root_.ZMod p) code.carrier)) (i : Fin r) :
    code.intrinsicEvaluation bidual i =
      bidual (code.inertiaFunctional i) := rfl

/-- Double-dual evaluation reconstructs the original ambient codeword
coordinate by coordinate. -/
@[simp]
theorem intrinsicEvaluation_evalEquiv (codeword : code.carrier) :
    code.intrinsicEvaluation
        (Module.evalEquiv (_root_.ZMod p) code.carrier codeword) =
      codeword.1 := by
  funext i
  rfl

/-- The range of intrinsic evaluation is exactly the original code.  This is
the coordinate-free reconstruction statement. -/
theorem range_intrinsicEvaluation :
    LinearMap.range code.intrinsicEvaluation = code.carrier := by
  apply le_antisymm
  · rintro word ⟨bidual, rfl⟩
    obtain ⟨codeword, rfl⟩ :=
      (Module.evalEquiv (_root_.ZMod p) code.carrier).surjective bidual
    rw [code.intrinsicEvaluation_evalEquiv]
    exact codeword.2
  · intro word membership
    refine ⟨Module.evalEquiv (_root_.ZMod p) code.carrier
      ⟨word, membership⟩, ?_⟩
    exact code.intrinsicEvaluation_evalEquiv ⟨word, membership⟩

/-! ## Adding, and then removing, coordinate choices -/

/-- A finrank equality is exactly what is needed to choose coordinates on the
intrinsic deck space.  The choice is noncomputable, as expected for a basis
choice. -/
noncomputable def deckCoordinatesOfFinrank
    (dimension :
      Module.finrank (_root_.ZMod p) code.carrier = m) :
    DeckSpace p m ≃ₗ[_root_.ZMod p]
      Module.Dual (_root_.ZMod p) code.carrier := by
  apply LinearEquiv.ofFinrankEq
  rw [Module.finrank_pi, Fintype.card_fin,
    Subspace.dual_finrank_eq, dimension]

/-- Choose coordinates on the intrinsic deck space `Dual(code)`.  This is the
only extra datum needed to produce the coordinate model
`PrimeBranchDatum p m r`. -/
def toPrimeBranchDatum
    (coordinates :
      DeckSpace p m ≃ₗ[_root_.ZMod p]
        Module.Dual (_root_.ZMod p) code.carrier) :
    PrimeBranchDatum p m r where
  inertia i := coordinates.symm (code.inertiaFunctional i)
  inertia_ne_zero i := by
    intro equality
    apply code.inertiaFunctional_ne_zero i
    rw [← coordinates.apply_symm_apply (code.inertiaFunctional i), equality]
    exact coordinates.map_zero
  sum_inertia := by
    apply coordinates.injective
    simpa only [map_sum, coordinates.apply_symm_apply, map_zero] using
      code.sum_inertiaFunctional
  span_inertia := by
    rw [show Set.range (fun i => coordinates.symm (code.inertiaFunctional i)) =
        coordinates.symm '' Set.range code.inertiaFunctional by
      ext vector
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨code.inertiaFunctional i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨functional, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩]
    rw [Submodule.span_image_linearEquiv,
      code.span_inertiaFunctional, Submodule.map_top,
      LinearEquiv.range]

/-- The exact converse in coordinate form: full support, coordinate sum zero,
and finrank `m` construct a `PrimeBranchDatum p m r`. -/
noncomputable def toPrimeBranchDatumOfFinrank
    (dimension :
      Module.finrank (_root_.ZMod p) code.carrier = m) :
    PrimeBranchDatum p m r :=
  code.toPrimeBranchDatum (code.deckCoordinatesOfFinrank dimension)

/-- Characters in chosen deck coordinates are canonically equivalent to the
original code.  The construction is: dot product, transport to the double
dual, then finite-dimensional reflexivity. -/
noncomputable def coordinateCharacterEquiv
    (coordinates :
      DeckSpace p m ≃ₗ[_root_.ZMod p]
        Module.Dual (_root_.ZMod p) code.carrier) :
    CoordinateDual p m ≃ₗ[_root_.ZMod p] code.carrier :=
  (coordinateDualEquiv p m).trans
    (coordinates.symm.dualMap.trans
      (Module.evalEquiv (_root_.ZMod p) code.carrier).symm)

/-- Evaluation after an arbitrary coordinate choice is the ambient inclusion
of the corresponding original codeword. -/
theorem evaluationLinearMap_toPrimeBranchDatum
    (coordinates :
      DeckSpace p m ≃ₗ[_root_.ZMod p]
        Module.Dual (_root_.ZMod p) code.carrier)
    (character : CoordinateDual p m) :
    (code.toPrimeBranchDatum coordinates).evaluationLinearMap character =
      (code.coordinateCharacterEquiv coordinates character).1 := by
  funext i
  change
    (coordinateDualEquiv p m character)
        (coordinates.symm (code.inertiaFunctional i)) =
      code.inertiaFunctional i
        ((Module.evalEquiv (_root_.ZMod p) code.carrier).symm
          (coordinates.symm.dualMap (coordinateDualEquiv p m character)))
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

/-- Every coordinate choice reconstructs exactly the original code, as a
submodule of the fixed ambient code space. -/
theorem evaluationCode_toPrimeBranchDatum
    (coordinates :
      DeckSpace p m ≃ₗ[_root_.ZMod p]
        Module.Dual (_root_.ZMod p) code.carrier) :
    (code.toPrimeBranchDatum coordinates).evaluationCode = code.carrier := by
  apply le_antisymm
  · rintro word ⟨character, rfl⟩
    rw [code.evaluationLinearMap_toPrimeBranchDatum coordinates]
    exact (code.coordinateCharacterEquiv coordinates character).2
  · intro word membership
    obtain ⟨character, characterMaps⟩ :=
      (code.coordinateCharacterEquiv coordinates).surjective ⟨word, membership⟩
    refine ⟨character, ?_⟩
    rw [code.evaluationLinearMap_toPrimeBranchDatum coordinates,
      characterMaps]

/-- The finrank-based coordinate converse reconstructs the supplied code
exactly. -/
theorem evaluationCode_toPrimeBranchDatumOfFinrank
    (dimension :
      Module.finrank (_root_.ZMod p) code.carrier = m) :
    (code.toPrimeBranchDatumOfFinrank dimension).evaluationCode =
      code.carrier :=
  code.evaluationCode_toPrimeBranchDatum
    (code.deckCoordinatesOfFinrank dimension)

/-- The evaluation code is independent of the chosen deck coordinates. -/
theorem evaluationCode_independent_of_coordinates
    (first second :
      DeckSpace p m ≃ₗ[_root_.ZMod p]
        Module.Dual (_root_.ZMod p) code.carrier) :
    (code.toPrimeBranchDatum first).evaluationCode =
      (code.toPrimeBranchDatum second).evaluationCode := by
  rw [code.evaluationCode_toPrimeBranchDatum first,
    code.evaluationCode_toPrimeBranchDatum second]

/-- Two coordinate choices produce inertia vectors related by their canonical
linear change of deck coordinates. -/
theorem coordinate_change_inertia
    (first second :
      DeckSpace p m ≃ₗ[_root_.ZMod p]
        Module.Dual (_root_.ZMod p) code.carrier)
    (i : Fin r) :
    (first.trans second.symm)
        ((code.toPrimeBranchDatum first).inertia i) =
      (code.toPrimeBranchDatum second).inertia i := by
  simp [toPrimeBranchDatum]

end FullSupportZeroSumCode

/-! ## Round trip from concrete branch data -/

namespace PrimeBranchDatum

variable (datum : PrimeBranchDatum p m r)

/-- Forget concrete deck coordinates but retain the resulting intrinsic code.
The previously proved sum-zero and full-support theorems discharge exactly the
converse hypotheses. -/
def toFullSupportZeroSumCode : FullSupportZeroSumCode p r where
  carrier := datum.evaluationCode
  sumZero := datum.evaluationCode_le_coordinateSumZero
  fullSupport := datum.evaluationCode_hasFullSupport

/-- The original deck coordinates identify with the dual of the evaluation
code: first use the dot-product self-duality, then dualize the inverse of the
evaluation equivalence. -/
noncomputable def reconstructedDeckCoordinates :
    DeckSpace p m ≃ₗ[_root_.ZMod p]
      Module.Dual (_root_.ZMod p) datum.evaluationCode :=
  (coordinateDualEquiv p m).trans
    datum.evaluationEquiv.symm.dualMap

/-- The canonical coordinates induced by a datum recover every original
inertia vector. -/
theorem reconstructed_inertia (i : Fin r) :
    ((datum.toFullSupportZeroSumCode.toPrimeBranchDatum
      datum.reconstructedDeckCoordinates).inertia i) = datum.inertia i := by
  change datum.reconstructedDeckCoordinates.symm
      (datum.toFullSupportZeroSumCode.inertiaFunctional i) = datum.inertia i
  apply (coordinateDualEquiv p m).injective
  have transported :
      coordinateDualEquiv p m
          (datum.reconstructedDeckCoordinates.symm
            (datum.toFullSupportZeroSumCode.inertiaFunctional i)) =
        datum.evaluationEquiv.dualMap
          (datum.toFullSupportZeroSumCode.inertiaFunctional i) := by
    change coordinateDualEquiv p m
        ((coordinateDualEquiv p m).symm
          (datum.evaluationEquiv.dualMap
            (datum.toFullSupportZeroSumCode.inertiaFunctional i))) = _
    exact (coordinateDualEquiv p m).apply_symm_apply _
  rw [transported]
  apply LinearMap.ext
  intro character
  change datum.evaluationLinearMap character i =
    dotProduct (datum.inertia i) character
  rw [datum.evaluationLinearMap_apply]
  exact dotProduct_comm character (datum.inertia i)

end PrimeBranchDatum

end

end


end AbelianCoverHodge.Mathlib
