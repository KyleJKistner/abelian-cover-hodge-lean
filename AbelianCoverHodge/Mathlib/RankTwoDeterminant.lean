module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The rank-two standard-to-dual determinant character

An element of `Hom(V*, V)` is acted on by congruence `T ↦ A T Aᵀ`.
On the alternating line in dimension two, this is multiplication by `det A`.
Thus, when `epsilon` denotes the determinant character, this line has
character `epsilon`, rather than `2 epsilon`. The reverse Hom line has the
inverse character. This file proves the concrete matrix identity and the
uniqueness of its coefficient; it makes no geometric Hodge claim.
-/

namespace AbelianCoverHodge.Mathlib.RankTwoDeterminant

public section

@[expose] section

variable (R : Type*) [CommRing R]

/-- The alternating tensor, written as a map from the dual standard module
to the standard module in the chosen two-element basis. -/
def alternatingMatrix : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- The alternating line in `Hom(V*, V)` transforms by the determinant,
over any commutative coefficient ring. Invertibility is unnecessary for the
polynomial identity. -/
theorem congruence_eq_det_smul (A : Matrix (Fin 2) (Fin 2) R) :
    A * alternatingMatrix R * A.transpose = A.det • alternatingMatrix R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alternatingMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two] <;> ring

/-- Any proposed scalar character for this action must equal `det A`.
This directly rules out the doubled determinant normalization in the legacy
rank-two calculation. -/
theorem congruence_coefficient_unique (A : Matrix (Fin 2) (Fin 2) R)
    (coefficient : R)
    (action : A * alternatingMatrix R * A.transpose =
      coefficient • alternatingMatrix R) :
    coefficient = A.det := by
  rw [congruence_eq_det_smul R A] at action
  have entry := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 0 1) action
  simpa [alternatingMatrix] using entry.symm

end

end

end AbelianCoverHodge.Mathlib.RankTwoDeterminant
