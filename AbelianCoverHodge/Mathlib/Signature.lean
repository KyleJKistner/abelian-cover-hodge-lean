module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Pi

/-!
# Integral signature arithmetic over mathlib's `ZMod`

This file is deliberately independent of `Verified.Core`: residues are
mathlib's genuine quotient ring `_root_.ZMod p`, branch words are functions on
a finite coordinate type, and signatures take values in `ℤ`.
-/

open scoped BigOperators

namespace AbelianCoverHodge.Mathlib.Signature

public section

@[expose] section

variable {p : ℕ} [NeZero p]
variable {ι : Type*} [Fintype ι]

/-- A branch word indexed by a finite coordinate type. -/
abbrev BranchWord (p : ℕ) (ι : Type*) := ι → _root_.ZMod p

/-- The least nonnegative representative of a residue class. -/
def leastResidue (x : _root_.ZMod p) : ℕ := x.val

theorem leastResidue_lt (x : _root_.ZMod p) : leastResidue x < p :=
  _root_.ZMod.val_lt x

omit [NeZero p] in
@[simp] theorem leastResidue_zero : leastResidue (0 : _root_.ZMod p) = 0 :=
  _root_.ZMod.val_zero

omit [NeZero p] in
theorem leastResidue_eq_zero_iff (x : _root_.ZMod p) :
    leastResidue x = 0 ↔ x = 0 :=
  _root_.ZMod.val_eq_zero x

/-- Coordinates on which the branch word is nonzero. -/
def support (c : BranchWord p ι) : Finset ι :=
  Finset.univ.filter fun i ↦ c i ≠ 0

/-- Number of nonzero branch coordinates. -/
def supportCard (c : BranchWord p ι) : ℕ := (support c).card

omit [NeZero p] in
@[simp] theorem mem_support [DecidableEq ι] (c : BranchWord p ι) (i : ι) :
    i ∈ support c ↔ c i ≠ 0 := by
  simp [support]

/-- Sum of the coordinates in `ZMod p`. -/
def coordinateSum (c : BranchWord p ι) : _root_.ZMod p :=
  ∑ i, c i

/-- The branch condition used by the signature calculation. -/
def IsBranchWord (c : BranchWord p ι) : Prop := coordinateSum c = 0

/-! ## Invariance under branch-coordinate permutations -/

/-- Reindex a branch word along a permutation of its occurrence set. -/
def reindex (permutation : ι ≃ ι) (c : BranchWord p ι) :
    BranchWord p ι :=
  c ∘ permutation

omit [NeZero p] in
theorem coordinateSum_reindex (permutation : ι ≃ ι)
    (c : BranchWord p ι) :
    coordinateSum (reindex permutation c) = coordinateSum c := by
  exact permutation.sum_comp c

omit [NeZero p] in
theorem isBranchWord_reindex (permutation : ι ≃ ι)
    {c : BranchWord p ι} (hc : IsBranchWord c) :
    IsBranchWord (reindex permutation c) := by
  rw [IsBranchWord, coordinateSum_reindex]
  exact hc

omit [NeZero p] in
theorem supportCard_reindex (permutation : ι ≃ ι)
    (c : BranchWord p ι) :
    supportCard (reindex permutation c) = supportCard c := by
  classical
  rw [supportCard, supportCard, support, support,
    Finset.card_filter, Finset.card_filter]
  change (∑ i, if c (permutation i) ≠ 0 then 1 else 0) =
    ∑ i, if c i ≠ 0 then 1 else 0
  exact Fintype.sum_equiv permutation
    (fun i ↦ if c (permutation i) ≠ 0 then 1 else 0)
    (fun i ↦ if c i ≠ 0 then 1 else 0) (fun _ ↦ rfl)

/-- Multiplication by a cyclotomic/Galois row. -/
def scale (a : _root_.ZMod p) (c : BranchWord p ι) : BranchWord p ι :=
  fun i ↦ a * c i

omit [NeZero p] in
theorem isBranchWord_neg {c : BranchWord p ι} (hc : IsBranchWord c) :
    IsBranchWord (-c) := by
  simpa [IsBranchWord, coordinateSum] using congrArg Neg.neg hc

omit [NeZero p] in
theorem isBranchWord_scale (a : _root_.ZMod p) {c : BranchWord p ι}
    (hc : IsBranchWord c) : IsBranchWord (scale a c) := by
  change ∑ i, a * c i = 0
  change (∑ i, c i) = 0 at hc
  rw [← Finset.mul_sum, hc, mul_zero]

omit [NeZero p] in
theorem support_neg (c : BranchWord p ι) : support (-c) = support c := by
  classical
  ext i
  simp [support]

omit [NeZero p] in
@[simp] theorem supportCard_neg (c : BranchWord p ι) :
    supportCard (-c) = supportCard c := by
  rw [supportCard, supportCard, support_neg]

omit [NeZero p] in
theorem support_scale_of_isUnit (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) : support (scale a c) = support c := by
  classical
  ext i
  simp [support, scale, ha.mul_right_eq_zero]

omit [NeZero p] in
theorem supportCard_scale_of_isUnit (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) :
    supportCard (scale a c) = supportCard c := by
  rw [supportCard, supportCard, support_scale_of_isUnit a ha]

/-! ## `q` and its exact divisibility -/

/-- Undivided Chevalley--Weil numerator at row `a`. -/
def qNumerator (a : _root_.ZMod p) (c : BranchWord p ι) : ℕ :=
  ∑ i, leastResidue (a * c i)

omit [NeZero p] in
theorem qNumerator_reindex (a : _root_.ZMod p)
    (permutation : ι ≃ ι) (c : BranchWord p ι) :
    qNumerator a (reindex permutation c) = qNumerator a c := by
  exact permutation.sum_comp (fun i ↦ leastResidue (a * c i))

/-- Chevalley--Weil integer `q_a(c)`.  Exactness is supplied by
`p_dvd_qNumerator` for branch words. -/
def qValue (a : _root_.ZMod p) (c : BranchWord p ι) : ℕ :=
  qNumerator a c / p

omit [NeZero p] in
theorem qValue_reindex (a : _root_.ZMod p)
    (permutation : ι ≃ ι) (c : BranchWord p ι) :
    qValue a (reindex permutation c) = qValue a c := by
  rw [qValue, qValue, qNumerator_reindex]

/-- Coordinate sum zero forces the sum of least representatives to be a
multiple of `p`. -/
theorem p_dvd_qNumerator (a : _root_.ZMod p) (c : BranchWord p ι)
    (hc : IsBranchWord c) : p ∣ qNumerator a c := by
  rw [← _root_.ZMod.natCast_eq_zero_iff (qNumerator a c) p]
  calc
    (qNumerator a c : _root_.ZMod p) =
        ∑ i, (leastResidue (a * c i) : _root_.ZMod p) := by
          simp only [qNumerator, Nat.cast_sum]
    _ = ∑ i, a * c i := by
      apply Finset.sum_congr rfl
      intro i _
      exact _root_.ZMod.natCast_zmod_val (a * c i)
    _ = a * ∑ i, c i := by rw [Finset.mul_sum]
    _ = 0 := by
      change (∑ i, c i) = 0 at hc
      rw [hc, mul_zero]

/-- On a branch word, division in `qValue` is exact. -/
theorem p_mul_qValue (a : _root_.ZMod p) (c : BranchWord p ι)
    (hc : IsBranchWord c) :
    p * qValue a c = qNumerator a c := by
  exact Nat.mul_div_cancel' (p_dvd_qNumerator a c hc)

/-! ## Complementary residues and integral delta -/

/-- Sum of least residues in an already-scaled row. -/
def residueSum (c : BranchWord p ι) : ℕ := ∑ i, leastResidue (c i)

theorem leastResidue_neg_add (x : _root_.ZMod p) :
    leastResidue (-x) + leastResidue x = if x = 0 then 0 else p := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [leastResidue, leastResidue, _root_.ZMod.neg_val]
    simp only [hx, if_false]
    exact Nat.sub_add_cancel (_root_.ZMod.val_le x)

/-- Complementing every residue contributes one copy of `p` at every
nonzero coordinate. -/
theorem residueSum_neg_add (c : BranchWord p ι) :
    residueSum (-c) + residueSum c = p * supportCard c := by
  classical
  rw [residueSum, residueSum, ← Finset.sum_add_distrib]
  calc
    (∑ i, (leastResidue ((-c) i) + leastResidue (c i))) =
        ∑ i, if c i ≠ 0 then p else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Pi.neg_apply, leastResidue_neg_add]
      by_cases hi : c i = 0 <;> simp [hi]
    _ = p * supportCard c := by
      rw [supportCard]
      calc
        (∑ i, if c i ≠ 0 then p else 0) =
            p * ∑ i, if c i ≠ 0 then 1 else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : c i ≠ 0 <;> simp [hi]
        _ = p * (support c).card := by
          rw [Finset.sum_boole]
          rfl

omit [NeZero p] in
@[simp] theorem qNumerator_eq_residueSum_scale
    (a : _root_.ZMod p) (c : BranchWord p ι) :
    qNumerator a c = residueSum (scale a c) := rfl

omit [NeZero p] in
theorem qNumerator_neg_word (a : _root_.ZMod p) (c : BranchWord p ι) :
    qNumerator a (-c) = residueSum (-(scale a c)) := by
  simp [qNumerator, residueSum, scale]

theorem qNumerator_neg_add (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) :
    qNumerator a (-c) + qNumerator a c = p * supportCard c := by
  rw [qNumerator_neg_word, qNumerator_eq_residueSum_scale,
      residueSum_neg_add, supportCard_scale_of_isUnit a ha]

theorem qValue_neg_add (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) (hc : IsBranchWord c) :
    qValue a (-c) + qValue a c = supportCard c := by
  have hp : 0 < p := NeZero.pos p
  apply Nat.eq_of_mul_eq_mul_left hp
  rw [Nat.mul_add, p_mul_qValue a (-c) (isBranchWord_neg hc),
      p_mul_qValue a c hc, qNumerator_neg_add a ha c]

/-- Integral signature `δ_a(c) = |supp(c)| - 2 q_a(c)`. -/
def delta (a : _root_.ZMod p) (c : BranchWord p ι) : ℤ :=
  (supportCard c : ℤ) - 2 * (qValue a c : ℤ)

omit [NeZero p] in
theorem delta_reindex (a : _root_.ZMod p)
    (permutation : ι ≃ ι) (c : BranchWord p ι) :
    delta a (reindex permutation c) = delta a c := by
  rw [delta, delta, supportCard_reindex, qValue_reindex]

/-- Negating a branch word negates its signature at every unit row. -/
theorem delta_neg_word (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) (hc : IsBranchWord c) :
    delta a (-c) = -delta a c := by
  have hq := qValue_neg_add a ha c hc
  simp only [delta, supportCard_neg]
  omega

omit [NeZero p] in
theorem qNumerator_neg_left (a : _root_.ZMod p) (c : BranchWord p ι) :
    qNumerator (-a) c = qNumerator a (-c) := by
  simp [qNumerator]

omit [NeZero p] in
theorem qValue_neg_left (a : _root_.ZMod p) (c : BranchWord p ι) :
    qValue (-a) c = qValue a (-c) := by
  rw [qValue, qValue, qNumerator_neg_left]

/-- The opposite Galois row has the opposite signature. -/
theorem delta_neg_row (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) (hc : IsBranchWord c) :
    delta (-a) c = -delta a c := by
  rw [delta, qValue_neg_left]
  simpa only [delta, supportCard_neg] using delta_neg_word a ha c hc

/-! ## Determinant/exponent signature as a linear map -/

variable {κ : Type*} [Fintype κ]

/-- Dot product with a fixed signature column, bundled as a genuine
`ℤ`-linear map on finite exponent vectors. -/
def exponentSignatureMap (column : κ → ℤ) : (κ → ℤ) →ₗ[ℤ] ℤ where
  toFun exponent := ∑ k, exponent k * column k
  map_add' left right := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' scalar exponent := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact (Finset.mul_sum Finset.univ
      (fun k ↦ exponent k * column k) scalar).symm

@[simp] theorem exponentSignatureMap_apply (column : κ → ℤ)
    (exponent : κ → ℤ) :
    exponentSignatureMap column exponent =
      ∑ k, exponent k * column k := rfl

/-- Signature of determinant exponents attached to a finite family of branch
words. -/
def determinantSignatureMap (a : _root_.ZMod p)
    (words : κ → BranchWord p ι) : (κ → ℤ) →ₗ[ℤ] ℤ :=
  exponentSignatureMap fun k ↦ delta a (words k)

omit [NeZero p] in
@[simp] theorem determinantSignatureMap_apply (a : _root_.ZMod p)
    (words : κ → BranchWord p ι) (exponent : κ → ℤ) :
    determinantSignatureMap a words exponent =
      ∑ k, exponent k * delta a (words k) := rfl

omit [NeZero p] in
theorem determinantSignatureMap_add (a : _root_.ZMod p)
    (words : κ → BranchWord p ι) (left right : κ → ℤ) :
    determinantSignatureMap a words (left + right) =
      determinantSignatureMap a words left +
        determinantSignatureMap a words right :=
  map_add (determinantSignatureMap a words) left right

omit [NeZero p] in
theorem determinantSignatureMap_zsmul (a : _root_.ZMod p)
    (words : κ → BranchWord p ι) (n : ℤ) (exponent : κ → ℤ) :
    determinantSignatureMap a words (n • exponent) =
      n * determinantSignatureMap a words exponent := by
  simpa only [smul_eq_mul] using
    map_smul (determinantSignatureMap a words) n exponent

end

end


end AbelianCoverHodge.Mathlib.Signature
