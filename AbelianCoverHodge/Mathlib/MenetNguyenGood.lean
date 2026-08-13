module

public import AbelianCoverHodge.Mathlib.Signature
public import Mathlib.Algebra.Order.Field.Rat

/-!
# The Menet--Nguyen case-(a) hypothesis match

This module formalizes only the arithmetic hypothesis match used by the Phase I
manuscript.  It does **not** assert Menet--Nguyen's monodromy theorem.

Source pin: G. Menet and D.-M. Nguyen, *Representations of braid groups via
cyclic covers of the sphere: Zariski closure and arithmeticity*,
arXiv:2310.10401v3 (16 November 2024), Definition 1.1(a) and Theorem 5.1.
Definition 1.1(a) calls a sequence `μᵢ ∈ ℚ ∩ (0,1)` good when
`1 < ∑ μᵢ < n - 1`.  Theorem 5.1 has further geometric and arithmetic standing
hypotheses (including connectedness and a primitive root); none is bundled into
the definition below.

Manuscript pin: `manuscripts/phase_I_complete.tex`, equation `CW` and the proof
of `prop:full-projection`, where positivity of
`d(c)=s(c)-q(c)-1` and `d(-c)=q(c)-1` is claimed to imply case (a).

For a branch word, the source sequence is indexed only by its nonzero support:
`μᵢ = [a cᵢ]ₚ / p`.  Restriction to the support and the assumption that `a` is a
unit are essential for the source requirement `μᵢ ∈ (0,1)`.
-/

open scoped BigOperators

namespace AbelianCoverHodge.Mathlib.MenetNguyenGood

public section

@[expose] section

open AbelianCoverHodge.Mathlib.Signature

variable {p : ℕ} [NeZero p]
variable {ι : Type*} [Fintype ι]

/-- Menet--Nguyen Definition 1.1(a), represented on a finite set of indices.
The first conjunct records the ambient requirement preceding cases (a) and
(b), namely that every entry lies in `ℚ ∩ (0,1)`. -/
def GoodSequenceCaseA (indices : Finset ι) (μ : ι → ℚ) : Prop :=
  (∀ i ∈ indices, 0 < μ i ∧ μ i < 1) ∧
    1 < ∑ i ∈ indices, μ i ∧
      ∑ i ∈ indices, μ i < (indices.card : ℚ) - 1

/-- Fractional residue sequence attached to row `a` and branch word `c`. -/
def fractionalResidue (a : _root_.ZMod p) (c : BranchWord p ι)
    (i : ι) : ℚ :=
  (leastResidue (a * c i) : ℚ) / p

/-- The manuscript's two Chevalley--Weil multiplicities, at the arithmetic
level consumed by the hypothesis match. -/
def hodge10 (a : _root_.ZMod p) (c : BranchWord p ι) : ℕ :=
  supportCard c - qValue a c - 1

def hodge01 (a : _root_.ZMod p) (c : BranchWord p ι) : ℕ :=
  qValue a c - 1

/-- Positivity of both Hodge multiplicities. -/
def PositiveHodgePair (a : _root_.ZMod p) (c : BranchWord p ι) : Prop :=
  0 < hodge10 a c ∧ 0 < hodge01 a c

omit [NeZero p] in
/-- Positivity is exactly the integral form of the two strict bounds in
Definition 1.1(a). -/
theorem positiveHodgePair_iff_qBounds (a : _root_.ZMod p)
    (c : BranchWord p ι) :
    PositiveHodgePair a c ↔
      1 < qValue a c ∧ qValue a c + 1 < supportCard c := by
  unfold PositiveHodgePair hodge10 hodge01
  omega

omit [NeZero p] in
/-- Outside the support, a fractional-residue summand is zero. -/
theorem fractionalResidue_eq_zero_of_not_mem_support
    (a : _root_.ZMod p) (c : BranchWord p ι) (i : ι)
    (hi : i ∉ support c) : fractionalResidue a c i = 0 := by
  have hci : c i = 0 := by
    by_contra hne
    exact hi (by simp [support, hne])
  simp [fractionalResidue, hci]

omit [NeZero p] in
/-- Restricting the numerator sum to the nonzero support loses no terms. -/
theorem sum_leastResidue_support (a : _root_.ZMod p)
    (c : BranchWord p ι) :
    ∑ i ∈ support c, leastResidue (a * c i) = qNumerator a c := by
  classical
  unfold qNumerator
  exact Finset.sum_subset (Finset.subset_univ (support c)) (by
    intro i _ hi
    have hci : c i = 0 := by
      by_contra hne
      exact hi (by simp [support, hne])
    simp [hci])

/-- The rational sum in Definition 1.1(a) is the integer `q_a(c)` for a
branch word. -/
theorem sum_fractionalResidue_support (a : _root_.ZMod p)
    (c : BranchWord p ι) (hc : IsBranchWord c) :
    ∑ i ∈ support c, fractionalResidue a c i = qValue a c := by
  simp only [fractionalResidue, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [← Nat.cast_sum, sum_leastResidue_support]
  rw [← p_mul_qValue a c hc, Nat.cast_mul]
  have hp : (p : ℚ) ≠ 0 := by
    exact_mod_cast NeZero.ne p
  rw [← div_eq_mul_inv]
  exact mul_div_cancel_left₀ (qValue a c : ℚ) hp

/-- A unit row sends every active label to a rational number strictly between
zero and one, exactly as required before Menet--Nguyen Definition 1.1. -/
theorem fractionalResidue_mem_openUnitInterval
    (a : _root_.ZMod p) (ha : IsUnit a) (c : BranchWord p ι)
    (i : ι) (hi : i ∈ support c) :
    0 < fractionalResidue a c i ∧ fractionalResidue a c i < 1 := by
  have hci : c i ≠ 0 := by simpa [support] using hi
  have hac : a * c i ≠ 0 := by
    simpa [ha.mul_right_eq_zero] using hci
  have hresPos : 0 < leastResidue (a * c i) := by
    exact Nat.pos_of_ne_zero ((leastResidue_eq_zero_iff (a * c i)).not.mpr hac)
  have hresLt : leastResidue (a * c i) < p := leastResidue_lt (a * c i)
  have hp : (0 : ℚ) < p := by exact_mod_cast NeZero.pos p
  have hresPosQ : (0 : ℚ) < leastResidue (a * c i) := by
    exact_mod_cast hresPos
  have hresLtQ : (leastResidue (a * c i) : ℚ) < p := by
    exact_mod_cast hresLt
  constructor
  · exact div_pos hresPosQ hp
  · apply (div_lt_iff₀ hp).2
    simpa using hresLtQ

/-- Exact hypothesis match: the manuscript's positive Chevalley--Weil pair is
equivalent to Menet--Nguyen's case-(a) good-sequence condition for the
fractional residue sequence on the active support.

This theorem proves no monodromy statement; Theorem 5.1 remains a separately
audited external input with its remaining hypotheses stated at the call site. -/
theorem positiveHodgePair_iff_goodSequenceCaseA
    (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) (hc : IsBranchWord c) :
    PositiveHodgePair a c ↔
      GoodSequenceCaseA (support c) (fractionalResidue a c) := by
  rw [positiveHodgePair_iff_qBounds]
  constructor
  · rintro ⟨hqLower, hqUpper⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact fractionalResidue_mem_openUnitInterval a ha c i hi
    · rw [sum_fractionalResidue_support a c hc]
      exact_mod_cast hqLower
    · rw [sum_fractionalResidue_support a c hc]
      apply (lt_sub_iff_add_lt).2
      have hcast : (qValue a c + 1 : ℕ) < supportCard c := hqUpper
      exact_mod_cast hcast
  · rintro ⟨_, hqLower, hqUpper⟩
    rw [sum_fractionalResidue_support a c hc] at hqLower hqUpper
    constructor
    · exact_mod_cast hqLower
    · have hcast : (qValue a c : ℚ) + 1 < supportCard c :=
        (lt_sub_iff_add_lt).1 hqUpper
      exact_mod_cast hcast

/-- The forward direction, named for direct use at the external-theorem
boundary. -/
theorem goodSequenceCaseA_of_positiveHodgePair
    (a : _root_.ZMod p) (ha : IsUnit a)
    (c : BranchWord p ι) (hc : IsBranchWord c)
    (hpositive : PositiveHodgePair a c) :
    GoodSequenceCaseA (support c) (fractionalResidue a c) :=
  (positiveHodgePair_iff_goodSequenceCaseA a ha c hc).mp hpositive

end

end

end AbelianCoverHodge.Mathlib.MenetNguyenGood
