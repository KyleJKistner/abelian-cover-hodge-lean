module

public import AbelianCoverHodge.Verified.Core

/-!
# Aoki balance and fusion bookkeeping

This module isolates the exact finite-combinatorial layer used between a
determinant-signature relation and the geometric fusion construction.

* `IsAokiBalanced` is the manuscript's balance condition at every nonzero
  Galois row.
* `OppositePairingWitness` records simplicity by an actual list permutation,
  not merely by a Boolean check.
* Opposite-paired words are proved balanced at every nonzero row for a prime
  modulus.
* the published converse is not asserted here; its exact source-facing input
  lives separately in `External/Aoki.lean`.
* `FusionComponent` packages the exact numerical hypotheses under which the
  compact-type rank calculation is valid.

No geometric curve, admissible cover, smoothing, or cycle is represented here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace AbelianCoverHodge.Verified

public section

@[expose] section

/-! ## Nonzero Galois rows -/

/-- An elementary primality predicate sufficient to expose the prime
hypothesis in the Aoki interface without importing a number-theory library. -/
def IsPrimeModulus (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- A row acts invertibly on residues exactly when its least residue is
coprime to the modulus. -/
def IsInvertibleRow {p : Nat} (a : ZMod p) : Prop :=
  Nat.Coprime a.val p

theorem nonzero_row_invertible_of_prime {p : Nat} [NeZero p]
    (hp : IsPrimeModulus p) (a : ZMod p) (ha : a ≠ zzero p) :
    IsInvertibleRow a := by
  unfold IsInvertibleRow Nat.Coprime
  rcases hp.2 (Nat.gcd a.val p) (Nat.gcd_dvd_right a.val p) with hg | hg
  · exact hg
  · have hpda : p ∣ a.val := by
      simpa only [hg] using Nat.gcd_dvd_left a.val p
    have hav : a.val ≠ 0 := by
      intro h
      apply ha
      apply Fin.ext
      simpa using h
    have hple : p ≤ a.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hav) hpda
    exact (Nat.not_le_of_gt a.isLt hple).elim

theorem zmul_ne_zero_of_invertible {p : Nat} [NeZero p]
    (a x : ZMod p) (ha : IsInvertibleRow a) (hx : x ≠ zzero p) :
    zmul a x ≠ zzero p := by
  intro hzero
  have hval : (zmul a x).val = 0 := congrArg Fin.val hzero
  have hmod : (a.val * x.val) % p = 0 := by
    simpa [zmul, zOfNat] using hval
  have hdvd : p ∣ a.val * x.val := Nat.dvd_of_mod_eq_zero hmod
  have hpdvdx : p ∣ x.val := ha.symm.dvd_of_dvd_mul_left hdvd
  have hxv : x.val ≠ 0 := by
    intro h
    apply hx
    apply Fin.ext
    simpa using h
  have hple : p ≤ x.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hxv) hpdvdx
  exact (Nat.not_le_of_gt x.isLt) hple

/-! ## Exact all-row balance -/

/-- Every listed residue is nonzero.  Aoki's theorem is stated for tuples in
`(F_p^×)^S`, so this hypothesis is part of its exact input. -/
def AllResiduesNonzero {p : Nat} [NeZero p] (residues : BranchWord p) : Prop :=
  ∀ x ∈ residues, x ≠ zzero p

/-- The division-free manuscript condition
`sum_i [a β_i]_p = p S / 2`, simultaneously for every nonzero Galois row.
The doubled form avoids any parity or division side condition. -/
def IsAokiBalanced (p : Nat) [NeZero p] (residues : BranchWord p) : Prop :=
  ∀ a : ZMod p, a ≠ zzero p →
    2 * galoisResidueSum a residues = p * llength residues

/-- For an odd modulus, the doubled balance equation itself forces Aoki's
even-length premise.  This is a manuscript-specific discharge of the source
side condition, not part of Aoki's imported theorem. -/
theorem aokiBalanced_length_even_of_odd {p : Nat} [NeZero p]
    (hpGtOne : 1 < p) (hpOdd : p % 2 = 1) {residues : BranchWord p}
    (balanced : IsAokiBalanced p residues) :
    llength residues % 2 = 0 := by
  have rowOneNonzero : zOfNat p 1 ≠ zzero p := by
    intro equality
    have values := congrArg Fin.val equality
    simp [zOfNat, Nat.mod_eq_of_lt hpGtOne] at values
  have equation := balanced (zOfNat p 1) rowOneNonzero
  have parity := congrArg (fun n : Nat ↦ n % 2) equation
  symm
  simpa [Nat.mul_mod, hpOdd] using parity

/-- Every prime modulus other than two is odd, so the preceding arithmetic
lemma discharges Aoki's even-length premise in the odd-prime application. -/
theorem aokiBalanced_length_even_of_prime_ne_two {p : Nat} [NeZero p]
    (hp : IsPrimeModulus p) (hpNotTwo : p ≠ 2)
    {residues : BranchWord p} (balanced : IsAokiBalanced p residues) :
    llength residues % 2 = 0 := by
  have hpOdd : p % 2 = 1 := by
    have hmodLt : p % 2 < 2 := Nat.mod_lt p (by omega)
    have hmodNonzero : p % 2 ≠ 0 := by
      intro hmodZero
      have twoDvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero hmodZero
      rcases hp.2 2 twoDvd with twoEqOne | twoEqP
      · omega
      · exact hpNotTwo twoEqP.symm
    omega
  apply aokiBalanced_length_even_of_odd
  · have hpAtLeastTwo := hp.1
    omega
  · exact hpOdd
  · exact balanced

/-- At an invertible row, a nonzero opposite pair has least residues summing
to the modulus. -/
theorem scaled_opposite_pair_value_sum {p : Nat} [NeZero p]
    (a x : ZMod p) (ha : IsInvertibleRow a) (hx : x ≠ zzero p) :
    (zmul a x).val + (zmul a (zneg x)).val = p := by
  have hax : zmul a x ≠ zzero p :=
    zmul_ne_zero_of_invertible a x ha hx
  have hnx : zneg x ≠ zzero p := zneg_ne_zero x hx
  have hanx : zmul a (zneg x) ≠ zzero p :=
    zmul_ne_zero_of_invertible a (zneg x) ha hnx
  have hnegval : (zneg x).val = p - x.val :=
    zneg_val_of_ne_zero x hx
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have haxv : (zmul a x).val ≠ 0 := by
    intro h
    apply hax
    apply Fin.ext
    simpa using h
  have hanxv : (zmul a (zneg x)).val ≠ 0 := by
    intro h
    apply hanx
    apply Fin.ext
    simpa using h
  have hmod :
      ((zmul a x).val + (zmul a (zneg x)).val) % p = 0 := by
    simp only [zmul, zOfNat]
    rw [hnegval, ← Nat.add_mod]
    have hxp : x.val ≤ p := Nat.le_of_lt x.isLt
    have hsplit : x.val + (p - x.val) = p := by omega
    have heq : a.val * x.val + a.val * (p - x.val) = a.val * p := by
      rw [← Nat.mul_add, hsplit]
    rw [heq]
    simp
  have hdvd : p ∣ (zmul a x).val + (zmul a (zneg x)).val :=
    Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < (zmul a x).val + (zmul a (zneg x)).val := by
    omega
  have hlt : (zmul a x).val + (zmul a (zneg x)).val < 2 * p := by
    have h1 := (zmul a x).isLt
    have h2 := (zmul a (zneg x)).isLt
    omega
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    rw [hkzero, Nat.mul_zero] at hk
    omega
  have hklt : k < 2 := by
    apply (Nat.mul_lt_mul_left hp).mp
    rw [← hk, Nat.mul_comm p 2]
    exact hlt
  have hkone : k = 1 := by omega
  rw [hkone, Nat.mul_one] at hk
  exact hk

/-- Exact Galois-row sum of an explicit list of opposite pairs. -/
theorem pairResidues_galoisResidueSum {p : Nat} [NeZero p]
    (a : ZMod p) (representatives : List (ZMod p))
    (ha : IsInvertibleRow a)
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p) :
    galoisResidueSum a (pairResidues representatives) =
      p * llength representatives := by
  induction representatives with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ≠ zzero p := hnonzero x (by simp)
      have hxs : ∀ y ∈ xs, y ≠ zzero p := by
        intro y hy
        exact hnonzero y (by simp [hy])
      have hpair := scaled_opposite_pair_value_sum a x ha hx
      simp only [pairResidues, galoisResidueSum, scaleWord,
        residueValueSum, llength]
      change (zmul a x).val +
        ((zmul a (zneg x)).val +
          galoisResidueSum a (pairResidues xs)) =
        p * (llength xs + 1)
      rw [ih hxs]
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- The easy direction complementary to Aoki: for a prime modulus, every
explicit opposite-pair word is balanced at every nonzero Galois row. -/
theorem pairResidues_aokiBalanced {p : Nat} [NeZero p]
    (hp : IsPrimeModulus p) (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p) :
    IsAokiBalanced p (pairResidues representatives) := by
  intro a ha
  rw [pairResidues_galoisResidueSum a representatives
      (nonzero_row_invertible_of_prime hp a ha) hnonzero,
      pairResidues_length]
  ac_rfl

/-! ## Concrete simplicity witness -/

/-- A concrete witness that a residue tuple is simple: up to an explicit
permutation, it is a list of nonzero opposite pairs. -/
structure OppositePairingWitness {p : Nat} [NeZero p]
    (residues : BranchWord p) where
  representatives : List (ZMod p)
  representatives_nonzero :
    ∀ x ∈ representatives, x ≠ zzero p
  perm : residues.Perm (pairResidues representatives)

theorem llength_eq_of_perm {xs ys : List α} (h : xs.Perm ys) :
    llength xs = llength ys := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [llength, ih]
  | swap x y l => rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem galoisResidueSum_eq_of_perm {p : Nat} [NeZero p]
    (a : ZMod p) {xs ys : BranchWord p} (h : xs.Perm ys) :
    galoisResidueSum a xs = galoisResidueSum a ys := by
  induction h with
  | nil => rfl
  | cons x h ih =>
      change (zmul a x).val + galoisResidueSum a _ =
        (zmul a x).val + galoisResidueSum a _
      rw [ih]
  | swap x y l =>
      change (zmul a y).val + ((zmul a x).val + galoisResidueSum a l) =
        (zmul a x).val + ((zmul a y).val + galoisResidueSum a l)
      omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mem_pairResidues_ne_zero {p : Nat} [NeZero p]
    (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p)
    {x : ZMod p} (hx : x ∈ pairResidues representatives) :
    x ≠ zzero p := by
  induction representatives with
  | nil =>
      simp only [pairResidues, List.not_mem_nil] at hx
  | cons y ys ih =>
      simp only [pairResidues, List.mem_cons] at hx
      rcases hx with hxy | hxy | htail
      · subst x
        exact hnonzero y (by simp)
      · subst x
        exact zneg_ne_zero y (hnonzero y (by simp))
      · have htailNonzero : ∀ z ∈ ys, z ≠ zzero p := by
          intro z hz
          exact hnonzero z (by simp [hz])
        exact ih htailNonzero htail

theorem OppositePairingWitness.allResiduesNonzero
    {p : Nat} [NeZero p] {residues : BranchWord p}
    (witness : OppositePairingWitness residues) :
    AllResiduesNonzero residues := by
  intro x hx
  have hxpair : x ∈ pairResidues witness.representatives :=
    witness.perm.mem_iff.mp hx
  exact mem_pairResidues_ne_zero witness.representatives
    witness.representatives_nonzero hxpair

theorem OppositePairingWitness.aokiBalanced
    {p : Nat} [NeZero p] {residues : BranchWord p}
    (witness : OppositePairingWitness residues)
    (hp : IsPrimeModulus p) : IsAokiBalanced p residues := by
  intro a ha
  have hpaired := pairResidues_aokiBalanced hp witness.representatives
    witness.representatives_nonzero a ha
  rw [galoisResidueSum_eq_of_perm a witness.perm,
      llength_eq_of_perm witness.perm]
  exact hpaired

/-! ## Fusion rank bookkeeping -/

/-- Numerical data for one connected component of the manuscript's pairing
graph.  Geometry must separately show that its selected edges really form a
spanning tree of inverse-inertia nodes. -/
structure FusionComponent where
  branches : Nat
  vertices : Nat
  treeEdges : Nat
  vertices_pos : 0 < vertices
  tree_edge_count : treeEdges = vertices - 1
  enough_branches : 2 * vertices ≤ branches

theorem FusionComponent.remainingBranches_eq (component : FusionComponent) :
    remainingBranches component.branches component.treeEdges =
      component.branches - 2 * (component.vertices - 1) := by
  simp [remainingBranches, component.tree_edge_count]

theorem FusionComponent.rank_preserved (component : FusionComponent) :
    originalKRank component.branches component.vertices =
      fusedKRank component.branches component.treeEdges :=
  fusion_rank_identity component.branches component.vertices
    component.treeEdges component.vertices_pos component.tree_edge_count
    component.enough_branches

end


end


end AbelianCoverHodge.Verified
