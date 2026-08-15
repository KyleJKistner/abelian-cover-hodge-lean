module

public import AbelianCoverHodge.Verified.IntegralSignature
public import AbelianCoverHodge.External.Aoki

/-!
# Determinant signatures give Aoki pairings

This module closes the finite, manuscript-specific deduction between a
zero-signature determinant relation and the exact published Aoki input.
Its hypotheses mention the literal determinant terms: every underlying word
has branch sum zero, and the additive integral determinant signature vanishes
at every nonzero cyclotomic row.

The resulting Aoki tuple is the literal concatenation
`Verified.determinantResidues terms`.  Its entries are nonzero by construction,
its all-row balance is proved from the integral signature calculation, and
the even-length side condition is derived for a prime modulus different from
two.  The only imported implication in the final theorem is the prime
balanced-tuple statement recorded by Aoki and credited there to Parry, passed
explicitly as `External.AokiPrimeBalanceInput`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace AbelianCoverHodge.Bridge

public section

@[expose] section

open AbelianCoverHodge.Verified

/-! ## Concrete determinant hypotheses -/

/-- Every unsigned word occurring in the determinant expression is a genuine
branch word.  This recursive definition is deliberately transparent: it does
not package divisibility or any later project deduction as an assumption. -/
def BranchValidDeterminantTerms {p : Nat} [NeZero p] :
    List (SignedWord p) → Prop
  | [] => True
  | term :: terms =>
      isBranchWord term.word ∧ BranchValidDeterminantTerms terms

/-- The additive integral determinant signature vanishes at every nonzero
cyclotomic row.  The zero row is excluded because it is not a Galois embedding
and its signature is generally the total support rather than zero. -/
def AllNonzeroRowIntegralSignaturesZero {p : Nat} [NeZero p]
    (terms : List (SignedWord p)) : Prop :=
  ∀ a : ZMod p, a ≠ zzero p →
    integralDeterminantSignatureAt a terms = 0

/-! ## Branch validity is stable under the determinant operations -/

/-- Scaling a branch word by a residue multiplies its total residue modulo
`p`.  This is the explicit modular identity behind preservation of the branch
condition. -/
theorem residueValueSum_scaleWord_mod {p : Nat} [NeZero p]
    (a : ZMod p) (word : BranchWord p) :
    residueValueSum (scaleWord a word) % p =
      (a.val * residueValueSum word) % p := by
  induction word with
  | nil => simp [scaleWord, residueValueSum]
  | cons x word ih =>
      simp only [scaleWord, residueValueSum, zmul, zOfNat]
      calc
        (a.val * x.val % p + residueValueSum (scaleWord a word)) % p =
            ((a.val * x.val % p) % p +
              residueValueSum (scaleWord a word) % p) % p :=
          Nat.add_mod _ _ _
        _ = ((a.val * x.val % p) % p +
              (a.val * residueValueSum word) % p) % p := by
          rw [ih]
        _ = (a.val * x.val + a.val * residueValueSum word) % p := by
          rw [Nat.mod_mod]
          exact (Nat.add_mod _ _ _).symm
        _ = (a.val * (x.val + residueValueSum word)) % p := by
          rw [Nat.mul_add]

/-- Every scalar row of a branch word again has branch sum zero. -/
theorem scaleWord_isBranchWord {p : Nat} [NeZero p]
    (a : ZMod p) (word : BranchWord p) (hword : isBranchWord word) :
    isBranchWord (scaleWord a word) := by
  unfold isBranchWord
  rw [residueValueSum_scaleWord_mod]
  have hdiv : p ∣ residueValueSum word := Nat.dvd_of_mod_eq_zero hword
  obtain ⟨k, hk⟩ := hdiv
  apply Nat.mod_eq_zero_of_dvd
  refine ⟨a.val * k, ?_⟩
  rw [hk]
  ac_rfl

/-- Orienting a signed determinant term preserves its branch condition. -/
theorem signedWord_oriented_isBranchWord {p : Nat} [NeZero p]
    (term : SignedWord p) (hword : isBranchWord term.word) :
    isBranchWord term.oriented := by
  cases hreversed : term.reversed with
  | false => simpa [SignedWord.oriented, hreversed] using hword
  | true =>
      simpa [SignedWord.oriented, hreversed] using
        (negativeWord_isBranchWord term.word hword)

/-- The concrete branch predicate recursively discharges every divisibility
hypothesis needed by the integral determinant-signature bridge, at any row. -/
theorem allScaledBranchWordsAt_of_branchValidDeterminantTerms
    {p : Nat} [NeZero p] (a : ZMod p) (terms : List (SignedWord p))
    (hterms : BranchValidDeterminantTerms terms) :
    AllScaledBranchWordsAt a terms := by
  induction terms with
  | nil => trivial
  | cons term terms ih =>
      constructor
      · exact scaleWord_isBranchWord a term.oriented
          (signedWord_oriented_isBranchWord term hterms.1)
      · exact ih hterms.2

/-! ## The literal determinant residue tuple has no zero entries -/

theorem nonzeroResidues_allResiduesNonzero {p : Nat} [NeZero p]
    (word : BranchWord p) :
    AllResiduesNonzero (nonzeroResidues word) := by
  intro x hx
  induction word with
  | nil => simp [nonzeroResidues] at hx
  | cons y word ih =>
      by_cases hy : y = zzero p
      · simp [nonzeroResidues, hy] at hx
        exact ih hx
      · simp [nonzeroResidues, hy] at hx
        rcases hx with rfl | hx
        · exact hy
        · exact ih hx

theorem allResiduesNonzero_lappend {p : Nat} [NeZero p]
    (left right : BranchWord p)
    (hleft : AllResiduesNonzero left)
    (hright : AllResiduesNonzero right) :
    AllResiduesNonzero (lappend left right) := by
  have mem_lappend_iff (x : ZMod p) (xs ys : BranchWord p) :
      x ∈ lappend xs ys ↔ x ∈ xs ∨ x ∈ ys := by
    induction xs with
    | nil => simp [lappend]
    | cons y xs ih => simp [lappend, ih, or_assoc]
  intro x hx
  rcases (mem_lappend_iff x left right).1 hx with hxleft | hxright
  · exact hleft x hxleft
  · exact hright x hxright

theorem concatenatedResidues_allResiduesNonzero {p : Nat} [NeZero p]
    (words : List (BranchWord p)) :
    AllResiduesNonzero (concatenatedResidues words) := by
  induction words with
  | nil => simp [AllResiduesNonzero, concatenatedResidues]
  | cons word words ih =>
      simp only [concatenatedResidues]
      exact allResiduesNonzero_lappend
        (nonzeroResidues word) (concatenatedResidues words)
        (nonzeroResidues_allResiduesNonzero word) ih

/-- Filtering each effective word before concatenation makes nonzeroness of
the final Aoki tuple a theorem, not an input to the manuscript bridge. -/
theorem determinantResidues_allResiduesNonzero
    {p : Nat} [NeZero p] (terms : List (SignedWord p)) :
    AllResiduesNonzero (determinantResidues terms) := by
  unfold determinantResidues
  exact concatenatedResidues_allResiduesNonzero (effectiveWords terms)

/-! ## Zero integral signatures imply Aoki balance -/

/-- This is the manuscript-specific zero-signature-to-balance arrow.  All
division side conditions are discharged from the concrete branch words. -/
theorem determinantResidues_isAokiBalanced
    {p : Nat} [NeZero p] (terms : List (SignedWord p))
    (hbranch : BranchValidDeterminantTerms terms)
    (hzero : AllNonzeroRowIntegralSignaturesZero terms) :
    IsAokiBalanced p (determinantResidues terms) := by
  intro a ha
  have hscaled : AllScaledBranchWordsAt a terms :=
    allScaledBranchWordsAt_of_branchValidDeterminantTerms a terms hbranch
  exact
    (integralDeterminantSignatureAt_eq_zero_iff_galoisBalanced_of_branch
      a terms hscaled).1 (hzero a ha)

/-! ## Exact source-side restrictions and the two short tuples -/

/-- The residue row represented by one is nonzero as soon as `p ≥ 2`. -/
theorem rowOne_ne_zero_of_two_le {p : Nat} [NeZero p]
    (hp : 2 ≤ p) : zOfNat p 1 ≠ zzero p := by
  intro equality
  have values := congrArg Fin.val equality
  simp [zOfNat, Nat.mod_eq_of_lt (by omega : 1 < p)] at values

/-- Multiplication by the canonical row one fixes every residue. -/
theorem zmul_rowOne {p : Nat} [NeZero p]
    (hp : 2 ≤ p) (x : ZMod p) :
    zmul (zOfNat p 1) x = x := by
  apply Fin.ext
  simp [zmul, zOfNat, Nat.mod_eq_of_lt (by omega : 1 < p),
    Nat.mod_eq_of_lt x.isLt]

/-- Scaling a whole word by the canonical row one is the identity. -/
theorem scaleWord_rowOne {p : Nat} [NeZero p]
    (hp : 2 ≤ p) (word : BranchWord p) :
    scaleWord (zOfNat p 1) word = word := by
  induction word with
  | nil => rfl
  | cons x word ih =>
      simp only [scaleWord]
      rw [zmul_rowOne hp x, ih]

/-- All-nonzero-row balance plus even length forces the branch-sum condition.
This supplies Aoki's `B_m^n` branch hypothesis from project-side arithmetic. -/
theorem isBranchWord_of_aokiBalanced_even
    {p : Nat} [NeZero p] (hp : 2 ≤ p)
    {residues : BranchWord p}
    (balanced : IsAokiBalanced p residues)
    (evenLength : llength residues % 2 = 0) :
    isBranchWord residues := by
  have equation := balanced (zOfNat p 1) (rowOne_ne_zero_of_two_le hp)
  unfold galoisResidueSum at equation
  rw [scaleWord_rowOne hp residues] at equation
  have lengthDivisible : 2 ∣ llength residues :=
    Nat.dvd_of_mod_eq_zero evenLength
  obtain ⟨halfLength, lengthEq⟩ := lengthDivisible
  rw [lengthEq] at equation
  have doubled :
      2 * residueValueSum residues = 2 * (p * halfLength) := by
    calc
      2 * residueValueSum residues = p * (2 * halfLength) := equation
      _ = 2 * (p * halfLength) := by ac_rfl
  have sumEq : residueValueSum residues = p * halfLength :=
    Nat.eq_of_mul_eq_mul_left (by omega) doubled
  unfold isBranchWord
  rw [sumEq]
  simp

/-- For a prime modulus, a unit row is nonzero. -/
theorem invertibleRow_ne_zero_of_prime
    {p : Nat} [NeZero p] (hp : IsPrimeModulus p)
    (a : ZMod p) (ha : IsInvertibleRow a) :
    a ≠ zzero p := by
  have hpTwo : 2 ≤ p := hp.1
  intro hazero
  subst a
  have hpOne : p = 1 := by
    simpa [IsInvertibleRow, Nat.Coprime] using ha
  omega

/-- The project's stronger balance on every nonzero row restricts to Aoki's
source-facing balance on unit rows. -/
theorem aokiUnitBalanced_of_aokiBalanced_prime
    {p : Nat} [NeZero p] (hp : IsPrimeModulus p)
    {residues : BranchWord p}
    (balanced : IsAokiBalanced p residues) :
    External.IsAokiUnitBalanced residues := by
  intro a ha
  exact balanced a (invertibleRow_ne_zero_of_prime hp a ha)

/-- A balanced nonzero tuple of literal length two is already one opposite
pair.  This is the short case outside Aoki's `n + 2`, positive-even setup. -/
def oppositePairingWitness_of_two_aokiBalanced
    {p : Nat} [NeZero p] (hp : 2 ≤ p)
    (x y : ZMod p)
    (hx : x ≠ zzero p) (_hy : y ≠ zzero p)
    (balanced : IsAokiBalanced p [x, y]) :
    OppositePairingWitness [x, y] := by
  have equation := balanced (zOfNat p 1) (rowOne_ne_zero_of_two_le hp)
  unfold galoisResidueSum at equation
  simp only [scaleWord, residueValueSum, llength] at equation
  rw [zmul_rowOne hp x, zmul_rowOne hp y] at equation
  have valueSum : x.val + y.val = p := by omega
  have hyOpposite : y = zneg x := by
    apply Fin.ext
    rw [zneg_val_of_ne_zero x hx]
    omega
  refine
    { representatives := [x]
      representatives_nonzero := ?_
      perm := ?_ }
  · intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with hzx | hz
    · cases hzx
      exact hx
    · simp at hz
  · simp [pairResidues, hyOpposite]

/-- Every balanced nonzero even tuple shorter than four has an explicit
pairing: its length is forced to be zero or two. -/
def oppositePairingWitness_of_short_aokiBalanced
    {p : Nat} [NeZero p] (hp : 2 ≤ p)
    (residues : BranchWord p)
    (hnonzero : AllResiduesNonzero residues)
    (heven : llength residues % 2 = 0)
    (hshort : ¬ 4 ≤ llength residues)
    (hbalanced : IsAokiBalanced p residues) :
    OppositePairingWitness residues := by
  cases residues with
  | nil =>
      exact
        { representatives := []
          representatives_nonzero := by simp
          perm := by simp [pairResidues] }
  | cons x residues =>
      cases residues with
      | nil => simp [llength] at heven
      | cons y residues =>
          cases residues with
          | nil =>
              exact oppositePairingWitness_of_two_aokiBalanced hp x y
                (hnonzero x (by simp)) (hnonzero y (by simp)) hbalanced
          | cons z residues =>
              cases residues with
              | nil => simp [llength] at heven
              | cons w residues =>
                  exact (hshort (by simp [llength])).elim

/-! ## Exact Aoki leaf and the resulting opposite pairing -/

/-- For an odd prime, a branch-valid all-row zero determinant relation has an
explicit opposite pairing.  The published direction is isolated in
`aokiInput`; nonzeroness, balance, and even length are all proved above. -/
noncomputable def determinantResidues_oppositePairing_of_aokiPrime
    {p : Nat} [NeZero p]
    (hp : External.IsPrime p) (hpNotTwo : p ≠ 2)
    (aokiInput : External.AokiPrimeBalanceInput)
    (terms : List (SignedWord p))
    (hbranch : BranchValidDeterminantTerms terms)
    (hzero : AllNonzeroRowIntegralSignaturesZero terms) :
    OppositePairingWitness (determinantResidues terms) := by
  have hbalanced : IsAokiBalanced p (determinantResidues terms) :=
    determinantResidues_isAokiBalanced terms hbranch hzero
  have heven : llength (determinantResidues terms) % 2 = 0 :=
    aokiBalanced_length_even_of_prime_ne_two
      hp hpNotTwo hbalanced
  have hbranchResidues : isBranchWord (determinantResidues terms) :=
    isBranchWord_of_aokiBalanced_even hp.1 hbalanced heven
  have hunitBalanced :
      External.IsAokiUnitBalanced (determinantResidues terms) :=
    aokiUnitBalanced_of_aokiBalanced_prime hp hbalanced
  have hnonzero : AllResiduesNonzero (determinantResidues terms) :=
    determinantResidues_allResiduesNonzero terms
  by_cases hfour : 4 ≤ llength (determinantResidues terms)
  · exact Classical.choice
      (aokiInput.balancedHasOppositePairing
        p hp (determinantResidues terms) hbranchResidues
        hnonzero heven hfour hunitBalanced)
  · exact oppositePairingWitness_of_short_aokiBalanced
      hp.1 (determinantResidues terms) hnonzero heven hfour hbalanced

end

end

end AbelianCoverHodge.Bridge
