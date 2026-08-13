module

public import AbelianCoverHodge.Verified.Core

/-!
# Integral signature arithmetic

This module gives the signature calculations used by the determinant-word
argument their literal `Int` meaning.  In particular, it proves that vanishing
of the additive integral signature is exactly the division-free Galois balance
equation, provided the displayed branch sums are divisible by `p`.

There are no geometric inputs here: every hypothesis is an explicit property
of the finite residue words occurring in `Verified.Core`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace AbelianCoverHodge.Verified

public section

@[expose] section

/-! ## The integer represented by `Defect` -/

/-- The literal integer encoded by the sign/magnitude representation in
`Core`.  Both constructors at magnitude zero represent the integer zero. -/
def defectToInt : Defect → Int
  | .nonnegative n => Int.ofNat n
  | .negative n => -Int.ofNat n

@[simp] theorem defectToInt_nonnegative (n : Nat) :
    defectToInt (.nonnegative n) = Int.ofNat n := rfl

@[simp] theorem defectToInt_negative (n : Nat) :
    defectToInt (.negative n) = -Int.ofNat n := rfl

/-- `defectOf positive negative` really represents `positive - negative`. -/
theorem defectToInt_defectOf (positive negative : Nat) :
    defectToInt (defectOf positive negative) =
      Int.ofNat positive - Int.ofNat negative := by
  by_cases h : negative ≤ positive
  · simp [defectOf, h]
    omega
  · have hlt : positive < negative := Nat.lt_of_not_ge h
    simp [defectOf, h]
    omega

@[simp] theorem defectToInt_defectNeg (d : Defect) :
    defectToInt (defectNeg d) = -defectToInt d := by
  cases d with
  | nonnegative n =>
      cases n with
      | zero => rfl
      | succ n => rfl
  | negative n => simp [defectNeg, defectToInt]

/-- The executable zero test agrees with the literal integer semantics for
both sign constructors, including the noncanonical value `negative 0`. -/
theorem defectIsZero_eq_true_iff (d : Defect) :
    defectIsZero d = true ↔ defectToInt d = 0 := by
  cases d with
  | nonnegative n =>
      cases n <;> simp [defectIsZero, defectToInt] <;> omega
  | negative n =>
      cases n <;> simp [defectIsZero, defectToInt] <;> omega

/-! ## Integral signatures -/

/-- The integral cyclotomic signature
`support(w) - 2 * q_a(w)`. -/
def integralSignatureAt {p : Nat} [NeZero p] (a : ZMod p)
    (w : BranchWord p) : Int :=
  Int.ofNat (supportSize w) - 2 * Int.ofNat (qValue a w)

/-- Conversion of the pre-existing sign/magnitude signature loses no
information. -/
theorem defectToInt_signatureAt {p : Nat} [NeZero p]
    (a : ZMod p) (w : BranchWord p) :
    defectToInt (signatureAt a w) = integralSignatureAt a w := by
  unfold signatureAt integralSignatureAt
  rw [defectToInt_defectOf]
  simp

theorem integralSignatureAt_eq_zero_iff {p : Nat} [NeZero p]
    (a : ZMod p) (w : BranchWord p) :
    integralSignatureAt a w = 0 ↔
      supportSize w = 2 * qValue a w := by
  unfold integralSignatureAt
  constructor
  · intro h
    apply Int.ofNat_inj.mp
    have hi : Int.ofNat (supportSize w) =
        2 * Int.ofNat (qValue a w) := by omega
    simpa using hi
  · intro h
    rw [h]
    simp

/-- Integral form of `rowSignature`, for a word already expressed in one
Galois row. -/
def integralRowSignature {p : Nat} [NeZero p] (w : BranchWord p) : Int :=
  Int.ofNat (supportSize w) -
    2 * Int.ofNat (residueValueSum w / p)

theorem defectToInt_rowSignature {p : Nat} [NeZero p]
    (w : BranchWord p) :
    defectToInt (rowSignature w) = integralRowSignature w := by
  unfold rowSignature integralRowSignature
  rw [defectToInt_defectOf]
  simp

theorem integralSignatureAt_eq_row {p : Nat} [NeZero p]
    (a : ZMod p) (w : BranchWord p) :
    integralSignatureAt a w =
      Int.ofNat (supportSize w) -
        2 * Int.ofNat (residueValueSum (scaleWord a w) / p) := by
  rfl

/-! ## Transparent list identities used by the balance bridge -/

theorem llength_lappend {xs ys : List α} :
    llength (lappend xs ys) = llength xs + llength ys := by
  induction xs with
  | nil => simp [lappend, llength]
  | cons x xs ih =>
      simp [lappend, llength, ih, Nat.add_comm,
        Nat.add_left_comm]

theorem lappend_assoc (xs ys zs : List α) :
    lappend (lappend xs ys) zs = lappend xs (lappend ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lappend, ih]

theorem residueValueSum_lappend {p : Nat}
    (xs ys : BranchWord p) :
    residueValueSum (lappend xs ys) =
      residueValueSum xs + residueValueSum ys := by
  induction xs with
  | nil => simp [lappend, residueValueSum]
  | cons x xs ih => simp [lappend, residueValueSum, ih, Nat.add_assoc]

theorem scaleWord_lappend {p : Nat} [NeZero p] (a : ZMod p)
    (xs ys : BranchWord p) :
    scaleWord a (lappend xs ys) =
      lappend (scaleWord a xs) (scaleWord a ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lappend, scaleWord, ih]

@[simp] theorem zmul_zero_right {p : Nat} [NeZero p] (a : ZMod p) :
    zmul a (zzero p) = zzero p := by
  apply Fin.ext
  simp [zmul, zOfNat]

theorem nonzeroResidues_length {p : Nat} [NeZero p]
    (w : BranchWord p) :
    llength (nonzeroResidues w) = supportSize w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x = zzero p
      · simp [nonzeroResidues, supportSize, hx, ih]
      · simp [nonzeroResidues, supportSize, hx, ih, llength]
        omega

theorem scaleWord_nonzeroResidues_valueSum {p : Nat} [NeZero p]
    (a : ZMod p) (w : BranchWord p) :
    residueValueSum (scaleWord a (nonzeroResidues w)) =
      residueValueSum (scaleWord a w) := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x = zzero p
      · simp [nonzeroResidues, scaleWord, residueValueSum, hx, ih]
      · simp [nonzeroResidues, scaleWord, residueValueSum, hx, ih]

theorem galoisResidueSum_nonzeroResidues {p : Nat} [NeZero p]
    (a : ZMod p) (w : BranchWord p) :
    galoisResidueSum a (nonzeroResidues w) = qNumerator a w := by
  unfold galoisResidueSum qNumerator
  exact scaleWord_nonzeroResidues_valueSum a w

theorem galoisResidueSum_lappend {p : Nat} [NeZero p]
    (a : ZMod p) (xs ys : BranchWord p) :
    galoisResidueSum a (lappend xs ys) =
      galoisResidueSum a xs + galoisResidueSum a ys := by
  unfold galoisResidueSum
  rw [scaleWord_lappend, residueValueSum_lappend]

theorem concatenatedResidues_lappend {p : Nat} [NeZero p]
    (words more : List (BranchWord p)) :
    concatenatedResidues (lappend words more) =
      lappend (concatenatedResidues words) (concatenatedResidues more) := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      simp only [lappend, concatenatedResidues]
      rw [ih]
      exact (lappend_assoc (nonzeroResidues word)
        (concatenatedResidues words) (concatenatedResidues more)).symm

theorem concatenatedResidues_replicate_length {p : Nat} [NeZero p]
    (n : Nat) (w : BranchWord p) :
    llength (concatenatedResidues (lreplicate n w)) =
      n * supportSize w := by
  induction n with
  | zero => simp [lreplicate, concatenatedResidues, llength]
  | succ n ih =>
      simp only [lreplicate, concatenatedResidues]
      rw [llength_lappend, nonzeroResidues_length, ih]
      rw [Nat.succ_mul]
      omega

theorem concatenatedResidues_replicate_galoisSum {p : Nat} [NeZero p]
    (a : ZMod p) (n : Nat) (w : BranchWord p) :
    galoisResidueSum a (concatenatedResidues (lreplicate n w)) =
      n * qNumerator a w := by
  induction n with
  | zero => simp [lreplicate, concatenatedResidues, galoisResidueSum,
      scaleWord, residueValueSum]
  | succ n ih =>
      simp only [lreplicate, concatenatedResidues]
      rw [galoisResidueSum_lappend,
          galoisResidueSum_nonzeroResidues, ih]
      rw [Nat.succ_mul]
      omega

/-! ## Additive determinant signatures -/

/-- Total support, with signed-word multiplicities expanded arithmetically. -/
def determinantSupport {p : Nat} [NeZero p] :
    List (SignedWord p) → Nat
  | [] => 0
  | term :: terms =>
      term.copies * supportSize term.oriented + determinantSupport terms

/-- Sum of the divided branch sums `q_a`, with multiplicity. -/
def determinantQuotientAt {p : Nat} [NeZero p] (a : ZMod p) :
    List (SignedWord p) → Nat
  | [] => 0
  | term :: terms =>
      term.copies * qValue a term.oriented +
        determinantQuotientAt a terms

/-- Sum of the undivided branch sums, with multiplicity. -/
def determinantNumeratorAt {p : Nat} [NeZero p] (a : ZMod p) :
    List (SignedWord p) → Nat
  | [] => 0
  | term :: terms =>
      term.copies * qNumerator a term.oriented +
        determinantNumeratorAt a terms

/-- The genuinely additive integral signature of a determinant word. -/
def integralDeterminantSignatureAt {p : Nat} [NeZero p]
    (a : ZMod p) (terms : List (SignedWord p)) : Int :=
  Int.ofNat (determinantSupport terms) -
    2 * Int.ofNat (determinantQuotientAt a terms)

theorem determinantSupport_lappend {p : Nat} [NeZero p]
    (terms more : List (SignedWord p)) :
    determinantSupport (lappend terms more) =
      determinantSupport terms + determinantSupport more := by
  induction terms with
  | nil => simp [lappend, determinantSupport]
  | cons term terms ih =>
      simp [lappend, determinantSupport, ih, Nat.add_assoc]

theorem determinantQuotientAt_lappend {p : Nat} [NeZero p]
    (a : ZMod p) (terms more : List (SignedWord p)) :
    determinantQuotientAt a (lappend terms more) =
      determinantQuotientAt a terms + determinantQuotientAt a more := by
  induction terms with
  | nil => simp [lappend, determinantQuotientAt]
  | cons term terms ih =>
      simp [lappend, determinantQuotientAt, ih, Nat.add_assoc]

/-- Concatenation of determinant words is addition of their integral
signatures. -/
theorem integralDeterminantSignatureAt_lappend {p : Nat} [NeZero p]
    (a : ZMod p) (terms more : List (SignedWord p)) :
    integralDeterminantSignatureAt a (lappend terms more) =
      integralDeterminantSignatureAt a terms +
        integralDeterminantSignatureAt a more := by
  unfold integralDeterminantSignatureAt
  rw [determinantSupport_lappend, determinantQuotientAt_lappend]
  simp
  omega

/-- The positive component of the legacy `SignatureWeight` is exactly total
support. -/
theorem determinantSignatureAt_positive {p : Nat} [NeZero p]
    (a : ZMod p) (terms : List (SignedWord p)) :
    (determinantSignatureAt a terms).positive = determinantSupport terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      simp [determinantSignatureAt, determinantSupport, ih]

/-- The negative component of the legacy `SignatureWeight` is twice the sum
of the `q_a`. -/
theorem determinantSignatureAt_negative {p : Nat} [NeZero p]
    (a : ZMod p) (terms : List (SignedWord p)) :
    (determinantSignatureAt a terms).negative =
      2 * determinantQuotientAt a terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      simp only [determinantSignatureAt, determinantQuotientAt]
      rw [ih]
      rw [Nat.mul_add]
      congr 1
      ac_rfl

theorem integralDeterminantSignatureAt_eq_weightDifference
    {p : Nat} [NeZero p] (a : ZMod p)
    (terms : List (SignedWord p)) :
    integralDeterminantSignatureAt a terms =
      Int.ofNat (determinantSignatureAt a terms).positive -
        Int.ofNat (determinantSignatureAt a terms).negative := by
  rw [determinantSignatureAt_positive,
      determinantSignatureAt_negative]
  unfold integralDeterminantSignatureAt
  simp

/-! ## The exact division-free Galois-balance bridge -/

/-- The actual residue multiset of a determinant word, not a summary count. -/
def determinantResidues {p : Nat} [NeZero p]
    (terms : List (SignedWord p)) : BranchWord p :=
  concatenatedResidues (effectiveWords terms)

theorem determinantResidues_length {p : Nat} [NeZero p]
    (terms : List (SignedWord p)) :
    llength (determinantResidues terms) = determinantSupport terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      unfold determinantResidues at ih ⊢
      simp only [effectiveWords, determinantSupport]
      rw [concatenatedResidues_lappend, llength_lappend,
          concatenatedResidues_replicate_length, ih]

theorem determinantResidues_galoisSum {p : Nat} [NeZero p]
    (a : ZMod p) (terms : List (SignedWord p)) :
    galoisResidueSum a (determinantResidues terms) =
      determinantNumeratorAt a terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      unfold determinantResidues at ih ⊢
      simp only [effectiveWords, determinantNumeratorAt]
      rw [concatenatedResidues_lappend, galoisResidueSum_lappend,
          concatenatedResidues_replicate_galoisSum, ih]

/-- Every displayed numerator is divisible by `p`.  This is the precise
hypothesis needed to replace division by the cross-multiplied equation. -/
def AllQNumeratorsDivisibleAt {p : Nat} [NeZero p] (a : ZMod p) :
    List (SignedWord p) → Prop
  | [] => True
  | term :: terms =>
      p ∣ qNumerator a term.oriented ∧
        AllQNumeratorsDivisibleAt a terms

/-- A branch-sum formulation of the same audit hypothesis. -/
def AllScaledBranchWordsAt {p : Nat} [NeZero p] (a : ZMod p) :
    List (SignedWord p) → Prop
  | [] => True
  | term :: terms =>
      isBranchWord (scaleWord a term.oriented) ∧
        AllScaledBranchWordsAt a terms

theorem allQNumeratorsDivisible_of_scaledBranchWords
    {p : Nat} [NeZero p] (a : ZMod p)
    (terms : List (SignedWord p))
    (hbranch : AllScaledBranchWordsAt a terms) :
    AllQNumeratorsDivisibleAt a terms := by
  induction terms with
  | nil => trivial
  | cons term terms ih =>
      have hhead := hbranch.1
      have htail := hbranch.2
      constructor
      · apply Nat.dvd_of_mod_eq_zero
        exact hhead
      · exact ih htail

/-- Under the explicit divisibility hypothesis, summing after division is
exactly division of the summed numerators. -/
theorem determinantNumerator_eq_p_mul_quotient
    {p : Nat} [NeZero p] (a : ZMod p)
    (terms : List (SignedWord p))
    (hdiv : AllQNumeratorsDivisibleAt a terms) :
    determinantNumeratorAt a terms =
      p * determinantQuotientAt a terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      have hhead := hdiv.1
      have htail := hdiv.2
      obtain ⟨k, hk⟩ := hhead
      simp only [determinantNumeratorAt, determinantQuotientAt]
      rw [ih htail]
      unfold qValue
      rw [hk]
      have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
      rw [Nat.mul_div_cancel_left k hp, Nat.mul_add]
      ac_rfl

/-- The division-free balance equation at one Galois row, written on the
literal concatenated residue multiset. -/
def determinantGaloisBalancedAt {p : Nat} [NeZero p]
    (a : ZMod p) (terms : List (SignedWord p)) : Prop :=
  2 * galoisResidueSum a (determinantResidues terms) =
    p * llength (determinantResidues terms)

/-- Vanishing of the additive integral signature is *equivalent* to the
division-free Galois balance equation.  No implication is postulated: the only
input is the explicit divisibility of each branch numerator. -/
theorem integralDeterminantSignatureAt_eq_zero_iff_galoisBalanced
    {p : Nat} [NeZero p] (a : ZMod p)
    (terms : List (SignedWord p))
    (hdiv : AllQNumeratorsDivisibleAt a terms) :
    integralDeterminantSignatureAt a terms = 0 ↔
      determinantGaloisBalancedAt a terms := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hnum := determinantNumerator_eq_p_mul_quotient a terms hdiv
  rw [determinantGaloisBalancedAt, determinantResidues_galoisSum,
      determinantResidues_length, hnum]
  constructor
  · intro hzero
    have hsupport : determinantSupport terms =
        2 * determinantQuotientAt a terms := by
      apply Int.ofNat_inj.mp
      have hi : Int.ofNat (determinantSupport terms) =
          2 * Int.ofNat (determinantQuotientAt a terms) := by
        unfold integralDeterminantSignatureAt at hzero
        omega
      simpa using hi
    rw [hsupport]
    ac_rfl
  · intro hbalance
    have hcancel : p * (2 * determinantQuotientAt a terms) =
        p * determinantSupport terms := by
      calc
        p * (2 * determinantQuotientAt a terms) =
            2 * (p * determinantQuotientAt a terms) := by ac_rfl
        _ = p * determinantSupport terms := hbalance
    have hsupport : 2 * determinantQuotientAt a terms =
        determinantSupport terms :=
      Nat.eq_of_mul_eq_mul_left hp hcancel
    unfold integralDeterminantSignatureAt
    rw [← hsupport]
    simp

theorem integralDeterminantSignatureAt_eq_zero_iff_galoisBalanced_of_branch
    {p : Nat} [NeZero p] (a : ZMod p)
    (terms : List (SignedWord p))
    (hbranch : AllScaledBranchWordsAt a terms) :
    integralDeterminantSignatureAt a terms = 0 ↔
      determinantGaloisBalancedAt a terms :=
  integralDeterminantSignatureAt_eq_zero_iff_galoisBalanced
    a terms (allQNumeratorsDivisible_of_scaledBranchWords a terms hbranch)

/-! ## Negation at a residue row -/

theorem supportSize_negativeWord {p : Nat} [NeZero p]
    (w : BranchWord p) :
    supportSize (negativeWord w) = supportSize w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x = zzero p
      · simp [negativeWord, supportSize, hx, ih]
      · have hnx := zneg_ne_zero x hx
        simp [negativeWord, supportSize, hx, hnx, ih]

/-- Negating all nonzero canonical residues complements their sum to one copy
of `p` per support position. -/
theorem negativeWord_valueSum_complement {p : Nat} [NeZero p]
    (w : BranchWord p) :
    residueValueSum (negativeWord w) + residueValueSum w =
      p * supportSize w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x = zzero p
      · simp [negativeWord, residueValueSum, supportSize, hx, ih]
      · have _hnx := zneg_ne_zero x hx
        simp only [negativeWord, residueValueSum, supportSize, hx,
          if_false]
        rw [zneg_val_of_ne_zero x hx, Nat.mul_add]
        omega

theorem negativeWord_isBranchWord {p : Nat} [NeZero p]
    (w : BranchWord p) (hw : isBranchWord w) :
    isBranchWord (negativeWord w) := by
  have hwdiv : p ∣ residueValueSum w :=
    Nat.dvd_of_mod_eq_zero hw
  have htotal : p ∣
      residueValueSum (negativeWord w) + residueValueSum w := by
    rw [negativeWord_valueSum_complement]
    exact Nat.dvd_mul_right p (supportSize w)
  have hnegdiv : p ∣ residueValueSum (negativeWord w) :=
    (Nat.dvd_add_iff_left hwdiv).2 htotal
  exact Nat.mod_eq_zero_of_dvd hnegdiv

private theorem quotient_add_of_dvd_of_sum_eq_mul
    (p x y s : Nat) (hp : 0 < p)
    (hx : p ∣ x) (hy : p ∣ y)
    (hsum : x + y = p * s) :
    x / p + y / p = s := by
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  rw [hkx, hky] at hsum ⊢
  rw [Nat.mul_div_cancel_left kx hp,
      Nat.mul_div_cancel_left ky hp]
  apply Nat.eq_of_mul_eq_mul_left hp
  calc
    p * (kx + ky) = p * kx + p * ky := Nat.mul_add p kx ky
    _ = p * s := hsum

/-- At any branch row, word negation negates the integral signature. -/
theorem integralRowSignature_negativeWord {p : Nat} [NeZero p]
    (w : BranchWord p) (hw : isBranchWord w) :
    integralRowSignature (negativeWord w) = -integralRowSignature w := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hneg := negativeWord_isBranchWord w hw
  have hwdiv : p ∣ residueValueSum w :=
    Nat.dvd_of_mod_eq_zero hw
  have hnegdiv : p ∣ residueValueSum (negativeWord w) :=
    Nat.dvd_of_mod_eq_zero hneg
  have hquotient :
      residueValueSum (negativeWord w) / p +
          residueValueSum w / p = supportSize w :=
    quotient_add_of_dvd_of_sum_eq_mul p
      (residueValueSum (negativeWord w)) (residueValueSum w)
      (supportSize w) hp hnegdiv hwdiv
      (negativeWord_valueSum_complement w)
  unfold integralRowSignature
  rw [supportSize_negativeWord]
  have hquotientInt :
      Int.ofNat (residueValueSum (negativeWord w) / p) +
          Int.ofNat (residueValueSum w / p) =
        Int.ofNat (supportSize w) := by
    have hcast := congrArg Int.ofNat hquotient
    exact hcast
  omega

/-! ## Opposite-pair consequences -/

theorem pairResidues_support {p : Nat} [NeZero p]
    (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p) :
    supportSize (pairResidues representatives) =
      2 * llength representatives := by
  induction representatives with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ≠ zzero p := hnonzero x (by simp)
      have hnx := zneg_ne_zero x hx
      have hxs : ∀ y ∈ xs, y ≠ zzero p := by
        intro y hy
        exact hnonzero y (by simp [hy])
      simp only [pairResidues, supportSize, hx, hnx, if_false,
        llength]
      rw [ih hxs]
      omega

theorem pairResidues_isBranchWord {p : Nat} [NeZero p]
    (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p) :
    isBranchWord (pairResidues representatives) := by
  unfold isBranchWord
  rw [pairResidues_valueSum representatives hnonzero]
  simp

/-- Every literal list of nonzero opposite pairs has zero integral row
signature, for arbitrary nonzero `p`. -/
theorem integralRowSignature_pairResidues_zero {p : Nat} [NeZero p]
    (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p) :
    integralRowSignature (pairResidues representatives) = 0 := by
  unfold integralRowSignature
  rw [pairResidues_support representatives hnonzero,
      pairResidues_valueSum representatives hnonzero]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [Nat.mul_div_cancel_left (llength representatives) hp]
  simp

/-- A scaled codeword whose scaled row is explicitly an opposite-pair list
has zero integral signature, provided scaling has not changed its support. -/
theorem integralSignatureAt_zero_of_scaled_oppositePairs
    {p : Nat} [NeZero p] (a : ZMod p) (w : BranchWord p)
    (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p)
    (hscaled : scaleWord a w = pairResidues representatives)
    (hsupport : supportSize w = supportSize (scaleWord a w)) :
    integralSignatureAt a w = 0 := by
  unfold integralSignatureAt qValue qNumerator
  rw [hsupport, hscaled,
      pairResidues_support representatives hnonzero,
      pairResidues_valueSum representatives hnonzero]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [Nat.mul_div_cancel_left (llength representatives) hp]
  simp

end

end

end AbelianCoverHodge.Verified
