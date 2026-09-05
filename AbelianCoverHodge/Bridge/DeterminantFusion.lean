module

public import AbelianCoverHodge.Bridge.DeterminantAoki
public import AbelianCoverHodge.Verified.FusionBounds

/-!
# From signed determinant terms to labelled finite fusion data

Every effective copy receives a distinct natural-number source label. Zero
entries are removed before constructing the source family, while all repeated
words and their multiplicities are retained. The concrete Aoki bridge then
produces an occurrence pairing on exactly this family.

Given a forest certificate for the pairing, the source rank is preserved and
every fused component has at least four surviving markings. This file does
not construct a spanning forest or identify the data with geometric covers.
-/

namespace AbelianCoverHodge.Bridge

public section

@[expose] section

open AbelianCoverHodge.Verified

variable {p : Nat} [NeZero p]

private theorem lappend_eq_append {α : Type} (xs ys : List α) :
    lappend xs ys = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lappend, ih]

private theorem llength_eq_length {α : Type} (xs : List α) :
    llength xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [llength, ih]

private theorem lreplicate_eq_replicate {α : Type} (n : Nat) (x : α) :
    lreplicate n x = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lreplicate, List.replicate_succ, ih]

/-- Distinct source labels for the effective copies, retaining their order and
every nonzero marking. The offset supports the recursive construction. -/
def labelledEffectiveWordsFrom (start : Nat) :
    List (BranchWord p) → List (LabelledBranchWord p Nat)
  | [] => []
  | word :: words =>
      ⟨start, nonzeroResidues word⟩ ::
        labelledEffectiveWordsFrom (start + 1) words

theorem labelledEffectiveWordsFrom_vertices (start : Nat)
    (words : List (BranchWord p)) :
    (labelledEffectiveWordsFrom start words).map LabelledBranchWord.vertex =
      List.range' start words.length := by
  induction words generalizing start with
  | nil => rfl
  | cons word words ih =>
    simp [labelledEffectiveWordsFrom, List.range'_succ, ih]

theorem labelledEffectiveWordsFrom_residues (start : Nat)
    (words : List (BranchWord p)) :
    LabelledBranchWord.concatenatedResidues
      (labelledEffectiveWordsFrom start words) =
      Verified.concatenatedResidues words := by
  induction words generalizing start with
  | nil => rfl
  | cons word words ih =>
    change nonzeroResidues word ++
      LabelledBranchWord.concatenatedResidues
        (labelledEffectiveWordsFrom (start + 1) words) =
      lappend (nonzeroResidues word) (Verified.concatenatedResidues words)
    rw [lappend_eq_append, ih]

theorem labelledEffectiveWordsFrom_length_bound (start : Nat)
    (words : List (BranchWord p)) (minimum : Nat)
    (hsupport : ∀ word ∈ words, minimum ≤ supportSize word) :
    ∀ word ∈ labelledEffectiveWordsFrom start words,
      minimum ≤ word.residues.length := by
  induction words generalizing start with
  | nil => simp [labelledEffectiveWordsFrom]
  | cons source sources ih =>
    intro word hword
    simp only [labelledEffectiveWordsFrom, List.mem_cons] at hword
    rcases hword with rfl | hword
    · have hhead := hsupport source (by simp)
      have hlength := nonzeroResidues_length source
      rw [llength_eq_length] at hlength
      simpa only [hlength] using hhead
    · exact ih (start + 1) (fun source hsource =>
        hsupport source (by simp [hsource])) word hword

theorem effectiveWords_support_bound
    (terms : List (SignedWord p)) (minimum : Nat)
    (hsupport : ∀ term ∈ terms, minimum ≤ supportSize term.word) :
    ∀ word ∈ effectiveWords terms, minimum ≤ supportSize word := by
  induction terms with
  | nil => simp [effectiveWords]
  | cons term terms ih =>
    intro word hword
    simp only [effectiveWords, lappend_eq_append, List.mem_append] at hword
    rcases hword with hcopy | htail
    · rw [lreplicate_eq_replicate] at hcopy
      have heq : word = term.oriented := (List.mem_replicate.mp hcopy).2
      subst word
      have hhead := hsupport term (by simp)
      cases hrev : term.reversed <;>
        simpa [SignedWord.oriented, hrev, supportSize_negativeWord] using hhead
    · exact ih (fun other hother => hsupport other (by simp [hother])) word htail

/-- A source family canonically built from the actual signed determinant
terms. Repeated terms and repeated copies have distinct position labels. -/
def determinantSourceFamily
    (terms : List (SignedWord p))
    (hthree : ∀ term ∈ terms, 3 ≤ supportSize term.word) :
    SourceBranchFamily p Nat where
  words := labelledEffectiveWordsFrom 0 (effectiveWords terms)
  vertices_nodup := by
    rw [labelledEffectiveWordsFrom_vertices]
    exact List.nodup_range'
  two_le_length := by
    have hbound := labelledEffectiveWordsFrom_length_bound 0
      (effectiveWords terms) 3 (effectiveWords_support_bound terms 3 hthree)
    intro word hword
    have h := hbound word hword
    omega

theorem determinantSourceFamily_three_le_length
    (terms : List (SignedWord p))
    (hthree : ∀ term ∈ terms, 3 ≤ supportSize term.word) :
    ∀ word ∈ (determinantSourceFamily terms hthree).words,
      3 ≤ word.residues.length := by
  exact labelledEffectiveWordsFrom_length_bound 0
    (effectiveWords terms) 3 (effectiveWords_support_bound terms 3 hthree)

theorem determinantSourceFamily_residues
    (terms : List (SignedWord p))
    (hthree : ∀ term ∈ terms, 3 ≤ supportSize term.word) :
    BranchOccurrence.residueWord
      (determinantSourceFamily terms hthree).occurrences = determinantResidues terms := by
  rw [SourceBranchFamily.occurrences,
    LabelledBranchWord.residueWord_allOccurrences]
  exact labelledEffectiveWordsFrom_residues 0 (effectiveWords terms)

/-- The prime balanced-to-paired source input produces concrete labelled
occurrence data on the canonical determinant source family. -/
noncomputable def determinantSourcePairing
    (hp : External.IsPrime p) (hpNotTwo : p ≠ 2)
    (aokiInput : External.AokiPrimeBalanceInput)
    (terms : List (SignedWord p))
    (hbranch : BranchValidDeterminantTerms terms)
    (hzero : AllNonzeroRowIntegralSignaturesZero terms)
    (hthree : ∀ term ∈ terms, 3 ≤ supportSize term.word) :
    OccurrencePairingWitness (determinantSourceFamily terms hthree).occurrences :=
  Classical.choose
    ((determinantResidues_oppositePairing_of_aokiPrime hp hpNotTwo aokiInput
      terms hbranch hzero).exists_occurrencePairing
        (determinantSourceFamily terms hthree).occurrences
        (determinantSourceFamily_residues terms hthree))

/-- The concrete determinant pairing and any forest certificate give exact
rank preservation and nondegenerate even fused rank, with no extra local
lower-bound assumptions on the forest. Forest existence remains separate. -/
theorem determinant_fusion_rank_and_bounds
    (hp : External.IsPrime p) (hpNotTwo : p ≠ 2)
    (aokiInput : External.AokiPrimeBalanceInput)
    (terms : List (SignedWord p))
    (hbranch : BranchValidDeterminantTerms terms)
    (hzero : AllNonzeroRowIntegralSignaturesZero terms)
    (hthree : ∀ term ∈ terms, 3 ≤ supportSize term.word)
    (forest : FusionForestWitness
      (determinantSourcePairing hp hpNotTwo aokiInput terms hbranch hzero hthree)) :
    (determinantSourceFamily terms hthree).rankSum = forest.fusedComponentRankSum ∧
      ∀ component ∈ forest.components,
        4 ≤ component.remainingBranchCount ∧
        0 < component.remainingBranchCount - 2 ∧
        (component.remainingBranchCount - 2) % 2 = 0 := by
  let family := determinantSourceFamily terms hthree
  let pairing := determinantSourcePairing hp hpNotTwo aokiInput
    terms hbranch hzero hthree
  constructor
  · exact forest.sourceRankSum_eq_fusedComponentRankSum_of_source_family family pairing
  · intro component hcomponent
    exact ⟨forest.four_le_component_remainingBranchCount family pairing
        (determinantSourceFamily_three_le_length terms hthree) component hcomponent,
      forest.component_fused_rank_positive_even family pairing
        (determinantSourceFamily_three_le_length terms hthree) component hcomponent⟩

end

end

end AbelianCoverHodge.Bridge
