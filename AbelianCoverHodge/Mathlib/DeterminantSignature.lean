module

public import AbelianCoverHodge.Mathlib.DeterminantLattice
public import AbelianCoverHodge.Mathlib.Signature

/-!
# Determinant relations and all-row signatures

This module connects the corrected saturated determinant lattice to the
mathlib-native integral signature.  Signature rows are units of `ZMod p`, so
every row corresponds to a genuine cyclotomic/Galois embedding.
-/

namespace AbelianCoverHodge.Mathlib

public section

@[expose] section

open Signature

/-- The rows relevant to cyclotomic signatures. -/
abbrev GaloisRows (p : Nat) := (_root_.ZMod p)ˣ

variable {p : Nat} [NeZero p]
variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

/-- Every unit row at once, bundled as an integral linear map from determinant
exponents to their signature column. -/
def allRowsDeterminantSignatureMap
    (words : ι → BranchWord p ρ) :
    RawDeterminantLattice ι →ₗ[ℤ] SignatureLattice (GaloisRows p) where
  toFun exponent row :=
    determinantSignatureMap (row : _root_.ZMod p) words exponent
  map_add' left right := by
    funext row
    exact determinantSignatureMap_add (row : _root_.ZMod p)
      words left right
  map_smul' scalar exponent := by
    funext row
    exact determinantSignatureMap_zsmul (row : _root_.ZMod p)
      words scalar exponent

omit [NeZero p] in
@[simp]
theorem allRowsDeterminantSignatureMap_apply
    (words : ι → BranchWord p ρ)
    (exponent : RawDeterminantLattice ι) (row : GaloisRows p) :
    allRowsDeterminantSignatureMap words exponent row =
      ∑ i, exponent i * delta (row : _root_.ZMod p) (words i) :=
  rfl

omit [NeZero p] in
@[simp]
theorem allRowsDeterminantSignatureMap_basis
    (words : ι → BranchWord p ρ) (index : ι) (row : GaloisRows p) :
    allRowsDeterminantSignatureMap words
        (rawDeterminantBasis ι index) row =
      delta (row : _root_.ZMod p) (words index) := by
  classical
  rw [allRowsDeterminantSignatureMap_apply]
  change ∑ i, Pi.single (M := fun _ : ι ↦ ℤ) index (1 : ℤ) i *
      delta (row : _root_.ZMod p) (words i) = _
  rw [Fintype.sum_eq_single index]
  · simp
  · intro other hne
    simp [hne]

namespace KummerRelation

/-- Arithmetic compatibility between one displayed Kummer relation and a
family of branch words, allowing the branch occurrences to be permuted.
Standard-to-standard relations identify reindexed words; standard-to-dual
relations identify a reindexed word with the negative and also record the
branch-sum condition needed by signature negation.  This includes self-dual
relations whose raw lattice vector is `2 ε_c`. -/
def CompatibleWithWords (words : ι → BranchWord p ρ)
    (relation : KummerRelation ι) : Prop :=
  match relation.kind with
  | .standardToStandard =>
      ∃ permutation : ρ ≃ ρ,
        words relation.right = reindex permutation (words relation.left)
  | .standardToDual =>
      ∃ permutation : ρ ≃ ρ,
        words relation.right =
          -(reindex permutation (words relation.left)) ∧
          IsBranchWord (words relation.left)

/-- A compatible raw Kummer generator has zero signature at every unit row. -/
theorem allRowsSignature_vector_eq_zero
    (words : ι → BranchWord p ρ) (relation : KummerRelation ι)
    (compatible : relation.CompatibleWithWords words) :
    allRowsDeterminantSignatureMap words relation.vector = 0 := by
  classical
  funext row
  cases relation with
  | mk left right kind =>
      cases kind with
      | standardToStandard =>
          simp only [CompatibleWithWords] at compatible
          obtain ⟨permutation, wordRight⟩ := compatible
          have signatureRight (row : GaloisRows p) :
              delta (row : _root_.ZMod p) (words right) =
                delta (row : _root_.ZMod p) (words left) := by
            rw [wordRight, delta_reindex]
          simp only [KummerRelation.vector, map_sub, Pi.sub_apply,
            allRowsDeterminantSignatureMap_basis]
          rw [signatureRight, sub_self]
          simp
      | standardToDual =>
          rcases compatible with ⟨permutation, wordRight, branchWord⟩
          have reindexedBranchWord :
              IsBranchWord (reindex permutation (words left)) :=
            isBranchWord_reindex permutation branchWord
          have negation := delta_neg_word (row : _root_.ZMod p)
            row.isUnit (reindex permutation (words left))
              reindexedBranchWord
          have signatureRight :
              delta (row : _root_.ZMod p) (words right) =
                -delta (row : _root_.ZMod p) (words left) := by
            rw [wordRight, negation, delta_reindex]
          simp only [KummerRelation.vector, map_add, Pi.add_apply,
            allRowsDeterminantSignatureMap_basis]
          rw [signatureRight, add_neg_cancel]
          simp

end KummerRelation

/-- If every displayed Kummer generator has the stated word compatibility,
then the entire saturated relation lattice lies in the all-row signature
kernel. -/
theorem kummerSaturatedSubmodule_le_allRowsSignatureKernel
    (words : ι → BranchWord p ρ)
    (relations : Set (KummerRelation ι))
    (compatible : ∀ relation ∈ relations,
      relation.CompatibleWithWords words) :
    kummerSaturatedSubmodule relations ≤
      LinearMap.ker (allRowsDeterminantSignatureMap words) := by
  apply kummerSaturatedSubmodule_le_signatureKernel
  intro relation inRelations
  exact relation.allRowsSignature_vector_eq_zero words
    (compatible relation inRelations)

/-- The concrete all-row signature descends to the corrected determinant
lattice whenever every displayed relation has compatible branch words. -/
noncomputable def allRowsSignatureOnSaturatedDeterminantLattice
    (words : ι → BranchWord p ρ)
    (relations : Set (KummerRelation ι))
    (compatible : ∀ relation ∈ relations,
      relation.CompatibleWithWords words) :
    SaturatedDeterminantLattice relations →ₗ[ℤ]
      SignatureLattice (GaloisRows p) :=
  signatureOnSaturatedDeterminantLattice relations
    (allRowsDeterminantSignatureMap words)
    (fun relation inRelations ↦
      relation.allRowsSignature_vector_eq_zero words
        (compatible relation inRelations))

end


end


end AbelianCoverHodge.Mathlib
