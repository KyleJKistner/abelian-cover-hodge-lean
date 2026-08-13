module

public import Std

/-!
# Finite/combinatorial core of the elementary-prime Phase II certificate

This module stays strictly below the algebro-geometric layer.  It gives
kernel-checkable definitions for branch-code spans, cyclotomic signatures,
effective determinant words, residue balance, opposite-pair witnesses, and
compact-type fusion ranks.  It contains no proof placeholders or new postulates.

At this dependency-free layer, `ZMod p` is Lean's canonical finite residue
type `Fin p`; modular operations are made explicit to keep reduction auditable.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace AbelianCoverHodge.Verified

public section

@[expose] section

abbrev ZMod (p : Nat) := Fin p
abbrev BranchWord (p : Nat) := List (ZMod p)

/-! ## Small transparent list kernel

The npm WASM verifier used during development ships only exported `.olean`
parts.  These transparent recursors avoid depending on private optimized list
helpers and also make certificate reduction easy to inspect.
-/

def lmap (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: lmap f xs

def lappend : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: lappend xs ys

def lflatMap (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => lappend (f x) (lflatMap f xs)

def llength : List α → Nat
  | [] => 0
  | _ :: xs => llength xs + 1

def lreplicate (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | n + 1 => x :: lreplicate n x

def lsumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + lsumNat xs

def lall (predicate : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => predicate x && lall predicate xs

def ltail : List α → List α
  | [] => []
  | _ :: xs => xs

/-! ## Explicit residues modulo `p` -/

def zzero (p : Nat) [NeZero p] : ZMod p :=
  ⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩

def zOfNat (p n : Nat) [NeZero p] : ZMod p :=
  ⟨n % p, Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne p))⟩

def zneg {p : Nat} [NeZero p] (x : ZMod p) : ZMod p :=
  if h : x.val = 0 then zzero p
  else ⟨p - x.val, by omega⟩

def zadd {p : Nat} [NeZero p] (x y : ZMod p) : ZMod p :=
  zOfNat p (x.val + y.val)

def zmul {p : Nat} [NeZero p] (x y : ZMod p) : ZMod p :=
  zOfNat p (x.val * y.val)

@[simp] theorem zzero_val (p : Nat) [NeZero p] : (zzero p).val = 0 := rfl

@[simp] theorem zneg_zero (p : Nat) [NeZero p] : zneg (zzero p) = zzero p := by
  apply Fin.ext
  simp [zneg]

theorem zneg_val_of_ne_zero {p : Nat} [NeZero p] (x : ZMod p)
    (hx : x ≠ zzero p) : (zneg x).val = p - x.val := by
  have hxv : x.val ≠ 0 := by
    intro h
    apply hx
    apply Fin.ext
    simpa using h
  simp [zneg, hxv]

@[simp] theorem zneg_involutive {p : Nat} [NeZero p] (x : ZMod p) :
    zneg (zneg x) = x := by
  apply Fin.ext
  by_cases hxv : x.val = 0
  · simp [zneg, hxv]
  · have hxpos : 0 < x.val := Nat.pos_of_ne_zero hxv
    have hcomp : p - x.val ≠ 0 := by omega
    simp [zneg, hxv, hcomp]
    omega

theorem zneg_ne_zero {p : Nat} [NeZero p] (x : ZMod p)
    (hx : x ≠ zzero p) : zneg x ≠ zzero p := by
  intro h
  have hn := congrArg zneg h
  rw [zneg_involutive, zneg_zero] at hn
  exact hx hn

def allResiduesAux (p start : Nat) [NeZero p] : Nat → List (ZMod p)
  | 0 => []
  | n + 1 => zOfNat p start :: allResiduesAux p (start + 1) n

/-- Every canonical residue `0, ..., p-1`. -/
def allResidues (p : Nat) [NeZero p] : List (ZMod p) :=
  allResiduesAux p 0 p

/-- The cyclotomic rows `1, ..., p-1`. -/
def cyclotomicRows (p : Nat) [NeZero p] : List (ZMod p) :=
  ltail (allResidues p)

/-! ## Branch-code computations -/

def addWords {p : Nat} [NeZero p] : BranchWord p → BranchWord p → BranchWord p
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => zadd x y :: addWords xs ys

def scaleWord {p : Nat} [NeZero p] (a : ZMod p) : BranchWord p → BranchWord p
  | [] => []
  | x :: xs => zmul a x :: scaleWord a xs

def negativeWord {p : Nat} [NeZero p] : BranchWord p → BranchWord p
  | [] => []
  | x :: xs => zneg x :: negativeWord xs

def coefficientVectors (p : Nat) [NeZero p] : Nat → List (List (ZMod p))
  | 0 => [[]]
  | n + 1 =>
      lflatMap (fun a => lmap (fun tail => a :: tail) (coefficientVectors p n))
        (allResidues p)

def zeroWord (p width : Nat) [NeZero p] : BranchWord p :=
  lreplicate width (zzero p)

def linearCombination {p : Nat} [NeZero p] (width : Nat) :
    List (ZMod p) → List (BranchWord p) → BranchWord p
  | [], _ => zeroWord p width
  | _, [] => zeroWord p width
  | a :: coefficients, g :: generators =>
      addWords (scaleWord a g)
        (linearCombination width coefficients generators)

/-- Executable enumeration of a generator matrix's `ZMod p` span. -/
def spanCode (p width : Nat) [NeZero p] (generators : List (BranchWord p)) :
    List (BranchWord p) :=
  lmap (fun coefficients => linearCombination width coefficients generators)
    (coefficientVectors p (llength generators))

def supportSize {p : Nat} [NeZero p] : BranchWord p → Nat
  | [] => 0
  | x :: xs => (if x = zzero p then 0 else 1) + supportSize xs

def hasCohomology {p : Nat} [NeZero p] (w : BranchWord p) : Bool :=
  3 ≤ supportSize w

def residueValueSum {p : Nat} : BranchWord p → Nat
  | [] => 0
  | x :: xs => x.val + residueValueSum xs

/-- Branch-sum zero expressed in canonical integer residues. -/
def isBranchWord {p : Nat} [NeZero p] (w : BranchWord p) : Prop :=
  residueValueSum w % p = 0

/-! ## Signature columns and determinant words -/

def qNumerator {p : Nat} [NeZero p] (a : ZMod p) (w : BranchWord p) : Nat :=
  residueValueSum (scaleWord a w)

def qValue {p : Nat} [NeZero p] (a : ZMod p) (w : BranchWord p) : Nat :=
  qNumerator a w / p

/-- Canonical sign/magnitude representation, avoiding any opaque integer cast. -/
inductive Defect where
  | nonnegative : Nat → Defect
  | negative : Nat → Defect

def defectOf (positive negative : Nat) : Defect :=
  if negative ≤ positive then Defect.nonnegative (positive - negative)
  else Defect.negative (negative - positive)

def defectNeg : Defect → Defect
  | .nonnegative 0 => .nonnegative 0
  | .nonnegative (n + 1) => .negative (n + 1)
  | .negative n => .nonnegative n

def defectIsZero : Defect → Bool
  | .nonnegative 0 => true
  | .negative 0 => true
  | _ => false

/-- Exact certificate formula `δₐ(c) = support(c) - 2 qₐ(c)`. -/
def signatureAt {p : Nat} [NeZero p] (a : ZMod p) (w : BranchWord p) : Defect :=
  defectOf (supportSize w) (2 * qValue a w)

def signatureColumn (p : Nat) [NeZero p] (w : BranchWord p) : List Defect :=
  lmap (fun a => signatureAt a w) (cyclotomicRows p)

structure SignedWord (p : Nat) where
  word : BranchWord p
  copies : Nat
  reversed : Bool

def SignedWord.oriented {p : Nat} [NeZero p] (term : SignedWord p) :
    BranchWord p :=
  if term.reversed then negativeWord term.word else term.word

def effectiveWords {p : Nat} [NeZero p] :
    List (SignedWord p) → List (BranchWord p)
  | [] => []
  | term :: terms =>
      lappend (lreplicate term.copies term.oriented) (effectiveWords terms)

def nonzeroResidues {p : Nat} [NeZero p] : BranchWord p → BranchWord p
  | [] => []
  | x :: xs =>
      if x = zzero p then nonzeroResidues xs
      else x :: nonzeroResidues xs

def concatenatedResidues {p : Nat} [NeZero p] :
    List (BranchWord p) → BranchWord p
  | [] => []
  | word :: words =>
      lappend (nonzeroResidues word) (concatenatedResidues words)

structure SignatureWeight where
  positive : Nat
  negative : Nat

def determinantSignatureAt {p : Nat} [NeZero p] (a : ZMod p) :
    List (SignedWord p) → SignatureWeight
  | [] => ⟨0, 0⟩
  | term :: terms =>
      let tail := determinantSignatureAt a terms
      ⟨term.copies * supportSize term.oriented + tail.positive,
       term.copies * (2 * qValue a term.oriented) + tail.negative⟩

def determinantSignatureZeroAt {p : Nat} [NeZero p] (a : ZMod p)
    (terms : List (SignedWord p)) : Bool :=
  let weight := determinantSignatureAt a terms
  weight.positive == weight.negative

/-! ## Balance and opposite-pair witnesses -/

def residueCount {p : Nat} (r : ZMod p) : BranchWord p → Nat
  | [] => 0
  | x :: xs => (if x = r then 1 else 0) + residueCount r xs

def hasOppositeMultiplicities {p : Nat} [NeZero p]
    (residues : BranchWord p) : Prop :=
  ∀ x : ZMod p, residueCount x residues = residueCount (zneg x) residues

def pairResidues {p : Nat} [NeZero p] : List (ZMod p) → BranchWord p
  | [] => []
  | x :: xs => x :: zneg x :: pairResidues xs

theorem pairResidues_length {p : Nat} [NeZero p]
    (representatives : List (ZMod p)) :
    llength (pairResidues representatives) = 2 * llength representatives := by
  induction representatives with
  | nil => rfl
  | cons x xs ih =>
      simp [pairResidues, llength, ih]
      omega

theorem count_pair_symmetric {p : Nat} [NeZero p] (x r : ZMod p) :
    residueCount r [x, zneg x] = residueCount (zneg r) [x, zneg x] := by
  have hleft : zneg x = r ↔ x = zneg r := by
    constructor
    · intro h
      have hn := congrArg zneg h
      simpa using hn
    · intro h
      rw [h, zneg_involutive]
  have hright : zneg x = zneg r ↔ x = r := by
    constructor
    · intro h
      have hn := congrArg zneg h
      simpa using hn
    · intro h
      rw [h]
  simp [residueCount, hleft, hright, Nat.add_comm]

theorem pairResidues_opposite {p : Nat} [NeZero p]
    (representatives : List (ZMod p)) :
    hasOppositeMultiplicities (pairResidues representatives) := by
  intro r
  induction representatives with
  | nil => simp [pairResidues, residueCount]
  | cons x xs ih =>
      have hp := count_pair_symmetric x r
      simp only [pairResidues, residueCount]
      simp only [residueCount] at hp
      omega

theorem pairResidues_even {p : Nat} [NeZero p]
    (representatives : List (ZMod p)) :
    llength (pairResidues representatives) % 2 = 0 := by
  rw [pairResidues_length]
  omega

/-- Division-free form of the Aoki balance equation at one Galois row. -/
def isBalancedResidueWord {p : Nat} (residues : BranchWord p) : Prop :=
  2 * residueValueSum residues = p * llength residues

theorem pairResidues_valueSum {p : Nat} [NeZero p]
    (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p) :
    residueValueSum (pairResidues representatives) =
      p * llength representatives := by
  induction representatives with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ≠ zzero p := hnonzero x (by simp)
      have hxs : ∀ y ∈ xs, y ≠ zzero p := by
        intro y hy
        exact hnonzero y (by simp [hy])
      simp only [pairResidues, residueValueSum]
      rw [zneg_val_of_ne_zero x hx, ih hxs]
      simp only [llength]
      have hxle : x.val ≤ p := Nat.le_of_lt x.isLt
      rw [Nat.mul_add]
      simp only [Nat.mul_one]
      omega

theorem pairResidues_balanced {p : Nat} [NeZero p]
    (representatives : List (ZMod p))
    (hnonzero : ∀ x ∈ representatives, x ≠ zzero p) :
    isBalancedResidueWord (pairResidues representatives) := by
  unfold isBalancedResidueWord
  rw [pairResidues_valueSum representatives hnonzero,
      pairResidues_length]
  exact Nat.mul_left_comm 2 p (llength representatives)

def oppositeMultiplicityCheck (p : Nat) [NeZero p]
    (residues : BranchWord p) : Bool :=
  lall (fun x => residueCount x residues == residueCount (zneg x) residues)
    (allResidues p)

def galoisResidueSum {p : Nat} [NeZero p] (a : ZMod p)
    (residues : BranchWord p) : Nat :=
  residueValueSum (scaleWord a residues)

def galoisBalanceCheck (p : Nat) [NeZero p]
    (residues : BranchWord p) : Bool :=
  lall (fun a =>
      2 * galoisResidueSum a residues == p * llength residues)
    (cyclotomicRows p)

/-! ## Split-family zero-signature calculation -/

def splitWord {p : Nat} [NeZero p] (u v : ZMod p) : BranchWord p :=
  [u, v, zneg u, zneg v]

theorem splitWord_support {p : Nat} [NeZero p] (u v : ZMod p)
    (hu : u ≠ zzero p) (hv : v ≠ zzero p) :
    supportSize (splitWord u v) = 4 := by
  have hnu := zneg_ne_zero u hu
  have hnv := zneg_ne_zero v hv
  simp [splitWord, supportSize, hu, hv, hnu, hnv]

theorem splitWord_valueSum {p : Nat} [NeZero p] (u v : ZMod p)
    (hu : u ≠ zzero p) (hv : v ≠ zzero p) :
    residueValueSum (splitWord u v) = 2 * p := by
  simp [splitWord, residueValueSum,
    zneg_val_of_ne_zero u hu, zneg_val_of_ne_zero v hv]
  omega

theorem splitWord_branchSum {p : Nat} [NeZero p] (u v : ZMod p)
    (hu : u ≠ zzero p) (hv : v ≠ zzero p) :
    isBranchWord (splitWord u v) := by
  unfold isBranchWord
  rw [splitWord_valueSum u v hu hv]
  simp

/-- Signature of a word already expressed at one cyclotomic row. -/
def rowSignature {p : Nat} [NeZero p] (w : BranchWord p) : Defect :=
  defectOf (supportSize w) (2 * (residueValueSum w / p))

/-- Symbolic all-`p` split-family zero-signature computation. -/
theorem splitWord_rowSignature_zero {p : Nat} [NeZero p]
    (u v : ZMod p) (hu : u ≠ zzero p) (hv : v ≠ zzero p) :
    rowSignature (splitWord u v) = Defect.nonnegative 0 := by
  rw [rowSignature, splitWord_support u v hu hv,
      splitWord_valueSum u v hu hv]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  simp [hp, defectOf]

/-- Exact bridge from a scaled codeword to the symbolic split calculation. -/
theorem splitWord_signature_zero_of_scaled_pair {p : Nat} [NeZero p]
    (a u v x y : ZMod p)
    (hu : u ≠ zzero p) (hv : v ≠ zzero p)
    (hx : x ≠ zzero p) (hy : y ≠ zzero p)
    (hscaled : scaleWord a (splitWord u v) = splitWord x y) :
    signatureAt a (splitWord u v) = Defect.nonnegative 0 := by
  unfold signatureAt qValue qNumerator
  rw [splitWord_support u v hu hv, hscaled,
      splitWord_valueSum x y hx hy]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  simp [hp, defectOf]

/-! ## Compact-type fusion bookkeeping -/

def originalKRank (branches vertices : Nat) : Nat :=
  branches - 2 * vertices

def remainingBranches (branches treeEdges : Nat) : Nat :=
  branches - 2 * treeEdges

def fusedKRank (branches treeEdges : Nat) : Nat :=
  remainingBranches branches treeEdges - 2

theorem fusion_rank_identity (branches vertices treeEdges : Nat)
    (hvertices : 0 < vertices)
    (htree : treeEdges = vertices - 1)
    (henough : 2 * vertices ≤ branches) :
    originalKRank branches vertices = fusedKRank branches treeEdges := by
  simp [originalKRank, fusedKRank, remainingBranches, htree]
  omega

/-! ## Frozen mixed `p = 5` witness -/

def mixedC : BranchWord 5 := [1, 1, 3, 0, 0, 0, 0, 0]
def mixedD : BranchWord 5 := [0, 0, 0, 1, 2, 4, 4, 4]
def mixedTerms : List (SignedWord 5) :=
  [{ word := mixedC, copies := 1, reversed := false },
   { word := mixedD, copies := 1, reversed := false }]
def mixedResidues : BranchWord 5 :=
  concatenatedResidues (effectiveWords mixedTerms)
def mixedFusedResidues : BranchWord 5 := [1, 1, 1, 4, 4, 4]

theorem mixedC_signature : signatureColumn 5 mixedC =
    [.nonnegative 1, .nonnegative 1, .negative 1, .negative 1] := by
  rfl

theorem mixedD_signature : signatureColumn 5 mixedD =
    [.negative 1, .negative 1, .nonnegative 1, .nonnegative 1] := by
  rfl

theorem mixed_relation_all_embeddings :
    signatureColumn 5 mixedC = lmap defectNeg (signatureColumn 5 mixedD) := by
  rfl

theorem mixed_residue_balance : oppositeMultiplicityCheck 5 mixedResidues = true := by
  rfl

theorem mixed_galois_balance : galoisBalanceCheck 5 mixedResidues = true := by
  rfl

theorem mixed_fused_tuple :
    oppositeMultiplicityCheck 5 mixedFusedResidues = true := by
  rfl

theorem mixed_fusion_rank :
    originalKRank 8 2 = fusedKRank 8 1 ∧ fusedKRank 8 1 = 4 := by
  decide

/-! ## Split-family regression matching the Python certificate -/

def splitFamily (p : Nat) [NeZero p] : List (BranchWord p) :=
  lflatMap (fun u => lmap (fun v => splitWord u v) (allResidues p))
    (allResidues p)

def splitFamilyZeroCheck (p : Nat) [NeZero p] : Bool :=
  lall (fun word =>
      !hasCohomology word || lall defectIsZero (signatureColumn p word))
    (splitFamily p)

/-- Kernel-reduced regression checks matching the first three prime rows of
the legacy Phase II split-family certificate. -/
theorem split_regression_p3 : splitFamilyZeroCheck 3 = true := by
  rfl

theorem split_regression_p5 : splitFamilyZeroCheck 5 = true := by
  rfl

theorem split_regression_p7 : splitFamilyZeroCheck 7 = true := by
  rfl

end

end

end AbelianCoverHodge.Verified
