module

public import AbelianCoverHodge.Mathlib.MenetNguyenGood
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Menet--Nguyen: source-scoped external interfaces

This module gives a focused interface to G. Menet and D.-M. Nguyen,
*Representations of braid groups via cyclic covers of the sphere: Zariski
closure and arithmeticity*, arXiv:2310.10401v3 (16 November 2024), Definition
1.1(a), Theorem 2.5, Corollary 2.7, Theorem 2.8, and Theorem 5.1.

The arithmetic data are concrete: there are exactly `n` finite labels, every
label is a natural number, and the Galois row is a unit of `ZMod d`.  Branch
count, range, nonvanishing, connectedness, and the case-(a) good condition are
definitions below.  Only the unavailable cyclic-cover cohomology and Zariski
closure identifications remain named propositions in `MonodromyModel`.

Each cited result is represented by a parameter structure whose only field is
the sourced implication.  All standing premises occur as separate arrows.
Constructing the finite data or the model does not supply any sourced result.

Theorem 2.5 and Theorem 2.8 are recorded at their source-level action-formula
strength.  The reflection spectrum immediately preceding Corollary 2.7 is a
separate interface; Corollary 2.7 itself records only its printed determinant,
order, and unipotence conclusions.  Nonidentity of a unipotent is a separate
manuscript obligation, not attributed to that corollary.

Theorem 2.8 is intentionally stated for the first `r` labels, as in the paper;
moving an arbitrary subset into those positions is a project-side reindexing
obligation.  We require `r < n`, because the four printed cases overlap at
`r = n`.  The last printed summand contains an undefined `q_l`; the formula
below records the inferred correction `g_l` and makes that correction visible
at the interface boundary.
-/

open scoped BigOperators

namespace AbelianCoverHodge.External.MenetNguyen

public section

@[expose] section

open AbelianCoverHodge.Mathlib.Signature
open AbelianCoverHodge.Mathlib.MenetNguyenGood

variable {d n : ℕ} [NeZero d]

/-! ## Concrete source data -/

/-- The finite labels `kᵢ` and the primitive Galois row `k mod d` used in the
paper.  Primitivity of the row is carried by the unit type itself. -/
structure Datum (d n : ℕ) [NeZero d] where
  labels : Fin n → ℕ
  row : (_root_.ZMod d)ˣ

/-- Number of finite branch labels. -/
def branchCount (_datum : Datum d n) : ℕ := n

@[simp] theorem branchCount_eq (datum : Datum d n) :
    branchCount datum = n := rfl

/-- The source standing assumption `n ≥ 3`. -/
def AtLeastThreeFiniteLabels (datum : Datum d n) : Prop :=
  3 ≤ branchCount datum

/-- Every integral label is positive. -/
def LabelsNonzero (datum : Datum d n) : Prop :=
  ∀ i, datum.labels i ≠ 0

/-- The standard representatives satisfy `1 ≤ kᵢ ≤ d - 1`. -/
def LabelsInRange (datum : Datum d n) : Prop :=
  ∀ i, 1 ≤ datum.labels i ∧ datum.labels i < d

/-- The finite label vector, now viewed in `ZMod d`. -/
def residueWord (datum : Datum d n) : BranchWord d (Fin n) :=
  fun i ↦ datum.labels i

/-- Every residue label is nonzero. -/
def ResidueLabelsNonzero (datum : Datum d n) : Prop :=
  ∀ i, residueWord datum i ≠ 0

/-- The row is active at every finite label, equivalently `q^(kᵢ) ≠ 1` in
the source notation. -/
def AllLabelsActiveAtRow (datum : Datum d n) : Prop :=
  ∀ i, (datum.row : _root_.ZMod d) * residueWord datum i ≠ 0

/-- The gcd of all finite labels. -/
def labelGCD (datum : Datum d n) : ℕ :=
  Finset.univ.gcd datum.labels

/-- Concrete connectedness criterion for
`y^d = ∏ᵢ (x - bᵢ)^(kᵢ)`: `gcd(k₁, ..., kₙ, d) = 1`. -/
def ConnectedCyclicCover (datum : Datum d n) : Prop :=
  Nat.gcd (labelGCD datum) d = 1

/-- The unit row as an ordinary residue. -/
def rowResidue (datum : Datum d n) : _root_.ZMod d :=
  datum.row

/-- Definition 1.1's rational sequence, indexed by all finite labels. -/
def fractionalWeights (datum : Datum d n) : Fin n → ℚ :=
  fractionalResidue (rowResidue datum) (residueWord datum)

/-- Menet--Nguyen Definition 1.1(a), without any hidden geometry. -/
def GoodSequenceCaseA (datum : Datum d n) : Prop :=
  AbelianCoverHodge.Mathlib.MenetNguyenGood.GoodSequenceCaseA
    Finset.univ (fractionalWeights datum)

theorem labelsNonzero_of_inRange (datum : Datum d n)
    (hRange : LabelsInRange datum) : LabelsNonzero datum := by
  intro i
  exact Nat.ne_of_gt (hRange i).1

theorem residueLabelsNonzero_of_inRange (datum : Datum d n)
    (hRange : LabelsInRange datum) : ResidueLabelsNonzero datum := by
  intro i hi
  change (datum.labels i : _root_.ZMod d) = 0 at hi
  have hval := congrArg _root_.ZMod.val hi
  rw [_root_.ZMod.val_natCast_of_lt (hRange i).2] at hval
  simp at hval
  exact (Nat.ne_of_gt (hRange i).1) hval

theorem allLabelsActiveAtRow_of_inRange (datum : Datum d n)
    (hRange : LabelsInRange datum) : AllLabelsActiveAtRow datum := by
  intro i
  have hi := residueLabelsNonzero_of_inRange datum hRange i
  simpa [datum.row.isUnit.mul_right_eq_zero] using hi

theorem support_residueWord_eq_univ (datum : Datum d n)
    (hRange : LabelsInRange datum) :
    support (residueWord datum) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro i
  simp [support, residueLabelsNonzero_of_inRange datum hRange i]

/-! ## A matrix model for the sourced action formulas -/

/-- A chosen-coordinate model of the row eigenspace.  Matrices and vectors are
mathlib objects.  The proposition-valued fields only identify them with the
geometric objects not currently constructed in the project.

`baseRoot` is intended to denote the source's `exp (-2 π i / d)`; that intent
is not silently trusted.  Every sourced interface below requires the explicit
`RootRowAlignment` predicate, and the actual row root is its power indexed by
the same `datum.row` used by `fractionalWeights`. -/
structure MonodromyModel (datum : Datum d n) where
  baseRoot : ℂˣ
  dimension : ℕ
  pairing : (Fin dimension → ℂ) → (Fin dimension → ℂ) → ℂ
  generators : Fin n → (Fin dimension → ℂ)
  pairTwist : Fin n → Fin n →
    LinearMap.GeneralLinearGroup ℂ (Fin dimension → ℂ)
  prefixTwist : ℕ → LinearMap.GeneralLinearGroup ℂ (Fin dimension → ℂ)
  EigenspaceIsCyclicCoverH1RowEigenspace : Prop
  PairingIsIntersectionHermitianForm : Prop
  RepresentationIsPureBraidMonodromy : Prop
  GeneratorsAreTheorem2_2Family : Prop
  PairCurveIsSimpleClosed : Fin n → Fin n → Prop
  PairCurveBoundsDisc : Fin n → Fin n → Prop
  PairDiscContainsExactlyTwoLabels : Fin n → Fin n → Prop
  PairTwistIsRhoOfPairDehnTwist : Fin n → Fin n → Prop
  PrefixCurveIsSimpleClosed : ℕ → Prop
  PrefixCurveBoundsDisc : ℕ → Prop
  PrefixDiscContainsExactlyFirstLabels : ℕ → Prop
  PrefixTwistIsRhoOfPrefixDehnTwist : ℕ → Prop
  IdentityComponentZariskiClosureEqSpecialUnitary : Prop

/-- The source's distinguished primitive-root generator as a complex scalar. -/
noncomputable def canonicalBaseRootScalar (d : ℕ) : ℂ :=
  Complex.exp (-((2 : ℂ) * Real.pi * Complex.I) / d)

/-- Explicit alignment between the matrix model and the cyclotomic row used
by the arithmetic sequence.  Together with the definition of `rowRoot`, this
says that the source parameter is
`exp (-2 π i / d) ^ datum.row.val`; hence changing `model.baseRoot` cannot
silently change the Menet--Nguyen sequence while leaving `fractionalWeights`
fixed. -/
def RootRowAlignment (datum : Datum d n)
    (model : MonodromyModel datum) : Prop :=
  (model.baseRoot : ℂ) = canonicalBaseRootScalar d

/-- The primitive root selected by the explicit unit row. -/
def rowRoot (datum : Datum d n) (model : MonodromyModel datum) : ℂˣ :=
  model.baseRoot ^ (rowResidue datum).val

/-- Project-side sign bridge.  The Menet--Nguyen formulas use the negative
exponential convention above, whereas the Phase I manuscript writes positive
roots `tᵢ`.  Any use that transports an MN eigenvalue to that notation must
exhibit this inverse-root equality rather than identifying the two conventions
definitionally. -/
def OppositeRootConventionBridge (datum : Datum d n)
    (model : MonodromyModel datum) (manuscriptRoot : ℂˣ) : Prop :=
  manuscriptRoot = (rowRoot datum model)⁻¹

/-- The selected root as a complex scalar. -/
def rowRootScalar (datum : Datum d n) (model : MonodromyModel datum) : ℂ :=
  rowRoot datum model

/-- The source premise that the selected `q` is a primitive `d`-th root. -/
def RowRootIsPrimitive (datum : Datum d n)
    (model : MonodromyModel datum) : Prop :=
  IsPrimitiveRoot (rowRoot datum model) d

/-- `q^(kᵢ+kⱼ)`, bundled as a complex unit. -/
def pairRoot (datum : Datum d n) (model : MonodromyModel datum)
    (i j : Fin n) : ℂˣ :=
  rowRoot datum model ^ (datum.labels i + datum.labels j)

/-- The first `r` finite labels, in the paper's fixed order. -/
def prefixLabels (_datum : Datum d n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.val < r

/-- Sum of the first `r` integral labels. -/
def prefixLabelSum (datum : Datum d n) (r : ℕ) : ℕ :=
  ∑ i ∈ prefixLabels datum r, datum.labels i

/-- `q^(k₁+⋯+kᵣ)`, bundled as a complex unit. -/
def prefixRoot (datum : Datum d n) (model : MonodromyModel datum)
    (r : ℕ) : ℂˣ :=
  rowRoot datum model ^ prefixLabelSum datum r

/-- Sum `k_(i+1) + ⋯ + k_l`, using zero-based `Fin n` indices. -/
def labelSumAfterThrough (datum : Datum d n) (i l : Fin n) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t ↦ i.val < t.val ∧ t.val ≤ l.val),
    datum.labels t

/-- The vector `g*_(i,j)` in Theorem 2.5. -/
def pairVector (datum : Datum d n) (model : MonodromyModel datum)
    (i j : Fin n) : Fin model.dimension → ℂ :=
  model.generators i +
    ∑ l ∈ Finset.univ.filter (fun l ↦ i.val < l.val ∧ l.val < j.val),
      (star (rowRootScalar datum model) ^ labelSumAfterThrough datum i l) •
        model.generators l

/-- The right-hand side of Menet--Nguyen Theorem 2.5, formula (11). -/
noncomputable def pairActionFormula (datum : Datum d n) (model : MonodromyModel datum)
    (i j : Fin n) (x : Fin model.dimension → ℂ) :
    Fin model.dimension → ℂ :=
  let q := rowRootScalar datum model
  let g := pairVector datum model i j
  x -
    (Complex.I * ((1 - q ^ datum.labels i) * (1 - q ^ datum.labels j)) /
      ((1 - q) * (1 - star q)) * model.pairing x g) • g

/-- Sum `k_(l+1) + ⋯ + k_r`, where `l` is zero-based and `r` is a
one-past-the-end prefix length. -/
def labelSumAfterToPrefix (datum : Datum d n) (l : Fin n) (r : ℕ) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t ↦ l.val < t.val ∧ t.val < r),
    datum.labels t

/-- The right-hand side of Theorem 2.8 for the generator `gᵢ`.  The four
branches are the four displayed cases in the source, translated from one-based
indices to `Fin n`.  In the last branch, the source prints an undefined `q_l`;
this definition records the inferred `g_l` correction. -/
def prefixActionFormula (datum : Datum d n) (model : MonodromyModel datum)
    (r : ℕ) (i : Fin n) : Fin model.dimension → ℂ :=
  let q := rowRootScalar datum model
  let eigen := (prefixRoot datum model r : ℂ)
  if i.val + 1 < r then
    eigen • model.generators i
  else if i.val + 1 = r then
    model.generators i + eigen •
      (∑ l ∈ Finset.univ.filter (fun l ↦ l.val + 1 < r),
        (star q ^ prefixLabelSum datum (l.val + 1) - 1) • model.generators l)
  else if i.val + 1 < n then
    model.generators i
  else
    model.generators i +
      ∑ l ∈ Finset.univ.filter (fun l ↦ l.val + 1 < r),
        (1 - q ^ labelSumAfterToPrefix datum l r) • model.generators l

/-- Concrete matrix unipotence. -/
def IsUnipotent {m : ℕ}
    (operator : LinearMap.GeneralLinearGroup ℂ (Fin m → ℂ)) : Prop :=
  IsNilpotent
    (operator.toLinearEquiv.toLinearMap - LinearMap.id)

/-- The stronger property needed by the Phase I separation argument.  The
source statements below supply unipotence but do not supply the second
conjunct, so this predicate remains a project-side obligation. -/
def IsNonidentityUnipotent {m : ℕ}
    (operator : LinearMap.GeneralLinearGroup ℂ (Fin m → ℂ)) : Prop :=
  IsUnipotent operator ∧ operator ≠ 1

/-- Manuscript obligation for a pair twist at the trivial exceptional root.
It is deliberately absent from `Corollary2_7Conclusion`. -/
def PairNonidentityUnipotentObligation (datum : Datum d n)
    (model : MonodromyModel datum) : Prop :=
  ∀ (i j : Fin n), i < j → pairRoot datum model i j = 1 →
    IsNonidentityUnipotent (model.pairTwist i j)

/-- Manuscript obligation for a prefix twist at trivial prefix root.  Theorem
2.8 supplies only unipotence in this case. -/
def PrefixNonidentityUnipotentObligation (datum : Datum d n)
    (model : MonodromyModel datum) : Prop :=
  ∀ r : ℕ, 2 ≤ r → r < n → prefixRoot datum model r = 1 →
    IsNonidentityUnipotent (model.prefixTwist r)

/-- The characteristic polynomial with one exceptional eigenvalue and all
remaining roots equal to one. -/
noncomputable def oneExceptionalCharpoly (m : ℕ) (eigenvalue : ℂ) : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C eigenvalue) *
    (Polynomial.X - Polynomial.C 1) ^ (m - 1)

/-! ## Theorem 2.5 and Corollary 2.7 -/

/-- External input for Theorem 2.5, specialized to the primitive unit row used
by this project.  The conclusion is the source's displayed formula (11). -/
structure Theorem2_5Input (datum : Datum d n)
    (model : MonodromyModel datum) : Prop where
  theorem2_5 :
    2 ≤ d →
    AtLeastThreeFiniteLabels datum →
    LabelsInRange datum →
    RootRowAlignment datum model →
    RowRootIsPrimitive datum model →
    AllLabelsActiveAtRow datum →
    model.EigenspaceIsCyclicCoverH1RowEigenspace →
    model.PairingIsIntersectionHermitianForm →
    model.RepresentationIsPureBraidMonodromy →
    model.GeneratorsAreTheorem2_2Family →
    ∀ (i j : Fin n), i < j →
      model.PairCurveIsSimpleClosed i j →
      model.PairCurveBoundsDisc i j →
      model.PairDiscContainsExactlyTwoLabels i j →
      model.PairTwistIsRhoOfPairDehnTwist i j →
      ∀ x,
        (model.pairTwist i j).toLinearEquiv x =
          pairActionFormula datum model i j x

/-- The nontrivial reflection spectrum established in the discussion between
Theorem 2.5 and Corollary 2.7.  It is intentionally not labelled as a
Corollary 2.7 conclusion. -/
structure NontrivialPairReflectionSpectrumConclusion (datum : Datum d n)
    (model : MonodromyModel datum) (i j : Fin n) : Prop where
  characteristicPolynomial :
    LinearMap.charpoly (model.pairTwist i j).toLinearEquiv.toLinearMap =
      oneExceptionalCharpoly model.dimension (pairRoot datum model i j : ℂ)

/-- External interface for the reflection-spectrum discussion immediately
preceding Corollary 2.7.  The nontrivial-root premise is explicit. -/
structure NontrivialPairReflectionSpectrumInput (datum : Datum d n)
    (model : MonodromyModel datum) : Prop where
  reflectionSpectrum :
    2 ≤ d →
    AtLeastThreeFiniteLabels datum →
    LabelsInRange datum →
    RootRowAlignment datum model →
    RowRootIsPrimitive datum model →
    AllLabelsActiveAtRow datum →
    model.EigenspaceIsCyclicCoverH1RowEigenspace →
    model.PairingIsIntersectionHermitianForm →
    model.RepresentationIsPureBraidMonodromy →
    model.GeneratorsAreTheorem2_2Family →
    ∀ (i j : Fin n), i < j →
      model.PairCurveIsSimpleClosed i j →
      model.PairCurveBoundsDisc i j →
      model.PairDiscContainsExactlyTwoLabels i j →
      model.PairTwistIsRhoOfPairDehnTwist i j →
      pairRoot datum model i j ≠ 1 →
      NontrivialPairReflectionSpectrumConclusion datum model i j

/-- The literal conclusions printed in Corollary 2.7. -/
structure Corollary2_7Conclusion (datum : Datum d n)
    (model : MonodromyModel datum) (i j : Fin n) : Prop where
  determinant :
    LinearEquiv.det (model.pairTwist i j).toLinearEquiv =
      pairRoot datum model i j
  sameOrderIfNontrivial :
    pairRoot datum model i j ≠ 1 →
      orderOf (model.pairTwist i j) = orderOf (pairRoot datum model i j)
  unipotentIfTrivial :
    pairRoot datum model i j = 1 → IsUnipotent (model.pairTwist i j)

/-- External input for Corollary 2.7 at exactly the pair-twist hypotheses. -/
structure Corollary2_7Input (datum : Datum d n)
    (model : MonodromyModel datum) : Prop where
  corollary2_7 :
    2 ≤ d →
    AtLeastThreeFiniteLabels datum →
    LabelsInRange datum →
    RootRowAlignment datum model →
    RowRootIsPrimitive datum model →
    AllLabelsActiveAtRow datum →
    model.EigenspaceIsCyclicCoverH1RowEigenspace →
    model.RepresentationIsPureBraidMonodromy →
    model.GeneratorsAreTheorem2_2Family →
    ∀ (i j : Fin n), i < j →
      model.PairCurveIsSimpleClosed i j →
      model.PairCurveBoundsDisc i j →
      model.PairDiscContainsExactlyTwoLabels i j →
      model.PairTwistIsRhoOfPairDehnTwist i j →
      Corollary2_7Conclusion datum model i j

/-! ## Theorem 2.8 -/

/-- The source-level action formula and the two order alternatives of Theorem
2.8. -/
structure Theorem2_8Conclusion (datum : Datum d n)
    (model : MonodromyModel datum) (r : ℕ) : Prop where
  actionFormula :
    ∀ i,
      (model.prefixTwist r).toLinearEquiv (model.generators i) =
        prefixActionFormula datum model r i
  unipotentIfTrivial :
    prefixRoot datum model r = 1 → IsUnipotent (model.prefixTwist r)
  sameOrderIfNontrivial :
    prefixRoot datum model r ≠ 1 →
      orderOf (model.prefixTwist r) = orderOf (prefixRoot datum model r)

/-- External input for Theorem 2.8.  The curve/disc/exact-branch-set premises
are deliberately three different arrows. -/
structure Theorem2_8Input (datum : Datum d n)
    (model : MonodromyModel datum) : Prop where
  theorem2_8 :
    2 ≤ d →
    AtLeastThreeFiniteLabels datum →
    LabelsInRange datum →
    RootRowAlignment datum model →
    RowRootIsPrimitive datum model →
    AllLabelsActiveAtRow datum →
    model.EigenspaceIsCyclicCoverH1RowEigenspace →
    model.RepresentationIsPureBraidMonodromy →
    model.GeneratorsAreTheorem2_2Family →
    ∀ r : ℕ, 2 ≤ r → r < n →
      model.PrefixCurveIsSimpleClosed r →
      model.PrefixCurveBoundsDisc r →
      model.PrefixDiscContainsExactlyFirstLabels r →
      model.PrefixTwistIsRhoOfPrefixDehnTwist r →
      Theorem2_8Conclusion datum model r

/-! ## Theorem 5.1, case (a), and the proved application bridge -/

/-- Case-(a) specialization of Menet--Nguyen Theorem 5.1.  The three erased
identifications and every arithmetic standing premise remain separate. -/
structure Theorem5_1CaseAInput (datum : Datum d n)
    (model : MonodromyModel datum) : Prop where
  theorem5_1_caseA :
    3 ≤ d →
    AtLeastThreeFiniteLabels datum →
    LabelsInRange datum →
    ConnectedCyclicCover datum →
    RootRowAlignment datum model →
    RowRootIsPrimitive datum model →
    model.EigenspaceIsCyclicCoverH1RowEigenspace →
    model.PairingIsIntersectionHermitianForm →
    model.RepresentationIsPureBraidMonodromy →
    GoodSequenceCaseA datum →
    model.IdentityComponentZariskiClosureEqSpecialUnitary

/-- The project's positivity criterion discharges Definition 1.1(a) exactly.
The support rewrite is the only additional step needed because the source
lists precisely the active finite labels whereas `MenetNguyenGood` starts
from a possibly zero-padded branch word. -/
theorem goodSequenceCaseA_of_positiveHodgePair
    (datum : Datum d n)
    (hRange : LabelsInRange datum)
    (hBranch : IsBranchWord (residueWord datum))
    (hPositive : PositiveHodgePair (rowResidue datum) (residueWord datum)) :
    GoodSequenceCaseA datum := by
  have hGood :=
    AbelianCoverHodge.Mathlib.MenetNguyenGood.goodSequenceCaseA_of_positiveHodgePair
      (rowResidue datum) datum.row.isUnit (residueWord datum) hBranch hPositive
  rw [support_residueWord_eq_univ datum hRange] at hGood
  exact hGood

/-- Audit-facing application of Theorem 5.1 in which positivity supplies only
the source's good-sequence premise; all other premises remain visible. -/
theorem theorem5_1_caseA_of_positiveHodgePair
    (datum : Datum d n) (model : MonodromyModel datum)
    (input : Theorem5_1CaseAInput datum model)
    (hDegree : 3 ≤ d)
    (hCount : AtLeastThreeFiniteLabels datum)
    (hRange : LabelsInRange datum)
    (hConnected : ConnectedCyclicCover datum)
    (hAlignment : RootRowAlignment datum model)
    (hPrimitive : RowRootIsPrimitive datum model)
    (hEigenspace : model.EigenspaceIsCyclicCoverH1RowEigenspace)
    (hPairing : model.PairingIsIntersectionHermitianForm)
    (hRepresentation : model.RepresentationIsPureBraidMonodromy)
    (hBranch : IsBranchWord (residueWord datum))
    (hPositive : PositiveHodgePair (rowResidue datum) (residueWord datum)) :
    model.IdentityComponentZariskiClosureEqSpecialUnitary :=
  input.theorem5_1_caseA hDegree hCount hRange hConnected hAlignment hPrimitive
    hEigenspace hPairing hRepresentation
    (goodSequenceCaseA_of_positiveHodgePair datum hRange hBranch hPositive)

/-! ## Auditable source bundle -/

/-- Exact project-side bridges currently needed on top of the five modeled
source interfaces.  They are kept out of `SourceInputs`: the sign conversion
is a manuscript convention match, and nonidentity is stronger than the
unipotence printed in Corollary 2.7 and Theorem 2.8. -/
structure ManuscriptBridgeObligations (datum : Datum d n)
    (model : MonodromyModel datum) (manuscriptRoot : ℂˣ) : Prop where
  oppositeRootConvention :
    OppositeRootConventionBridge datum model manuscriptRoot
  pairNonidentityUnipotent : PairNonidentityUnipotentObligation datum model
  prefixNonidentityUnipotent : PrefixNonidentityUnipotentObligation datum model

/-- The five Menet--Nguyen inputs currently modeled by this project.  Bundling
them changes no premise: each field retains its source-scoped implication,
including root-row and geometric-operator alignment.

This is not yet a complete source bundle for the Phase I manuscript.  The
exact Gram and generator identities of Theorem 2.2, the prefix-subspace
dimension and nondegeneracy statements of Lemma 3.9, and the eigenspace
decomposition of Corollary 3.11 are not represented here.  They must receive
separate exact interfaces before the manuscript's pair/subset spectral
separation argument can be marked complete. -/
structure SourceInputs (datum : Datum d n)
    (model : MonodromyModel datum) : Prop where
  theorem2_5 : Theorem2_5Input datum model
  nontrivialPairReflectionSpectrum :
    NontrivialPairReflectionSpectrumInput datum model
  corollary2_7 : Corollary2_7Input datum model
  theorem2_8 : Theorem2_8Input datum model
  theorem5_1_caseA : Theorem5_1CaseAInput datum model

end

end

end AbelianCoverHodge.External.MenetNguyen
