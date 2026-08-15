module

public import AbelianCoverHodge.Verified.AokiFusion

/-!
# Exact input boundary for Aoki's prime balanced-tuple theorem

This file contains the one citation leaf used by the finite determinant-to-
pairing bridge.  It is intentionally independent of the prospective geometric
input bundle: callers pass a value of `AokiPrimeBalanceInput`, while every
application-specific deduction is proved elsewhere.

The prime balanced-tuple statement is recorded on p. 24 of N. Aoki,
*On Some Arithmetic Problems Related to the Hodge Cycles on the Fermat
Varieties*, Math. Ann. 266 (1983), 23--54, where Aoki explicitly credits it
to W. Parry.  It is used inside Aoki's classification culminating in Theorem
A; this leaf imports only the prime `B = D` statement, not that whole theorem.
Aoki's 1984 erratum changes only Theorem B and does not alter this input.
-/

namespace AbelianCoverHodge.External

public section

@[expose] section

open AbelianCoverHodge.Verified

/-- Concrete primality predicate used by the current `Std`-only residue layer. -/
abbrev IsPrime := IsPrimeModulus

/-- Every entry of the tuple lies in the nonzero part of `ZMod p`. -/
abbrev AllEntriesNonzero {p : Nat} [NeZero p]
    (word : BranchWord p) : Prop :=
  AllResiduesNonzero word

/-- Aoki's balance equation on the unit rows of `ZMod p`, in division-free
form.  The source indexes characters by units; the project separately proves
that its stronger all-nonzero-row balance restricts to this predicate. -/
def IsAokiUnitBalanced {p : Nat} [NeZero p]
    (word : BranchWord p) : Prop :=
  ∀ a : ZMod p, IsInvertibleRow a →
    2 * galoisResidueSum a word = p * llength word

/-- Exact typed form of the prime balanced-tuple theorem stated by Aoki and
credited there to Parry.

Aoki's `B_m^n` setup requires a branch tuple (sum zero modulo `p`) and writes
its length as `n + 2`, with `n` positive and even.  The branch, even-length,
minimum-length-four, and unit-row-balance premises are therefore all retained
in this citation leaf.  The determinant application proves each project-side
condition and handles the shorter balanced tuples directly. -/
structure AokiPrimeBalanceInput : Prop where
  balancedHasOppositePairing :
    forall (p : Nat) [NeZero p], IsPrime p →
      forall residues : BranchWord p,
        isBranchWord residues →
        AllEntriesNonzero residues →
        llength residues % 2 = 0 →
        4 ≤ llength residues →
        IsAokiUnitBalanced residues →
        Nonempty (OppositePairingWitness residues)

end

end


end AbelianCoverHodge.External
