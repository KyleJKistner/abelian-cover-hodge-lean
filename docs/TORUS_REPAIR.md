# Corrected determinant-torus refinement

This note replaces the raw presentation and rank-two normalization used in
legacy Phase II P2.5/P2.9. The later
[structural companion](../manuscripts/structural_extensions.tex) now supplies
the geometric ambient-group identification that was previously conditional.
The distinctions below explain why the old presentation itself remains unsafe.

## Saturation is the identity-component operation

Let `E` be a finite free character lattice, `Q = D(E)` its split torus over a
characteristic-zero field, and `R ⊂ E` a subgroup of monomial relations. Put

\[
H=\bigcap_{r\in R}\ker(r:Q\longrightarrow\mathbb G_m),\qquad
R^{\rm sat}=\{e\in E:\exists n\in\mathbb Z\setminus\{0\},\quad ne\in R\}.
\]

Then

\[
X^*(H)=E/R,\qquad X^*(H^0)=E/R^{\rm sat}.
\]

For the second equality, the torsion subgroup of `E/R` consists exactly of
`R^sat/R`. Removing that torsion gives the character group of the identity
component. Equivalently, Smith normal form gives
`H ≅ μ_d1 × ... × μ_dr × G_m^(rank E-r)` and discarding the finite root-of-unity
factors gives `H^0`. These are characteristic-zero assertions. The
diagonalizable-group/character-module equivalence and the torus criterion are
the standard input, as in [Milne, Algebraic Groups, Chapter 12, especially
12.14–12.15](https://www.jmilne.org/math/Books/iAG2022.pdf).

If an integral signature map `Σ:E→Z^Γ` kills `R`, it kills `R^sat`: from
`ne∈R` follows `nΣ(e)=0`, and the target is torsion-free. It therefore descends
to `E/R^sat` with the same image. This last statement is proved in the
repository's `Mathlib/DeterminantLattice.lean` and
`Mathlib/DeterminantSignature.lean`.

**Scope boundary.** To identify this `H^0` with the determinant quotient of
the actual geometric centralizer, one must prove that the supplied oriented
correspondences give exactly these monomial equations, with no missing
relations or unrecorded finite isogeny. A determinant image and a central
torus can be isogenous without the displayed determinant characters forming
the entire integral character lattice. Saturation alone does not prove that
geometric identification. The new general monodromy block proof supplies
part of the background; it does not identify the full Hodge-group center.
The [general all-powers proof](GENERAL_ALL_POWERS.md) avoids this refinement.
The new structural companion separately defines the symplectic centralizer
of the deck action and actual oriented graph maps, proves over K that its
factors are GL_h or self-negative SL_2, and identifies its derived group
with monodromy. Thus its determinant quotient has an explicit free lattice:
one generator per non-self-negative oriented pair, and none for a
self-negative pair. This supplies the missing geometric identification
without retaining spurious 2-torsion or substituting the center for its
isogenous determinant image.

## The rank-two character is one determinant

For a two-dimensional standard space `V`, let

\[
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\]

The action on `Hom(V*,V)` is `T↦ATA^t`, and direct multiplication gives

\[
AJA^t=\det(A)J.
\]

Thus its alternating invariant line has character `det(V)`; the reverse
Hom line has its inverse character. If `ε` denotes the determinant
character, the two characters are `+ε` and `-ε`, not `2ε`.
`Mathlib/RankTwoDeterminant.lean` encodes the universal polynomial identity
over a commutative ring and uniqueness of the scalar coefficient. It does
not assert that every such line is a geometric Hodge homomorphism.

## The group-theoretic deduction and its now-supplied geometric premise

Suppose a connected rational reductive group `P`, its derived subgroup `D`,
and a rational Hodge representation have actually been identified, with
`D ⊂ Hg ⊂ P`. For the quotient `π:P→P/D`, let `T` be the smallest rational
subtorus containing the image of the Hodge circle. Then `Hg=π⁻¹(T)`.
Indeed, the image of `Hg` is `T` by its defining minimality, and `Hg` already
contains the entire kernel `D`. Describing `T` by the annihilator of all
Galois-conjugate circle cocharacters is standard torus duality.

This deduction is useful only after proving the displayed inclusions and
the correct integral lattice and cocharacters. It is not a replacement for
the general geometric group theorem. The structural companion now proves
the displayed inclusions and quotient lattice for the elementary-prime
family and applies this deduction. It obtains Hg=q^-1(T), with
X*(T)=E/ker(Sigma)=im(Sigma), as an exact quotient lattice; it does not claim
the image is saturated in the auxiliary row lattice. This is a written
proof, not a new Lean or external verification result. The signature-span
method itself is already in Xue--Zarhin, arXiv:0907.1563v4, Lemma 3.9 and
Theorem 3.11. Its uniform geometric application is assessed separately in
[NOVELTY.md](NOVELTY.md).
