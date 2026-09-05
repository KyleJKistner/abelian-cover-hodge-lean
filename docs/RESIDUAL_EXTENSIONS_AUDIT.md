# Adversarial assessment of the structural extensions

Date: 5 September 2026. Source checked: `abelian-cover-hodge-lean` commit
`add067109eb00dc9bd3e4cd3dcdcc2852067dd87`, especially structural Sections
3, 4, 6 and 7 and `docs/NOVELTY.md`. This is a contribution analysis, not
an external referee report or a proof of historical priority.

## Finding

The extensions do not presently provide independent evidence of a deep new
Hodge-theoretic contribution. After contracting their dependencies, the
new mathematical work is elementary finite-group arithmetic, an explicit
small-conductor exception analysis, and assembly around the same
simultaneous cross-word monodromy classification. They add breadth and
specific descriptions, but do not introduce a new cycle construction,
new general monodromy technique, or new generalized-Hodge method.

This is stronger than saying their significance is simply unknown. The
proofs themselves give positive evidence for an incremental assessment.
It is weaker than proving the exact statements were published before or
that no journal would publish them. A useful short classification can be
original and publishable; the present analysis does not settle that editorial
question.

## 1. Exceptional subgroup families: a classical-input calculation

Take the branch word consisting of an odd-order multiplicative subgroup
P of F_p^* and k opposite pairs, and put h=|P|+2k−2, which is odd.
Rohde supplies the cyclic monodromy product SL_h^{(p−1)/2}. Its commutant
immediately gives End^0(A)=Q(zeta_p) and simplicity at a very general
point. This requires no comparison of different quotient words of a
noncyclic cover.

The remaining calculation contracts as follows:

1. For SL_h on U plus U*, exterior invariants are pairings and the two
   degree-h volumes. Thus an even-degree invariant below degree 2h has
   only pairings: the first possible exceptional codimension is h.
2. In degree 2h, the candidates are pairs D_b D_c. The Hodge condition is
   equality of the corresponding signature functions. The standard prime
   balanced-tuple criterion reduces this to vP=P for c=−vb.
3. Exclude v=1, whose volume pair is already a power of a pairing, and
   identify v with v^{-1}. This gives (p−1)(|P|−1)/2 extra dimensions.
4. Fermat determinant algebraicity and diagonal pullback provide their
   cycles; the divisor dimension is the elementary monomial count
   binomial((p−1)/2+h−1,h).

The specific dimension formula and uniform family packaging may be
unprinted. Their derivation contains no further cycle-algebraization
obstruction after the classical inputs are granted. Calling these
“exceptional classes on moving simple non-CM Jacobians” describes the
objects correctly but does not measure the novelty of their construction.

## 2. All-powers generators: invariant theory plus polarization

Section 4 adds two deductions to the preceding calculation. Every balanced
volume word has equal multiplicities of each coset bP and its negative;
pairing these occurrences factors the word into the degree-2h generators
already found. Their arbitrary placement in copies of A follows from
polarization: pure powers span Sym^h of the copy-index space, and the
coefficient vectors at distinct cyclotomic embeddings vary independently
after scalar extension. Clearing denominators gives actual homomorphisms.

This is a useful precise generator theorem. Its marginal argument is a
standard polynomial polarization argument, not a new all-powers invariant
theorem. Again, the noncyclic simultaneous-factor classification is
unnecessary. The finite verification checks support the combinatorial
calculation but add no independent significance evidence.

## 3. The degree-seven generalized-Hodge statement

The additional computation is that P={1,2,4} fixes Q(sqrt(−7)), so the
twisted cyclotomic determinant is three copies of H^1 of a CM elliptic
curve E. Powers of E realize the required paired torus characters with
types (n,0) and (0,n).

[Abdulali, Theorem 10, Lemma 9 and Remark 12](https://arxiv.org/html/1203.4857v1)
then apply because the unitary signatures are (k+1,k). Ordinary HC on
A^u times E^v comes from the cyclic monodromy and Fermat sources; his
domination criterion gives generalized HC. The key method is the cited
domination machinery, with its hypotheses checked explicitly here. The
quadratic CM identification makes its application transparent. This is
an attributed classical corollary, not a new GHC principle, and does not
need the simultaneous noncyclic theorem.

## 4. Odd-exponent extension: precise marginal content

### Density

The arithmetic reduction genuinely removes a hypothesis in the usable
form of the result, but it is short. If every pair root has order at
most five for odd conductor d, all these orders divide 15. From
2a_i=(a_i+a_j)+(a_i+a_k)−(a_j+a_k) and primitivity, d divides 15.
Outside 3,5,15 there is therefore a pair of order greater than five.
Either it belongs to a good triple, or the remaining weights are its
negatives; that last case is immediately mixed or yields a different
good triple. The conditions of
[Menet–Nguyen, Definition 1.1 and Theorem 5.1](https://arxiv.org/html/2310.10401v3)
then apply.

At d=15 the residual proof checks a seven-vertex compatibility graph.
Its only all-definite primitive word is (1,2,4,8). Its pure CM type is
induced from Q(sqrt(−15)), so the primitive abelian factor is E^8; the
three-point word (1,2,12) puts E inside the Fermat Jacobian. This is an
explicit finite classification and elementary CM-type computation, not
a new density theorem or new CM algebraicity theorem.

### Cycles and assembly

Primitive cyclotomic decomposition and its rational group-ring projector
are standard. Crucially, arbitrary-order primitive determinants and the
one-slot action already occur in
[Schoen, Lemmas 1.1–1.2 and Remark 1.4](https://www.numdam.org/item/CM_1988__65_1_3_0.pdf).
The Fermat reduction uses the established Shioda–Katsura resolution;
[Aoki's Theorem 0.1](https://rikkyo.repo.nii.ac.jp/record/9851/files/AA00610867_49-02_04.pdf)
supplies exactly the stated unconditional exponents. The extension does
not prove any new Fermat Hodge case.

Given the simultaneous blocks and their algebraic identifications, the
remaining argument is: special-linear tensor invariants are generated
by pairings and determinants; those sources are Fermat summands;
rational Fourier expansion supplies a rational Hodge surjection;
semisimplicity lifts Hodge classes; algebraic maps carry source cycles
to the target. This requires care with rationality and constant factors,
but introduces no new geometric mechanism. It is a standard assembly
once the necessary block classification is available.

### Reused simultaneous classification

Odd exponent changes the reconstruction ring from F_p to Z/N, where
two remains invertible. The equations and the support-four half-sum
formula therefore work unchanged, and relations preserve conductor.
The real marginal issues are retaining the conductor-15 constant
factor and avoiding double-counted nonprimitive pieces.

Moreover, the mechanism for excluding graph relations is already in
Menet–Nguyen Proposition 6.2: Lie intertwiners become inner or dual
maps; projective scalar intertwiners are constrained by rank-one braid
spectra. The cross-word classification extends that mechanism. The
extension is not a new independence technique.

## 5. What remains to establish

The candidate original statements are the complete simultaneous
cross-word classification, its exact rank-two exceptions, and the final
uniform combination theorem. The extensions audited here concentrate
their significance in that same contribution; they do not provide four
independent routes to a major result.

The next useful test is a short referee-facing note containing only the
cross-word theorem, its genuinely extra proof over Menet–Nguyen, and one
consequence inaccessible to the quoted statements alone. If that
residual proof is only the expected support argument and elementary
pair-sum reconstruction, then the evidence favors a modest completion
or synthesis. Exact priority could still survive. Stronger journal
ambitions would require an independently important consequence or a
new obstruction overcome; the present extensions do not exhibit one.

No exact-priority claim or journal acceptance prediction follows from
this bounded assessment. This audit changes no mathematical manuscript or formal proof.
