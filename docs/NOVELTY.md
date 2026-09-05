# Novelty assessment: 5 September 2026

**The earlier Duke/JEMS assessment was premature.** The search and direct
proof comparison identify classical sources for much of the apparent Hodge
breakthrough. A direct reduction of the remaining proofs now favors
**incremental technical novelty and synthesis**, rather than unexplored
evidence of substantial new Hodge theory. Exact priority and publishability
remain unestablished. Correctness, priority and significance are separate
questions throughout this report.

## Exact theorem under assessment

For every prime p, every rank m, and every spanning zero-sum branch datum for
(Z/p)^m, let all ordered branch points on P1 vary. The proposed theorem gives
the rational Hodge conjecture for every power of the very general Jacobian.
It includes arbitrary branch residues and repeated character factors. It is
not limited to squarefree polynomial equations. That manuscript requires
base P1, prime exponent and the full branch family.

**The new structural Section 7 goes beyond prime exponent.** For any odd
integer N, it proves a transfer criterion: if the rational Hodge conjecture
holds on every power of the degree-N Fermat Jacobian, then it holds on every
power of the very general Jacobian in every full P1 branch family of finite
abelian covers with exponent dividing N. Aoki's theorem supplies the premise
unconditionally for N=p^e (p odd), N=3^a5^b and N=3^a7^b. This includes
arbitrary abelian p-groups, such as Z/9 × Z/3, and mixed-prime groups of
exponent 15. It is a written extension, not a priority-certified theorem.

The current argument is in [general_all_powers.tex](../manuscripts/general_all_powers.tex).
The new [Fermat companion](../manuscripts/fermat_determinant_transfer.tex)
simplifies its algebraicity input. The [structural companion](../manuscripts/structural_extensions.tex)
supplies the group and Hodge-ring refinements below. All are written proofs
using stated published inputs, internally checked but not externally refereed
or fully formalized in Lean.

## What is old, and what remains a candidate contribution

| Claim | Assessment | Decisive comparison |
|---|---|---|
| Arbitrary balanced mixed determinant classes are algebraic | **Classical consequence** | A cyclic P1 determinant is an algebraic summand of prime-degree Fermat cohomology. Shioda's product theorem supplies algebraicity, even when the individual determinants are not Hodge. |
| The determinant-to-Fermat construction | **Classical mechanism, explicitly rederived** | Schoen's 1989 introduction describes this construction. The new companion supplies the full finite-quotient correspondence needed here. |
| All powers of a single prime cyclic cover, with arbitrary residues | **Old formal consequence** | Rohde's unrestricted prime cyclic monodromy theorem, classical invariant theory and the preceding Fermat algebraicity imply it. This is our deduction, not a claim that Rohde prints the HC corollary. |
| Full individual character projections | **Published input and elementary reductions** | Rohde, Mohajer–Zuo and Menet–Nguyen already supply the relevant density results. |
| Exact simultaneous blocks across distinct character words, including equal-signature factors | **Modest technical extension candidate** | MN Proposition 6.2 already uses the central proof mechanism. Comparing arbitrary words adds support separation, a triangle identity in rank at least three, and an elementary signed-pair-sum calculation with classical Klein-four geometry in rank two. Exact priority remains open; proof depth is no longer an unexplored question. |
| Full elementary-abelian all-powers theorem | **Combination-theorem candidate** | Its possible contribution is the preceding joint classification and rational algebraic assembly. The cycle construction itself should not be claimed as new. No earlier theorem with precisely all these quantifiers was located; that is not a proof of priority. |
| Exact generic Hodge group | **Structural consequence; standard torus method** | The actual graph centralizer now supplies the missing geometric premise. Signature-span determination of the center is already explicit in Xue–Zarhin. |
| Explicit first exceptional degree, dimensions and all-powers generators for the subgroup families | **Potentially useful explicit descriptions** | The new text proves precise formulas. Their algebraicity follows from old ingredients; exact priority of the descriptions is not established. |
| Products across distinct primes, even with shared branch configurations | **Structural extension candidate** | Section 5 adds joint independence and cyclotomic-field descent. This product theorem is distinct from the composite-exponent cover theorem in Section 7. |
| All odd-conductor density, with one conductor-fifteen exception | **Elementary reduction of published density, with explicit exception analysis** | MN Definition 1.1 and Theorem 5.1 apply through a good-triple lemma. The exceptional primitive word (1,2,4,8) has its whole primitive factor isogenous to E^8 for CM by Q(sqrt(−15)); it is retained. |
| Odd-exponent transfer criterion and Aoki-exponent all-powers theorem | **Broader combination-theorem candidate** | Primitive cyclic projectors, the same joint graph classification, Shioda–Katsura, and Aoki replace the prime-only assembly. No new general Fermat-cycle theorem is claimed. Exact priority of the combined scope remains unverified. |
| Genus-five special-hull example | **Short consequence of older results** | Spelta–Tamborini's Example 2 leaves the hull equality undecided, but Borówka–Ortega already supplies the exact independent elliptic variation. Classical genus-two monodromy and Goursat finish it. Earliest printing of the hull equality remains unverified. |
| All-powers generalized HC for the prime-seven subgroup family | **Attributed classical corollary** | Rohde, Fermat transfer, Shioda and Abdulali's domination machinery suffice. The quadratic CM determinant calculation makes the deduction explicit; no new GHC mechanism or priority is claimed. |

## Primary sources and precise reach

- **Shioda (1979), Theorem 2, printed p. 112.** The theorem concerns arbitrary
  products of Fermat hypersurfaces of a *fixed* degree; the preceding text
  verifies the needed condition for every prime degree in all dimensions.
  The original four-page author scan was directly inspected. Its hosting
  page has mismatched metadata for a different paper, so cite the actual
  [Proc. Japan Acad. note, 55, 111–114](https://doi.org/10.3792/pjaa.55.111).
  The [direct scan](https://www.researchgate.net/profile/Tetsuji-Shioda/publication/226509160_The_hodge_conjecture_for_Fermat_varieties/links/56716efe08ae2b1f87aef843/The-hodge-conjecture-for-Fermat-varieties.pdf)
  gives the statement on PDF page 2. This does not directly assert a theorem
  for products of different prime degrees.
- **Schoen (1989), pp. 137–138.** The inspected introduction describes a
  Fermat quotient and an algebraic correspondence to a cyclic-cover
  determinant. Only the [publisher preview](https://page-one.springer.com/pdf/preview/10.1007/BFb0095974)
  was accessible; the complete later hypotheses were not read. We therefore
  do not attribute an exact arbitrary-list theorem number to the chapter.
  The [chapter DOI](https://doi.org/10.1007/BFb0095974) identifies LNM 1399,
  137–154. The explicit companion proof removes this access limitation as a
  mathematical dependency; it remains an exact attribution limitation.
- **Schoen (1988), Lemmas 1.1–1.2 and Remark 1.4, printed pp. 5–7.**
  The [complete original article](https://www.numdam.org/item/CM_1988__65_1_3_0.pdf)
  explicitly constructs the primitive cyclotomic determinant for arbitrary
  order m using the kernel-of-sum and symmetric-group quotient. Its residual
  cyclotomic action is already on one slot. Remark 1.4 also explains
  Abel–Jacobi equivariance up to translation. Thus neither the composite
  primitive determinant construction nor that correction is new here.
  Theorem 2.0, printed p. 11, has the simple-tuple hypothesis; it is not an
  unrestricted all-powers HC theorem for noncyclic abelian covers.
- **Rohde (2007), Construction 3.2.1, Remark 3.2.2, Section 4.3 and
  Theorem 5.3.7.** The [official dissertation](https://webdoc.sub.gwdg.de/ebook/dissts/Duisburg/Rohde2007.pdf)
  allows arbitrary rational branch weights of integral sum and the full
  configuration family. Its prime cyclic theorem, printed p. 64, reaches
  the derived deck centralizer, including all conjugate embeddings. There
  is no squarefree-polynomial or dense-CM restriction. Its treatment of
  several primitive factors concerns one cyclic cover, not all distinct
  character words of an elementary-abelian cover.
  In particular, Theorem 5.6.1 and Proposition 5.6.5, printed pp. 71–74,
  already separate different conductor constituents within one odd-degree
  cyclic cover. This is stronger precedent than individual density alone;
  it still does not assemble every branch word of a noncyclic deck group.
- **Menet–Nguyen, arXiv:2310.10401v3, Theorem 5.1, Theorem B and
  Proposition 6.2.** [Primary text](https://arxiv.org/html/2310.10401v3).
  Individual eigenspace density and assembly of conjugate cyclic factors
  already use braid spectra and adjoint intertwiners. Those techniques are
  precedents, not new methods of the present paper.
- **Aoki (2000), Theorem 0.1, printed p. 177.** The original
  [paper scan](https://rikkyo.repo.nii.ac.jp/record/9851/files/AA00610867_49-02_04.pdf)
  was directly inspected, including its definition of Fermat type as any
  isogeny factor of any power of the Fermat Jacobian. The theorem proves HC
  for degrees p^e and 2p^e (p odd), and for 2^a3^b5^c7^d when c=0 or d=0.
  The present extension uses only the odd degrees. The title is *Some
  remarks on the Hodge conjecture for abelian varieties of Fermat type*,
  Comment. Math. Univ. Sancti Pauli 49 (2000), 177–194. This is a cycle
  input, not an assertion there about all moving abelian-cover families.
- **Shioda–Katsura (1979), Lemmas 1.1–1.2, printed pp. 98–99.**
  [Original paper](https://www.jstage.jst.go.jp/article/tmj1949/31/1/31_1_97/_pdf).
  Its degree-N rational map from a product of two Fermat hypersurfaces
  resolves by blowing up a product of lower-dimensional Fermat varieties.
  The structural proof uses this specific resolution to deduce HC for all
  Fermat products from the all-powers Fermat-Jacobian premise; arbitrary
  rational domination without control of its centers would not suffice.
- **Mohajer–Zuo, Lemma 6.2.2 in the inspected preprint.**
  [Primary text](https://arxiv.org/pdf/1402.1900).
  Individual positive-signature monodromy for abelian covers comes from
  cyclic quotients. This is not an exact classification of all graph
  relations between equal-signature words.
- **Spelta–Tamborini (2025), Theorem 1.7 = Theorem 3.7, Section 3 and
  Example 2.** [Author manuscript](https://arxiv.org/pdf/2305.19030v2),
  [published paper](https://doi.org/10.1016/j.bulsci.2025.103616).
  The theorem treats pairwise nonisomorphic noncompact unitary factors.
  Diagonal obstructions and several explicit repeated-factor cases are
  already studied there. Example 2 is the genus-five datum of the earlier
  note. Their [2026 manuscript](https://arxiv.org/html/2512.23479v2),
  Definition 4.3 and Theorem 4.4, also retains a no-repeating-factors condition.
- **Xue–Zarhin, Lemma 3.9, Theorem 3.11 and Section 3.13.**
  [Primary text](https://arxiv.org/pdf/0907.1563).
  Hodge-circle signatures and their Galois span already determine the
  relevant central Lie algebra. The new structural text proves its own
  exact integral quotient lattice rather than confusing it with an
  isogenous central torus.
- **Forni–Matheus–Zorich (2011), Section 2.6, pp. 299–301, Lemma 16.**
  [Author PDF](https://webusers.imj-prg.fr/~anton.zorich/Papers/SQUARE_TILED_CYCLIC_COVERS.pdf).
  The four-point Klein-four cover symmetries are explicitly described in
  their square-tiled formulation. The symmetry construction itself is old;
  the proposed additional statement excludes every other cross-character
  monodromy graph in the present family.
- **Borówka–Ortega (2020), author-manuscript Remark 3.5 and Proposition 3.9.**
  [Primary text](https://arxiv.org/pdf/1904.05962v2),
  [publication record](https://www.ams.org/tran/0000-000-00/S0002-9947-2019-07971-0/).
  The genus-five example is their non-isotropic etale Klein cover of a
  genus-two curve. They describe precisely the three independently varying
  Legendre factors; the degree-six parameterization in Proposition 3.9
  confirms independence. The proposed special-hull equality is therefore
  a short consequence of older results, even though the later example
  leaves its particular formulation undecided.
- **Abdulali (2012), Theorem 10, Lemma 9, Remark 12 and Proposition 1.**
  [Primary text](https://arxiv.org/html/1203.4857v1).
  The degree-seven family has signatures (k+1,k), satisfying the required
  difference-one condition. Its twisted determinant is three copies of
  the first cohomology of a CM elliptic curve over Q(sqrt(−7)). Explicit
  tensor characters supply every fully twisted partner required for
  domination. This strengthens the conclusion by a classical corollary,
  not by inferring generalized HC from ordinary HC alone.
- **Patel–Zhang, arXiv:2506.13729v2, Theorems 1.1–1.2 and Section 1.3.**
  [Primary text](https://arxiv.org/html/2506.13729v2).
  Their generalized Prym cycle construction concerns etale abelian covers
  of positive-genus curves and sets ramified extensions aside. It is useful
  modern context, but does not make our classical P1 determinant input new.
- **Libgober (2015), Theorem 3.1 and Corollary 3.3, printed pp. 110–111.**
  [Primary paper](https://www.journalofsing.org/volume12/libgober.pdf).
  Arbitrary abelian P1-cover Jacobians already decompose into isogeny
  components of cyclic-cover Jacobians. The decomposition is old; HC on
  its individual factors does not by itself control mixed Hodge classes.
- **Terasoma, Section 10, Theorem 4(1), printed p. 36 of the inspected v3.**
  [Primary text](https://arxiv.org/pdf/alg-geom/9705023).
  Isomorphisms between the specified hypergeometric variations are expressed
  through algebraic correspondences and Fermat Hodge cycles. This is
  substantial conceptual precedent. An identification of all mixed tensor
  summands in the present problem with universal GKZ sheaves meeting his
  hypotheses was not established; arbitrary tensor closure cannot be
  assumed from this isomorphism theorem.

General product criteria were checked as well: Hazama's 1989 Theorem 0.1
excludes type-IV factors and requires stable nondegeneracy; Arapura's
Theorems 3.1, 3.4 and Proposition 3.8 in the
[primary preprint](https://arxiv.org/pdf/math/0102070) give useful
Lefschetz-group, Fermat and curve/Jacobian statements. They do not supply an
automatic all-powers theorem for arbitrary products of the unitary factors
here. The final search combined abelian covers, noncyclic covers, odd degree,
prime powers, all powers, Fermat, Rohde and hypergeometric-sheaf terms, then
compared exact primary-source hypotheses. No exact full noncyclic
odd-exponent statement was located. This is a bounded search result,
not a proof of historical priority.

The audit also checked Schoen 1988 and its 1998 addendum, Aoki's Fermat
results, Xue–Zarhin's superelliptic all-powers results, Garnek's arithmetic
superelliptic results, low-dimensional Weil-class results, and Abdulali's
domination methods. An exact implication comparison was used throughout;
similar titles or the word “Hodge” were not treated as equivalent theorems.

## Mathematical development completed in this revision

General Section 8 gives three concrete tests of the claimed extra scope.
At p=3 the two code rows (1,1,1,2,2,2) and (1,1,2,1,2,2) both have signature
(2,2), but a single labelled twist separates them; the genus-ten cover has
complex monodromy SL4 × SL4 × SL2. At p=5 the nonproportional rows
(1,1,1,2) and (1,1,2,1) genuinely share a rank-two block through a
Klein-four graph. For the exact published genus-five binary datum,
the support argument gives Hg = Sp4 × SL2^3 and special-hull dimension six,
answering the equality left undecided in the cited example. The latter
also follows from Borówka–Ortega and classical monodromy, so it is an
illustration rather than evidence of an unprecedented phenomenon. The
odd-prime cases demonstrate the scope of the uniform classification
beyond the inspected nonrepetition criterion; they do not certify priority.

The new finite-quotient proof takes C^(s−2), divides by the kernel of the
product deck character and the symmetric group, and identifies the same
normal quotient as a quotient of a degree-p Fermat hypersurface. Proper
Chow-correspondence composition and the geometric Koszul sign give an
algebraic direct summand. This bypasses the fusion proof's smoothing and
specialization dependencies and makes the classical nature of the cycle
input visible.

The structural companion identifies the actual ambient group L over
Q(zeta_p), proves L^der equals connected monodromy, and obtains
Hg = q^−1(T). The character lattice of T is E/ker(Sigma), where E has one
determinant generator per non-self-negative oriented pair. No spurious
2-torsion or unsupported saturation of the row-image lattice is retained.

For an odd subgroup P of F_p^× of order m≥3, take each element of P once
and add k opposite pairs, with h=m+2k−2≥3. The very general Jacobian is
absolutely simple, has genus (p−1)h/2 and endomorphism algebra Q(zeta_p).
Its first exceptional Hodge classes occur exactly in codimension h, where
the quotient by divisor classes has dimension (p−1)(m−1)/2. Those classes,
their pullbacks by homomorphisms from powers, and divisors generate the
Hodge rings of every power. Their cycles exist on every smooth fiber;
simplicity, absence of lower exceptional classes and exhaustion require
the very-general hypothesis.

For p=7, P={1,2,4}, k=1, this is a two-dimensional family of simple
abelian ninefolds: codimension three has ten divisor classes and six
additional independent classes. Larger k gives unbounded genus and first
exceptional codimension. These explicit descriptions are stronger than a
bare existence statement but are not by themselves evidence of new HC cases.

The distinct-prime product theorem handles independent configurations and
a shared full configuration. It proves independence of moving groups using
projective local orders and separates determinant Hodge conditions through
linearly disjoint cyclotomic fields. It keeps constant factors and odd
Kunneth components in the argument.

Structural Section 6 additionally proves generalized HC for every power
of the prime-seven family, for all k≥1. The determinant CM partner is a
fixed elliptic curve E with field Q(sqrt(−7)). Every irreducible determinant
tensor has a fully twisted realization on a power of E, and ordinary HC
on all A^u × E^v follows from the same classical Fermat route. Abdulali's
domination criterion then applies. This is an explicitly attributed
corollary; no all-prime generalized-Hodge assertion is made.

Structural Section 7 substantially enlarges the group scope. It decomposes
the cover into primitive factors of their actual conductors, avoiding the
double counting that summing whole cyclic quotients would cause. For every
odd conductor except 3, 5 and 15, the pair-order argument produces MN's good
triple; the small conductors are treated explicitly. At conductor 15 the
one all-definite primitive orbit is an actual E^8 factor, not a missing
moving SL2 or just a determinant. E is a factor of the Fermat-15 Jacobian.
The graph classification works modulo N because it divides only by two.
Primitive determinant motives are cut out by rational cyclotomic Chow
projectors. Full rational tensor sources, including E's first cohomology,
and expanded Fourier selectors give the rational invariant surjection
without assuming those tensors are rank one over Q(zeta_N). Aoki and the
controlled Fermat blowup induction then provide the cycles. These new
steps are written out and internally reviewed; bounded arithmetic checks
are not their proof.

## Publication judgment and next decision

The current working assessment is **incremental technical novelty and
synthesis**, with no affirmative evidence for Duke/JEMS-level significance.
This is supported by a direct contraction of the proofs, not just by failure
to find an exact earlier theorem. MN Proposition 6.2 already contains the
inner/dual comparison, control of projective scalars, braid spectra and
residue reconstruction. Our marginal steps are arbitrary-word comparison,
support separation, and the elementary rank-two completion. Rohde already
supplies the graph method and cyclic conductor separation. The extensions
add arithmetic reductions, finite exception analysis and standard assembly;
they supply no independent new cycle or generalized-Hodge mechanism.

See the [seven-step residual group audit](RESIDUAL_GROUP_AUDIT.md) and
[extension audit](RESIDUAL_EXTENSIONS_AUDIT.md) for the actual deductions.
An exact statement can still be original even when its proof is a modest
extension. That does not establish publishability, which remains
unassessed by an external specialist. Merely expanding the present route
with more corollaries is not a supported strategy for reaching Duke/JEMS.

There is a specific counterweight to a claim of no identifiable new use.
The existing four-point genus-16 example has dim S_f=3<4=dim S(G), contrary
to the informal expectation in Spelta–Tamborini Remark 3.8. The group audit
records an explicit extra involution, all contributing signatures, and
three independent moving factors. The strict inequality already follows
from the involution and signatures, without the uniform theorem or HC.
The source does not require G to be the full automorphism group. This
challenges an informal expectation, not the paper's proved theorems.
Subject to priority and external verification, it provides a concrete
reason for a short note. Its classical extra-symmetry mechanism does not
restore the earlier high-significance Hodge rationale.

The strongest current presentation would lead with exact simultaneous
monodromy and generic Hodge groups, explain explicitly how it removes the
repeated-factor restriction, and present all-powers HC as an application of
classical determinant cycles. A referee should be able to locate the precise
new group assertion before encountering journal-level claims.

A substantive scope obstruction was resolved during this revision:
mixed-order primitive motives and graph relations can be assembled for
odd-exponent covers. The new statement is therefore stronger than the
original prime-P1 theorem. Its algebraicity is still supplied by classical
Fermat results, and broader scope alone does not establish Duke/JEMS-level
novelty. Remaining directions include even composite exponent, odd exponents
outside the known Fermat premise, and ramified positive-genus bases. An
unconditional theorem for unrestricted odd N is not claimed. Arbitrary
restricted subfamilies acquire new Hodge tensors and cannot be reached by
reusing the full-family proof.

This revision pursued exact Hodge groups, minimal exceptional degree,
all-powers generators, mixed-prime products, degree-seven generalized HC,
and the odd-exponent criterion with unconditional Aoki cases to written
proof milestones.
It does not claim to have reached the requested journal level. The remaining
review questions are concrete: correctness of the universal graph
classification and rational assembly; exact prior scope in the full Schoen
chapter and abelian-cover literature; and whether the resulting new scope
is substantial enough for publication. No collaborators were contacted.
