# Adversarial reduction of the simultaneous-factor theorem

5 September 2026. Read-only review of `general_all_powers.tex` Section 3 and `structural_extensions.tex` Section 7.3 at repository commit `add067109eb00dc9bd3e4cd3dcdcc2852067dd87`. The task is to identify the smallest contribution remaining after crediting published tools, not merely to ask whether an identical theorem title can be found.

## Assessment

The simultaneous-factor classification looks like a **modest uniform technical generalization of an established proof**, not a new monodromy mechanism. This is positive evidence from a step-by-step reduction, rather than a pessimistic guess based on a missing citation.

The exact classification across arbitrary quotient words may be unprinted. That can make it a new theorem in the literal sense. It does not make its proof conceptually substantial: its central argument is already the argument of Menet–Nguyen Proposition 6.2, with independently varying residue words substituted for two embeddings of the same residue word. The remaining completion is support separation and an elementary four-point signed-pair-sum calculation with classical geometric converses.

I have not proved that no journal would publish this. Publication depends on usefulness, exposition, priority, and how the result is situated. I have found no mechanism here that supports the earlier Duke/JEMS rationale. Calling the unexplored remainder “potentially substantial” without this reduction would overstate the uncertainty in a favorable direction.

The final section records an important counterweight discovered during the review: a genus-16 example with dim S_f=3<4=dim S(G), contradicting the literal expectation in Spelta–Tamborini Remark 3.8. Its mechanism is classical extra automorphisms and a short spectrum calculation. It supplies a concrete possible use for a note, subject to priority review, without reversing the assessment of the general proof's depth.

## Published dependency map

The primary sources were inspected again, including proofs rather than abstracts:

| Source | Exact relevant locations | What is already there |
|---|---|---|
| [Rohde, 2007 dissertation](https://webdoc.sub.gwdg.de/ebook/dissts/Duisburg/Rohde2007.pdf) | Proposition 5.2.2; Lemma 5.2.4 and 5.2.5, printed pp. 59–61; Proposition 5.3.1 and Theorem 5.3.7, pp. 61–64 | Full individual projections, reduction of a proper subdirect product to a graph, and exclusion of graphs using pair Dehn-twist eigenvalues. The prime cyclic case is completed. |
| Same source | Lemma 5.4.2, p. 65 | The four-point exceptional analysis already uses sign choices on three pair sums and a divisibility reconstruction. |
| Same source | Theorem 5.6.1, Proposition 5.6.5, pp. 72–74 | Different-conductor factors of a single odd cyclic family are independent; proof uses graph obstruction and different orders of projective twists. |
| [Menet–Nguyen, arXiv:2310.10401v3](https://arxiv.org/html/2310.10401v3) | Theorems 2.2, 2.5, 5.1; Proposition 6.2, equations (31)–(32); Section 6.1 | Spanning-vector/reflection formulas and density; the inner-or-dual alternative, scalar ambiguity, pair spectrum, and residue recovery; full-group adjoint invariance makes the graph obstruction apply to original braid images. |
| [Forni–Matheus–Zorich, 2011](https://webusers.imj-prg.fr/~anton.zorich/Papers/SQUARE_TILED_CYCLIC_COVERS.pdf) | Section 2.6, pp. 299–301, especially Lemma 16 | The double-transposition Klein four geometry and the resulting isomorphisms between four-point cyclic covers are classical. Its formulation uses flat cyclic covers; the corresponding Kummer lift over the full labelled four-point family is also elementary. |

The first source concerns cyclic covers, not arbitrary pairs of quotient words in one abelian cover. The second's stated Proposition 6.2 also compares embeddings of one fixed word. Neither should be quoted as literally printing the new classification. The claim here is that their proof mechanism extends with very little additional work.

## Minimal residual lemma

Fix an odd integer N. Consider any finite collection of residue words c in (Z/N)^r with sum zero. Retain only words whose active support has at least four entries and whose connected complex character monodromy is the full SL_(s(c)-2). Assume the standard cyclic pair-twist formulas, and compare all characters on the same ordered configuration space. Then:

1. Two words with different supports cannot share a simple connected factor.
2. On a common support of size at least five, two words share a simple factor exactly when e=±c.
3. On a common four-point support, they share a simple factor exactly when e=±P c for a double transposition or identity P.
4. The unsigned P relations are actual deck-equivariant algebraic isomorphisms after a finite cover of the base. The negative relation is polarized duality, unless an actual unsigned symmetry also realizes it.

This lemma is the part that may deserve separate attribution as an explicit uniform statement. The group C being an evaluation code imposes no extra difficulty: at the end intersect these equivalence classes with C. Freeness of C is not needed. Changing a prime modulus to an arbitrary odd modulus requires only that 2 remain invertible.

## Independent short derivation of the residual lemma

The following is a deduction for arbitrary residue words, not a claim that the cited sources state that scope verbatim.

**Step 1: reduce to two factors.** Full SL projections imply that the connected radical acts trivially on every character space. Faithfulness kills it. A semisimple subdirect product of simple adjoint groups is a product of diagonal graph blocks. Thus a failure of the asserted independence is visible in a pair. This is ordinary semisimple Goursat; there is no new higher-order compatibility problem to solve.

**Step 2: retain the original braid images.** If a connected two-factor image is Graph(θ) in H×H with H centerless, its normalizer is itself: a normalizing pair (a,b) has θ(a)^−1 b centralizing H. Since the connected closure is normal in the full closure, each original braid belongs to the graph. This is a useful clean formulation of the standard full-group-invariance argument. It is not an additional mathematical mechanism beyond the adjoint-invariance formulation in the published proof. It prevents an erroneous finite-cover argument from killing the very eigenvalues used in the comparison.

**Step 3: separate supports.** If c has an active label i that e does not, choose another c-active label j. The (i,j) twist is projectively trivial on e after forgetting i. It is nontrivial on c, including when c_i+c_j=0: the rank-one operator in the cyclic formula has a nonzero vector, a nonzero coefficient, and a nondegenerate pairing, so it is a nonidentity unipotent in that case. A graph cannot contain a pair with exactly one coordinate equal to identity. The entire new support argument is this paragraph once the published local formula is available.

**Step 4: recover a word in rank at least three.** A complex automorphism of PGL_h is inner or inner followed by inverse transpose. Choose its one global sign ε. On a pair twist with nonzero sum the spectrum, up to a scalar, is (ζ_N^(c_i+c_j),1,...,1). The unequal multiplicities 1 and h−1 distinguish the exceptional ratio. Therefore e_i+e_j=ε(c_i+c_j) for all pairs; a zero sum must also match a zero sum because it is unipotent. Three distinct finite labels give

    2e_i=(e_i+e_j)+(e_i+e_k)−(e_j+e_k)=2εc_i.

As N is odd, this gives every finite coordinate and then the infinity coordinate by the zero-sum relation. This is the key compression: arbitrary-word reconstruction is one triangle identity after the established spectral argument. The original formulation for two embeddings does not hide a hard additional classification problem here.

**Step 5: complete rank two.** On four active positions put x=c_1+c_2, y=c_1+c_3, z=c_1+c_4. The inverse change of coordinates is

    c = (x+y+z, x−y−z, −x+y−z, −x−y+z)/2.

The three unordered eigenvalue ratios permit independently replacing x,y,z by their negatives. The four even sign changes are the Klein four double transpositions; the odd sign changes are their negatives. Hence e lies in ±V4.c. Zero pair sums change only stabilizers, so no case splitting over arbitrarily large moduli is needed.

**Step 6: give the geometric converse.** The usual Möbius double transpositions of 0,1,t,∞ carry the corresponding Kummer branch divisors to each other. Their quotient is a d-th power times a scalar in the base parameter, where d is the conductor. Adjoin the d-th root of that scalar. This gives a deck-equivariant curve isomorphism over a finite étale cover of the open configuration space. Apply its graph on cohomology. Polarization gives the negative orientation. This is classical four-point cover geometry, not a new correspondence construction.

**Step 7: reassemble.** Goursat assembles the now fully classified pair relations. Each SL block has a faithful standard occurrence, removing a putative hidden central quotient. The conditions are stable under multiplying residues by a unit. Also e=±P c preserves additive order, so different conductors cannot share these moving simple factors. No extra conductor argument remains.

This derivation is short even when all the necessary cautions are kept. The full manuscript is longer because it makes conventions, base changes, degeneracies, and Hodge orientations explicit. Those details matter for correctness; their number does not show a new conceptual obstacle has been overcome.

## What the odd-exponent extension adds to this group argument

Section 7.3 does not introduce a new simultaneous-monodromy step. The reconstruction and converse work over Z/N exactly as written above. The primitive projectors keep the conductor factors from being double counted, but are standard cyclotomic representation theory.

The work that broadens the available individual projections occurs in the preceding Section 7.2: a good-triple argument reduces the only small odd conductors to 3, 5, and 15; a finite conductor-15 classification isolates the constant CM factor. That is additional useful arithmetic analysis, and this note does not claim its exact classification is already printed. But for the group determination it is just verification of the hypotheses of the residual lemma. No stronger simultaneous-factor mechanism appears when the modulus becomes composite.

In particular, “arbitrary odd conductor” is a much broader quantifier than “prime conductor,” but the simultaneous-factor proof cost is essentially unchanged. Scope alone cannot carry the significance assessment.

## Honest boundary of the conclusion

The evidence supports saying: **the main remaining theorem probably has modest technical novelty, if its exact statement is new at all. Its proof is an economical extension and completion of published methods.** That judgment is considerably firmer than “we have not assessed whether it is substantial.”

What the evidence does not support saying:

- that the precise classification has definitely appeared before;
- that an economical theorem cannot be useful or publishable;
- that the remaining cycle-transfer and total-paper assembly have been exhaustively reduced by this group-only audit;
- that a particular journal would certainly reject it.

The burden for a higher significance claim is now concrete: exhibit a nonroutine new consequence or a genuinely new mechanism beyond this seven-step reduction. Merely finishing the exact formulation, adding more examples, or extending the modulus through invertibility of 2 does not supply that evidence.

## Counterweight: a concrete strict special-hull example

After the initial reduction, a separate check of the four-point example identified a consequential application. The formulas, dimensions and scope of the published expectation were checked independently within this audit. It does not introduce a new proof mechanism, but it is a useful concrete counterexample to a published expectation.

[Spelta–Tamborini 2025, Section 2.1 and Section 3.1](https://arxiv.org/pdf/2305.19030v2) considers all Galois G-covers with fixed topological data. It does not require G to be the full automorphism group. Their Remark 3.8, printed p. 7, suggests equality between the smallest special hull S_f and the G-defined PEL locus S(G) for all abelian covers of P1. Their proven theorems have additional hypotheses; the following challenges that expectation, not those proven theorems.

Take G=(Z/5)^2 and the code spanned by

    c=(1,1,1,2),  e=(1,1,2,1).

The four columns are nonzero and span G. Their sum is zero. The full one-parameter family is the normalization of

    y^5=x(x−1)(x−t),
    z^5=x(x−1)(x−t)^2,
    t∈P1\{0,1,∞}.

Riemann–Hurwitz gives 2g−2=25(−2+4·4/5)=30, hence g=16.

The four G-character/conjugate pairs contributing noncompact one-dimensional factors to the PEL domain have representatives

    (1,1,4,4), (2,2,3,3), 2c=(2,2,2,4), 2e=(2,2,4,2).

Each has signature (1,1); all remaining character pairs are definite or have zero cohomology. Hence dim S(G)=4. I checked this by enumerating all 24 nonzero codewords in addition to the direct signature calculation.

There is an explicit involution of the whole covering curve. Put

    T(x)=t(x−1)/(x−t),
    α^5=t^2(t−1)^2,
    β=t(t−1)/α.

Then β^5=t^3(t−1)^3, and after that finite étale root cover of the t-line,

    Φ(x,y,z)=(T(x), αz/(x−t), βy/(x−t)).

Indeed, with f_c=x(x−1)(x−t) and f_e=x(x−1)(x−t)^2,

    f_c(T(x))/f_e(x)=t^2(t−1)^2/(x−t)^5,
    f_e(T(x))/f_c(x)=t^3(t−1)^3/(x−t)^5.

Also T(T(x))=x, T(x)−t=t(t−1)/(x−t), and αβ=t(t−1), so Φ²=id. The involution conjugates the two deck generators by exchanging them. Thus the automorphism group contains G⋊C2; requiring G to be full Aut would indeed exclude this example, but that requirement is absent from the cited formulation.

The involution identifies the 2c and 2e weight-one eigenspaces as actual Hodge structures, so the four-dimensional G-only PEL domain has a diagonal relation between those two disc factors. The whole family lies in the smaller PEL locus defined by G and Φ, whose dimension is at most three. Consequently

    dim S_f ≤ 3 < 4 = dim S(G).

This strict inequality alone disproves the stated expectation in its literal scope. It requires only the explicit involution and the signature calculation, **not** the entire uniform simultaneous-factor theorem or any Hodge-conjecture argument.

One can also establish the exact dimension. Set u=2c, v=(1,1,4,4), w=(2,2,3,3). Their three individual monodromy projections are SL2. The pair twist at (1,2) separates u from v and v from w: their nontrivial eigenvalue ratios have different unordered pairs of exponents {1,4} and {2,3}. The pair at (1,3) separates u from w, with a nonzero pair sum for u and zero sum for w. Thus their three SL2 factors are independent by the elementary graph obstruction. This gives dim S_f≥3 and hence

    dim S_f=3<4=dim S(G).

The family itself has dimension one, so Z is not special. Nothing here contradicts the known statement about when one-dimensional abelian-cover families themselves are special.

A bounded search for this specific correction, the genus-16 family in the special-hull context, and Klein-four abelian-cover examples did not locate an earlier explicit treatment. This does not establish priority. The curves and extra-automorphism phenomenon are classical: for example, with v=z/y and u=y/v the same curve becomes u^5=(v^5+t)(v^5+t−1), a familiar cyclic family with additional symmetries.

**Effect on the assessment:** the strongest negative interpretation, that the result has no identifiable use beyond repackaging, is not supported. There is now a precise, short consequence correcting a published expectation. That could support a useful note if novel. It does not make the simultaneous-factor proof a new major mechanism, and does not restore the original high-significance Hodge claim.
