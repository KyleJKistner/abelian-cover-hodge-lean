# Balanced fusion repair: scope and evidence

Revision: 4 September 2026. The new source is [fusion_revised.tex](../manuscripts/fusion_revised.tex). The recovered Phase I and Phase II manuscripts are preserved.

The standalone mixed-determinant statement now has a classical proof draft with its rational realization, gluing, smoothing, and cycle-specialization steps written out. It is a **repaired proof candidate for independent mathematical review**, using explicit established inputs. It is not a Lean-certified geometric theorem, a novelty certification, or a proof of the full Hodge conjecture for all powers of every elementary-prime cover Jacobian.

## Exact claim

Fix an odd prime p and K = Q(zeta_p). Take any finite nonempty list of smooth connected cyclic degree-p covers of P1, each with a chosen faithful deck generator and at least three nonzero branch residues. Let their K-ranks in H1 be h_j = s_j - 2 > 0. Repetitions are allowed; branch points can be arbitrary distinct points on each individual base.

If the concatenated tuple satisfies

`2 * sum([b*a]_p for every branch occurrence a) = p * sum(s_j)`

for every b in F_p^*, then H = sum(h_j) is positive and even. The rational space whose complexification is

`direct_sum_b tensor_product_j exterior_power^(h_j)(V_(j,b))`

has dimension p - 1, lies in H^H(product_j J(Y_j), Q), and the draft proves that it is spanned by codimension-H/2 algebraic cycle classes. This is the matching-embedding realization of the tensor product **over K** of the individual K-determinants. It is smaller than their full tensor product over Q.

The proof does not require generic monodromy, independent factors, a maximal endomorphism algebra, or individual balance of each curve. The p=5 genus-2 times genus-6 example has ranks 1 and 3, individually non-middle determinant types, and a four-dimensional rational space of mixed codimension-two classes.

## Repairs supplied in the new manuscript

1. **Rational projectors, before taking determinants.** On two raw H1 tensor slots the equality-of-embedding projector is `(1/p) * sum_a T_u^a T_v^(-a)`. A star of these projectors selects matching embeddings in any number of slots. It is a rational linear combination of algebraic deck correspondences. Addition, diagonal pullback, algebraic cohomological Kunneth projectors, and normalized alternation transfer the construction to the intended cohomology of the original product of Jacobians. Koszul signs for geometric permutations are accounted for.

2. **A previously hidden scalar-action error is avoided.** The K-scalar zeta on a determinant is induced from one raw tensor slot after matching the embeddings. It acts as zeta^b on the b-line. The exterior-power deck map instead acts as zeta^(b*h_j). If p divides h_j it is trivial and cannot recover the embedding label. The revised construction works without a coprimality assumption. In the exact p=5, h_1=h_2=5 check the naive map keeps 16 embedding pairs; the correct projector keeps 4. Even with ranks 1 and 3 the naive map selects the wrong four lines.

3. **Disconnected pairing graphs.** The opposite pairing can have loops and multiple connected components. One chooses a spanning tree only within each component. Schoen and specialization provide the determinant space for each component; external products initially permit independent embedding choices. The raw-slot projector selects the desired common embedding across all components. No connectedness is silently assumed.

4. **Branch inertia versus tangent character.** Residue a is defined by positive local monodromy sigma^a. If x=u^p, the tangent action of sigma is zeta^(a^-1), not zeta^a. Thus a and -a still give inverse tangent characters. This is derived in the manuscript rather than absorbed into a sign convention.

5. **Stable admissible gluing.** Each selected tree edge consumes two opposite branch occurrences. Every target component retains exactly its original s_j special points, hence is stable. Positive source genera and the tree condition give a stable source of compact type. Its Picard identity component is the product of the original Jacobians. The remaining branch tuple is simple and has length sum(h_j)+2 in each connected component.

6. **Simultaneous algebraic smoothing.** The local cover is `uv=t`, `x=u^p`, `y=v^p`, `xy=t^p`, with the balanced deck action. The map of curves is finite; it is not claimed flat at its nodes. The curve families over the DVR are flat. ACV's balanced deformation theory and a transverse algebraic curve in a smooth atlas produce a smoothing with the prescribed special fiber. This avoids replacing an algebraic family by an unalgebraized analytic plumbing. Taking each source node parameter to have order one also makes the source total space regular there.

7. **Cycle spreading and specialization.** Apply the simple-tuple input at the geometric generic point. A finite spanning list of cycles is defined over one finite extension of the fraction field. Normalize the DVR in that extension and specialize the closures in Chow. For cohomological comparison, pass to its strict henselization with residue field C unchanged; the cycles and their descent were already constructed over the preceding DVR. Flat base-change compatibility preserves their specializations. This explicitly satisfies the henselian hypothesis of SGA 6, X.7.13. The relative K-action and projectors identify the specialized subspace exactly. Betti–etale comparison and faithful extension of scalars recover the rational span, not merely an l-adic span. This specializes known algebraic cycles; it is not an appeal to the variational Hodge conjecture.

8. **Independent Hodge-type computation.** The manuscript derives the eigendifferential multiplicity directly from local valuations in `y^p = product(x-t_i)^a_i`, with the chosen pullback action. It verifies that concatenated balance gives Hodge type (H/2,H/2), without importing a potentially opposite Chevalley–Weil sign convention.

## Exact published inputs and audit boundaries

| Input | Locator and what was checked | Role |
|---|---|---|
| Prime balanced tuples are opposite-pair tuples | [Aoki, Math. Ann. 266 (1983), p. 24 before Theorem A](https://doi.org/10.1007/BF01458703), prime case credited there to Parry. Source hypotheses and [1984 erratum](https://eudml.org/doc/163917) were pinned in the prior repository source audit. | Provides a pairing, for a nonzero even tuple of length at least four and sum zero. The manuscript checks these premises. |
| Simple-tuple determinant cycles | [Schoen 1988, Theorem 2.0, p. 11; Corollary 3.1, pp. 24–25](https://www.numdam.org/item/CM_1988__65_1_3_0.pdf), directly inspected. | Supplies cycles on the generic fused Jacobian; prime degree and genus-zero quotient identify its primitive factor with the full Jacobian up to isogeny. |
| Correction to Schoen's broader fourfold theorem | [Schoen 1998 addendum, pp. 329–330 and 334](https://doi.org/10.1023/A:1000566205021), directly inspected. | The missing polarization invariant concerns 1988 Theorem 3.2. The addendum continues to invoke Corollary 3.1. Our proof does not use the uncorrected statement of Theorem 3.2. |
| Algebraic balanced-cover deformation | [ACV, arXiv:math/0106211v1](https://arxiv.org/abs/math/0106211v1), Theorem 3.0.2, Section 3 calculation, Corollary 3.0.5, Definition 4.3.1 and Theorem 4.3.2, directly inspected. | Admissible-cover interpretation and unobstructed balanced node smoothing. The atlas-to-DVR construction is supplied in the new proof. |
| Relative Picard | [BLR, Neron Models](https://doi.org/10.1007/978-3-642-51438-8), Section 9.2, Example 8, printed pp. 246–247 (neron4.pdf page 39), and Section 9.4, Theorem 1, printed p. 259 (PDF page 45), directly inspected in the final cross-review. The original explicitly attributes Theorem 1 to **Deligne**, not Raynaud, whose theorem is the following Theorem 2. | The relative theorem supplies a smooth separated semiabelian Picard scheme. Example 8 identifies its torus rank with the dual-graph first Betti number, hence gives the product Jacobian for a tree. |
| Chow specialization and cycle compatibility | [SGA 6 original scan](https://library.slmath.org/nonmsri/sga/sga/pdf/sga6.pdf), X.7.13, printed pp. 576–579 (PDF pages 583–586), especially the explicit rational cycle-class compatibility in 7.13.11; X.7.16, printed p. 585 (PDF page 588), directly inspected. [Stacks Tag 0H4H](https://stacks.math.columbia.edu/tag/0H4H), including Lemma 62.4.3, and [0H4M](https://stacks.math.columbia.edu/tag/0H4M) were also inspected. | Closure, DVR extension, geometric-fiber passage, and rational cycle-class compatibility. Section 7.13 assumes a henselian trait; the proof now passes explicitly to strict henselization for that comparison. |

The former pending BLR and SGA 6 original-page gate is closed for the exact subsections used. The scan omits intervening SGA 6 sections 7.14–7.15; no claim of directly inspecting them is made. The citation now specifies the verified 7.13, especially 7.13.11, and 7.16 instead of implying that every intervening subsection was read. These remain standard imported results, not theorems newly proved here. The local geometrical hypotheses are checked in the manuscript. The final cross-review also checked the factorial and Koszul normalizations of the rational projectors without finding a counterexample.

## Central torus repairs: separate from fusion

The standalone theorem needs no assertion about the central torus. The two algebraic corrections in the earlier audit remain necessary for any route that computes it.

**Saturation.** If R is the subgroup generated by proposed signed Kummer relations in a free character lattice L, the character lattice for a connected quotient torus must use `L / Sat(R)`, not automatically `L / R`. For instance a self-dual relation can give `2*epsilon = 0`, leaving a spurious Z/2 quotient if one does not saturate. Any map from L to a torsion-free signature lattice that kills R also kills Sat(R): if nx belongs to R then n*delta(x)=0, whence delta(x)=0. Thus the rational kernel calculation can survive while the claimed integral character group was wrong. Proving that this saturated lattice is the geometric central torus remains a separate identification problem.

**Rank-two normalization.** If epsilon is the determinant character of a rank-two standard representation V, the canonical equivariant isomorphism `det(V) tensor V_dual -> V` shows that a standard-to-dual SL2 intertwiner acquires determinant weight plus or minus epsilon, depending on orientation. It does not automatically have weight `2*epsilon`. A scalar matrix is a direct check: it acts on the relevant Hom line by t^2, exactly det(t I), not its square. The zero-character condition may sometimes be unchanged, but that does not validate the old normalization.

**Lattice versus effective tensor monoid.** A lattice basis is not by itself a list of algebraic generators for all effective determinant words. Negative basis coefficients require an explicit realization of duals and Tate twists, or a separate effective-monoid generation argument. The fusion manuscript keeps this obligation visible. The new general
companion resolves it by enumerating all effective diagrams in each finite
degree, with actual negative-character factors and their Tate twists.

## Verification and remaining mathematical work

Run the standard-library checker with:

```sh
python3 scripts/check_fusion.py --output /tmp/fusion-check.json
```

It uses exact rational matrices for p=3,5,7 to test the matching projector and its permutation symmetry. It checks a determinant projector on an actual rank-two K-module, verifies the distinction between scalar and exterior-power actions, and exhausts finite embedding-label tests. Four curve/graph fixtures check the p=5 mixed example, repeated curves with disconnected pairing, repeated mixed connected components, and K-rank divisible by p. Reports record the script and fixture SHA-256 hashes. A failed assertion produces a nonzero exit status. These finite tests do not prove any geometric theorem or the uniform Aoki input.

The local replay and source-level environment, brace, label, and citation checks passed. PDF compilation is handled by the repository-wide repair verification; it is a separate check and is not certified by the finite projector script.

The standalone proof needs independent expert review, particularly the precise passage from the generic simple-tuple cycle theorem to the compact-type special fiber and the rational correspondence normalization. The **generator hypothesis** in this manuscript is now proved in the separate [general all-powers manuscript](../manuscripts/general_all_powers.tex), Sections 5–6. That proof retains all rational embeddings, uses actual oriented graphs, and constructs a rational algebraic diagram-source map; Hodge lifting then selects balanced effective words. It does not need the complete central torus. The standalone fusion proof remains independent of these generator arguments, so this application is not circular.

For prior art, a single simple cover is already Schoen's result, and clutching and specialization are established methods. The possible contribution is the arbitrary-list, mixed-product consequence with balance only after concatenation and a correct rational projector. A bounded search did not identify the exact quantified formulation; no priority claim or journal ranking is made.
