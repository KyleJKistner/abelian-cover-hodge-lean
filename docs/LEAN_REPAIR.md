# Finite fusion repairs, September 4, 2026

Three new modules strengthen the concrete finite layer. Existing theorem APIs are unchanged. These proofs do not establish the geometric fusion construction or the headline Hodge theorem.

## Component bounds from the actual source family

`AbelianCoverHodge/Verified/FusionBounds.lean` proves the missing local accounting step. For a `SourceBranchFamily`, its exact opposite-occurrence pairing, and a supplied `FusionForestWitness`, every forest component contains precisely the branches of the source words whose labels occur among its vertices. The proof uses the full multiplicity-preserving pair partition and the globally nonrepeated vertex labels.

The principal declarations, in namespace `AbelianCoverHodge.Verified.FusionForestWitness`, are:

- `component_originalBranchCount_eq_source_sum`: exact original branch count as a sum over the selected source words.
- `component_source_vertices_perm`: those source labels are a permutation of the component's vertex list.
- `component_originalBranchCount_lower_bound`: a uniform lower bound on each source word gives the corresponding lower bound on the component's total original branch count.
- `two_le_component_remainingBranchCount`: the existing source-family bound of two markings per source already implies two surviving markings per fused component.
- `sourceRankSum_eq_fusedComponentRankSum_of_source_family`: the old rank-preservation conclusion now follows without any separate lower-bound hypothesis on the fused components.
- `component_vertices_add_two_le_remainingBranchCount`: with at least three markings at each source, a fused component retains at least its vertex count plus two markings.
- `four_le_component_remainingBranchCount`: the preceding bound and evenness give at least four surviving markings.
- `component_fused_rank_positive_even`: the resulting numerical rank, surviving markings minus two, is positive and even.

For example, a component with source branch counts `s_v` and `V` source vertices has `S = sum s_v` original markings and `S' = S - 2(V-1)` survivors. The new proof identifies `S` with the actual source sum before applying this arithmetic. Thus `s_v >= 2` implies `S' >= 2`; `s_v >= 3` implies `S' >= V+2`, and `S'` is even. This removes an unnecessary assumption rather than renaming it.

## Determinant terms now produce labelled source and pairing data

`AbelianCoverHodge/Bridge/DeterminantFusion.lean` connects the existing concrete determinant-to-Aoki bridge to that finite fusion layer.

- `labelledEffectiveWordsFrom` labels each effective determinant copy by a distinct natural-number position and removes zero residues. Identical words and repeated copies remain distinct source positions.
- `labelledEffectiveWordsFrom_vertices` proves that the labels form the specified consecutive range.
- `effectiveWords_support_bound` and `labelledEffectiveWordsFrom_length_bound` transfer support lower bounds from signed terms to all actual labelled copies, including reversed terms.
- `determinantSourceFamily` constructs the source family under the explicit assumption that every input term has support at least three.
- `determinantSourceFamily_residues` proves that forgetting source labels gives exactly the existing `determinantResidues terms`, not a replacement tuple.
- `determinantSourcePairing` constructs a labelled occurrence pairing using the existing precisely scoped `External.AokiPrimeBalanceInput` and its verified adapters.
- `determinant_fusion_rank_and_bounds` proves rank preservation, at least four surviving markings per component, and positive even component ranks for any supplied forest certificate over this canonical pairing.

The last theorem takes an odd prime, the explicit published Aoki/Parry input, branch-valid signed terms, zero integral determinant signature at every nonzero row, support at least three for every term, and an actual forest certificate. It contains no abstract geometric stage propositions. The published input remains a theorem parameter; its absence from an axiom-dependency list does not mean Aoki's theorem has been reproved here.

## Forest existence for connected pairing graphs

`AbelianCoverHodge/Verified/ConnectedFusion.lean` supplies actual existence proofs, rather than a further certificate assumption. The selected edges are elements of the original opposite-pair list. The underlying simple graph is used only for reachability; loops and repeated parallel pairs remain in the original list and are retained among the unused smooth pairs with exact multiplicity.

In namespace `AbelianCoverHodge.Verified`:

- `oppositePairGraph` defines adjacency by the existence of an actual opposite pair between distinct endpoints.
- `IsAttachmentSpanningTree.edges_nodup` proves that an attachment tree cannot reuse an earlier pair.
- `exists_attachmentSpanningTree_of_connected` proves existence of an attachment-order spanning tree for every finite connected pair graph. A largest finite attachment tree must span: a walk leaving its vertex set would supply a new attachment and contradict maximality.
- `exists_fusionComponent_of_connected` recovers the unused pair list by a subpermutation argument and constructs a `FusionForestComponent`, preserving every pair occurrence.
- `exists_fusionForest_of_connected` builds a complete singleton forest when every vertex of the finite ambient type occurs in the source data.
- `exists_fusionComponent_on` removes the finite-ambient-type restriction. It works over a nonempty, nonrepeated list of active vertices, with actual pair endpoints in that list and reachability between those vertices.
- `SourceBranchFamily.exists_fusionForest_of_preconnected` constructs a forest directly from an actual source family and pairing, assuming reachability between its source labels. It works with arbitrary ambient labels, including the natural-number labels of `determinantSourceFamily`, and handles the empty source family as well.

The final theorem's remaining connectedness premise is the concrete statement
`forall u in family.vertexLabels, forall v in family.vertexLabels, (oppositePairGraph pairing.pairs).Reachable u v`. It is not an abstract geometric stage. Disconnected determinant pairings need a component partition before applying this result.

The existing mathlib results `SimpleGraph.exists_isAcyclic_reachable_eq_le` and `Connected.exists_isTree_le` confirm the graph-theoretic route, but do not directly produce this repository's attachment order or recover individual opposite-pair occurrences. The new proof supplies that concrete conversion by the finite maximal-attachment argument rather than treating it as an input.

## Verification

All three modules compile without warnings with the repository-pinned Lean 4.33.0, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`. The finite dependency chain was built directly with Lean into an isolated output directory, avoiding interference with the full repository build. The checked dependency chain includes `Core`, `AokiFusion`, `FusionForest`, `IntegralSignature`, `External/Aoki`, and `Bridge/DeterminantAoki`. `ConnectedFusion` additionally uses the pinned mathlib cache for connected walks, finite-cardinality bounds, list subpermutations, and bounded greatest witnesses.

Direct dependency reports for the principal local-count, rank, bound, source-family, and determinant-fusion declarations contain only `propext`, `Classical.choice`, and `Quot.sound`. No new project postulates or unfinished proof terms were introduced.

After importing the three new modules into the package root, the normal package checks are:

```sh
lake build
./scripts/audit.sh
```

For an isolated finite-layer check, compile the dependency modules in the order above with `lean -o` into a separate directory and set `LEAN_PATH` to that directory. Compile `Verified/FusionBounds` after `Verified/FusionForest`, and `Bridge/DeterminantFusion` after its two imported modules. For `ConnectedFusion`, append the dependency paths printed by `lake env printenv LEAN_PATH`; its local output can remain in the isolated directory. The local audit run saved source hashes, exact compiler version, dependency output, and generated module files under the review workspace's `work/hodge_fusion_lean_check/` directory. The coordinating full package build and dependency audit also pass with these modules imported; see `REPAIR_STATUS.md`.

## Remaining boundary

The rank and determinant theorems consume a `FusionForestWitness`, and the connected-graph results now construct one. General disconnected pair graphs still need the following concrete reduction: partition the actual source labels into reachability classes; restrict the original pair list to each class without losing multiplicity; apply `exists_fusionComponent_on`; then concatenate the component witnesses with exact pair partition, disjoint vertex lists, and vertex coverage. The target is a theorem `Nonempty (FusionForestWitness pairing)` for any `SourceBranchFamily` and its occurrence pairing, without a connectedness premise. That partition-and-assembly theorem is not yet provided.

None of these modules defines admissible covers, performs smoothing, establishes compact type, identifies the primitive factor with the relevant Jacobian, or specializes a cycle to the required determinant tensor. Distinct source-copy labels are now constructed; persistent identities for individual geometric marking slots remain a separate modeling concern.

The surviving-marking lower-bound obligation and connected-graph forest existence can now be removed from the outstanding proof list. General disconnected forest assembly and geometric realization cannot.
