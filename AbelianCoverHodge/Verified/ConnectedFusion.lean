module

public import AbelianCoverHodge.Verified.FusionBounds
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Nat.Find

/-!
# Attachment trees and fusion components for finite connected pair graphs

The graph below records adjacency through actual opposite-occurrence pairs.
Loops do not give adjacency, but are retained in the original pair list. A
maximal finite attachment tree must contain every vertex of a connected graph:
otherwise a walk out of the tree supplies another attachment.

Unused pairs, including loops and repeated parallel pairs, are retained with
their full multiplicity in a concrete `FusionForestComponent`. The disconnected
component partition is a separate construction.
-/

namespace AbelianCoverHodge.Verified

public section

@[expose] section

variable {p : Nat} [NeZero p] {Vertex : Type}

/-- Adjacency in the multigraph's underlying simple graph. The original pair
list, rather than this simple graph, remains the source of selected edges. -/
def oppositePairGraph (pairs : List (OppositeOccurrencePair p Vertex)) :
    SimpleGraph Vertex where
  Adj left right := left ≠ right ∧
    ∃ pair ∈ pairs, pair.Joins left right
  symm := by
    constructor
    intro left right h
    rcases h with ⟨hne, pair, hpair, hjoins⟩
    exact ⟨Ne.symm hne, pair, hpair, pair.joins_comm.mp hjoins⟩
  loopless := by
    constructor
    intro vertex h
    exact h.1 rfl

namespace IsAttachmentSpanningTree

/-- An attachment cannot reuse an earlier pair: its new endpoint was absent
from all earlier edges. This controls multiplicity when pairs are selected. -/
theorem edges_nodup
    {vertices : List Vertex} {edges : List (OppositeOccurrencePair p Vertex)}
    (tree : IsAttachmentSpanningTree vertices edges) : edges.Nodup := by
  induction tree with
  | root => simp
  | @attach vertices edges tree edge newVertex oldVertex old_mem new_not_mem joins ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih⟩
    intro hedge
    have hends := tree.edge_endpoints_mem edge hedge
    rcases joins with h | h
    · exact new_not_mem (h.1 ▸ hends.1)
    · exact new_not_mem (h.2 ▸ hends.2)

end IsAttachmentSpanningTree

private theorem walk_crosses_vertex_list
    {graph : SimpleGraph Vertex} {first last : Vertex}
    (walk : graph.Walk first last) (vertices : List Vertex)
    (hfirst : first ∈ vertices) (hlast : last ∉ vertices) :
    ∃ oldVertex ∈ vertices, ∃ newVertex ∉ vertices,
      graph.Adj oldVertex newVertex := by
  classical
  induction walk with
  | nil => exact (hlast hfirst).elim
  | @cons first next last hadj walk ih =>
    by_cases hnext : next ∈ vertices
    · exact ih hnext hlast
    · exact ⟨first, hfirst, next, hnext, hadj⟩

/-- Every finite connected opposite-pair graph has an attachment-order
spanning tree made from actual pairs in the original list. -/
theorem exists_attachmentSpanningTree_of_connected
    [Fintype Vertex]
    (pairs : List (OppositeOccurrencePair p Vertex))
    (hconnected : (oppositePairGraph pairs).Connected) :
    ∃ vertices edges,
      IsAttachmentSpanningTree vertices edges ∧
      (∀ vertex : Vertex, vertex ∈ vertices) ∧
      (∀ pair ∈ edges, pair ∈ pairs) := by
  classical
  let Possible : Nat → Prop := fun count =>
    ∃ vertices edges,
      IsAttachmentSpanningTree vertices edges ∧
      (∀ pair ∈ edges, pair ∈ pairs) ∧ vertices.length = count
  obtain ⟨root⟩ := hconnected.nonempty
  have hbase : Possible 1 :=
    ⟨[root], [], .root root, by simp, rfl⟩
  have hcard : 1 ≤ Fintype.card Vertex :=
    (IsAttachmentSpanningTree.root (p := p) root).vertices_nodup.length_le_card
  obtain ⟨vertices, edges, tree, hselected, hlength⟩ :=
    Nat.findGreatest_spec (P := Possible) hcard hbase
  refine ⟨vertices, edges, tree, ?_, hselected⟩
  intro vertex
  by_contra hnot
  obtain ⟨inside, hinside⟩ := List.exists_mem_of_ne_nil vertices tree.vertices_nonempty
  obtain ⟨walk⟩ := hconnected inside vertex
  obtain ⟨oldVertex, hold, newVertex, hnew, hadj⟩ :=
    walk_crosses_vertex_list walk vertices hinside hnot
  rcases hadj.2 with ⟨pair, hpair, hjoins⟩
  have extended := tree.attach pair newVertex oldVertex hold hnew
    (pair.joins_comm.mp hjoins)
  have hmore : Possible (vertices.length + 1) := by
    refine ⟨newVertex :: vertices, pair :: edges, extended, ?_, by simp⟩
    intro chosen hchosen
    simp only [List.mem_cons] at hchosen
    rcases hchosen with rfl | hchosen
    · exact hpair
    · exact hselected chosen hchosen
  have hbound : vertices.length + 1 ≤ Fintype.card Vertex :=
    extended.vertices_nodup.length_le_card
  have hmax := Nat.le_findGreatest hbound hmore
  omega

/-- The unused list is recovered with exact multiplicity. Parallel copies of
a selected graph edge are retained, and every loop remains a smooth pair. -/
theorem exists_fusionComponent_of_connected
    [Fintype Vertex]
    (pairs : List (OppositeOccurrencePair p Vertex))
    (hconnected : (oppositePairGraph pairs).Connected) :
    ∃ component : FusionForestComponent p Vertex,
      pairs.Perm component.allPairs ∧
      ∀ vertex : Vertex, vertex ∈ component.vertices := by
  classical
  obtain ⟨vertices, edges, tree, hall, hselected⟩ :=
    exists_attachmentSpanningTree_of_connected pairs hconnected
  have hsubperm : edges.Subperm pairs :=
    tree.edges_nodup.subperm hselected
  rcases hsubperm with ⟨selected, hperm, hsublist⟩
  obtain ⟨smooth, hsplit⟩ := hsublist.exists_perm_append
  refine ⟨{
    vertices := vertices
    nodePairs := edges
    smoothPairs := smooth
    spanningTree := tree
    smooth_endpoints_mem := fun pair _ => ⟨hall pair.leftVertex, hall pair.rightVertex⟩
  }, ?_, hall⟩
  exact hsplit.trans (hperm.append_right smooth)

/-- A connected pairing graph covering every vertex has a complete singleton
forest certificate. The coverage premise is the concrete absence of unused
ambient labels; it is automatic when the vertex type is the actual source set. -/
theorem exists_fusionForest_of_connected
    [Fintype Vertex]
    (occurrences : List (BranchOccurrence p Vertex))
    (pairing : OccurrencePairingWitness occurrences)
    (hconnected : (oppositePairGraph pairing.pairs).Connected)
    (hcoverage : ∀ vertex : Vertex,
      ∃ occurrence ∈ occurrences, occurrence.vertex = vertex) :
    Nonempty (FusionForestWitness pairing) := by
  obtain ⟨component, hpartition, hall⟩ :=
    exists_fusionComponent_of_connected pairing.pairs hconnected
  refine ⟨{
    components := [component]
    pair_partition := ?_
    vertices_nodup := ?_
    vertex_coverage := ?_
  }⟩
  · simpa [forestNodePairs, forestSmoothPairs, FusionForestComponent.allPairs] using hpartition
  · simpa [forestVertices] using component.spanningTree.vertices_nodup
  · intro vertex
    constructor
    · intro _
      exact hcoverage vertex
    · intro _
      simpa [forestVertices] using hall vertex

/-- The finite-support form also permits an infinite ambient label type, such
as the natural-number labels used for determinant copies. -/
theorem exists_fusionComponent_on
    (pairs : List (OppositeOccurrencePair p Vertex))
    (active : List Vertex) (hnodup : active.Nodup) (hne : active ≠ [])
    (hends : ∀ pair ∈ pairs,
      pair.leftVertex ∈ active ∧ pair.rightVertex ∈ active)
    (hconnected : ∀ first ∈ active, ∀ last ∈ active,
      (oppositePairGraph pairs).Reachable first last) :
    ∃ component : FusionForestComponent p Vertex,
      pairs.Perm component.allPairs ∧ component.vertices.Perm active := by
  classical
  let Possible : Nat → Prop := fun count =>
    ∃ vertices edges,
      IsAttachmentSpanningTree vertices edges ∧
      (∀ pair ∈ edges, pair ∈ pairs) ∧
      vertices ⊆ active ∧ vertices.length = count
  obtain ⟨root, hroot⟩ := List.exists_mem_of_ne_nil active hne
  have hbase : Possible 1 :=
    ⟨[root], [], .root root, by simp, by simpa using hroot, rfl⟩
  have hcard : 1 ≤ active.length := by
    cases active with
    | nil => exact (hne rfl).elim
    | cons head tail => simp
  obtain ⟨vertices, edges, tree, hselected, hsubset, hlength⟩ :=
    Nat.findGreatest_spec (P := Possible) hcard hbase
  have hall : ∀ vertex ∈ active, vertex ∈ vertices := by
    intro vertex hactive
    by_contra hnot
    obtain ⟨inside, hinside⟩ := List.exists_mem_of_ne_nil vertices tree.vertices_nonempty
    obtain ⟨walk⟩ := hconnected inside (hsubset hinside) vertex hactive
    obtain ⟨oldVertex, hold, newVertex, hnew, hadj⟩ :=
      walk_crosses_vertex_list walk vertices hinside hnot
    rcases hadj.2 with ⟨pair, hpair, hjoins⟩
    have hnewActive : newVertex ∈ active := by
      have hpairends := hends pair hpair
      rcases hjoins with h | h
      · exact h.2 ▸ hpairends.2
      · exact h.1 ▸ hpairends.1
    have extended := tree.attach pair newVertex oldVertex hold hnew
      (pair.joins_comm.mp hjoins)
    have hsubset' : newVertex :: vertices ⊆ active := by
      intro vertex hvertex
      simp only [List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact hnewActive
      · exact hsubset hvertex
    have hmore : Possible (vertices.length + 1) := by
      refine ⟨newVertex :: vertices, pair :: edges, extended, ?_, hsubset', by simp⟩
      intro chosen hchosen
      simp only [List.mem_cons] at hchosen
      rcases hchosen with rfl | hchosen
      · exact hpair
      · exact hselected chosen hchosen
    have hbound : vertices.length + 1 ≤ active.length :=
      extended.vertices_nodup.length_le_of_subset hsubset'
    have hmax := Nat.le_findGreatest hbound hmore
    omega
  have hvertices : vertices.Perm active :=
    (List.perm_ext_iff_of_nodup tree.vertices_nodup hnodup).2
      (fun vertex => ⟨fun h => hsubset h, fun h => hall vertex h⟩)
  have hsubperm : edges.Subperm pairs := tree.edges_nodup.subperm hselected
  rcases hsubperm with ⟨selected, hperm, hsublist⟩
  obtain ⟨smooth, hsplit⟩ := hsublist.exists_perm_append
  have hpartition : pairs.Perm (edges ++ smooth) :=
    hsplit.trans (hperm.append_right smooth)
  refine ⟨{
    vertices := vertices
    nodePairs := edges
    smoothPairs := smooth
    spanningTree := tree
    smooth_endpoints_mem := ?_
  }, hpartition, hvertices⟩
  intro pair hpair
  have hin : pair ∈ pairs := hpartition.mem_iff.mpr (by simp [hpair])
  have hpends := hends pair hin
  exact ⟨hall _ hpends.1, hall _ hpends.2⟩

/-- A connected graph on the actual source labels supplies a forest directly,
even for natural-number labels. The empty source family is included. -/
theorem SourceBranchFamily.exists_fusionForest_of_preconnected
    (family : SourceBranchFamily p Vertex)
    (pairing : OccurrencePairingWitness family.occurrences)
    (hconnected : ∀ first ∈ family.vertexLabels, ∀ last ∈ family.vertexLabels,
      (oppositePairGraph pairing.pairs).Reachable first last) :
    Nonempty (FusionForestWitness pairing) := by
  classical
  by_cases hempty : family.words = []
  · have hoccurrences : family.occurrences = [] := by
      simp [SourceBranchFamily.occurrences, LabelledBranchWord.allOccurrences, hempty]
    have hlength := pairing.occurrence_count_eq_twice_pair_count
    have hzero : family.occurrences.length = 0 := congrArg List.length hoccurrences
    have hpairs : pairing.pairs = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨{
      components := []
      pair_partition := ?_
      vertices_nodup := by simp [forestVertices]
      vertex_coverage := ?_
    }⟩
    · simp [forestNodePairs, forestSmoothPairs, hpairs]
    · intro vertex
      simp [forestVertices, hoccurrences]
  · have hlabels : family.vertexLabels ≠ [] := by
      simpa [SourceBranchFamily.vertexLabels] using hempty
    have hends : ∀ pair ∈ pairing.pairs,
        pair.leftVertex ∈ family.vertexLabels ∧ pair.rightVertex ∈ family.vertexLabels := by
      intro pair hpair
      constructor
      · apply (family.mem_vertexLabels_iff_exists_occurrence pair.leftVertex).mpr
        refine ⟨⟨pair.leftVertex, pair.representative⟩, ?_, rfl⟩
        apply pairing.coverage.mem_iff.mpr
        simp only [occurrencesOfPairs, List.mem_flatMap]
        exact ⟨pair, hpair, by simp [OppositeOccurrencePair.occurrences]⟩
      · apply (family.mem_vertexLabels_iff_exists_occurrence pair.rightVertex).mpr
        refine ⟨⟨pair.rightVertex, zneg pair.representative⟩, ?_, rfl⟩
        apply pairing.coverage.mem_iff.mpr
        simp only [occurrencesOfPairs, List.mem_flatMap]
        exact ⟨pair, hpair, by simp [OppositeOccurrencePair.occurrences]⟩
    obtain ⟨component, hpartition, hvertices⟩ :=
      exists_fusionComponent_on pairing.pairs family.vertexLabels family.vertices_nodup
        hlabels hends hconnected
    refine ⟨{
      components := [component]
      pair_partition := ?_
      vertices_nodup := ?_
      vertex_coverage := ?_
    }⟩
    · simpa [forestNodePairs, forestSmoothPairs, FusionForestComponent.allPairs] using hpartition
    · simpa [forestVertices] using component.spanningTree.vertices_nodup
    · intro vertex
      simp only [forestVertices, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      exact hvertices.mem_iff.trans (family.mem_vertexLabels_iff_exists_occurrence vertex)

end

end

end AbelianCoverHodge.Verified
