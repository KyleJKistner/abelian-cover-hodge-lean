module

public import AbelianCoverHodge.Verified.FusionForest

/-!
# Local branch bounds from a source family

A forest's exact occurrence partition and disjoint vertex lists determine the
source words belonging to each component. This file derives the componentwise
branch lower bounds from those source words; they need not be additional data.
The result concerns finite labelled lists and a supplied forest certificate.
-/

namespace AbelianCoverHodge.Verified

public section

@[expose] section

variable {p : Nat} [NeZero p] {Vertex : Type}

private theorem filter_all {α : Type} (keep : α → Bool) (items : List α)
    (hkeep : ∀ item ∈ items, keep item = true) :
    items.filter keep = items := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    have hhead := hkeep item (by simp)
    have htail := ih (fun x hx => hkeep x (by simp [hx]))
    simp [hhead, htail]

private theorem filter_none {α : Type} (keep : α → Bool) (items : List α)
    (hkeep : ∀ item ∈ items, keep item = false) :
    items.filter keep = [] := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    have hhead := hkeep item (by simp)
    have htail := ih (fun x hx => hkeep x (by simp [hx]))
    simp [hhead, htail]

private theorem occurrence_vertex_mem
    (component : FusionForestComponent p Vertex)
    (occurrence : BranchOccurrence p Vertex)
    (hoccurrence : occurrence ∈ occurrencesOfPairs component.allPairs) :
    occurrence.vertex ∈ component.vertices := by
  simp only [occurrencesOfPairs, List.mem_flatMap] at hoccurrence
  rcases hoccurrence with ⟨pair, hpair, hoccurrence⟩
  have hends := component.allPair_endpoints_mem pair hpair
  simp only [OppositeOccurrencePair.occurrences, List.mem_cons,
    List.not_mem_nil, or_false] at hoccurrence
  rcases hoccurrence with rfl | rfl
  · exact hends.1
  · exact hends.2

private theorem filtered_pair_count_sum
    (keep : BranchOccurrence p Vertex → Bool)
    (components : List (FusionForestComponent p Vertex)) :
    ((occurrencesOfPairs (forestNodePairs components)).filter keep).length +
        ((occurrencesOfPairs (forestSmoothPairs components)).filter keep).length =
      (components.map fun component =>
        ((occurrencesOfPairs component.allPairs).filter keep).length).sum := by
  induction components with
  | nil => rfl
  | cons component components ih =>
    simp only [forestNodePairs, forestSmoothPairs, List.flatMap_cons,
      occurrencesOfPairs_append, List.filter_append, List.length_append,
      List.map_cons, List.sum_cons, FusionForestComponent.allPairs] at ih ⊢
    omega

private theorem filtered_component_sum
    [DecidableEq Vertex]
    (components : List (FusionForestComponent p Vertex))
    (hnodup : (forestVertices components).Nodup)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ components) :
    (components.map fun other =>
      ((occurrencesOfPairs other.allPairs).filter
        (fun occurrence => decide (occurrence.vertex ∈ component.vertices))).length).sum =
      component.originalBranchCount := by
  induction components with
  | nil => simp at hcomponent
  | cons head tail ih =>
    have hsplit :
        (head.vertices ++ forestVertices tail).Nodup := by
      simpa [forestVertices] using hnodup
    have htail : (forestVertices tail).Nodup :=
      (List.nodup_append.mp hsplit).2.1
    have hdisjoint := (List.nodup_append.mp hsplit).2.2
    simp only [List.mem_cons] at hcomponent
    rcases hcomponent with heq | hcomponent
    · subst component
      have hhead :
          (occurrencesOfPairs head.allPairs).filter
            (fun occurrence => decide (occurrence.vertex ∈ head.vertices)) =
          occurrencesOfPairs head.allPairs := by
        apply filter_all
        intro occurrence hoccurrence
        simp [occurrence_vertex_mem head occurrence hoccurrence]
      have htailzero : ∀ other ∈ tail,
          ((occurrencesOfPairs other.allPairs).filter
            (fun occurrence => decide (occurrence.vertex ∈ head.vertices))).length = 0 := by
        intro other hother
        rw [filter_none]
        · rfl
        · intro occurrence hoccurrence
          have hothermem := occurrence_vertex_mem other occurrence hoccurrence
          have hglobal : occurrence.vertex ∈ forestVertices tail := by
            simp only [forestVertices, List.mem_flatMap]
            exact ⟨other, hother, hothermem⟩
          have hnot : occurrence.vertex ∉ head.vertices := by
            intro hmem
            exact hdisjoint _ hmem _ hglobal rfl
          simp [hnot]
      have hsumzero :
          (tail.map fun other =>
            ((occurrencesOfPairs other.allPairs).filter
              (fun occurrence => decide (occurrence.vertex ∈ head.vertices))).length).sum = 0 := by
        apply List.sum_eq_zero_iff_forall_eq_nat.mpr
        intro count hcount
        simp only [List.mem_map] at hcount
        rcases hcount with ⟨other, hother, rfl⟩
        exact htailzero other hother
      simp only [List.map_cons, List.sum_cons, hhead, hsumzero,
        Nat.add_zero, occurrencesOfPairs_length,
        FusionForestComponent.originalBranchCount]
    · have hzero :
          (occurrencesOfPairs head.allPairs).filter
            (fun occurrence => decide (occurrence.vertex ∈ component.vertices)) = [] := by
        apply filter_none
        intro occurrence hoccurrence
        have hheadmem := occurrence_vertex_mem head occurrence hoccurrence
        have hnot : occurrence.vertex ∉ component.vertices := by
          intro hmem
          have hglobal : occurrence.vertex ∈ forestVertices tail := by
            simp only [forestVertices, List.mem_flatMap]
            exact ⟨component, hcomponent, hmem⟩
          exact hdisjoint _ hheadmem _ hglobal rfl
        simp [hnot]
      simpa only [List.map_cons, List.sum_cons, hzero, List.length_nil,
        Nat.zero_add] using ih htail hcomponent

namespace SourceBranchFamily

/-- The source words whose component labels occur in the supplied vertex list.
This preserves repeated residue words at distinct source positions. -/
noncomputable def wordsAt (family : SourceBranchFamily p Vertex)
    (vertices : List Vertex) : List (LabelledBranchWord p Vertex) := by
  classical
  exact family.words.filter fun word => decide (word.vertex ∈ vertices)

omit [NeZero p] in
theorem mem_wordsAt (family : SourceBranchFamily p Vertex)
    (vertices : List Vertex) (word : LabelledBranchWord p Vertex) :
    word ∈ family.wordsAt vertices ↔ word ∈ family.words ∧ word.vertex ∈ vertices := by
  classical
  simp [wordsAt]

omit [NeZero p] in
private theorem filter_word_occurrences [DecidableEq Vertex]
    (vertices : List Vertex) (word : LabelledBranchWord p Vertex) :
    word.occurrences.filter
        (fun occurrence => decide (occurrence.vertex ∈ vertices)) =
      if word.vertex ∈ vertices then word.occurrences else [] := by
  by_cases hmem : word.vertex ∈ vertices
  · rw [if_pos hmem]
    apply filter_all
    intro occurrence hoccurrence
    simp only [LabelledBranchWord.occurrences, List.mem_map] at hoccurrence
    rcases hoccurrence with ⟨residue, _, rfl⟩
    simp [hmem]
  · rw [if_neg hmem]
    apply filter_none
    intro occurrence hoccurrence
    simp only [LabelledBranchWord.occurrences, List.mem_map] at hoccurrence
    rcases hoccurrence with ⟨residue, _, rfl⟩
    simp [hmem]

omit [NeZero p] in
theorem occurrences_filter_eq_wordsAt [DecidableEq Vertex]
    (family : SourceBranchFamily p Vertex) (vertices : List Vertex) :
    (family.occurrences.filter
      (fun occurrence => decide (occurrence.vertex ∈ vertices))) =
      LabelledBranchWord.allOccurrences (family.wordsAt vertices) := by
  classical
  unfold occurrences wordsAt
  induction family.words with
  | nil => rfl
  | cons word words ih =>
    simp only [LabelledBranchWord.allOccurrences, List.flatMap_cons,
      List.filter_append] at ih ⊢
    rw [filter_word_occurrences]
    by_cases hmem : word.vertex ∈ vertices <;> simp [hmem, ih]

end SourceBranchFamily

namespace FusionForestWitness

/-- Exact local occurrence accounting: a fused component contains precisely
the original branches of the source words at its vertices. -/
theorem component_originalBranchCount_eq_source_sum
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ forest.components) :
    component.originalBranchCount =
      ((family.wordsAt component.vertices).map fun word => word.residues.length).sum := by
  classical
  let keep : BranchOccurrence p Vertex → Bool :=
    fun occurrence => decide (occurrence.vertex ∈ component.vertices)
  have hpaired := sourcePairing.coverage.filter keep
  have hpartition :=
    (forest.pair_partition.flatMap_right OppositeOccurrencePair.occurrences).filter keep
  have hcounts := (hpaired.trans hpartition).length_eq
  have hsum := filtered_pair_count_sum keep forest.components
  have hlocal := filtered_component_sum forest.components
    forest.vertices_nodup component hcomponent
  have hsource :
      (family.occurrences.filter keep).length =
        ((family.wordsAt component.vertices).map fun word => word.residues.length).sum := by
    change (family.occurrences.filter
      (fun occurrence => decide (occurrence.vertex ∈ component.vertices))).length = _
    rw [family.occurrences_filter_eq_wordsAt]
    simp [LabelledBranchWord.allOccurrences, LabelledBranchWord.occurrences]
  simp only [List.flatMap_append, List.filter_append,
    List.length_append] at hcounts
  calc
    component.originalBranchCount = _ := hlocal.symm
    _ = _ := hsum.symm
    _ = _ := hcounts.symm
    _ = _ := hsource

theorem component_source_vertices_perm
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ forest.components) :
    ((family.wordsAt component.vertices).map LabelledBranchWord.vertex).Perm
      component.vertices := by
  classical
  have hsourceNodup :
      ((family.wordsAt component.vertices).map LabelledBranchWord.vertex).Nodup := by
    exact List.Nodup.sublist
      (List.Sublist.map _ List.filter_sublist) family.vertices_nodup
  apply (List.perm_ext_iff_of_nodup hsourceNodup
    component.spanningTree.vertices_nodup).2
  intro vertex
  constructor
  · intro hvertex
    simp only [List.mem_map] at hvertex
    rcases hvertex with ⟨word, hword, rfl⟩
    exact ((family.mem_wordsAt component.vertices word).1 hword).2
  · intro hvertex
    have hforest : vertex ∈ forest.vertices := by
      simp only [vertices, forestVertices, List.mem_flatMap]
      exact ⟨component, hcomponent, hvertex⟩
    have hfamily : vertex ∈ family.vertexLabels :=
      (forest.vertices_perm_sourceVertexLabels family sourcePairing).mem_iff.mp hforest
    simp only [SourceBranchFamily.vertexLabels, List.mem_map] at hfamily
    rcases hfamily with ⟨word, hword, hlabel⟩
    simp only [List.mem_map]
    refine ⟨word, ?_, hlabel⟩
    apply (family.mem_wordsAt component.vertices word).2
    exact ⟨hword, hlabel ▸ hvertex⟩

omit [NeZero p] in
private theorem lower_bound_sum_lengths
    (words : List (LabelledBranchWord p Vertex)) (minimum : Nat)
    (hlength : ∀ word ∈ words, minimum ≤ word.residues.length) :
    minimum * words.length ≤ (words.map fun word => word.residues.length).sum := by
  induction words with
  | nil => simp
  | cons word words ih =>
    have hhead := hlength word (by simp)
    have htail := ih (fun other hother => hlength other (by simp [hother]))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ]
    omega

/-- Every per-source branch lower bound descends to the actual source count
of each forest component. No componentwise rank premise is added. -/
theorem component_originalBranchCount_lower_bound
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (minimum : Nat)
    (hlength : ∀ word ∈ family.words, minimum ≤ word.residues.length)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ forest.components) :
    minimum * component.vertices.length ≤ component.originalBranchCount := by
  rw [forest.component_originalBranchCount_eq_source_sum family sourcePairing
    component hcomponent]
  have hcount :=
    (forest.component_source_vertices_perm family sourcePairing component hcomponent).length_eq
  simp only [List.length_map] at hcount
  rw [← hcount]
  apply lower_bound_sum_lengths
  intro word hword
  exact hlength word ((family.mem_wordsAt component.vertices word).1 hword).1

/-- The local nontruncation condition in the original rank-sum theorem follows
already from the existing source-family bound of two markings per source. -/
theorem two_le_component_remainingBranchCount
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ forest.components) :
    2 ≤ component.remainingBranchCount := by
  have hlower := forest.component_originalBranchCount_lower_bound family
    sourcePairing 2 family.two_le_length component hcomponent
  have hbranches := component.originalBranchCount_eq_nodes_add_remaining
  have htree := component.node_count_add_one_eq_vertex_count
  omega

/-- The natural-number rank sum is preserved for every forest certificate over
an actual source family; separate bounds on the fused components are redundant. -/
theorem sourceRankSum_eq_fusedComponentRankSum_of_source_family
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing) :
    family.rankSum = forest.fusedComponentRankSum := by
  apply forest.sourceRankSum_eq_fusedComponentRankSum family sourcePairing
  exact forest.two_le_component_remainingBranchCount family sourcePairing

/-- For cohomological source words (at least three markings each), every
fused component retains at least its source-vertex count plus two markings. -/
theorem component_vertices_add_two_le_remainingBranchCount
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (hthree : ∀ word ∈ family.words, 3 ≤ word.residues.length)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ forest.components) :
    component.vertices.length + 2 ≤ component.remainingBranchCount := by
  have hlower := forest.component_originalBranchCount_lower_bound family
    sourcePairing 3 hthree component hcomponent
  have hbranches := component.originalBranchCount_eq_nodes_add_remaining
  have htree := component.node_count_add_one_eq_vertex_count
  omega

/-- A component has a vertex and its surviving tuple has even length. Thus
three markings at each source force at least four surviving markings. -/
theorem four_le_component_remainingBranchCount
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (hthree : ∀ word ∈ family.words, 3 ≤ word.residues.length)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ forest.components) :
    4 ≤ component.remainingBranchCount := by
  have hlower := forest.component_vertices_add_two_le_remainingBranchCount
    family sourcePairing hthree component hcomponent
  have htree := component.node_count_add_one_eq_vertex_count
  unfold FusionForestComponent.remainingBranchCount at hlower ⊢
  omega

/-- The fused cohomological rank is positive and even under the source-wise
three-marking hypothesis. This is numerical rank data, not a cover construction. -/
theorem component_fused_rank_positive_even
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (hthree : ∀ word ∈ family.words, 3 ≤ word.residues.length)
    (component : FusionForestComponent p Vertex)
    (hcomponent : component ∈ forest.components) :
    0 < component.remainingBranchCount - 2 ∧
      (component.remainingBranchCount - 2) % 2 = 0 := by
  have hlower := forest.four_le_component_remainingBranchCount
    family sourcePairing hthree component hcomponent
  unfold FusionForestComponent.remainingBranchCount at hlower ⊢
  omega

end FusionForestWitness

end

end

end AbelianCoverHodge.Verified
