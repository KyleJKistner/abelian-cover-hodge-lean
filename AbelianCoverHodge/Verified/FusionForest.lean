module

public import AbelianCoverHodge.Verified.AokiFusion

/-!
# Occurrence pairings and fusion forests

This module formalizes the finite combinatorics between Aoki's opposite-pair
witness and the geometric admissible-cover construction.

The main points are:

* an unlabelled `OppositePairingWitness` lifts to a pairing of actual branch
  occurrences, so the source component of every occurrence is retained;
* every paired occurrence gives a concrete graph edge, including loops;
* a spanning tree is certified by an attachment order, rather than only by an
  edge-count equation;
* a forest witness partitions all opposite pairs, with multiplicity, into node
  pairs and surviving smooth pairs;
* the surviving residue tuple is explicitly simple, and exact branch-count
  and integer rank-expression identities follow from the certified forest;
* a source-family wrapper records distinct, nonempty source positions, and a
  separate theorem identifies the actual sums of local natural-number ranks
  only after the required local lower bounds are supplied.

No curve, cover, node, smoothing, Jacobian, or cycle is defined here.  A later
geometric layer must realize the selected cross-edges as inverse-inertia nodes,
prove that the resulting cover has the required connectedness and compact-type
properties, and relate its smoothing to the surviving tuple.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace AbelianCoverHodge.Verified

public section

@[expose] section

/-! ## Branch occurrences with source labels -/

/-- One occurrence of a nonzero branch residue, labelled by the component on
which that marking occurs.  Nonzeroness is supplied by the pairing witness. -/
structure BranchOccurrence (p : Nat) (Vertex : Type) where
  vertex : Vertex
  residue : ZMod p

/-- A branch word together with the vertex/component on which it occurs. -/
structure LabelledBranchWord (p : Nat) (Vertex : Type) where
  vertex : Vertex
  residues : BranchWord p

namespace BranchOccurrence

variable {p : Nat} {Vertex : Type}

/-- Forget source labels from a list of occurrences. -/
def residueWord (occurrences : List (BranchOccurrence p Vertex)) : BranchWord p :=
  occurrences.map BranchOccurrence.residue

end BranchOccurrence

namespace LabelledBranchWord

variable {p : Nat} {Vertex : Type}

/-- The actual labelled occurrences in one component word. -/
def occurrences (word : LabelledBranchWord p Vertex) :
    List (BranchOccurrence p Vertex) :=
  word.residues.map fun residue => ⟨word.vertex, residue⟩

/-- All labelled occurrences in an effective determinant word. -/
def allOccurrences (words : List (LabelledBranchWord p Vertex)) :
    List (BranchOccurrence p Vertex) :=
  words.flatMap fun word => occurrences word

/-- The concatenated residue tuple underlying the labelled component words. -/
def concatenatedResidues (words : List (LabelledBranchWord p Vertex)) :
    BranchWord p :=
  words.flatMap fun word => word.residues

@[simp]
theorem residueWord_occurrences (word : LabelledBranchWord p Vertex) :
    BranchOccurrence.residueWord word.occurrences = word.residues := by
  cases word with
  | mk vertex residues =>
      induction residues with
      | nil => rfl
      | cons residue residues ih =>
          change residue ::
              BranchOccurrence.residueWord
                (residues.map fun residue => ⟨vertex, residue⟩) =
            residue :: residues
          exact congrArg (List.cons residue) ih

@[simp]
theorem residueWord_allOccurrences
    (words : List (LabelledBranchWord p Vertex)) :
    BranchOccurrence.residueWord (allOccurrences words) =
      concatenatedResidues words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      rw [allOccurrences, concatenatedResidues,
        List.flatMap_cons, List.flatMap_cons]
      rw [BranchOccurrence.residueWord, List.map_append,
        ← BranchOccurrence.residueWord,
        residueWord_occurrences]
      exact congrArg (List.append word.residues) ih

end LabelledBranchWord

/-! ## Source families with distinct component positions -/

/-- Source branch words with one distinct label for each source position.

The lower bound rules out invisible empty source words and makes
`word.residues.length - 2` an ordinary, nontruncated local rank.  Repeated
residue words are allowed: only their source labels must be distinct. -/
structure SourceBranchFamily (p : Nat) (Vertex : Type) where
  words : List (LabelledBranchWord p Vertex)
  vertices_nodup : (words.map LabelledBranchWord.vertex).Nodup
  two_le_length : ∀ word ∈ words, 2 ≤ word.residues.length

namespace SourceBranchFamily

variable {p : Nat} {Vertex : Type}

/-- The distinct source-position labels. -/
def vertexLabels (family : SourceBranchFamily p Vertex) : List Vertex :=
  family.words.map LabelledBranchWord.vertex

/-- All occurrences, retaining their source-position labels. -/
def occurrences (family : SourceBranchFamily p Vertex) :
    List (BranchOccurrence p Vertex) :=
  LabelledBranchWord.allOccurrences family.words

/-- Number of source positions. -/
def vertexCount (family : SourceBranchFamily p Vertex) : Nat :=
  family.words.length

/-- Total number of source branch occurrences. -/
def branchCount (family : SourceBranchFamily p Vertex) : Nat :=
  family.occurrences.length

/-- The actual sum of the local natural-number ranks `s(v) - 2`. -/
def rankSum (family : SourceBranchFamily p Vertex) : Nat :=
  (family.words.map fun word => word.residues.length - 2).sum

/-- The occurrence count is the sum of the individual word lengths. -/
theorem branchCount_eq_sum_lengths (family : SourceBranchFamily p Vertex) :
    family.branchCount =
      (family.words.map fun word => word.residues.length).sum := by
  simp [branchCount, occurrences, LabelledBranchWord.allOccurrences,
    LabelledBranchWord.occurrences]

/-- A source label occurs in the family exactly when an occurrence carrying
that label occurs.  The local length bound is essential in the
label-to-occurrence direction: an empty labelled word would otherwise be
invisible. -/
theorem mem_vertexLabels_iff_exists_occurrence
    (family : SourceBranchFamily p Vertex) (vertex : Vertex) :
    vertex ∈ family.vertexLabels ↔
      ∃ occurrence ∈ family.occurrences, occurrence.vertex = vertex := by
  constructor
  · intro hvertex
    simp only [vertexLabels, List.mem_map] at hvertex
    rcases hvertex with ⟨word, hword, hwordVertex⟩
    have hlength := family.two_le_length word hword
    cases hresidues : word.residues with
    | nil => simp [hresidues] at hlength
    | cons residue residues =>
        let occurrence : BranchOccurrence p Vertex :=
          ⟨word.vertex, residue⟩
        refine ⟨occurrence, ?_, hwordVertex⟩
        simp only [occurrences, LabelledBranchWord.allOccurrences,
          List.mem_flatMap]
        refine ⟨word, hword, ?_⟩
        simp [LabelledBranchWord.occurrences, hresidues, occurrence]
  · rintro ⟨occurrence, hoccurrence, hlabel⟩
    simp only [occurrences, LabelledBranchWord.allOccurrences,
      List.mem_flatMap] at hoccurrence
    rcases hoccurrence with ⟨word, hword, hoccurrence⟩
    simp only [LabelledBranchWord.occurrences, List.mem_map] at hoccurrence
    rcases hoccurrence with ⟨residue, hresidue, hoccurrenceEq⟩
    have hwordVertex : word.vertex = occurrence.vertex :=
      congrArg BranchOccurrence.vertex hoccurrenceEq
    simp only [vertexLabels, List.mem_map]
    exact ⟨word, hword, hwordVertex.trans hlabel⟩

private theorem rankSum_add_twice_length_eq_sum_lengths_aux
    (words : List (LabelledBranchWord p Vertex))
    (two_le_length : ∀ word ∈ words, 2 ≤ word.residues.length) :
    (words.map fun word => word.residues.length - 2).sum +
        2 * words.length =
      (words.map fun word => word.residues.length).sum := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      have hword : 2 ≤ word.residues.length :=
        two_le_length word (by simp)
      have htail : ∀ tail ∈ words, 2 ≤ tail.residues.length := by
        intro tail htail
        exact two_le_length tail (by simp [htail])
      have ih' := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
      omega

/-- Exact additive form of the actual source-rank sum. -/
theorem rankSum_add_twice_vertexCount_eq_branchCount
    (family : SourceBranchFamily p Vertex) :
    family.rankSum + 2 * family.vertexCount = family.branchCount := by
  rw [family.branchCount_eq_sum_lengths]
  exact rankSum_add_twice_length_eq_sum_lengths_aux family.words
    family.two_le_length

/-- Subtractive form of the actual source-rank sum. -/
theorem rankSum_eq_branchCount_sub_twice_vertexCount
    (family : SourceBranchFamily p Vertex) :
    family.rankSum = family.branchCount - 2 * family.vertexCount := by
  have h := family.rankSum_add_twice_vertexCount_eq_branchCount
  omega

end SourceBranchFamily

/-! ## Lifting a permutation through occurrence labels -/

/-- Any permutation of the image of a list can be lifted to a permutation of
the list itself.  No injectivity of the map is needed: repeated residues remain
distinct occurrences before labels are forgotten. -/
theorem exists_perm_of_map_perm
    {α β : Type} (f : α → β) {source target : List β}
    (permutation : source.Perm target) (items : List α)
    (mapped : items.map f = source) :
    ∃ reordered : List α,
      items.Perm reordered ∧ reordered.map f = target := by
  induction permutation generalizing items with
  | nil =>
      cases items with
      | nil => exact ⟨[], .nil, rfl⟩
      | cons item items => simp at mapped
  | cons value permutation ih =>
      cases items with
      | nil => simp at mapped
      | cons item items =>
          simp only [List.map_cons, List.cons.injEq] at mapped
          rcases mapped with ⟨hvalue, htail⟩
          obtain ⟨reordered, hperm, hmap⟩ := ih items htail
          refine ⟨item :: reordered, hperm.cons item, ?_⟩
          simp [hvalue, hmap]
  | swap first second tail =>
      cases items with
      | nil => simp at mapped
      | cons item₁ items =>
          cases items with
          | nil => simp at mapped
          | cons item₂ items =>
              simp only [List.map_cons, List.cons.injEq] at mapped
              rcases mapped with ⟨hfirst, hsecond, htail⟩
              refine ⟨item₂ :: item₁ :: items, .swap item₂ item₁ items, ?_⟩
              simp [hfirst, hsecond, htail]
  | trans first second ihFirst ihSecond =>
      obtain ⟨middle, hFirstPerm, hMiddleMap⟩ :=
        ihFirst items mapped
      obtain ⟨reordered, hSecondPerm, hReorderedMap⟩ :=
        ihSecond middle hMiddleMap
      exact ⟨reordered, hFirstPerm.trans hSecondPerm, hReorderedMap⟩

/-! ## Concrete opposite-occurrence pairs -/

/-- A chosen opposite pair of actual branch occurrences.  Its endpoints are
vertices of the pairing multigraph; equal endpoints give a loop. -/
structure OppositeOccurrencePair (p : Nat) [NeZero p] (Vertex : Type) where
  leftVertex : Vertex
  rightVertex : Vertex
  representative : ZMod p
  representative_nonzero : representative ≠ zzero p

namespace OppositeOccurrencePair

variable {p : Nat} [NeZero p] {Vertex : Type}

/-- The two labelled occurrences covered by one opposite pair. -/
def occurrences (pair : OppositeOccurrencePair p Vertex) :
    List (BranchOccurrence p Vertex) :=
  [⟨pair.leftVertex, pair.representative⟩,
   ⟨pair.rightVertex, zneg pair.representative⟩]

/-- Its two residues, in the chosen opposite order. -/
def residues (pair : OppositeOccurrencePair p Vertex) : BranchWord p :=
  [pair.representative, zneg pair.representative]

/-- The two endpoints joined by the underlying undirected edge. -/
def Joins (pair : OppositeOccurrencePair p Vertex) (left right : Vertex) : Prop :=
  (pair.leftVertex = left ∧ pair.rightVertex = right) ∨
    (pair.leftVertex = right ∧ pair.rightVertex = left)

/-- A graph edge is cross-vertex rather than a loop. -/
def IsCrossEdge (pair : OppositeOccurrencePair p Vertex) : Prop :=
  pair.leftVertex ≠ pair.rightVertex

@[simp]
theorem residueWord_occurrences (pair : OppositeOccurrencePair p Vertex) :
    BranchOccurrence.residueWord pair.occurrences = pair.residues := by
  rfl

theorem left_residue_nonzero (pair : OppositeOccurrencePair p Vertex) :
    pair.representative ≠ zzero p :=
  pair.representative_nonzero

theorem right_residue_nonzero (pair : OppositeOccurrencePair p Vertex) :
    zneg pair.representative ≠ zzero p :=
  zneg_ne_zero pair.representative pair.representative_nonzero

theorem joins_comm (pair : OppositeOccurrencePair p Vertex)
    {left right : Vertex} :
    pair.Joins left right ↔ pair.Joins right left := by
  constructor <;> intro h <;> rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

end OppositeOccurrencePair

/-- Flatten a list of opposite pairs to the labelled occurrences they cover. -/
def occurrencesOfPairs {p : Nat} [NeZero p] {Vertex : Type}
    (pairs : List (OppositeOccurrencePair p Vertex)) :
    List (BranchOccurrence p Vertex) :=
  pairs.flatMap fun pair => pair.occurrences

/-- Flatten a list of opposite pairs to its simple residue tuple. -/
def residuesOfPairs {p : Nat} [NeZero p] {Vertex : Type}
    (pairs : List (OppositeOccurrencePair p Vertex)) : BranchWord p :=
  pairs.flatMap fun pair => pair.residues

@[simp]
theorem occurrencesOfPairs_append {p : Nat} [NeZero p] {Vertex : Type}
    (left right : List (OppositeOccurrencePair p Vertex)) :
    occurrencesOfPairs (left ++ right) =
      occurrencesOfPairs left ++ occurrencesOfPairs right := by
  simp [occurrencesOfPairs]

@[simp]
theorem residuesOfPairs_append {p : Nat} [NeZero p] {Vertex : Type}
    (left right : List (OppositeOccurrencePair p Vertex)) :
    residuesOfPairs (left ++ right) =
      residuesOfPairs left ++ residuesOfPairs right := by
  simp [residuesOfPairs]

@[simp]
theorem residueWord_occurrencesOfPairs
    {p : Nat} [NeZero p] {Vertex : Type}
    (pairs : List (OppositeOccurrencePair p Vertex)) :
    BranchOccurrence.residueWord (occurrencesOfPairs pairs) =
      residuesOfPairs pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rw [occurrencesOfPairs, residuesOfPairs,
        List.flatMap_cons, List.flatMap_cons]
      rw [BranchOccurrence.residueWord, List.map_append,
        ← BranchOccurrence.residueWord,
        OppositeOccurrencePair.residueWord_occurrences]
      exact congrArg (List.append pair.residues) ih

@[simp]
theorem residuesOfPairs_eq_pairResidues
    {p : Nat} [NeZero p] {Vertex : Type}
    (pairs : List (OppositeOccurrencePair p Vertex)) :
    residuesOfPairs pairs =
      pairResidues (pairs.map OppositeOccurrencePair.representative) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      change [pair.representative, zneg pair.representative] ++
          residuesOfPairs pairs =
        pair.representative :: zneg pair.representative ::
          pairResidues (pairs.map OppositeOccurrencePair.representative)
      rw [ih]
      rfl

@[simp]
theorem occurrencesOfPairs_length
    {p : Nat} [NeZero p] {Vertex : Type}
    (pairs : List (OppositeOccurrencePair p Vertex)) :
    (occurrencesOfPairs pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rw [occurrencesOfPairs, List.flatMap_cons, List.length_append]
      change 2 + (occurrencesOfPairs pairs).length =
        2 * (pairs.length + 1)
      rw [ih]
      omega

@[simp]
theorem residuesOfPairs_length
    {p : Nat} [NeZero p] {Vertex : Type}
    (pairs : List (OppositeOccurrencePair p Vertex)) :
    (residuesOfPairs pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rw [residuesOfPairs, List.flatMap_cons, List.length_append]
      change 2 + (residuesOfPairs pairs).length =
        2 * (pairs.length + 1)
      rw [ih]
      omega

/-- A multiplicity-exact pairing of a list of actual branch occurrences. -/
structure OccurrencePairingWitness {p : Nat} [NeZero p] {Vertex : Type}
    (occurrences : List (BranchOccurrence p Vertex)) where
  pairs : List (OppositeOccurrencePair p Vertex)
  coverage : occurrences.Perm (occurrencesOfPairs pairs)

namespace OccurrencePairingWitness

variable {p : Nat} [NeZero p] {Vertex : Type}
variable {occurrences : List (BranchOccurrence p Vertex)}

/-- Forgetting source labels recovers an ordinary Aoki simplicity witness. -/
def toOppositePairingWitness
    (witness : OccurrencePairingWitness occurrences) :
    OppositePairingWitness (BranchOccurrence.residueWord occurrences) where
  representatives :=
    witness.pairs.map OppositeOccurrencePair.representative
  representatives_nonzero := by
    intro residue hresidue
    simp only [List.mem_map] at hresidue
    rcases hresidue with ⟨pair, _, rfl⟩
    exact pair.representative_nonzero
  perm := by
    have hmap := witness.coverage.map BranchOccurrence.residue
    change (BranchOccurrence.residueWord occurrences).Perm
      (BranchOccurrence.residueWord (occurrencesOfPairs witness.pairs)) at hmap
    rw [residueWord_occurrencesOfPairs,
      residuesOfPairs_eq_pairResidues] at hmap
    exact hmap

/-- Exact number of original occurrences covered by the chosen pairs. -/
theorem occurrence_count_eq_twice_pair_count
    (witness : OccurrencePairingWitness occurrences) :
    occurrences.length = 2 * witness.pairs.length := by
  rw [witness.coverage.length_eq, occurrencesOfPairs_length]

end OccurrencePairingWitness

/-! ## Constructing labelled pairs from Aoki's witness -/

/-- An aligned simple residue word can be grouped into actual opposite pairs
without losing the source label of either occurrence. -/
theorem exists_occurrencePairs_of_aligned
    {p : Nat} [NeZero p] {Vertex : Type}
    (representatives : List (ZMod p))
    (representatives_nonzero :
      ∀ x ∈ representatives, x ≠ zzero p)
    (occurrences : List (BranchOccurrence p Vertex))
    (aligned : BranchOccurrence.residueWord occurrences =
      pairResidues representatives) :
    ∃ pairs : List (OppositeOccurrencePair p Vertex),
      occurrences = occurrencesOfPairs pairs ∧
      pairs.map OppositeOccurrencePair.representative = representatives := by
  induction representatives generalizing occurrences with
  | nil =>
      cases occurrences with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons occurrence occurrences =>
          simp [BranchOccurrence.residueWord, pairResidues] at aligned
  | cons representative representatives ih =>
      cases occurrences with
      | nil =>
          simp [BranchOccurrence.residueWord, pairResidues] at aligned
      | cons left occurrences =>
          cases occurrences with
          | nil =>
              simp [BranchOccurrence.residueWord, pairResidues] at aligned
          | cons right occurrences =>
              simp only [BranchOccurrence.residueWord, List.map_cons,
                pairResidues, List.cons.injEq] at aligned
              rcases aligned with ⟨hleft, hright, htail⟩
              have hrepresentative : representative ≠ zzero p :=
                representatives_nonzero representative (by simp)
              have hrepresentatives :
                  ∀ x ∈ representatives, x ≠ zzero p := by
                intro x hx
                exact representatives_nonzero x (by simp [hx])
              obtain ⟨pairs, hpairs, hreps⟩ :=
                ih hrepresentatives occurrences htail
              let pair : OppositeOccurrencePair p Vertex :=
                { leftVertex := left.vertex
                  rightVertex := right.vertex
                  representative := representative
                  representative_nonzero := hrepresentative }
              refine ⟨pair :: pairs, ?_, ?_⟩
              · cases left with
                | mk leftVertex leftResidue =>
                    cases right with
                    | mk rightVertex rightResidue =>
                        change leftResidue = representative at hleft
                        change rightResidue = zneg representative at hright
                        subst leftResidue
                        subst rightResidue
                        simp [occurrencesOfPairs,
                          OppositeOccurrencePair.occurrences, pair, hpairs]
              · simp [pair, hreps]

/-- Aoki's unlabelled opposite-pair permutation lifts to a concrete pairing of
the original labelled occurrences. -/
theorem OppositePairingWitness.exists_occurrencePairing
    {p : Nat} [NeZero p] {Vertex : Type}
    {residues : BranchWord p}
    (aoki : OppositePairingWitness residues)
    (occurrences : List (BranchOccurrence p Vertex))
    (hresidues : BranchOccurrence.residueWord occurrences = residues) :
    ∃ pairing : OccurrencePairingWitness occurrences,
      pairing.pairs.map OppositeOccurrencePair.representative =
        aoki.representatives := by
  obtain ⟨reordered, hreorder, haligned⟩ :=
    exists_perm_of_map_perm BranchOccurrence.residue aoki.perm
      occurrences hresidues
  obtain ⟨pairs, hpairs, hreps⟩ :=
    exists_occurrencePairs_of_aligned aoki.representatives
      aoki.representatives_nonzero reordered haligned
  refine ⟨{ pairs := pairs, coverage := ?_ }, hreps⟩
  exact hreorder.trans (List.Perm.of_eq hpairs)

/-- Component-labelled form of the preceding lifting theorem. -/
theorem OppositePairingWitness.exists_componentOccurrencePairing
    {p : Nat} [NeZero p] {Vertex : Type}
    (words : List (LabelledBranchWord p Vertex))
    (aoki : OppositePairingWitness
      (LabelledBranchWord.concatenatedResidues words)) :
    ∃ pairing : OccurrencePairingWitness
        (LabelledBranchWord.allOccurrences words),
      pairing.pairs.map OppositeOccurrencePair.representative =
        aoki.representatives := by
  apply aoki.exists_occurrencePairing
    (LabelledBranchWord.allOccurrences words)
  exact LabelledBranchWord.residueWord_allOccurrences words

/-! ## Attachment-order certificates for spanning trees -/

/-- A concrete spanning-tree certificate.  A singleton root is a tree.  Each
subsequent step attaches one genuinely new vertex to an old vertex by one of
the chosen opposite-pair edges. -/
inductive IsAttachmentSpanningTree
    {p : Nat} [NeZero p] {Vertex : Type} :
    List Vertex → List (OppositeOccurrencePair p Vertex) → Prop
  | root (vertex : Vertex) :
      IsAttachmentSpanningTree [vertex] []
  | attach
      {vertices : List Vertex}
      {edges : List (OppositeOccurrencePair p Vertex)}
      (tree : IsAttachmentSpanningTree vertices edges)
      (edge : OppositeOccurrencePair p Vertex)
      (newVertex oldVertex : Vertex)
      (old_mem : oldVertex ∈ vertices)
      (new_not_mem : newVertex ∉ vertices)
      (joins : edge.Joins newVertex oldVertex) :
      IsAttachmentSpanningTree
        (newVertex :: vertices) (edge :: edges)

namespace IsAttachmentSpanningTree

variable {p : Nat} [NeZero p] {Vertex : Type}
variable {vertices : List Vertex}
variable {edges : List (OppositeOccurrencePair p Vertex)}

/-- A certified tree has a nonempty vertex list. -/
theorem vertices_nonempty
    (tree : IsAttachmentSpanningTree vertices edges) :
    vertices ≠ [] := by
  cases tree <;> simp

/-- The attachment order never repeats a vertex. -/
theorem vertices_nodup
    (tree : IsAttachmentSpanningTree vertices edges) :
    vertices.Nodup := by
  induction tree with
  | root vertex => simp
  | attach tree edge newVertex oldVertex old_mem new_not_mem joins ih =>
      exact List.nodup_cons.mpr ⟨new_not_mem, ih⟩

/-- Exact tree identity, stated without truncated subtraction. -/
theorem edge_count_add_one_eq_vertex_count
    (tree : IsAttachmentSpanningTree vertices edges) :
    edges.length + 1 = vertices.length := by
  induction tree with
  | root vertex => rfl
  | attach tree edge newVertex oldVertex old_mem new_not_mem joins ih =>
      simp only [List.length_cons]
      omega

/-- Conventional `|E| = |V| - 1` form of the tree identity. -/
theorem edge_count_eq_vertex_count_sub_one
    (tree : IsAttachmentSpanningTree vertices edges) :
    edges.length = vertices.length - 1 := by
  have h := tree.edge_count_add_one_eq_vertex_count
  omega

/-- Every selected tree edge is genuinely cross-vertex. -/
theorem edges_cross
    (tree : IsAttachmentSpanningTree vertices edges) :
    ∀ edge ∈ edges, edge.IsCrossEdge := by
  induction tree with
  | root vertex => simp
  | attach tree edge newVertex oldVertex old_mem new_not_mem joins ih =>
      intro selected hselected
      simp only [List.mem_cons] at hselected
      rcases hselected with rfl | htail
      · intro hequal
        rcases joins with h | h
        · apply new_not_mem
          simpa [← h.1, ← h.2, hequal] using old_mem
        · apply new_not_mem
          simpa [← h.2, ← h.1, hequal] using old_mem
      · exact ih selected htail

/-- Both endpoints of every tree edge occur in its certified vertex list. -/
theorem edge_endpoints_mem
    (tree : IsAttachmentSpanningTree vertices edges) :
    ∀ edge ∈ edges,
      edge.leftVertex ∈ vertices ∧ edge.rightVertex ∈ vertices := by
  induction tree with
  | root vertex => simp
  | attach tree edge newVertex oldVertex old_mem new_not_mem joins ih =>
      intro selected hselected
      simp only [List.mem_cons] at hselected
      rcases hselected with rfl | htail
      · rcases joins with h | h
        · constructor
          · simp [h.1]
          · simp [h.2, old_mem]
        · constructor
          · simp [h.1, old_mem]
          · simp [h.2]
      · rcases ih selected htail with ⟨hleft, hright⟩
        exact ⟨by simp [hleft], by simp [hright]⟩

end IsAttachmentSpanningTree

/-! ## Forest components and exact global partition -/

/-- One connected pairing-graph component.  The node pairs carry an actual
attachment-tree certificate.  Every unused pair stays inside this component
and will survive as two smooth branch residues. -/
structure FusionForestComponent (p : Nat) [NeZero p] (Vertex : Type) where
  vertices : List Vertex
  nodePairs : List (OppositeOccurrencePair p Vertex)
  smoothPairs : List (OppositeOccurrencePair p Vertex)
  spanningTree : IsAttachmentSpanningTree vertices nodePairs
  smooth_endpoints_mem : ∀ pair ∈ smoothPairs,
    pair.leftVertex ∈ vertices ∧ pair.rightVertex ∈ vertices

namespace FusionForestComponent

variable {p : Nat} [NeZero p] {Vertex : Type}

/-- All original pairs assigned to this graph component. -/
def allPairs (component : FusionForestComponent p Vertex) :
    List (OppositeOccurrencePair p Vertex) :=
  component.nodePairs ++ component.smoothPairs

/-- Residues which remain marked after the tree pairs are used as nodes. -/
def remainingResidues (component : FusionForestComponent p Vertex) :
    BranchWord p :=
  residuesOfPairs component.smoothPairs

/-- Original branch count of this graph component. -/
def originalBranchCount (component : FusionForestComponent p Vertex) : Nat :=
  2 * component.allPairs.length

/-- Remaining smooth branch count of this graph component. -/
def remainingBranchCount (component : FusionForestComponent p Vertex) : Nat :=
  2 * component.smoothPairs.length

/-- The aggregate integer expression `S - 2V` attached to this graph
component.  The forest data does not assign a separate branch count to each
vertex, so this is deliberately not called a sum of local ranks. -/
def originalRankExpression (component : FusionForestComponent p Vertex) : Int :=
  (component.originalBranchCount : Int) -
    2 * (component.vertices.length : Int)

/-- The integer expression `S' - 2` for the single fused component. -/
def fusedRankExpression (component : FusionForestComponent p Vertex) : Int :=
  (component.remainingBranchCount : Int) - 2

/-- The surviving tuple is literally a list of nonzero opposite pairs. -/
def remainingOppositePairingWitness
    (component : FusionForestComponent p Vertex) :
    OppositePairingWitness component.remainingResidues where
  representatives :=
    component.smoothPairs.map OppositeOccurrencePair.representative
  representatives_nonzero := by
    intro residue hresidue
    simp only [List.mem_map] at hresidue
    rcases hresidue with ⟨pair, _, rfl⟩
    exact pair.representative_nonzero
  perm := by
    rw [remainingResidues, residuesOfPairs_eq_pairResidues]

/-- Every component's selected pairs number one fewer than its vertices. -/
theorem node_count_add_one_eq_vertex_count
    (component : FusionForestComponent p Vertex) :
    component.nodePairs.length + 1 = component.vertices.length :=
  component.spanningTree.edge_count_add_one_eq_vertex_count

/-- Every selected pair is cross-vertex, as required for a tree gluing. -/
theorem nodePairs_cross (component : FusionForestComponent p Vertex) :
    ∀ pair ∈ component.nodePairs, pair.IsCrossEdge :=
  component.spanningTree.edges_cross

/-- Both selected and surviving pair edges stay in this component. -/
theorem allPair_endpoints_mem (component : FusionForestComponent p Vertex) :
    ∀ pair ∈ component.allPairs,
      pair.leftVertex ∈ component.vertices ∧
      pair.rightVertex ∈ component.vertices := by
  intro pair hpair
  simp only [allPairs, List.mem_append] at hpair
  rcases hpair with hnode | hsmooth
  · exact component.spanningTree.edge_endpoints_mem pair hnode
  · exact component.smooth_endpoints_mem pair hsmooth

/-- Removing selected tree pairs gives an additive branch-count identity. -/
theorem originalBranchCount_eq_nodes_add_remaining
    (component : FusionForestComponent p Vertex) :
    component.originalBranchCount =
      2 * component.nodePairs.length + component.remainingBranchCount := by
  simp [originalBranchCount, remainingBranchCount, allPairs]
  omega

/-- Subtractive form of the same branch-count identity. -/
theorem remainingBranchCount_eq_original_sub_nodes
    (component : FusionForestComponent p Vertex) :
    component.remainingBranchCount =
      component.originalBranchCount - 2 * component.nodePairs.length := by
  have h := component.originalBranchCount_eq_nodes_add_remaining
  omega

/-- The numerical remaining branch count is the actual length of the
surviving residue tuple. -/
theorem remainingResidues_length
    (component : FusionForestComponent p Vertex) :
    component.remainingResidues.length = component.remainingBranchCount := by
  exact residuesOfPairs_length component.smoothPairs

/-- Componentwise form of the manuscript's fused-branch formula. -/
theorem remainingBranchCount_eq_tree_formula
    (component : FusionForestComponent p Vertex) :
    component.remainingBranchCount =
      component.originalBranchCount -
        2 * (component.vertices.length - 1) := by
  rw [component.remainingBranchCount_eq_original_sub_nodes,
    component.spanningTree.edge_count_eq_vertex_count_sub_one]

/-- Tree-pair deletion preserves the component's aggregate integer rank
expression.  This statement has no hidden natural-number truncation. -/
theorem rankExpression_preserved
    (component : FusionForestComponent p Vertex) :
    component.originalRankExpression = component.fusedRankExpression := by
  have hbranches := component.originalBranchCount_eq_nodes_add_remaining
  have htree := component.node_count_add_one_eq_vertex_count
  have hbranchesInt :
      (component.originalBranchCount : Int) =
        2 * (component.nodePairs.length : Int) +
          (component.remainingBranchCount : Int) := by
    exact_mod_cast hbranches
  have htreeInt :
      (component.nodePairs.length : Int) + 1 =
        (component.vertices.length : Int) := by
    exact_mod_cast htree
  unfold originalRankExpression fusedRankExpression
  omega

end FusionForestComponent

/-- Concatenate the node-pair lists of all forest components. -/
def forestNodePairs {p : Nat} [NeZero p] {Vertex : Type}
    (components : List (FusionForestComponent p Vertex)) :
    List (OppositeOccurrencePair p Vertex) :=
  components.flatMap FusionForestComponent.nodePairs

/-- Concatenate the surviving pair lists of all forest components. -/
def forestSmoothPairs {p : Nat} [NeZero p] {Vertex : Type}
    (components : List (FusionForestComponent p Vertex)) :
    List (OppositeOccurrencePair p Vertex) :=
  components.flatMap FusionForestComponent.smoothPairs

/-- Concatenate the certified vertex lists of all forest components. -/
def forestVertices {p : Nat} [NeZero p] {Vertex : Type}
    (components : List (FusionForestComponent p Vertex)) : List Vertex :=
  components.flatMap FusionForestComponent.vertices

/-- A complete forest choice for a concrete occurrence pairing.  The pair
partition is a `List.Perm`, so repeated equal residues and repeated equal graph
edges are accounted for with their full multiplicity.  Global vertex nodup
ensures distinct tree components do not share a vertex. -/
structure FusionForestWitness
    {p : Nat} [NeZero p] {Vertex : Type}
    {occurrences : List (BranchOccurrence p Vertex)}
    (pairing : OccurrencePairingWitness occurrences) where
  components : List (FusionForestComponent p Vertex)
  pair_partition : pairing.pairs.Perm
    (forestNodePairs components ++ forestSmoothPairs components)
  vertices_nodup : (forestVertices components).Nodup
  vertex_coverage : ∀ vertex,
    vertex ∈ forestVertices components ↔
      ∃ occurrence ∈ occurrences, occurrence.vertex = vertex

namespace FusionForestWitness

variable {p : Nat} [NeZero p] {Vertex : Type}
variable {occurrences : List (BranchOccurrence p Vertex)}
variable {pairing : OccurrencePairingWitness occurrences}

/-- All selected tree pairs. -/
def nodePairs (forest : FusionForestWitness pairing) :
    List (OppositeOccurrencePair p Vertex) :=
  forestNodePairs forest.components

/-- All pairs which survive as smooth marked branches. -/
def smoothPairs (forest : FusionForestWitness pairing) :
    List (OppositeOccurrencePair p Vertex) :=
  forestSmoothPairs forest.components

/-- The vertices of the original pairing multigraph. -/
def vertices (forest : FusionForestWitness pairing) : List Vertex :=
  forestVertices forest.components

/-- The certified vertex list is exactly the set of component labels occurring
in the original branch word.  This excludes irrelevant singleton components
from silently changing the rank count. -/
theorem mem_vertices_iff_occurs
    (forest : FusionForestWitness pairing) (vertex : Vertex) :
    vertex ∈ forest.vertices ↔
      ∃ occurrence ∈ occurrences, occurrence.vertex = vertex :=
  forest.vertex_coverage vertex

/-- Number of graph components, hence number of fused residue tuples. -/
def componentCount (forest : FusionForestWitness pairing) : Nat :=
  forest.components.length

/-- Number of original component vertices. -/
def vertexCount (forest : FusionForestWitness pairing) : Nat :=
  forest.vertices.length

/-- Original branch count, retaining the actual occurrence list as source. -/
def originalBranchCount (_forest : FusionForestWitness pairing) : Nat :=
  occurrences.length

/-- Total branch count after every selected node pair is removed. -/
def remainingBranchCount (forest : FusionForestWitness pairing) : Nat :=
  2 * forest.smoothPairs.length

/-- The full surviving residue tuple. -/
def remainingResidues (forest : FusionForestWitness pairing) : BranchWord p :=
  residuesOfPairs forest.smoothPairs

/-- The residues consumed by selected tree edges. -/
def nodeResidues (forest : FusionForestWitness pairing) : BranchWord p :=
  residuesOfPairs forest.nodePairs

/-- The aggregate integer expression `S - 2V` for the original forest.
Without source-word data this is not asserted to be a sum of local ranks. -/
def originalRankExpression (forest : FusionForestWitness pairing) : Int :=
  (forest.originalBranchCount : Int) -
    2 * (forest.vertexCount : Int)

/-- The aggregate integer expression `S' - 2C` for the fused forest. -/
def fusedRankExpression (forest : FusionForestWitness pairing) : Int :=
  (forest.remainingBranchCount : Int) -
    2 * (forest.componentCount : Int)

/-- The actual sum of the componentwise natural-number expressions
`remainingBranchCount - 2`.  Its comparison with the aggregate expression is
made only under a lower bound for every individual component. -/
def fusedComponentRankSum (forest : FusionForestWitness pairing) : Nat :=
  (forest.components.map fun component =>
    component.remainingBranchCount - 2).sum

/-- Every original opposite pair occurs exactly once in either the selected or
the surviving list. -/
theorem pair_count_eq_nodes_add_smooth
    (forest : FusionForestWitness pairing) :
    pairing.pairs.length =
      forest.nodePairs.length + forest.smoothPairs.length := by
  have h := forest.pair_partition.length_eq
  simpa [nodePairs, smoothPairs] using h

/-- Exact forest identity `|E_forest| + components = |vertices|`, obtained
from actual attachment trees component by component. -/
theorem node_count_add_component_count_eq_vertex_count
    (forest : FusionForestWitness pairing) :
    forest.nodePairs.length + forest.componentCount = forest.vertexCount := by
  unfold nodePairs componentCount vertexCount vertices
  induction forest.components with
  | nil => rfl
  | cons component components ih =>
      rw [forestNodePairs, forestVertices,
        List.flatMap_cons, List.flatMap_cons,
        List.length_append, List.length_append, List.length_cons]
      have hcomponent := component.node_count_add_one_eq_vertex_count
      have hvertices : 0 < component.vertices.length := by
        cases hverticesEq : component.vertices with
        | nil => exact
            (component.spanningTree.vertices_nonempty hverticesEq).elim
        | cons vertex vertices => simp
      have ih' :
          (forestNodePairs components).length + components.length =
            (forestVertices components).length := ih
      calc
        component.nodePairs.length +
              (forestNodePairs components).length +
              (components.length + 1) =
            (component.nodePairs.length + 1) +
              ((forestNodePairs components).length +
                components.length) := by omega
        _ = component.vertices.length +
              (forestVertices components).length := by
                rw [hcomponent, ih']

/-- Every selected node pair is a cross-vertex edge. -/
theorem nodePairs_cross (forest : FusionForestWitness pairing) :
    ∀ pair ∈ forest.nodePairs, pair.IsCrossEdge := by
  intro pair hpair
  unfold nodePairs forestNodePairs at hpair
  simp only [List.mem_flatMap] at hpair
  rcases hpair with ⟨component, hcomponent, hpairs⟩
  exact component.nodePairs_cross pair hpairs

/-- Forgetting occurrence labels, the original tuple is a permutation of the
node residues followed by the surviving residues.  Thus removing a tree pair
removes exactly its two opposite occurrences and nothing else. -/
theorem residue_partition (forest : FusionForestWitness pairing) :
    (BranchOccurrence.residueWord occurrences).Perm
      (forest.nodeResidues ++ forest.remainingResidues) := by
  have hpairs := forest.pair_partition.flatMap_right
    OppositeOccurrencePair.occurrences
  have hoccurrences : occurrences.Perm
      (occurrencesOfPairs forest.nodePairs ++
        occurrencesOfPairs forest.smoothPairs) := by
    refine pairing.coverage.trans ?_
    simpa [occurrencesOfPairs, nodePairs, smoothPairs] using hpairs
  have hresidues := hoccurrences.map BranchOccurrence.residue
  change (BranchOccurrence.residueWord occurrences).Perm
    (List.map BranchOccurrence.residue
      (occurrencesOfPairs forest.nodePairs ++
        occurrencesOfPairs forest.smoothPairs)) at hresidues
  rw [List.map_append] at hresidues
  change (BranchOccurrence.residueWord occurrences).Perm
    (BranchOccurrence.residueWord
        (occurrencesOfPairs forest.nodePairs) ++
      BranchOccurrence.residueWord
        (occurrencesOfPairs forest.smoothPairs)) at hresidues
  rw [residueWord_occurrencesOfPairs,
    residueWord_occurrencesOfPairs] at hresidues
  exact hresidues

/-- The global surviving tuple remains simple. -/
def remainingOppositePairingWitness
    (forest : FusionForestWitness pairing) :
    OppositePairingWitness forest.remainingResidues where
  representatives :=
    forest.smoothPairs.map OppositeOccurrencePair.representative
  representatives_nonzero := by
    intro residue hresidue
    simp only [List.mem_map] at hresidue
    rcases hresidue with ⟨pair, _, rfl⟩
    exact pair.representative_nonzero
  perm := by
    rw [remainingResidues, residuesOfPairs_eq_pairResidues]

/-- The actual surviving residue list has the numerical remaining branch
count. -/
theorem remainingResidues_length (forest : FusionForestWitness pairing) :
    forest.remainingResidues.length = forest.remainingBranchCount := by
  exact residuesOfPairs_length forest.smoothPairs

/-- Global additive branch identity. -/
theorem originalBranchCount_eq_nodes_add_remaining
    (forest : FusionForestWitness pairing) :
    forest.originalBranchCount =
      2 * forest.nodePairs.length + forest.remainingBranchCount := by
  have hcoverage := pairing.occurrence_count_eq_twice_pair_count
  have hpartition := forest.pair_count_eq_nodes_add_smooth
  simp only [originalBranchCount, remainingBranchCount] at hcoverage ⊢
  omega

/-- Global subtractive branch identity. -/
theorem remainingBranchCount_eq_original_sub_nodes
    (forest : FusionForestWitness pairing) :
    forest.remainingBranchCount =
      forest.originalBranchCount - 2 * forest.nodePairs.length := by
  have h := forest.originalBranchCount_eq_nodes_add_remaining
  omega

/-- Forest form of the fused-branch formula. -/
theorem remainingBranchCount_eq_forest_formula
    (forest : FusionForestWitness pairing) :
    forest.remainingBranchCount =
      forest.originalBranchCount -
        2 * (forest.vertexCount - forest.componentCount) := by
  have hbranches := forest.remainingBranchCount_eq_original_sub_nodes
  have hforest := forest.node_count_add_component_count_eq_vertex_count
  omega

/-- The forest identities preserve the aggregate integer rank expression.
This is a bookkeeping identity, not yet a claim about sums of local ranks. -/
theorem rankExpression_preserved (forest : FusionForestWitness pairing) :
    forest.originalRankExpression = forest.fusedRankExpression := by
  have hbranches := forest.originalBranchCount_eq_nodes_add_remaining
  have hforest := forest.node_count_add_component_count_eq_vertex_count
  have hbranchesInt :
      (forest.originalBranchCount : Int) =
        2 * (forest.nodePairs.length : Int) +
          (forest.remainingBranchCount : Int) := by
    exact_mod_cast hbranches
  have hforestInt :
      (forest.nodePairs.length : Int) +
          (forest.componentCount : Int) =
        (forest.vertexCount : Int) := by
    exact_mod_cast hforest
  unfold originalRankExpression fusedRankExpression
  omega

private theorem sum_componentBranchCounts_eq_twice_smooth_length
    (components : List (FusionForestComponent p Vertex)) :
    (components.map fun component =>
      component.remainingBranchCount).sum =
        2 * (forestSmoothPairs components).length := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      change component.remainingBranchCount +
          (components.map fun tail => tail.remainingBranchCount).sum =
        2 * (component.smoothPairs ++
          forestSmoothPairs components).length
      rw [List.length_append, ih]
      unfold FusionForestComponent.remainingBranchCount
      omega

/-- The global surviving branch count is the sum of the individual fused
component branch counts. -/
theorem remainingBranchCount_eq_sum_componentBranchCounts
    (forest : FusionForestWitness pairing) :
    forest.remainingBranchCount =
      (forest.components.map fun component =>
        component.remainingBranchCount).sum := by
  have h := sum_componentBranchCounts_eq_twice_smooth_length
    forest.components
  simpa [remainingBranchCount, smoothPairs] using h.symm

private theorem componentRankSum_add_twice_length_eq_branchSum_aux
    (components : List (FusionForestComponent p Vertex))
    (two_le_remaining : ∀ component ∈ components,
      2 ≤ component.remainingBranchCount) :
    (components.map fun component =>
        component.remainingBranchCount - 2).sum +
          2 * components.length =
      (components.map fun component =>
        component.remainingBranchCount).sum := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      have hcomponent : 2 ≤ component.remainingBranchCount :=
        two_le_remaining component (by simp)
      have htail : ∀ tail ∈ components,
          2 ≤ tail.remainingBranchCount := by
        intro tail htail
        exact two_le_remaining tail (by simp [htail])
      have ih' := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
      omega

/-- Under a lower bound for every fused component, the componentwise
natural-number rank sum has the expected additive form.  An aggregate lower
bound is intentionally insufficient here. -/
theorem fusedComponentRankSum_add_twice_componentCount_eq_remainingBranchCount
    (forest : FusionForestWitness pairing)
    (two_le_remaining : ∀ component ∈ forest.components,
      2 ≤ component.remainingBranchCount) :
    forest.fusedComponentRankSum + 2 * forest.componentCount =
      forest.remainingBranchCount := by
  rw [forest.remainingBranchCount_eq_sum_componentBranchCounts]
  exact componentRankSum_add_twice_length_eq_branchSum_aux
    forest.components two_le_remaining

/-! ## Connecting an exact source family to actual local rank sums -/

/-- For a forest built from a source family, the certified forest vertices
are a permutation of the distinct source-position labels. -/
theorem vertices_perm_sourceVertexLabels
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing) :
    forest.vertices.Perm family.vertexLabels := by
  classical
  have hforestNodup : forest.vertices.Nodup := by
    simpa [vertices] using forest.vertices_nodup
  have hsourceNodup : family.vertexLabels.Nodup := by
    simpa [SourceBranchFamily.vertexLabels] using family.vertices_nodup
  apply (List.perm_ext_iff_of_nodup hforestNodup hsourceNodup).2
  intro vertex
  rw [forest.mem_vertices_iff_occurs]
  exact (family.mem_vertexLabels_iff_exists_occurrence vertex).symm

/-- Exact source branch count for a forest built from the source family's
occurrence list. -/
theorem originalBranchCount_eq_sourceBranchCount
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing) :
    forest.originalBranchCount = family.branchCount := by
  rfl

/-- Exact source-position count; distinct labels and nonempty source words
prevent two positions from collapsing or a position from disappearing. -/
theorem vertexCount_eq_sourceVertexCount
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing) :
    forest.vertexCount = family.vertexCount := by
  have hlength :=
    (forest.vertices_perm_sourceVertexLabels family sourcePairing).length_eq
  simpa [vertexCount, SourceBranchFamily.vertexCount,
    SourceBranchFamily.vertexLabels] using hlength

/-- Honest componentwise natural-number rank preservation.

The left side is the explicit sum over distinct source words.  The right side
is the explicit sum over fused forest components.  Besides the source
family's local bounds, the theorem requires `2 ≤ S'_c` separately for every
fused component, rather than replacing those conditions by one aggregate
inequality. -/
theorem sourceRankSum_eq_fusedComponentRankSum
    (family : SourceBranchFamily p Vertex)
    (sourcePairing : OccurrencePairingWitness family.occurrences)
    (forest : FusionForestWitness sourcePairing)
    (two_le_remaining : ∀ component ∈ forest.components,
      2 ≤ component.remainingBranchCount) :
    family.rankSum = forest.fusedComponentRankSum := by
  have hsource := family.rankSum_add_twice_vertexCount_eq_branchCount
  have hfused :=
    forest.fusedComponentRankSum_add_twice_componentCount_eq_remainingBranchCount
      two_le_remaining
  have hbranches := forest.originalBranchCount_eq_nodes_add_remaining
  have hforest := forest.node_count_add_component_count_eq_vertex_count
  have horiginal :=
    forest.originalBranchCount_eq_sourceBranchCount family sourcePairing
  have hvertices :=
    forest.vertexCount_eq_sourceVertexCount family sourcePairing
  omega

end FusionForestWitness

end

end

end AbelianCoverHodge.Verified
