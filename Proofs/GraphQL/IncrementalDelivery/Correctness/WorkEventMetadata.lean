import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata

/-! All observed descriptors come from actual work, through every grouping choice. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- Every descriptor carried by an event, including its owner and pending notices. -/
def eventNodes : WorkEvent → List DeliveryNode
  | .groupValues node _
  | .groupFailure node _
  | .streamSuccess node
  | .streamFailure node _ => [node]
  | .groupSuccess node groups streams | .streamValues node _ groups streams =>
      node :: (groups ++ streams)
  | .workQueueTermination => []

/-- A descriptor is backed by some structural work occurrence, without deduplication. -/
def KnownNode (work : Work) (node : DeliveryNode) : Prop :=
  ∃ kind parents birth, NodeAt work node kind parents birth

/-- Licensed announcements contain only work descriptors, by their structural premises.
-/
theorem announcement_nodes {work initial matching events failed groups streams}
    (announced : Announcements work initial matching events failed groups streams)
    : ∀ node ∈ groups ++ streams, KnownNode work node := by
  intro node member
  rcases List.mem_append.mp member with group | stream
  · obtain ⟨parents, birth, known, _⟩ := announced.2.1 node group
    exact ⟨.group, parents, birth, known⟩
  · obtain ⟨parents, birth, known, _⟩ := announced.2.2 node stream
    exact ⟨.stream, parents, birth, known⟩

/-- Atomic events contain only known descriptors, by owner and announcement rules. -/
theorem event_allowed_nodes {work initial matching before failed event}
    (allowed : EventAllowed work initial matching before failed event)
    : ∀ node ∈ eventNodes event, KnownNode work node := by
  cases event with
  | groupValues node values =>
      obtain ⟨_, _, _, _, _, _, _, _, owner⟩ := allowed
      simpa [eventNodes, KnownNode] using owner.1.1
  | groupSuccess node groups streams =>
      obtain ⟨⟨parents, birth, known⟩, _, _, _, announced⟩ := allowed
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨.group, parents, birth, known⟩
      · exact announcement_nodes announced other member
  | groupFailure node errors =>
      obtain ⟨⟨parents, birth, known⟩, _⟩ := allowed
      simpa [eventNodes] using (show KnownNode work node from ⟨.group, parents, birth, known⟩)
  | streamValues node values groups streams =>
      obtain ⟨_, _, _, _, _, _, _, owner, announced⟩ := allowed
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact owner.1.1
      · exact announcement_nodes announced other member
  | streamSuccess node | streamFailure node errors =>
      obtain ⟨⟨parents, birth, known⟩, _⟩ := allowed
      simpa [eventNodes] using (show KnownNode work node from ⟨.stream, parents, birth, known⟩)
  | workQueueTermination => cases allowed

/-- Compatible value combination cannot invent a descriptor; witness: its two cases.
-/
theorem combineValues_nodes {left right combined}
    (combinedAt : combineValues left right = some combined)
    : ∀ node ∈ eventNodes combined, node ∈ eventNodes left ++ eventNodes right := by
  cases left <;> cases right <;> simp [combineValues] at combinedAt
  all_goals
    obtain ⟨_, rfl⟩ := combinedAt
    simp only [eventNodes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    grind

/-- Value grouping retains descriptor provenance, by grouping induction and containment.
-/
theorem valueGrouping_nodes {events grouped} (grouping : ValueGrouping events grouped)
    : ∀ node ∈ grouped.flatMap eventNodes, node ∈ events.flatMap eventNodes := by
  induction grouping with
  | nil => simp
  | separate head _ ih =>
      intro node member
      rcases List.mem_append.mp member with head | tail
      · exact List.mem_append_left _ head
      · exact List.mem_append_right _ (ih node tail)
  | @combine head tail first rest merged _ compatible ih =>
      intro node member
      rcases List.mem_append.mp member with merged | tail
      · rcases List.mem_append.mp (combineValues_nodes compatible node merged) with first | next
        · exact List.mem_append_left _ first
        · exact List.mem_append_right _ (ih node (List.mem_append_left _ next))
      · exact List.mem_append_right _ (ih node (List.mem_append_right _ tail))

/-- Work batching retains descriptor provenance across all flattened output groups. -/
theorem workBatching_nodes {events batches} (grouping : WorkBatching events batches)
    : ∀ node ∈ batches.flatten.flatMap eventNodes, node ∈ events.flatMap eventNodes := by
  induction grouping with
  | nil => simp
  | cons _ values _ ih =>
      intro node member
      simp only [List.flatten_cons, List.flatMap_append, List.mem_append] at member ⊢
      exact member.elim (fun head => Or.inl (valueGrouping_nodes values node head))
        (fun tail => Or.inr (ih node tail))

/-- Every descriptor in an explaining history is real, by its selected event's rule. -/
theorem explained_nodes {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : ∀ node ∈ events.flatMap eventNodes, KnownNode work node := by
  intro node member
  obtain ⟨event, selected, member⟩ := List.mem_flatMap.mp member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp selected
  exact event_allowed_nodes (explained.2.2 index event selected) node member

/-- Both initial and later descriptors in an admitted observation retain their source
paths. Witness: work-node provenance and the independently proved assignment invariant.
-/
theorem history_node_paths {paths bound work history}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (admitted : AdmissiblePrefix work history ∨ AdmissibleRun work history)
    : (∀ node ∈ history.initialGroups ++ history.initialStreams,
        paths node.key = node.path)
      ∧ ∀ node ∈ history.batches.flatten.flatMap eventNodes,
          paths node.key = node.path := by
  have fromKnown {node} (known : KnownNode work node) : paths node.key = node.path := by
    obtain ⟨kind, parents, birth, known⟩ := known
    exact (workAt_node coherent known).2
  rcases admitted with ⟨events, matching, failures, explained, grouped⟩
    | ⟨events, matching, failures, explained, _, grouped⟩
  · exact ⟨fun node member => fromKnown (announcement_nodes explained.1.1 node member),
      fun node member => fromKnown
        (explained_nodes explained node (workBatching_nodes grouped node member))⟩
  · refine ⟨fun node member => fromKnown (announcement_nodes explained.1.1 node member), ?_⟩
    intro node member
    have source := workBatching_nodes grouped node member
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      eventNodes, List.append_nil] at source
    exact fromKnown (explained_nodes explained node source)

end GraphQL.IncrementalDelivery.Correctness
