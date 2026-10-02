import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamOpenness
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Item-produced child streams retain their own item identities across batching. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerItemStreams
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def outer : DeliveryNode := { key := 0, path := [.field "users"] }

private def child (index : Nat) : DeliveryNode :=
  { key := index + 1, path := [.field "users", .index index, .field "values"] }

private def childItems : List (Result ResponseValue × Execution.Work) :=
  [
    (.ok (.scalar "x", 0), .empty),
    (.ok (.null, 0), .empty),
    (.ok (.scalar "z", 0), .empty)
  ]

private def children (index : Nat) : Execution.Work :=
  .combine (.combine (.combine .empty (.stream (child index) childItems)) .empty) .empty

private def value : ResponseValue := .object [("values", .list [])]

private def entries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (value, 0), children 0), (.ok (value, 0), children 1)]

private def work : Execution.Work :=
  .combine (.combine (.combine .empty (.stream outer entries)) .empty) .empty

private def item (index : Nat) : StreamItem :=
  {
    occurrence := .item [0, 0, 1] index,
    value := ⟨value, 0⟩,
    work := Work.fromExecution (children index) ([0, 0, 1] ++ [index])
  }

private def initial : State := State.initialize (Work.fromExecution work)
private def first : GraphEvent := .streamItems outer [item 0]
private def second : GraphEvent := .streamItems outer [item 1]
private def joined : GraphEvent := .streamItems outer [item 0, item 1]

/-- Real query execution produces two equal-valued items with distinct child streams.
Witness: evaluate users @stream { values @stream } with the shared finite resolvers.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [field "users" [field "values" [] [.stream]] [.stream]], ?_⟩
  cbv

/-- The outer stream is producer-free. Witness: its exact generated structural location. -/
private theorem outerLocated
    : Located work [0, 0, 1] (.stream outer entries) none [] := by cbv

/-- Each item has its exact source payload and independently lowered child stream.
Witness: its indexed entry in the generated outer stream.
-/
private theorem itemMatches (index : Nat) (bound : index < 2)
    : ∃ owners producer,
        TaskAt work (item index).occurrence owners producer
          (.item outer (.ok ((item index).value.item, (item index).value.errors)))
        ∧ streamItemWork? work (item index).occurrence = some (item index).work := by
  have entry : entries[index]? = some (.ok (value, 0), children index) := by
    have casesIndex : index = 0 ∨ index = 1 := by omega
    rcases casesIndex with rfl | rfl <;> rfl
  refine ⟨
    [outer.key],
    none,
    ⟨outer, entries, [], .ok (value, 0), children index, outerLocated, entry, rfl, rfl⟩,
    ?_
  ⟩
  have located : locateWork work [0, 0, 1] = some ⟨.stream outer entries, none, []⟩ := outerLocated
  simp [streamItemWork?, item, located, entry]

/-- A child stream retains its corresponding outer item as producer.
Witness: the exact generated child location at either outer item index.
-/
private theorem childLocated (index : Nat) (bound : index < 2)
    : Located work ([0, 0, 1, index, 0, 0, 1]) (.stream (child index) childItems)
        (some (item index).occurrence) [] := by
  have casesIndex : index = 0 ∨ index = 1 := by omega
  rcases casesIndex with rfl | rfl <;> cbv

/-- Each child descriptor is a genuine stream node with the expected producing item.
Witness: project its exact stream location.
-/
private theorem childKnown (index : Nat) (bound : index < 2)
    : NodeAt work (child index) .stream [] (some (item index).occurrence) :=
  ⟨_, childItems, childLocated index bound⟩

/-- Both graph-event widths respect the existing source semantics and actual start checks.
Witness: exact matching, distinct item identities, and contiguous ordinals from zero.
-/
theorem inputs_valid_started
    : ValidGraphEvents work [first, second]
      ∧ inputsStarted work [[first], [second]] = true
      ∧ ValidGraphEvents work [joined]
      ∧ inputsStarted work [[joined]] = true := by
  have firstMatch : first.MatchesWork work := by
    intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact itemMatches 0 (by omega)
  have secondMatch : second.MatchesWork work := by
    intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact itemMatches 1 (by omega)
  have firstValid : ValidGraphEvents work [first] :=
    .append .nil firstMatch (by simp [first, item, GraphEvent.Fresh, GraphEvent.identities])
      ⟨[0, 0, 1], entries, none, [], outerLocated, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  refine ⟨
    .append firstValid secondMatch
      (by simp [first, second, item, GraphEvent.Fresh, GraphEvent.identities])
      ⟨
        [0, 0, 1],
        entries,
        none,
        [],
        outerLocated,
        by simp,
        (by simp [first, GraphEvent.identities]),
        (by intro source impossible; cases impossible),
        by cbv
      ⟩,
    by cbv,
    ?_,
    by cbv
  ⟩
  apply ValidGraphEvents.append .nil
  · intro supplied member
    rcases List.mem_cons.mp member with left | right
    · subst supplied; exact itemMatches 0 (by omega)
    · have same := List.mem_singleton.mp right
      subst supplied; exact itemMatches 1 (by omega)
  · simp [joined, item, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨[0, 0, 1], entries, none, [], outerLocated, by simp, by simp,
      (by intro source impossible; cases impossible), rfl⟩

/-- The normalized runner retains the same item-release inventory at both event widths.
Witness: apply the general full-replay theorem to the valid, started generated inputs.
-/
theorem normalized_item_release_inventory
    : NormalizedItemStreamReleasePublications work
        ([first, second].flatMap GraphEvent.itemPublications)
        (initial.runNormalized [[first], [second]]).2.flatten
      ∧ NormalizedItemStreamReleasePublications work joined.itemPublications
          (initial.runNormalized [[joined]]).2.flatten := by
  constructor
  · exact createWorkQueue_runNormalized_itemStreamReleasePublications
      inputs_valid_started.1 inputs_valid_started.2.1
  · exact createWorkQueue_runNormalized_itemStreamReleasePublications
      inputs_valid_started.2.2.1 inputs_valid_started.2.2.2

/-- Equal-valued items still require the correct occurrence labels at the first child notice.
Witness: the first stream's unique structural producer is item zero, which a reversed
inventory places after its notice's inclusive item prefix. This is not a queue trace bug.
-/
theorem swapped_item_labels_lose_release_support
    : (item 0).value = (item 1).value
      ∧ ¬NormalizedItemStreamReleasePublications work
          (([first, second].flatMap GraphEvent.itemPublications).reverse)
          (initial.runNormalized [[first], [second]]).2.flatten := by
  refine ⟨rfl, ?_⟩
  intro support
  obtain ⟨occurrence, known, published⟩ := support 0 outer [⟨value, 0⟩] [] [child 0]
    (by cbv) (child 0) List.mem_cons_self
  have same := Option.some.inj
    (generated.streamProducer_unique known (childKnown 0 (by omega)) rfl)
  subst occurrence
  change (item 0).occurrence ∈ [(item 1).occurrence] at published
  simp [item] at published

-----------------------------------------------------------------------------------------
-- A later child-stream reference uses the same joint publication matching
-----------------------------------------------------------------------------------------

private def leaf : StreamItem :=
  { occurrence := .item [0, 0, 1, 0, 0, 0, 1] 0, value := ⟨.scalar "x", 0⟩ }

private def next : GraphEvent := .streamItems (child 0) [leaf]

/-- The first child item can arrive after the joined outer-item carrier.
Witness: its exact outcome and child lowering, fresh occurrence, published source-order
producer input, contiguous child ordinal, and the queue's executable start check.
-/
theorem continued_inputs_valid_started
    : ValidGraphEvents work [joined, next]
      ∧ inputsStarted work [[joined], [next]] = true := by
  refine ⟨.append inputs_valid_started.2.2.1 ?_ ?_ ?_, by cbv⟩
  · intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    refine ⟨[(child 0).key], some (item 0).occurrence, ?_, by cbv⟩
    exact ⟨child 0, childItems, [], .ok (.scalar "x", 0), .empty,
      childLocated 0 (by omega), rfl, rfl, rfl⟩
  · simp [joined, next, leaf, item, GraphEvent.Fresh, GraphEvent.identities]
  · refine ⟨[0, 0, 1, 0, 0, 0, 1], childItems, some (item 0).occurrence, [],
      childLocated 0 (by omega), by simp, ?_, ?_, by cbv⟩
    · simp [joined, GraphEvent.identities]
    · intro source same
      cases same
      simp [joined, GraphEvent.successes]

/-- Both producer items are published by the last carrier atom, before the child item arrives.
Witness: the common freshness/release/readiness matching. The two equal-valued producers
remain distinct, and the later child reference uses item zero's actual earlier publication.
-/
theorem joint_item_stream_readiness
    : let outputs := (initial.runNormalized [[joined], [next]]).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → ¬Published matching (atoms.take index) (matching index))
        ∧ Published matching (atoms.take 2) (item 0).occurrence
        ∧ Published matching (atoms.take 2) (item 1).occurrence := by
  obtain ⟨matching, batching, values, notices, references⟩ :=
    createWorkQueue_runNormalized_streamProducerReadinessMatching
      (batches := [[joined], [next]]) generated
      continued_inputs_valid_started.1 continued_inputs_valid_started.2
  refine ⟨matching, batching, fun index event atEvent value =>
    (values index event atEvent value).2.1, ?_, ?_⟩
  · exact references 2 (.streamValues (child 0) [⟨.scalar "x", 0⟩] [] [])
      (by cbv) (child 0) [] (some (item 0).occurrence) List.mem_cons_self
      (childKnown 0 (by omega)) _ rfl
  · obtain ⟨dependencies, occurrence, located, published⟩ :=
      notices 1 (.streamValues outer [⟨value, 0⟩] [] [child 0, child 1]) (by cbv)
        (child 1) (by simp)
    have same := Option.some.inj
      (generated.streamProducer_unique located (childKnown 1 (by omega)) rfl)
    subst occurrence
    exact published

/-- Every outer/child item satisfies CanPublish when there are no failure cuts.
Witness: the actual matching's exact singleton payload and readiness equivalence; an
empty cut list has no historical cancellation. This does not claim full EventAllowed.
-/
theorem stream_values_ready_without_cuts
    : let outputs := (initial.runNormalized [[joined], [next]]).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ ∀ index stream values groups streams,
            atoms[index]? = some (.streamValues stream values groups streams)
            → ∃ value producer,
                values = [value]
                ∧ TaskAt work (matching index) [stream.key] producer
                    (.item stream (.ok (value.item, value.errors)))
                ∧ CanPublish work matching (atoms.take index) [] (matching index)
                    producer := by
  obtain ⟨matching, batching, _, ready⟩ :=
    createWorkQueue_runNormalized_streamPublicationReadinessMatching
      (batches := [[joined], [next]]) generated
      continued_inputs_valid_started.1 continued_inputs_valid_started.2
  refine ⟨matching, batching, ?_⟩
  intro index stream values groups streams atEvent
  obtain ⟨value, producer, singleton, known, admissible⟩ :=
    ready index stream values groups streams atEvent
  exact ⟨
    value,
    producer,
    singleton,
    known,
    (admissible []).mpr (by rintro ⟨cut, impossible, _⟩; cases impossible)
  ⟩

/-- The readiness bridge retains, rather than erases, a supplied cancellation cut.
Witness: a synthetic failure of the current successful item cancels its sole owner at
cut zero and blocks CanPublish. That failure is not licensed by the source or admission;
the test checks the arbitrary-cut equivalence, not a claimed implementation behavior.
-/
theorem cancellation_cut_still_blocks
    : let outputs := (initial.runNormalized [[joined], [next]]).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
      ∃ producer,
        TaskAt work (matching 0) [outer.key] producer (.item outer (.ok (value, 0)))
        ∧ ¬CanPublish work matching (atoms.take 0) [(0, matching 0)] (matching 0)
            producer := by
  obtain ⟨matching, _, _, ready⟩ :=
    createWorkQueue_runNormalized_streamPublicationReadinessMatching
      (batches := [[joined], [next]]) generated
      continued_inputs_valid_started.1 continued_inputs_valid_started.2
  obtain ⟨supplied, producer, singleton, known, admissible⟩ :=
    ready 0 outer [⟨value, 0⟩] [] [] (by cbv)
  have same : supplied = ⟨value, 0⟩ := (List.singleton_inj.mp singleton).symm
  subst supplied
  refine ⟨matching, producer, known, ?_⟩
  intro allowed
  have uncancelled := (admissible [(0, matching 0)]).mp allowed
  apply uncancelled
  refine ⟨0, by simp, by simp, ?_⟩
  apply Causality.TaskCancelled.owners ⟨producer, _, known⟩
  · simp [Published]
  · simp
  · intro key member
    exact Causality.NodeFailed.task ⟨producer, _, known⟩ member (by simp [failedBefore])

/-- Root and item-produced streams use open keys at each actual reference.
Witness: the generated-work openness theorem, including the first child reference after
the shared carrier announces two equal-valued outer items' distinct child streams.
-/
theorem nested_stream_references_open
    : let atoms :=
        (initial.runNormalized [[joined], [next]]).2.flatten.flatMap publicationAtoms
      ∀ index event,
        atoms[index]? = some event
        → ∀ key ∈ streamReferenceKeys event,
            Open ((initial.initialGroups ++ initial.initialStreams).map DeliveryNode.key)
              (atoms.take index) key := by
  dsimp only
  intro index event atEvent key reference
  exact createWorkQueue_runNormalized_streamOpenAt generated
    (batches := [[joined], [next]]) continued_inputs_valid_started.1 atEvent reference

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerItemStreams
