import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedWorkProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamSourceOrder
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Work legality alone does not license a buffered callback: a generated held stream
can receive premature items before its owner flushes. Erasing those items changes FIFO.+-/

namespace AlternativePrematureStreamChecks

open GraphQL.IncrementalDelivery
open Execution (DeliveryNode Result ResponseValue)
open AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
open ReferenceWorkQueue (GraphEvent StreamItem)
open WorkQueueSemantics

private def group : DeliveryNode := { ref := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { ref := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 2, path := [], label := some (.string "C") }
private def stream : DeliveryNode := { ref := 3, path := [.field "values"] }
private def producer : Occurrence := .executionGroup [1, 0]
private def blocker : Occurrence := .executionGroup [1, 1, 0]
private def address : Address := [1, 0, 0, 0, 1]

private def entries : List (Result ResponseValue × Execution.Work) :=
  [
    (.ok (.scalar "x", 0), .empty),
    (.ok (.null, 0), .empty),
    (.ok (.scalar "z", 0), .empty)
  ]

private def children : Execution.Work :=
  .combine (.combine .empty (.stream stream entries)) .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [{ node := group }, ⟨child, [parent]⟩] []
        (.ok ([("values", .list [])], 0)) children)
      (.combine
        (.executionGroup [{ node := group }] [] (.ok ([("b", .scalar "b")], 0))
          (.combine .empty .empty))
        (.combine
          (.executionGroup [{ node := parent }] [] (.ok ([("c", .scalar "c")], 0))
            (.combine .empty .empty)) .empty)))

private theorem generated : ReferenceWorkQueue.ExecutedWork work := by
  refine ⟨Nat, Tests.schema, Tests.resolvers, [], 50, "Query", .object "Query" 0,
    [Tests.defer [Tests.field "values" [] [.stream], Tests.field "b"] (some "R"),
      Tests.defer [Tests.field "c",
        Tests.defer [Tests.field "values" [] [.stream]] (some "C")] (some "P")], ?_⟩
  cbv

private theorem nonempty : work.size ≠ 0 := by decide

private def produced : GraphEvent :=
  .taskSuccess producer
    {
      value :=
        { deliveryGroups := [group, child], path := [], data := [("values", .list [])] }
      work := ReferenceWorkQueue.Work.fromExecution children [1, 0, 0]
    }

private def release : GraphEvent :=
  .taskSuccess blocker
    { value := { deliveryGroups := [group], path := [], data := [("b", .scalar "b")] } }

private def first : StreamItem := ⟨.item address 0, ⟨.scalar "x", 0⟩, {}⟩
private def second : StreamItem := ⟨.item address 1, ⟨.null, 0⟩, {}⟩
private def premature : GraphEvent := .streamItems stream [first]
private def later : GraphEvent := .streamItems stream [second]

private def raw : List (List GraphEvent) :=
  [[produced], [premature], [release], [later]]

private def effective : List (List GraphEvent) := [[produced], [release], [later]]

private abbrev initial :=
  ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)

private theorem producer_known
    : TaskAt work producer [0, 2] none (.object [] (.ok ([("values", .list [])], 0))) :=
  ⟨[{ node := group }, ⟨child, [parent]⟩], [], _, children, [], rfl, rfl, rfl⟩

private theorem blocker_known
    : TaskAt work blocker [0] none (.object [] (.ok ([("b", .scalar "b")], 0))) :=
  ⟨[{ node := group }], [], _, .combine .empty .empty, [], rfl, rfl, rfl⟩

private theorem stream_known
    : Located work address (.stream stream entries) (some producer) [0, 2] := by
  rfl

private theorem first_known
    : TaskAt work first.occurrence [stream.ref] (some producer)
        (.item stream (.ok (.scalar "x", 0))) :=
  ⟨stream, entries, [0, 2], _, .empty, stream_known, rfl, rfl, rfl⟩

private theorem second_known
    : TaskAt work second.occurrence [stream.ref] (some producer)
        (.item stream (.ok (.null, 0))) :=
  ⟨stream, entries, [0, 2], _, .empty, stream_known, rfl, rfl, rfl⟩

private theorem raw_valid : ReferenceWorkQueue.ValidGraphEvents work raw.flatten := by
  have one : ReferenceWorkQueue.ValidGraphEvents work [produced] :=
    .append .nil ⟨_, _, producer_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, produced])
      ⟨_, _, _, producer_known, fun _ impossible => by cases impossible⟩
  have two : ReferenceWorkQueue.ValidGraphEvents work [produced, premature] := by
    refine .append one ?_ ?_ ?_
    · intro item member
      have same : item = first := List.mem_singleton.mp member
      subst item
      exact ⟨[stream.ref], some producer, first_known, rfl⟩
    · simp [GraphEvent.Fresh, GraphEvent.identities, produced, premature, first,
        producer, address]
    · refine ⟨address, entries, some producer, [0, 2], stream_known, by decide, ?_, ?_, ?_⟩
      · simp [GraphEvent.identities, produced]
      · intro source same
        cases same
        exact List.mem_cons_self
      · rfl
  have three : ReferenceWorkQueue.ValidGraphEvents work [produced, premature, release] :=
    .append two ⟨_, _, blocker_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, produced, premature, release,
        first, producer, blocker, address])
      ⟨_, _, _, blocker_known, fun _ impossible => by cases impossible⟩
  refine .append three ?_ ?_ ?_
  · intro item member
    have same : item = second := List.mem_singleton.mp member
    subst item
    exact ⟨[stream.ref], some producer, second_known, rfl⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities, produced, premature, release, later,
      first, second, producer, blocker, address]
  · refine ⟨address, entries, some producer, [0, 2], stream_known, by decide, ?_, ?_, ?_⟩
    · simp [GraphEvent.identities, produced, premature, release]
    · intro source same
      cases same
      simp [GraphEvent.successes, produced, premature, release]
    · rfl

private theorem projected : projectHistory initial raw = effective := by cbv

private theorem projected_not_valid
    : ¬ReferenceWorkQueue.ValidGraphEvents work (projectHistory initial raw).flatten := by
  intro valid
  have order := valid.itemsBefore_order generated stream_known
  rw [projected] at order
  simp [GraphEvent.itemsBefore, effective, produced, release, later, second, stream,
    address, List.range_succ] at order

/-- Even generated nonempty work refutes filtering justified only by raw work legality.
The missing permission is source activation at enqueue, not an output lifecycle premise.
-/
theorem work_only_projection_refuted
    : ¬(∀ (work : Execution.Work) (batches : List (List GraphEvent)),
          ReferenceWorkQueue.ExecutedWork work
          → work.size ≠ 0
          → ReferenceWorkQueue.ValidGraphEvents work batches.flatten
          → ReferenceWorkQueue.ValidGraphEvents work
              (projectHistory
                (ReferenceWorkQueue.State.initialize
                  (ReferenceWorkQueue.Work.fromExecution work))
                batches).flatten) := by
  intro projection
  exact projected_not_valid (projection work raw generated nonempty raw_valid)

-- The producer has settled, but group flushing and stream activation are still pending.
example : (initial.handleGraphEvents [produced]).1.rootStreams = [] := by cbv

example
    : (initial.handleGraphEvents [produced]).1.acceptsGraphEvent premature = false := by
  cbv

example
    : (initial.runNormalized [[produced], [release]]).1.acceptsGraphEvent later
      = true := by cbv

example : ReferenceWorkQueue.ExecutedWork work := generated
example : ReferenceWorkQueue.ValidGraphEvents work raw.flatten := raw_valid
example : projectHistory initial raw = effective := projected

example : ¬ReferenceWorkQueue.ValidGraphEvents work effective.flatten := by
  simpa only [projected] using projected_not_valid

-- The premise missing from the work-only projection is genuinely enqueue-time eligibility.
example (receipt : Nat)
    : ¬Enqueued work (initial.handleGraphEvents [produced]).1 [produced]
        [⟨receipt, premature⟩] := by
  intro enqueued
  have live := enqueued.started ⟨receipt, premature⟩ List.mem_cons_self
  have stale : (initial.handleGraphEvents [produced]).1.acceptsGraphEvent premature = false := by
    cbv
  rw [stale] at live
  cases live

-----------------------------------------------------------------------------------------
-- Delaying source consumption until activation preserves the complete item prefix
-----------------------------------------------------------------------------------------

private abbrev released := (initial.runNormalized [[produced], [release]]).1
private def itemCallbacks : List BufferedCallback := [⟨20, premature⟩, ⟨21, later⟩]
private def legal : List (List GraphEvent) := [[produced], [release], [premature, later]]

private theorem before_valid
    : ReferenceWorkQueue.ValidGraphEvents work [produced, release] := by
  have one : ReferenceWorkQueue.ValidGraphEvents work [produced] :=
    .append .nil ⟨_, _, producer_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, produced])
      ⟨_, _, _, producer_known, fun _ impossible => by cases impossible⟩
  exact .append one ⟨_, _, blocker_known, rfl, rfl⟩
    (by
      simp [GraphEvent.Fresh, GraphEvent.identities, produced, release, producer, blocker])
    ⟨_, _, _, blocker_known, fun _ impossible => by cases impossible⟩

private theorem items_enqueued
    : Enqueued work released [produced, release] itemCallbacks := by
  have one : Enqueued work released [produced, release] [⟨20, premature⟩] := by
    refine .append .nil ⟨20, premature⟩ (by cbv) (by cbv) (by simp) ?_ ?_ ?_
    · intro item member
      have same : item = first := List.mem_singleton.mp member
      subst item
      exact ⟨[stream.ref], some producer, first_known, rfl⟩
    · simp [GraphEvent.Fresh, GraphEvent.identities, produced, release, premature,
        first, producer, blocker, address]
    · refine ⟨address, entries, some producer, [0, 2], stream_known, by decide, ?_, ?_, ?_⟩
      · simp [GraphEvent.identities, produced, release]
      · intro source same
        cases same
        simp [GraphEvent.successes, produced, release]
      · rfl
  refine .append one ⟨21, later⟩ (by cbv) (by cbv) (by decide) ?_ ?_ ?_
  · intro item member
    have same : item = second := List.mem_singleton.mp member
    subst item
    exact ⟨[stream.ref], some producer, second_known, rfl⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities, produced, release, premature, later,
      first, second, producer, blocker, address]
  · refine ⟨address, entries, some producer, [0, 2], stream_known, by decide, ?_, ?_, ?_⟩
    · simp [GraphEvent.identities, produced, release, premature]
    · intro source same
      cases same
      simp [GraphEvent.successes, produced, release, premature]
    · rfl

private theorem legal_buffers : BoundaryBuffers work initial [] legal := by
  refine ⟨⟨[⟨10, produced⟩], ?_, rfl⟩, ⟨⟨[⟨11, release⟩], ?_, rfl⟩, ?_⟩⟩
  · exact .append .nil ⟨10, produced⟩ (by cbv) (by cbv) (by simp)
      ⟨_, _, producer_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, produced])
      ⟨_, _, _, producer_known, fun _ impossible => by cases impossible⟩
  · exact .append .nil ⟨11, release⟩ (by cbv) (by cbv) (by simp)
      ⟨_, _, blocker_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, produced, release, producer, blocker])
      ⟨_, _, _, blocker_known, fun _ impossible => by cases impossible⟩
  · exact ⟨⟨itemCallbacks, items_enqueued, rfl⟩, trivial⟩

private theorem legal_valid : ReferenceWorkQueue.ValidGraphEvents work legal.flatten :=
  legal_buffers.work_valid .nil

example
    : GraphEvent.itemsBefore
        (projectBatch released (itemCallbacks.map BufferedCallback.event)) stream.ref
      = [first, second] :=
  items_enqueued.itemsBefore_projectBatch before_valid stream.ref

example
    : (projectBatch released (itemCallbacks.map BufferedCallback.event)).filterMap
        GraphEvent.streamAction
      = [(stream.ref, false), (stream.ref, false)] :=
  items_enqueued.streamActions_projectBatch before_valid

example : BoundaryBuffers work initial [] legal := legal_buffers
example : ReferenceWorkQueue.ValidGraphEvents work legal.flatten := legal_valid
example : projectHistory initial legal = legal := by cbv

-- Conformance is derived for the same legal history, not for the premature raw source.
example
    : (AlternativeWorkQueue.createWorkQueueForSchedule work
        (EventSource.ofList legal)).Conforms
        work := by
  have projected : projectHistory initial legal = legal := by cbv
  rw [← projected]
  exact projected_conforms generated nonempty legal legal_buffers

#print axioms projected_not_valid
#print axioms work_only_projection_refuted
#print axioms legal_buffers
#print axioms Enqueued.itemsBefore_projectBatch
#print axioms Enqueued.streamActions_projectBatch

end AlternativePrematureStreamChecks
