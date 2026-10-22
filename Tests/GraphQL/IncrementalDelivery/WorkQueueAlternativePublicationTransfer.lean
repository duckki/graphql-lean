import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PublicationExclusion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceHandoff
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordProgress
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Full generated publication transfers an earlier buffer to a stop-reachable source. -/

namespace AlternativePublicationTransferChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence TaskAt)
open GraphQL.IncrementalDelivery.Tests (schema resolvers field defer)

example : GeneratedPublishedBufferTransfer := GeneratedPublishedBufferTransfer_holds

example : GeneratedPublicationExclusionTransfer :=
  GeneratedPublicationExclusionTransfer_holds

private def group : Execution.DeliveryNode := ⟨0, [], some (.string "P")⟩
private def source : Execution.DeliveryNode := ⟨1, [.field "user", .field "values"], none⟩
private def producer : Occurrence := .executionGroup [0, 0, 1, 0]
private def finisher : Occurrence := .executionGroup [1, 0]

private def value : Execution.ExecutionGroupValue :=
  { deliveryGroups := [group], path := [.field "user"], data := [("values", .list [])] }

private def lastValue : Execution.ExecutionGroupValue :=
  { deliveryGroups := [group], path := [], data := [("b", .scalar "b")] }

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.stream source
        [
          ({ result := .ok (.scalar "x", 0) }, .empty),
          ({ result := .ok (.null, 0) }, .empty),
          ({ result := .ok (.scalar "z", 0) }, .empty)
        ]))
    .empty

private def work : Execution.Work :=
  .combine
    (.combine
      (.combine (.combine .empty .empty)
        (.combine
          (.executionGroup [⟨group, []⟩] value.path ({ result := .ok (value.data, 0) })
            children)
          .empty))
      .empty)
    (.combine
      (.executionGroup [⟨group, []⟩] [] ({ result := .ok (lastValue.data, 0) })
        (.combine .empty .empty))
      .empty)

private def success : GraphEvent :=
  .taskSuccess producer
    { value, work := ReferenceWorkQueue.Work.fromExecution children [0, 0, 1, 0, 0] }

private def finish : GraphEvent :=
  .taskSuccess finisher
    {
      value := lastValue,
      work := ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 0, 0]
    }

private def earlierInputs : List (List GraphEvent) := [[success]]
private abbrev before := ((State.initialize work).runNormalized earlierInputs).1
private abbrev reduced := ({ state := before } : GraphBatchResult).handleGraphEvent finish

private def node : ReferenceWorkQueue.TaskNode :=
  {
    task := { occurrence := producer, groups := [group] },
    value := some value,
    childStreams := [1]
  }

private theorem generated : ReferenceWorkQueue.ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [field "user" [field "name"],
     defer [field "b", field "user" [field "values" [] [.stream (.boolean true) none (.int 0)]]]
       (some "P")], ?_⟩
  cbv

private theorem producer_known
    : TaskAt work producer [group.ref] none (.object value.path (.ok (value.data, 0))) :=
  ⟨_, value.path, { result := .ok (value.data, 0) }, children, [], rfl, rfl, rfl⟩

private theorem finisher_known
    : TaskAt work finisher [group.ref] none (.object [] (.ok (lastValue.data, 0))) :=
  ⟨
    _,
    [],
    { result := .ok (lastValue.data, 0) },
    .combine .empty .empty,
    [],
    rfl,
    rfl,
    rfl
  ⟩

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents work (earlierInputs.flatten ++ [finish]) := by
  have first : ReferenceWorkQueue.ValidGraphEvents work [success] :=
    .append .nil ⟨_, _, producer_known, rfl, rfl⟩
      (by simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities, success])
      ⟨_, _, _, producer_known, by intro other impossible; cases impossible⟩
  exact .append first ⟨_, _, finisher_known, rfl, rfl⟩
    (by
      simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        earlierInputs, success, finish, producer, finisher])
    ⟨_, _, _, finisher_known, by intro other impossible; cases impossible⟩

private theorem started
    : ReferenceWorkQueue.inputsStarted work (earlierInputs ++ [[finish]]) = true := by cbv

example : before.queue.taskNode? producer = some node := by cbv
example : before.queue.rootStreams = [] := by cbv
example : reduced.state.queue.taskNode? producer = none := by cbv

private theorem transferred
    : 1 ∈ reduced.state.queue.rootStreams ∧ .stream 1 ∈ reduced.state.cleanupTargets := by
  have coverage := GeneratedPublishedBufferTransfer_holds work earlierInputs finish generated valid started
    producer node value 1 group [] [source] (by cbv) rfl (by decide) List.mem_cons_self
    (by cbv; exact List.mem_cons_self) (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
  exact coverage.2

example : 1 ∈ reduced.state.queue.rootStreams := transferred.1
example : .stream 1 ∈ reduced.state.cleanupTargets := transferred.2

-- Source progress does not require the caller to know that the old buffer disappears.
example
    : RecordTargetRepresented reduced.state.queue (.stream 1)
      ∨ .cancelSource 1 ∈ reduced.effects :=
  GeneratedPreparedSourceProgress_holds work earlierInputs finish generated valid started
    trivial producer node 1 (by cbv) rfl (by decide)

-- The exact public key-based exclusion needs neither a caller-supplied owner nor liveness.
example : 1 ∈ reduced.state.queue.rootStreams := by
  have coverage := GeneratedPublicationExclusionTransfer_holds work earlierInputs finish
    generated valid started trivial producer node 1 (by cbv) (by cbv) (by decide) (by cbv)
  exact coverage.2.1

-- Completing the input task does not normally complete its transferred child source.
private def leases : ResourceState :=
  ((ResourceState.empty.set (.stream 1) (.owned (.producer producer))).adopt producer
    [.stream 1]).set
    (.task finisher) (.owned .queue)

private abbrev completed := leases.observeNormalCompletion before.queue finish

example : completed.1 (.task finisher) = .released := by
  exact leases.finishQueueTarget_owned (.task finisher)
    (by simp [leases, ResourceState.set])

example : completed.1 (.stream 1) = .owned .queue := by
  change (leases.finishQueueTarget (.task finisher)).1 (.stream 1) = .owned .queue
  rw [ResourceState.finishQueueTarget_other]
  · simp [leases, ResourceState.set, ResourceState.adopt]
  · simp

example : .cancelSource 1 ∈ reduced.state.cancel.2 := by
  rw [State.cancel_effects]
  have running : reduced.state.stopped = false := rfl
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_flatMap.mpr ⟨.stream 1, transferred.2, List.mem_cons_self⟩

#print axioms GeneratedPublishedBufferTransfer_holds
#print axioms generatedReplay_beforeNext

end AlternativePublicationTransferChecks

namespace AlternativeNewSourceTransferChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence TaskAt)
open GraphQL.IncrementalDelivery.Tests (schema resolvers field defer)

-----------------------------------------------------------------------------------------
-- The same input adopts and immediately publishes a source absent from the old buffer
-----------------------------------------------------------------------------------------

private def group : Execution.DeliveryNode := ⟨0, [], some (.string "P")⟩
private def source : Execution.DeliveryNode := ⟨1, [.field "empty"], none⟩
private def occurrence : Occurrence := .executionGroup [1, 0]

private def value : Execution.ExecutionGroupValue :=
  { deliveryGroups := [group], path := [], data := [("empty", .list [])] }

private def children : Execution.Work :=
  .combine (.combine .empty (.stream source [])) .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨group, []⟩] [] ({ result := .ok (value.data, 0) }) children)
      .empty)

private def event : GraphEvent :=
  .taskSuccess occurrence
    { value, work := ReferenceWorkQueue.Work.fromExecution children [1, 0, 0] }

private abbrev before := State.initialize work
private abbrev snapshot := registrationSnapshot before.queue event
private abbrev reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event

private def node : ReferenceWorkQueue.TaskNode :=
  { task := { occurrence, groups := [group] }, value := some value, childStreams := [1] }

private theorem generated : ReferenceWorkQueue.ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "empty" [] [.stream (.boolean true) none (.int 0)]] (some "P")], ?_⟩
  cbv

private theorem known
    : TaskAt work occurrence [group.ref] none (.object [] (.ok (value.data, 0))) :=
  ⟨_, [], { result := .ok (value.data, 0) }, children, [], rfl, rfl, rfl⟩

private theorem valid : ReferenceWorkQueue.ValidGraphEvents work [event] :=
  .append .nil ⟨_, _, known, rfl, rfl⟩
    (by
      simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities, event])
    ⟨_, _, _, known, by intro other impossible; cases impossible⟩

example
    : (before.queue.taskNode? occurrence).bind ReferenceWorkQueue.TaskNode.value
      = none := by cbv

example : before.queue.stream? source.ref = none := by cbv
example : snapshot.taskNode? occurrence = some node := by cbv
example : reduced.state.queue.taskNode? occurrence = none := by cbv

example : 1 ∈ reduced.state.queue.rootStreams := by
  have coverage := GeneratedPublicationExclusionTransfer_holds work [] event generated valid
    (by cbv) trivial occurrence node 1 (by cbv) (by cbv) (by decide) (by cbv)
  exact coverage.2.1

example
    : 1 ∈ reduced.state.queue.rootStreams ∧ .stream 1 ∈ reduced.state.cleanupTargets := by
  have result := GeneratedPublishedBufferTransfer_holds work [] event generated valid (by cbv)
    occurrence node value 1 group [] [source] (by cbv) rfl (by decide) List.mem_cons_self
    (by cbv; exact List.mem_cons_self) (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
  exact result.2

-- Acquisition is independent; this actual dispatch supplies adoption and task completion.
private def acquired : ResourceState :=
  (ResourceState.empty.set (.task occurrence) (.owned .queue)).set
    (.stream 1) (.owned (.producer occurrence))

private def inventories : ProducerInventories := fun _ => [.stream 1]
private abbrev observed := acquired.observeDispatch inventories before event

example
    : observed.2
      = [.finishNormally (.task occurrence), .adopt occurrence [.stream 1]] := by cbv

example : observed.1 (.task occurrence) = .released := by cbv
example : observed.1 (.stream 1) = .owned .queue := by cbv

-- Same-input acquisition/adoption/publication has a record, not merely a disposal disjunction.
example : RecordTargetRepresented reduced.state.queue (.stream 1) :=
  GeneratedDispatchSourceRepresentation_holds work [] event generated valid (by cbv)
    trivial acquired inventories occurrence node 1 (by cbv) rfl (by decide) (by cbv)

private theorem handoff
    : ResourceReplay ResourceState.empty
        ([.acquire (.task occurrence) .queue, .acquire (.stream 1) (.producer occurrence)]
          ++ observed.2) observed.1 := by
  have initial : ResourceReplay ResourceState.empty
      [.acquire (.task occurrence) .queue, .acquire (.stream 1) (.producer occurrence)] acquired :=
    .cons (.acquire _ _ _ rfl) (.cons (.acquire _ _ _ (by cbv)) (.nil _))
  exact initial.append (acquired.observeDispatch_replay inventories before event)

-- Newly adopted and immediately published does not mean normally exhausted or disposed.
example
    : 1 ∈ reduced.state.queue.rootStreams
      ∨ (.cancelSource 1 ∈ reduced.effects
          ∧ observed.1 (.stream 1) = .cleanupRequested .queue) :=
  (GeneratedDispatchHandoffDisposal_holds work [] event generated valid (by cbv) trivial
    acquired inventories).2
    occurrence occurrence node 1
    (by cbv; exact .head _)
    (by decide)
    (by cbv)
    (by cbv)
    rfl
    (by decide)
    (by cbv)

example
    : (observed.1.observeStop reduced.state).1 (.stream 1)
      = .cleanupRequested .queue := by cbv

#print axioms handoff

end AlternativeNewSourceTransferChecks

#print axioms
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.GeneratedPublicationExclusionTransfer_holds
#print axioms
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.registrationSnapshot_publicationRoots_live
