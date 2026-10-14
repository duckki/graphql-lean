import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceHandoff
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RepresentedStopSafety
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AdoptedSourceRecords

open GraphQL.IncrementalDelivery.Tests

/-! Independent acquisition, actual acceptance labels, incomplete inventories, and stop. -/

namespace AlternativeResourceHandoffChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedDispatchHandoffDisposal := GeneratedDispatchHandoffDisposal_holds

private abbrev producer := SharedOwnerFailure.heldProducer

private def inventories : ProducerInventories :=
  fun owner => if owner = producer then [.stream 2] else []

private def acquired : ResourceState :=
  (ResourceState.empty.set (.task producer) (.owned .queue)).set
    (.stream 2) (.owned (.producer producer))

private def inputs : List (List GraphEvent) := [[SharedOwnerFailure.parentSuccess]]

private abbrev before :=
  ((State.initialize SharedOwnerFailure.work).runNormalized inputs).1

private abbrev observed :=
  acquired.observeDispatch inventories before SharedOwnerFailure.success

private abbrev after :=
  ((State.initialize SharedOwnerFailure.work).runNormalized
    (inputs ++ [[SharedOwnerFailure.success]])).1

-----------------------------------------------------------------------------------------
-- Acquisitions precede dispatch; actual accepting labels construct the handoff
-----------------------------------------------------------------------------------------

private theorem acquisition
    : ResourceReplay ResourceState.empty
        [.acquire (.task producer) .queue, .acquire (.stream 2) (.producer producer)]
        acquired :=
  .cons (.acquire _ _ _ rfl) (.cons (.acquire _ _ _ (by cbv)) (.nil _))

private theorem labels
    : graphEffects before.queue SharedOwnerFailure.success = [.adopt producer] := by
  dsimp only [before]
  rw [SharedOwnerFailure.work_shape]
  cbv

private theorem complete
    : CompleteAdoptionInventories acquired inventories
        (graphEffects before.queue SharedOwnerFailure.success) := by
  rw [labels]
  intro owner emitted target owned
  have same := List.mem_singleton.mp emitted
  cases same
  by_cases stream : target = .stream 2
  · simp [inventories, stream]
  · by_cases task : target = .task producer
    · subst target; simp [acquired, ResourceState.set] at owned
    · simp [acquired, ResourceState.set, ResourceState.empty, stream, task] at owned

example
    : observed.2 = [.finishNormally (.task producer), .adopt producer [.stream 2]] := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example : observed.1 (.task producer) = .released := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example : observed.1 (.stream 2) = .owned .queue := by
  dsimp only [observed, before]
  rw [SharedOwnerFailure.work_shape]
  cbv

-- This is one compatible history, not an independently chosen legal adoption script.
private theorem actualHandoff
    : ResourceReplay ResourceState.empty
        ([.acquire (.task producer) .queue, .acquire (.stream 2) (.producer producer)]
          ++ observed.2) observed.1 :=
  acquisition.append
    (acquired.observeDispatch_replay inventories before SharedOwnerFailure.success)

private theorem representation : ResourcesRepresented after.queue observed.1 := by
  intro target owned
  by_cases same : target = .stream 2
  · subst target
    let snapshot := registrationSnapshot before.queue SharedOwnerFailure.success
    let node := (snapshot.taskNode? producer).getD { task := { occurrence := producer, groups := [] } }
    have progress := GeneratedDispatchSourceRepresentation_holds SharedOwnerFailure.work inputs
      SharedOwnerFailure.success SharedOwnerFailure.executed
      (SharedOwnerFailure.valid_events.prefix ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩)
      (by rw [SharedOwnerFailure.work_shape]; cbv) trivial acquired inventories producer node 2
      (by dsimp only [node, snapshot, before]; rw [SharedOwnerFailure.work_shape]; cbv)
      (by dsimp only [node, snapshot, before]; rw [SharedOwnerFailure.work_shape]; cbv)
      (by dsimp only [node, snapshot, before]; rw [SharedOwnerFailure.work_shape]; cbv; exact .head _)
      owned
    have sameQueue : after.queue =
        (({ state := before } : GraphBatchResult).handleGraphEvent SharedOwnerFailure.success).state.queue := by
      dsimp only [after, before]
      rw [SharedOwnerFailure.work_shape]
      cbv
    rw [sameQueue]
    exact progress
  · by_cases task : target = .task producer
    · subst target
      dsimp only [observed, before] at owned
      rw [SharedOwnerFailure.work_shape] at owned
      cbv at owned; cases owned
    · have absent := acquired.observeDispatch_unacquired inventories before SharedOwnerFailure.success
        target (by simp [acquired, ResourceState.set, ResourceState.empty, same, task])
      rw [absent] at owned
      cases owned

-- Structural source identity supplies registration evidence without any assumed node lookup.
private theorem sourceIdentity
    : ∃ dependencies,
        WorkQueueSemantics.NodeAt SharedOwnerFailure.work SharedOwnerFailure.source
          .stream dependencies (some producer) :=
  SharedOwnerFailure.success_matches.childStream_producer
    (stream := ⟨SharedOwnerFailure.source⟩) (by cbv; exact .head _)

private theorem incomingSources
    : ProducerSourcesMatchWork SharedOwnerFailure.work acquired inventories
        (graphEffects before.queue SharedOwnerFailure.success) := by
  rw [labels]
  intro owner key emitted listed _
  have sameOwner : owner = producer := HostEffect.adopt.inj (List.mem_singleton.mp emitted)
  subst owner
  have sameKey : key = 2 := by simpa [inventories] using listed
  subst key
  obtain ⟨dependencies, known⟩ := sourceIdentity
  exact ⟨SharedOwnerFailure.source, dependencies, rfl, known⟩

private theorem sourcesRepresented
    : SourcesRepresented
        (({ state := before } : GraphBatchResult).handleGraphEvent
          SharedOwnerFailure.success).state.queue
        observed.1 := by
  apply GeneratedDispatchSourcesRepresented_holds SharedOwnerFailure.work inputs
    SharedOwnerFailure.success SharedOwnerFailure.executed
    (SharedOwnerFailure.valid_events.prefix
      ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩)
    (by rw [SharedOwnerFailure.work_shape]; cbv) acquired inventories _ incomingSources
  intro key owned
  by_cases same : key = 2
  · simp [acquired, ResourceState.set, same] at owned
  · simp [acquired, ResourceState.set, ResourceState.empty, same] at owned

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        (inputs ++ [[SharedOwnerFailure.success]]).flatten :=
  SharedOwnerFailure.valid_events.prefix
    ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩

private theorem stopped
    : ∀ target, (observed.1.observeStop after).1 target ≠ .owned .queue :=
  (GeneratedRepresentedStopSafety_holds SharedOwnerFailure.work
    (inputs ++ [[SharedOwnerFailure.success]])
    SharedOwnerFailure.executed valid
    (by rw [SharedOwnerFailure.work_shape]; cbv)
    observed.1 representation
    (by rw [SharedOwnerFailure.work_shape]; cbv)).2

example
    : ResourceReplay ResourceState.empty
        (([.acquire (.task producer) .queue, .acquire (.stream 2) (.producer producer)]
            ++ observed.2)
          ++ (observed.1.observeStop after).2)
        (observed.1.observeStop after).1 :=
  actualHandoff.append (observed.1.observeStop_replay after)

-----------------------------------------------------------------------------------------
-- Omitted identities remain producer-owned; legality does not imply complete handoff
-----------------------------------------------------------------------------------------

private def incomplete : ResourceState :=
  acquired.set (.stream 9) (.owned (.producer producer))

example
    : ¬CompleteAdoptionInventories incomplete inventories
        (graphEffects before.queue SharedOwnerFailure.success) := by
  intro all
  have listed := all producer (by rw [labels]; exact .head _) (.stream 9)
    (by simp [incomplete, ResourceState.set])
  simp [inventories] at listed

example
    : (incomplete.observeAdoptions inventories [.adopt producer]).1 (.stream 9)
      = .owned (.producer producer) := by cbv

-- Acknowledgement/cancellation labels alone do not relinquish producer-owned work.
example
    : (acquired.observeAdoptions inventories [.acknowledge 2, .cancelSource 2]).1
        (.stream 2)
      = .owned (.producer producer) := by cbv

-- An ignored task success has no adoption label, despite a supplied producer inventory.
example
    : (acquired.observeDispatch inventories { queue := {} } SharedOwnerFailure.success).1
        (.stream 2)
      = .owned (.producer producer) := by cbv

-- Repeated labels do not reacquire anything or transfer another producer's lease.
private def foreign : ResourceState :=
  acquired.set (.stream 2) (.owned (.producer (.executionGroup [999])))

example
    : (foreign.observeAdoptions inventories [.adopt producer, .adopt producer]).1
        (.stream 2)
      = .owned (.producer (.executionGroup [999])) := by cbv

example
    : (ResourceState.empty.observeAdoptions inventories [.adopt producer]).1 (.stream 2)
      = .unacquired := by cbv

-----------------------------------------------------------------------------------------
-- Item adoption follows FIFO receipt order and disappears when the source is inactive
-----------------------------------------------------------------------------------------

private def itemProducer : WorkQueueSemantics.Occurrence := .item [] 0
private def nextProducer : WorkQueueSemantics.Occurrence := .item [] 1
private def source : Execution.DeliveryNode := ⟨7, [], none⟩

private def item : ReferenceWorkQueue.StreamItem :=
  { occurrence := itemProducer, value := { item := .null } }

private def nextItem : ReferenceWorkQueue.StreamItem :=
  { item with occurrence := nextProducer }

private def itemInventories : ProducerInventories := fun _ => []

example
    : (ResourceState.empty.observeDispatch itemInventories
        { queue := { rootStreams := [7] } } (.streamItems source [item, nextItem])).2
      = [.adopt itemProducer [], .adopt nextProducer []] := by cbv

example
    : graphEffects ({} : ReferenceWorkQueue.State) (.streamItems source [item, nextItem])
      = [.acknowledge 7] := by cbv

example
    : (ResourceState.empty.observeDispatch itemInventories
        { queue := {} } (.streamItems source [item, nextItem])).2
      = [] := by cbv

#print axioms GeneratedDispatchHandoffDisposal_holds
#print axioms ResourceState.observeDispatch_replay
#print axioms ResourceState.observeDispatch_actions
#print axioms ResourceState.observeAdoptions_no_producer
#print axioms actualHandoff
#print axioms stopped
#print axioms GeneratedDispatchSourceRepresentation_holds
#print axioms sourcesRepresented

end AlternativeResourceHandoffChecks
