import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceAuditConstruction
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceLifecycleCounts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResponseResourceSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceEffectTrace
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

/-! Nonvacuous generated acquisition/adoption/failure/terminal trace uses the universal prefix root. -/

namespace AlternativeResourcePrefixChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

private def acquired :=
  ResourceState.empty.set (.stream 2) (.owned (.producer SharedOwnerFailure.heldProducer))

private def inventories : ProducerInventories :=
  fun producer =>
    if producer = SharedOwnerFailure.heldProducer then [.stream 2] else []

private def acquisition : List ResourceAction :=
  [.acquire (.stream 2) (.producer SharedOwnerFailure.heldProducer)]

private theorem tasks (resources : ResourceState) (effects : List HostEffect)
    : ProducerTasksMatchWork SharedOwnerFailure.work resources inventories effects := by
  intro producer occurrence _ listed _
  simp only [inventories] at listed
  split at listed <;> simp at listed

private theorem sources (resources : ResourceState) (effects : List HostEffect)
    : ProducerSourcesMatchWork SharedOwnerFailure.work resources inventories effects := by
  intro producer key _ listed _
  simp only [inventories] at listed
  split at listed
  · rename_i same
    subst producer
    have sameKey : key = 2 := by simpa using listed
    subst key
    obtain ⟨dependencies, known⟩ := SharedOwnerFailure.success_matches.childStream_producer
      (stream := ⟨SharedOwnerFailure.source⟩) (by cbv; exact .head _)
    exact ⟨SharedOwnerFailure.source, dependencies, rfl, known⟩
  · cases listed

private theorem initial
    : ResourcePrefixConstruction SharedOwnerFailure.work [] acquired acquisition := by
  apply ResourcePrefixConstruction.initial
  · exact .cons (.acquire _ _ _ rfl) (.nil _)
  · constructor
    · intro occurrence owned
      simp [acquired, ResourceState.set, ResourceState.empty] at owned
    · intro key owned
      by_cases same : key = 2
      · simp [acquired, ResourceState.set, same] at owned
      · simp [acquired, ResourceState.set, ResourceState.empty, same] at owned

private def first :=
  State.observeResourceBatch (State.initialize SharedOwnerFailure.work) acquired
    inventories [SharedOwnerFailure.parentSuccess]

private def second :=
  State.observeResourceBatch
    ((State.initialize SharedOwnerFailure.work).runNormalized
      [[SharedOwnerFailure.parentSuccess]]).1
    first.resources inventories [SharedOwnerFailure.success]

private def third :=
  State.observeResourceBatch
    ((State.initialize SharedOwnerFailure.work).runNormalized
      [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]).1
    second.resources inventories [SharedOwnerFailure.failureG]

private def fourth :=
  State.observeResourceBatch
    ((State.initialize SharedOwnerFailure.work).runNormalized
      [
        [SharedOwnerFailure.parentSuccess],
        [SharedOwnerFailure.success],
        [SharedOwnerFailure.failureG]
      ]).1
    third.resources inventories [SharedOwnerFailure.failureH]

private theorem firstBuilt
    : ResourcePrefixConstruction SharedOwnerFailure.work
        [[SharedOwnerFailure.parentSuccess]] first.resources
        (acquisition ++ first.actions) := by
  simpa only [first, State.runNormalized, List.foldl_nil, List.append_nil,
    List.nil_append]
    using ResourcePrefixConstruction.append initial SharedOwnerFailure.parentSuccess
      inventories acquired []
      (.nil _)
      (by simp)
      (SharedOwnerFailure.valid_events.prefix
        ⟨
          [
            SharedOwnerFailure.success,
            SharedOwnerFailure.failureG,
            SharedOwnerFailure.failureH
          ],
          rfl
        ⟩)
      (by rw [SharedOwnerFailure.work_shape]; cbv)
      (tasks _ _)
      (sources _ _)

private theorem secondBuilt
    : ResourcePrefixConstruction SharedOwnerFailure.work
        [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]
        second.resources ((acquisition ++ first.actions) ++ second.actions) := by
  simpa only [second, List.cons_append, List.nil_append, List.append_nil]
    using
      ResourcePrefixConstruction.append firstBuilt SharedOwnerFailure.success inventories
        first.resources []
        (.nil _)
        (by simp)
        (SharedOwnerFailure.valid_events.prefix
          ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩)
        (by rw [SharedOwnerFailure.work_shape]; cbv)
        (tasks _ _)
        (sources _ _)

private theorem thirdBuilt
    : ResourcePrefixConstruction SharedOwnerFailure.work
        [
          [SharedOwnerFailure.parentSuccess],
          [SharedOwnerFailure.success],
          [SharedOwnerFailure.failureG]
        ]
        third.resources
        (((acquisition ++ first.actions) ++ second.actions) ++ third.actions) := by
  simpa only [third, List.cons_append, List.nil_append, List.append_nil]
    using ResourcePrefixConstruction.append secondBuilt SharedOwnerFailure.failureG
      inventories second.resources []
      (.nil _)
      (by simp)
      (SharedOwnerFailure.valid_events.prefix ⟨[SharedOwnerFailure.failureH], rfl⟩)
      (by rw [SharedOwnerFailure.work_shape]; cbv)
      (tasks _ _)
      (sources _ _)

private theorem fourthBuilt
    : ResourcePrefixConstruction SharedOwnerFailure.work SharedOwnerFailure.inputs
        fourth.resources
        ((((acquisition ++ first.actions) ++ second.actions) ++ third.actions)
          ++ fourth.actions) := by
  simpa only [fourth, SharedOwnerFailure.inputs, List.cons_append, List.nil_append,
    List.append_nil]
    using ResourcePrefixConstruction.append thirdBuilt SharedOwnerFailure.failureH
      inventories third.resources [] (.nil _) (by simp) SharedOwnerFailure.valid_events
      SharedOwnerFailure.started (tasks _ _) (sources _ _)

-- Endpoint records and stop safety follow the same actual acquired/adopted trace.
example : ResourcesRepresented second.dispatch.state.queue second.resources := by
  have represented := (secondBuilt.invariants SharedOwnerFailure.executed).2.1.records
  have same := State.observeResourceSingleton_state
    ((State.initialize SharedOwnerFailure.work).runNormalized [[SharedOwnerFailure.parentSuccess]]).1
    first.resources inventories SharedOwnerFailure.success
  rw [← State.runNormalized_append_state] at same
  exact same.symm ▸ represented

example : ∀ target, fourth.resources target ≠ .owned .queue := by
  apply (fourthBuilt.invariants SharedOwnerFailure.executed).2.2
  rw [SharedOwnerFailure.work_shape]
  cbv

example : fourth.resources (.stream 2) = .cleanupRequested .queue := by
  unfold fourth third second first
  rw [SharedOwnerFailure.work_shape]
  cbv

-- Account for the acquisition made after the empty initial resource state, not just
-- resources already owned before the history began.
example : fourth.resources (.stream 2) ≠ .unacquired :=
  fourthBuilt.acquisition_accounted SharedOwnerFailure.executed
    (owner := .producer SharedOwnerFailure.heldProducer) (by simp [acquisition])

private def fullActions :=
  (((acquisition ++ first.actions) ++ second.actions) ++ third.actions) ++ fourth.actions

-- These are observed resource-action counts, not counts of host abort labels or
-- asynchronous callbacks. The pending request has neither vanished nor settled.
example : fullActions.countP (ResourceMilestone.acquisition.matches (.stream 2)) = 1 := by
  unfold fullActions fourth third second first
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : fullActions.countP (ResourceMilestone.cleanupRequest.matches (.stream 2)) = 1 := by
  unfold fullActions fourth third second first
  rw [SharedOwnerFailure.work_shape]
  cbv

example : fullActions.countP (ResourceMilestone.release.matches (.stream 2)) = 0 := by
  unfold fullActions fourth third second first
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : (fullActions
        ++ (fourth.resources.observeStop
              ((State.initialize SharedOwnerFailure.work).runNormalized
                SharedOwnerFailure.inputs).1).2).countP
        (ResourceMilestone.cleanupRequest.matches (.stream 2))
      ≤ 1 :=
  fourthBuilt.stop_milestoneCount_le_one SharedOwnerFailure.executed .cleanupRequest
    (.stream 2)

private def representedAudit : AuditWitness :=
  {
    queue :=
      ((State.initialize SharedOwnerFailure.work).runNormalized
        [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]).1
    resourcesBefore := ResourceState.empty
    resourceActions := (acquisition ++ first.actions) ++ second.actions
    resourcesAfter := second.resources
    receiptBefore := Receipt.initialize 0 2 []
    receiptActions := []
    receiptAfter := Receipt.initialize 0 2 []
    cleanupBefore := {}
    cleanupActions := []
    cleanupAfter := {}
  }

private theorem representedAuditValid : representedAudit.Valid :=
  representedAudit.valid_of_resourcePrefix SharedOwnerFailure.executed secondBuilt rfl rfl
    (Receipt.initialize_valid _ _ _) (.nil _) CleanupTracker.empty_valid (.nil _)

-- A nonempty independently acquired queue lease receives coverage from the generated
-- prefix; the audit does not assume its presence in cleanupTargets.
example : second.resources (.stream 2) = .owned .queue := by
  unfold second first
  rw [SharedOwnerFailure.work_shape]
  cbv

example : representedAudit.LocalSafety :=
  representedAudit.localSafety representedAuditValid

example
    : .stream 2 ∈ representedAudit.queue.cancel.2.filterMap HostEffect.cleanupStart? := by
  apply (representedAudit.localSafety representedAuditValid).2.2.1
  · unfold representedAudit
    rw [SharedOwnerFailure.work_shape]
    cbv
  · unfold representedAudit second first
    rw [SharedOwnerFailure.work_shape]
    cbv

private def response : Execution.Response := { data := .object [] }

private def liveReader :=
  ((ResponseStreamCursor.buildResponse response SharedOwnerFailure.work).2.run
    [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]).2.1

-- The actual response mapper, not a separately chosen queue, carries the held lease.
example : StopCoverage liveReader.queue second.resources :=
  (secondBuilt.readerSafety SharedOwnerFailure.executed response).2.1

example
    : ∀ target,
        (second.resources.observeReaderClose liveReader).1 target ≠ .owned .queue :=
  (secondBuilt.readerCloseSafety SharedOwnerFailure.executed response).2

example
    : (second.resources.observeReaderClose liveReader).1 (.stream 2)
      = .cleanupRequested .queue := by
  unfold liveReader second first
  rw [SharedOwnerFailure.work_shape]
  cbv

example : liveReader.close.1.queue.queue.terminated = false := by
  unfold liveReader
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : ((acquisition ++ first.actions)
        ++ second.actions
        ++ (second.resources.observeReaderClose liveReader).2).countP
        (ResourceMilestone.cleanupRequest.matches (.stream 2))
      ≤ 1 :=
  (secondBuilt.readerCloseSafety SharedOwnerFailure.executed
    response).1.milestoneCount_le_one
    .cleanupRequest (.stream 2)

-- An already-finished reader cannot synthesize late cleanup of a malformed raw inventory.
-- The constructed-prefix premise, not this guard alone, establishes terminal safety.
example
    : (second.resources.observeReaderClose { liveReader with finished := true }).1
        (.stream 2)
      = .owned .queue := by
  unfold second first
  rw [SharedOwnerFailure.work_shape]
  cbv

private def finalReader :=
  ((ResponseStreamCursor.buildResponse response SharedOwnerFailure.work).2.run
    SharedOwnerFailure.inputs).2.1

example : (fourth.resources.observeReaderClose finalReader).2 = [] := by
  unfold finalReader
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : ∀ target,
        (fourth.resources.observeReaderClose finalReader).1 target ≠ .owned .queue :=
  (fourthBuilt.readerCloseSafety SharedOwnerFailure.executed response).2

private def readerObserved :=
  ResponseStreamCursor.observeResourceRun
    (ResponseStreamCursor.buildResponse response SharedOwnerFailure.work).2 acquired
    inventories [SharedOwnerFailure.inputs.flatten]

example
    : readerObserved.cursor
      = ((ResponseStreamCursor.buildResponse response SharedOwnerFailure.work).2.run
          [SharedOwnerFailure.inputs.flatten]).2.1 :=
  (ResponseStreamCursor.observeResourceRun_projection _ _ _ _).1

example
    : EffectObservationsCovered readerObserved.actions
        ((ResponseStreamCursor.buildResponse response SharedOwnerFailure.work).2.run
          [SharedOwnerFailure.inputs.flatten]).2.2 :=
  (ResponseStreamCursor.observeResourceRun_safety _ _ _ _).2

example : readerObserved.resources (.stream 2) = .cleanupRequested .queue := by
  unfold readerObserved SharedOwnerFailure.inputs
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : .stream 2
      ∈ (((ResponseStreamCursor.buildResponse response SharedOwnerFailure.work).2.run
            [SharedOwnerFailure.inputs.flatten]).2.2.filterMap
          HostEffect.cleanupStart?) := by
  apply (ResponseStreamCursor.observeResourceRun_safety _ acquired inventories [SharedOwnerFailure.inputs.flatten]).2.2
  unfold ResponseStreamCursor.observeResourceRun SharedOwnerFailure.inputs
  rw [SharedOwnerFailure.work_shape]
  cbv
  exact .tail _ (.tail _ (.head _))

example
    : ResourceReplay acquired
        (readerObserved.actions
          ++ (readerObserved.resources.observeReaderClose readerObserved.cursor).2)
        (readerObserved.resources.observeReaderClose readerObserved.cursor).1 :=
  (ResponseStreamCursor.observeResourceRun_close_safety _ _ _ _).1

-- A late result after actual close cannot secretly adopt, finish or request cleanup.
example
    : acquired.observeReaderBatch liveReader.close.1 inventories
        [SharedOwnerFailure.success]
      = (acquired, []) := by
  simp [ResourceState.observeReaderBatch]

private def wide :=
  State.observeResourceBatch (State.initialize SharedOwnerFailure.work) acquired
    inventories SharedOwnerFailure.inputs.flatten

private theorem wideBuilt
    : ResourcePrefixConstruction SharedOwnerFailure.work
        [SharedOwnerFailure.inputs.flatten] wide.resources
        (acquisition ++ wide.actions) := by
  simpa only [wide, State.runNormalized, List.foldl_nil, List.append_nil, List.nil_append]
    using ResourcePrefixConstruction.appendBatch initial SharedOwnerFailure.inputs.flatten
      inventories acquired []
      (.nil _)
      (by simp)
      SharedOwnerFailure.valid_events
      (by rw [SharedOwnerFailure.work_shape]; cbv)
      (by intro earlier event later _; exact ⟨tasks _ _, sources _ _⟩)

-- One FIFO batch contains acquisition handoff and both shared-owner failures. The
-- universal construction, not a separately supplied cleanup law, proves its endpoint.
example
    : ResourceReplay ResourceState.empty (acquisition ++ wide.actions) wide.resources :=
  (wideBuilt.invariants SharedOwnerFailure.executed).1

example : ResourcesRepresented wide.dispatch.state.queue wide.resources := by
  have represented := (wideBuilt.invariants SharedOwnerFailure.executed).2.1.records
  have same := State.observeResourceBatch_state (State.initialize SharedOwnerFailure.work)
    acquired inventories SharedOwnerFailure.inputs.flatten
  exact same.symm ▸ represented

example : ∀ target, wide.resources target ≠ .owned .queue := by
  apply (wideBuilt.invariants SharedOwnerFailure.executed).2.2
  rw [SharedOwnerFailure.work_shape]
  cbv

example : wide.resources (.stream 2) = .cleanupRequested .queue := by
  unfold wide
  rw [SharedOwnerFailure.work_shape]
  cbv

private def lateSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [1, 0, 0, 0, 1, 1, 0])
    {
      value :=
        {
          deliveryGroups := [SharedOwnerFailure.groupH],
          path := [.field "box"],
          data := [("dummy", .scalar "ok")]
        }
      work :=
        ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty)
          [1, 0, 0, 0, 1, 1, 0, 0]
    }

private theorem lateKnown
    : WorkQueueSemantics.TaskAt SharedOwnerFailure.work
        (.executionGroup [1, 0, 0, 0, 1, 1, 0]) [1]
        (some (.executionGroup [1, 0]))
        (.object [.field "box"] (.ok ([("dummy", .scalar "ok")], 0))) := by
  refine ⟨[{ node := SharedOwnerFailure.groupH }], [.field "box"],
    .ok ([("dummy", .scalar "ok")], 0), .combine .empty .empty, [0, 1], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

private theorem lateValid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        (SharedOwnerFailure.inputs.flatten ++ [lateSuccess]) := by
  apply ReferenceWorkQueue.ValidGraphEvents.append SharedOwnerFailure.valid_events
  · refine ⟨[1], some (.executionGroup [1, 0]), lateKnown, ?_, ?_⟩
    all_goals rw [SharedOwnerFailure.work_shape]; rfl
  · cbv
    decide
  · refine ⟨[1], some (.executionGroup [1, 0]), _, lateKnown, ?_⟩
    intro producer same
    cases same
    cbv
    exact .head _

-- Matching/ready source evidence alone does not admit a late task result whose
-- runtime record was removed. The start contract rejects it within this same batch.
example
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        (SharedOwnerFailure.inputs.flatten ++ [lateSuccess]) :=
  lateValid

example
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work
        [SharedOwnerFailure.inputs.flatten ++ [lateSuccess]]
      = false := by
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : .adopt (.executionGroup [1, 0, 0, 0, 1, 1, 0])
      ∉ graphEffects
          ((ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution
                SharedOwnerFailure.work)).replayGraphEvents
            SharedOwnerFailure.inputs.flatten) lateSuccess := by
  rw [SharedOwnerFailure.work_shape]
  cbv
  intro impossible
  cases impossible

#print axioms graphEffects_emptyRoots_noAdopt
#print axioms generatedRaw_resourceInvariant
#print axioms State.handleGraphEvent_terminated
#print axioms State.handleGraphEvents_flagsAligned
#print axioms State.runNormalized_stopped_eq_terminated
#print axioms generatedRaw_resourceFold
#print axioms GeneratedResourceBatchInvariant_holds
#print axioms ResourcePrefixConstruction.invariants
#print axioms ResourcePrefixConstruction.stopSafety
#print axioms ResourceReplay.acquisition_accounted
#print axioms ResourcePrefixConstruction.stopCoverage
#print axioms AuditWitness.valid_of_resourcePrefix
#print axioms representedAuditValid
#print axioms ResourceReplay.milestoneCount_le_one
#print axioms ResourcePrefixConstruction.stop_milestoneCount_le_one
#print axioms ResponseStreamCursor.run_buildResponse_queue
#print axioms ResponseStreamCursor.run_buildResponse_finished
#print axioms ResourcePrefixConstruction.readerSafety
#print axioms ResourcePrefixConstruction.readerCloseSafety
#print axioms ResourceState.observeReaderClose_requests
#print axioms State.observeResourceBatch_effectCoverage
#print axioms ResponseStreamCursor.observeResourceRun_projection
#print axioms ResponseStreamCursor.observeResourceRun_safety
#print axioms ResponseStreamCursor.observeResourceRun_close_safety

end AlternativeResourcePrefixChecks
