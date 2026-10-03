import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTaskProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicHandlerBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeTaskProducers

/-! Successful group carriers retain concrete unpublished task contents on one matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A noticed descriptor retains unpublished tasks and supported cached errors together.
The queue record and contents facts share one emitting boundary. `failed` is the
visible accepted inventory; `received` supplies successful registration prerequisites.
The prerequisites concern source success, not already-published producer values. This package
is derived evidence, not a source assumption or scheduler-contract premise.
-/
def RetainedNoticeContents (work : Execution.Work) (matching : PublicationMatching)
    (events : List Execution.WorkQueueEvent) (failed : List Occurrence)
    (received : List GraphEvent) (child : Execution.DeliveryNode)
    : Prop :=
  (∃ dependencies producer, NodeAt work child .group dependencies producer)
  ∧ ∃ queue : State,
    ∃ node : GroupNode,
      queue.groupNode? child.ref = some node
      ∧ node.group.node = child
      ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
      ∧ queue.GroupMembershipSound
      ∧ queue.RegisteredTasksMatch work
      ∧ queue.CachedFailuresSupported work failed
      ∧ TaskProducersSucceeded work queue.tasks received
      ∧ ∀ occurrence ∈ node.tasks, ¬Published matching events occurrence

/-- Concrete retained contents supply a visible failure or a real unpublished contributor.
Witness: a cache supplies its accepted contributor at the same cut. Without a cache,
pruning retained a nonempty task list, whose sound membership and registered descriptor
give the original work occurrence. Producer readiness still decides cancellation safety.
-/
theorem RetainedNoticeContents.recorded_or_unpublished
    {work matching events failures cut received child}
    (contents
      : RetainedNoticeContents work matching events (failedBefore failures cut) received
          child)
    : HasRecordedFailure work failures cut child.ref
      ∨ ∃ occurrence owners,
          TaskHasOwners work occurrence owners
          ∧ child.ref ∈ owners
          ∧ ¬Published matching events occurrence := by
  obtain ⟨_, queue, node, found, same, retained, sound, registered, cached,
    _, unpublished⟩ := contents
  have member := List.mem_of_find?_eq_some found
  by_cases present : node.failure.isSome = true
  · left
    rw [← same]
    exact cached.recorded (List.Subset.refl _) member present
  · obtain ⟨occurrence, listed⟩ := List.exists_mem_of_ne_nil _ (retained.resolve_right present)
    obtain ⟨task, taskMember, sameTask, owner⟩ := sound node member occurrence listed
    obtain ⟨_, payload, producer, _, known⟩ := (registered task taskMember).1
    rw [sameTask] at known
    exact .inr ⟨occurrence, _, ⟨producer, payload, known⟩, same ▸ owner,
      unpublished occurrence listed⟩

-----------------------------------------------------------------------------------------
-- Task-success notices come from the owner fold or the subsequent recursive drain
-----------------------------------------------------------------------------------------

/-- A task-success carrier has retained unpublished contents at its own emitting boundary.
Witness: invert the accepted handler and split its indexed output between the owner fold
and drain. Each branch uses that exact boundary's metadata and the common publication
ledger, never the final queue after later owners or drain iterations.
-/
theorem ExecutedWork.taskSuccess_groupNotice_unpublished
    {work before occurrence result after published inputs w cut index group groups streams
      child failed}
    (generated : ExecutedWork work)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .taskSuccess occurrence result :: after) published)
    (valid : ValidGraphEvents work (before ++ .taskSuccess occurrence result :: after))
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (ready : ConformancePlan.StreamPublicationReady work w)
    (cached
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).CachedFailuresSupported
          work failed)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      ((current.taskSuccess occurrence result).2)[index]?
        = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ((w.events.take cut).flatMap normalizedObjectValues).length
        = (((State.initialize (Work.fromExecution work)).rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length
          + (((current.taskSuccess occurrence result).2.take index).flatMap
              WorkQueueEvent.objectValues).length
      → RetainedNoticeContents work w.matching (w.events.take cut) failed
          (before ++ .taskSuccess occurrence result :: after) child := by
  intro current selected noticed count
  have prior := valid.prefix (List.prefix_append before (.taskSuccess occurrence result :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.taskSuccess occurrence result]).IsPrefix
      (before ++ GraphEvent.taskSuccess occurrence result :: after) from ⟨after, by simp⟩)
  cases found : current.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found, List.getElem?_nil, reduceCtorEq] at selected
  | some incoming =>
      cases healthy : current.taskHasHealthyOwner incoming.task with
      | false =>
          rw [current.taskSuccess_eq occurrence result incoming found] at selected
          simp only [healthy, Bool.not_false, ↓reduceIte, List.getElem?_nil,
            reduceCtorEq] at selected
      | true =>
          let stored := current.putTaskNode { incoming with value := some result.value }
          let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
          let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
          let active := released.1.startNewWork released.2.2
          have preparedReady := createWorkQueue_taskSuccess_prepared_producersSucceeded
            valid incoming
          have storedCached : stored.CachedFailuresSupported work failed := cached
          have preparedCached := storedCached.maybeIntegrateWork result.work (some occurrence)
          have output : (current.taskSuccess occurrence result).2
              = released.2.1 ++ active.drainReadyGroups.2 := by
            rw [current.taskSuccess_eq occurrence result incoming found]
            simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rfl
          rw [output] at selected count
          by_cases inFold : index < released.2.1.length
          · rw [List.getElem?_append_left inFold] at selected
            obtain ⟨steps, _, _, located, node, lookup, same, contents, excluded⟩ :=
              generated.taskSuccess_ownerNoticeContents covered valid found healthy selected noticed
            obtain ⟨sound, registered⟩ :=
              createWorkQueue_taskSuccess_prepared_noticeTaskProvenance
                (fun _ member => prior.eachMatches member) matching incoming
            obtain ⟨boundarySound, boundaryRegistered⟩ :=
              State.successGroupFold_noticeTaskProvenance sound registered
                (incoming.task.groups.take (steps + 1))
            refine ⟨located, _, node, lookup, same, contents,
              boundarySound, boundaryRegistered,
              preparedCached.successGroupFold (incoming.task.groups.take (steps + 1)),
              preparedReady.successGroupFold (incoming.task.groups.take (steps + 1)), ?_⟩
            apply ConformancePlan.retainedGroupMembers_unpublished ledger objects ready
              boundarySound boundaryRegistered (List.mem_of_find?_eq_some lookup)
            rw [List.take_append_of_le_length (Nat.le_of_lt inFold)] at count
            simpa only [count] using excluded
          · have inDrain : released.2.1.length ≤ index := by omega
            rw [List.getElem?_append_right inDrain] at selected
            obtain ⟨steps, _, _, located, node, lookup, same, contents, excluded⟩ :=
              generated.taskSuccess_drainNoticeContents covered valid found healthy selected noticed
            obtain ⟨sound, registered⟩ := createWorkQueue_taskSuccess_drain_noticeTaskProvenance
              (fun _ member => prior.eachMatches member) matching incoming
            obtain ⟨boundarySound, boundaryRegistered⟩ :=
              State.drainReadyGroups_go_noticeTaskProvenance sound registered (steps + 1)
            refine ⟨located, _, node, lookup, same, contents,
              boundarySound, boundaryRegistered,
              ((preparedCached.successGroupFold incoming.task.groups).startNewWork
                released.2.2).drainReadyGroups_go (steps + 1),
              ((preparedReady.successGroupFold incoming.task.groups).startNewWork
                released.2.2).drainReadyGroups_go (steps + 1), ?_⟩
            apply ConformancePlan.retainedGroupMembers_unpublished ledger objects ready
              boundarySound boundaryRegistered (List.mem_of_find?_eq_some lookup)
            rw [List.take_append, List.take_of_length_le inDrain] at count
            simpa only [count] using excluded

-----------------------------------------------------------------------------------------
-- Item handlers carry successful group notices only in their post-item drain
-----------------------------------------------------------------------------------------

/-- An item handler's group carrier retains unpublished contents at its actual drain step.
Witness: its leading stream-value event cannot be a group completion and adds no object
offset. Prepared task metadata and the same ledger survive each earlier drain iteration.
-/
theorem ExecutedWork.streamItems_groupNotice_unpublished
    {work before stream items after published inputs w cut index group groups streams
      child failed}
    (generated : ExecutedWork work)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .streamItems stream items :: after) published)
    (valid : ValidGraphEvents work (before ++ .streamItems stream items :: after))
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (ready : ConformancePlan.StreamPublicationReady work w)
    (cached
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).CachedFailuresSupported
          work failed)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      ((current.streamItems stream items).2)[index]?
        = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ((w.events.take cut).flatMap normalizedObjectValues).length
        = (((State.initialize (Work.fromExecution work)).rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length
          + (((current.streamItems stream items).2.take index).flatMap
              WorkQueueEvent.objectValues).length
      → RetainedNoticeContents work w.matching (w.events.take cut) failed
          (before ++ .streamItems stream items :: after) child := by
  intro current selected noticed count
  have prior := valid.prefix (List.prefix_append before (.streamItems stream items :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.streamItems stream items]).IsPrefix
      (before ++ GraphEvent.streamItems stream items :: after) from ⟨after, by simp⟩)
  have sourceReady := (createWorkQueue_replayGraphEvents_producerOrder prior).1.mono
    (List.subset_append_left before (.streamItems stream items :: after))
  rw [current.streamItems_eq stream items] at selected count
  cases active : current.rootStreams.contains stream.ref with
  | false =>
      simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil, reduceCtorEq] at selected
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at selected count
      cases index with
      | zero => cases selected
      | succ index =>
          obtain ⟨steps, _, _, located, node, lookup, same, contents, excluded⟩ :=
            generated.streamItems_drainNoticeContents covered valid active selected noticed
          obtain ⟨sound, registered⟩ := State.replay_noticeTaskProvenance
            (createWorkQueue_groupMembershipSound _)
            (createWorkQueue_fromSpec_registeredTasksMatch work) before
            (fun _ member => prior.eachMatches member)
          obtain ⟨preparedSound, preparedRegistered⟩ :=
            State.preparedStreamItems_noticeTaskProvenance sound registered matching items
              (List.Subset.refl _)
          obtain ⟨boundarySound, boundaryRegistered⟩ :=
            State.drainReadyGroups_go_noticeTaskProvenance preparedSound preparedRegistered
              (steps + 1)
          refine ⟨located, _, node, lookup, same, contents,
            boundarySound, boundaryRegistered,
            (cached.preparedStreamItems items).drainReadyGroups_go (steps + 1),
            (sourceReady.preparedStreamItems matching (List.mem_append_right before
              List.mem_cons_self) items (List.Subset.refl _)).drainReadyGroups_go (steps + 1), ?_⟩
          apply ConformancePlan.retainedGroupMembers_unpublished ledger objects ready
            boundarySound boundaryRegistered (List.mem_of_find?_eq_some lookup)
          simp only [List.take_succ_cons, List.flatMap_cons,
            WorkQueueEvent.objectValues, List.nil_append] at count
          simpa only [count, State.preparedStreamItems, current] using excluded

/-- Every successful group carrier uses one of the two derived value-handler boundaries.
Witness: failures and stream closures cannot emit a successful group event; task-success
and item handlers use their actual indexed owner/drain branches, retaining one ledger.
-/
theorem ExecutedWork.handleGraphEvent_groupNotice_unpublished
    {work before event after published inputs w cut index group groups streams child
      failed}
    (generated : ExecutedWork work)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ event :: after) published)
    (valid : ValidGraphEvents work (before ++ event :: after))
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (ready : ConformancePlan.StreamPublicationReady work w)
    (cached
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).CachedFailuresSupported
          work failed)
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      ((current.handleGraphEvent event).2)[index]?
        = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ((w.events.take cut).flatMap normalizedObjectValues).length
        = (((State.initialize (Work.fromExecution work)).rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length
          + (((current.handleGraphEvent event).2.take index).flatMap
              WorkQueueEvent.objectValues).length
      → RetainedNoticeContents work w.matching (w.events.take cut) failed
          (before ++ event :: after) child := by
  intro current selected noticed count
  have member := List.mem_of_getElem? selected
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_groupNotice_unpublished covered valid ledger objects ready
        cached selected noticed count
  | streamItems stream items =>
      exact generated.streamItems_groupNotice_unpublished covered valid ledger objects ready
        cached selected noticed count
  | taskFailure occurrence errors =>
      exact False.elim
        (current.taskFailure_noGroupSuccess occurrence errors group groups streams member)
  | streamSuccess stream =>
      cases active : current.rootStreams.contains stream.ref <;>
        simp only [State.handleGraphEvent, State.streamSuccess, active,
          Bool.false_eq_true, ↓reduceIte] at member <;> simp at member
  | streamFailure stream errors =>
      cases active : current.rootStreams.contains stream.ref <;>
        simp only [State.handleGraphEvent, State.streamFailure, active,
          Bool.false_eq_true, ↓reduceIte] at member <;> simp at member

namespace ConformancePlan

/-- Every canonical group notice retains unpublished tasks and supported errors together.
Witness: the joint source boundary supplies the carrier's object rank and accepted cache
support at the same cut. Preserve both through its actual owner/drain boundary; the common
publication ledger supplies nonpublication without assuming the child's notice admission.
-/
theorem groupGroupNotice_unpublished
    {work inputs w index group groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (objects : GroupPublicationAdmission work w)
    (ready : StreamPublicationReady work w)
    {streamCuts : FailureCuts}
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streamCuts
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : RetainedNoticeContents work w.matching (w.events.take index)
        (failedBefore w.failures index) inputs.flatten child := by
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])
  obtain ⟨before, event, after, publisher, localIndex, sourceShape, emitted, count, cached⟩ :=
    Witness.handlerBoundary_cachedFailures generated valid started history partition selected
  obtain ⟨normalizedIndex, normalizedAt, atomicCount⟩ :=
    publicationAtoms_groupSuccess_prefix _ emitted
  obtain ⟨rawIndex, rawAt, rawCount⟩ := publisher.normalizeBatch_groupSuccess _ normalizedAt
  rw [sourceShape] at covered
  rw [sourceShape]
  apply generated.handleGraphEvent_groupNotice_unpublished covered (sourceShape ▸ valid)
    matching objects ready cached rawAt noticed
  rw [atomicCount, rawCount] at count
  exact count

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
