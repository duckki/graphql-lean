import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedBufferDisposal
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedFailureCut
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedStopCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Two latent failed contributors remove the same held source in one mixed drain.
The first failure retains the shared buffer; the second disposes its last live owner.
-/

namespace AlternativeMixedOwnerCutChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence TaskAt)
open GraphQL.IncrementalDelivery.Tests (schema resolvers field defer)

private def root : Execution.DeliveryNode := ⟨0, [], some (.string "R")⟩
private def parent : Execution.DeliveryNode := ⟨1, [], some (.string "P")⟩
private def child : Execution.DeliveryNode := ⟨2, [], some (.string "C")⟩
private def sibling : Execution.DeliveryNode := ⟨3, [], some (.string "D")⟩
private def supporter : Execution.DeliveryNode := ⟨4, [], some (.string "S")⟩
private def otherSupporter : Execution.DeliveryNode := ⟨5, [], some (.string "T")⟩
private def source : Execution.DeliveryNode := ⟨6, [.field "empty"], none⟩

private def producer : Occurrence := .executionGroup [1, 0]
private def rootFailure : Occurrence := .executionGroup [1, 1, 0]
private def finisher : Occurrence := .executionGroup [1, 1, 1, 0]
private def childFailure : Occurrence := .executionGroup [1, 1, 1, 1, 0]
private def siblingFailure : Occurrence := .executionGroup [1, 1, 1, 1, 1, 0]

private def value : Execution.ExecutionGroupValue :=
  { deliveryGroups := [root, child, sibling], path := [], data := [("empty", .list [])] }

private def parentValue : Execution.ExecutionGroupValue :=
  { deliveryGroups := [parent], path := [], data := [("b", .scalar "b")] }

private def streamWork : Execution.Work :=
  .combine (.combine .empty (.stream source [])) .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩, ⟨sibling, [parent]⟩] []
        (.ok (value.data, 0)) streamWork)
      (.combine (.executionGroup [⟨root, []⟩] [] (.error 1) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (parentValue.data, 0))
            (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨child, [parent]⟩, ⟨supporter, []⟩] [] (.error 1) .empty)
            (.combine
              (.executionGroup [⟨sibling, [parent]⟩, ⟨otherSupporter, []⟩] [] (.error 1)
                .empty)
              .empty)))))

private def success : GraphEvent :=
  .taskSuccess producer
    { value, work := ReferenceWorkQueue.Work.fromExecution streamWork [1, 0, 0] }

private def killRoot : GraphEvent := .taskFailure rootFailure 1
private def killChild : GraphEvent := .taskFailure childFailure 1
private def killSibling : GraphEvent := .taskFailure siblingFailure 1

private def finish : GraphEvent :=
  .taskSuccess finisher
    {
      value := parentValue,
      work :=
        ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def earlierInputs : List (List GraphEvent) :=
  [[success], [killRoot], [killChild], [killSibling]]

private abbrev before := ((State.initialize work).runNormalized earlierInputs).1
private abbrev snapshot := registrationSnapshot before.queue finish
private abbrev events := (before.queue.handleGraphEvent finish).2
private abbrev reduced := ({ state := before } : GraphBatchResult).handleGraphEvent finish
private abbrev view := failurePruningView before.queue finish events

private def buffered : ReferenceWorkQueue.TaskNode :=
  {
    task := { occurrence := producer, groups := [root, child, sibling] },
    value := some value,
    childStreams := [6]
  }

-----------------------------------------------------------------------------------------
-- Generation, source, and start premises are independent of the disposal outcome
-----------------------------------------------------------------------------------------

private theorem generated : ReferenceWorkQueue.ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "empty" [] [.stream], field "required" [] [] (some "badR")] (some "R"),
     defer [field "b",
       defer [field "empty" [] [.stream], field "required" [] [] (some "badC")] (some "C"),
       defer [field "empty" [] [.stream], field "required" [] [] (some "badD")] (some "D")]
       (some "P"),
     defer [field "required" [] [] (some "badC")] (some "S"),
     defer [field "required" [] [] (some "badD")] (some "T")], ?_⟩
  cbv

private theorem producer_known
    : TaskAt work producer [root.ref, child.ref, sibling.ref] none
        (.object [] (.ok (value.data, 0))) :=
  ⟨_, [], .ok (value.data, 0), streamWork, [], rfl, rfl, rfl⟩

private theorem root_known
    : TaskAt work rootFailure [root.ref] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem child_known
    : TaskAt work childFailure [child.ref, supporter.ref] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem sibling_known
    : TaskAt work siblingFailure [sibling.ref, otherSupporter.ref] none
        (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem finisher_known
    : TaskAt work finisher [parent.ref] none (.object [] (.ok (parentValue.data, 0))) :=
  ⟨_, [], .ok (parentValue.data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents work (earlierInputs.flatten ++ [finish]) := by
  have first : ReferenceWorkQueue.ValidGraphEvents work [success] :=
    .append .nil ⟨_, _, producer_known, rfl, rfl⟩
      (by simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities, success])
      ⟨_, _, _, producer_known, by intro other impossible; cases impossible⟩
  have second : ReferenceWorkQueue.ValidGraphEvents work [success, killRoot] :=
    .append first ⟨_, _, _, root_known⟩
      (by simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        success, killRoot, producer, rootFailure])
      ⟨_, _, _, root_known, by intro other impossible; cases impossible⟩
  have third : ReferenceWorkQueue.ValidGraphEvents work [success, killRoot, killChild] :=
    .append second ⟨_, _, _, child_known⟩
      (by simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        success, killRoot, killChild, producer, rootFailure, childFailure])
      ⟨_, _, _, child_known, by intro other impossible; cases impossible⟩
  have fourth : ReferenceWorkQueue.ValidGraphEvents work [success, killRoot, killChild, killSibling] :=
    .append third ⟨_, _, _, sibling_known⟩
      (by simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        success, killRoot, killChild, killSibling, producer, rootFailure, childFailure, siblingFailure])
      ⟨_, _, _, sibling_known, by intro other impossible; cases impossible⟩
  exact .append fourth ⟨_, _, finisher_known, rfl, rfl⟩
    (by
      simp [earlierInputs, ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        success, killRoot, killChild, killSibling, finish, producer, rootFailure,
        childFailure, siblingFailure, finisher])
    ⟨_, _, _, finisher_known, by intro other impossible; cases impossible⟩

private theorem started
    : ReferenceWorkQueue.inputsStarted work (earlierInputs ++ [[finish]]) = true := by cbv

example : snapshot.taskNode? producer = some buffered := by cbv
example : reduced.state.queue.taskNode? producer = none := by cbv

example
    : events
      = [
        .groupValues parent [parentValue],
        .groupSuccess parent [child, sibling] [],
        .groupFailure child 1,
        .groupFailure sibling 1
      ] := by cbv

private def parentNode : ReferenceWorkQueue.GroupNode :=
  { group := ⟨parent, none⟩, childGroups := [2, 3], tasks := [finisher], pending := 0 }

private abbrev released :=
  (snapshot.putGroupNode parentNode).finishGroupSuccess parentNode

private abbrev drainEntry := released.1.startNewWork released.2.2

-- Pin the real mixed-drain boundary and its first shared-owner removal separately.
example : released.2.1 ++ drainEntry.drainReadyGroups.2 = events := by cbv

example
    : (ReferenceWorkQueue.State.drainReadyGroups.go 1 drainEntry).2
      = [.groupFailure child 1] := by cbv

example
    : (ReferenceWorkQueue.State.drainReadyGroups.go 1 drainEntry).1.taskNode? producer
      = some buffered := by cbv

example
    : (ReferenceWorkQueue.State.drainReadyGroups.go 2 drainEntry).1.taskNode? producer
      = none := by cbv

-----------------------------------------------------------------------------------------
-- The universal cut and disposal witnesses cover both chronological owner failures
-----------------------------------------------------------------------------------------

private theorem ownerCut
    : ∀ owner ∈ buffered.task.groups,
        ∀ group,
          view.groupNode? owner.ref = some group
          → ∃ root ∈ failureRoots events, view.LiveDescendant root owner.ref :=
  GeneratedPendingBufferFailureCut_holds work earlierInputs finish generated valid started
    trivial producer buffered (by cbv) rfl (by cbv) (by cbv)

example : ∃ root ∈ failureRoots events, view.LiveDescendant root child.ref :=
  ownerCut child (by simp [buffered]) _ (by cbv)

example : ∃ root ∈ failureRoots events, view.LiveDescendant root sibling.ref :=
  ownerCut sibling (by simp [buffered]) _ (by cbv)

private def leases : ResourceState :=
  ((ResourceState.empty.set (.stream 6) (.owned (.producer producer))).adopt producer
    [.stream 6]).set
    (.task finisher) (.owned .queue)

private theorem disposed
    : .cancelSource 6 ∈ reduced.effects
      ∧ (leases.observeCompletionAndCleanup before finish).1 (.stream 6)
        = .cleanupRequested .queue := by
  have coverage := GeneratedStoredReleaseDisposal_holds work earlierInputs finish generated
    valid started trivial leases
  have outcome := coverage.2 producer buffered 6 (by cbv) rfl
    (by decide) (by cbv)
  rcases outcome with transferred | requested
  · have absent : 6 ∉ reduced.state.queue.rootStreams := by cbv; intro impossible; cases impossible
    exact False.elim (absent transferred)
  · exact ⟨requested.1, requested.2 (by simp [leases, ResourceState.set, ResourceState.adopt])⟩

example : .cancelSource 6 ∈ reduced.effects := disposed.1

-- All prepared sources are classified, including this buffer whose two latent owners fail.
example
    : RecordTargetRepresented reduced.state.queue (.stream 6)
      ∨ .cancelSource 6 ∈ reduced.effects :=
  GeneratedPreparedSourceProgress_holds work earlierInputs finish generated valid started
    trivial producer buffered 6 (by cbv) rfl (by decide)

-- Neither surviving contributor is healthy: owner existence must include latent failures.
example : before.queue.taskHasHealthyOwner buffered.task = false := by cbv

example : before.queue.BufferedOwnersPresent := by
  obtain ⟨prior, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  exact generatedReplay_bufferedOwnersPresent generated prior earlierStarted

example : before.queue.LiveContributorsCovered := by
  obtain ⟨prior, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  exact GeneratedLiveContributorCoverage_holds work earlierInputs generated prior earlierStarted

-- Stop still reaches the held source when every remaining owner is cached failed and latent.
private theorem stoppedHeld : .stream 6 ∈ before.cleanupTargets := by
  obtain ⟨prior, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  have targets := GeneratedBufferedStopCoverage_holds work earlierInputs generated prior
    earlierStarted producer buffered (by cbv) rfl
  apply targets
  cbv
  exact .tail _ (.head _)

example : .stream 6 ∈ before.cleanupTargets := stoppedHeld

example : snapshot.BufferedOwnersPresent := by
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  exact GeneratedSnapshotBufferedOwners_holds work earlierInputs finish generated valid earlierStarted

example
    : (leases.observeCompletionAndCleanup before finish).1 (.stream 6)
      = .cleanupRequested .queue :=
  disposed.2

example
    : (leases.observeCompletionAndCleanup before finish).1 (.task finisher)
      = .released := by
  exact leases.observeCompletionAndCleanup_finishedTarget before finish (.task finisher)
    rfl (by simp [leases, ResourceState.set])

private theorem handoff
    : ResourceReplay ResourceState.empty
        [
          .acquire (.stream 6) (.producer producer),
          .adopt producer [.stream 6],
          .acquire (.task finisher) .queue
        ] leases := by
  exact .cons (.acquire _ _ _ rfl)
    (.cons (.adopt _ _ _)
      (.cons
        (.acquire _ _ _
          (by simp [ResourceState.set, ResourceState.adopt, ResourceState.empty]))
        (.nil _)))

example
    : ResourceReplay ResourceState.empty
        ([
            .acquire (.stream 6) (.producer producer),
            .adopt producer [.stream 6],
            .acquire (.task finisher) .queue
          ]
          ++ (leases.observeCompletionAndCleanup before finish).2)
        (leases.observeCompletionAndCleanup before finish).1 :=
  handoff.append (leases.observeCompletionAndCleanup_replay before finish)

#print axioms ownerCut
#print axioms disposed
#print axioms GeneratedPendingBufferFailureCut_holds
#print axioms GeneratedReleaseFailureDisposal_holds
#print axioms GeneratedSnapshotBufferedOwners_holds
#print axioms GeneratedStoredReleaseDisposal_holds
#print axioms GeneratedBufferedStopCoverage_holds
#print axioms stoppedHeld

end AlternativeMixedOwnerCutChecks
