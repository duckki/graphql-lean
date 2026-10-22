import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedFailureCut
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulBufferRetention
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A generated source held by a latent failed child is disposed during parent success. -/

namespace AlternativeReleaseFailureChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence TaskAt)
open GraphQL.IncrementalDelivery.Tests (schema resolvers field defer)

-- Actual disposal is constructed directly; the optional cut is a topology theorem.
example : GeneratedStoredReleaseDisposal := GeneratedStoredReleaseDisposal_holds

example : GeneratedPendingBufferFailureCut := GeneratedPendingBufferFailureCut_holds
example : GeneratedReleaseFailureDisposal := GeneratedReleaseFailureDisposal_holds

private def root : Execution.DeliveryNode := ⟨0, [], some (.string "R")⟩
private def parent : Execution.DeliveryNode := ⟨1, [], some (.string "P")⟩
private def child : Execution.DeliveryNode := ⟨2, [], some (.string "C")⟩
private def supporter : Execution.DeliveryNode := ⟨3, [], some (.string "S")⟩
private def source : Execution.DeliveryNode := ⟨4, [.field "empty"], none⟩
private def producer : Occurrence := .executionGroup [1, 0]
private def rootFailure : Occurrence := .executionGroup [1, 1, 0]
private def finisher : Occurrence := .executionGroup [1, 1, 1, 0]
private def childFailure : Occurrence := .executionGroup [1, 1, 1, 1, 0]

private def value : Execution.ExecutionGroupValue :=
  { deliveryGroups := [root, child], path := [], data := [("empty", .list [])] }

private def parentValue : Execution.ExecutionGroupValue :=
  { deliveryGroups := [parent], path := [], data := [("b", .scalar "b")] }

private def streamWork : Execution.Work :=
  .combine (.combine .empty (.stream source [])) .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] []
        ({ result := .ok (value.data, 0) }) streamWork)
      (.combine
        (.executionGroup [⟨root, []⟩] [] ({ result := .error 1, cause := some 1 }) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] ({ result := .ok (parentValue.data, 0) })
            (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨child, [parent]⟩, ⟨supporter, []⟩] []
              ({ result := .error 1, cause := some 1 }) .empty)
            .empty))))

private def success : GraphEvent :=
  .taskSuccess producer
    { value, work := ReferenceWorkQueue.Work.fromExecution streamWork [1, 0, 0] }

private def killRoot : GraphEvent := .taskFailure rootFailure 1
private def killChild : GraphEvent := .taskFailure childFailure 1

private def finish : GraphEvent :=
  .taskSuccess finisher
    {
      value := parentValue,
      work :=
        ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def earlierInputs : List (List GraphEvent) := [[success], [killRoot], [killChild]]
private def inputs : List (List GraphEvent) := earlierInputs ++ [[finish]]
private abbrev before := ((State.initialize work).runNormalized earlierInputs).1
private abbrev reduced := ({ state := before } : GraphBatchResult).handleGraphEvent finish
private abbrev events := (before.queue.handleGraphEvent finish).2
private abbrev snapshot := registrationSnapshot before.queue finish
private abbrev view := failurePruningView before.queue finish events

private def buffered : ReferenceWorkQueue.TaskNode :=
  {
    task := { occurrence := producer, groups := [root, child] },
    value := some value,
    childStreams := [4]
  }

-- Every public generation/source/start premise is checked independently of cleanup.
private theorem generated : ReferenceWorkQueue.ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "empty" [] [.stream], field "required" [] [] (some "badR")] (some "R"),
     defer [field "b", defer [field "empty" [] [.stream],
       field "required" [] [] (some "badC")] (some "C")] (some "P"),
     defer [field "required" [] [] (some "badC")] (some "S")], ?_⟩
  cbv

private theorem producer_known
    : TaskAt work producer [root.ref, child.ref] none
        (.object [] (.ok (value.data, 0))) :=
  ⟨_, [], { result := .ok (value.data, 0) }, streamWork, [], rfl, rfl, rfl⟩

private theorem root_known
    : TaskAt work rootFailure [root.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem child_known
    : TaskAt work childFailure [child.ref, supporter.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem finisher_known
    : TaskAt work finisher [parent.ref] none (.object [] (.ok (parentValue.data, 0))) :=
  ⟨
    _,
    [],
    { result := .ok (parentValue.data, 0) },
    .combine .empty .empty,
    [],
    rfl,
    rfl,
    rfl
  ⟩

private theorem valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten := by
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
  exact .append third ⟨_, _, finisher_known, rfl, rfl⟩
    (by
      simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        success, killRoot, killChild, finish, producer, rootFailure, childFailure, finisher])
    ⟨_, _, _, finisher_known, by intro other impossible; cases impossible⟩

example : ReferenceWorkQueue.ExecutedWork work := generated
example : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten := valid
example : ReferenceWorkQueue.inputsStarted work inputs = true := by cbv
example : before.queue.taskNode? producer = some buffered := by cbv

example
    : (before.queue.taskNode? childFailure).map ReferenceWorkQueue.TaskNode.rejection
      = some (some 1) := by cbv

example : before.queue.rootGroups = [parent.ref] := by cbv
example : reduced.state.queue.taskNode? producer = none := by cbv

example
    : events
      = [
        .groupValues parent [parentValue],
        .groupSuccess parent [child] [],
        .groupFailure child 1
      ] := by cbv

example : GeneratedSnapshotTaskEvidence := GeneratedSnapshotTaskEvidence_holds

example : ∃ parents, snapshot.RemovalForest parents ∧ view.RemovalForest parents := by
  obtain ⟨parents, forest, views⟩ := generatedSnapshot_removalForest
    (inputs := earlierInputs) (event := finish) generated valid (by cbv)
  exact ⟨parents, forest, views events⟩

-- The actual successful parent sits above the failed child, not on its failure path.
private def parentNode : ReferenceWorkQueue.GroupNode :=
  { group := ⟨parent, none⟩, childGroups := [2], tasks := [finisher], pending := 1 }

private abbrev closing := { parentNode with pending := 0 }
private abbrev updated := snapshot.putGroupNode closing
private abbrev released := updated.finishGroupSuccess closing
private abbrev failureBoundary := released.1.startNewWork released.2.2

-- Parent closure cannot dispose a buffer owned by its child, including the failed child.
private theorem updatedFrame : SnapshotTaskEvidence updated work := by
  have frame := GeneratedSnapshotTaskEvidence_holds work earlierInputs finish generated valid (by cbv)
  have found : snapshot.groupNode? parent.ref = some parentNode := by cbv
  have registered := frame.live parentNode (List.mem_of_find?_eq_some found)
  exact { frame with
    keys := frame.keys.putGroupNode closing,
    live := frame.live.putGroupNode closing registered,
    buffered := frame.buffered.putGroupNodeSameTasks frame.keys parentNode
      (List.mem_of_find?_eq_some found) closing rfl rfl,
    sound := frame.sound.putGroupNode closing (frame.sound parentNode
      (List.mem_of_find?_eq_some found)) }

example : released.1.taskNode? producer = some buffered := by
  exact (successfulFlush_noncontributorBuffer updatedFrame closing
          (by cbv; exact List.mem_cons_self)
          (by cbv)
          rfl
          (by decide)).1

example : failureBoundary.rootGroups = [child.ref] := by cbv
example : released.2.1 ++ failureBoundary.drainReadyGroups.2 = events := by cbv

private theorem childPath : view.LiveDescendant child.ref child.ref := by
  have frame := GeneratedSnapshotTaskEvidence_holds work earlierInputs finish generated valid (by cbv)
  have found : snapshot.groupNode? parent.ref = some parentNode := by cbv
  have registered := frame.live parentNode (List.mem_of_find?_eq_some found)
  have updatedLive := frame.live.putGroupNode closing registered
  have postRegistration := updated.finishGroupSuccess_registration updatedLive frame.contributors closing
  have activeRegistration := ReferenceWorkQueue.State.startNewWork_registration
    postRegistration.1 postRegistration.2.1 released.2.2
  have closed := ReferenceWorkQueue.State.finishGroupSuccess_closureAccounting updatedLive closing
    (by cbv; exact List.mem_cons_self)
  have initialClosures : ReferenceWorkQueue.GroupClosureAccounting snapshot
      (failureBoundary, released.2.1) := by
    simpa only [List.nil_append]
      using (ReferenceWorkQueue.GroupClosureAccounting.silent
              (fun _ retired => retired.putGroupNode closing)).append
        (closed.post (fun _ retired => retired.startNewWork released.2.2))
  have edges : failureBoundary.GroupEdgesFrom snapshot := by
    intro key node live
    rw [ReferenceWorkQueue.State.groupNode?,
      (ReferenceWorkQueue.State.startNewWork_groupCore _ _).1] at live
    exact ((updated.finishGroupSuccess_descendants closing).1.trans
      (ReferenceWorkQueue.State.putPending_groupEdgesFrom frame.keys found 0)) key node live
  obtain ⟨parents, forest, _⟩ := generatedSnapshot_removalForest
    (inputs := earlierInputs) (event := finish) generated valid (by cbv)
  have activeForest := ((forest.putCounters frame.keys found 0).finishGroupSuccess closing).startNewWork
    released.2.2
  have activeFrame := (updatedFrame.finishGroupSuccess closing).startNewWork released.2.2
  have tracked := drain_pendingBuffer_ownerCut (before := before.queue) (event := finish)
    activeFrame activeForest edges initialClosures failureBoundary.groupNodes.length
    (occurrence := producer) (node := buffered) (by cbv) rfl
    (by
      intro key contributes
      change key ∉ publicationRoots (released.2.1 ++ failureBoundary.drainReadyGroups.2)
      have onlyPub : publicationRoots
          (released.2.1 ++ failureBoundary.drainReadyGroups.2) = [parent.ref] := by cbv
      rw [onlyPub]
      have keys : key = root.ref ∨ key = child.ref := by simpa [buffered] using contributes
      rcases keys with rfl | rfl <;> decide)
    (owner := child) (by simp [buffered])
    (by cbv; exact List.mem_cons_self)
  rcases tracked with kept | cut
  · have dropped : failureBoundary.drainReadyGroups.1.taskNode? producer = none := by cbv
    change failureBoundary.drainReadyGroups.1.taskNode? producer = some buffered ∧ _ at kept
    rw [dropped] at kept
    contradiction
  · obtain ⟨key, failed, path⟩ := cut
    have onlyFailure : failureRoots failureBoundary.drainReadyGroups.2 = [child.ref] := by cbv
    have same : key = child.ref := List.mem_singleton.mp (onlyFailure ▸ failed)
    have exactEvents : released.2.1 ++ failureBoundary.drainReadyGroups.2 = events := by cbv
    change (failurePruningView before.queue finish
      (released.2.1 ++ failureBoundary.drainReadyGroups.2)).LiveDescendant key child.ref at path
    simpa only [exactEvents, same] using path

example : view.LiveDescendant child.ref child.ref := childPath

-- The incoming successful task is newly buffered in this snapshot, not in the prefix.
private def newlyStored : ReferenceWorkQueue.TaskNode :=
  { task := { occurrence := finisher, groups := [parent] }, value := some parentValue }

example
    : (before.queue.taskNode? finisher).bind ReferenceWorkQueue.TaskNode.value
      = none := by cbv

example : snapshot.taskNode? finisher = some newlyStored := by cbv

example
    : snapshot.TaskLinkedOn finisher
        (newlyStored.task.groups.map Execution.DeliveryNode.ref) := by
  have frame := GeneratedSnapshotTaskEvidence_holds work earlierInputs finish generated valid (by cbv)
  exact frame.buffered newlyStored
    (List.mem_of_find?_eq_some
      (show snapshot.taskNode? finisher
        = some newlyStored by cbv))
    rfl

private theorem target : .cancelSource 4 ∈ reduced.effects := by
  have classified := generatedPrepared_sourceClassified (inputs := earlierInputs) (event := finish) (occurrence := producer)
    (node := buffered) (key := 4) generated valid (by cbv) trivial (by cbv) rfl (by decide)
  rcases classified with retained | active | requested
  · have dropped : reduced.state.queue.taskNode? producer = none := by cbv
    rw [dropped] at retained
    contradiction
  · have absent : reduced.state.queue.rootStreams = [] := by cbv
    rw [absent] at active
    cases active
  · exact requested

private def leases : ResourceState :=
  ((ResourceState.empty.set (.stream 4) (.owned (.producer producer))).adopt producer
    [.stream 4]).set
    (.task finisher) (.owned .queue)

private theorem source_owned : leases (.stream 4) = .owned .queue := by
  simp [leases, ResourceState.set, ResourceState.adopt]

private theorem disposed
    : .cancelSource 4 ∈ reduced.effects
      ∧ (leases.observeHandlerCleanup before finish).1 (.stream 4)
        = .cleanupRequested .queue := by
  refine ⟨target, ?_⟩
  exact leases.requestQueueCleanup_owned _ _ (List.mem_filterMap.mpr
    ⟨.cancelSource 4, target, rfl⟩) source_owned

example : .cancelSource 4 ∈ reduced.effects := disposed.1

example
    : (leases.observeHandlerCleanup before finish).1 (.stream 4)
      = .cleanupRequested .queue :=
  disposed.2

private abbrev observed := leases.observeCompletionAndCleanup before finish

example : observed.1 (.task finisher) = .released := by
  exact leases.observeCompletionAndCleanup_finishedTarget before finish (.task finisher)
    rfl (by simp [leases, ResourceState.set])

example : observed.1 (.stream 4) = .cleanupRequested .queue := by
  apply leases.observeCompletionAndCleanup_requested before finish (.stream 4)
    (by simp [normalCompletionTarget?, finish]) _ source_owned
  exact List.mem_filterMap.mpr ⟨.cancelSource 4, disposed.1, rfl⟩

private theorem handoff
    : ResourceReplay ResourceState.empty
        [
          .acquire (.stream 4) (.producer producer),
          .adopt producer [.stream 4],
          .acquire (.task finisher) .queue
        ] leases := by
  exact .cons (.acquire _ _ _ rfl)
    (.cons (.adopt _ _ _)
      (.cons
        (.acquire _ _ _
          (by simp [ResourceState.set, ResourceState.adopt,
            ResourceState.empty]))
        (.nil _)))

example
    : ResourceReplay ResourceState.empty
        ([
            .acquire (.stream 4) (.producer producer),
            .adopt producer [.stream 4],
            .acquire (.task finisher) .queue
          ]
          ++ observed.2) observed.1 :=
  handoff.append (leases.observeCompletionAndCleanup_replay before finish)

#print axioms failureFrontier_heldSource
#print axioms failurePruningView_pendingLinks
#print axioms generatedPrepared_sourceClassified
#print axioms ResourceState.observeCompletionAndCleanup_requested
#print axioms GeneratedSnapshotTaskEvidence_holds
#print axioms generatedSnapshot_removalForest
#print axioms generatedSnapshot_failureFrontierSource
#print axioms GeneratedStoredReleaseDisposal_holds
#print axioms generatedSnapshot_pendingOwned
#print axioms childPath
#print axioms drainFailureBoundary_path
#print axioms ReferenceWorkQueue.State.drainReadyGroups_go_closureAccounting
#print axioms successfulFlush_noncontributorBuffer
#print axioms generatedSnapshot_listedContributor
#print axioms SnapshotTaskEvidence.drainReadyGroups
#print axioms drain_pendingBuffer_ownerCut
#print axioms successGroupFold_releaseEvidence
#print axioms successGroupFold_pendingBuffer_retained
#print axioms GeneratedPendingBufferFailureCut_holds
#print axioms GeneratedReleaseFailureDisposal_holds

end AlternativeReleaseFailureChecks

namespace AlternativeItemSnapshotChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence Located TaskAt)
open GraphQL.IncrementalDelivery.Tests (schema resolvers field defer)

-----------------------------------------------------------------------------------------
-- Item preparation starts a new deferred task before the ready drain
-----------------------------------------------------------------------------------------

private def selections : List Selection :=
  [field "users" [defer [field "name"] (some "C")]
    [.stream (.boolean true) none (.int 0)]]

private def work : Execution.Work :=
  ((Execution.executeRootSelectionSetCore schema resolvers [] 30 "Query"
      (.object "Query" 0) selections).run
    0).1.work

private def stream : Execution.DeliveryNode := ⟨0, [.field "users"], none⟩

private def child (index : Nat) : Execution.DeliveryNode :=
  ⟨index + 1, [.field "users", .index index], some (.string "C")⟩

private def children (index : Nat) : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨child index, []⟩] (child index).path
        ({ result := .ok ([("name", .scalar ("name" ++ toString (index + 1)))], 0) })
        (.combine .empty .empty)) .empty)

private def occurrence : Occurrence := .item [0, 0, 1] 0
private def childOccurrence : Occurrence := .executionGroup [0, 0, 1, 0, 1, 0]

private def item : ReferenceWorkQueue.StreamItem :=
  ⟨
    occurrence,
    ⟨.object [], 0⟩,
    ReferenceWorkQueue.Work.fromExecution (children 0) [0, 0, 1, 0]
  ⟩

private def event : GraphEvent := .streamItems stream [item]
private abbrev before := State.initialize work
private abbrev snapshot := registrationSnapshot before.queue event

private def node : ReferenceWorkQueue.TaskNode :=
  { task := { occurrence := childOccurrence, groups := [child 0] } }

private theorem generated : ReferenceWorkQueue.ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

private theorem located
    : Located work [0, 0, 1]
        (.stream stream
          [
            ({ result := .ok (.object [], 0) }, children 0),
            ({ result := .ok (.object [], 0) }, children 1)
          ])
        none [] := by cbv

private theorem known
    : TaskAt work occurrence [stream.ref] none (.item stream (.ok (.object [], 0))) :=
  .item (result := { result := .ok (.object [], 0) }) located rfl

private theorem valid : ReferenceWorkQueue.ValidGraphEvents work [event] := by
  refine .append .nil ?_ ?_ ?_
  · intro candidate member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, _, known, by cbv⟩
  · simp [event, ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities, item]
  · exact ⟨_, _, _, _, located, by simp, by simp,
      (by intro producer impossible; cases impossible), rfl⟩

example : ReferenceWorkQueue.inputsStarted work [[event]] = true := by cbv
example : before.queue.taskNode? childOccurrence = none := by cbv
example : snapshot.taskNode? childOccurrence = some node := by cbv
example : snapshot.rootGroups = [(child 0).ref] := by cbv

-- Item integration preserves the actual active source's record and ownership.
example
    : RecordTargetRepresented
        (({ state := before } : GraphBatchResult).handleGraphEvent event).state.queue
        (.stream 0) :=
  GeneratedDispatchExistingSourceRepresentation_holds work [] event generated valid
    (by cbv)
    (ResourceState.empty.set (.stream 0) (.owned .queue))
    (fun _ => [])
    0
    (.activeStream (by cbv; exact .head _))
    (by cbv)

example : SnapshotTaskEvidence snapshot work :=
  GeneratedSnapshotTaskEvidence_holds work [] event generated valid (by cbv)

example
    : ∃ task,
        snapshot.task? childOccurrence = some task ∧ task.groups = node.task.groups :=
  generatedSnapshot_taskCatalogue (inputs := []) (event := event)
    (occurrence := childOccurrence) generated valid (by cbv) (by cbv)

example : ∃ parents, snapshot.RemovalForest parents := by
  obtain ⟨parents, forest, _⟩ := generatedSnapshot_removalForest (inputs := []) (event := event)
    generated valid rfl
  exact ⟨parents, forest⟩

end AlternativeItemSnapshotChecks
