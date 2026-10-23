import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskAnnouncementReplay

/-! Historical contributor announcements through startup-aware initialization and replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every task started at initialization has an initially announced contributing owner. -/
theorem State.initializeWithStartup_announcementFacts (work : Execution.Work)
    (startup : InitialStartup)
    : let initial := State.initialize (Work.fromExecution work) startup
      AnnouncementFacts work (initial.initialGroups.map Execution.DeliveryNode.ref)
        initial := by
  have empty : ({} : State).StartedTasksAnnounced [] := by
    intro node member; cases member
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  have prepared := (empty.maybeIntegrateWork (by intro ref member; cases member)
    (Work.fromExecution work)).pruneEmptyGroups integrated.2.newGroups
  have owners := initialPreparation_taskOwnerFrame work
  have known := prepared.startNewWork owners.sound owners.registered owners.matching
    (initialPreparation work).2 startup.failures
  have tasks := State.initializeWithStartup_taskOwnerFrame work startup
  dsimp only
  refine ⟨?_, ?_, tasks.sound, tasks.registered, tasks.matching⟩
  · rw [State.initializeWithStartup_eq_preparation]
    exact known
  · rw [State.initializeWithStartup_eq_preparation]
    intro ref member
    have released := ((initialPreparation work).1.startNewWork_rootGroups_sublist
      (initialPreparation work).2 startup.failures).subset member
    rw [initialPreparation_rootGroups_empty] at released
    exact released

/-- Ordinary publisher replay retains announcement evidence with pending startup controls. -/
theorem AnnouncementFacts.runWithPublisher {work seen queue}
    (facts : AnnouncementFacts work seen queue) (publisher : IncrementalPublisher)
    (inputs : List (List GraphEvent))
    (allMatch : ∀ event ∈ inputs.flatten, event.MatchesWork work)
    : let result := queue.runWithPublisher publisher inputs
      AnnouncementFacts work (seen ++ result.2.2.flatten.flatMap groupNoticeRefs)
        result.1 := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (prior : AnnouncementFacts work (seen ++ acc.2.2.flatten.flatMap groupNoticeRefs) acc.1)
      (matching : ∀ event ∈ more.flatten, event.MatchesWork work)
      : AnnouncementFacts work
          (seen ++ (more.foldl normalizedStep acc).2.2.flatten.flatMap groupNoticeRefs)
          (more.foldl normalizedStep acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih =>
        apply ih
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupNotices]
          simpa only [List.append_assoc] using prior.handleGraphEvents batch
            (fun event member => matching event (List.mem_append_left _ member))
        · exact fun event member => matching event (List.mem_append_right _ member)
  exact loop inputs (queue, publisher, [])
    (by simpa only [List.flatten_nil, List.flatMap_nil, List.append_nil] using facts)
    allMatch

/-- Startup-aware normalized replay retains exact task-origin and announcement certificates. -/
theorem State.startup_runNormalized_announcementFacts {work : Execution.Work}
    (startup : InitialStartup) {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      AnnouncementFacts work
        (initial.initialGroups.map Execution.DeliveryNode.ref
          ++ (initial.runNormalized inputs).2.flatten.flatMap groupNoticeRefs)
        (initial.runNormalized inputs).1 := by
  exact (State.initializeWithStartup_announcementFacts work startup).runWithPublisher
    _ inputs (fun event member => valid.eachMatches member)

/-- Every actual startup-aware task lookup has a historically announced contributor. -/
theorem State.startup_runNormalized_announcedOwner {work : Execution.Work}
    (startup : InitialStartup) {inputs : List (List GraphEvent)}
    (valid : ValidGraphEvents work inputs.flatten) {occurrence : Occurrence}
    {node : TaskNode}
    (found
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.taskNode? occurrence = some node)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ initial.initialGroups.map Execution.DeliveryNode.ref
            ++ (initial.runNormalized inputs).2.flatten.flatMap groupNoticeRefs := by
  have facts := State.startup_runNormalized_announcementFacts startup valid
  obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some found
  obtain ⟨owner, contributes, announced⟩ := facts.known node member
  obtain ⟨⟨_, payload, producer, _, located⟩, _⟩ :=
    facts.matching node.task (facts.registered node member)
  exact ⟨node.task.groups.map Execution.DeliveryNode.ref, owner.ref,
    ⟨producer, payload, occurrenceEq ▸ located⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, announced⟩

/-- A FIFO task lookup retains an owner announced before the same actual output boundary. -/
theorem State.startup_batchPrefix_announcedOwner {work : Execution.Work}
    (startup : InitialStartup) (earlier : List (List GraphEvent))
    (before : List GraphEvent) (valid : ValidGraphEvents work (earlier.flatten ++ before))
    (available : List (Occurrence × Nat)) {occurrence : Occurrence} {node : TaskNode}
    (found
      : let initial := State.initialize (Work.fromExecution work) startup
        State.taskNode?
          ((initial.runNormalized earlier).1.replayGraphEvents before available)
          occurrence
        = some node)
    : let initial := State.initialize (Work.fromExecution work) startup
      let current := (initial.runNormalized earlier).1
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ initial.initialGroups.map Execution.DeliveryNode.ref
            ++ (initial.runNormalized earlier).2.flatten.flatMap groupNoticeRefs
            ++ (current.rawEventReplay before available).2.flatMap
                rawGroupNoticeRefs := by
  have prior := State.startup_runNormalized_announcementFacts startup
    (valid.prefix (List.prefix_append earlier.flatten before))
  have facts := prior.rawEventReplay before
    (fun event member => valid.eachMatches (List.mem_append_right _ member)) available
  let initial := State.initialize (Work.fromExecution work) startup
  let current := (initial.runNormalized earlier).1
  have foundRaw : (current.rawEventReplay before available).1.taskNode? occurrence = some node := by
    rwa [State.rawEventReplay_state _ _ available]
  obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some foundRaw
  obtain ⟨owner, contributes, announced⟩ := facts.known node member
  obtain ⟨⟨_, payload, producer, _, located⟩, _⟩ :=
    facts.matching node.task (facts.registered node member)
  exact ⟨node.task.groups.map Execution.DeliveryNode.ref, owner.ref,
    ⟨producer, payload, occurrenceEq ▸ located⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, announced⟩

/-- Actual startup source eligibility retains an earlier FIFO lookup boundary in the same batch. -/
theorem inputsStartedWithStartup_eachAccepted (work : Execution.Work)
    (startup : InitialStartup) (earlier later : List (List GraphEvent))
    (batch before : List GraphEvent) (event : GraphEvent)
    (started : inputsStarted work (earlier ++ batch :: later) startup = true)
    (prefixOfBatch : (before ++ [event]).IsPrefix batch)
    : let initial := (State.initialize (Work.fromExecution work) startup)
      ∃ seen,
        seen.IsPrefix before
        ∧ ((initial.replayBatches earlier).replayGraphEvents seen
            (GraphEvent.availableFailures batch)).acceptsGraphEvent
            event
          = true := by
  rw [inputsStartedWithStartup_eq_batchesStarted] at started
  exact State.acceptsBatch_eachAccepted _ batch before event
    (State.batchesStarted_eachBatch _ earlier batch later started) prefixOfBatch

/-- Every admitted failure notification has a contributing announcement at its actual cut.
The task may have been retired earlier in the same available batch; historical notices
retain its licensing contributor from the earlier eligibility boundary.
-/
theorem State.startup_taskFailure_announcedOwner {work : Execution.Work}
    (startup : InitialStartup) (earlier : List (List GraphEvent))
    (batch : List GraphEvent) (later : List (List GraphEvent))
    (before after : List GraphEvent) (occurrence : Occurrence) (errors : Nat)
    (split : batch = before ++ .taskFailure occurrence errors :: after)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let current := (initial.runNormalized earlier).1
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ initial.initialGroups.map Execution.DeliveryNode.ref
            ++ (initial.runNormalized earlier).2.flatten.flatMap groupNoticeRefs
            ++ (current.rawEventReplay before
                  (GraphEvent.availableFailures batch)).2.flatMap
                rawGroupNoticeRefs := by
  let initial := State.initialize (Work.fromExecution work) startup
  let current := (initial.runNormalized earlier).1
  let available := GraphEvent.availableFailures batch
  have priorValid : ValidGraphEvents work (earlier.flatten ++ before) := by
    apply valid.prefix
    refine ⟨.taskFailure occurrence errors :: (after ++ later.flatten), ?_⟩
    simp [List.flatten_append, split, List.append_assoc]
  have earlierValid := priorValid.prefix (List.prefix_append earlier.flatten before)
  have eligible := inputsStartedWithStartup_eachAccepted work startup earlier later batch before
    (.taskFailure occurrence errors) started ⟨after, by simp [split]⟩
  have endpoint : current = initial.replayBatches earlier :=
    State.runNormalized_replayBatches initial earlier
  dsimp only at eligible
  rw [← endpoint] at eligible
  have findNode (state : State)
      (accepted : state.acceptsGraphEvent (.taskFailure occurrence errors) = true)
      : ∃ node, state.taskNode? occurrence = some node := by
    cases found : state.taskNode? occurrence with
    | none => simp only [State.acceptsGraphEvent, found, Option.isSome_none,
        Bool.false_eq_true] at accepted
    | some node => exact ⟨node, rfl⟩
  obtain ⟨seen, seenPrefix, accepted⟩ := eligible
  obtain ⟨node, found⟩ := findNode _ accepted
  have seenValid : ValidGraphEvents work (earlier.flatten ++ seen) := by
    apply priorValid.prefix
    obtain ⟨remaining, same⟩ := seenPrefix
    exact ⟨remaining, by simp only [same, List.append_assoc]⟩
  obtain ⟨owners, owner, known, contributes, announced⟩ :=
    State.startup_batchPrefix_announcedOwner startup earlier seen seenValid available found
  refine ⟨owners, owner, known, contributes, ?_⟩
  rcases List.mem_append.mp announced with prior | atNotice
  · exact List.mem_append_left _ prior
  · apply List.mem_append_right
    obtain ⟨remaining, rfl⟩ := seenPrefix
    rw [State.rawEventReplay_append _ _ _ available, List.flatMap_append]
    exact List.mem_append_left _ atNotice

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
