import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureContributions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureAccounting

/-! Failed group closures retain exact accumulated source totals through actual batching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Raw source replay retains distinct-contributor error totals
-----------------------------------------------------------------------------------------

/-- A failed group closure is backed by a sum of distinct matching source failures.
The group descriptor indexes the total; its count need not match any single input.
-/
abbrev GroupFailureOrigin (work : Execution.Work) (inputs : List GraphEvent)
    (group : Execution.DeliveryNode) (errors : Nat)
    : Prop :=
  GroupFailureTotal work inputs group.ref errors

/-- A successful flush itself emits no failed group closure.
Witness: its exact output is optional values followed by successful completion.
The enclosing handler can still emit failed closures during its later drain.
-/
theorem State.finishGroupSuccess_no_groupFailure (queue : State) (node : GroupNode)
    (group : Execution.DeliveryNode) (errors : Nat)
    : Execution.WorkQueueEvent.groupFailure group errors
      ∉ (queue.finishGroupSuccess node).2.1 :=
  queue.finishGroupSuccess_groupFailure_absent node group errors

/-- A task-failure handler emits its current count for one of the task's contributors.
Witness: its actual owner fold; this does not cover cached failures from other handlers.
-/
theorem State.taskFailure_groupFailure_source (queue : State) (occurrence : Occurrence)
    (errors : Nat) {group count}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group count
        ∈ (queue.taskFailure occurrence errors).2)
    : ∃ node,
        queue.taskNode? occurrence = some node
        ∧ group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
        ∧ count = errors :=
  queue.taskFailure_groupFailure_current occurrence errors emitted

/-- Sequential handlers preserve exact cached and emitted totals over their source prefix.
Witness: source freshness extends each cache without duplicate contributors; every emitted
failure uses either the current input or an earlier certified cache.
-/
theorem State.CachedErrorsSatisfy.rawEventReplay_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (tasks : queue.RegisteredTasksMatch work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : (queue.rawEventReplay events).1.CachedErrorsSatisfy
        (GroupFailureTotal work (before ++ events))
      ∧ ∀ group errors,
          Execution.WorkQueueEvent.groupFailure group errors
            ∈ (queue.rawEventReplay events).2
          → GroupFailureOrigin work (before ++ events) group errors := by
  induction events generalizing queue before with
  | nil =>
      exact ⟨by simpa [State.rawEventReplay] using totals, by simp [State.rawEventReplay]⟩
  | cons event rest ih =>
      have initialPart : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have localLaws := valid.atPrefix initialPart
      have next := totals.handleGraphEvent_totals generated registered tasks event
        localLaws.1 localLaws.2.1
      obtain ⟨cached, output⟩ := ih next (registered.handleGraphEvent event)
        (tasks.handleGraphEvent event localLaws.1)
        (by simpa [List.append_assoc] using valid)
      rw [State.rawEventReplay_cons]
      refine ⟨by simpa [List.append_assoc] using cached, ?_⟩
      intro group errors emitted
      rcases List.mem_append.mp emitted with first | later
      · have total := totals.handleGraphEvent_outputTotal registered tasks event
          localLaws.1 first
        exact total.weaken initialPart.subset
      · simpa [List.append_assoc] using output group errors later

/-- Real batch wrapping preserves totals and creates no failed group closure.
Witness: ignored inputs merely extend source membership, while an open batch runs the
same handlers and may append only a queue-termination marker.
-/
theorem State.CachedErrorsSatisfy.handleGraphEvents_totals {queue : State} {work before}
    (totals : queue.CachedErrorsSatisfy (GroupFailureTotal work before))
    (generated : ExecutedWork work) (registered : queue.StartedTasksRegistered)
    (tasks : queue.RegisteredTasksMatch work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : (queue.handleGraphEvents events).1.CachedErrorsSatisfy
        (GroupFailureTotal work (before ++ events))
      ∧ ∀ group errors,
          Execution.WorkQueueEvent.groupFailure group errors
            ∈ (queue.handleGraphEvents events).2
          → GroupFailureOrigin work (before ++ events) group errors := by
  obtain ⟨cached, output⟩ := totals.rawEventReplay_totals generated registered tasks events valid
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact ⟨totals.mono (fun _ _ total => total.weaken (List.subset_append_left before events)),
      by simp⟩
  · dsimp only
    split
    · refine ⟨cached, ?_⟩
      intro group errors emitted
      apply output group errors
      simpa using emitted
    · exact ⟨cached, output⟩

-----------------------------------------------------------------------------------------
-- Publisher normalization copies error counts; it does not choose contributing failures
-----------------------------------------------------------------------------------------

/-- Publisher normalization copies failed group closures without changing their payloads.
Witness: all other raw constructors emit only values or their own control constructor.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupFailure_mem
    (publisher : IncrementalPublisher) (event : WorkQueueEvent) {group errors}
    : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (publisher.handleWorkQueueEvent event).2
      ↔ event = .groupFailure group errors := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, eq_comm]

/-- A normalized failed group closure occurred in that exact raw queue batch.
Witness: eventwise publisher replay and unchanged failure descriptors and counts.
-/
theorem IncrementalPublisher.normalizeBatch_groupFailure_mem
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent) {group errors}
    : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (publisher.normalizeBatch events).2
      ↔ Execution.WorkQueueEvent.groupFailure group errors ∈ events := by
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.mem_append, publisher.handleWorkQueueEvent_groupFailure_mem,
        ih, List.mem_cons]
      constructor <;> intro member
      · exact member.imp Eq.symm id
      · exact member.imp Eq.symm id

/-- Every normalized failed group closure reports an exact distinct-source sum.
Witness: joint cache/registry replay through actual host batches, including delayed
closures from successful handlers. Ignored batches and empty outputs are allowed;
no accepted-start or output-admission premise is needed for this provenance direction.
-/
theorem createWorkQueue_runNormalized_groupFailure_source {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    : GroupFailureOrigin work batches.flatten group errors := by
  have loop (more : List (List GraphEvent)) (before : List GraphEvent) (acc : NormalizedAcc)
      (totals : acc.1.CachedErrorsSatisfy (GroupFailureTotal work before))
      (registered : acc.1.StartedTasksRegistered)
      (tasks : acc.1.RegisteredTasksMatch work)
      (valid : ValidGraphEvents work (before ++ more.flatten))
      (output : ∀ group errors, Execution.WorkQueueEvent.groupFailure group errors ∈ acc.2.2.flatten
        → GroupFailureOrigin work before group errors)
      : ∀ group errors,
          Execution.WorkQueueEvent.groupFailure group errors
            ∈ (more.foldl normalizedStep acc).2.2.flatten
          → GroupFailureOrigin work (before ++ more.flatten) group errors := by
    induction more generalizing acc before with
    | nil => simpa using output
    | cons batch rest ih =>
        have firstValid : ValidGraphEvents work (before ++ batch) :=
          valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩
        have batchMatch : ∀ event ∈ batch, event.MatchesWork work :=
          fun event member => firstValid.eachMatches (List.mem_append_right before member)
        obtain ⟨cached, emitted⟩ := totals.handleGraphEvents_totals generated registered
          tasks batch firstValid
        have nextTotals : (normalizedStep acc batch).1.CachedErrorsSatisfy
            (GroupFailureTotal work (before ++ batch)) := by
          rw [normalizedStep_queue]
          exact cached
        have nextRegistered : (normalizedStep acc batch).1.StartedTasksRegistered := by
          rw [normalizedStep_queue]
          exact registered.handleGraphEvents batch
        have nextTasks : (normalizedStep acc batch).1.RegisteredTasksMatch work := by
          rw [normalizedStep_queue]
          exact tasks.handleGraphEvents batch batchMatch
        have nextOutput : ∀ group errors,
            Execution.WorkQueueEvent.groupFailure group errors
              ∈ (normalizedStep acc batch).2.2.flatten
            → GroupFailureOrigin work (before ++ batch) group errors := by
          dsimp only [normalizedStep]
          split
          · exact fun group errors member =>
              (output group errors member).weaken (List.subset_append_left before batch)
          · intro group errors member
            simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.mem_append] at member
            rcases member with earlier | latest
            · exact (output group errors earlier).weaken (List.subset_append_left before batch)
            · exact emitted group errors
                ((acc.2.1.normalizeBatch_groupFailure_mem _).mp latest)
        have result := ih (before ++ batch) (normalizedStep acc batch) nextTotals
          nextRegistered nextTasks (by simpa [List.append_assoc] using valid) nextOutput
        simpa [List.append_assoc] using result
  exact loop batches [] (_, _, []) (createWorkQueue_cachedErrors _ _)
    (createWorkQueue_startedTasksRegistered
      _) (createWorkQueue_fromSpec_registeredTasksMatch work)
    valid (by simp) group errors emitted

/-- Atomic value splitting neither creates nor changes a failed group closure.
Witness: only the failed group constructor has such a control atom.
-/
theorem publicationAtoms_groupFailure_mem (event : Execution.WorkQueueEvent)
    {group errors}
    : Execution.WorkQueueEvent.groupFailure group errors ∈ publicationAtoms event
      ↔ event = .groupFailure group errors := by
  cases event with
  | groupValues => simp [publicationAtoms]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms]
      | case2 => simp [publicationAtoms, streamPublicationAtoms]
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms] using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms, eq_comm]

/-- Atomic group failures retain the exact distinct-source total of their wire event.
Witness: atomic value expansion leaves group-failure controls and error counts intact.
-/
theorem createWorkQueue_runNormalized_atomicGroupFailure_source {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms)
    : GroupFailureOrigin work batches.flatten group errors := by
  obtain ⟨event, member, within⟩ := List.mem_flatMap.mp emitted
  have same := (publicationAtoms_groupFailure_mem event).mp within
  subst event
  exact createWorkQueue_runNormalized_groupFailure_source generated valid member

-----------------------------------------------------------------------------------------
-- Source readiness and payload matching constrain every contributor, not just one
-----------------------------------------------------------------------------------------

/-- A valid failed task settlement is structurally reachable through successful producers.
Witness: its valid source prefix and readiness, not a queue-history or cut premise.
-/
theorem ValidGraphEvents.taskFailure_reachable {work events}
    (valid : ValidGraphEvents work events) (generated : ExecutedWork work)
    {occurrence errors} (received : GraphEvent.taskFailure occurrence errors ∈ events)
    : Reachable work occurrence := by
  obtain ⟨before, _, _, validBefore, ready⟩ := valid.event_ready_context received
  obtain ⟨owners, producer, payload, known, supported⟩ := ready
  exact task_reachable_of_source_support validBefore (validBefore.successes_reachable generated)
    known supported

/-- Each actual atomic group-failure total has distinct reachable unpublished contributors.
Witness: exact source totals, source readiness, and the successful-only publication
matching. Counts are summed over the whole contributor list, not attributed to one input.
This does not yet place or license their failure cuts.
-/
theorem createWorkQueue_runNormalized_groupFailure_accounting {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) (matching : PublicationMatching)
    (exactValues
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atFailure
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : ∃ contributions : List (Occurrence × Nat),
        contributions ≠ []
        ∧ (contributions.map Prod.fst).Nodup
        ∧ (contributions.map Prod.snd).sum = errors
        ∧ ∀ occurrence count,
            (occurrence, count) ∈ contributions
            → GraphEvent.taskFailure occurrence count ∈ batches.flatten
              ∧ (∃ owners producer path,
                  TaskAt work occurrence owners producer (.object path (.error count))
                  ∧ group.ref ∈ owners)
              ∧ Reachable work occurrence
              ∧ ¬Published matching
                  (((State.initialize (Work.fromExecution work)).runNormalized
                      batches).2.flatten.flatMap
                    publicationAtoms) occurrence := by
  obtain ⟨parts, nonempty, unique, sum, sources⟩ :=
    createWorkQueue_runNormalized_atomicGroupFailure_source generated valid
      (List.mem_of_getElem? atFailure)
  refine ⟨parts, nonempty, unique, sum, ?_⟩
  intro occurrence count member
  obtain ⟨received, owners, producer, path, known, owner⟩ := sources occurrence count member
  exact ⟨received, ⟨owners, producer, path, known, owner⟩,
    valid.taskFailure_reachable generated received,
    failedTask_unpublished_of_exactValues exactValues known rfl⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
