import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailureCacheStability

/-! Consumed failures retain exact rejection counts. This supplies cache stability at a
complete batch boundary without treating availability as FIFO notification consumption.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence)

private theorem State.FailureCached.successGroupFold {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors)
    (groups : List Execution.DeliveryNode) (events : List Execution.WorkQueueEvent)
    (released : NewWork)
    : (groups.foldl successGroupStep (queue, events, released)).1.FailureCached occurrence
        errors := by
  induction groups generalizing queue events released with
  | nil => exact cached
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih cached _ _
      · rename_i node found
        have changed : (queue.putGroupNode {node with pending := node.pending - 1}).FailureCached
            occurrence errors := cached
        split
        · exact ih (changed.finishGroupSuccess _) _ _
        · exact ih changed _ _

/-- Successful completion retains rejection metadata while installing only fresh children. -/
theorem State.FailureCached.taskSuccess {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (source : Occurrence)
    (result : TaskResult)
    (fresh : ∀ task ∈ result.work.tasks, occurrence ≠ task.occurrence)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.taskSuccess source result available).1.FailureCached occurrence errors := by
  cases found : queue.taskNode? source with
  | none => simpa only [State.taskSuccess, found] using cached
  | some node =>
      rw [queue.taskSuccess_eq source result node found available]
      have stored := cached.putTaskNode {node with value := some result.value}
        (fun same => cached node (List.mem_of_find?_eq_some found) same)
      have prepared := stored.maybeIntegrateWork result.work fresh (some source)
      exact ((prepared.successGroupFold node.task.groups [] {}).startNewWork _ known)
        |>.drainReadyGroups_go _ known

/-- Another failure preserves the tracked count when the source counts agree. -/
theorem State.FailureCached.taskFailure {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (source : Occurrence)
    (count : Nat) (agrees : source = occurrence → count = errors)
    : (queue.taskFailure source count).1.FailureCached occurrence errors := by
  cases found : queue.taskNode? source with
  | none => simpa only [State.taskFailure, found] using cached
  | some node =>
      rw [queue.taskFailure_eq source count node found]
      apply failureGroupFold_preserves (fun q => q.FailureCached occurrence errors)
        (fun _ ref prior => prior.removeGroup ref)
      apply cached.putTaskNode
      intro same
      exact congrArg some (agrees ((State.taskNode?_some found).2.symm.trans same))

/-- Recording this failure establishes its slot equality even without a previous cache. -/
theorem State.taskFailure_failureCached (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.FailureCached occurrence errors := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskFailure, found] using (State.FailureCached.of_missing found)
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      apply failureGroupFold_preserves (fun q => q.FailureCached occurrence errors)
        (fun _ ref prior => prior.removeGroup ref)
      intro updated member same
      obtain ⟨old, prior, selected⟩ := List.mem_map.mp member
      split at selected
      · subst updated; rfl
      · rename_i different
        subst updated
        exact False.elim (different ((occurrence_beq_iff_eq _ _).mpr
          (same.trans (State.taskNode?_some found).2.symm)))

/-- Every receipt preparation and ready drain retains the tracked exact failure. -/
theorem State.FailureCached.streamItems {queue occurrence errors stream items}
    (cached : State.FailureCached queue occurrence errors)
    (fresh : ∀ item ∈ items, ∀ task ∈ item.work.tasks, occurrence ≠ task.occurrence)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.streamItems stream items available).1.FailureCached occurrence errors := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact cached
  · apply State.FailureCached.drainReadyGroups_go (known := known)
    apply State.preparedStreamItems_preserves (fun q => q.FailureCached occurrence errors)
      cached items available
    intro current item member prior
    exact ((prior.maybeIntegrateWork item.work (fresh item member)).pruneEmptyGroups _)
      |>.startNewWork _ known

/-- A later handler preserves an already consumed failure under the same fixed snapshot. -/
theorem State.FailureCached.handleGraphEvent {queue occurrence errors event}
    (cached : State.FailureCached queue occurrence errors)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (agrees
      : ∀ source count,
          event = .taskFailure source count → source = occurrence → count = errors)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.handleGraphEvent event available).1.FailureCached occurrence errors := by
  have exposed := cached.cacheTaskFailures available known.consistent
  cases event with
  | taskSuccess source result => exact exposed.taskSuccess source result fresh known
  | taskFailure source count =>
      exact exposed.taskFailure source count (agrees source count rfl)
  | streamItems stream items =>
      exact exposed.streamItems
        (fun item member task listed => fresh task (List.mem_flatMap.mpr ⟨item, member, listed⟩))
        known
  | streamSuccess stream =>
      change ((queue.cacheTaskFailures available).streamSuccess stream).1.FailureCached
        occurrence errors
      unfold State.streamSuccess
      split <;> exact exposed
  | streamFailure stream count =>
      change ((queue.cacheTaskFailures available).streamFailure stream count).1.FailureCached
        occurrence errors
      unfold State.streamFailure
      split <;> exact exposed

  | groupFailure notice =>
      change ((queue.cacheTaskFailures available).groupFailure notice).1.FailureCached occurrence errors
      unfold State.groupFailure
      split
      · exact exposed
      · split <;> exact exposed

/-- Realizing enqueue effects preserves every exact retained rejection slot. -/
theorem State.FailureCached.dispatchGraphEvent {queue occurrence errors event}
    (cached : State.FailureCached queue occurrence errors)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (agrees
      : ∀ source count,
          event = .taskFailure source count → source = occurrence → count = errors)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.dispatchGraphEvent event available).1.FailureCached occurrence errors := by
  exact cached.handleGraphEvent fresh agrees known

/-- Source freshness prevents later registration from replacing a consumed failure slot. -/
theorem State.FailureCached.replayGraphEvents {queue work occurrence errors before}
    (cached : State.FailureCached queue occurrence errors)
    (failed : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (recorded : occurrence ∈ before.flatMap (fun prior => prior.identities.1))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.replayGraphEvents events available).FailureCached occurrence errors := by
  induction events generalizing queue before with
  | nil => exact cached
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := cached.dispatchGraphEvent (by
        intro child member same
        exact matching.childTasks_unsettled priorValid fresh member (same ▸ recorded))
        (by
          intro source count same identity
          subst source
          subst event
          exact matching.taskFailure_count_unique failed) known
      have nextRecorded
          : occurrence
            ∈ (before ++ [event]).flatMap (fun prior => prior.identities.1) := by
        rw [List.flatMap_append]; exact List.mem_append_left _ recorded
      exact ih next nextRecorded
        (by simpa only [List.append_assoc, List.singleton_append] using valid)

/-- Every failure notified by a source-valid finite batch has an exact surviving slot.
The result does not require its callback to remain eligible when consumed.
-/
theorem State.replayGraphEvents_failuresCached (queue : State) {work before}
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (snapshot
      : ∀ entry ∈ GraphEvent.availableFailures events,
          FailureInSnapshot available entry.1 entry.2)
    : ∀ entry ∈ GraphEvent.availableFailures events,
        (queue.replayGraphEvents events available).FailureCached entry.1 entry.2 := by
  induction events generalizing queue before with
  | nil => intro entry member; cases member
  | cons event rest ih =>
      intro entry member
      have first : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last (valid.prefix first)
      have tailValid : ValidGraphEvents work ((before ++ [event]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using valid
      have later (selected : Occurrence × Nat)
          (listed : selected ∈ GraphEvent.availableFailures rest)
          : selected ∈ GraphEvent.availableFailures (event :: rest) := by
        cases event with
        | taskFailure => exact List.mem_cons_of_mem _ listed
        | taskSuccess | streamItems | streamSuccess | streamFailure | groupFailure =>
            exact listed
      cases event with
      | taskFailure occurrence errors =>
          simp only [GraphEvent.availableFailures, List.filterMap_cons, List.mem_cons] at member
          rcases member with same | received
          · subst entry
            have completed : (queue.dispatchGraphEvent (.taskFailure occurrence errors)
                available).1.FailureCached occurrence errors :=
              (queue.cacheTaskFailures available).taskFailure_failureCached occurrence errors
            exact completed.replayGraphEvents matching
              (by simp [List.flatMap_append, GraphEvent.identities]) rest tailValid
              (snapshot (occurrence, errors) (by simp [GraphEvent.availableFailures]))
          · exact ih _ tailValid (fun next member => snapshot next (later next member)) _ received
      | taskSuccess | streamItems | streamSuccess | streamFailure | groupFailure =>
          exact ih _ tailValid (fun next member => snapshot next (later next member)) _ member

/-- With exact slots for every supplied failure, cache exposure changes no queue field. -/
theorem State.TaskNodeKeysUnique.cacheTaskFailures_eq_self {queue : State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (cached : ∀ entry ∈ available, queue.FailureCached entry.1 entry.2)
    : queue.cacheTaskFailures available = queue := by
  rw [unique.cacheTaskFailures_eq available]
  have nodes : queue.taskNodes.map
      (fun node =>
        { node with
          rejection := available.foldl
            (fun prior entry => if entry.1 == node.task.occurrence then some entry.2 else prior)
            node.rejection }) = queue.taskNodes := by
    conv => rhs; rw [← List.map_id queue.taskNodes]
    apply List.map_congr_left
    intro node member
    have loop (entries : List (Occurrence × Nat)) (included : entries.Subset available)
        : entries.foldl
            (fun prior entry => if entry.1 == node.task.occurrence then some entry.2 else prior)
            node.rejection = node.rejection := by
      induction entries with
      | nil => rfl
      | cons entry rest ih =>
          have first : (if entry.1 == node.task.occurrence then some entry.2 else node.rejection)
              = node.rejection := by
            split
            · rename_i same
              exact (cached entry (included List.mem_cons_self) node member
                ((occurrence_beq_iff_eq _ _).mp same).symm).symm
            · rfl
          rw [List.foldl_cons, first]
          exact ih (fun next listed => included (List.mem_cons_of_mem _ listed))
    rw [loop available (List.Subset.refl _)]
    rfl
  rw [nodes]

/-- A complete source-valid batch has consumed every supplied failure, so another cache
exposure leaves its raw endpoint unchanged. This says nothing about earlier FIFO cuts.
-/
theorem State.TaskNodeKeysUnique.replayGraphEvents_cache_fixed {queue : State}
    (unique : queue.TaskNodeKeysUnique) {work before} (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : (queue.replayGraphEvents events
        (GraphEvent.availableFailures events)).cacheTaskFailures
        (GraphEvent.availableFailures events)
      = queue.replayGraphEvents events (GraphEvent.availableFailures events) := by
  apply (unique.replayGraphEvents events
          (GraphEvent.availableFailures events)).cacheTaskFailures_eq_self
  apply queue.replayGraphEvents_failuresCached events valid
  intro entry member
  apply FailureInSnapshot.of_mem member
  intro other received same
  have licensed (candidate : Occurrence × Nat)
      (received : candidate ∈ GraphEvent.availableFailures events)
      : (GraphEvent.taskFailure candidate.1 candidate.2).MatchesWork work := by
    obtain ⟨event, input, identity⟩ := List.mem_filterMap.mp received
    cases event <;> simp only [Option.some.injEq, reduceCtorEq] at identity
    obtain ⟨rfl, rfl⟩ := identity
    exact valid.eachMatches (List.mem_append_right _ input)
  have one := licensed other received
  rw [same] at one
  exact one.taskFailure_count_unique (licensed entry member)

/-- Eager exposure before an actual handler is absorbed by that handler's own exposure. -/
theorem State.TaskNodeKeysUnique.handleGraphEvent_cache {queue : State}
    (unique : queue.TaskNodeKeysUnique) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).handleGraphEvent event available
      = queue.handleGraphEvent event available := by
  simp only [State.handleGraphEvent, unique.cacheTaskFailures_idempotent available]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
