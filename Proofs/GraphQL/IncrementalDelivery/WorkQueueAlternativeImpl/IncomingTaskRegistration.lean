import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AdoptedSourceRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationReceiptCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerOrder

/-! Fresh incoming tasks at the actual accepted registration boundary. Rejected tasks
receive the public abort operation; retained tasks have real live memberships, not merely
entries in the permanent proof catalogue. Later release/drain preservation is separate.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence TaskAt)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Observe the exact immediate task chunk accepted by the public registration branch
-----------------------------------------------------------------------------------------

/-- Proof-side projection of the public registration cleanup's returned-task list.
It includes only accepted immediate work, never recursively evaluated latent computations.
-/
def acceptedChildTasks (before : Kernel) : GraphEvent → List Task
  | .taskSuccess occurrence result =>
      match before.taskNode? occurrence with
      | none => []
      | some node =>
          if before.taskHasHealthyOwner node.task then result.work.tasks else []
  | .streamItems stream items =>
      if before.rootStreams.contains stream.ref then
        items.flatMap (fun item => item.work.tasks)
      else
        []
  | _ => []

/-- Every ownerless accepted task receives an abort in this same dispatch, even when
no computation node was started. The unsettled registration frame justifies receipt-wide
retention; no native acquisition or desired endpoint conclusion is assumed.
-/
theorem registration_rejectedTask_aborted {before : Kernel} {event task work settled}
    (frame : RegistrationFrame before settled)
    (matching : event.MatchesWork work) (fresh : task.occurrence ∉ settled)
    (returned : task ∈ acceptedChildTasks before event)
    (ownerless
      : ∀ owner ∈ task.groups,
          (registrationSnapshot before event).groupNode? owner.ref = none)
    : .abortTask task.occurrence
      ∈ (({ state := { queue := before } } : GraphBatchResult).handleGraphEvent
          event).effects := by
  have emitted : .abortTask task.occurrence ∈
      (({ queue := before } : State).handleGraphEvent event).2.2 := by
    cases event with
    | taskSuccess occurrence result =>
        cases found : before.taskNode? occurrence with
        | none => simp [acceptedChildTasks, found] at returned
        | some node =>
            cases healthy : before.taskHasHealthyOwner node.task with
            | false => simp [acceptedChildTasks, found, healthy] at returned
            | true =>
                simp only [acceptedChildTasks, found, healthy, ↓reduceIte] at returned
                simp only [registrationSnapshot, found, healthy, ↓reduceIte] at ownerless
                exact State.taskSuccess_ownerless_aborted found healthy rfl task returned ownerless
    | streamItems stream items =>
        cases active : before.rootStreams.contains stream.ref with
        | false => simp only [acceptedChildTasks, active, Bool.false_eq_true,
            ↓reduceIte, List.not_mem_nil] at returned
        | true =>
            simp only [acceptedChildTasks, active, ↓reduceIte] at returned
            rw [registrationSnapshot_itemFold before stream items active] at ownerless
            exact streamItems_ownerless_aborted frame
              (fun item member => matching.streamItem_childTasksCovered member)
              active returned fresh ownerless
    | taskFailure | streamSuccess | streamFailure => cases returned
  unfold GraphBatchResult.handleGraphEvent
  exact List.mem_append_right _ emitted

/-- The registration snapshot's permanent catalogue contains every accepted task.
Subsequent item registration preserves prior entries; this says nothing about live owners.
-/
theorem registrationSnapshot_acceptedTask_registered {before : Kernel} {event task}
    (returned : task ∈ acceptedChildTasks before event)
    : task ∈ (registrationSnapshot before event).tasks := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : before.taskNode? occurrence with
      | none => simp [acceptedChildTasks, found] at returned
      | some node =>
          cases healthy : before.taskHasHealthyOwner node.task with
          | false => simp [acceptedChildTasks, found, healthy] at returned
          | true =>
              simp only [acceptedChildTasks, found, healthy, ↓reduceIte] at returned
              simp only [registrationSnapshot, found, healthy, ↓reduceIte,
                State.maybeIntegrateWork_tasks]
              exact List.mem_append_right _ returned
  | streamItems stream items =>
      cases active : before.rootStreams.contains stream.ref with
      | false => simp only [acceptedChildTasks, active, Bool.false_eq_true,
          ↓reduceIte, List.not_mem_nil] at returned
      | true =>
          simp only [acceptedChildTasks, active, ↓reduceIte] at returned
          rw [registrationSnapshot_itemFold before stream items active]
          have loop (more : List ReferenceWorkQueue.StreamItem) (current : StreamRegistrationAcc)
              : (more.foldl streamRegistrationStep current).1.queue.tasks
                  = current.1.queue.tasks ++ more.flatMap (fun item => item.work.tasks) := by
            induction more generalizing current with
            | nil => simp
            | cons item rest ih =>
                simp only [List.foldl_cons, ih,
                  streamRegistrationStep_tasks,
                  List.flatMap_cons, List.append_assoc]
          rw [loop]
          exact List.mem_append_right _ returned
  | taskFailure | streamSuccess | streamFailure => cases returned

-----------------------------------------------------------------------------------------
-- Generated replay derives unsettled links at this same registration snapshot
-----------------------------------------------------------------------------------------

/-- Registration preserves all unsettled links. Matching work supplies registry coverage
for each item; no live-owner or desired cleanup conclusion is assumed.
-/
private theorem eagerRegistrationSnapshot_unsettledLinks {queue : Kernel} {work settled}
    (accounted : queue.PendingAccounting work settled) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : (eagerRegistrationSnapshot queue event).UnsettledTaskLinks settled := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using accounted.links
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false => simpa only [eagerRegistrationSnapshot, found, healthy,
              Bool.false_eq_true, ↓reduceIte] using accounted.links
          | true =>
              simp only [eagerRegistrationSnapshot, found, healthy, ↓reduceIte]
              exact (accounted.links.putTaskNode _).maybeIntegrateWork accounted.refs
                accounted.taskGroups result.work (some occurrence)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false => simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true,
          ↓reduceIte] using accounted.links
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          let invariant (current : Kernel) := current.UnsettledTaskLinks settled
            ∧ current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
          suffices invariant (queue.preparedStreamItems items) from this.1
          apply ReferenceWorkQueue.State.preparedStreamItems_preserves invariant
            ⟨accounted.links, accounted.refs, accounted.liveGroups, accounted.taskGroups⟩ items
          intro current item member prior
          have registered := current.maybeIntegrateWork_registration prior.2.2.1 prior.2.2.2
            item.work (matching.streamItem_childTasksCovered member)
          have pruned := ReferenceWorkQueue.State.pruneEmptyGroups_registration
            registered.1 registered.2.1 (current.maybeIntegrateWork item.work).2.newGroups
          exact ⟨((prior.1.maybeIntegrateWork prior.2.1 prior.2.2.2 item.work).pruneEmptyGroups _).startNewWork _,
            ((prior.2.1.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _,
            ReferenceWorkQueue.State.startNewWork_registration pruned.1 pruned.2.1 _⟩
  | taskFailure | streamSuccess | streamFailure => exact accounted.links

/-- The delayed snapshot retains all reference unsettled links through its accounting core. -/
theorem registrationSnapshot_unsettledLinks {queue : Kernel} {work settled}
    (accounted : queue.PendingAccounting work settled) (event : GraphEvent)
    (projection : SnapshotProjection queue event)
    (matching : event.MatchesWork work)
    : (registrationSnapshot queue event).UnsettledTaskLinks settled := by
  change (registrationCore (registrationSnapshot queue event)).UnsettledTaskLinks settled
  rw [projection.core]
  exact eagerRegistrationSnapshot_unsettledLinks accounted event matching

/-- Accepted child tasks are a membership projection of this input's immediate child chunk. -/
theorem acceptedChildTasks_subset (queue : Kernel) (event : GraphEvent)
    : (acceptedChildTasks queue event).Subset event.childTasks := by
  intro task returned
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simp only [acceptedChildTasks, found, List.not_mem_nil] at returned
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false => simp only [acceptedChildTasks, found, healthy, Bool.false_eq_true,
              ↓reduceIte, List.not_mem_nil] at returned
          | true => simpa only [acceptedChildTasks, found, healthy, ↓reduceIte,
              ReferenceWorkQueue.GraphEvent.childTasks] using returned
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false => simp only [acceptedChildTasks, active, Bool.false_eq_true,
          ↓reduceIte, List.not_mem_nil] at returned
      | true => simpa only [acceptedChildTasks, active, ↓reduceIte,
          ReferenceWorkQueue.GraphEvent.childTasks] using returned
  | taskFailure | streamSuccess | streamFailure => cases returned

/-- Accepted immediate child tasks are fresh against the actual preceding input history.
The structural producer cannot have settled before the source admits its child's chunk.
-/
theorem acceptedChildTask_unsettled {queue : Kernel} {work before event task}
    (matching : event.MatchesWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work before) (fresh : event.Fresh before)
    (returned : task ∈ acceptedChildTasks queue event)
    : task.occurrence ∉ before.flatMap (fun prior => prior.identities.1) :=
  matching.childTasks_unsettled valid fresh
    (acceptedChildTasks_subset queue event returned)

/-- Structural child identity selects an immediate task in an actually adopted chunk.
Catalogue membership is derived from matching work, not inferred from a native inventory.
-/
theorem adoptedTask_returned {queue : Kernel} {work event producer address owners payload}
    (matching : event.MatchesWork work)
    (adopted : .adopt producer ∈ graphEffects queue event)
    (known : TaskAt work (.executionGroup address) owners (some producer) payload)
    : ∃ task ∈ acceptedChildTasks queue event,
        task.occurrence = .executionGroup address := by
  cases event with
  | taskSuccess incoming result =>
      cases found : queue.taskNode? incoming with
      | none => simp [graphEffects, found] at adopted
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false => simp [graphEffects, found, healthy] at adopted
          | true =>
              have same : producer = incoming := by
                simpa only [graphEffects, found, healthy, ↓reduceIte, List.mem_singleton,
                  HostEffect.adopt.injEq]
                  using adopted
              subst producer
              obtain ⟨task, returned, identity, _⟩ := matching.taskChildren_complete known
              exact ⟨
                task,
                by
                  simpa only [acceptedChildTasks, found, healthy, ↓reduceIte]
                    using returned,
                identity
              ⟩
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false => simp only [graphEffects, active, Bool.false_eq_true, ↓reduceIte,
          List.nil_append, List.mem_singleton, reduceCtorEq] at adopted
      | true =>
          have listed : .adopt producer ∈ items.map (fun item => HostEffect.adopt item.occurrence) := by
            simpa only [graphEffects, active, ↓reduceIte, List.mem_append,
              List.mem_singleton, reduceCtorEq, or_false]
              using adopted
          obtain ⟨item, selected, same⟩ := List.mem_map.mp listed
          have identity : item.occurrence = producer := HostEffect.adopt.inj same
          obtain ⟨task, returned, taskIdentity, _⟩ := matching.streamItemChildren_complete
            selected (identity.symm ▸ known)
          exact ⟨
            task,
            by
              simp only [acceptedChildTasks, active, ↓reduceIte]
              exact List.mem_flatMap.mpr ⟨item, selected, returned⟩,
            taskIdentity
          ⟩
  | taskFailure | streamSuccess => cases adopted
  | streamFailure stream errors =>
      simp only [graphEffects] at adopted
      split at adopted <;> simp at adopted

/-- Generated started prefixes supply unsettled links in the exact next snapshot.
The proof-only settlement list contains only earlier input task outcomes.
-/
theorem generatedSnapshot_unsettledLinks {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
        event).UnsettledTaskLinks
        (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) := by
  obtain ⟨raw, priorStarted, accepted⟩ := generatedReplay_beforeNext generated valid started
  have projection := generatedSnapshot_projection generated valid priorStarted
  obtain ⟨prior, matching, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  rw [raw] at projection ⊢
  apply registrationSnapshot_unsettledLinks _ event projection matching
  exact (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated inputs.flatten prior accepted

-----------------------------------------------------------------------------------------
-- Every incoming structural task is retained or rejected explicitly at registration
-----------------------------------------------------------------------------------------

/-- Registration coverage for every structurally identified adopted task, not only the
previous counterexample. The retained alternative is a live group membership in the
pre-release snapshot; preservation through subsequent publication/drain is a separate leaf.
-/
def GeneratedAdoptedTaskRegistrationProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ producer address owners payload,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        .adopt producer ∈ graphEffects before.queue event
        → TaskAt work (.executionGroup address) owners (some producer) payload
        → RecordTargetRepresented (registrationSnapshot before.queue event)
            (.task (.executionGroup address))
          ∨ .abortTask (.executionGroup address) ∈ reduced.effects

/-- Universal registration construction. Freshness supplies actual membership links;
an absent owner supplies the public abort effect. Native leases are never manufactured.
-/
theorem GeneratedAdoptedTaskRegistrationProgress_holds
    : GeneratedAdoptedTaskRegistrationProgress := by
  intro work inputs event generated valid started producer address owners payload
  dsimp only
  intro adopted known
  let before := ((State.initialize work).runNormalized inputs).1
  let snapshot := registrationSnapshot before.queue event
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨raw, _, accepted⟩ := generatedReplay_beforeNext generated valid started
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated inputs.flatten prior accepted
  have frame : RegistrationFrame before.queue
      (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) := by
    rw [raw]
    exact ⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.links⟩
  obtain ⟨task, returned, identity⟩ := adoptedTask_returned matching adopted known
  have unsettled : task.occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten := by
    intro settled
    exact acceptedChildTask_unsettled matching prior fresh returned
      (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _ settled)
  have linked := generatedSnapshot_unsettledLinks generated valid started task
    (registrationSnapshot_acceptedTask_registered returned) unsettled
  by_cases owned :
    ∃ owner ∈ task.groups, ∃ group, snapshot.groupNode? owner.ref = some group
  · obtain ⟨owner, contributes, group, found⟩ := owned
    refine Or.inl (.task found ?_)
    rw [← identity]
    apply linked group (List.mem_of_find?_eq_some found)
    exact List.mem_map.mpr ⟨owner, contributes, (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩
  · have ownerless : ∀ owner ∈ task.groups, snapshot.groupNode? owner.ref = none := by
      intro owner member
      cases found : snapshot.groupNode? owner.ref with
      | none => rfl
      | some group => exact False.elim (owned ⟨owner, member, group, found⟩)
    have aborted := registration_rejectedTask_aborted frame matching unsettled returned ownerless
    have canonical := generatedReplay_beforeNextState generated valid started
    dsimp only at canonical
    change before = { queue := before.queue } at canonical
    refine Or.inr ?_
    change .abortTask (.executionGroup address) ∈
      (({ state := before } : GraphBatchResult).handleGraphEvent event).effects
    rw [canonical]
    exact identity ▸ aborted

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
