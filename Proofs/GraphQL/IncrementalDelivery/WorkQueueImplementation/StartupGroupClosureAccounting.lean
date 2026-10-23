import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting

/-! Startup group reports remain distinct across activation and later host batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial activation returns distinct reports for already permanently retired groups.
Their local notification delay does not restore any live group record.
-/
theorem State.initializeWithStartup_failureRetirements (work : Execution.Work)
    (startup : InitialStartup)
    : let initial := State.initialize (Work.fromExecution work) startup
      (initial.groupFailureEvents.map (fun failure => failure.group.ref)).Nodup
      ∧ ∀ failure ∈ initial.groupFailureEvents,
          initial.RetiredGroup failure.group.ref := by
  have empty : ({} : State).LiveGroupsRegistered := by intro node member; cases member
  have live := (empty.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  have accounted := State.startNewWork_failureRetirements
    live
    (initialPreparation work).2 startup.failures
  unfold State.initialize
  simpa only [State.enqueueGroupFailures, State.startNewWork_groupFailureEvents,
    State.pruneEmptyGroups_groupFailureEvents,
    State.maybeIntegrateWork_groupFailureEvents, List.nil_append, initialPreparation,
    State.RetiredGroup]
    using accounted

/-- Synchronous startup establishes the same pending-control invariant as ordinary dispatch. -/
theorem State.initializeWithStartup_pendingGroupFailures (work : Execution.Work)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).PendingGroupFailures := by
  have retained := State.initializeWithStartup_failureRetirements work startup
  refine ⟨retained.1, ?_⟩
  intro ref member
  obtain ⟨failure, queued, same⟩ := List.mem_map.mp member
  exact same ▸ retained.2 failure queued

/-- Actual startup replay inherits distinct, retired group closures from its initializer. -/
theorem State.startup_runNormalized_groupClosuresUnique {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (_matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    (_started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      ((initial.runNormalized batches).2.flatten.flatMap groupClosureRefs).Nodup := by
  have empty : ({} : State).LiveGroupsRegistered := by intro node member; cases member
  have live : (State.initialize (Work.fromExecution work) startup).LiveGroupsRegistered := by
    unfold State.initialize
    exact ((empty.maybeIntegrateWork _).pruneEmptyGroups _).startNewWork _ startup.failures
  exact (State.runNormalized_groupClosures live
    (State.initializeWithStartup_pendingGroupFailures work startup) batches).1

/-- Atomic splitting retains the same nonrepeating startup group-closure list. -/
theorem State.startup_runNormalized_atomicGroupClosuresUnique {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).flatMap
        groupClosureRefs).Nodup := by
  dsimp only
  rw [List.flatMap_assoc]
  simp only [publicationAtoms_groupClosureRefs]
  exact State.startup_runNormalized_groupClosuresUnique startup matching started

/-- An actual startup group completion has no earlier same-ref group completion. -/
theorem State.startup_runNormalized_groupUnclosedAt {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true) {index : Nat} {event ref}
    (selected
      : let initial := State.initialize (Work.fromExecution work) startup
        ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
        = some event)
    (closure : ref ∈ groupClosureRefs event)
    : let initial := State.initialize (Work.fromExecution work) startup
      ref
      ∉ (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).take
          index).flatMap
          groupClosureRefs :=
  groupClosuresUnique_atEvent
    (State.startup_runNormalized_atomicGroupClosuresUnique startup
      (fun _ member => valid.eachMatches member) started)
    selected closure

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
