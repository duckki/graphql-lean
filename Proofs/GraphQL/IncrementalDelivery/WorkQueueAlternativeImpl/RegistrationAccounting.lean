import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingAccounting

/-! Reuse reference bookkeeping over complete registration scopes and initialization. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

-----------------------------------------------------------------------------------------
-- Scope registration inherits the reference accounting facts
-----------------------------------------------------------------------------------------

/-- Exact pending counts survive a fresh scope registration through the phase projection. -/
theorem State.maybeIntegrateWork_pendingTracks {state : State} {settled : List Occurrence}
    (tracks : state.queue.PendingTracks settled) (work : ReferenceWorkQueue.Work)
    (fresh : ∀ task ∈ work.tasks, task.occurrence ∉ settled)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.PendingTracks settled := by
  change (registrationCore (state.maybeIntegrateWork work parent).1.queue).PendingTracks settled
  rw [state.maybeIntegrateWork_registrationCore work parent]
  exact tracks.maybeIntegrateWork work fresh parent

/-- Registration preserves pending lower bounds without new host assumptions. -/
theorem State.maybeIntegrateWork_pendingBound {state : State} {eligible settled}
    (bounded : state.queue.PendingBound eligible settled) (work : ReferenceWorkQueue.Work)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.PendingBound eligible settled := by
  change (registrationCore (state.maybeIntegrateWork work parent).1.queue).PendingBound eligible settled
  rw [state.maybeIntegrateWork_registrationCore work parent]
  exact bounded.maybeIntegrateWork work parent

/-- Every scope preserves unique live group keys by the reference proof. -/
theorem State.maybeIntegrateWork_groupKeysUnique {state : State}
    (unique : state.queue.GroupRefsUnique) (work : ReferenceWorkQueue.Work)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.GroupRefsUnique := by
  change (registrationCore (state.maybeIntegrateWork work parent).1.queue).GroupRefsUnique
  rw [state.maybeIntegrateWork_registrationCore work parent]
  exact unique.maybeIntegrateWork work parent

/-- Duplicate-free owner memberships are inherited for complete scopes. -/
theorem State.maybeIntegrateWork_taskMembershipsUnique {state : State}
    (unique : state.queue.TaskMembershipsUnique) (work : ReferenceWorkQueue.Work)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.TaskMembershipsUnique := by
  change (registrationCore (state.maybeIntegrateWork work parent).1.queue).TaskMembershipsUnique
  rw [state.maybeIntegrateWork_registrationCore work parent]
  exact unique.maybeIntegrateWork work parent

/-- Protected old task links and newly established links reuse reference scope accounting. -/
theorem State.maybeIntegrateWork_unsettledTaskLinks {state : State}
    {settled : List Occurrence} (linked : state.queue.UnsettledTaskLinks settled)
    (unique : state.queue.GroupRefsUnique) (registered : state.queue.TaskGroupsRegistered)
    (work : ReferenceWorkQueue.Work) (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.UnsettledTaskLinks settled := by
  change (registrationCore (state.maybeIntegrateWork work parent).1.queue).UnsettledTaskLinks settled
  rw [state.maybeIntegrateWork_registrationCore work parent]
  exact linked.maybeIntegrateWork unique registered work parent

/-- Structurally matched scope tasks preserve permanent-catalogue provenance. -/
theorem State.maybeIntegrateWork_registeredTasksMatch {state : State} {work : Work}
    (matching : state.queue.RegisteredTasksMatch work)
    (incoming : ReferenceWorkQueue.Work)
    (known : ∀ task ∈ incoming.tasks, ReferenceWorkQueue.TaskMatches work task)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork incoming parent).1.queue.RegisteredTasksMatch work := by
  change (registrationCore (state.maybeIntegrateWork incoming parent).1.queue).RegisteredTasksMatch work
  rw [state.maybeIntegrateWork_registrationCore incoming parent]
  exact matching.maybeIntegrateWork incoming known parent

/-- Existing active roots remain present across complete scope registration. -/
theorem State.maybeIntegrateWork_rootsPresent {state : State}
    (present : state.queue.RootGroupsPresent) (work : ReferenceWorkQueue.Work)
    (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.RootGroupsPresent := by
  change (registrationCore (state.maybeIntegrateWork work parent).1.queue).RootGroupsPresent
  rw [state.maybeIntegrateWork_registrationCore work parent]
  exact present.maybeIntegrateWork work parent

/-- Complete registration never removes a live group key; delayed task starts are irrelevant. -/
theorem State.maybeIntegrateWork_includesRefs (state : State)
    (work : ReferenceWorkQueue.Work) (parent : Option Occurrence := none)
    : (state.queue.groupNodes.map (fun node => node.group.node.ref)).Subset
        ((state.maybeIntegrateWork work parent).1.queue.groupNodes.map
          (fun node => node.group.node.ref)) := by
  have groups := congrArg ReferenceWorkQueue.State.groupNodes
    (state.maybeIntegrateWork_registrationCore work parent)
  change (state.maybeIntegrateWork work parent).1.queue.groupNodes
    = (state.queue.maybeIntegrateWork work parent).1.groupNodes at groups
  rw [groups]
  exact state.queue.maybeIntegrateWork_includesRefs work parent

-----------------------------------------------------------------------------------------
-- Startup reuses the complete reference invariant, including started-task provenance
-----------------------------------------------------------------------------------------

/-- Startup inherits the full all-owner invariant, not merely its accounting-core fragment.
Witness: exact initial kernel correspondence transfers the existing reference invariant.
-/
theorem State.initialize_pendingAccounting (work : Work)
    (certified : ReferenceWorkQueue.DeclarationCoverage.Certified [] work)
    : (State.initialize work).queue.PendingAccounting work [] := by
  rw [State.initialize_queue]
  exact ReferenceWorkQueue.createWorkQueue_pendingAccounting work certified

/-- Initial active roots have live records, as established by reference initialization. -/
theorem State.initialize_rootsPresent (work : Work)
    : (State.initialize work).queue.RootGroupsPresent := by
  rw [State.initialize_queue]
  exact ReferenceWorkQueue.createWorkQueue_rootGroupsPresent _

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
