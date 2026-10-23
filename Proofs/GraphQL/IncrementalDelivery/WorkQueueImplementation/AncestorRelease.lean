import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay

/-! Retired ancestry survives successful and cached-failure release-time draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Activation carries old and newly released ancestor certificates
-----------------------------------------------------------------------------------------

/-- Activating work preserves retired ancestors for old and newly announced roots.
Witness: every surviving root came from the old roots or the released group list,
and every earlier retirement remains permanent through startup removal.
-/
theorem State.RootAncestorsRetired.startNewWork {queue : State} {work}
    (prior : queue.RootAncestorsRetired work) (released : NewWork)
    (protectedGroups
      : ∀ group ∈ released.newGroups, queue.AncestorsRetired work group.ref)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.RootAncestorsRetired work := by
  intro ref active
  have active := (queue.startNewWork_rootGroups_sublist released available).subset active
  rcases List.mem_append.mp active with old | new
  · exact (prior ref old).mono (fun ref retired => retired.startNewWork released available)
  · obtain ⟨node, member, same⟩ := List.mem_map.mp new
    exact same ▸ (protectedGroups node member).mono
      (fun ref retired => retired.startNewWork released available)

-----------------------------------------------------------------------------------------
-- Recursive draining needs cache provenance, not health of every active root
-----------------------------------------------------------------------------------------

private structure RetirementDrain (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (failed : List Occurrence)
    : Prop where
  roots : queue.RootAncestorsRetired work
  retirement : queue.HealthyRetiredAncestors work failed
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  live : queue.LiveGroupsRegistered
  contributors : queue.TaskGroupsRegistered
  cached : queue.CachedFailuresSupported work failed
  registered : queue.StartedTasksRegistered
  tasks : queue.RegisteredTasksMatch work
  sound : queue.GroupMembershipSound

/-- Successful draining preserves root and healthy-retirement certificates.
Any removal during subsequent startup is justified by its cached member failures;
already active failures remain subject to their FIFO notification.
-/
theorem State.drainReadyGroups_retirement {queue : State} {work parents failed}
    (roots : queue.RootAncestorsRetired work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (supported : queue.CachedFailuresSupported work failed)
    (started : queue.StartedTasksRegistered)
    (taskMatching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (available : List (Occurrence × Nat) := [])
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.drainReadyGroups available).1.RootAncestorsRetired work
      ∧ (queue.drainReadyGroups available).1.HealthyRetiredAncestors work failed := by
  let invariant (current : State) := RetirementDrain current work parents failed
  have initial : invariant queue :=
    ⟨roots, retirement, matching, links, registered, tasks, supported, started, taskMatching, sound⟩
  have final := State.drainReadyGroups_preserves invariant
    (available := available) (valid := initial) (by
      intro current node prior member active _
      have closed := State.finishGroupSuccess_retirement (failed := failed)
        generated prior.groups prior.links canonical prior.live member (prior.roots _ active)
      have covered := current.finishGroupSuccess_registration prior.live prior.contributors node
      have activated := State.startNewWork_registration covered.1 covered.2.1
        (current.finishGroupSuccess node).2.2 available
      have survivingRoots := prior.roots.mono (current.finishGroupSuccess_rootsSubset node)
        (fun _ retired => retired.finishGroupSuccess node)
      have caches := prior.cached.finishGroupSuccess node
      have started := prior.registered.finishGroupSuccess node
      have taskMatch := prior.tasks.finishGroupSuccess node
      have memberships := prior.sound.finishGroupSuccess node
      have edges := prior.links.finishGroupSuccess node
      have groups := prior.groups.finishGroupSuccess node
      exact ⟨survivingRoots.startNewWork _ closed.2.2.1 available,
        (closed.2.2.2 prior.retirement).startNewWork caches started taskMatch memberships
          edges groups canonical _ available recorded,
        groups.startNewWork _ available, edges.startNewWork _ available,
        activated.1, activated.2,
        caches.startNewWork_available started taskMatch _ available recorded,
        started.startNewWork _ available, taskMatch.startNewWork _ available,
        memberships.startNewWork _ available⟩)
  exact ⟨final.roots, final.retirement⟩

-----------------------------------------------------------------------------------------
-- Retired ancestry closes the object-task availability obligation locally
-----------------------------------------------------------------------------------------

/-- Permanent registration suffices to locate child contributors, even after the producer's
last live owner retires. Source freshness excludes earlier settlement, and retirement
closure supplies the availability certificate from the healthy owner/count projections.
-/
theorem State.OwnerAccountingInInventory.taskSuccess_available_of_registered
    {queue : State} {work parents before occurrence result failed}
    (accounting : queue.OwnerAccountingInInventory work parents before failed)
    (generated : ExecutedWork work) (closure : queue.HealthyRetiredAncestors work failed)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (known : ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    : queue.ChildGroupsAvailable work failed result.work := by
  obtain ⟨task, registered, same⟩ := known
  apply closure.childGroupsAvailable accounting.owners accounting.healthy
    accounting.pending.matching generated registered
  · rw [same]
    exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
      (GraphEvent.taskSettlements_subsetIdentities before member)
  · simpa only [same] using matching

/-- A live task supplies the permanent registration used by contributor availability. -/
theorem State.OwnerAccountingInInventory.taskSuccess_available {queue : State}
    {work parents before occurrence result failed}
    (accounting : queue.OwnerAccountingInInventory work parents before failed)
    (generated : ExecutedWork work)
    (closure : queue.HealthyRetiredAncestors work failed)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (accepted : queue.acceptsGraphEvent (.taskSuccess occurrence result) = true)
    : queue.ChildGroupsAvailable work failed result.work := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some node =>
      exact accounting.taskSuccess_available_of_registered generated closure matching fresh
        ⟨node.task, accounting.pending.started node (List.mem_of_find?_eq_some found),
          (State.taskNode?_some found).2⟩

/-- Boundary accounting specializes the same local availability result. -/
theorem State.OwnerAccounting.taskSuccess_available {queue : State}
    {work parents before occurrence result}
    (accounting : queue.OwnerAccounting work parents before)
    (generated : ExecutedWork work)
    (closure : queue.HealthyRetiredAncestors work (GraphEvent.failureSettlements before))
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (accepted : queue.acceptsGraphEvent (.taskSuccess occurrence result) = true)
    : queue.ChildGroupsAvailable work (GraphEvent.failureSettlements before)
        result.work :=
  State.OwnerAccountingInInventory.taskSuccess_available accounting generated closure
    matching fresh accepted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
