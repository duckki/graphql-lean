import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureValueRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseReplay

/-! One task-success publication ledger through snapshot-aware owner release and drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Successful input has one ledger covering both the input and prepared task maps.
Witness: source freshness separates every earlier stored value from the incoming task;
registration preserves those exact lookups before the joint release/drain certificate.
The prepared-state clause additionally covers the newly installed input value.
-/
theorem State.PublicationInventory.taskSuccess_bufferedCoverage {queue : State}
    {work before published settledTasks}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work settledTasks)
    (included : settledTasks.Subset (before.flatMap (fun event => event.identities.1)))
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (occurrence : Occurrence)
    (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (memberships : queue.GroupMembershipOrder)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ task value,
          ObjectValueFrom (before ++ [.taskSuccess occurrence result]) task value
          → ∀ errors, (task, errors) ∉ available := by
        intro task value allowed errors impossible; cases impossible)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.taskSuccess occurrence result available).2.1.flatMap
              WorkQueueEvent.objectValues
        ∧ (queue.taskSuccess occurrence result available).1.PublicationInventory
            (ObjectValueFrom (before ++ [.taskSuccess occurrence result]))
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added
            (queue.taskSuccess occurrence result available).2.1
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → let stored := queue.putTaskNode { node with value := some result.value }
              let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
              prepared.BufferedClosuresCovered added
                (queue.taskSuccess occurrence result available).2.1)
        ∧ StreamReleasePublications work added
            (queue.taskSuccess occurrence result available).2.1
        ∧ queue.StoredValuesConserved added
            (queue.taskSuccess occurrence result available).1
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.StoredValuesConserved
                added (queue.taskSuccess occurrence result available).1)
        ∧ BlocksFollowRegistrations
            (queue.taskSuccess occurrence result available).1.tasks added
            (queue.taskSuccess occurrence result available).2.1
        ∧ queue.StoredOwnersConserved added
            (queue.taskSuccess occurrence result available).1
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.StoredOwnersConserved
                added (queue.taskSuccess occurrence result available).1)
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.ReleaseOwners
                node.task.groups added available)
        ∧ (∀ node,
            queue.taskNode? occurrence = some node
            → ((queue.putTaskNode
                  { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1.ReleaseMembershipsCleared
                node.task.groups added available) := by
  have current := inventory.mono (fun _ _ source =>
    source.mono (List.subset_append_left before [.taskSuccess occurrence result]))
  cases found : queue.taskNode? occurrence with
  | none =>
      refine ⟨
        [],
        by simp [State.taskSuccess, found],
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_,
        ?_
      ⟩
      · simpa only [State.taskSuccess, found, List.append_nil] using current
      · simpa only [State.taskSuccess, found] using State.BufferedClosuresCovered.nil queue
      · intro node impossible
        simp at impossible
      · simpa only [State.taskSuccess, found] using StreamReleasePublications.nil work
      · intro task buffered value lookup _ _
        exact Or.inr (by simpa only [State.taskSuccess, found] using lookup)
      · intro node impossible
        simp at impossible
      · simpa only [State.taskSuccess, found] using BlocksFollowRegistrations.nil queue.tasks []
      · simpa only [State.taskSuccess, found] using State.StoredOwnersConserved.refl queue
      · intro node impossible
        simp at impossible
      · intro node impossible
        simp at impossible
      · intro node impossible
        simp at impossible
  | some node =>
      obtain ⟨added, values, final, preparedCoverage, conservation, streams, ordered,
        owners, drainOwners, drainCleared⟩ :=
        current.taskSuccess_preparedCoverage generated accounted links settled children
          occurrence result matching node found
          (fun member => fresh.2.2.1 occurrence List.mem_cons_self (included member))
          ⟨result, List.mem_append_right _ List.mem_cons_self, rfl⟩
          (inventory.fresh_success fresh) memberships available clean
      have retained : ∀ task buffered value,
          queue.taskNode? task = some buffered → buffered.value = some value
          → ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
              result.work (some occurrence)).1.taskNode? task = some buffered := by
        intro task buffered value lookup stored
        have known := State.taskNode?_some lookup
        have source := (inventory.stored buffered known.1 value stored).1
        have different : occurrence ≠ task := by
          intro same
          exact fresh.2.2.1 occurrence List.mem_cons_self
            (same.symm ▸ known.2 ▸ source.identity)
        have retained := State.putTaskNode_lookup_other lookup
          { node with value := some result.value }
          ((State.taskNode?_some found).2 ▸ different)
        exact State.maybeIntegrateWork_lookup_other retained result.work
          (some occurrence) (fun same => different (Option.some.inj same))
      refine ⟨added, values, final, preparedCoverage.of_lookups retained, ?_, streams,
        State.StoredValuesConserved.of_lookups conservation retained,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro other lookup
        have same := Option.some.inj lookup
        subst other
        exact preparedCoverage
      · intro other lookup
        have same := Option.some.inj lookup
        subst other
        exact conservation
      · rw [State.taskSuccess_tasks found available]
        simpa only [State.maybeIntegrateWork_tasks_append, State.putTaskNode] using ordered
      · exact owners.of_lookups retained
          (State.maybeIntegrateWork_includesRefs
            (queue.putTaskNode { node with value := some result.value })
            result.work (some occurrence))
      · intro other lookup
        have same := Option.some.inj lookup
        subst other
        exact owners
      · intro other lookup
        have same := Option.some.inj lookup
        subst other
        exact drainOwners
      · intro other lookup
        have same := Option.some.inj lookup
        subst other
        exact drainCleared

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
