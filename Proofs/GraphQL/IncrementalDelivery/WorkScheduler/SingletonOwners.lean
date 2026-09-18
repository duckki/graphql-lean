import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.TaskReadiness

/-! Singleton owners cannot be silently accounted for through another owner's notice.
These consequences of work admission deliberately do not apply to shared owner lists.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Publication and cancellation identify the sole owner
-----------------------------------------------------------------------------------------

/-- A cancelled producer-free singleton-owned task has a failed owner. Witness: invert
the cancellation rule; producer cases contradict the task's unique root descriptor.
-/
theorem TaskCancelled.singleton_root_failed {work failed occurrence key payload}
    (cancelled : TaskCancelled work failed occurrence)
    (known : TaskAt work occurrence [key] none payload)
    : NodeFailed work failed key := by
  cases cancelled with
  | owners projected nonempty failedOwners =>
      obtain ⟨producer, result, task⟩ := projected
      have same := (TaskAt.unique task known).1
      exact failedOwners key (by simp [same])
  | producerFailed projected failure | producerCancelled projected cancelled =>
      obtain ⟨owners, result, task⟩ := projected
      have impossible := (TaskAt.unique task known).2.1
      cases impossible

/-- A published singleton-owned task has announced its sole owner's key. Witness: the
value event chooses an open contributing owner; uniqueness of the task's owner list
identifies that key, and prefix announcements remain present in the full history.
-/
theorem Explains.singleton_published_announced
    {work groups streams events matching failures occurrence key producer payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence [key] producer payload)
    (published : Published matching events occurrence)
    : key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have length : (events.take index).length = index := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have allowed := explained.2.2 index event selected
  have before : key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key)
      (events.take index) := by
    cases event <;> simp only [IsValue] at value
    all_goals try contradiction
    case groupValues owner values =>
      simp only [EventAllowed, length, same] at allowed
      obtain ⟨owners, producer, path, data, errors, _, task, _, chosen⟩ := allowed
      have ownersSame := (TaskAt.unique task known).1
      have keySame : owner.key = key := by
        simpa only [ownersSame, List.mem_singleton] using chosen.1.2.1
      exact keySame ▸ chosen.1.2.2.1.1
    case streamValues owner values newGroups newStreams =>
      simp only [EventAllowed, length, same] at allowed
      obtain ⟨owners, producer, item, errors, _, task, _, chosen, _⟩ := allowed
      have ownersSame := (TaskAt.unique task known).1
      have keySame : owner.key = key := by
        simpa only [ownersSame, List.mem_singleton] using chosen.1.2.1
      exact keySame ▸ chosen.1.2.2.1.1
  rcases List.mem_append.mp before with initial | pending
  · exact List.mem_append_left _ initial
  · apply List.mem_append_right
    obtain ⟨output, member, notices⟩ := List.mem_flatMap.mp pending
    exact List.mem_flatMap.mpr ⟨output, List.mem_of_mem_take member, notices⟩

-----------------------------------------------------------------------------------------
-- Healthy singleton-root accounting requires an announced ID
-----------------------------------------------------------------------------------------

/-- Accounting for a healthy singleton-owned root task entails owner announcement.
Witness: cancellation would fail the owner, so accounting must be a licensed publication.
-/
theorem Explains.singleton_accounted_announced
    {work groups streams events matching failures occurrence key payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence [key] none payload)
    (healthy : ¬NodeFailed work (failedBefore failures events.length) key)
    (accounted
      : Accounted work matching events (failedBefore failures events.length) occurrence)
    : key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events := by
  rcases accounted with cancelled | published
  · exact False.elim (healthy (cancelled.singleton_root_failed known))
  · exact explained.singleton_published_announced known published

/-- A healthy dependency represented by a singleton-owned root task is satisfied exactly
when its ID has completed. Witness: its descriptor excludes absence, and the preceding
announcement theorem excludes the unannounced-accounted alternative. This reduction is
not valid for general shared-owner work.
-/
theorem Explains.singleton_dependency_iff_completed
    {work groups streams events matching failures occurrence key payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence [key] none payload)
    (healthy : ¬NodeFailed work (failedBefore failures events.length) key)
    : DependencySatisfied work ((groups ++ streams).map DeliveryNode.key) matching events
        (failedBefore failures events.length) key
      ↔ key ∈ completedKeys events := by
  constructor
  · rintro ⟨_, absent | completed | ⟨unannounced, accounted⟩⟩
    · obtain ⟨node, kind, parents, birth, descriptor, same⟩ :=
        known.owner_known (by simp : key ∈ [key])
      exact False.elim (absent ⟨birth, node, kind, parents, descriptor, same⟩)
    · exact completed
    · exact False.elim (unannounced (explained.singleton_accounted_announced known healthy
        (accounted occurrence [key] ⟨none, payload, known⟩ (by simp))))
  · exact fun completed => ⟨healthy, Or.inr (Or.inl completed)⟩

end GraphQL.IncrementalDelivery.WorkScheduler
