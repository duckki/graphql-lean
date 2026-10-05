import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementPrefixes

/-! Singleton owners cannot be silently accounted for through another owner's notice.
These consequences of work admission deliberately do not apply to shared owner lists.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Publication and cancellation identify the sole owner
-----------------------------------------------------------------------------------------

/-- A cancelled producer-free singleton-owned task has a failed owner at the same cut.
Witness: preserve the historical cut and invert its snapshot cancellation rule;
producer cases contradict the task's unique root descriptor.
-/
theorem TaskCancelled.singleton_root_failed
    {work matching events failures occurrence ref payload}
    (cancelled : TaskCancelled work matching events failures occurrence)
    (known : TaskAt work occurrence [ref] none payload)
    : NodeFailed work matching events failures ref := by
  obtain ⟨cut, member, reached, cancelled⟩ := cancelled
  refine ⟨cut, member, reached, ?_⟩
  cases cancelled with
  | owners projected _ nonempty failedOwners =>
      obtain ⟨producer, result, task⟩ := projected
      have same := (TaskAt.unique task known).1
      exact failedOwners ref (by simp [same])
  | producerFailed projected _ failure | producerCancelled projected _ cancelled =>
      obtain ⟨owners, result, task⟩ := projected
      have impossible := (TaskAt.unique task known).2.1
      cases impossible

/-- A published singleton-owned task has announced its sole owner's ref. Witness: the
value event chooses an open contributing owner; uniqueness of the task's owner list
identifies that ref, and prefix announcements remain present in the full history.
-/
theorem Explains.singleton_published_announced
    {work groups streams events matching failures occurrence ref producer payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence [ref] producer payload)
    (published : Published matching events occurrence)
    : ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have length : (events.take index).length = index := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have allowed := explained.2.2 index event selected
  have before : ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
      (events.take index) := by
    cases event <;> simp only [IsValue] at value
    all_goals try contradiction
    case groupValues owner values =>
      simp only [EventAllowed, length, same] at allowed
      obtain ⟨owners, producer, ⟨path, data, errors, deliveryGroups⟩, _, task, _, chosen⟩ := allowed
      have ownersSame := (TaskAt.unique task known).1
      have refSame : owner.ref = ref := by
        simpa only [ownersSame, List.mem_singleton] using chosen.1.2.1
      exact refSame ▸ chosen.1.2.2.1
    case streamValues owner values newGroups newStreams =>
      simp only [EventAllowed, length, same] at allowed
      obtain ⟨owners, producer, ⟨item, errors⟩, _, task, _, chosen, _⟩ := allowed
      have ownersSame := (TaskAt.unique task known).1
      have refSame : owner.ref = ref := by
        simpa only [ownersSame, List.mem_singleton] using chosen.1.2.1
      exact refSame ▸ chosen.1.2.2.1
  rcases List.mem_append.mp before with initial | pending
  · exact List.mem_append_left _ initial
  · apply List.mem_append_right
    obtain ⟨output, member, notices⟩ := List.mem_flatMap.mp pending
    exact List.mem_flatMap.mpr ⟨output, List.mem_of_mem_take member, notices⟩

-----------------------------------------------------------------------------------------
-- A singleton failure retains an open reporting owner
-----------------------------------------------------------------------------------------

/-- An accepted singleton-owned failure has its sole owner open at settlement.
Witness: licensing announces that owner and excludes earlier cancellation. A prior
completion would either fail that sole owner or account for this task; its fixed failing
payload excludes publication. Shared tasks may settle after one co-owner closes, so this
conclusion deliberately requires singleton ownership.
-/
theorem Explains.singleton_failure_open
    {work groups streams events matching failures cut occurrence ref producer payload}
    (explained : Explains work groups streams events matching failures)
    (recorded : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence [ref] producer payload)
    : Open ((groups ++ streams).map DeliveryNode.ref) (events.take cut) ref := by
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp recorded
  rw [equal] at explained
  have licensed := explained.2.1 before cut occurrence after rfl
  obtain ⟨owner, contributes, announced⟩ := explained.2.1.announced_owner
    (cut := cut) (by simp) known
  have same : owner = ref := List.mem_singleton.mp contributes
  subst owner
  refine ⟨announced, ?_⟩
  intro closed
  have earlier := explained.before_settlement
  have unpublished : ¬Published matching (events.take cut) occurrence := by
    intro published
    apply explained.failed_unpublished (occurrence := occurrence)
      (mem_failedBefore (occurrence := occurrence) (by simp) (Nat.le_refl cut))
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  apply licensed.2.2.2
  rcases earlier.completed_accounted closed with failed | accounted
  · apply earlier.snapshot_taskCancelled
    refine .owners ⟨producer, payload, known⟩ unpublished (by simp) ?_
    intro owner contributes
    have same : owner = ref := List.mem_singleton.mp contributes
    subst owner
    exact earlier.nodeFailed_snapshot failed
  · exact (accounted occurrence [ref] ⟨producer, payload, known⟩ (by simp)).resolve_right
      unpublished

-----------------------------------------------------------------------------------------
-- Healthy singleton-root accounting requires an announced ID
-----------------------------------------------------------------------------------------

/-- Accounting for a healthy singleton-owned root task entails owner announcement.
Witness: cancellation would fail the owner, so accounting must be a licensed publication.
-/
theorem Explains.singleton_accounted_announced
    {work groups streams events matching failures occurrence ref payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence [ref] none payload)
    (healthy : ¬NodeFailed work matching events failures ref)
    (accounted : TaskAccounted work matching events failures occurrence)
    : ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events := by
  rcases accounted with cancelled | published
  · exact False.elim (healthy (cancelled.singleton_root_failed known))
  · exact explained.singleton_published_announced known published

/-- A healthy dependency represented by a singleton-owned root task is satisfied exactly
when its ID has completed. Witness: its descriptor excludes absence, and the preceding
announcement theorem excludes the unannounced-accounted alternative. This reduction is
not valid for general shared-owner work.
-/
theorem Explains.singleton_dependency_iff_completed
    {work groups streams events matching failures occurrence ref payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence [ref] none payload)
    (healthy : ¬NodeFailed work matching events failures ref)
    : DependencySatisfied work ((groups ++ streams).map DeliveryNode.ref) matching events
        failures ref
      ↔ ref ∈ completedRefs events := by
  constructor
  · rintro ⟨_, absent | completed | ⟨unannounced, accounted⟩⟩
    · obtain ⟨node, kind, dependencies, birth, descriptor, same⟩ :=
        known.owner_known (by simp : ref ∈ [ref])
      exact False.elim (absent ⟨birth, node, kind, dependencies, descriptor, same⟩)
    · exact completed
    · exact False.elim (unannounced (explained.singleton_accounted_announced known healthy
        (accounted occurrence [ref] ⟨none, payload, known⟩ (by simp))))
  · exact fun completed => ⟨healthy, Or.inr (Or.inl completed)⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
