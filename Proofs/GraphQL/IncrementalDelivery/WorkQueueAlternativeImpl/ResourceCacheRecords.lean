import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNodeKeys
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventoryReplay

/-! Concrete resource record locations across common task-failure exposure. Source records
are unaffected; a task record additionally requires its own computation to remain unfinished.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

/-- Exposure leaves an unavailable computation's exact lookup unchanged. -/
theorem taskLookup_cacheTaskFailures {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (occurrence : Occurrence) (fresh : ∀ errors, (occurrence, errors) ∉ available)
    : (queue.cacheTaskFailures available).taskNode? occurrence
      = queue.taskNode? occurrence := by
  cases found : queue.taskNode? occurrence with
  | none => rw [unique.cacheTaskFailures_lookup available, found]; rfl
  | some node =>
      exact ReferenceWorkQueue.State.cacheTaskFailures_lookup_existing found available fresh

/-- Task representation is preserved exactly when this computation is outside the snapshot. -/
theorem taskRecord_cacheTaskFailures_iff {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (occurrence : Occurrence) (fresh : ∀ errors, (occurrence, errors) ∉ available)
    : RecordTargetRepresented (queue.cacheTaskFailures available) (.task occurrence)
      ↔ RecordTargetRepresented queue (.task occurrence) := by
  have lookup := taskLookup_cacheTaskFailures unique available occurrence fresh
  constructor
  · intro represented
    cases represented with
    | task found linked unrejected =>
        rw [lookup] at unrejected
        have prior := found
        simp only [ReferenceWorkQueue.State.groupNode?,
          ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at prior
        exact .task prior linked unrejected
  · intro represented
    cases represented with
    | task found linked unrejected =>
        apply RecordTargetRepresented.task
          (by
            simpa only [ReferenceWorkQueue.State.groupNode?,
              ReferenceWorkQueue.State.cacheTaskFailures_groupNodes]
              using found)
          linked
        rwa [lookup]

/-- A buffered source remains attached to the same task value even if that task rejects. -/
theorem streamRecord_cacheTaskFailures_iff {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (available : List (Occurrence × Nat)) (key : Nat)
    : RecordTargetRepresented (queue.cacheTaskFailures available) (.stream key)
      ↔ RecordTargetRepresented queue (.stream key) := by
  have roots := congrArg ReferenceWorkQueue.State.rootStreams
    (queue.cacheTaskFailures_frame available)
  change (queue.cacheTaskFailures available).rootStreams = queue.rootStreams at roots
  constructor
  · intro represented
    cases represented with
    | activeStream active =>
        exact .activeStream (by simpa only [roots] using active)
    | @bufferedStream occurrence observed _ found stored held =>
        rw [unique.cacheTaskFailures_lookup available] at found
        cases prior : queue.taskNode? occurrence with
        | none => simp [prior] at found
        | some node =>
            simp only [prior, Option.map_some, Option.some.injEq] at found
            subst observed
            exact .bufferedStream prior stored held
  · intro represented
    cases represented with
    | activeStream active =>
        exact .activeStream (by simpa only [roots] using active)
    | @bufferedStream occurrence node _ found stored held =>
        let observed : ReferenceWorkQueue.TaskNode :=
          { node with
            rejection :=
              available.foldl
                (fun prior entry =>
                  if entry.1 == node.task.occurrence then some entry.2 else prior)
                node.rejection }
        have lookup : (queue.cacheTaskFailures available).taskNode? occurrence = some observed := by
          rw [unique.cacheTaskFailures_lookup available, found]
          rfl
        exact .bufferedStream lookup stored held

/-- A common exposure transfers unfinished task records between actual source cuts. -/
theorem taskRecord_of_cache_eq {first second : ReferenceWorkQueue.State}
    (firstKeys : first.TaskNodeKeysUnique) (secondKeys : second.TaskNodeKeysUnique)
    (available : List (Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (occurrence : Occurrence) (fresh : ∀ errors, (occurrence, errors) ∉ available)
    (represented : RecordTargetRepresented second (.task occurrence))
    : RecordTargetRepresented first (.task occurrence) := by
  apply (taskRecord_cacheTaskFailures_iff firstKeys available occurrence fresh).mp
  rw [same]
  exact (taskRecord_cacheTaskFailures_iff secondKeys available occurrence fresh).mpr represented

/-- A common exposure transfers every active or buffered source record. -/
theorem streamRecord_of_cache_eq {first second : ReferenceWorkQueue.State}
    (firstKeys : first.TaskNodeKeysUnique) (secondKeys : second.TaskNodeKeysUnique)
    (available : List (Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (key : Nat) (represented : RecordTargetRepresented second (.stream key))
    : RecordTargetRepresented first (.stream key) := by
  apply (streamRecord_cacheTaskFailures_iff firstKeys available key).mp
  rw [same]
  exact (streamRecord_cacheTaskFailures_iff secondKeys available key).mpr represented

/-- Common exposure transfers the child-source inventory, whose fields ignore rejection slots. -/
theorem childStreamInventory_of_cache_eq {first second : ReferenceWorkQueue.State}
    (firstKeys : first.TaskNodeKeysUnique) (available : List (Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (inventory : second.ChildStreamInventory)
    : first.ChildStreamInventory := by
  have exposedInventory := inventory.cacheTaskFailures available
  rw [← same] at exposedInventory
  have streams := congrArg ReferenceWorkQueue.State.streams
    (first.cacheTaskFailures_frame available)
  change (first.cacheTaskFailures available).streams = first.streams at streams
  intro node member
  let exposed : ReferenceWorkQueue.TaskNode :=
    { node with
      rejection := available.foldl
        (fun prior entry => if entry.1 == node.task.occurrence then some entry.2 else prior)
        node.rejection }
  have included : exposed ∈ (first.cacheTaskFailures available).taskNodes := by
    rw [firstKeys.cacheTaskFailures_nodes available]
    exact List.mem_map_of_mem member
  have captured := exposedInventory exposed included
  change node.childStreams.Nodup ∧ node.childStreams.Subset
    ((first.cacheTaskFailures available).streams.map (fun stream => stream.node.ref)) at captured
  rwa [streams] at captured

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
