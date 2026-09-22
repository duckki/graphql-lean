import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFlushCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRemoval

/-! Activation and failed-group cleanup retain exact stored values with surviving owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Activation appends empty nodes without changing an existing first-match lookup
-----------------------------------------------------------------------------------------

/-- Starting another task preserves any existing task lookup, including its stored value.
Witness: the only modifying branch appends a node after every existing lookup candidate.
No task-map uniqueness or source-admission premise is needed.
-/
theorem State.startTask_lookup_existing {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (started : Occurrence)
    : (queue.startTask started).taskNode? occurrence = some node := by
  unfold State.startTask
  split
  · exact found
  · split
    · exact found
    · change (queue.taskNodes ++ _).find? _ = some node
      rw [List.find?_append]
      change (queue.taskNode? occurrence).or _ = some node
      simp [found]

/-- Activating released groups and streams retains every earlier exact task lookup.
Witness: group activation iterates append-only task starts; stream activation changes no
task nodes. Payload, contributor list, and child-stream links are preserved together.
-/
theorem State.startNewWork_lookup_existing {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (released : NewWork)
    : (queue.startNewWork released).taskNode? occurrence = some node := by
  have foldLookup {α : Type} (step : State → α → State)
      (preserves : ∀ current item, current.taskNode? occurrence = some node →
        (step current item).taskNode? occurrence = some node)
      (items : List α) (current : State) (prior : current.taskNode? occurrence = some node)
      : (items.foldl step current).taskNode? occurrence = some node := by
    induction items generalizing current with
    | nil => exact prior
    | cons item rest ih => exact ih _ (preserves current item prior)
  have startGroup (current : State) (key : Nat)
      (prior : current.taskNode? occurrence = some node)
      : (current.startGroup key).taskNode? occurrence = some node := by
    unfold State.startGroup
    split
    · exact prior
    · split
      · exact prior
      · exact foldLookup State.startTask (fun _ task lookup =>
          State.startTask_lookup_existing lookup task) _ _ prior
  have startStream (current : State) (key : Nat)
      (prior : current.taskNode? occurrence = some node)
      : (current.startStream key).taskNode? occurrence = some node := by
    unfold State.startStream
    split <;> exact prior
  unfold State.startNewWork
  apply foldLookup State.startStream startStream
  exact foldLookup State.startGroup startGroup _ _ found

-----------------------------------------------------------------------------------------
-- Failure cleanup cannot discard a task while a contributing live record survives
-----------------------------------------------------------------------------------------

/-- Filtering preserves the first selected element when that element passes the filter.
Witness: list induction; skipped earlier elements remain nonmatching.
-/
private theorem find_filter_of_kept {α : Type} {items : List α} {select keep : α → Bool}
    {item : α} (found : items.find? select = some item) (kept : keep item = true)
    : (items.filter keep).find? select = some item := by
  induction items with
  | nil => cases found
  | cons first rest ih =>
      cases chosen : select first with
      | true =>
          have same : first = item := by simpa [chosen] using found
          subst first
          simp [kept, chosen]
      | false =>
          have later : rest.find? select = some item := by simpa [chosen] using found
          cases passes : keep first <;> simpa [passes, chosen] using ih later

/-- Failed-group removal retains an exact lookup with any surviving contributing owner.
Witness: the existing first match passes the executable live-owner filter. Earlier
nonmatching nodes cannot become matches after filtering, even in a raw duplicate map.
-/
theorem State.removeGroup_lookup_survivingOwner {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (removed : Nat)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode} (live : owner ∈ (queue.removeGroup removed).groupNodes)
    (same : owner.group.node.key = contributor.key)
    : (queue.removeGroup removed).taskNode? occurrence = some node := by
  have keep : node.task.groups.any (fun group =>
      (queue.removeGroup removed).groupNodes.any
        (fun owner => owner.group.node.key == group.key)) = true := by
    exact List.any_eq_true.mpr ⟨contributor, contributes,
      List.any_eq_true.mpr ⟨owner, live, beq_iff_eq.mpr same⟩⟩
  change (queue.taskNodes.filter _).find? _ = some node
  exact find_filter_of_kept found keep

/-- Failed cleanup preserves a stored task protected by a healthy live contributor.
Witness: canonical removal provenance retains that record, so the live-owner filter
retains the exact task node. This uses internal record health, not assumed wire admission.
-/
theorem State.removeGroup_lookup_healthyOwner {queue : State} {work parents failed}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.key)
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (removed : Nat) (invalid : GroupRecordInvalidated work failed removed)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode} (live : owner ∈ queue.groupNodes)
    (same : owner.group.node.key = contributor.key)
    (healthy : ¬GroupRecordInvalidated work failed contributor.key)
    : (queue.removeGroup removed).taskNode? occurrence = some node := by
  exact State.removeGroup_lookup_survivingOwner found removed contributes
    (queue.removeGroup_recordHealthyRetained links matching canonical removed invalid
      owner live (same ▸ healthy)) same

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
