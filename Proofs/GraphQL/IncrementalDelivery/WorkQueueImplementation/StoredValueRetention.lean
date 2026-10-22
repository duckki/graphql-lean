import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLookupUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
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
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask started available).taskNode? occurrence = some node := by
  unfold State.startTask
  split
  · exact found
  · split
    · exact found
    · change (queue.taskNodes ++ _).find? _ = some node
      rw [List.find?_append]
      change (queue.taskNode? occurrence).or _ = some node
      simp [found]

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
    (same : owner.group.node.ref = contributor.ref)
    : (queue.removeGroup removed).taskNode? occurrence = some node := by
  have keep : node.task.groups.any (fun group =>
      (queue.removeGroup removed).groupNodes.any
        (fun owner => owner.group.node.ref == group.ref)) = true := by
    exact List.any_eq_true.mpr ⟨contributor, contributes,
      List.any_eq_true.mpr ⟨owner, live, beq_iff_eq.mpr same⟩⟩
  change (queue.taskNodes.filter _).find? _ = some node
  exact find_filter_of_kept found keep

/-- Exposing other computations' rejections preserves an exact existing task record. -/
theorem State.cacheTaskFailures_lookup_existing {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (available : List (Occurrence × Nat))
    (notAvailable : ∀ errors, (occurrence, errors) ∉ available)
    : (queue.cacheTaskFailures available).taskNode? occurrence = some node := by
  induction available generalizing queue with
  | nil => exact found
  | cons entry rest ih =>
      obtain ⟨other, errors⟩ := entry
      have different : other ≠ occurrence := by
        intro same
        subst other
        exact notAvailable errors List.mem_cons_self
      have remaining : ∀ errors, (occurrence, errors) ∉ rest :=
        fun count member => notAvailable count (List.mem_cons_of_mem _ member)
      unfold State.cacheTaskFailures
      simp only [List.foldl_cons]
      apply ih (notAvailable := remaining)
      split
      · exact found
      · rename_i cached selected
        apply State.putTaskNode_lookup_other found
        simpa only [(State.taskNode?_some selected).2] using different

private def LookupWithOwner (queue : State) (occurrence : Occurrence) (node : TaskNode)
    (ref : NodeRef)
    : Prop :=
  ∀ owner ∈ queue.groupNodes,
    owner.group.node.ref = ref → queue.taskNode? occurrence = some node

private theorem LookupWithOwner.startTask {queue occurrence node ref}
    (prior : LookupWithOwner queue occurrence node ref) (task : Occurrence)
    (available : List (Occurrence × Nat))
    : LookupWithOwner (queue.startTask task available) occurrence node ref := by
  intro owner member same
  rw [State.startTask_groupNodes] at member
  exact State.startTask_lookup_existing (prior owner member same) task available

private theorem LookupWithOwner.startGroup {queue occurrence node}
    {contributor : Execution.DeliveryNode}
    (prior : LookupWithOwner queue occurrence node contributor.ref)
    (contributes : contributor ∈ node.task.groups) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    (notAvailable : ∀ errors, (occurrence, errors) ∉ available)
    : LookupWithOwner (queue.startGroup ref available).1 occurrence node
        contributor.ref := by
  have cached : LookupWithOwner (queue.cacheTaskFailures available) occurrence node
      contributor.ref := by
    intro owner member same
    rw [State.cacheTaskFailures_groupNodes] at member
    exact State.cacheTaskFailures_lookup_existing (prior owner member same) available notAvailable
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · have loop (tasks : List Occurrence) (current : State)
          (valid : LookupWithOwner current occurrence node contributor.ref)
          : LookupWithOwner (tasks.foldl (fun current task => current.startTask task available)
              current) occurrence node contributor.ref := by
        induction tasks generalizing current with
        | nil => exact valid
        | cons task rest ih => exact ih _ (valid.startTask task available)
      exact loop _ _ cached
    · intro owner member same
      exact State.removeGroup_lookup_survivingOwner
        (cached owner (List.mem_filter.mp member).1 same) _ contributes member same

/-- Startup retains an exact stored task record while a contributing owner survives.
Available rejections may update other records; the task's own outcome is excluded from
that snapshot. Immediate last-owner removal therefore requires the explicit survivor.
-/
theorem State.startNewWork_lookup_existing {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    (notAvailable : ∀ errors, (occurrence, errors) ∉ available := by
      intro errors member; cases member)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode}
    (live : owner ∈ (queue.startNewWork released available).1.groupNodes)
    (same : owner.group.node.ref = contributor.ref)
    : (queue.startNewWork released available).1.taskNode? occurrence = some node := by
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (valid : LookupWithOwner acc.1 occurrence node contributor.ref)
      : LookupWithOwner (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1 occurrence node contributor.ref := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih =>
        exact ih _ (valid.startGroup contributes ref available notAvailable)
  have streams (refs : NodeRefs) (current : State)
      (valid : LookupWithOwner current occurrence node contributor.ref)
      : LookupWithOwner (refs.foldl State.startStream current) occurrence node contributor.ref := by
    induction refs generalizing current with
    | nil => exact valid
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact valid
  have retained : LookupWithOwner (queue.startNewWork released available).1 occurrence node
      contributor.ref := by
    unfold State.startNewWork
    exact streams _ _ (loop _ _ (fun _ _ _ => found))
  exact retained owner live same

/-- Replaying a retained rejection preserves an exact task lookup with any surviving
owner. Witness: its computation already has the selected rejection, so the initial task
replacement changes no first match; subsequent owner steps only filter live records.
-/
theorem State.taskFailure_replay_lookup_survivingOwner {queue : State}
    {group failed errors} (replayed : queue.rejectedTask? group = some (failed, errors))
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode} (live : owner ∈ (queue.taskFailure failed errors).1.groupNodes)
    (same : owner.group.node.ref = contributor.ref)
    : (queue.taskFailure failed errors).1.taskNode? occurrence = some node := by
  obtain ⟨_, task, selected, rejected⟩ := State.rejectedTask?_sound replayed
  let invariant (current : State) := ∀ owner ∈ current.groupNodes,
    owner.group.node.ref = contributor.ref → current.taskNode? occurrence = some node
  have stored : (queue.putTaskNode { task with rejection := some errors }).taskNode? occurrence
      = some node := by
    have identical : { task with rejection := some errors } = task := by rw [← rejected]
    by_cases equal : failed = occurrence
    · subst failed
      have taskEq := Option.some.inj (selected.symm.trans found)
      rw [identical, taskEq]
      exact State.putTaskNode_lookup_same found node (State.taskNode?_some found).2
    · exact State.putTaskNode_lookup_other found _ (by
        simpa only [(State.taskNode?_some selected).2] using equal)
  have initial : invariant (queue.putTaskNode { task with rejection := some errors }) :=
    fun _ _ _ => stored
  rw [queue.taskFailure_eq failed errors task selected] at live ⊢
  have final := failureGroupFold_preserves invariant
    (fun current ref prior owner member same =>
      State.removeGroup_lookup_survivingOwner
        (prior owner (List.mem_filter.mp member).1 same) ref contributes member same)
    errors task.task.groups (queue.putTaskNode { task with rejection := some errors }, []) initial
  exact final owner live same

/-- Failed cleanup preserves a stored task protected by a healthy live contributor.
Witness: canonical removal provenance retains that record, so the live-owner filter
retains the exact task node. This uses internal record health, not assumed wire admission.
-/
theorem State.removeGroup_lookup_healthyOwner {queue : State} {work parents failed}
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    {occurrence node} (found : queue.taskNode? occurrence = some node)
    (removed : Nat) (invalid : GroupRecordInvalidated work failed removed)
    {contributor : Execution.DeliveryNode} (contributes : contributor ∈ node.task.groups)
    {owner : GroupNode} (live : owner ∈ queue.groupNodes)
    (same : owner.group.node.ref = contributor.ref)
    (healthy : ¬GroupRecordInvalidated work failed contributor.ref)
    : (queue.removeGroup removed).taskNode? occurrence = some node := by
  exact State.removeGroup_lookup_survivingOwner found removed contributes
    (queue.removeGroup_recordHealthyRetained links matching canonical removed invalid
      owner live (same ▸ healthy)) same

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
