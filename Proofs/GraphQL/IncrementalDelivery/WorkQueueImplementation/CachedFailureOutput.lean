import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt

/-! Failed closures released by later inputs retain their pre-existing exact error cache. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Recursive release transfers cached-error facts to emitted failures
-----------------------------------------------------------------------------------------

/-- A successful flush emits no failed group closure.
Witness: its output is optional values followed by exactly one successful closure.
-/
theorem State.finishGroupSuccess_groupFailure_absent (queue : State) (node : GroupNode)
    (group : Execution.DeliveryNode) (errors : Nat)
    : Execution.WorkQueueEvent.groupFailure group errors
      ∉ (queue.finishGroupSuccess node).2.1 := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output]
  split <;> simp

/-- Every failed closure emitted by the drain satisfies the original cached-error facts.
Witness: each selected failure emits its exact cache, while all preceding cleanup and
activation preserve the property. Successful flushes emit no failed closure.
-/
theorem State.CachedErrorsSatisfy.drainReadyGroups_output {queue : State} {property}
    (cached : queue.CachedErrorsSatisfy property) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors ∈ queue.drainReadyGroups.2)
    : property group.ref errors := by
  have loop (fuel : Nat) (current : State) (known : current.CachedErrorsSatisfy property)
      (member : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (State.drainReadyGroups.go fuel current).2)
      : property group.ref errors := by
    induction fuel generalizing current with
    | zero => cases member
    | succ fuel ih =>
        unfold State.drainReadyGroups.go at member
        dsimp only at member
        split at member
        · cases member
        · rename_i node selected
          have live : node ∈ current.groupNodes := by
            obtain ⟨ref, _, choice⟩ := List.exists_of_findSome?_eq_some selected
            cases found : current.groupNode? ref with
            | none => simp [found] at choice
            | some candidate =>
                simp only [found] at choice
                change (if _ then some candidate else none) = some node at choice
                split at choice
                · cases Option.some.inj choice
                  exact List.mem_of_find?_eq_some found
                · contradiction
          cases failed : node.failure with
          | none =>
              rw [failed] at member
              rcases List.mem_append.mp member with first | later
              · exact (current.finishGroupSuccess_groupFailure_absent node group errors
                  first).elim
              · exact ih _ ((known.finishGroupSuccess node).startNewWork _) later
          | some count =>
              rw [failed] at member
              rcases List.mem_append.mp member with first | later
              · have same := Execution.WorkQueueEvent.groupFailure.inj (List.mem_singleton.mp first)
                rcases same with ⟨rfl, rfl⟩
                exact known node live errors failed
              · exact ih _ (known.removeGroup node.group.node.ref) later
  exact loop _ queue cached emitted

-----------------------------------------------------------------------------------------
-- Successful inputs can release earlier cached failures, but cannot invent their counts
-----------------------------------------------------------------------------------------

/-- Failed group closures from task success satisfy the pre-input cache predicate.
Witness: integration and the contributor fold preserve caches and emit only success;
the final release-time drain transfers the same facts to its failed closures.
-/
theorem State.CachedErrorsSatisfy.taskSuccess_output {queue : State} {property}
    (cached : queue.CachedErrorsSatisfy property) (occurrence : Occurrence)
    (result : TaskResult) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.taskSuccess occurrence result).2)
    : property group.ref errors := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (known : acc.1.CachedErrorsSatisfy property)
      (absent : Execution.WorkQueueEvent.groupFailure group errors ∉ acc.2.1)
      : (groups.foldl successGroupStep acc).1.CachedErrorsSatisfy property
        ∧ Execution.WorkQueueEvent.groupFailure group errors
          ∉ (groups.foldl successGroupStep acc).2.1 := by
    induction groups generalizing acc with
    | nil => exact ⟨known, absent⟩
    | cons owner rest ih =>
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ known absent
        · rename_i node found
          have updated := known.putGroupNode { node with pending := node.pending - 1 }
            (known node (List.mem_of_find?_eq_some found))
          split
          · apply ih
            · exact updated.finishGroupSuccess _
            · intro member
              exact (List.mem_append.mp member).elim absent
                (State.finishGroupSuccess_groupFailure_absent _ _ group errors)
          · exact ih _ updated absent
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found] at emitted
  | some node =>
      have stored : State.CachedErrorsSatisfy
          (queue.putTaskNode { node with value := some result.value }) property := cached
      have integrated := stored.maybeIntegrateWork result.work (some occurrence)
      obtain ⟨known, absent⟩ := loop node.task.groups (_, [], {}) integrated (by simp)
      rw [queue.taskSuccess_eq occurrence result node found] at emitted
      split at emitted
      · cases emitted
      rcases List.mem_append.mp emitted with first | later
      · exact (absent first).elim
      · exact (known.startNewWork _).drainReadyGroups_output later

/-- Failed group closures from item arrival satisfy the pre-input cache predicate.
Witness: item-child integration never creates a cache; only its trailing drain can
emit failed group closures, each with its unchanged accumulated count.
-/
theorem State.CachedErrorsSatisfy.streamItems_output {queue : State} {property}
    (cached : queue.CachedErrorsSatisfy property) (stream : Execution.DeliveryNode)
    (items : List StreamItem) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.streamItems stream items).2)
    : property group.ref errors := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have loop (items : List StreamItem) (acc)
      (known : acc.1.CachedErrorsSatisfy property)
      : (items.foldl step acc).1.CachedErrorsSatisfy property := by
    induction items generalizing acc with
    | nil => exact known
    | cons item rest ih =>
        exact ih _ (((known.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
  unfold State.streamItems at emitted
  split at emitted
  · cases emitted
  · have later := (List.mem_cons.mp emitted).resolve_left (by intro same; cases same)
    exact (loop items (queue, [], [], []) cached).drainReadyGroups_output later

-----------------------------------------------------------------------------------------
-- Concrete exact-cache provenance, with no source or admission assumptions
-----------------------------------------------------------------------------------------

/-- The queue itself witnesses the exact ref and count in each of its caches.
Witness: the same live node supplies membership and both projection equalities.
-/
theorem State.cachedErrors_fromSelf (queue : State)
    : queue.CachedErrorsSatisfy
        (fun ref errors =>
          ∃ node ∈ queue.groupNodes,
            node.group.node.ref = ref ∧ node.failure = some errors) :=
  fun node member _ same => ⟨node, member, rfl, same⟩

/-- A failed closure released during task success copies an earlier cache exactly.
Witness: specialize arbitrary cached-error preservation to the input state's cache map.
-/
theorem State.taskSuccess_groupFailure_cached (queue : State) (occurrence : Occurrence)
    (result : TaskResult) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.taskSuccess occurrence result).2)
    : ∃ node ∈ queue.groupNodes,
        node.group.node.ref = group.ref ∧ node.failure = some errors :=
  queue.cachedErrors_fromSelf.taskSuccess_output occurrence result emitted

/-- A failed closure released during item arrival copies an earlier cache exactly.
Witness: specialize the item-handler preservation theorem to the input cache map.
-/
theorem State.streamItems_groupFailure_cached (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.streamItems stream items).2)
    : ∃ node ∈ queue.groupNodes,
        node.group.node.ref = group.ref ∧ node.failure = some errors :=
  queue.cachedErrors_fromSelf.streamItems_output stream items emitted

-----------------------------------------------------------------------------------------
-- Failed closures come from this settlement or a pre-existing cache
-----------------------------------------------------------------------------------------

/-- A task-failure handler emits its own count only for one of the task's contributors.
Witness: the actual owner fold emits only active-group failures; latent updates emit none.
-/
theorem State.taskFailure_groupFailure_current (queue : State) (occurrence : Occurrence)
    (errors : Nat) {group count}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group count
        ∈ (queue.taskFailure occurrence errors).2)
    : ∃ task,
        queue.taskNode? occurrence = some task
        ∧ group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref
        ∧ count = errors := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : Execution.WorkQueueEvent.groupFailure group count
          ∈ (groups.foldl (failureGroupStep errors) acc).2
        → Execution.WorkQueueEvent.groupFailure group count ∈ acc.2
          ∨ group.ref ∈ groups.map Execution.DeliveryNode.ref ∧ count = errors := by
    induction groups generalizing acc with
    | nil => exact Or.inl
    | cons owner rest ih =>
        intro member
        obtain ⟨current, events⟩ := acc
        rcases ih (failureGroupStep errors (current, events) owner) member with first | later
        · dsimp only [failureGroupStep] at first
          split at first
          · exact Or.inl first
          · rename_i node found
            split at first
            · rcases List.mem_append.mp first with earlier | latest
              · exact Or.inl earlier
              · have same := Execution.WorkQueueEvent.groupFailure.inj (List.mem_singleton.mp latest)
                exact Or.inr ⟨by simp [same.1, current.groupNode?_ref found], same.2⟩
            · exact Or.inl first
        · exact Or.inr ⟨List.mem_cons_of_mem _ later.1, later.2⟩
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found] at emitted
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found] at emitted
      split at emitted
      · cases emitted
      have origin := loop task.task.groups (queue.removeTask occurrence, []) emitted
      exact ⟨task, rfl, origin.resolve_left (by simp)⟩

/-- Every failed group closure uses either this task failure or an exact earlier cache.
Witness: dispatch the actual handler; successful inputs can drain prior failures, whereas
stream closures emit no group failure. No scheduler admission or source law is assumed.
-/
theorem State.handleGraphEvent_groupFailure_origin (queue : State) (event : GraphEvent)
    {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ (queue.handleGraphEvent event).2)
    : (∃ occurrence task,
        event = .taskFailure occurrence errors
        ∧ queue.taskNode? occurrence = some task
        ∧ group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
      ∨ ∃ node ∈ queue.groupNodes,
          node.group.node.ref = group.ref ∧ node.failure = some errors := by
  cases event with
  | taskSuccess occurrence result =>
      exact Or.inr (queue.taskSuccess_groupFailure_cached occurrence result emitted)
  | taskFailure occurrence count =>
      obtain ⟨task, found, owner, same⟩ :=
        queue.taskFailure_groupFailure_current occurrence count emitted
      subst count
      exact Or.inl ⟨occurrence, task, rfl, found, owner⟩
  | streamItems stream items =>
      exact Or.inr (queue.streamItems_groupFailure_cached stream items emitted)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess] at emitted
      split at emitted <;> simp at emitted
  | streamFailure stream count =>
      simp only [State.handleGraphEvent, State.streamFailure] at emitted
      split at emitted <;> simp at emitted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
