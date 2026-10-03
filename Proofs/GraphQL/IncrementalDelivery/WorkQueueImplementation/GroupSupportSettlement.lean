import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupActivationSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Contributor-ref support survives settlement, release, and cached-result draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Successful and failed group closures name supported refs; other events are unchecked.
This tracks contributor existence, not equality of the closing delivery descriptor.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupClosureRefSupported
    (supported : Nat → Prop) : WorkQueueEvent → Prop
  | .groupSuccess group _ _ | .groupFailure group _ => supported group.ref
  | _ => True

/-- A success flush emits a closure only for its supplied supported ref.
Witness: the exact output consists of optional values followed by that group's closure.
-/
theorem State.finishGroupSuccess_groupClosureRefSupported {supported}
    (queue : State) (group : GroupNode) (known : supported group.group.node.ref)
    : ∀ event ∈ (queue.finishGroupSuccess group).2.1,
        event.GroupClosureRefSupported supported := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  intro event member
  rw [output] at member
  rcases List.mem_append.mp member with value | closure
  · split at value
    · cases value
    · have same := List.mem_singleton.mp value
      subst event
      trivial
  · have same := List.mem_singleton.mp closure
    subst event
    exact known

-----------------------------------------------------------------------------------------
-- Settlement cannot give taskless shells contents or release them as active roots
-----------------------------------------------------------------------------------------

/-- Removing a task can only empty a group's membership list.
Witness: each surviving record filters the old memberships and retains its error cache.
-/
theorem State.GroupRefSupport.removeTask {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (occurrence : Occurrence)
    : (queue.removeTask occurrence).GroupRefSupport supported := by
  refine ⟨?_, valid.roots⟩
  intro node member absent
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  subst node
  obtain ⟨tasks, failure⟩ := valid.contents old oldMember absent
  exact ⟨by simp [tasks], failure⟩

/-- Removing a failed subtree preserves support of every surviving record and root.
Witness: both collections are filtered without adding contents or active refs.
-/
theorem State.GroupRefSupport.removeGroup {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (ref : NodeRef)
    : (queue.removeGroup ref).GroupRefSupport supported := by
  constructor
  · intro node member absent
    exact valid.contents node (List.mem_filter.mp member).1 absent
  · intro root member
    exact valid.roots root (List.mem_filter.mp member).1

/-- Flushing a successful group preserves support and releases only supported child refs.
Witness: remove flushed memberships and the closing group, then apply the pruning gate.
-/
theorem State.GroupRefSupport.finishGroupSuccess {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.GroupRefSupport supported
      ∧ ∀ node ∈ (queue.finishGroupSuccess group).2.2.newGroups, supported node.ref := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    match acc.1.taskNode? occurrence with
    | none => acc
    | some taskNode =>
        let values := match taskNode.value with
          | none => acc.2.1
          | some value => acc.2.1 ++ [value]
        (acc.1.removeTask occurrence, values, acc.2.2 ++ taskNode.childStreams)
  have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (known : acc.1.GroupRefSupport supported)
      : (tasks.foldl step acc).1.GroupRefSupport supported := by
    induction tasks generalizing acc with
    | nil => exact known
    | cons occurrence rest ih =>
        apply ih
        unfold step
        split
        · exact known
        · exact known.removeTask occurrence
  let flushed := group.tasks.foldl step (queue, [], [])
  have known := loop group.tasks (queue, [], []) valid
  let current : State := { flushed.1 with
    groupNodes := flushed.1.groupNodes.filter (fun node =>
      node.group.node.ref != group.group.node.ref)
    rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  have retained : current.GroupRefSupport supported :=
    ⟨fun node member => known.contents node (List.mem_filter.mp member).1,
      fun ref member => known.roots ref (List.mem_filter.mp member).1⟩
  exact retained.pruneEmptyGroups _

/-- Recursive draining preserves contributor support, including newly promoted roots.
Witness: each success prunes released children before activation; failures only remove.
-/
theorem State.GroupRefSupport.drainReadyGroups_support {queue : State} {supported}
    (valid : queue.GroupRefSupport supported)
    : queue.drainReadyGroups.1.GroupRefSupport supported
      ∧ ∀ event ∈ queue.drainReadyGroups.2, event.GroupClosureRefSupported supported := by
  have loop (fuel : Nat) (current : State) (known : current.GroupRefSupport supported)
      : (State.drainReadyGroups.go fuel current).1.GroupRefSupport supported
        ∧ ∀ event ∈ (State.drainReadyGroups.go fuel current).2,
            event.GroupClosureRefSupported supported := by
    induction fuel generalizing current with
    | zero => exact ⟨known, by simp [State.drainReadyGroups.go]⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨known, by simp⟩
        · rename_i node selected
          have refSupported : supported node.group.node.ref := by
            obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
            cases found : current.groupNode? ref with
            | none => simp [found] at choice
            | some candidate =>
                simp only [found] at choice
                change (if _ then some candidate else none) = some node at choice
                split at choice
                · cases Option.some.inj choice
                  exact State.groupNode?_ref found ▸ known.roots ref active
                · contradiction
          cases cached : node.failure with
          | none =>
              obtain ⟨retained, released⟩ := known.finishGroupSuccess node
              obtain ⟨next, outputs⟩ := ih _ (retained.startNewWork _ released)
              refine ⟨next, ?_⟩
              intro event member
              exact (List.mem_append.mp member).elim
                (current.finishGroupSuccess_groupClosureRefSupported node refSupported event)
                (outputs event)
          | some errors =>
              obtain ⟨next, outputs⟩ := ih _ (known.removeGroup node.group.node.ref)
              refine ⟨next, ?_⟩
              intro event member
              rcases List.mem_append.mp member with first | later
              · have same := List.mem_singleton.mp first
                subst event
                exact refSupported
              · exact outputs event later
  exact loop _ queue valid

/-- Draining preserves the queue's support invariant.
Witness: project the joint state/output draining theorem.
-/
theorem State.GroupRefSupport.drainReadyGroups {queue : State} {supported}
    (valid : queue.GroupRefSupport supported)
    : queue.drainReadyGroups.1.GroupRefSupport supported :=
  valid.drainReadyGroups_support.1

-----------------------------------------------------------------------------------------
-- The single-pass task handlers and stream-item integration retain the same invariant
-----------------------------------------------------------------------------------------

/-- Task success preserves support even when shared owners close during its single pass.
Witness: matched child owners support integration; pending decrements preserve contents;
each flush releases supported groups before final activation and draining.
-/
theorem State.GroupRefSupport.taskSuccess_support {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (occurrence : Occurrence)
    (result : TaskResult)
    (owners : ∀ task ∈ result.work.tasks, ∀ group ∈ task.groups, supported group.ref)
    : (queue.taskSuccess occurrence result).1.GroupRefSupport supported
      ∧ ∀ event ∈ (queue.taskSuccess occurrence result).2,
          event.GroupClosureRefSupported supported := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (known : acc.1.GroupRefSupport supported)
      (released : ∀ group ∈ acc.2.2.newGroups, supported group.ref)
      (outputs : ∀ event ∈ acc.2.1, event.GroupClosureRefSupported supported)
      : (groups.foldl successGroupStep acc).1.GroupRefSupport supported
        ∧ (∀ group ∈ (groups.foldl successGroupStep acc).2.2.newGroups,
            supported group.ref)
        ∧ ∀ event ∈ (groups.foldl successGroupStep acc).2.1,
            event.GroupClosureRefSupported supported := by
    induction groups generalizing acc with
    | nil => exact ⟨known, released, outputs⟩
    | cons group rest ih =>
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ known released outputs
        · rename_i node found
          have updated := known.putGroupNode { node with pending := node.pending - 1 }
            (known.contents node (List.mem_of_find?_eq_some found))
          split
          · rename_i closes
            have active : group.ref ∈ acc.1.rootGroups := by
              simp only [Bool.and_eq_true, State.putGroupNode,
                List.contains_iff_mem] at closes
              exact closes.1.1
            have refSupported := State.groupNode?_ref found ▸ known.roots group.ref active
            obtain ⟨retained, newGroups⟩ := updated.finishGroupSuccess
              { node with pending := node.pending - 1 }
            refine ih _ retained ?_ ?_
            · intro node member
              exact (List.mem_append.mp member).elim (released node) (newGroups node)
            · intro event member
              exact (List.mem_append.mp member).elim (outputs event)
                (State.finishGroupSuccess_groupClosureRefSupported _ _ refSupported event)
          · exact ih _ updated released outputs
  cases found : queue.taskNode? occurrence with
  | none =>
      exact ⟨
        by simpa [State.taskSuccess, found] using valid,
        by simp [State.taskSuccess, found]
      ⟩
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact ⟨valid.removeTask occurrence, by simp⟩
      · have stored : (queue.putTaskNode { node with value := some result.value }).GroupRefSupport
            supported := ⟨valid.contents, valid.roots⟩
        obtain ⟨known, released, outputs⟩ := loop node.task.groups (_, [], {})
          (stored.maybeIntegrateWork result.work owners (some occurrence)) (by simp) (by simp)
        obtain ⟨next, later⟩ := (known.startNewWork _ released).drainReadyGroups_support
        exact ⟨next, fun event member =>
          (List.mem_append.mp member).elim (outputs event) (later event)⟩

/-- Successful settlement preserves queue support independently of its output projection.
Witness: project the joint single-pass state/output theorem.
-/
theorem State.GroupRefSupport.taskSuccess {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (occurrence : Occurrence)
    (result : TaskResult)
    (owners : ∀ task ∈ result.work.tasks, ∀ group ∈ task.groups, supported group.ref)
    : (queue.taskSuccess occurrence result).1.GroupRefSupport supported :=
  (valid.taskSuccess_support occurrence result owners).1

/-- Task failure can create a cache only at an actual supported task-owner ref.
Witness: remove memberships once, then either remove an active owner or cache its failure.
-/
theorem State.GroupRefSupport.taskFailure_support {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (occurrence : Occurrence) (errors : Nat)
    (owners
      : ∀ node,
          queue.taskNode? occurrence = some node
          → ∀ group ∈ node.task.groups, supported group.ref)
    : (queue.taskFailure occurrence errors).1.GroupRefSupport supported
      ∧ ∀ event ∈ (queue.taskFailure occurrence errors).2,
          event.GroupClosureRefSupported supported := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, event) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [event])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode)
      (all : ∀ group ∈ groups, supported group.ref) (acc : State × List WorkQueueEvent)
      (known : acc.1.GroupRefSupport supported)
      (outputs : ∀ event ∈ acc.2, event.GroupClosureRefSupported supported)
      : (groups.foldl step acc).1.GroupRefSupport supported
        ∧ ∀ event ∈ (groups.foldl step acc).2,
            event.GroupClosureRefSupported supported := by
    induction groups generalizing acc with
    | nil => exact ⟨known, outputs⟩
    | cons group rest ih =>
        refine ih (fun node member => all node (List.mem_cons_of_mem _ member)) _ ?_ ?_
        all_goals unfold step; split
        · exact known
        · rename_i node found
          split
          · exact known.removeGroup node.group.node.ref
          · apply known.putGroupNode
            intro absent
            exact (absent (State.groupNode?_ref found ▸ all group List.mem_cons_self)).elim
        · exact outputs
        · rename_i node found
          split
          · intro event member
            rcases List.mem_append.mp member with old | closed
            · exact outputs event old
            · have same := List.mem_singleton.mp closed
              subst event
              change supported node.group.node.ref
              exact State.groupNode?_ref found ▸ all group List.mem_cons_self
          · exact outputs
  unfold State.taskFailure
  split
  · exact ⟨valid, by simp⟩
  · rename_i node found
    split
    · exact ⟨valid.removeTask occurrence, by simp⟩
    · exact loop node.task.groups (owners node found) (_, [])
        (valid.removeTask occurrence) (by simp)

/-- Failed settlement preserves queue support independently of its output projection.
Witness: project the joint failure-fold state/output theorem.
-/
theorem State.GroupRefSupport.taskFailure {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (occurrence : Occurrence) (errors : Nat)
    (owners
      : ∀ node,
          queue.taskNode? occurrence = some node
          → ∀ group ∈ node.task.groups, supported group.ref)
    : (queue.taskFailure occurrence errors).1.GroupRefSupport supported :=
  (valid.taskFailure_support occurrence errors owners).1

/-- Each stream item may add ancestor shells but can activate only supported contributors.
Witness: integrate the item's supported tasks, prune, activate, then drain the final state.
-/
theorem State.GroupRefSupport.streamItems_support {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (owners
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ∀ group ∈ task.groups, supported group.ref)
    : (queue.streamItems stream items).1.GroupRefSupport supported
      ∧ ∀ event ∈ (queue.streamItems stream items).2,
          event.GroupClosureRefSupported supported := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (integrated, newWork) := acc.1.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      acc.2.1 ++ nonempty, acc.2.2.1 ++ newWork.newStreams, acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (subset : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (known : acc.1.GroupRefSupport supported)
      : (more.foldl step acc).1.GroupRefSupport supported := by
    induction more generalizing acc with
    | nil => exact known
    | cons item rest ih =>
        apply ih (fun _ h => subset (List.mem_cons_of_mem _ h))
        have integrated := known.maybeIntegrateWork item.work
          (owners item (subset List.mem_cons_self))
        obtain ⟨pruned, released⟩ := integrated.pruneEmptyGroups
          (acc.1.maybeIntegrateWork item.work).2.newGroups
        exact pruned.startNewWork _ released
  unfold State.streamItems
  split
  · exact ⟨valid, by simp⟩
  · obtain ⟨next, outputs⟩ :=
      (loop items (fun _ h => h) (queue, [], [], []) valid).drainReadyGroups_support
    refine ⟨next, ?_⟩
    intro event member
    rcases List.mem_cons.mp member with same | later
    · subst event
      trivial
    · exact outputs event later

/-- Item integration preserves queue support independently of its output projection.
Witness: project the joint item-fold and drain theorem.
-/
theorem State.GroupRefSupport.streamItems {queue : State} {supported}
    (valid : queue.GroupRefSupport supported) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (owners
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ∀ group ∈ task.groups, supported group.ref)
    : (queue.streamItems stream items).1.GroupRefSupport supported :=
  (valid.streamItems_support stream items owners).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
