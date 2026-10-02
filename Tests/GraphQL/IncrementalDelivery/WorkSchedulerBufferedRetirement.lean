import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAncestorCoverage

/-! A silently pruned shared owner retires only after its buffered value is published. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerBufferedRetirement
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := { key := 0, path := [] }
private def child : DeliveryNode := { key := 1, path := [] }
private def occurrence : Occurrence := .executionGroup []
private def task : Task := ⟨occurrence, [parent, child]⟩

private def value : ExecutionGroupValue :=
  {
    path := [],
    data := [("x", .scalar "X")],
    errors := 0,
    deliveryGroups := [parent, child]
  }

private def buffered : TaskNode := ⟨task, some value, []⟩

private def parentNode : GroupNode :=
  { group := ⟨parent, none⟩, childGroups := [child.key], tasks := [occurrence] }

private def childNode : GroupNode :=
  { group := ⟨child, some parent.key⟩, tasks := [occurrence] }

private def queue : State :=
  {
    rootGroups := [parent.key],
    registeredGroups := [parent.key, child.key],
    groupNodes := [parentNode, childNode],
    taskNodes := [buffered],
    tasks := [task]
  }

private theorem inventory : queue.PublicationInventory (fun _ _ => True) [] := by
  refine ⟨by simp, by simp, ?_⟩
  intro node member stored found
  exact ⟨trivial, by simp⟩

private theorem links : queue.StoredTaskLinks := by
  intro node member stored owner live contributes
  have same : node = buffered := List.mem_singleton.mp member
  subst node
  rcases List.mem_cons.mp live with same | last
  · subst owner
    exact List.mem_cons_self
  · have same := List.mem_singleton.mp last
    subst owner
    exact List.mem_cons_self

/-- The child's empty record disappears without a completion notice of its own.
Witness: reduction of the actual mixed drain, which flushes the shared value under P,
removes its membership from C, and silently prunes C's now-empty shell.
This is a local queue-state regression, not an assertion of generated-work conformance.
-/
theorem silent_retirement_output
    : queue.drainReadyGroups.2 = [.groupValues parent [value], .groupSuccess parent [] []]
      ∧ child.key ∉ queue.drainReadyGroups.1.cancelledGroups
      ∧ child.key
        ∉ queue.drainReadyGroups.1.groupNodes.map (fun node => node.group.node.key)
      ∧ queue.drainReadyGroups.1.taskNode? occurrence = none := by
  constructor
  · cbv
  · constructor
    · cbv; intro impossible; cases impossible
    · constructor
      · cbv; intro impossible; cases impossible
      · cbv

/-- The generic mixed-drain ledger accounts for data before silent owner retirement.
Witness: uncancelled owner conservation on the same exact publication list. The retained
alternative contradicts C's disappearance, so the pair must be in that ledger. No C
completion event, payload-based identity, or supplied publication premise is used.
-/
theorem silent_retirement_publishes
    : ∃ published : List ObjectPublication,
        published.map Prod.snd = [value]
        ∧ queue.StoredOwnersConserved published queue.drainReadyGroups.1
        ∧ (occurrence, value) ∈ published := by
  obtain ⟨published, values, _, _, _, _, _, owners⟩ :=
    inventory.drainReadyGroups_go_bufferedCoverage links queue.groupNodes.length
  have emitted := owners occurrence buffered value (by cbv) rfl child.key
    (by simp [buffered, task]) (by simp [queue, parentNode, childNode])
    silent_retirement_output.2.1
  refine ⟨published, ?_, owners, ?_⟩
  · change published.map Prod.snd = queue.drainReadyGroups.2.flatMap
      WorkQueueEvent.objectValues at values
    simpa only [silent_retirement_output.1, List.flatMap_cons, List.flatMap_nil,
      WorkQueueEvent.objectValues, List.append_nil] using values
  · exact emitted.resolve_right (fun retained => silent_retirement_output.2.2.1 retained.2)

/-- Failed retirement may discard buffered data, but records cancellation of the owner.
Witness: direct reduction of the same state through failed-group removal; the generic
conservation certificate deliberately exempts C only because its key is now cancelled.
-/
theorem failed_retirement_records_cancellation
    : child.key ∈ (queue.removeGroup parent.key).cancelledGroups
      ∧ (queue.removeGroup parent.key).taskNode? occurrence = none
      ∧ queue.StoredOwnersConserved [] (queue.removeGroup parent.key) := by
  exact ⟨
    by cbv; exact .head _,
    by cbv,
    queue.removeGroup_storedOwnersConserved parent.key
  ⟩

-----------------------------------------------------------------------------------------
-- A child activates and flushes after its buffered parent in the same drain
-----------------------------------------------------------------------------------------

namespace Nested

private def childTask : Task := ⟨.executionGroup [0], [child]⟩

private def parentValue : ExecutionGroupValue :=
  { path := [], data := [("obj", .object [])], errors := 0, deliveryGroups := [parent] }

private def childValue : ExecutionGroupValue :=
  {
    path := [.field "obj"],
    data := [("x", .scalar "X")],
    errors := 0,
    deliveryGroups := [child]
  }

private def parentTask : Task := ⟨occurrence, [parent]⟩
private def parentBuffered : TaskNode := ⟨parentTask, some parentValue, []⟩
private def childBuffered : TaskNode := ⟨childTask, some childValue, []⟩

private def waiting : State :=
  {
    rootGroups := [parent.key],
    registeredGroups := [parent.key, child.key],
    groupNodes := [parentNode, { childNode with tasks := [childTask.occurrence] }],
    taskNodes := [parentBuffered, childBuffered],
    tasks := [parentTask, childTask]
  }

/-- One drain activates C after publishing P, then emits C's already buffered value.
Witness: reduce both actual closure blocks. C is not an initial root of this drain.
This fixture checks the internal queue boundary, not generated-work conformance.
-/
theorem same_drain_output
    : waiting.drainReadyGroups.2
        = [
          .groupValues parent [parentValue],
          .groupSuccess parent [child] [],
          .groupValues child [childValue],
          .groupSuccess child [] []
        ]
      ∧ child.key ∉ waiting.rootGroups := by
  constructor
  · cbv
  · cbv; intro impossible; cases impossible; contradiction

/-- The common drain ledger puts P's value strictly before C's value event.
Witness: prefix owner conservation after one internal closure excludes retention of the
retired P record. This uses the prefix of the full ledger, not a separately chosen trace.
-/
theorem same_drain_parent_published_first
    : ∃ published : List ObjectPublication,
        published.map Prod.snd = [parentValue, childValue]
        ∧ (parentTask.occurrence, parentValue) ∈ published.take 1 := by
  have inventory : waiting.PublicationInventory (fun _ _ => True) [] := by
    refine ⟨by simp, by simp, ?_⟩
    intro node member stored found
    exact ⟨trivial, by simp⟩
  have links : waiting.StoredTaskLinks := by
    intro node member stored owner live contributes
    rcases List.mem_cons.mp member with same | tail
    · subst node
      have key : owner.group.node.key = parent.key := by
        simpa [parentBuffered, parentTask] using contributes
      rcases List.mem_cons.mp live with same | tail
      · subst owner; exact List.mem_cons_self
      · have same := List.mem_singleton.mp tail
        subst owner
        cases key
    · have same := List.mem_singleton.mp tail
      subst node
      have key : owner.group.node.key = child.key := by
        simpa [childBuffered, childTask] using contributes
      rcases List.mem_cons.mp live with same | tail
      · subst owner; cases key
      · have same := List.mem_singleton.mp tail
        subst owner; exact List.mem_cons_self
  obtain ⟨published, values, _, _, _, _, _, prefixes, _⟩ :=
    inventory.drainReadyGroups_go_prefixCoverage links waiting.groupNodes.length
  have conserved := prefixes 1 (by decide)
  have emitted := conserved parentTask.occurrence parentBuffered parentValue (by cbv) rfl
    parent.key (by simp [parentBuffered, parentTask]) (by simp [waiting, parentNode])
    (by cbv; intro impossible; cases impossible)
  refine ⟨published, ?_, ?_⟩
  · change published.map Prod.snd = waiting.drainReadyGroups.2.flatMap
      WorkQueueEvent.objectValues at values
    simpa only [same_drain_output.1, List.flatMap_cons, List.flatMap_nil,
      WorkQueueEvent.objectValues, List.append_nil, List.nil_append, List.cons_append]
      using values
  · rcases emitted with emitted | retained
    · exact emitted
    · have gone : parent.key ∉ (State.drainReadyGroups.go 1 waiting).1.groupNodes.map
          (fun owner => owner.group.node.key) := by
        cbv; intro impossible; cases impossible; contradiction
      exact False.elim (gone retained.2)

end Nested

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerBufferedRetirement
