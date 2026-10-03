import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingCounts

/-! Exact stored-node witnesses for successful group publication. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Extract the selected nodes from the executable flush, without storing new queue state
-----------------------------------------------------------------------------------------

/-- Proof notation for the actual task iteration in `finishGroupSuccess`.
The accumulator holds the queue, emitted object values, and released stream refs. -/
def flushGroupTask (acc : State × List ExecutionGroupValue × NodeRefs)
    (occurrence : Occurrence)
    : State × List ExecutionGroupValue × NodeRefs :=
  match acc.1.taskNode? occurrence with
  | none => acc
  | some node =>
      let values :=
        match node.value with
        | none => acc.2.1
        | some value => acc.2.1 ++ [value]
      (acc.1.removeTask occurrence, values, acc.2.2 ++ node.childStreams)

/-- A task lookup identifies both an existing node and its exact occurrence.
Witness: membership and predicate satisfaction of the executable first-match lookup. -/
theorem State.taskNode?_some {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node)
    : node ∈ queue.taskNodes ∧ node.task.occurrence = occurrence :=
  ⟨
    List.mem_of_find?_eq_some found,
    (occurrence_beq_iff_eq _ _).mp
      (List.find?_some
        (p :=
          fun candidate : TaskNode =>
            candidate.task.occurrence == occurrence)
        found)
  ⟩

/-- Removing a task retains only old nodes with a different occurrence.
Witness: the executable task-node filter, independent of task-map uniqueness. -/
theorem State.removeTask_node {queue : State} {occurrence node}
    (member : node ∈ (queue.removeTask occurrence).taskNodes)
    : node ∈ queue.taskNodes ∧ node.task.occurrence ≠ occurrence := by
  obtain ⟨old, kept⟩ := List.mem_filter.mp member
  exact ⟨
    old,
    by
      intro same
      have reflexive := (occurrence_beq_iff_eq occurrence occurrence).mpr rfl
      simp [same, bne, reflexive] at kept
  ⟩

/-- Removing a different occurrence preserves the exact first-match task lookup.
Witness: the removal filter retains every candidate satisfying the lookup predicate.
No uniqueness assumption on the raw task-node map is needed.
-/
theorem State.removeTask_lookup_other (queue : State) {removed occurrence : Occurrence}
    (different : occurrence ≠ removed)
    : (queue.removeTask removed).taskNode? occurrence = queue.taskNode? occurrence := by
  simp only [State.removeTask, State.taskNode?, List.find?_filter]
  congr 1
  funext node
  by_cases same : node.task.occurrence = occurrence
  · have excluded : (node.task.occurrence == removed) = false := by
      cases equal : node.task.occurrence == removed with
      | false => rfl
      | true => exact False.elim (different (same ▸ (occurrence_beq_iff_eq _ _).mp equal))
    simp [bne, excluded]
  · have excluded : (node.task.occurrence == occurrence) = false := by
      cases equal : node.task.occurrence == occurrence with
      | false => rfl
      | true => exact False.elim (same ((occurrence_beq_iff_eq _ _).mp equal))
    simp [excluded]

/-- A flush selects every initially findable member exactly once, in lookup order.
Witness: induction through the executable fold. Each successful lookup is removed before
the next iteration, so duplicate memberships cannot produce duplicate selections.
Other removals preserve the first-match lookup, so no initially findable member is lost.
The selected nodes explain the exact value and child-stream accumulators.
-/
theorem flushGroupTask_completeWitness (queue : State) (tasks : List Occurrence)
    (values : List ExecutionGroupValue) (streams : NodeRefs)
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ (∀ node ∈ selected, node ∈ queue.taskNodes ∧ node.task.occurrence ∈ tasks)
        ∧ (tasks.foldl flushGroupTask (queue, values, streams)).2.1
          = values ++ selected.filterMap TaskNode.value
        ∧ (tasks.foldl flushGroupTask (queue, values, streams)).2.2
          = streams ++ selected.flatMap TaskNode.childStreams
        ∧ (tasks.foldl flushGroupTask (queue, values, streams)).1.taskNodes.Subset
            queue.taskNodes
        ∧ (∀ node ∈ selected,
            ∀ retained ∈
              (tasks.foldl flushGroupTask (queue, values, streams)).1.taskNodes,
              retained.task.occurrence ≠ node.task.occurrence)
        ∧ (∀ occurrence ∈ tasks,
            ∀ node, queue.taskNode? occurrence = some node → node ∈ selected)
        ∧ (selected.map (fun node => node.task.occurrence)).Sublist tasks := by
  induction tasks generalizing queue values streams with
  | nil =>
      exact ⟨
        [],
        by simp,
        by simp,
        by simp,
        by simp,
        List.Subset.refl _,
        by simp,
        by simp,
        .refl _
      ⟩
  | cons occurrence rest ih =>
      cases found : queue.taskNode? occurrence with
      | none =>
          obtain ⟨selected, unique, known, data, children, retained, absent, covered, ordered⟩ :=
            ih queue values streams
          refine ⟨selected, unique, ?_, ?_, ?_, ?_, ?_, ?_, ordered.cons _⟩
          · intro node member
            exact ⟨(known node member).1, List.mem_cons_of_mem _ (known node member).2⟩
          · simpa only [List.foldl_cons, flushGroupTask, found] using data
          · simpa only [List.foldl_cons, flushGroupTask, found] using children
          · simpa only [List.foldl_cons, flushGroupTask, found] using retained
          · simpa only [List.foldl_cons, flushGroupTask, found] using absent
          · intro other member node lookup
            rcases List.mem_cons.mp member with same | later
            · subst other
              rw [found] at lookup
              contradiction
            · exact covered other later node lookup
      | some node =>
          have nodeKnown := State.taskNode?_some found
          let nextValues := match node.value with
            | none => values
            | some value => values ++ [value]
          obtain ⟨selected, unique, known, data, children, retained, absent, covered, ordered⟩ :=
            ih (queue.removeTask occurrence) nextValues (streams ++ node.childStreams)
          have selectedKnown (other : TaskNode) (member : other ∈ selected)
              : other ∈ queue.taskNodes ∧ other.task.occurrence ≠ occurrence :=
            State.removeTask_node (known other member).1
          refine ⟨node :: selected, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · apply List.nodup_cons.mpr
            refine ⟨?_, unique⟩
            intro repeated
            obtain ⟨other, member, same⟩ := List.mem_map.mp repeated
            exact (selectedKnown other member).2 (same.trans nodeKnown.2)
          · intro other member
            rcases List.mem_cons.mp member with same | later
            · subst other
              exact ⟨nodeKnown.1, nodeKnown.2 ▸ List.mem_cons_self⟩
            · exact ⟨(selectedKnown other later).1,
                List.mem_cons_of_mem _ (known other later).2⟩
          · simp only [List.foldl_cons, flushGroupTask, found]
            change _ = values ++ (node :: selected).filterMap TaskNode.value
            rw [data]
            cases value : node.value <;> simp [nextValues, value, List.append_assoc]
          · simp only [List.foldl_cons, flushGroupTask, found]
            rw [children]
            simp [List.append_assoc]
          · intro other member
            have after
                : other
                  ∈ (rest.foldl flushGroupTask
                      (
                        queue.removeTask occurrence,
                        nextValues,
                        streams ++ node.childStreams
                      )).1.taskNodes := by
              simpa only [List.foldl_cons, flushGroupTask, found] using member
            exact (State.removeTask_node (retained after)).1
          · intro other member live liveMember
            simp only [List.foldl_cons, flushGroupTask, found] at liveMember
            rcases List.mem_cons.mp member with same | later
            · subst other
              rw [nodeKnown.2]
              exact (State.removeTask_node (retained liveMember)).2
            · exact absent other later live liveMember
          · intro other member selectedNode lookup
            by_cases same : other = occurrence
            · subst other
              have equal := Option.some.inj (lookup.symm.trans found)
              exact equal ▸ List.mem_cons_self
            · have later : other ∈ rest := (List.mem_cons.mp member).resolve_left same
              apply List.mem_cons_of_mem
              apply covered other later selectedNode
              rwa [queue.removeTask_lookup_other same]
          · simpa only [List.map_cons, nodeKnown.2] using ordered.cons_cons occurrence

/-- A flush's selected nodes explain its values, child streams, and residual task map.
Witness: project the complete selection theorem, retaining the established proof interface.
-/
theorem flushGroupTask_witness (queue : State) (tasks : List Occurrence)
    (values : List ExecutionGroupValue) (streams : NodeRefs)
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ (∀ node ∈ selected, node ∈ queue.taskNodes ∧ node.task.occurrence ∈ tasks)
        ∧ (tasks.foldl flushGroupTask (queue, values, streams)).2.1
          = values ++ selected.filterMap TaskNode.value
        ∧ (tasks.foldl flushGroupTask (queue, values, streams)).2.2
          = streams ++ selected.flatMap TaskNode.childStreams
        ∧ (tasks.foldl flushGroupTask (queue, values, streams)).1.taskNodes.Subset
            queue.taskNodes
        ∧ (∀ node ∈ selected,
            ∀ retained ∈
              (tasks.foldl flushGroupTask (queue, values, streams)).1.taskNodes,
              retained.task.occurrence ≠ node.task.occurrence) := by
  obtain ⟨selected, unique, known, values, streams, retained, absent, _⟩ :=
    flushGroupTask_completeWitness queue tasks values streams
  exact ⟨selected, unique, known, values, streams, retained, absent⟩

/-- A flush leaves every unlisted occurrence's exact task lookup unchanged.
Witness: each successful iteration removes only its own listed occurrence; failed lookups
leave the accumulator unchanged. This also covers duplicate raw task-map entries.
-/
theorem flushGroupTask_lookup_unselected (queue : State) (tasks : List Occurrence)
    (values : List ExecutionGroupValue) (streams : NodeRefs) {occurrence : Occurrence}
    (unselected : occurrence ∉ tasks)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.taskNode? occurrence
      = queue.taskNode? occurrence := by
  induction tasks generalizing queue values streams with
  | nil => rfl
  | cons head rest ih =>
      have different : occurrence ≠ head := fun same =>
        unselected (List.mem_cons.mpr (Or.inl same))
      have later : occurrence ∉ rest := fun member =>
        unselected (List.mem_cons_of_mem _ member)
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih _ _ _ later
      · rw [ih _ _ _ later, queue.removeTask_lookup_other different]

-----------------------------------------------------------------------------------------
-- Successful group cleanup publishes exactly its selected stored values
-----------------------------------------------------------------------------------------

/-- Pruning empty groups never changes the live task-node map.
Witness: recursion over the actual pruning loop, which modifies group nodes only. -/
theorem State.pruneEmptyGroups_taskNodes (queue : State)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.taskNodes = queue.taskNodes := by
  have loop (fuel : Nat) (queue : State) (groups kept : List Execution.DeliveryNode)
      : (State.pruneEmptyGroups.go fuel queue groups kept).1.taskNodes = queue.taskNodes := by
    induction fuel generalizing queue groups kept with
    | zero => rfl
    | succ fuel ih =>
        cases groups with
        | nil => rfl
        | cons group rest =>
            simp only [State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _
            · split <;> exact ih _ _ _
  exact loop _ _ _ _

/-- A flush's values and released streams share one complete, occurrence-unique selection.
Witness: the executable fold's two accumulators and task-map-preserving pruning. Each
released stream is looked up by a child ref belonging to one of these selected nodes.
Every initially findable group membership is selected, including repeated memberships.
Selected occurrences retain their order in the group's membership list.
-/
theorem State.finishGroupSuccess_completeSelection (queue : State) (group : GroupNode)
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ (∀ node ∈ selected, node ∈ queue.taskNodes ∧ node.task.occurrence ∈ group.tasks)
        ∧ (queue.finishGroupSuccess group).2.1
          = (if (selected.filterMap TaskNode.value).isEmpty then
                []
              else
                [.groupValues group.group.node (selected.filterMap TaskNode.value)])
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ (queue.finishGroupSuccess group).1.taskNodes.Subset queue.taskNodes
        ∧ (∀ node ∈ selected,
            ∀ retained ∈ (queue.finishGroupSuccess group).1.taskNodes,
              retained.task.occurrence ≠ node.task.occurrence)
        ∧ (∀ stream ∈ (queue.finishGroupSuccess group).2.2.newStreams,
            ∃ node ∈ selected, stream.ref ∈ node.childStreams)
        ∧ (∀ occurrence ∈ group.tasks,
            ∀ node, queue.taskNode? occurrence = some node → node ∈ selected)
        ∧ (selected.map (fun node => node.task.occurrence)).Sublist group.tasks := by
  obtain ⟨selected, unique, known, values, streams, retained, absent, covered, ordered⟩ :=
    flushGroupTask_completeWitness queue group.tasks [] []
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State :=
    { flushed.1 with
      groupNodes := flushed.1.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  have taskNodes : (queue.finishGroupSuccess group).1.taskNodes = flushed.1.taskNodes :=
    State.pruneEmptyGroups_taskNodes current _
  refine ⟨selected, unique, known, ?_, ?_, ?_, ?_, covered, ordered⟩
  · change (if flushed.2.1.isEmpty then []
        else [Execution.WorkQueueEvent.groupValues group.group.node flushed.2.1]) ++ _ = _
    have exactValues : flushed.2.1 = selected.filterMap TaskNode.value := values
    rw [exactValues]
    rfl
  · rw [taskNodes]
    exact retained
  · rw [taskNodes]
    exact absent
  · intro stream released
    have exactStreams : flushed.2.2 = selected.flatMap TaskNode.childStreams := streams
    change stream ∈ flushed.2.2.filterMap
      (fun ref => ((queue.finishGroupSuccess group).1.stream? ref).map Stream.node) at released
    rw [exactStreams] at released
    obtain ⟨ref, child, lookup⟩ := List.mem_filterMap.mp released
    obtain ⟨node, member, linked⟩ := List.mem_flatMap.mp child
    cases found : (queue.finishGroupSuccess group).1.stream? ref with
    | none => simp [found] at lookup
    | some registered =>
        have same : registered.node = stream := by simpa [found] using lookup
        have sameRef : stream.ref = ref := by
          rw [← same]
          exact beq_iff_eq.mp
            (List.find?_some (p := fun entry : Stream => entry.node.ref == ref) found)
        exact ⟨node, member, sameRef ▸ linked⟩

/-- A flush's values and released streams share one occurrence-unique node selection.
Witness: project the complete selection while preserving the established release interface.
-/
theorem State.finishGroupSuccess_selection (queue : State) (group : GroupNode)
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ (∀ node ∈ selected, node ∈ queue.taskNodes ∧ node.task.occurrence ∈ group.tasks)
        ∧ (queue.finishGroupSuccess group).2.1
          = (if (selected.filterMap TaskNode.value).isEmpty then
                []
              else
                [.groupValues group.group.node (selected.filterMap TaskNode.value)])
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ (queue.finishGroupSuccess group).1.taskNodes.Subset queue.taskNodes
        ∧ (∀ node ∈ selected,
            ∀ retained ∈ (queue.finishGroupSuccess group).1.taskNodes,
              retained.task.occurrence ≠ node.task.occurrence)
        ∧ (∀ stream ∈ (queue.finishGroupSuccess group).2.2.newStreams,
            ∃ node ∈ selected, stream.ref ∈ node.childStreams) := by
  obtain ⟨selected, unique, known, events, retained, absent, streams, _⟩ :=
    queue.finishGroupSuccess_completeSelection group
  exact ⟨selected, unique, known, events, retained, absent, streams⟩

/-- A completed group's raw value event has an exact, occurrence-unique stored-node witness.
Witness: project the common value/stream selection, retaining payloads, error counts,
and residual task-map inclusion. Selection does not imply any new host settlement. -/
theorem State.finishGroupSuccess_publications (queue : State) (group : GroupNode)
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ (∀ node ∈ selected, node ∈ queue.taskNodes ∧ node.task.occurrence ∈ group.tasks)
        ∧ (queue.finishGroupSuccess group).2.1
          = (if (selected.filterMap TaskNode.value).isEmpty then
                []
              else
                [.groupValues group.group.node (selected.filterMap TaskNode.value)])
            ++ [.groupSuccess group.group.node
                  (queue.finishGroupSuccess group).2.2.newGroups
                  (queue.finishGroupSuccess group).2.2.newStreams]
        ∧ (queue.finishGroupSuccess group).1.taskNodes.Subset queue.taskNodes
        ∧ (∀ node ∈ selected,
            ∀ retained ∈ (queue.finishGroupSuccess group).1.taskNodes,
              retained.task.occurrence ≠ node.task.occurrence) := by
  obtain ⟨selected, unique, known, events, retained, absent, _⟩ :=
    queue.finishGroupSuccess_selection group
  exact ⟨selected, unique, known, events, retained, absent⟩

/-- Every raw group value came from a selected stored task belonging to that group.
Witness: the exact publication witness and filter-map membership recover the unchanged
stored payload. The selected occurrence is absent from the residual live task map. -/
theorem State.finishGroupSuccess_value {queue : State} {group : GroupNode}
    {trigger values value}
    (emitted : .groupValues trigger values ∈ (queue.finishGroupSuccess group).2.1)
    (member : value ∈ values)
    : trigger = group.group.node
      ∧ ∃ node ∈ queue.taskNodes,
          node.task.occurrence ∈ group.tasks
          ∧ node.value = some value
          ∧ ∀ retained ∈ (queue.finishGroupSuccess group).1.taskNodes,
              retained.task.occurrence ≠ node.task.occurrence := by
  obtain ⟨selected, _, known, events, _, absent⟩ := queue.finishGroupSuccess_publications group
  rw [events] at emitted
  split at emitted
  · simp at emitted
  · simp only [List.mem_append, List.mem_singleton, Execution.WorkQueueEvent.groupValues.injEq,
      reduceCtorEq, or_false] at emitted
    obtain ⟨same, exactValues⟩ := emitted
    rw [exactValues] at member
    obtain ⟨node, selectedNode, stored⟩ := List.mem_filterMap.mp member
    exact ⟨same, node, (known node selectedNode).1, (known node selectedNode).2,
      stored, absent node selectedNode⟩

/-- Successful group cleanup leaves unlisted task lookups unchanged.
Witness: the exact flush lookup equation and task-map-preserving descendant pruning.
Shared tasks absent from this group's membership list are not silently removed.
-/
theorem State.finishGroupSuccess_lookup_unselected (queue : State) (group : GroupNode)
    {occurrence : Occurrence} (unselected : occurrence ∉ group.tasks)
    : (queue.finishGroupSuccess group).1.taskNode? occurrence
      = queue.taskNode? occurrence := by
  let flushed := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State :=
    { flushed.1 with
      groupNodes := flushed.1.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref) }
  have taskNodes : (queue.finishGroupSuccess group).1.taskNodes = flushed.1.taskNodes :=
    State.pruneEmptyGroups_taskNodes current _
  change (queue.finishGroupSuccess group).1.taskNodes.find? _ = _
  rw [taskNodes]
  exact flushGroupTask_lookup_unselected queue group.tasks [] [] unselected

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
