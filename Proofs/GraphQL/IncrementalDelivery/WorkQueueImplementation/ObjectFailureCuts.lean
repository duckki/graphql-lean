import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AvailableObjectFailureCuts

/-! Exact group reporting over notification and cached-rejection availability cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Reporting availability retains an actual rejection in the complete source history.
Its callback need not have been consumed at the report's output cut. -/
theorem createWorkQueue_availableObjectFailureCuts_source {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) {entry : Nat × Occurrence}
    (member
      : entry
        ∈ availableObjectFailureCuts work 0
            ((State.initialize (Work.fromExecution work)).sourceRunBlocks
              {
                active :=
                  (State.initialize (Work.fromExecution work)).initialGroups
                  ++ (State.initialize (Work.fromExecution work)).initialStreams
              } batches).2.2)
    : ∃ errors, GraphEvent.taskFailure entry.2 errors ∈ batches.flatten := by
  rcases availableObjectFailureCuts_origin member with source | report
  · obtain ⟨errors, received⟩ := sourceObjectFailureCuts_source source
    exact ⟨errors, (State.sourceRunBlocks_inputs _ _ _).subset received⟩
  · obtain ⟨index, group, errors, count, selected, _, cause⟩ :=
      groupReportCandidateCuts_origin report
    have sources := createWorkQueue_sourceRunBlocks_groupFailureTotals generated valid
      group errors (List.mem_of_getElem? selected)
    simp only [List.nil_append] at sources
    have received := ((groupReportSourceParts_spec sources).2.2.2 entry.2 count cause).1
    exact ⟨count, (State.sourceRunBlocks_inputs _ _ _).subset received⟩

/-- Actual object availability refers to fixed failed reachable tasks within the output.
Both callback cuts and aggregate-report cuts retain genuine source rejection evidence. -/
theorem createWorkQueue_availableObjectFailureCuts_origin {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∀ entry ∈ availableObjectFailureCuts work 0 blocks,
        entry.1
          ≤ ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).length
        ∧ ∃ owners producer path errors,
            TaskAt work entry.2 owners producer (.object path (.error errors))
            ∧ Reachable work entry.2 := by
  dsimp only
  intro entry member
  have bound := (availableObjectFailureCuts_bounds member).2
  refine ⟨?_, ?_⟩
  · simpa only [Nat.zero_add, (State.sourceRunBlocks_agrees _ _).2] using bound
  · rcases availableObjectFailureCuts_origin member with source | report
    · exact (createWorkQueue_sourceObjectFailureCuts_origin generated valid entry source).2
    · obtain ⟨index, group, errors, count, selected, _, cause⟩ :=
        groupReportCandidateCuts_origin report
      have totals := createWorkQueue_sourceRunBlocks_groupFailureTotals generated valid
      have sources := totals group errors (List.mem_of_getElem? selected)
      simp only [List.nil_append] at sources
      obtain ⟨received, owners, producer, path, known, _⟩ :=
        (groupReportSourceParts_spec sources).2.2.2 entry.2 count cause
      exact ⟨owners, producer, path, count, known,
        valid.taskFailure_reachable generated ((State.sourceRunBlocks_inputs _ _ _).subset received)⟩

-----------------------------------------------------------------------------------------
-- Every emitted cause has reporting availability by its actual output position
-----------------------------------------------------------------------------------------

/-- Each group failure sees its matching contributor’s source-task candidate cut.
Witness: choose the selected cause inventory, which may precede the current input.
The selected task has the completion's exact cause count.
-/
theorem availableObjectFailureCuts_covers {work : Execution.Work}
    {blocks : List SourceOutputBlock}
    (totals : SourceBlocksHaveFailureTotals work [] blocks) (offset : Nat) {index : Nat}
    {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent : (blocks.flatMap Prod.snd)[index]? = some (.groupFailure group errors))
    : ∃ cut occurrence count owners producer path,
        (cut, occurrence) ∈ availableObjectFailureCuts work offset blocks
        ∧ cut ≤ offset + index
        ∧ TaskAt work occurrence owners producer (.object path (.error count))
        ∧ group.ref ∈ owners := by
  obtain ⟨parts, nonempty, _, _, contributions⟩ :=
    availableObjectFailureCuts_contributions totals offset atEvent
  obtain ⟨⟨occurrence, count⟩, member⟩ := List.exists_mem_of_ne_nil parts nonempty
  obtain ⟨visible, owners, producer, path, known, owner⟩ :=
    contributions occurrence count member
  obtain ⟨⟨cut, task⟩, selected, same⟩ := List.mem_map.mp visible
  dsimp only at same
  subst task
  obtain ⟨recorded, reached⟩ := List.mem_filter.mp selected
  exact ⟨cut, occurrence, count, owners, producer, path, recorded,
    of_decide_eq_true reached, known, owner⟩

/-- Every actual group total has a distinct exact inventory inside its visible object cuts.
Witness: generated replay supplies aggregate provenance; runner agreement retains the index.
General contributor completeness and failure-cut licensing are not assumed or established.
-/
theorem createWorkQueue_availableObjectFailureCuts_contributions {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∃ parts : List (Occurrence × Nat),
        parts ≠ []
        ∧ (parts.map Prod.fst).Nodup
        ∧ (parts.map Prod.snd).sum = errors
        ∧ ∀ occurrence count,
            (occurrence, count) ∈ parts
            → occurrence ∈ failedBefore (availableObjectFailureCuts work 0 blocks) index
              ∧ ∃ owners producer path,
                  TaskAt work occurrence owners producer (.object path (.error count))
                  ∧ group.ref ∈ owners := by
  dsimp only
  simpa only [Nat.zero_add]
    using availableObjectFailureCuts_contributions
      (createWorkQueue_sourceRunBlocks_groupFailureTotals generated valid) 0
      (index := index) (group := group) (errors := errors)
      (by rw [(State.sourceRunBlocks_agrees _ _).2]; exact atEvent)

/-- Each actual group report has distinct positive causes among its visible object cuts.
Witness: the exact aggregate inventory retains each contributing source count; execution
supplies positivity. Causal licensing of visible candidates remains separate.
-/
theorem createWorkQueue_availableObjectFailureCuts_nodeFailureCauses
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      NodeFailureCauses work
        (failedBefore (availableObjectFailureCuts work 0 blocks) index) group.ref
        errors := by
  obtain ⟨parts, nonempty, distinct, total, known⟩ :=
    createWorkQueue_availableObjectFailureCuts_contributions generated valid atEvent
  refine ⟨parts, nonempty, distinct, ?_, total.symm⟩
  intro occurrence count member
  obtain ⟨visible, owners, producer, path, failed, owner⟩ := known occurrence count member
  exact ⟨visible, owners, producer, _, failed, owner, rfl,
    generated.taskFailure_positive failed rfl⟩

/-- Each actual group-failure atom is covered by an earlier contributing source cut.
Witness: exact runner agreement and the nonempty prefix total retain the original index.
A delayed closure can reuse earlier task cuts, and one task can justify several closures.
-/
theorem createWorkQueue_availableObjectFailureCuts_covers {work : Execution.Work}
    (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∃ cut occurrence count owners producer path,
        (cut, occurrence) ∈ availableObjectFailureCuts work 0 blocks
        ∧ cut ≤ index
        ∧ TaskAt work occurrence owners producer (.object path (.error count))
        ∧ group.ref ∈ owners := by
  dsimp only
  simpa only [Nat.zero_add]
    using availableObjectFailureCuts_covers
      (createWorkQueue_sourceRunBlocks_groupFailureTotals generated valid) 0
      (index := index) (group := group) (errors := errors)
      (by rw [(State.sourceRunBlocks_agrees _ _).2]; exact atEvent)

/-- Actual failed group closures have a historical failure under the candidate object cuts.
Witness: some contributing source cut is visible before closure; several closures can
reuse it. No matching-specific or admitted-history premise is used. Licensing all candidate
cuts, including cancellation safety and open owners, remains a separate obligation.
-/
theorem createWorkQueue_availableObjectFailureCuts_nodeFailed {work : Execution.Work}
    (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (matching : PublicationMatching) {index : Nat} {group : Execution.DeliveryNode}
    {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      NodeFailed work matching
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        (availableObjectFailureCuts work 0 blocks) group.ref := by
  obtain ⟨cut, occurrence, count, owners, producer, path, member, visible, known, owner⟩ :=
    createWorkQueue_availableObjectFailureCuts_covers generated valid atEvent
  apply NodeFailed.task known owner
  have length :
      ((((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten.flatMap
          publicationAtoms).take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1)
  rw [length]
  exact mem_failedBefore member visible

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
