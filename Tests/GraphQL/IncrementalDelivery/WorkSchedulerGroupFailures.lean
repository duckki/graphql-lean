import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A shared failed task closes two groups but contributes only one failure occurrence. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupFailures
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def selections : List Selection :=
  [defer [field "required"], defer [field "required"]]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def left : DeliveryNode := { key := 0, path := [] }
private def right : DeliveryNode := { key := 1, path := [] }
private def failed : Occurrence := .executionGroup [1, 0]
private def inputs : List (List GraphEvent) := [[.taskFailure failed 1]]

private def atoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
    publicationAtoms

private def initial : Keys :=
  ((State.initialize (Work.fromExecution work)).initialGroups
    ++ (State.initialize (Work.fromExecution work)).initialStreams).map
    DeliveryNode.key

private def cuts : FailureCuts := [(0, failed)]

private def candidateCuts : FailureCuts :=
  let queue := State.initialize (Work.fromExecution work)
  sourceObjectFailureCuts 0
    (queue.sourceRunBlocks { active := queue.initialGroups ++ queue.initialStreams }
      inputs).2.2

/-- Overlapping defer selections generate one failed task with two distinct contributors.
Witness: actual root execution and its shared partition's structural location.
-/
private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- Both contributors belong to the one fixed failed object task.
Witness: the execution-group projection of the generated shared partition.
-/
private theorem task_known
    : TaskAt work failed [left.key, right.key] none (.object [] (.error 1)) :=
  TaskAt.executionGroup (groups := [⟨left, []⟩, ⟨right, []⟩])
    (children := .empty) (owners := []) (by cbv)

/-- The one source failure is valid and its task has actually started.
Witness: matching fixed failure, fresh root settlement, and direct start-check evaluation.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  refine ⟨
    .append .nil ⟨_, _, _, task_known⟩ ?_
      ⟨_, _, _, task_known, by intro source impossible; cases impossible⟩,
    by cbv
  ⟩
  simp [GraphEvent.Fresh, GraphEvent.identities]

/-- One shared failure emits two one-error group closures, followed by termination.
Witness: evaluate the actual normalized runner; no synthetic output trace is substituted.
-/
theorem output
    : atoms = [.groupFailure left 1, .groupFailure right 1, .workQueueTermination] := by
  cbv

/-- A shared failed settlement has one handler boundary despite its two group closures.
Witness: exact source-block evaluation; the terminal marker has no task label.
-/
theorem shared_failure_one_block
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      (queue.sourceRunBlocks publisher inputs).2.2
      = [
        (some (.taskFailure failed 1), [.groupFailure left 1, .groupFailure right 1]),
        (none, [.workQueueTermination])
      ] := by cbv

/-- The source-boundary construction records the shared failed task once, before both notices.
Witness: evaluate the constructed cuts over the actual annotated runner.
-/
theorem shared_candidate_cuts : candidateCuts = [(0, failed)] := by cbv

/-- Both actual failed closures have a causal failure under that same constructed cut list.
Witness: the general source-block coverage theorem at each selected atomic output index.
-/
theorem shared_candidate_nodeFailed (matching : PublicationMatching) {index : Nat}
    {group : DeliveryNode} (selected : atoms[index]? = some (.groupFailure group 1))
    : NodeFailed work matching (atoms.take index) candidateCuts group.key :=
  createWorkQueue_sourceObjectFailureCuts_nodeFailed generated source_valid.1 matching
    selected

/-- Constructed cut uniqueness follows from source freshness, not a manually checked list.
Witness: apply the generic source-subsequence theorem to the shared generated execution.
-/
theorem shared_candidate_unique : (candidateCuts.map Prod.snd).Nodup :=
  createWorkQueue_sourceObjectFailureCuts_unique source_valid.1

/-- Even the second shared closure sees only this task, regardless of later source blocks.
Witness: the general visibility equation inside a two-atom handler. In particular, later
silent failures cannot change the earlier closure's visible failure inventory.
-/
theorem shared_candidate_visibility (later : List SourceOutputBlock)
    : failedBefore
        (sourceObjectFailureCuts 0
          ((some (.taskFailure failed 1), [.groupFailure left 1, .groupFailure right 1])
            :: later)) 1
      = [failed] := by
  simpa [sourceObjectFailureCuts, GraphEvent.objectFailure?]
    using sourceObjectFailureCuts_visible 0 [] later
      (some (.taskFailure failed 1), [.groupFailure left 1, .groupFailure right 1]) 1
      (by decide)

/-- Each actual group closure traces back to the same reachable, unpublished source task.
Witness: apply the general replay provenance theorem to both output positions. The sole
received failure fixes the task identity, independently of the supplied publication matching.
-/
theorem shared_failure_source (matching : PublicationMatching)
    : ∀ group ∈ [left, right],
        GroupFailureOrigin work inputs.flatten group 1
        ∧ Reachable work failed
        ∧ ¬Published matching atoms failed := by
  have exactValues : ∀ index event, atoms[index]? = some event → IsValue event
      → PublicationAt work (matching index) event := by
    intro index event atEvent value
    have member := List.mem_of_getElem? atEvent
    rw [output] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> cases value
  intro group member
  have selected : ∃ index : Nat, atoms[index]? = some (.groupFailure group 1) := by
    rcases List.mem_cons.mp member with same | last
    · subst group
      exact ⟨0, by rw [output]; rfl⟩
    · have same := List.mem_singleton.mp last
      subst group
      exact ⟨1, by rw [output]; rfl⟩
  obtain ⟨index, atEvent⟩ := selected
  obtain ⟨parts, nonempty, _, _, sources⟩ :=
    createWorkQueue_runNormalized_groupFailure_accounting generated source_valid.1
      matching exactValues atEvent
  obtain ⟨⟨occurrence, count⟩, member⟩ := List.exists_mem_of_ne_nil parts nonempty
  obtain ⟨received, _, reachable, unpublished⟩ :=
    sources occurrence count member
  have same : occurrence = failed ∧ count = 1 := by simpa [inputs] using received
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨createWorkQueue_runNormalized_atomicGroupFailure_source generated source_valid.1
    (List.mem_of_getElem? atEvent), reachable, unpublished⟩

/-- A single cut licenses the shared task's failure for both later group completions.
Witness: record the initially open root task once and extend over the actual output.
-/
theorem shared_failure_licensed (matching : PublicationMatching)
    : FailureWitness work initial matching atoms cuts := by
  have empty : FailureWitness work initial matching [] [] := by
    intro before cut occurrence after impossible
    have sizes := congrArg List.length impossible
    simp at sizes
  have opened : Open initial [] left.key := by
    cbv
    exact ⟨.head _, fun impossible => nomatch impossible⟩
  have recorded := empty.record task_known rfl (.root ⟨_, _, task_known⟩)
    ⟨left.key, List.mem_cons_self, opened⟩ (fun cancelled => cancelled.nonempty rfl)
  simpa [cuts] using recorded.append atoms

/-- The actual constructed candidate is fully licensed in the shared root-failure fixture.
Witness: its checked equality to the single cut recorded before either group closes.
-/
theorem shared_candidate_licensed (matching : PublicationMatching)
    : FailureWitness work initial matching atoms candidateCuts := by
  rw [shared_candidate_cuts]
  exact shared_failure_licensed matching

/-- Every contributing group counts the one failed task once, despite two emitted closures.
Witness: the singleton failure inventory and exact shared owner list, not closure counting.
-/
theorem shared_error_counts
    : ∀ group ∈ [left, right], NodeErrors work (failedBefore cuts 2) group.key 1 := by
  intro group member
  have owner : group.key ∈ [left.key, right.key] := List.mem_map_of_mem member
  refine ⟨fun _ => 1, ?_, rfl⟩
  intro occurrence entry
  have same : occurrence = failed := by simpa [failedBefore, cuts] using entry
  subst occurrence
  exact ⟨_, _, _, task_known, by simp [owner, Payload.failure]⟩

-----------------------------------------------------------------------------------------
-- A later two-error group does not accumulate an earlier group or stream's errors
-----------------------------------------------------------------------------------------

namespace MixedCounts

private def selections : List Selection :=
  [
    field "strict" [] [.stream],
    defer [field "required" [] [] (some "left")],
    defer [field "fail", field "required" [] [] (some "right")]
  ]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def left : DeliveryNode := { key := 0, path := [] }
private def right : DeliveryNode := { key := 1, path := [] }
private def stream : DeliveryNode := { key := 2, path := [.field "strict"] }
private def leftTask : Occurrence := .executionGroup [1, 0]
private def rightTask : Occurrence := .executionGroup [1, 1, 0]
private def failedItem : Occurrence := .item [0, 0, 1] 1

private def first : GraphEvent :=
  .streamItems stream [⟨.item [0, 0, 1] 0, ⟨.scalar "x", 0⟩, {}⟩]

private def priorInputs : List (List GraphEvent) :=
  [[first], [.taskFailure leftTask 1, .streamFailure stream 1]]

private def inputs : List (List GraphEvent) := priorInputs ++ [[.taskFailure rightTask 2]]

private def atoms : List Execution.WorkQueueEvent :=
  ((State.initialize (Work.fromExecution work)).runNormalized inputs).2.flatten.flatMap
    publicationAtoms

private def cuts : FailureCuts := [(1, leftTask), (2, failedItem), (3, rightTask)]

/-- Execution produces one streamed failure and two distinct failed deferred partitions.
Witness: actual root execution; the last task retains a nullable error before bubbling.
-/
private theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The first group's one-error task is structurally located independently of the last group.
Witness: project its exact generated execution-group address.
-/
private theorem left_known
    : TaskAt work leftTask [left.key] none (.object [] (.error 1)) :=
  TaskAt.executionGroup (groups := [⟨left, []⟩]) (children := .empty)
    (owners := []) (by cbv)

/-- The last group retains two errors from its own fixed pure execution result.
Witness: locate its nullable-error-plus-non-null-failure partition in the generated work.
-/
private theorem right_known
    : TaskAt work rightTask [right.key] none (.object [] (.error 2)) :=
  TaskAt.executionGroup (groups := [⟨right, []⟩]) (children := .empty)
    (owners := []) (by cbv)

/-- The streamed list has one successful item followed by its one-error non-null failure.
Witness: its exact generated stream location and finite outcome list.
-/
private theorem stream_located
    : Located work [0, 0, 1]
        (.stream stream [(.ok (.scalar "x", 0), .empty), (.error 1, .empty)]) none
        [] := by cbv

/-- The earlier mixed source prefix is valid and every supplied event was started.
Witness: fixed outcomes, independent root tasks, and the stream's contiguous item cursor.
-/
theorem prior_source_valid
    : ValidGraphEvents work priorInputs.flatten
      ∧ inputsStarted work priorInputs = true := by
  have firstMatch : first.MatchesWork work := by
    intro item member
    have same := List.mem_singleton.mp member
    subst item
    exact ⟨[stream.key], none, TaskAt.item stream_located rfl, by cbv⟩
  have firstValid : ValidGraphEvents work [first] :=
    .append .nil firstMatch (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, stream_located, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  have two : ValidGraphEvents work [first, .taskFailure leftTask 1] :=
    .append firstValid ⟨_, _, _, left_known⟩
      (by simp [first, leftTask, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, left_known, by intro source impossible; cases impossible⟩
  refine ⟨.append two ?_ ?_ ?_, by cbv⟩
  · exact ⟨_, _, _, _, stream_located, .empty, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · simp [first, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, stream_located,
      (by intro source impossible; cases impossible), .empty, rfl⟩

/-- The final failure extends the same valid, actually started source trace.
Witness: its distinct task identity, exact two-error outcome, and root readiness.
-/
theorem full_source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  refine ⟨?_, by cbv⟩
  change ValidGraphEvents work (priorInputs.flatten ++ [.taskFailure rightTask 2])
  refine .append prior_source_valid.1 ⟨_, _, _, right_known⟩ ?_ ?_
  · simp [priorInputs, first, GraphEvent.Fresh, GraphEvent.identities, leftTask, rightTask]
  · exact ⟨_, _, _, right_known, by intro source impossible; cases impossible⟩

/-- The actual output distinguishes the two earlier one-error failures from the last two.
Witness: evaluate the normalized mixed replay, including its terminal event.
-/
theorem mixed_output
    : atoms
      = [
        .streamValues stream [⟨.scalar "x", 0⟩] [] [],
        .groupFailure left 1,
        .streamFailure stream 1,
        .groupFailure right 2,
        .workQueueTermination
      ] := by cbv

/-- Constructed object cuts keep absolute positions across an intervening stream failure.
Witness: evaluate source-handler boundaries in the real mixed input batching. The stream
cut is supplied separately, but its output still advances the later object's cut index.
-/
theorem mixed_object_candidate_cuts
    : let queue := State.initialize (Work.fromExecution work)
      sourceObjectFailureCuts 0
        (queue.sourceRunBlocks { active := queue.initialGroups ++ queue.initialStreams }
          inputs).2.2
      = [(1, leftTask), (3, rightTask)] := by cbv

/-- Only the right-hand task contributes to the last group's two-error total.
Witness: the three actual task descriptors give zero contribution for the earlier group
and stream failures, and two for the last task.
-/
theorem mixed_group_error_count : NodeErrors work (failedBefore cuts 3) right.key 2 := by
  refine ⟨fun occurrence => if occurrence = rightTask then 2 else 0, ?_, ?_⟩
  · intro occurrence member
    change occurrence ∈ [leftTask, failedItem, rightTask] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨_, _, _, left_known, by simp [leftTask, rightTask, left, right]⟩
    · exact ⟨_, _, _, TaskAt.item stream_located (by rfl),
        by simp [failedItem, rightTask, stream, right]⟩
    · exact ⟨_, _, _, right_known, by simp [Payload.failure]⟩
  · simp [failedBefore, cuts, leftTask, failedItem, rightTask]

end MixedCounts

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerGroupFailures
