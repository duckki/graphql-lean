import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFlushCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureSettlements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Stored nullable-error data waits for a later shared-owner task before publication. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerPublication
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := { key := 0, path := [], label := some (.string "P") }
private def other : DeliveryNode := { key := 1, path := [], label := some (.string "Q") }
private def firstTask : Occurrence := .executionGroup [1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 0]

private def firstValue : ExecutionGroupValue :=
  { deliveryGroups := [parent], path := [], data := [("fail", .null)], errors := 1 }

private def sharedValue : ExecutionGroupValue :=
  { deliveryGroups := [parent, other], path := [], data := [("b", .scalar "b")] }

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨parent, []⟩] [] (.ok (firstValue.data, 1))
        (.combine .empty .empty))
      (.combine
        (.executionGroup [⟨parent, []⟩, ⟨other, []⟩] [] (.ok (sharedValue.data, 0))
          (.combine .empty .empty))
        .empty))

private def firstResult : TaskResult := { value := firstValue }
private def sharedResult : TaskResult := { value := sharedValue }
private def first : GraphEvent := .taskSuccess firstTask firstResult
private def shared : GraphEvent := .taskSuccess sharedTask sharedResult
private def initial : State := State.initialize (Work.fromExecution work)
private def waiting : State := initial.replayGraphEvents [first]

/-- The shared-owner fixture is execution-generated, including its nullable error count.
Witness: execute overlapping defers P { fail b } and Q { b } with the ordinary test resolvers.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "fail", field "b"] (some "P"), defer [field "b"] (some "Q")], ?_⟩
  cbv

/-- The first task has a successful null-data result carrying one nullable-field error.
Witness: its exact generated execution-group descriptor. -/
private theorem firstKnown
    : TaskAt work firstTask [parent.key] none
        (.object [] (.ok (firstValue.data, 1))) := by
  refine ⟨[⟨parent, []⟩], [], _, .combine .empty .empty, [], ?_, rfl, rfl⟩
  cbv

/-- The second task belongs to both pending defer groups and returns b unchanged.
Witness: its exact generated descriptor, not a single-owner approximation. -/
private theorem sharedKnown
    : TaskAt work sharedTask [parent.key, other.key] none
        (.object [] (.ok (sharedValue.data, 0))) := by
  refine ⟨[⟨parent, []⟩, ⟨other, []⟩], [], _, .combine .empty .empty, [], ?_, rfl, rfl⟩
  cbv

/-- The first input carries the fixed nullable-error result and its empty child boundary.
Witness: exact task, contributor, and child-work matching. -/
private theorem firstMatches : first.MatchesWork work :=
  ⟨_, _, firstKnown, by cbv, by cbv⟩

/-- The shared input retains both contributor descriptors.
Witness: exact source matching for the second task. -/
private theorem sharedMatches : shared.MatchesWork work :=
  ⟨_, _, sharedKnown, by cbv, by cbv⟩

/-- The waiting prefix is legal even though it has emitted no value or completion.
Witness: one fresh root-produced task settlement with exact fixed outcomes. -/
theorem waiting_valid : ValidGraphEvents work [first] :=
  .append .nil firstMatches
    (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, firstKnown, by intro source impossible; cases impossible⟩

/-- The later shared settlement is also legal and was actually started by the queue.
Witness: source freshness, producer readiness, and the executable start check. -/
theorem inputs_valid_started
    : ValidGraphEvents work [first, shared]
      ∧ inputsStarted work [[first], [shared]] = true := by
  refine ⟨.append waiting_valid sharedMatches ?_ ?_, by cbv⟩
  · simp [first, shared, firstTask, sharedTask, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, sharedKnown, by intro source impossible; cases impossible⟩

/-- Settling the first task stores its value without publishing or closing P.
Witness: execute the actual handler while its other shared contributor is still pending.
-/
theorem settlement_waits
    : (initial.taskSuccess firstTask firstResult).2 = []
      ∧ (waiting.taskNode? firstTask).bind TaskNode.value = some firstValue := by
  constructor <;> cbv

/-- The waiting value has an exact earlier-input witness, including its error count.
Witness: the general stored-value replay theorem, applied to the actual retained node. -/
theorem waiting_value_provenance
    : ∃ supplied,
        .taskSuccess firstTask supplied ∈ [first]
        ∧ supplied.value = firstValue
        ∧ (GraphEvent.taskSuccess firstTask supplied).MatchesWork work := by
  have member : ({ task := ⟨firstTask, [parent]⟩, value := some firstValue } : TaskNode)
      ∈ waiting.taskNodes := by
    change _ ∈ ([{ task := ⟨firstTask, [parent]⟩, value := some firstValue },
      { task := ⟨sharedTask, [parent, other]⟩ }] : List TaskNode)
    exact List.mem_cons_self
  exact createWorkQueue_replay_storedValues_match waiting_valid _ member _ rfl

/-- The shared settlement publishes both values once, then closes both contributing groups.
Witness: the actual single-pass handler; Q does not republish the removed shared value. -/
theorem later_publication
    : (waiting.taskSuccess sharedTask sharedResult).2
      = [
        .groupValues parent [firstValue, sharedValue],
        .groupSuccess parent [] [],
        .groupSuccess other [] []
      ] := by
  cbv

/-- Source annotations retain a silent success before the later four-atom publication block.
Witness: both split and joined input batches have the same handler blocks, including the
empty first block and the separate terminal marker. The queue's batching is unchanged.
-/
theorem source_blocks_keep_silent_settlement
    : let publisher : IncrementalPublisher :=
        { active := initial.initialGroups ++ initial.initialStreams }
      let split := initial.sourceRunBlocks publisher [[first], [shared]]
      let joined := initial.sourceRunBlocks publisher [[first, shared]]
      split.2.2 = joined.2.2
      ∧ split.2.2.map (fun block => (block.1, block.2.length))
        = [(some first, 0), (some shared, 4), (none, 1)] := by
  constructor <;> cbv

/-- Flattening annotated handler blocks recovers the actual split-batch output exactly.
Witness: the general runner-agreement theorem, including the silent first settlement.
-/
theorem source_blocks_exact_output
    : let publisher : IncrementalPublisher :=
        { active := initial.initialGroups ++ initial.initialStreams }
      (initial.sourceRunBlocks publisher [[first], [shared]]).2.2.flatMap Prod.snd
      = (initial.runNormalized [[first], [shared]]).2.flatten.flatMap publicationAtoms :=
  (initial.sourceRunBlocks_agrees [[first], [shared]]).2

/-- The first value's later publication still points back to the earlier settlement.
Witness: the general success-handler output theorem, not a restated source payload.
The other possible input has a distinct task occurrence. -/
theorem delayed_publication_provenance
    : ∃ supplied,
        .taskSuccess firstTask supplied ∈ [first]
        ∧ supplied.value = firstValue
        ∧ (GraphEvent.taskSuccess firstTask supplied).MatchesWork work := by
  have emitted : Execution.WorkQueueEvent.groupValues parent [firstValue, sharedValue]
      ∈ (waiting.taskSuccess sharedTask sharedResult).2 := by
    rw [later_publication]
    exact List.mem_cons_self
  obtain ⟨occurrence, supplied, source, same, matching⟩ :=
    createWorkQueue_replay_taskSuccess_publishedValues waiting_valid sharedMatches
      parent [firstValue, sharedValue] emitted firstValue List.mem_cons_self
  rcases List.mem_append.mp source with earlier | current
  · have eventEq := List.mem_singleton.mp earlier
    have parts := GraphEvent.taskSuccess.inj eventEq
    exact ⟨supplied, parts.1 ▸ earlier, same, parts.1 ▸ matching⟩
  · have eventEq := List.mem_singleton.mp current
    have parts := GraphEvent.taskSuccess.inj eventEq
    rw [parts.2] at same
    have errorsEq := congrArg ExecutionGroupValue.errors same
    contradiction

/-- Split and joined input batches have the same two distinct publication occurrences.
Witness: the general normalized-output theorem, with actual payload evaluation to ensure
the uniqueness conclusion is not vacuous. Both contributor closures are retained. -/
theorem normalized_sources_unique
    : ∀ batches ∈ [[[first], [shared]], [[first, shared]]],
        ∃ published : List ObjectPublication,
          (published.map Prod.fst).Nodup
          ∧ published.map (fun publication => publication.2) = [firstValue, sharedValue]
          ∧ ∀ publication ∈ published,
              ∃ result,
                .taskSuccess publication.1 result ∈ batches.flatten
                ∧ result.value = publication.2
                ∧ (GraphEvent.taskSuccess publication.1 result).MatchesWork work := by
  intro batches member
  have choices : batches = [[first], [shared]] ∨ batches = [[first, shared]] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have inputs : batches.flatten = [first, shared] := by
    rcases choices with rfl | rfl <;> rfl
  have valid : ValidGraphEvents work batches.flatten := inputs ▸ inputs_valid_started.1
  have output : (initial.runNormalized batches).2.flatten.flatMap normalizedObjectValues =
      [firstValue, sharedValue] := by
    rcases choices with rfl | rfl <;> cbv
  obtain ⟨published, unique, values, sources⟩ := createWorkQueue_runNormalized_objectSources valid
  exact ⟨published, unique, values.trans output, sources⟩

-----------------------------------------------------------------------------------------
-- Shared-owner flushing retains one matching under both input batching choices
-----------------------------------------------------------------------------------------

/-- Delayed nullable-error output has fresh, exact sources under split or joined input.
Witness: the general atomic matching theorem uses the actual normalized output, including
both owner closures and termination, without identifying settlement with publication.
-/
theorem normalized_publication_matching
    : ∀ batches ∈ [[[first], [shared]], [[first, shared]]],
        let outputs := (initial.runNormalized batches).2
        ∃ matching : PublicationMatching,
          WorkBatching (outputs.flatten.flatMap publicationAtoms) outputs
          ∧ ∀ index event,
              (outputs.flatten.flatMap publicationAtoms)[index]? = some event
              → IsValue event
              → PublicationAt work (matching index) event
                ∧ ¬Published matching
                    ((outputs.flatten.flatMap publicationAtoms).take index)
                    (matching index) := by
  intro batches member
  have choices : batches = [[first], [shared]] ∨ batches = [[first, shared]] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have inputs : batches.flatten = [first, shared] := by
    rcases choices with rfl | rfl <;> rfl
  have valid : ValidGraphEvents work batches.flatten := inputs ▸ inputs_valid_started.1
  have started : inputsStarted work batches = true := by
    rcases choices with rfl | rfl <;> cbv
  exact createWorkQueue_runNormalized_publicationMatching valid started

-----------------------------------------------------------------------------------------
-- Actual closures account for root contributors by their source-handler boundary
-----------------------------------------------------------------------------------------

/-- Every root contributor has succeeded by either owner's actual closure handler.
Witness: generic inverse registration and healthy retirement, specialized to both
normalized batching choices. The source prefix is tied to that carrier, not the final run.
-/
theorem successful_carrier_root_settlements
    : ∀ batches ∈ [[[first], [shared]], [[first, shared]]],
      ∀ group ∈ [parent, other],
        ∀ address owners payload,
          TaskAt work (.executionGroup address) owners none payload
          → group.key ∈ owners
          → ∃ before event after result,
              batches.flatten = before ++ event :: after
              ∧ Execution.WorkQueueEvent.groupSuccess group [] []
                ∈ ((initial.replayGraphEvents before).handleGraphEvent event).2
              ∧ GraphEvent.taskSuccess (.executionGroup address) result
                ∈ before ++ [event] := by
  intro batches member group owner address owners payload known contributes
  have choices : batches = [[first], [shared]] ∨ batches = [[first, shared]] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have inputs : batches.flatten = [first, shared] := by
    rcases choices with rfl | rfl <;> rfl
  have started : inputsStarted work batches = true := by
    rcases choices with rfl | rfl <;> rfl
  have output : (initial.runNormalized batches).2.flatten =
      [.groupValues parent [firstValue],
        .groupValues parent [sharedValue], .groupSuccess parent [] [],
        .groupSuccess other [] [], .workQueueTermination] := by
    rcases choices with rfl | rfl <;> rfl
  have carrier : Execution.WorkQueueEvent.groupSuccess group [] []
      ∈ (initial.runNormalized batches).2.flatten := by
    rw [output]
    have choice : group = parent ∨ group = other := by simpa using owner
    rcases choice with rfl | rfl <;> simp
  exact generated.runNormalized_successfulCarrier_rootContributor_prefix
    (inputs ▸ inputs_valid_started.1) started carrier known contributes

-----------------------------------------------------------------------------------------
-- Local flush uniqueness does not need a duplicate-free input membership list
-----------------------------------------------------------------------------------------

/-- A raw duplicate membership cannot select the same stored task twice in one flush.
Witness: apply the general flush witness to the reached waiting state. This synthetic
group argument tests the local fold; it is not claimed to be a legal completion event. -/
theorem duplicate_membership_selects_once
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ (selected.filterMap TaskNode.value) = [firstValue] := by
  let repeated : GroupNode :=
    { group := ⟨parent, none⟩, tasks := [firstTask, firstTask] }
  obtain ⟨selected, unique, _, values, _, _, _⟩ :=
    flushGroupTask_witness waiting repeated.tasks [] []
  refine ⟨selected, unique, ?_⟩
  have actual : (repeated.tasks.foldl flushGroupTask (waiting, [], [])).2.1 = [firstValue] := by
    cbv
  simpa only [List.nil_append, actual] using values.symm

/-- Repeated raw memberships still select every available stored task, not just at most one.
Witness: complete selection includes the actual waiting lookup, while occurrence uniqueness
and the exact output show that its nullable-error value is emitted once. The repeated list
is a local robustness test, not a generated group-completion premise.
-/
theorem duplicate_membership_covers_value
    : ∃ selected : List TaskNode,
        (selected.map (fun node => node.task.occurrence)).Nodup
        ∧ selected.filterMap TaskNode.value = [firstValue]
        ∧ ∀ node, waiting.taskNode? firstTask = some node → node ∈ selected := by
  obtain ⟨selected, unique, _, values, _, _, _, covered, _⟩ :=
    flushGroupTask_completeWitness waiting [firstTask, firstTask] [] []
  refine ⟨
    selected,
    unique,
    ?_,
    fun node found =>
      covered firstTask (by simp) node found
  ⟩
  have actual : ([firstTask, firstTask].foldl flushGroupTask (waiting, [], [])).2.1
      = [firstValue] := by cbv
  simpa only [List.nil_append, actual] using values.symm

-----------------------------------------------------------------------------------------
-- The actual shared-owner success fold cannot lose either stored occurrence
-----------------------------------------------------------------------------------------

/-- The actual stored state immediately before the later shared settlement's owner fold. -/
private def ready : State :=
  waiting.putTaskNode { task := ⟨sharedTask, [parent, other]⟩, value := some sharedValue }

/-- Both stored fixture values are fresh against its still-empty publication prefix.
Witness: the empty prefix and a deliberately unconstrained payload predicate; the general
conservation theorem still tracks exact occurrences, values, and error counts.
-/
private theorem ready_inventory : ready.PublicationInventory (fun _ _ => True) [] :=
  ⟨by simp, by simp, fun _ _ _ _ => ⟨trivial, by simp⟩⟩

/-- Both buffered values are in the same unique ledger, even though two owners close.
Witness: apply single-pass conservation to the actual stored state. Executable residual
lookups are empty, so both occurrences must have been published, including nullable errors.
The output equality checks that this is the fold used by the actual shared-task handler.
-/
theorem shared_fold_covers_both_values
    : let result := [parent, other].foldl successGroupStep (ready, [], {})
      ∃ added : List ObjectPublication,
        (added.map Prod.fst).Nodup
        ∧ added.map Prod.snd = result.2.1.flatMap WorkQueueEvent.objectValues
        ∧ (firstTask, firstValue) ∈ added
        ∧ (sharedTask, sharedValue) ∈ added
        ∧ result.2.1 = (waiting.taskSuccess sharedTask sharedResult).2 := by
  let result := [parent, other].foldl successGroupStep (ready, [], {})
  obtain ⟨added, values, inventory, conserved⟩ :=
    ready_inventory.successGroupFold_conserves [parent, other]
  have firstFound : ready.taskNode? firstTask = some
      { task := ⟨firstTask, [parent]⟩, value := some firstValue } := rfl
  have sharedFound : ready.taskNode? sharedTask = some
      { task := ⟨sharedTask, [parent, other]⟩, value := some sharedValue } := rfl
  have firstGone : result.1.taskNode? firstTask = none := rfl
  have sharedGone : result.1.taskNode? sharedTask = none := rfl
  refine ⟨
    added,
    by simpa only [List.nil_append] using inventory.unique,
    values,
    ?_,
    ?_,
    ?_
  ⟩
  · exact (conserved firstTask _ firstValue firstFound rfl).resolve_right (by
      change result.1.taskNode? firstTask ≠ _
      simp [firstGone])
  · exact (conserved sharedTask _ sharedValue sharedFound rfl).resolve_right (by
      change result.1.taskNode? sharedTask ≠ _
      simp [sharedGone])
  · rfl

/-- A synthetic partial flush preserves another group's stored task exactly.
Witness: the unselected-lookup theorem, applied with a list containing only the first task.
This local test rules out using successful closure as blanket permission to drop values.
-/
theorem unselected_shared_value_retained
    : let onlyFirst : GroupNode := { group := ⟨parent, none⟩, tasks := [firstTask] }
      (ready.finishGroupSuccess onlyFirst).1.taskNode? sharedTask
      = ready.taskNode? sharedTask := by
  apply State.finishGroupSuccess_lookup_unselected
  simp [firstTask, sharedTask]

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerPublication
