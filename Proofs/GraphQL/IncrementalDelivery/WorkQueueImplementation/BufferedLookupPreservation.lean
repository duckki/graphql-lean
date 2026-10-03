import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasePublicationLedger

/-! Integration preserves exact buffered lookups outside the settling producer. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration and producer attachment cannot overwrite another stored task
-----------------------------------------------------------------------------------------

/-- Replacing another occurrence preserves the existing first-match task lookup.
Witness: map/find induction; the replacement still has the distinct updated occurrence.
No task-map uniqueness premise is required.
-/
theorem State.putTaskNode_lookup_other {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (updated : TaskNode)
    (different : updated.task.occurrence ≠ occurrence)
    : (queue.putTaskNode updated).taskNode? occurrence = some node := by
  have loop (nodes : List TaskNode)
      (lookup : nodes.find? (fun node => node.task.occurrence == occurrence) = some node)
      : (nodes.map (fun old =>
          if old.task.occurrence == updated.task.occurrence then updated else old)).find?
            (fun node => node.task.occurrence == occurrence) = some node := by
    induction nodes with
    | nil => cases lookup
    | cons head rest ih =>
        by_cases replace : head.task.occurrence = updated.task.occurrence
        · have skip : head.task.occurrence ≠ occurrence := replace ▸ different
          have tail : rest.find? (fun node => node.task.occurrence == occurrence)
              = some node := by
            simpa [List.find?_cons, occurrence_beq_iff_eq, skip] using lookup
          simpa [List.find?_cons, occurrence_beq_iff_eq, replace, different] using ih tail
        · by_cases selected : head.task.occurrence = occurrence
          · simpa [List.find?_cons, occurrence_beq_iff_eq, selected, Ne.symm different]
              using lookup
          · have tail : rest.find? (fun node => node.task.occurrence == occurrence)
                = some node := by
              simpa [List.find?_cons, occurrence_beq_iff_eq, selected] using lookup
            simpa [List.find?_cons, occurrence_beq_iff_eq, replace, selected]
              using ih tail
  exact loop queue.taskNodes found

/-- Integrating child work retains every lookup except its stream-attachment producer.
Witness: group registration leaves tasks unchanged, task registration appends new nodes,
and stream attachment can replace only the explicitly supplied producer.
-/
theorem State.maybeIntegrateWork_lookup_other {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (work : Work)
    (producer : Option Occurrence := none)
    (different : producer ≠ some occurrence := by simp)
    : (queue.maybeIntegrateWork work producer).1.taskNode? occurrence = some node := by
  have grouped : (queue.addGroups work.groups).1.taskNode? occurrence = some node := by
    simpa only [State.taskNode?, State.addGroups_taskNodes] using found
  have loop (tasks : List Task) (current : State)
      (prior : current.taskNode? occurrence = some node)
      : (tasks.foldl State.addTask current).taskNode? occurrence = some node := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (State.addTask_taskNode?_of_some prior task)
  have integrated := loop work.tasks _ grouped
  unfold State.maybeIntegrateWork
  dsimp only
  cases producer with
  | none => exact integrated
  | some parent =>
      simp only [State.addStreams]
      split
      · exact integrated
      · rename_i owner lookup
        exact State.putTaskNode_lookup_other integrated _ (by
          intro same
          exact different (congrArg some ((State.taskNode?_some lookup).2.symm.trans same)))

/-- Replacing a present occurrence makes that exact replacement the first matching node.
Witness: map/find induction; earlier nonmatching nodes remain nonmatching and the first
matching node receives the supplied replacement, regardless of duplicate later entries.
-/
theorem State.putTaskNode_lookup_same {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (updated : TaskNode)
    (same : updated.task.occurrence = occurrence)
    : (queue.putTaskNode updated).taskNode? occurrence = some updated := by
  change (queue.taskNodes.map (fun old =>
    if old.task.occurrence == updated.task.occurrence then updated else old)).find?
      (fun candidate => candidate.task.occurrence == occurrence) = _
  rw [same]
  have loop (nodes : List TaskNode)
      (lookup : nodes.find? (fun candidate => candidate.task.occurrence == occurrence)
        = some node)
      : (nodes.map (fun old =>
          if old.task.occurrence == occurrence then updated else old)).find?
            (fun candidate => candidate.task.occurrence == occurrence) = some updated := by
    induction nodes with
    | nil => cases lookup
    | cons head rest ih =>
        by_cases selected : (head.task.occurrence == occurrence) = true
        · simp [selected, same, (occurrence_beq_iff_eq occurrence occurrence).mpr rfl]
        · have tail : rest.find? (fun candidate => candidate.task.occurrence == occurrence)
              = some node := by simpa [List.find?_cons, selected] using lookup
          simpa [List.find?_cons, selected] using ih tail
  exact loop queue.taskNodes found

/-- Producer attachment retains the task descriptor and value while extending stream refs.
Witness: group/task registration preserves its first lookup; the final stream operation
only replaces that producer's child-stream list. No well-formedness premise is required.
-/
theorem State.maybeIntegrateWork_lookup_producer {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (work : Work)
    : ∃ next,
        (queue.maybeIntegrateWork work (some occurrence)).1.taskNode? occurrence
          = some next
        ∧ next.task = node.task
        ∧ next.value = node.value := by
  have grouped : (queue.addGroups work.groups).1.taskNode? occurrence = some node := by
    simpa only [State.taskNode?, State.addGroups_taskNodes] using found
  have loop (tasks : List Task) (current : State)
      (prior : current.taskNode? occurrence = some node)
      : (tasks.foldl State.addTask current).taskNode? occurrence = some node := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih => exact ih _ (State.addTask_taskNode?_of_some prior task)
  have integrated := loop work.tasks _ grouped
  unfold State.maybeIntegrateWork
  dsimp only
  simp only [State.addStreams]
  split
  · rename_i impossible
    have contradiction : some node = none := integrated.symm.trans impossible
    cases contradiction
  · rename_i current lookup
    have equal : current = node := Option.some.inj (lookup.symm.trans integrated)
    subst current
    refine ⟨_, State.putTaskNode_lookup_same integrated _ (State.taskNode?_some found).2,
      rfl, rfl⟩

-----------------------------------------------------------------------------------------
-- Buffered carrier coverage transports through lookup-preserving preparation
-----------------------------------------------------------------------------------------

/-- The success handler's prepared state contains its input value and original task.
Witness: install the exact first-match node, then preserve its descriptor and value
through child integration; attaching streams may extend only its child-stream refs.
-/
theorem State.taskSuccess_prepared_value {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (result : TaskResult)
    : ∃ prepared,
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.taskNode?
            occurrence
          = some prepared
        ∧ prepared.task = node.task
        ∧ prepared.value = some result.value :=
  State.maybeIntegrateWork_lookup_producer
    (State.putTaskNode_value_lookup found result.value) result.work

/-- Coverage for a prepared queue also covers each unchanged input lookup.
Witness: use the exact retained node, including its contributor list and stored payload.
-/
theorem State.BufferedClosuresCovered.of_lookups {queue prepared : State}
    {published events} (covered : prepared.BufferedClosuresCovered published events)
    (retained
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → prepared.taskNode? occurrence = some node)
    : queue.BufferedClosuresCovered published events := by
  intro index group groups streams selected occurrence node value found stored contributes
  exact covered index group groups streams selected occurrence node value
    (retained occurrence node value found stored) stored contributes

/-- Output with no successful group carrier has no buffered closure obligations.
Witness: any indexed carrier would contradict its exclusion from the output list.
-/
theorem State.BufferedClosuresCovered.of_noGroupSuccess {queue : State} {published events}
    (absent
      : ∀ group groups streams,
          Execution.WorkQueueEvent.groupSuccess group groups streams ∉ events)
    : queue.BufferedClosuresCovered published events := by
  intro index group groups streams selected
  exact False.elim (absent group groups streams (List.mem_of_getElem? selected))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
