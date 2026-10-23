import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupObjectPublicationAcceptance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemPublicationReflection

/-! Actual startup publications expose the complete permanent object-child registration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A processed object callback registers its complete child chunk, and the permanent
catalogue retains those tasks through the remaining FIFO inputs and later host batches.
-/
theorem TaskAt.executionGroup_registered_after_startup_batch_object
    {work inputs earlier batch later fifo tail producer result node address owners
      payload}
    (startup : InitialStartup)
    (known : TaskAt work (.executionGroup address) owners (some producer) payload)
    (matching : (GraphEvent.taskSuccess producer result).MatchesWork work)
    (started : inputsStarted work inputs startup = true)
    (split : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ .taskSuccess producer result :: tail)
    (found
      : (((((State.initialize (Work.fromExecution work) startup)).replayBatches
            earlier).replayGraphEvents
            fifo (GraphEvent.availableFailures batch)).cacheTaskFailures
          (GraphEvent.availableFailures batch)).taskNode?
          producer
        = some node)
    : ∃ task ∈
        (((State.initialize (Work.fromExecution work) startup)).runNormalized
          inputs).1.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  obtain ⟨task, member, identity, groups⟩ :=
    State.taskSuccess_child_registered found matching known available
  have afterMember : task ∈
      (current.handleGraphEvent (.taskSuccess producer result) available).1.tasks
      := member
  have dispatchedMember : task ∈ (current.dispatchGraphEvent (.taskSuccess producer result)
      available).1.tasks := afterMember
  have remaining := (current.dispatchGraphEvent (.taskSuccess producer result)
    available).1.replayGraphEvents_tasks_subset tail available dispatchedMember
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← split, ← inputsStartedWithStartup_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  obtain ⟨running, _, _⟩ := boundary.batchesStarted_cons batch later checked.2
  obtain ⟨terminal, core⟩ := boundary.handleGraphEvents_stateCore batch running
  have batchMember : task ∈ (boundary.handleGraphEvents batch).1.tasks := by
    rw [core]
    change task ∈ (boundary.replayGraphEvents batch available).tasks
    rw [batchEq, State.replayGraphEvents_append _ _ _ available]
    exact remaining
  have retained := (boundary.handleGraphEvents batch).1.replayBatches_tasks_subset later batchMember
  refine ⟨task, ?_, identity, groups⟩
  simpa only [initial, boundary, State.runNormalized_replayBatches, split,
    State.replayBatches, List.foldl_append, List.foldl_cons]
    using retained

namespace ConformancePlan

/-- A published structural object has an accepted, source-matched storing boundary.
Witness: publication provenance selects its object atom, then exact raw release accounting
recovers the actual input, lookup for that same occurrence.
-/
theorem startup_published_object_processed {work inputs w address}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (published : Published w.matching w.events (.executionGroup address))
    : ∃ earlier batch later fifo result tail node,
        inputs = earlier ++ batch :: later
        ∧ batch = fifo ++ .taskSuccess (.executionGroup address) result :: tail
        ∧ (GraphEvent.taskSuccess (.executionGroup address) result).MatchesWork work
        ∧ (((((State.initialize (Work.fromExecution work) startup)).replayBatches
              earlier).replayGraphEvents
              fifo (GraphEvent.availableFailures batch)).cacheTaskFailures
            (GraphEvent.availableFailures batch)).taskNode?
            (.executionGroup address)
          = some node := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have exactValue := same ▸ admitted.publicationAt selected value
  cases event <;> try cases value
  case groupValues owner payload =>
    simpa only [same] using Witness.startup_groupPublication_processed generated startup matched
      valid started
      history ledger selected
  case streamValues node values groups streams =>
    cases values with
    | nil => cases exactValue
    | cons head tail =>
        cases tail with
        | cons next rest => cases exactValue
        | nil =>
            obtain ⟨owners, producer, impossible⟩ := exactValue
            obtain ⟨_, _, _, _, _, _, _, _, payload⟩ := impossible

/-- Every object child of a published object is permanently registered.
Witness: the actual accepted handler integrates its source-matched child chunk; subsequent
handlers preserve the task registry. No endpoint lookup or child publication is assumed.
-/
theorem startup_published_object_child_registered
    {work inputs w address owners producer payload} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (known
      : TaskAt work (.executionGroup address) owners
          (some (.executionGroup producer)) payload)
    (published : Published w.matching w.events (.executionGroup producer))
    : ∃ task ∈
        (((State.initialize (Work.fromExecution work) startup)).runNormalized
          inputs).1.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  obtain ⟨earlier, batch, later, fifo, result, tail, node, split, batchEq, matching, found⟩ :=
    startup_published_object_processed generated startup matched valid started history admitted
      ledger published
  exact TaskAt.executionGroup_registered_after_startup_batch_object startup known matching
    started split
    batchEq found

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
