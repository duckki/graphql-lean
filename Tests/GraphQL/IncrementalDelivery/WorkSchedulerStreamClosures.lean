import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Successful, failed, and empty stream boundaries retain source closure order. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerStreamClosures
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def node : DeliveryNode := { key := 0, path := [.field "values"] }
private def emptyWork : Execution.Work := .stream node []
private def failedWork : Execution.Work := .stream node [(.error 1, .empty)]

/-- An exhausted stream may immediately close without publishing items.
Witness: its empty source cursor has reached the exact result count; the queue starts it.
No generated-work premise is needed for the closure-order argument.
-/
theorem empty_source_valid
    : ValidGraphEvents emptyWork [.streamSuccess node]
      ∧ inputsStarted emptyWork [[.streamSuccess node]] = true := by
  refine ⟨.append .nil ⟨[], none, ⟨[], [], Located.root⟩⟩ ?_ ?_, by cbv⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨[], [], none, [], Located.root,
      (by intro source impossible; cases impossible), rfl⟩

/-- A failed first item can close a stream with an error and no item publication.
Witness: the fixed first outcome is the reported failure, with a fresh source closure.
-/
theorem failed_source_valid
    : ValidGraphEvents failedWork [.streamFailure node 1]
      ∧ inputsStarted failedWork [[.streamFailure node 1]] = true := by
  refine ⟨.append .nil ?_ ?_ ?_, by cbv⟩
  · exact ⟨[], [(.error 1, .empty)], none, [], Located.root, .empty, List.mem_cons_self⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨[], [(.error 1, .empty)], none, [], Located.root,
      (by intro source impossible; cases impossible), .empty, rfl⟩

/-- Empty success and first-item failure each emit one closure, followed by termination.
Witness: evaluate both real runners and project the single closing stream action.
-/
theorem empty_and_failed_outputs
    : ((State.initialize (Work.fromExecution emptyWork)).runNormalized
          [[.streamSuccess node]]).2
        = [[.streamSuccess node, .workQueueTermination]]
      ∧ ((State.initialize (Work.fromExecution failedWork)).runNormalized
          [[.streamFailure node 1]]).2
        = [[.streamFailure node 1, .workQueueTermination]] := by
  constructor <;> cbv

/-- Both zero-item outcomes satisfy the same general atomic closure-order witness.
Witness: only existing source validity is supplied; no publication matching is assumed.
-/
theorem empty_and_failed_ordered
    : let empty :=
        ((State.initialize (Work.fromExecution emptyWork)).runNormalized
          [[.streamSuccess node]]).2
      let failed :=
        ((State.initialize (Work.fromExecution failedWork)).runNormalized
          [[.streamFailure node 1]]).2
      ((empty.flatten.flatMap publicationAtoms).filterMap streamAction).Pairwise
        StreamAction.Before
      ∧ ((failed.flatten.flatMap publicationAtoms).filterMap streamAction).Pairwise
          StreamAction.Before := by
  exact ⟨createWorkQueue_runNormalized_atomicStreamActions_ordered
      (batches := [[.streamSuccess node]]) empty_source_valid.1,
    createWorkQueue_runNormalized_atomicStreamActions_ordered
      (batches := [[.streamFailure node 1]]) failed_source_valid.1⟩

/-- Successful and failed completions retain their exact source kind and error count.
Witness: recover the source settlement from each actual emitted closing atom. In
particular, a failure-only input cannot explain a successful closing output.
-/
theorem completion_source_preserves_outcome
    : GraphEvent.streamSuccess node ∈ ([.streamSuccess node] : List GraphEvent)
      ∧ GraphEvent.streamFailure node 1 ∈ ([.streamFailure node 1] : List GraphEvent)
      ∧ Execution.WorkQueueEvent.streamSuccess node
        ∉ ((State.initialize (Work.fromExecution failedWork)).runNormalized
            [[.streamFailure node 1]]).2.flatten.flatMap
            publicationAtoms := by
  refine ⟨?_, ?_, ?_⟩
  · exact createWorkQueue_runNormalized_streamCompletion_source (Work.fromExecution emptyWork)
      [[.streamSuccess node]] (event := .streamSuccess node)
      (by rw [empty_and_failed_outputs.1]; simp [publicationAtoms]) rfl
  · exact createWorkQueue_runNormalized_streamCompletion_source (Work.fromExecution failedWork)
      [[.streamFailure node 1]] (event := .streamFailure node 1)
      (by rw [empty_and_failed_outputs.2]; simp [publicationAtoms]) rfl
  · intro completed
    have source := createWorkQueue_runNormalized_streamCompletion_source (Work.fromExecution failedWork)
      [[.streamFailure node 1]] completed rfl
    simp at source

/-- Neither kind of stream closure permits another item reference with the same key.
Witness: the two-action relation requires unequal keys after the closing action. These
are rejected candidate histories, not output attributed to the executable queue.
-/
theorem post_closure_references_rejected
    : ¬List.Pairwise StreamAction.Before
        ([.streamSuccess node, .streamValues node [⟨.null, 0⟩] [] []].filterMap
          streamAction)
      ∧ ¬List.Pairwise StreamAction.Before
          ([.streamFailure node 1, .streamValues node [⟨.null, 0⟩] [] []].filterMap
            streamAction) := by
  simp [streamAction, StreamAction.Before]

/-- A second closure is also forbidden, even if its success/failure kind changes.
Witness: closing actions are references themselves and the earlier closure forbids the key.
-/
theorem duplicate_closure_rejected
    : ¬List.Pairwise StreamAction.Before
        ([.streamSuccess node, .streamFailure node 1].filterMap streamAction) := by
  simp [streamAction, StreamAction.Before]

/-- Stream-only closure order is not enough when a hypothetical group shares its key.
Witness: the stream action projection omits group closures, but Open counts them. The
generated-work theorem rules out this collision through structural role separation;
this candidate history is not attributed to generated execution.
-/
theorem stream_order_alone_is_not_openness
    : List.Pairwise StreamAction.Before
        ([.groupSuccess node [] [], .streamValues node [⟨.null, 0⟩] [] []].filterMap
          streamAction)
      ∧ ¬Open [node.key] [.groupSuccess node [] []] node.key := by
  simp [List.filterMap_cons, streamAction, Open, announcedKeys, pendingKeys, completedKeys,
    eventPending, eventCompleted]

-----------------------------------------------------------------------------------------
-- Generated non-null item failure retains the successful prefix and exact error task
-----------------------------------------------------------------------------------------

private def failureNode : DeliveryNode := { key := 0, path := [.field "strict"] }

private def failureEntries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (.scalar "x", 0), .empty), (.error 1, .empty)]

private def generatedFailureWork : Execution.Work :=
  .combine (.combine (.combine .empty (.stream failureNode failureEntries)) .empty) .empty

private def firstArrival : GraphEvent :=
  .streamItems failureNode [⟨.item [0, 0, 1] 0, ⟨.scalar "x", 0⟩, {}⟩]

private def failureInputs : List (List GraphEvent) :=
  [[firstArrival], [.streamFailure failureNode 1]]

/-- The first successful item and second failing item come from real non-null completion.
Witness: evaluate strict @stream, whose second resolver item is null under String!.
-/
private theorem failure_generated : ExecutedWork generatedFailureWork := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [field "strict" [] [.stream]], ?_⟩
  cbv

/-- The failed generated stream has its exact finite structural location.
Witness: navigate the root execution's combination wrappers.
-/
private theorem failure_located
    : Located generatedFailureWork [0, 0, 1] (.stream failureNode failureEntries) none
        [] := by
  cbv

/-- The source publishes ordinal zero and fails at ordinal one with the fixed error count.
Witness: exact outcomes, contiguous cursor readiness, fresh identities, and actual starts.
-/
theorem generated_failure_source_valid
    : ValidGraphEvents generatedFailureWork failureInputs.flatten
      ∧ inputsStarted generatedFailureWork failureInputs = true := by
  have firstMatch : firstArrival.MatchesWork generatedFailureWork := by
    intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact ⟨[failureNode.key], none, TaskAt.item failure_located rfl, by cbv⟩
  have firstValid : ValidGraphEvents generatedFailureWork [firstArrival] :=
    .append .nil firstMatch
      (by simp [firstArrival, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, _, failure_located, by simp, by simp,
        (by intro source impossible; cases impossible), rfl⟩
  refine ⟨.append firstValid ?_ ?_ ?_, by cbv⟩
  · exact ⟨_, _, _, _, failure_located, .empty, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · simp [firstArrival, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, failure_located,
      (by intro source impossible; cases impossible), .empty, rfl⟩

/-- The failed generated stream emits exactly its successful prefix, error, and termination.
Witness: evaluate the unchanged queue/publisher; the second item has no value event.
-/
theorem generated_failure_output
    : ((State.initialize (Work.fromExecution generatedFailureWork)).runNormalized
        failureInputs).2
      = [
        [.streamValues failureNode [⟨.scalar "x", 0⟩] [] []],
        [.streamFailure failureNode 1, .workQueueTermination]
      ] := by
  cbv

/-- A real failure notice retains the exact failure task and earlier item publications.
Witness: specialize the joint matching theorem at the actual failure atom, index one.
The candidate task is reachable and unpublished, and its owner is open. This does not
assert cancellation safety or claim to construct the complete ordered failure witness.
-/
theorem generated_failure_accounting
    : let queue := State.initialize (Work.fromExecution generatedFailureWork)
      let atoms := (queue.runNormalized failureInputs).2.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        (∀ index event,
          atoms[index]? = some event
          → IsValue event
          → ¬Published matching (atoms.take index) (matching index))
        ∧ ∃ address ordinal producer,
            TaskAt generatedFailureWork (.item address ordinal) [failureNode.key] producer
              (.item failureNode (.error 1))
            ∧ Reachable generatedFailureWork (.item address ordinal)
            ∧ Open ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.key)
                (atoms.take 1) failureNode.key
            ∧ ¬Published matching atoms (.item address ordinal)
            ∧ ∀ earlier,
                earlier < ordinal
                → Published matching (atoms.take 1) (.item address earlier) := by
  obtain ⟨matching, values, _, failures⟩ :=
    createWorkQueue_runNormalized_streamFailureMatching failure_generated
      generated_failure_source_valid.1 generated_failure_source_valid.2
  refine ⟨matching, fun index event atEvent value => (values index event atEvent value).2, ?_⟩
  apply failures 1 failureNode 1
  rw [generated_failure_output]
  rfl

/-- The generated first failure has a licensed cut and its exact one-error total.
Witness: assemble candidate cuts from the actual joint matching. The only failure
position is one, so no prior cut can cancel its task; the generic licensing equivalence
then proves FailureWitness, and exact stream error accounting gives NodeErrors.
This checks failure evidence, not full admission of every output event.
-/
theorem generated_failure_cut_licensed
    : let queue := State.initialize (Work.fromExecution generatedFailureWork)
      let atoms := (queue.runNormalized failureInputs).2.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
      ∃ failures : FailureCuts,
        StreamFailureCuts generatedFailureWork atoms failures
        ∧ FailureWitness generatedFailureWork
            ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.key)
            matching atoms failures
        ∧ NodeErrors generatedFailureWork (failedBefore failures 1) failureNode.key
            1 := by
  obtain ⟨matching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage failure_generated
      generated_failure_source_valid.1 generated_failure_source_valid.2
  have valid := generated_failure_source_valid.1
  obtain ⟨failures, cuts, unique, evidence⟩ :=
    createWorkQueue_runNormalized_streamFailureCuts failure_generated valid
      matching (fun index event atEvent value => (values index event atEvent value).1) covered
  have positions : failures.map Prod.fst = [1] := cuts.1
  have one : failures.length = 1 := by
    simpa using congrArg List.length positions
  refine ⟨
    matching,
    failures,
    cuts,
    ?_,
    cuts.nodeErrors
      (createWorkQueue_runNormalized_atomicStreamActions_ordered
        generated_failure_source_valid.1) ?_
  ⟩
  · apply (cuts.failureWitness_iff (fun entry member =>
      ⟨(evidence entry member).1, (evidence entry member).2.2⟩)).mpr
    intro before cut occurrence after split
    have sizes := congrArg List.length split
    rw [one] at sizes
    simp only [List.length_append, List.length_cons] at sizes
    have empty : before = [] := List.length_eq_zero_iff.mp (by omega)
    rw [empty]
    exact fun cancelled => cancelled.nonempty rfl
  · rw [generated_failure_output]
    rfl

-----------------------------------------------------------------------------------------
-- Publication safety is derived even when the same stream subsequently fails
-----------------------------------------------------------------------------------------

/-- An actual nonempty failure history protects its earlier successful item.
Witness: construct publication support from the runner's exact payloads, root producer,
and owner health before the failure cut. The new readiness bridge supplies CanPublish
without assuming cancellation safety or full history admission. At the end the stream
has failed, but its published item remains uncancelled under that same cut and matching.
-/
theorem generated_publication_survives_failure
    : let outputs :=
        ((State.initialize (Work.fromExecution generatedFailureWork)).runNormalized
          failureInputs).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      let failures : FailureCuts := [(1, .item [0, 0, 1] 1)]
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ CanPublish generatedFailureWork matching (atoms.take 0) failures (matching 0)
            none
        ∧ NodeFailed generatedFailureWork matching atoms failures failureNode.key
        ∧ ¬TaskCancelled generatedFailureWork matching atoms failures (matching 0) := by
  intro outputs atoms failures
  have shape : atoms = [.streamValues failureNode [⟨.scalar "x", 0⟩] [] [],
      .streamFailure failureNode 1, .workQueueTermination] := by
    dsimp only [atoms, outputs]
    rw [generated_failure_output]
    rfl
  have first : atoms[0]? = some (.streamValues failureNode [⟨.scalar "x", 0⟩] [] []) := by
    rw [shape]
    rfl
  have failedKnown : TaskAt generatedFailureWork (.item [0, 0, 1] 1) [failureNode.key]
      none (.item failureNode (.error 1)) := TaskAt.item failure_located rfl
  have failedPayloads cut occurrence (member : (cut, occurrence) ∈ failures)
      : ∃ owners producer payload,
          TaskAt generatedFailureWork occurrence owners producer payload
          ∧ payload.failure.isSome = true := by
    have same : cut = 1 ∧ occurrence = .item [0, 0, 1] 1 := by
      simpa only [failures, List.mem_singleton, Prod.mk.injEq] using member
    rcases same with ⟨rfl, rfl⟩
    exact ⟨[failureNode.key], none, _, failedKnown, rfl⟩
  obtain ⟨matching, batching, sources, readiness⟩ :=
    createWorkQueue_runNormalized_supportedPublicationReadinessMatching failure_generated
      generated_failure_source_valid.1 generated_failure_source_valid.2
  have support : PublicationSupport generatedFailureWork matching atoms failures := by
    intro index event selected value
    have atFirst : index = 0 ∧ event = .streamValues failureNode [⟨.scalar "x", 0⟩] [] [] := by
      cases index with
      | zero => simpa [shape] using selected.symm
      | succ index =>
          cases index with
          | zero =>
              have same : event = .streamFailure failureNode 1 := by
                simpa [shape] using selected.symm
              subst event
              cases value
          | succ index =>
              cases index with
              | zero =>
                  have same : event = .workQueueTermination := by
                    simpa [shape] using selected.symm
                  subst event
                  cases value
              | succ index => simp [shape] at selected
    rcases atFirst with ⟨rfl, rfl⟩
    obtain ⟨owners, producer, known⟩ := (sources 0 _ first trivial).1
    obtain ⟨ownersEq, dependencies, located⟩ := itemTask_owner_nodeAt known
    have producerEq := failure_generated.streamProducer_unique located
      (NodeAt.stream failure_located) rfl
    refine ⟨owners, producer, _, failureNode.key, known, rfl, ?_, ?_, ?_⟩
    · simp [ownersEq]
    · rintro ⟨cut, member, reached, _⟩
      have same : cut = 1 := by simpa [failures] using member
      simp [same] at reached
    · intro parent same
      rw [producerEq] at same
      cases same
  obtain ⟨owners, producer, known⟩ := (sources 0 _ first trivial).1
  obtain ⟨_, dependencies, located⟩ := itemTask_owner_nodeAt known
  have producerEq := failure_generated.streamProducer_unique located
    (NodeAt.stream failure_located) rfl
  refine ⟨matching, batching, ?_, ?_, ?_⟩
  · simpa only [producerEq]
      using readiness failures failedPayloads support 0 _ first trivial owners producer _
        known
  · exact NodeFailed.task failedKnown (by simp)
      (by simp [failedBefore, failures, shape])
  · intro cancelled
    exact support.cancelled_unpublished failedPayloads cancelled
      ⟨0, _, first, trivial, rfl⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerStreamClosures
