import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureSettlementPrefixes
import Proofs.GraphQL.IncrementalDelivery.Correctness.TaskErrors

/-! Accepted failures retain an owner untouched by earlier direct failure contributions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact error totals connect the executable health guard to direct failure causes
-----------------------------------------------------------------------------------------

/-- Every failed task in generated work contributes a positive execution-error count.
Witness: root execution's positive-failure certificate and structural task lookup.
-/
theorem ExecutedWork.taskFailure_positive {work : Execution.Work}
    (generated : ExecutedWork work) {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (failed : payload.failure.isSome = true)
    : 0 < payload.failure.getD 0 := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source, selections,
    generated⟩ := generated
  have positive := (Correctness.ExecutionErrors.executeRootSelectionSetCore_positive
    schema resolvers variables fuel parentType source selections 0).2
  rw [generated] at positive
  exact positive.task known failed

/-- An uncached live record has no contributing failure in its complete inventory.
Witness: exact zero error totals contradict generated positive failed-task counts.
Unlike the guard wrapper, this local fact also applies inside its bounded parent walk.
-/
theorem State.GroupErrorAccounting.uncached_noFailedContributor
    {queue : State} {work failed occurrence owners producer payload} {node : GroupNode}
    (counts : queue.GroupErrorAccounting work failed) (generated : ExecutedWork work)
    (member : node ∈ queue.groupNodes) (uncached : node.failure = none)
    (known : TaskAt work occurrence owners producer payload)
    (failure : payload.failure.isSome = true) (owner : node.group.node.key ∈ owners)
    : occurrence ∉ failed := by
  intro recorded
  have total := counts.live node member
  rw [uncached] at total
  have bound := total.contribution_le recorded known owner
  have positive := generated.taskFailure_positive known failure
  simp only [Option.getD_none] at bound
  omega

/-- A guard-healthy group cannot own a failure in its exact accepted-error inventory.
Witness: the guard supplies an uncached live record, whose exact zero count excludes
every generated positive failed contribution.
-/
theorem State.GroupErrorAccounting.groupIsHealthy_noFailedContributor
    {queue : State} {work failed key occurrence owners producer payload}
    (counts : queue.GroupErrorAccounting work failed) (generated : ExecutedWork work)
    (healthy : queue.groupIsHealthy key = true)
    (known : TaskAt work occurrence owners producer payload)
    (failure : payload.failure.isSome = true) (owner : key ∈ owners)
    : occurrence ∉ failed := by
  obtain ⟨node, found, uncached⟩ := State.groupIsHealthy_present healthy
  apply counts.uncached_noFailedContributor generated (List.mem_of_find?_eq_some found)
    uncached known failure
  simpa only [State.groupNode?_key found] using owner

-----------------------------------------------------------------------------------------
-- Recover exact pre-handler counts at an ordered source-failure cut
-----------------------------------------------------------------------------------------

/-- An executable batch acceptance proof restricts to any earlier source prefix.
Witness: split the received list and recurse through the same handler states.
-/
theorem State.acceptsBatch_prefix {queue : State} {before after : List GraphEvent}
    (accepted : queue.acceptsBatch (before ++ after) = true)
    : queue.acceptsBatch before = true := by
  induction before generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      have both : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch (rest ++ after) = true := by
        simpa only [List.cons_append, State.acceptsBatch, Bool.and_eq_true] using accepted
      simpa only [State.acceptsBatch, Bool.and_eq_true] using And.intro both.1 (ih both.2)

/-- Each eligible object cut retains a structural owner with no earlier direct failure.
Witness: exact pre-handler replay supplies the healthy guard, complete error accounting,
and task provenance. The earlier-cut ledger retains settlement order at equal indices.
This excludes direct contributor failure only, not ancestor or producer cancellation.
-/
theorem createWorkQueue_eligibleObjectFailureCuts_directHealthyOwner
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {before after : FailureCuts} {cut : Nat}
    {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        = before ++ (cut, occurrence) :: after)
    : ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ ∀ prior priorOwners,
            prior ∈ before.map Prod.snd
            → TaskHasOwners work prior priorOwners
            → owner ∉ priorOwners := by
  let queue := State.initialize (Work.fromExecution work)
  obtain ⟨earlier, _, _, _, node, _, _, _, sourcePrefix, priorValid, _, _, ledger,
    found, healthy⟩ := createWorkQueue_eligibleObjectFailureCuts_split valid started split
  have accepted := queue.batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have beforePrefix : (earlier.filterMap Prod.fst).IsPrefix batches.flatten :=
    (List.prefix_append _ _).trans sourcePrefix
  obtain ⟨suffix, inputEq⟩ := beforePrefix
  rw [← inputEq] at accepted
  have priorAccepted := State.acceptsBatch_prefix accepted
  have bookkeeping := (createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated (earlier.filterMap Prod.fst) priorValid priorAccepted
  have counts := (createWorkQueue_groupErrorAccounting (Work.fromExecution work) work).replayGraphEvents
    (before := []) (createWorkQueue_pendingAccounting work) generated
    (earlier.filterMap Prod.fst) priorValid priorAccepted
  simp only [List.append_nil] at counts
  obtain ⟨nodeMember, occurrenceEq⟩ := State.taskNode?_some found
  obtain ⟨⟨_, payload, producer, _, task⟩, _⟩ :=
    bookkeeping.matching node.task (bookkeeping.started node nodeMember)
  obtain ⟨owner, contributes, guard⟩ := State.taskHasHealthyOwner_iff.mp healthy
  refine ⟨node.task.groups.map Execution.DeliveryNode.key, owner.key,
    ⟨producer, payload, occurrenceEq ▸ task⟩,
    List.mem_map.mpr ⟨owner, contributes, rfl⟩, ?_⟩
  intro prior priorOwners earlierFailure descriptor contributesPrior
  have recorded : prior ∈ queue.objectFailureContributions (earlier.filterMap Prod.fst) := by
    rw [← ledger, List.mem_reverse]
    exact earlierFailure
  obtain ⟨owners, producer, path, errors, failedTask⟩ := priorValid.failureSettlements_known prior
    ((queue.objectFailureContributions_sublist _).subset recorded)
  obtain ⟨parent, value, known⟩ := descriptor
  have same := failedTask.unique known
  have ownerMember : owner.key ∈ owners := same.1.symm ▸ contributesPrior
  exact counts.groupIsHealthy_noFailedContributor generated guard failedTask rfl
    ownerMember recorded

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
