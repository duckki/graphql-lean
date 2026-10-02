import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupObjectProducer
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulSettlementAcceptance

/-! Canonical object publications originate at actual accepted storing boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The exact object label is already registered by its own releasing handler
-----------------------------------------------------------------------------------------

/-- An element's inner projection index lies within the whole flattened projection.
Witness: list induction adds the lengths of preceding projections without comparing values.
-/
private theorem projected_rank_lt {α β : Type} (project : α → List β)
    {events : List α} {index event offset}
    (selected : events[index]? = some event) (within : offset < (project event).length)
    : ((events.take index).flatMap project).length + offset
      < (events.flatMap project).length := by
  induction events generalizing index with
  | nil => cases selected
  | cons head rest ih =>
      cases index with
      | zero =>
          cases selected
          simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
            List.flatMap_cons, List.length_append]
          omega
      | succ index =>
          have tail := ih selected
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          omega

/-- Every value in a recovered release block lies before that handler's endpoint.
Witness: the boundary's exact prior count and the selected block's indexed value.
-/
theorem GroupPublicationHandlerBoundary.value_rank_lt
    {queue received group values count offset value}
    (boundary : GroupPublicationHandlerBoundary queue received group values count)
    (selected : values[offset]? = some value)
    : count + offset
      < ((queue.rawEventReplay (boundary.before ++ [boundary.event])).2.flatMap
          WorkQueueEvent.objectValues).length := by
  have inside := projected_rank_lt WorkQueueEvent.objectValues boundary.atHandler
    (offset := offset) (List.getElem?_eq_some_iff.mp selected).1
  have countEq := boundary.count
  rw [State.rawEventReplay_append]
  simp only [State.rawEventReplay_cons, State.rawEventReplay_state]
  change count + offset < (((queue.rawEventReplay boundary.before).2
    ++ (((queue.replayGraphEvents boundary.before).handleGraphEvent boundary.event).2
      ++ [])).flatMap WorkQueueEvent.objectValues).length
  simp only [List.append_nil, List.flatMap_append, List.length_append]
  omega

namespace ConformancePlan

/-- A canonical object's exact matched task is registered by its raw release handler.
Witness: its unchanged ledger entry lies within that handler's consumed prefix; the
registration certificate covers precisely those labels, even when wire values coincide.
-/
theorem Witness.groupPublication_registered_at_handler {work inputs w index owner payload}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupValues owner payload))
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    (boundary
      : GroupPublicationHandlerBoundary (initialQueue work) inputs.flatten origin.group
          origin.values (origin.before.flatMap WorkQueueEvent.objectValues).length)
    : ∃ task,
        task
          ∈ ((initialQueue work).replayGraphEvents
              (boundary.before ++ [boundary.event])).tasks
        ∧ task.occurrence = w.matching index := by
  obtain ⟨published, batched, exactLedger, _⟩ := ledger
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  have earlierLedger : (initialQueue work).ReplayClosuresCovered
      (boundary.before ++ [boundary.event]) published := by
    apply State.ReplayClosuresCovered.prefix (after := boundary.after)
    simpa only [boundary.sourceEq, List.append_assoc, List.singleton_append]
      using batched.flatten accepted
  have rank := origin.objectRank
  have historyEq := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [← historyEq] at rank
  have entry := exactLedger.atObject index owner payload selected
  rw [rank, List.getElem?_map] at entry
  cases found
        : published[(origin.before.flatMap WorkQueueEvent.objectValues).length
                    + origin.offset]? with
  | none => simp only [found, Option.map_none, reduceCtorEq] at entry
  | some publication =>
      have same : publication.1 = w.matching index := by
        simpa only [found, Option.map_some, Option.some.injEq] using entry
      have present := List.mem_of_getElem?
        ((List.getElem?_take_of_lt (boundary.value_rank_lt origin.found)).trans found)
      obtain ⟨task, member, identity⟩ := List.mem_map.mp
        (earlierLedger.registered publication present)
      exact ⟨task, member, identity.trans same⟩

-----------------------------------------------------------------------------------------
-- Successful release excludes ignored source successes of its exact contributor
-----------------------------------------------------------------------------------------

/-- Every canonical object atom has a real accepted success handler for its matched task.
Witness: recover the raw release group, register the exact ledger label at that handler,
and use successful-carrier health to rule out the source handler's rejection branch.
Publisher owner remapping and equal response values do not change the selected task.
-/
theorem Witness.groupPublication_processed {work inputs w index owner payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupValues owner payload))
    : ∃ before result after node,
        inputs.flatten = before ++ .taskSuccess (w.matching index) result :: after
        ∧ (GraphEvent.taskSuccess (w.matching index) result).MatchesWork work
        ∧ ((initialQueue work).replayGraphEvents before).taskNode? (w.matching index)
          = some node
        ∧ ((initialQueue work).replayGraphEvents before).taskHasHealthyOwner node.task
          = true := by
  obtain ⟨origin⟩ := Witness.groupPublication_origin started history selected
  obtain ⟨boundary⟩ := origin.handlerBoundary
  obtain ⟨task, registered, identity⟩ := Witness.groupPublication_registered_at_handler
    started history ledger selected origin boundary
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  have received := (initialQueue work).batchesStarted_acceptsBatch inputs accepted
  have prior : (boundary.before ++ [boundary.event]).IsPrefix inputs.flatten :=
    ⟨boundary.after, by simp [boundary.sourceEq, List.append_assoc]⟩
  have priorAccepted : (initialQueue work).acceptsBatch
      (boundary.before ++ [boundary.event]) = true := by
    apply State.acceptsBatch_prefix (after := boundary.after)
    simpa only [boundary.sourceEq, List.append_assoc, List.singleton_append] using received
  obtain ⟨groups, streams, carrier⟩ :=
    (((initialQueue work).replayGraphEvents boundary.before).handleGraphEvent_publicationPairs
      boundary.event).next boundary.atHandler
  obtain ⟨producer, known⟩ := Witness.groupPublication_taskAt started history ledger selected origin
  have contributes := createWorkQueue_rawEventReplay_publicationContributors valid
    origin.group origin.values origin.members.1 origin.value origin.members.2
  have accounting := (createWorkQueue_pendingAccounting work).replayGraphEvents (before := [])
    generated (boundary.before ++ [boundary.event]) (valid.prefix prior) priorAccepted
  obtain ⟨_, actualPayload, actualProducer, _, actualKnown⟩ :=
    (accounting.matching task registered).1
  have ownersEq := (TaskAt.unique (identity ▸ actualKnown) known).1
  obtain ⟨before, result, after, node, split, found, healthy⟩ :=
    generated.successfulCarrier_registeredContributor_processed (valid.prefix prior)
      priorAccepted (List.mem_of_getElem? carrier) registered (ownersEq.symm ▸ contributes)
  rw [identity] at split found
  have full : inputs.flatten = before ++ .taskSuccess (w.matching index) result
      :: (after ++ boundary.after) := by
    calc
      inputs.flatten = (boundary.before ++ [boundary.event]) ++ boundary.after := by
        simp only [boundary.sourceEq, List.append_assoc, List.singleton_append]
      _ = _ := by rw [split]; simp only [List.append_assoc, List.cons_append]
  exact ⟨before, result, after ++ boundary.after, node, full,
    valid.eachMatches (full ▸ List.mem_append_right _ List.mem_cons_self), found, healthy⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
