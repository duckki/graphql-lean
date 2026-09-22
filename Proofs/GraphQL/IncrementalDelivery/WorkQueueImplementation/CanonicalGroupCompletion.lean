import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCompletionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupNoticeFreshness

/-! Announced group completion on the actual canonical conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Publisher normalization preserves exact group-notice and completion inventories
-----------------------------------------------------------------------------------------

/-- Every canonical group notice remains active or has a canonical group completion.
Witness: raw tracking, exact notice/closure projection through normalization and atomization,
and agreement between started eventwise replay and the actual normalized final state.
No abstract admission, failure matching, or terminal premise is required.
-/
theorem groupNoticeKeys_tracked {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    : ∀ key ∈ (initialQueue work).rootGroups ++ w.events.flatMap groupNoticeKeys,
        key ∈ ((initialQueue work).runNormalized inputs).1.rootGroups
        ∨ key ∈ w.events.flatMap groupClosureKeys := by
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  have notices
      : w.events.flatMap groupNoticeKeys
        = ((initialQueue work).rawEventReplay inputs.flatten).2.flatMap rawGroupNoticeKeys := by
    rw [exactHistory, atomicGroupNotices _ _
      ((initialQueue work).rawEventReplay_nonemptyValues inputs.flatten valid.nonemptyItems)]
  have closures
      : w.events.flatMap groupClosureKeys
        = ((initialQueue work).rawEventReplay inputs.flatten).2.flatMap rawGroupClosureKeys := by
    rw [exactHistory, List.flatMap_assoc]
    simp only [publicationAtoms_groupClosureKeys,
      IncrementalPublisher.normalizeBatch_groupClosureKeys]
  obtain ⟨flag, state⟩ := State.runNormalized_stateCore (initialQueue work) inputs
    ((inputsStarted_eq_batchesStarted work inputs) ▸ started)
  intro key member
  rw [notices] at member
  rw [state, closures]
  have tracked := generated.rawEventReplay_groupNoticeCompletion inputs.flatten
    (fun _ member => valid.eachMatches member) key member
  simpa only [State.rawEventReplay_state] using tracked

-----------------------------------------------------------------------------------------
-- The announced-group branch of terminal node accounting is discharged
-----------------------------------------------------------------------------------------

/-- A generated group announced anywhere in a terminated canonical history has completed.
Witness: generated group/stream role separation identifies its group notice; exact replay
tracking and empty final roots force a real completion. This covers successful and failed
groups, but makes no claim yet about omitted latent nodes or announced streams.
-/
theorem groupNode_terminalCompleted {work inputs node dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .group dependencies producer)
    (announced : node.key ∈ announcedKeys (initialKeys work) w.events)
    : node.key ∈ completedKeys w.events := by
  have groupNotice := groupNode_announced_group (index := w.events.length)
    generated valid history known (by simpa only [List.take_length] using announced)
  simp only [List.take_length] at groupNotice
  rcases groupNoticeKeys_tracked generated valid started history node.key groupNotice with
    active | completed
  · have empty := (createWorkQueue_terminalRoots (Work.fromExecution work) inputs ended).1
    rw [empty] at active
    cases active
  · exact groupClosureKeys_subset_completed w.events completed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
