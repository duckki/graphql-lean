import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionSettlement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay

/-! Actual source replay derives rejection retention against successful counter settlements. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A fixed successful task cannot occur in a valid source prefix's object failures. -/
theorem ValidGraphEvents.succeeds_not_failureSettlements {work events occurrence}
    (valid : ValidGraphEvents work events) (succeeds : TaskSucceeds work occurrence)
    : occurrence ∉ GraphEvent.failureSettlements events := by
  intro recorded
  obtain ⟨owners, producer, path, errors, known⟩ := valid.failureSettlements_known occurrence recorded
  obtain ⟨otherOwners, birth, payload, descriptor, successful⟩ := succeeds
  have same := (known.unique descriptor).2.2
  subst payload
  simp [Payload.failure] at successful

/-- Each object success in a valid source prefix has a successful fixed task outcome. -/
theorem ValidGraphEvents.groupSettlements_succeed {work events occurrence}
    (valid : ValidGraphEvents work events)
    (member : occurrence ∈ GraphEvent.groupSettlements events)
    : TaskSucceeds work occurrence := by
  have recorded : occurrence ∈ events.flatMap GraphEvent.groupSuccesses :=
    List.mem_reverse.mp member
  obtain ⟨event, eventMember, success⟩ := List.mem_flatMap.mp recorded
  have succeeds : occurrence ∈ event.successes := by
    cases event <;> simp_all [GraphEvent.groupSuccesses, GraphEvent.successes]
  exact valid.successes_succeed (List.mem_flatMap.mpr ⟨event, eventMember, succeeds⟩)

/-- Every source step preserves retention, recording only a present task's new rejection.
Witness: source outcome uniqueness separates successes from earlier failures; the
success-only pending ledger supplies live owner memberships before each fresh rejection.
-/
theorem State.RetainedFailures.handleGraphEvent {queue : State} {work before failed}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    : (queue.handleGraphEvent event).1.RetainedFailures work
        (queue.objectFailureContribution event ++ failed) := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa [State.handleGraphEvent, State.taskSuccess, found,
          State.objectFailureContribution] using prior
      | some node =>
          apply prior.taskSuccess ledger occurrence result node found
          · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
              (GraphEvent.groupSettlements_subsetIdentities before member)
          · exact fun member => valid.succeeds_not_failureSettlements
              (matching.successes_succeed (by simp [GraphEvent.successes])) (included member)
          · intro task member recorded
            exact valid.succeeds_not_failureSettlements (valid.groupSettlements_succeed member)
              (included recorded)
          · exact ledger.matching.contributorsNodup generated
              (ledger.started node (List.mem_of_find?_eq_some found))
          · intro task member
            obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
            exact ⟨⟨address, payload, some occurrence, same, known⟩,
              matching.childTask_groupsExact member⟩
  | taskFailure occurrence errors =>
      cases found : queue.taskNode? occurrence with
      | none => simpa [State.handleGraphEvent, State.taskFailure, found,
          State.objectFailureContribution] using prior
      | some node =>
          simpa only [State.handleGraphEvent, State.objectFailureContribution, found,
            List.singleton_append]
            using prior.taskFailure ledger occurrence errors node found
              (fun member =>
                fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                  (GraphEvent.groupSettlements_subsetIdentities before member)) matching
  | streamItems stream items =>
      exact prior.streamItems ledger.refs ledger.sound ledger.matching matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess, State.objectFailureContribution,
        List.nil_append]
      split <;> exact prior
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure, State.objectFailureContribution,
        List.nil_append]
      split <;> exact prior

/-- Sequential replay preserves retention for every present rejected source task.
Witness: joint induction with successful-settlement pending accounting and the actual
presence-filtered failure projection. Redundant rejections are retained without claiming
that they are additional licensed causal cuts.
-/
theorem State.RetainedFailures.replayGraphEvents {queue : State} {work before failed}
    (prior : queue.RetainedFailures work failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : (queue.replayGraphEvents events).RetainedFailures work
        (queue.objectFailureContributions events ++ failed) := by
  induction events generalizing queue before failed with
  | nil => simpa [State.replayGraphEvents, State.objectFailureContributions] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have nextRetained := prior.handleGraphEvent ledger generated priorValid included event matching fresh
      have nextLedger := ledger.handleGraphEvent_successes generated
        (GraphEvent.groupSettlements_subsetIdentities before) event matching fresh accepts.1
      rw [← GraphEvent.groupSettlements_append] at nextLedger
      have nextIncluded : (queue.objectFailureContribution event ++ failed).Subset
          (GraphEvent.failureSettlements (before ++ [event])) := by
        rw [GraphEvent.failureSettlements_append]
        intro occurrence member
        rcases List.mem_append.mp member with new | old
        · apply List.mem_append_left
          cases event <;> simp only [State.objectFailureContribution, GraphEvent.groupFailures] at new ⊢
          all_goals try cases new
          split at new
          · cases new
          · exact new
        · exact List.mem_append_right _ (included old)
      have result := ih nextRetained nextLedger nextIncluded
        (by simpa [List.append_assoc] using valid) accepts.2
      simpa only [State.replayGraphEvents, State.objectFailureContributions,
        List.append_assoc, List.foldl_cons]
        using result

/-- Initialization has no failed task inventory. -/
theorem createWorkQueue_retainedFailures (input : Work) (work : Execution.Work)
    : (State.initialize input).RetainedFailures work [] :=
  State.RetainedFailures.nil _ _

/-- Every normalized started replay retains failures on surviving contributor records.
Witness: actual handler replay and the control-only termination flag change. This is
retention and fresh-ref exclusion; causal cut licensing remains a separate proof.
-/
theorem ExecutedWork.runNormalized_retainedFailures {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RetainedFailures
        work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten) := by
  have retained := (createWorkQueue_retainedFailures (Work.fromExecution work) work).replayGraphEvents
    (before := []) (createWorkQueue_pendingAccounting work) generated (by intro _ member; cases member) batches.flatten valid
    ((State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
      (by rwa [inputsStarted_eq_batchesStarted] at started))
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  rw [same]
  simpa only [State.RetainedFailures, State.taskNode?, List.append_nil] using retained

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
