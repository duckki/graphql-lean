import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeFreshness

/-! Source handlers cannot repeat group announcements from earlier source inputs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failure-only handlers carry no group notices
-----------------------------------------------------------------------------------------

/-- Task failures emit no group notice refs.
Witness: handler output shape excludes both notice-bearing constructors; this includes
cached failures and ignored settlements, without requiring a well-formed entry state.
-/
theorem State.taskFailure_groupNoticeRefs (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).2.flatMap rawGroupNoticeRefs = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ref member
  obtain ⟨event, emitted, noticed⟩ := List.mem_flatMap.mp member
  cases event with
  | groupSuccess group groups streams =>
      exact queue.taskFailure_noGroupSuccess occurrence errors group groups streams emitted
  | streamValues stream values groups streams =>
      have impossible : stream.ref ∈
          (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceRefs :=
        List.mem_flatMap.mpr ⟨_, emitted, List.mem_cons_self⟩
      rw [State.taskFailure_streamReferences] at impossible
      cases impossible
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases noticed

-----------------------------------------------------------------------------------------
-- A new source input cannot repeat initial or earlier-source group announcements
-----------------------------------------------------------------------------------------

/-- Any matching source handler excludes all group notices announced before its input.
Witness: task and item successes preserve permanent ancestor protection; item integration
also excludes the old registry. Failure and stream-close handlers carry no group notices.
This proves cross-input freshness, not uniqueness within one handler or carrier.
-/
theorem ExecutedWork.handleGraphEvent_noEarlierGroupNotice
    {work before event ref} (generated : ExecutedWork work)
    (matching : ∀ entry ∈ before, entry.MatchesWork work)
    (matched : event.MatchesWork work)
    (announced
      : ref
        ∈ (State.initialize (Work.fromExecution work)).rootGroups
          ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
              rawGroupNoticeRefs)
    : ref
      ∉ ((((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
            event).2.flatMap
          rawGroupNoticeRefs) := by
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_noEarlierGroupNotice matching matched announced
  | streamItems stream items =>
      exact generated.streamItems_noEarlierGroupNotice matching matched announced
  | taskFailure occurrence errors =>
      simp only [State.handleGraphEvent, State.taskFailure_groupNoticeRefs, List.not_mem_nil,
        not_false_eq_true]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [rawGroupNoticeRefs]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
