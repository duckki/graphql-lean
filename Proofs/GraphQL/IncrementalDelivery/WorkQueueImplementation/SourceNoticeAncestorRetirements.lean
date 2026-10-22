import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StructuralRegistrationFromRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualSourceFrames

/-! Actual source frames derive notice-ancestor retirement under the supplied cache snapshot. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem failed_not_succeeded {work occurrence errors}
    (failed : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (succeeded : TaskSucceeds work occurrence)
    : False := by
  obtain ⟨owners, producer, path, known⟩ := failed
  obtain ⟨otherOwners, birth, payload, descriptor, successful⟩ := succeeded
  have same := (known.unique descriptor).2.2
  subst payload
  simp [Payload.failure] at successful

/-- Every actual source handler derives uncancelled retirement for noticed ancestors.
The cache contains licensed fixed task rejections. Their computations cannot also belong
to the consumed success inventory, which supplies the closure and startup certificates. -/
theorem UncancelledReplayFrame.noticeAncestorRetirements {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : (queue.handleGraphEvent event available).1.NoticeAncestorRetirements work
        (queue.handleGraphEvent event available).2.1 := by
  obtain ⟨_, matching, fresh⟩ := validGraphEvents_last valid
  let current := queue.cacheTaskFailures available
  have parent := frame.parent.cacheTaskFailures available
  have roots := frame.roots.cacheTaskFailures available
  have tasks := frame.tasks.cacheTaskFailures available
  have pending := frame.pending.cacheTaskFailures available
  have owners := frame.owners.cacheTaskFailures available
  have markers := frame.markers.cacheTaskFailures available
  have regions := frame.regions.cacheTaskFailures available
  have rejected := frame.rejected.cacheTaskFailures available licensed
  have rejectedFresh : current.TaskRejectionsSatisfy
      (fun occurrence _ => occurrence ∉ GraphEvent.groupSettlements (before ++ [event])) :=
    rejected.mono (fun _ _ known member =>
      failed_not_succeeded known (valid.groupSettlements_succeed member))
  have availableFresh : ∀ occurrence errors, (occurrence, errors) ∈ available →
      occurrence ∉ GraphEvent.groupSettlements (before ++ [event]) :=
    fun _ _ member settled => failed_not_succeeded (licensed _ _ member)
      (valid.groupSettlements_succeed settled)
  cases event with
  | taskSuccess occurrence result =>
      have taskFresh : occurrence ∉ GraphEvent.groupSettlements before := fun member =>
        fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.groupSettlements_subsetIdentities before member)
      rw [GraphEvent.groupSettlements_append] at rejectedFresh availableFresh
      exact (markers.taskSuccess_certificates owners parent roots tasks pending generated
        canonical occurrence result matching taskFresh rejectedFresh available availableFresh).2
  | streamItems stream items =>
      rw [GraphEvent.groupSettlements_append] at rejectedFresh availableFresh
      exact (markers.streamItems_certificates owners parent roots tasks regions rejectedFresh
        pending.pending generated canonical matching fresh.1
        (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member))
        available availableFresh).2.2
  | taskFailure occurrence errors =>
      apply State.NoticeAncestorRetirements.of_noNotices
      intro output member
      obtain ⟨group, rfl⟩ := current.taskFailure_event_failure occurrence errors output member
      rfl
  | streamSuccess stream =>
      apply State.NoticeAncestorRetirements.of_noNotices
      intro output member
      change output ∈ (current.streamSuccess stream).2 at member
      unfold State.streamSuccess at member
      split at member <;> simp_all [rawGroupNoticeRefs]
  | streamFailure stream errors =>
      apply State.NoticeAncestorRetirements.of_noNotices
      intro output member
      change output ∈ (current.streamFailure stream errors).2 at member
      unfold State.streamFailure at member
      split at member <;> simp_all [rawGroupNoticeRefs]
  | groupFailure notice =>
      apply State.NoticeAncestorRetirements.of_noNotices
      intro output member
      change output ∈ (current.groupFailure notice).2 at member
      unfold State.groupFailure at member
      split at member
      · cases member
      · split at member <;> simp_all [rawGroupNoticeRefs]

/-- Leading stream receipts have already retired their task-bearing ancestors before drain. -/
theorem UncancelledReplayFrame.streamItems_preparedNoticeAncestors
    {queue work parents before stream items}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [.streamItems stream items]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : let current := queue.cacheTaskFailures available
      let prepared :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (current, [], [], [], [])
      prepared.1.NoticeAncestorRetirements work
        [.streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1] := by
  obtain ⟨prior, matching, fresh⟩ := validGraphEvents_last valid
  have rejected := frame.rejected.cacheTaskFailures available licensed
  have rejectedFresh := rejected.mono (fun _ _ known member =>
    failed_not_succeeded known (prior.groupSettlements_succeed member))
  have availableFresh : ∀ occurrence errors, (occurrence, errors) ∈ available →
      occurrence ∉ GraphEvent.groupSettlements before :=
    fun _ _ member settled => failed_not_succeeded (licensed _ _ member)
      (prior.groupSettlements_succeed settled)
  exact ((frame.markers.cacheTaskFailures available).prepareItems_certificates
    (frame.owners.cacheTaskFailures available) (frame.parent.cacheTaskFailures available)
    (frame.roots.cacheTaskFailures available) (frame.tasks.cacheTaskFailures available)
    (frame.regions.cacheTaskFailures available) rejectedFresh
    (frame.pending.cacheTaskFailures available).pending generated canonical matching fresh.1
    (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member))
    available availableFresh).2

/-- Each structural contributor of a noticed ancestor has a consumed successful source.
The actual notice certificate supplies retirement and noncancellation. Complete structural
registration and success-only owner accounting then identify the same source occurrence. -/
theorem UncancelledReplayFrame.noticeAncestor_structuralContributor_succeeded
    {queue work parents before output child dependencies ref address owners producer
      payload}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (emitted : output ∈ (queue.handleGraphEvent event available).2.1)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ result,
        GraphEvent.taskSuccess (.executionGroup address) result ∈ before ++ [event] := by
  have notice := frame.noticeAncestorRetirements generated canonical event valid available licensed
  have retired := notice child.ref (List.mem_flatMap.mpr ⟨output, emitted, noticed⟩)
    child dependencies known rfl ref ancestor (.executionGroup address) owners
    ⟨producer, payload, task⟩ contributes
  have afterSource := frame.handleGraphEvent generated canonical event valid accepted available
    licensed
  obtain ⟨registeredTask, registered, occurrence, groups⟩ :=
    afterSource.retired_structuralContributor_registered generated valid task contributes
      retired.retired retired.uncancelled
  have settled := afterSource.owners.retired_contributor_settled registered
    (groups.symm ▸ contributes) retired.uncancelled retired.retired
  rw [occurrence] at settled
  obtain ⟨source, member, included⟩ := List.mem_flatMap.mp (List.mem_reverse.mp settled)
  cases source with
  | taskSuccess task result =>
      have same : task = .executionGroup address := (List.mem_singleton.mp included).symm
      subst task
      exact ⟨result, member⟩
  | taskFailure | groupFailure | streamItems | streamSuccess | streamFailure =>
      cases included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
