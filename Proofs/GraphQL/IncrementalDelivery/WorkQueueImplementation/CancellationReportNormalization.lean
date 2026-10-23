import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureReportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedStreamRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputAtoms
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Actual normalized batches retain the exact positive reports explaining cancellation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem normalizeBatch_retains_groupFailure (publisher : IncrementalPublisher)
    (events : List WorkQueueEvent) {group errors}
    (emitted : WorkQueueEvent.groupFailure group errors ∈ events)
    : WorkQueueEvent.groupFailure group errors ∈ (publisher.normalizeBatch events).2 := by
  induction events generalizing publisher with
  | nil => cases emitted
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      rcases List.mem_cons.mp emitted with same | later
      · subst event
        exact List.mem_append_left _ List.mem_cons_self
      · exact List.mem_append_right _ (ih _ later)

/-- Normalize a newly appended batch without changing an earlier report inventory.
Witness: old positive reports remain earlier events; every new failed-group control is
copied with its exact descriptor and error count by the actual publisher fold.
-/
theorem State.CancelledRecordsReported.normalizeAppend {queue : State}
    {work before events}
    (reported : queue.CancelledRecordsReported work (before ++ events))
    (publisher : IncrementalPublisher)
    : queue.CancelledRecordsReported work
        (before ++ (publisher.normalizeBatch events).2) := by
  intro node dependencies known cancelled
  obtain ⟨reporter, errors, positive, emitted, ancestry⟩ :=
    reported node dependencies known cancelled
  refine ⟨reporter, errors, positive, ?_, ancestry⟩
  exact (List.mem_append.mp emitted).elim (List.mem_append_left _)
    (fun member => List.mem_append_right _
      (normalizeBatch_retains_groupFailure publisher events member))

/-- Normalization preserves emitted reports and leaves the pending FIFO inventory intact. -/
theorem State.FifoCancelledRecordsReported.normalizeAppend {queue : State}
    {work before events}
    (reported : queue.FifoCancelledRecordsReported work (before ++ events))
    (publisher : IncrementalPublisher)
    : queue.FifoCancelledRecordsReported work
        (before ++ (publisher.normalizeBatch events).2) := by
  intro node dependencies known cancelled
  obtain ⟨reporter, errors, positive, emitted, ancestry⟩ :=
    reported node dependencies known cancelled
  refine ⟨reporter, errors, positive, ?_, ancestry⟩
  rcases List.mem_append.mp emitted with prior | pending
  · rcases List.mem_append.mp prior with old | fresh
    · exact List.mem_append_left _ (List.mem_append_left _ old)
    · exact List.mem_append_left _ (List.mem_append_right _
        (normalizeBatch_retains_groupFailure publisher events fresh))
  · exact List.mem_append_right _ pending

/-- Actual normalized replay retains an emitted or pending completion for each cancellation.
Witness: each real batch exposes its own cache snapshot and retains queued startup
notices until observed dispatch. Joint induction retains reports, exact task positivity and
structural metadata in the actual queue states. No start or output-admission law is used.
-/
theorem State.FifoCancelledRecordsReported.runNormalized {queue : State}
    {work events parents} (reported : queue.FifoCancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (positive : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : (queue.runNormalized batches).1.FifoCancelledRecordsReported work
        (events ++ (queue.runNormalized batches).2.flatten) := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (prior : acc.1.FifoCancelledRecordsReported work (events ++ acc.2.2.flatten))
      (counts : acc.1.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
      (known : acc.1.GroupNodesMatchWork work) (edges : acc.1.ChildLinksCanonical parents)
      (matched : ∀ event ∈ more.flatten, event.MatchesWork work)
      : (more.foldl normalizedStep acc).1.FifoCancelledRecordsReported work
          (events ++ (more.foldl normalizedStep acc).2.2.flatten) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih =>
        have batchMatch : ∀ event ∈ batch, event.MatchesWork work :=
          fun event member => matched event (List.mem_append_left _ member)
        have raw := prior.handleGraphEvents generated counts known edges canonical batch batchMatch
        have normalized := State.FifoCancelledRecordsReported.normalizeAppend raw acc.2.1
        apply ih (normalizedStep acc batch)
        · rw [normalizedStep_queue, normalizedStep_flatten]
          simpa only [List.append_assoc] using normalized
        · rw [normalizedStep_queue]
          exact counts.handleGraphEvents batch (fun occurrence errors member =>
            generated.matchedTaskFailure_positive (batchMatch _ member))
        · rw [normalizedStep_queue]
          exact known.handleGraphEvents batch batchMatch
        · rw [normalizedStep_queue]
          exact edges.handleGraphEvents batch batchMatch canonical
        · exact fun event member => matched event (List.mem_append_right _ member)
  exact loop batches
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, [])
    (by simpa only [List.flatten_nil, List.append_nil] using reported) positive records
    links matching

/-- Atomic expansion and removal of the terminal constructor preserve every group report.
Witness: each group-failure event remains a singleton atom and passes the terminal filter.
Neither its positive count nor its same-or-ancestor attachment is changed.
-/
theorem State.CancelledRecordsReported.publicationAtoms_withoutTermination
    {queue : State} {work events} (reported : queue.CancelledRecordsReported work events)
    : queue.CancelledRecordsReported work
        ((events.flatMap publicationAtoms).filter
          (fun
            | .workQueueTermination => false
            | _ => true)) := by
  intro node dependencies known cancelled
  obtain ⟨reporter, errors, positive, emitted, ancestry⟩ :=
    reported node dependencies known cancelled
  refine ⟨reporter, errors, positive, List.mem_filter.mpr ⟨?_, rfl⟩, ancestry⟩
  exact List.mem_flatMap.mpr ⟨.groupFailure reporter errors, emitted, List.mem_cons_self⟩

/-- Generated source matching supplies cancellation reports in actual normalized output.
Witness: initialization has no cancellation markers or task rejections; canonical source
records supply the joint actual-batch induction. No flatten-only state bridge is used.
-/
theorem ExecutedWork.runNormalized_cancellationReports {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.terminated
        = true)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.runNormalized batches).1.CancelledRecordsReported work
        (queue.runNormalized batches).2.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial : (State.initialize (Work.fromExecution work)).FifoCancelledRecordsReported work [] :=
    createWorkQueue_cancelledRecordsReported (Work.fromExecution work) work _
  have reported := initial.runNormalized generated
    (createWorkQueue_taskRejections _ _)
    (createWorkQueue_groupNodesMatchWork work)
    (createWorkQueue_childLinksCanonical _ parents
      (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)) canonical batches matching
  simpa only [List.nil_append] using reported.completed
    (createWorkQueue_terminalPending (Work.fromExecution work) batches ended)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
