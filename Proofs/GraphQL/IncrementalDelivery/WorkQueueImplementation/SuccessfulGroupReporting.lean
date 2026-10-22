import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancelledGroupReportingHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Successful inputs preserve prior reports and can release new cached-failure reports. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Output-aware bookkeeping before the final failure drain
-----------------------------------------------------------------------------------------

/-- Internal facts needed to attribute later release-time cleanup to actual output.
The accumulated `events` are executable outputs, not an assumed admitted history.
-/
private def State.ReportingContext (queue : State) (work : Execution.Work)
    (parents : NodeRef → NodeRefs) (events : List WorkQueueEvent)
    : Prop :=
  queue.CancelledRecordsReported work events
  ∧ queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors)
  ∧ queue.GroupNodesMatchWork work
  ∧ queue.ChildLinksCanonical parents

/-- Activation adds the queued controls that explain its new cancellation markers.
Witness: the startup-reporting theorem threads task-local positivity and structural
metadata, and all other context fields survive the actual group removal.
-/
private theorem State.ReportingContext.startNewWork {queue : State} {work parents events}
    (valid : queue.ReportingContext work parents events) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (released : NewWork) (available : List (Occurrence × Nat))
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors)
    : (queue.startNewWork released available).1.ReportingContext work parents
        (events
          ++ (queue.startNewWork released available).2.map
              (fun failure => .groupFailure failure.group failure.errors)) :=
  ⟨
    valid.1.startNewWork generated valid.2.2.1 valid.2.2.2 canonical valid.2.1
      released available licensed,
    valid.2.1.startNewWork released available licensed,
    valid.2.2.1.startNewWork released available,
    valid.2.2.2.startNewWork released available
  ⟩

/-- Successful closure appends its actual outputs without losing earlier failure reports.
Witness: successful retirement introduces no cancellation markers or failure caches.
-/
private theorem State.ReportingContext.finishGroupSuccess {queue : State}
    {work parents events} (valid : queue.ReportingContext work parents events)
    (node : GroupNode)
    : (queue.finishGroupSuccess node).1.ReportingContext work parents
        (events ++ (queue.finishGroupSuccess node).2.1) :=
  ⟨
    valid.1.finishGroupSuccess _,
    valid.2.1.finishGroupSuccess _,
    valid.2.2.1.finishGroupSuccess _,
    valid.2.2.2.finishGroupSuccess _
  ⟩

/-- Generated child registration retains report origins and canonical group metadata.
Witness: refused children inherit their parent's report; all other integration stages
preserve the cancellation registry and positive caches.
-/
private theorem State.ReportingContext.maybeIntegrateWork {queue : State}
    {work parents events} (valid : queue.ReportingContext work parents events)
    (generated : ExecutedWork work) (newWork : Work) (producer : Option Occurrence)
    (descriptors
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.maybeIntegrateWork newWork producer).1.ReportingContext work parents
        events := by
  refine ⟨valid.1.maybeIntegrateWork generated newWork producer descriptors,
    valid.2.1.maybeIntegrateWork newWork producer,
    valid.2.2.1.maybeIntegrateWork newWork ?_ producer,
    valid.2.2.2.maybeIntegrateWork newWork ?_ producer⟩
  · intro group member
    obtain ⟨dependencies, known, _⟩ := descriptors group member
    exact ⟨dependencies, known⟩
  · intro group member
    obtain ⟨dependencies, known, parent⟩ := descriptors group member
    rw [parent, canonical group.node dependencies known]

/-- Empty-shell promotion introduces no cancellation markers or unproved cache counts.
Witness: pruning only filters retained nodes and preserves the cancellation registry.
-/
private theorem State.ReportingContext.pruneEmptyGroups {queue : State}
    {work parents events} (valid : queue.ReportingContext work parents events)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ReportingContext work parents events := by
  refine ⟨?_, valid.2.1.pruneEmptyGroups _, valid.2.2.1.pruneEmptyGroups _,
    valid.2.2.2.pruneEmptyGroups _⟩
  intro node dependencies known member
  rw [State.pruneEmptyGroups_cancelledGroups] at member
  exact valid.1 node dependencies known member

-----------------------------------------------------------------------------------------
-- Success settlement and item arrival retain actual report origins
-----------------------------------------------------------------------------------------

/-- Successful task settlement retains old reports and attributes its final cleanup.
Witness: thread the actual success-fold outputs through integration and activation, then
use output-aware draining to report any newly released positive failure cache.
-/
theorem State.CancelledRecordsReported.taskSuccess {queue : State} {work events parents}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (result : TaskResult)
    (descriptors
      : ∀ group ∈ result.work.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (queue.taskSuccess occurrence result available).1.CancelledRecordsReported work
        (events
          ++ (queue.taskSuccess occurrence result available).2.1
          ++ (queue.taskSuccess occurrence result available).2.2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
  let invariant (acc : State × List WorkQueueEvent × NewWork) :=
    acc.1.ReportingContext work parents (events ++ acc.2.1)
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (valid : invariant acc) : invariant (successGroupStep acc group) := by
    obtain ⟨current, outputs, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact valid
    · rename_i node found
      have member := List.mem_of_find?_eq_some found
      have updated : State.ReportingContext
          (current.putGroupNode { node with pending := node.pending - 1 }) work parents
          (events ++ outputs) :=
        ⟨valid.1.putGroupNode _, valid.2.1.putGroupNode _,
          valid.2.2.1.putGroupNode _ (valid.2.2.1 node member),
          valid.2.2.2.putGroupNode _ (valid.2.2.2 node member)⟩
      split
      · simpa only [List.append_assoc] using updated.finishGroupSuccess _
      · exact updated
  have fold (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork) (valid : invariant acc)
      : invariant (groups.foldl successGroupStep acc) := by
    induction groups generalizing acc with
    | nil => exact valid
    | cons group rest ih => exact ih _ (step acc group valid)
  unfold State.taskSuccess
  split
  · simpa only [List.map_nil, List.append_nil] using reported
  · rename_i taskNode found
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have before : withValue.ReportingContext work parents events :=
      ⟨reported, cached.putTaskNode _
        (cached taskNode (List.mem_of_find?_eq_some found)), records, links⟩
    have integrated := before.maybeIntegrateWork generated result.work (some occurrence)
      descriptors canonical
    have released := fold taskNode.task.groups
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {})
      (by simpa only [invariant, List.append_nil] using integrated)
    let folded := taskNode.task.groups.foldl successGroupStep
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {})
    let startedState := folded.1.startNewWork folded.2.2 available
    let drainedState := startedState.1.drainReadyGroups available
    have started := released.startNewWork generated canonical folded.2.2 available licensed
    have drained := started.1.drainReadyGroups generated started.2.2.1 started.2.2.2
      canonical started.2.1 available licensed
    apply drained.mono
    have permutation := List.Perm.append_left (events ++ folded.2.1)
      (List.perm_append_comm_assoc
      (startedState.2.map (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors))
      drainedState.2.1
      (drainedState.2.2.map
        (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors)))
    intro event member
    simp only [List.map_append, List.append_assoc] at member ⊢
    have arranged := permutation
    simp only [List.append_assoc] at arranged
    exact arranged.subset member

/-- Stream item integration preserves reports through child activation and final draining.
Witness: child integration introduces no reports or caches; the actual item carrier is
appended before the output-aware drain, which attributes any newly released failure.
-/
theorem State.CancelledRecordsReported.streamItems {queue : State} {work events parents}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (descriptors
      : ∀ item ∈ items,
        ∀ group ∈ item.work.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (available : List (Occurrence × Nat) := [])
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors := by
      intro occurrence errors member; cases member)
    : (queue.streamItems stream items available).1.CancelledRecordsReported work
        (events
          ++ (queue.streamItems stream items available).2.1
          ++ (queue.streamItems stream items available).2.2.map
              (fun failure => .groupFailure failure.group failure.errors)) := by
  let step := fun acc item => streamItemStep acc item available
  have fold (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue × List GroupFailureEvent)
      (valid : acc.1.ReportingContext work parents
        (events ++ acc.2.2.2.2.map (fun failure => .groupFailure failure.group failure.errors)))
      : (more.foldl step acc).1.ReportingContext work parents
          (events ++ (more.foldl step acc).2.2.2.2.map
            (fun failure => .groupFailure failure.group failure.errors)) := by
    induction more generalizing acc with
    | nil => exact valid
    | cons item rest ih =>
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released : NewWork := { integrated.2 with newGroups := pruned.2 }
        have adopted := valid.maybeIntegrateWork generated item.work none
          (descriptors item (included List.mem_cons_self)) canonical
        have prepared := adopted.pruneEmptyGroups integrated.2.newGroups
        have started := prepared.startNewWork generated canonical released available licensed
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) (step acc item)
        simpa only [step, streamItemStep, integrated, pruned, released,
          List.map_append, List.append_assoc] using started
  rw [queue.streamItems_eq stream items available]
  split
  · simpa only [List.map_nil, List.append_nil] using reported
  · let prepared := items.foldl step (queue, [], [], [], [])
    let carrier : WorkQueueEvent :=
      .streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1
    let drained := prepared.1.drainReadyGroups available
    have final :=
      fold items (List.Subset.refl _) (queue, [], [], [], [])
        (by
          simpa only [List.map_nil, List.append_nil]
            using (show queue.ReportingContext work parents events from ⟨
                    reported,
                    cached,
                    records,
                    links
                  ⟩))
    have reporting := (final.1.append [carrier]).drainReadyGroups generated
      final.2.2.1 final.2.2.2 canonical final.2.1 available licensed
    apply reporting.mono
    have permutation := List.Perm.append_left events
      (List.perm_append_comm_assoc
      (prepared.2.2.2.2.map (fun failure => WorkQueueEvent.groupFailure
        failure.group failure.errors)) ([carrier] ++ drained.2.1)
      (drained.2.2.map (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors)))
    intro event member
    simp only [List.map_append, List.singleton_append, List.append_assoc] at member ⊢
    have arranged := permutation
    simp only [List.singleton_append] at arranged
    exact arranged.subset member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
