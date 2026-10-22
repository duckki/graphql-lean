import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancelledGroupReportingHandlers

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
  ∧ queue.CachedErrorsSatisfy (fun _ errors => 0 < errors)
  ∧ queue.GroupNodesMatchWork work
  ∧ queue.ChildLinksCanonical parents

/-- Activation changes none of the four report-attribution facts.
Witness: cancellation markers, caches, and group metadata are retained exactly.
-/
private theorem State.ReportingContext.startNewWork {queue : State} {work parents events}
    (valid : queue.ReportingContext work parents events) (released : NewWork)
    : (queue.startNewWork released).ReportingContext work parents events :=
  ⟨
    valid.1.startNewWork _,
    valid.2.1.startNewWork _,
    valid.2.2.1.startNewWork _,
    valid.2.2.2.startNewWork _
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
    (cached : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
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
    : (queue.taskSuccess occurrence result).1.CancelledRecordsReported work
        (events ++ (queue.taskSuccess occurrence result).2) := by
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
  · simpa only [List.append_nil] using reported
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
    have started := released.startNewWork
      (taskNode.task.groups.foldl successGroupStep
        ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {})).2.2
    have drained := started.1.drainReadyGroups generated started.2.2.1 started.2.2.2
      canonical started.2.1
    rw [List.append_assoc] at drained
    exact drained

/-- Stream item integration preserves reports through child activation and final draining.
Witness: child integration introduces no reports or caches; the actual item carrier is
appended before the output-aware drain, which attributes any newly released failure.
-/
theorem State.CancelledRecordsReported.streamItems {queue : State} {work events parents}
    (reported : queue.CancelledRecordsReported work events)
    (generated : ExecutedWork work)
    (cached : queue.CachedErrorsSatisfy (fun _ errors => 0 < errors))
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
    : (queue.streamItems stream items).1.CancelledRecordsReported work
        (events ++ (queue.streamItems stream items).2) := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have fold (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue) (valid : acc.1.ReportingContext work parents events)
      : (more.foldl step acc).1.ReportingContext work parents events := by
    induction more generalizing acc with
    | nil => exact valid
    | cons item rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        have integrated := valid.maybeIntegrateWork generated item.work none
          (descriptors item (included List.mem_cons_self)) canonical
        exact (integrated.pruneEmptyGroups _).startNewWork _
  unfold State.streamItems
  split
  · simpa only [List.append_nil] using reported
  · have final := fold items (List.Subset.refl _) (queue, [], [], [])
      ⟨reported, cached, records, links⟩
    simpa only [List.append_assoc, List.singleton_append]
      using (final.1.append
              [.streamValues stream (items.foldl step (queue, [], [], [])).2.2.2
                (items.foldl step (queue, [], [], [])).2.1
                (items.foldl step (queue, [], [], [])).2.2.1]).drainReadyGroups
        generated final.2.2.1 final.2.2.2 canonical final.2.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
