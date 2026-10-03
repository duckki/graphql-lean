import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures

/-! Causal support for cancellation refs written by executable graph-event handlers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful transitions retain support; failure removal requires a real cause
-----------------------------------------------------------------------------------------

/-- Task cleanup preserves the cancellation registry and its causal witnesses.
Witness: removing task nodes and memberships changes no retained cancellation ref. -/
theorem State.CancelledRecordsSupported.removeTask {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (task : Occurrence)
    : (queue.removeTask task).CancelledRecordsSupported work failed :=
  supported

/-- Activation retains cancellation support exactly.
Witness: the unchanged-history equation for starting released work. -/
theorem State.CancelledRecordsSupported.startNewWork {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (newWork : NewWork)
    : (queue.startNewWork newWork).CancelledRecordsSupported work failed := by
  intro ref member
  rw [State.startNewWork_cancelledGroups] at member
  exact supported ref member

/-- Successful closure cannot introduce an unsupported cancellation.
Witness: successful flushing and pruning preserve the exact cancellation list. -/
theorem State.CancelledRecordsSupported.finishGroupSuccess {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (node : GroupNode)
    : (queue.finishGroupSuccess node).1.CancelledRecordsSupported work failed := by
  intro ref member
  rw [State.finishGroupSuccess_cancelledGroups] at member
  exact supported ref member

/-- Facts threaded through release draining, all internal to the executable queue.
No output-history admission or response-correctness condition is included. -/
private def State.CancellationContext (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (failed : List Occurrence)
    : Prop :=
  queue.CancelledRecordsSupported work failed
  ∧ queue.CachedFailuresSupported work failed
  ∧ queue.GroupNodesMatchWork work
  ∧ queue.ChildLinksCanonical parents

/-- Success preserves the four facts needed by subsequent release-time failures.
Witness: unchanged cancellation refs plus existing cache and metadata preservation. -/
private theorem State.CancellationContext.finishGroupSuccess {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed) (node : GroupNode)
    : (queue.finishGroupSuccess node).1.CancellationContext work parents failed :=
  ⟨
    valid.1.finishGroupSuccess node,
    valid.2.1.finishGroupSuccess node,
    valid.2.2.1.finishGroupSuccess node,
    valid.2.2.2.finishGroupSuccess node
  ⟩

/-- Activation does not alter cancellation evidence, failure caches, or causal metadata.
Witness: compose the corresponding four activation-preservation theorems. -/
private theorem State.CancellationContext.startNewWork {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed) (newWork : NewWork)
    : (queue.startNewWork newWork).CancellationContext work parents failed :=
  ⟨
    valid.1.startNewWork newWork,
    valid.2.1.startNewWork newWork,
    valid.2.2.1.startNewWork newWork,
    valid.2.2.2.startNewWork newWork
  ⟩

/-- Draining settled groups records only cancellations justified by prior failures.
Witness: a selected failure cache supplies its root's invalidation; canonical child links
justify descendant removal. Successful closures and activation retain support. -/
theorem State.CancelledRecordsSupported.drainReadyGroups {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : queue.drainReadyGroups.1.CancelledRecordsSupported work failed := by
  have drained := State.drainReadyGroups_preserves
    (fun current => current.CancellationContext work parents failed)
    (fun _ node prior _ _ _ _ => (prior.finishGroupSuccess node).startNewWork _)
    (fun current node errors prior member _ failure =>
      show (current.finishGroupFailure node errors).1.CancellationContext
          work parents failed from
        ⟨prior.1.removeGroup prior.2.2.2 prior.2.2.1 canonical node.group.node.ref
          (prior.2.1.invalidated member (by simp [failure])).toRecordInvalidated,
         prior.2.1.removeGroup node.group.node.ref,
         prior.2.2.1.removeGroup node.group.node.ref,
         prior.2.2.2.removeGroup node.group.node.ref⟩)
    (show queue.CancellationContext work parents failed from
      ⟨supported, cached, matching, links⟩)
  exact drained.1

-----------------------------------------------------------------------------------------
-- A task failure justifies cancellation of all owners visited by its handler
-----------------------------------------------------------------------------------------

/-- Failed-task handling preserves support using the actual started task's contributors.
Witness: task provenance licenses each removed owner; canonical edges license descendants.
Ignored or missing tasks retain the old registry without using the recorded-failure premise.
-/
theorem State.CancelledRecordsSupported.taskFailure {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    (recorded
      : ∀ node,
          queue.taskNode? occurrence = some node
          → queue.taskHasHealthyOwner node.task = true
          → occurrence ∈ failed)
    : (queue.taskFailure occurrence errors).1.CancelledRecordsSupported work failed := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    let (current, outputs) := acc
    match current.groupNode? group.ref with
    | none => (current, outputs)
    | some node =>
        if current.rootGroups.contains group.ref then
          let (next, failure) := current.finishGroupFailure node errors
          (next, outputs ++ [failure])
        else (current.putGroupNode
          { node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors) }, outputs)
  unfold State.taskFailure
  split
  · exact supported
  · rename_i taskNode found
    split
    · exact supported.removeTask occurrence
    · rename_i accepted
      have healthy : queue.taskHasHealthyOwner taskNode.task = true := by
        simpa using accepted
      have member := List.mem_of_find?_eq_some found
      have same : taskNode.task.occurrence = occurrence :=
        (occurrence_beq_iff_eq _ _).mp
          (List.find?_some (p := fun node : TaskNode => node.task.occurrence == occurrence) found)
      obtain ⟨address, payload, producer, _, known⟩ :=
        (tasksMatch taskNode.task (registered taskNode member)).1
      have owners : TaskHasOwners work occurrence
          (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
        ⟨producer, payload, same ▸ known⟩
      let invariant (current : State) := current.CancelledRecordsSupported work failed
        ∧ current.GroupNodesMatchWork work ∧ current.ChildLinksCanonical parents
      have fold (groups : List Execution.DeliveryNode)
          (included : groups.Subset taskNode.task.groups)
          (acc : State × List WorkQueueEvent) (valid : invariant acc.1)
          : invariant (groups.foldl step acc).1 := by
        induction groups generalizing acc with
        | nil => exact valid
        | cons group rest ih =>
            apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
            obtain ⟨current, outputs⟩ := acc
            dsimp only [step]
            split
            · exact valid
            · rename_i node located
              have nodeMember := List.mem_of_find?_eq_some located
              split
              · have invalid : GroupRecordInvalidated work failed node.group.node.ref := by
                  rw [current.groupNode?_ref located]
                  exact .task owners
                    (List.mem_map.mpr ⟨group, included List.mem_cons_self, rfl⟩)
                    (recorded taskNode found healthy)
                exact ⟨valid.1.removeGroup valid.2.2 valid.2.1 canonical _ invalid,
                  valid.2.1.removeGroup _, valid.2.2.removeGroup _⟩
              · exact ⟨valid.1, valid.2.1.putGroupNode _ (valid.2.1 node nodeMember),
                  valid.2.2.putGroupNode _ (valid.2.2 node nodeMember)⟩
      exact (fold taskNode.task.groups (List.Subset.refl _)
        (queue.removeTask occurrence, [])
        ⟨supported.removeTask occurrence, matching.removeTask occurrence,
          links.removeTask occurrence⟩).1

-----------------------------------------------------------------------------------------
-- Successful producers integrate child work before releasing retained outcomes
-----------------------------------------------------------------------------------------

/-- Matched child integration preserves cancellation causes and release metadata.
Witness: registration propagates real parent invalidation; other integration stages
retain cancellation history, caches, and fixed-work descriptors. -/
private theorem State.CancellationContext.maybeIntegrateWork {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed) (newWork : Work)
    (parentTask : Option Occurrence)
    (descriptors
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.maybeIntegrateWork newWork parentTask).1.CancellationContext
        work parents failed := by
  refine ⟨valid.1.maybeIntegrateWork newWork parentTask descriptors,
    valid.2.1.maybeIntegrateWork newWork parentTask,
    valid.2.2.1.maybeIntegrateWork newWork ?_ parentTask,
    valid.2.2.2.maybeIntegrateWork newWork ?_ parentTask⟩
  · intro group member
    obtain ⟨dependencies, known, _⟩ := descriptors group member
    exact ⟨dependencies, known⟩
  · intro group member
    obtain ⟨dependencies, known, parent⟩ := descriptors group member
    rw [parent, canonical group.node dependencies known]

/-- Empty-shell promotion preserves the facts needed by later failure draining.
Witness: pruning preserves cancellation history and only filters existing metadata. -/
private theorem State.CancellationContext.pruneEmptyGroups {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.CancellationContext work parents failed := by
  refine ⟨?_, valid.2.1.pruneEmptyGroups groups, valid.2.2.1.pruneEmptyGroups groups,
    valid.2.2.2.pruneEmptyGroups groups⟩
  intro ref member
  rw [State.pruneEmptyGroups_cancelledGroups] at member
  exact valid.1 ref member

/-- Successful settlement preserves support even when it releases an older cached failure.
Witness: child registration and the single-pass success loop preserve the local facts;
the final drain attributes newly cancelled groups to their retained failure causes. -/
theorem State.CancelledRecordsSupported.taskSuccess {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (result : TaskResult)
    (descriptors
      : ∀ group ∈ result.work.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    : (queue.taskSuccess occurrence result).1.CancelledRecordsSupported work failed := by
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (valid : acc.1.CancellationContext work parents failed)
      : (successGroupStep acc group).1.CancellationContext work parents failed := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact valid
    · rename_i node found
      have member := List.mem_of_find?_eq_some found
      have updated : State.CancellationContext
          (current.putGroupNode { node with pending := node.pending - 1 }) work parents failed :=
        ⟨valid.1, valid.2.1.putGroupNode _ (valid.2.1 node member),
          valid.2.2.1.putGroupNode _ (valid.2.2.1 node member),
          valid.2.2.2.putGroupNode _ (valid.2.2.2 node member)⟩
      split
      · exact updated.finishGroupSuccess _
      · exact updated
  have fold (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (valid : acc.1.CancellationContext work parents failed)
      : (groups.foldl successGroupStep acc).1.CancellationContext work parents
          failed := by
    induction groups generalizing acc with
    | nil => exact valid
    | cons group rest ih => exact ih _ (step acc group valid)
  unfold State.taskSuccess
  split
  · exact supported
  · rename_i taskNode found
    split
    · exact supported.removeTask occurrence
    · let withValue := queue.putTaskNode { taskNode with value := some result.value }
      have before : withValue.CancellationContext work parents failed :=
        ⟨supported, cached, matching, links⟩
      have integrated := before.maybeIntegrateWork result.work (some occurrence)
        descriptors canonical
      have released := fold taskNode.task.groups
        ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {}) integrated
      have started := released.startNewWork
        (taskNode.task.groups.foldl successGroupStep
          ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {})).2.2
      exact started.1.drainReadyGroups started.2.1 started.2.2.1 started.2.2.2 canonical

/-- Item batches preserve support through integration, activation, and retained failures.
Witness: each matched child chunk preserves the same context before the final drain. -/
theorem State.CancelledRecordsSupported.streamItems {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
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
    : (queue.streamItems stream items).1.CancelledRecordsSupported work failed := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    (pruned.startNewWork { more with newGroups := nonempty }, groups ++ nonempty,
      streams ++ more.newStreams, values ++ [item.value])
  have fold (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue) (valid : acc.1.CancellationContext work parents failed)
      : (more.foldl step acc).1.CancellationContext work parents failed := by
    induction more generalizing acc with
    | nil => exact valid
    | cons item rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        have integrated := valid.maybeIntegrateWork item.work none
          (descriptors item (included List.mem_cons_self)) canonical
        exact (integrated.pruneEmptyGroups _).startNewWork _
  unfold State.streamItems
  split
  · exact supported
  · have final := fold items (List.Subset.refl _) (queue, [], [], [])
      ⟨supported, cached, matching, links⟩
    exact final.1.drainReadyGroups final.2.1 final.2.2.1 final.2.2.2 canonical

-----------------------------------------------------------------------------------------
-- The source's structural matching discharges child-registration metadata
-----------------------------------------------------------------------------------------

/-- Every matched host event preserves cancellation support when accepted failures are known.
Witness: source matching supplies child descriptors; each task/stream handler then applies
its local preservation theorem. This assumes no admitted output history. -/
theorem State.CancelledRecordsSupported.handleGraphEvent {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (source : event.MatchesWork work)
    (recorded
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → ∀ node,
              queue.taskNode? occurrence = some node
              → queue.taskHasHealthyOwner node.task = true
              → occurrence ∈ failed)
    : (queue.handleGraphEvent event).1.CancelledRecordsSupported work failed := by
  cases event with
  | taskSuccess occurrence result =>
      apply supported.taskSuccess cached matching links canonical occurrence result
      intro group member
      obtain ⟨dependencies, known⟩ := source.taskChildGroups_recordAt member
      refine ⟨dependencies, known, ?_⟩
      rw [canonical group.node dependencies known]
      exact source.taskChildGroups_parentCanonical canonical member
  | taskFailure occurrence errors =>
      exact supported.taskFailure registered tasksMatch matching links canonical occurrence
        errors (recorded occurrence errors rfl)
  | streamItems stream items =>
      apply supported.streamItems cached matching links canonical stream items
      intro item itemMember group member
      obtain ⟨dependencies, known⟩ :=
        source.streamItem_childGroups_recordAt itemMember member
      refine ⟨dependencies, known, ?_⟩
      rw [canonical group.node dependencies known]
      exact source.streamItem_childGroups_parentCanonical canonical itemMember member
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.CancelledRecordsSupported work failed
      unfold State.streamSuccess
      split <;> exact supported
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.CancelledRecordsSupported work failed
      unfold State.streamFailure
      split <;> exact supported

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
