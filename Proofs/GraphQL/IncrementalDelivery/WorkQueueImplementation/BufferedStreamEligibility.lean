import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRootFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebtBound
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Buffered item callbacks retain their stream root until source-ordered completion. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Activation preserves every earlier stream root, whether or not new descriptors exist. -/
theorem State.startNewWork_rootStreams_mono (queue : State) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : queue.rootStreams.Subset (queue.startNewWork released available).1.rootStreams := by
  have one (current : State) (ref : NodeRef)
      : current.rootStreams.Subset (current.startStream ref).rootStreams := by
    unfold State.startStream
    split
    · exact List.Subset.refl _
    · exact List.subset_append_left _ _
  have loop (refs : NodeRefs) (current : State)
      : current.rootStreams.Subset
          (refs.foldl State.startStream current).rootStreams := by
    induction refs generalizing current with
    | nil => exact List.Subset.refl _
    | cons ref rest ih => exact (one current ref).trans (ih _)
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have groups : ∀ acc ref, (step acc ref).1.rootStreams = acc.1.rootStreams := by
    intro acc ref
    exact acc.1.startGroup_rootStreams ref available
  unfold State.startNewWork
  have covered := loop (released.newStreams.map Execution.DeliveryNode.ref)
    (((released.newGroups.map Execution.DeliveryNode.ref).foldl step
      ({ queue with rootGroups := queue.rootGroups ++
        released.newGroups.map Execution.DeliveryNode.ref }, [])).1)
  rw [fold_projection (fun acc : State × List GroupFailureEvent => acc.1.rootStreams)
    step groups] at covered
  exact covered

/-- Successful draining cannot remove an active stream. -/
theorem State.drainReadyGroups_rootStreams_mono (queue : State)
    (available : List (Occurrence × Nat) := [])
    : queue.rootStreams.Subset (queue.drainReadyGroups available).1.rootStreams := by
  have loop (fuel : Nat) (current : State)
      : current.rootStreams.Subset
          (State.drainReadyGroups.go available fuel current).1.rootStreams := by
    induction fuel generalizing current with
    | zero => exact List.Subset.refl _
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact List.Subset.refl _
        · rename_i node selected
          have activated := (current.finishGroupSuccess node).1.startNewWork_rootStreams_mono
            (current.finishGroupSuccess node).2.2 available
          rw [State.finishGroupSuccess_rootStreams] at activated
          exact activated.trans (ih _)
  exact loop _ queue

/-- Successful task processing integrates and activates streams without closing any. -/
theorem State.taskSuccess_rootStreams_mono (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : queue.rootStreams.Subset
        (queue.taskSuccess occurrence result available).1.rootStreams := by
  have step (acc : State × List Execution.WorkQueueEvent × NewWork)
      (group : Execution.DeliveryNode)
      : (successGroupStep acc group).1.rootStreams = acc.1.rootStreams := by
    unfold successGroupStep
    dsimp only
    split
    · rfl
    · split
      · exact State.finishGroupSuccess_rootStreams _ _
      · rfl
  cases found : queue.taskNode? occurrence with
  | none =>
      intro ref active
      simpa only [State.taskSuccess, found] using active
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      intro ref active
      apply State.drainReadyGroups_rootStreams_mono _ available
      let integrated := ((queue.putTaskNode { node with value := some result.value
        }).maybeIntegrateWork result.work (some occurrence)).1
      let released := node.task.groups.foldl successGroupStep (integrated, [], {})
      have covered := released.1.startNewWork_rootStreams_mono released.2.2 available
      rw [fold_projection (fun acc : State × List Execution.WorkQueueEvent × NewWork =>
        acc.1.rootStreams) successGroupStep step] at covered
      apply covered
      simpa only [integrated, State.maybeIntegrateWork_rootStreams, State.putTaskNode] using active

/-- Item integration and its final drain preserve earlier active streams. -/
theorem State.streamItems_rootStreams_mono (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : queue.rootStreams.Subset
        (queue.streamItems stream items available).1.rootStreams := by
  have one (current : State) (item : StreamItem)
      : current.rootStreams.Subset (current.integrateStreamItem item available).rootStreams := by
    let integrated := current.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    have next := pruned.1.startNewWork_rootStreams_mono
      { integrated.2 with newGroups := pruned.2 } available
    simpa only [State.integrateStreamItem, pruned, integrated,
      State.pruneEmptyGroups_rootStreams, State.maybeIntegrateWork_rootStreams] using next
  have loop (remaining : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List Execution.StreamItemValue × List GroupFailureEvent)
      : acc.1.rootStreams.Subset
          (remaining.foldl (fun acc item => streamItemStep acc item available)
            acc).1.rootStreams := by
    induction remaining generalizing acc with
    | nil => exact List.Subset.refl _
    | cons item rest ih =>
        rw [List.foldl_cons]
        exact (one acc.1 item).trans (ih (streamItemStep acc item available))
  rw [queue.streamItems_eq stream items available]
  split
  · exact List.Subset.refl _
  · exact (loop items (queue, [], [], [], [])).trans
      (State.drainReadyGroups_rootStreams_mono _ available)

/-- Only a stream's own completion can remove its active root. Group cleanup and child
activation preserve every earlier stream root, including under cached task failures.
-/
theorem State.handleGraphEvent_retains_unclosed_stream (queue : State)
    (event : GraphEvent) (ref : NodeRef) (active : ref ∈ queue.rootStreams)
    (unclosed : ref ∉ event.identities.2) (available : List (Occurrence × Nat) := [])
    : ref ∈ (queue.handleGraphEvent event available).1.rootStreams := by
  let current := queue.cacheTaskFailures available
  have roots : current.rootStreams = queue.rootStreams := by
    have frame := congrArg State.rootStreams (queue.cacheTaskFailures_frame available)
    exact frame
  have currentActive : ref ∈ current.rootStreams := roots ▸ active
  cases event with
  | taskSuccess occurrence result =>
      exact current.taskSuccess_rootStreams_mono occurrence result available currentActive
  | groupFailure failure =>
      change ref ∈ (current.groupFailure failure).1.rootStreams
      unfold State.groupFailure
      split
      · exact currentActive
      · split <;> exact currentActive
  | taskFailure occurrence errors =>
      change ref ∈ (current.taskFailure occurrence errors).1.rootStreams
      cases found : current.taskNode? occurrence with
      | none => simpa only [State.taskFailure, found] using currentActive
      | some node =>
          rw [current.taskFailure_eq occurrence errors node found]
          have roots := failureGroupFold_preserves
            (fun next => next.rootStreams = current.rootStreams)
            (fun _ _ prior => prior) errors node.task.groups
              (current.putTaskNode { node with rejection := some errors }, []) rfl
          exact roots ▸ currentActive
  | streamItems stream items =>
      exact current.streamItems_rootStreams_mono stream items available currentActive
  | streamSuccess stream =>
      have different : ref ≠ stream.ref := by simpa [GraphEvent.identities] using unclosed
      change ref ∈ (current.streamSuccess stream).1.rootStreams
      simp only [State.streamSuccess]
      split
      · exact List.mem_filter.mpr ⟨currentActive, by simpa using different⟩
      · exact currentActive
  | streamFailure stream errors =>
      have different : ref ≠ stream.ref := by simpa [GraphEvent.identities] using unclosed
      change ref ∈ (current.streamFailure stream errors).1.rootStreams
      simp only [State.streamFailure]
      split
      · exact List.mem_filter.mpr ⟨currentActive, by simpa using different⟩
      · exact currentActive

/-- A batch-entry stream root remains live through every preceding nonclosing input. -/
theorem State.replayGraphEvents_retains_unclosed_stream (queue : State)
    (events : List GraphEvent) (ref : NodeRef) (active : ref ∈ queue.rootStreams)
    (unclosed : ref ∉ events.flatMap (fun event => event.identities.2))
    (available : List (Occurrence × Nat) := [])
    : ref ∈ (queue.replayGraphEvents events available).rootStreams := by
  induction events generalizing queue with
  | nil => exact active
  | cons event rest ih =>
      apply ih
      · exact queue.handleGraphEvent_retains_unclosed_stream event ref active
          (fun member => unclosed (List.mem_append_left _ member)) available
      · exact fun member => unclosed (List.mem_append_right _ member)

/-- Source readiness at a selected event cut retains the original preceding history. -/
theorem ValidGraphEvents.last_ready {work : Execution.Work} {before : List GraphEvent}
    {event : GraphEvent} (valid : ValidGraphEvents work (before ++ [event]))
    : event.Ready work before := by
  generalize same : before ++ [event] = events at valid
  cases valid with
  | nil => simp at same
  | @append earlier last prior matching fresh ready =>
      obtain ⟨sameBefore, sameLast⟩ := List.append_inj' same (by simp)
      have equal : event = last := by simpa using sameLast
      subst earlier
      subst last
      exact ready

/-- An item callback admitted from batch entry remains executable at its FIFO cut.
Source readiness excludes an earlier completion of that stream. This uses the existing
source-order law, while allowing task callbacks to become stale during the same batch.
-/
theorem State.acceptsBatch_streamItems_live {queue : State} {work : Execution.Work}
    {before batch fifo : List GraphEvent} {stream : Execution.DeliveryNode}
    {items : List StreamItem} (valid : ValidGraphEvents work (before ++ batch))
    (accepted : queue.acceptsBatch batch = true)
    (earlier : (fifo ++ [GraphEvent.streamItems stream items]).IsPrefix batch)
    : (queue.replayGraphEvents fifo
        (GraphEvent.availableFailures batch)).acceptsGraphEvent
        (.streamItems stream items)
      = true := by
  obtain ⟨seen, seenPrefix, eligible⟩ :=
    queue.acceptsBatch_eachAccepted batch fifo (.streamItems stream items) accepted earlier
  obtain ⟨tail, joined⟩ := earlier
  have cut : ValidGraphEvents work ((before ++ fifo) ++ [GraphEvent.streamItems stream items]) :=
    valid.prefix ⟨tail, by simp [List.append_assoc, joined]⟩
  obtain ⟨address, results, producer, dependencies, located, nonempty, unclosed, rest⟩ :=
    cut.last_ready
  obtain ⟨remaining, same⟩ := seenPrefix
  have unclosedRemaining : stream.ref ∉ remaining.flatMap (fun event => event.identities.2) := by
    intro member
    exact unclosed (by
      simp only [List.flatMap_append, ← same]
      exact List.mem_append_right _ (List.mem_append_right _ member))
  rw [← same, State.replayGraphEvents_append queue seen remaining
    (GraphEvent.availableFailures batch)]
  exact List.contains_iff_mem.mpr
    ((queue.replayGraphEvents seen
        (GraphEvent.availableFailures batch)).replayGraphEvents_retains_unclosed_stream
      remaining stream.ref (List.contains_iff_mem.mp eligible) unclosedRemaining
      (GraphEvent.availableFailures batch))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
