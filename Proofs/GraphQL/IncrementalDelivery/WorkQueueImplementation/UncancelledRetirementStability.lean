import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledMarkers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRetirementReplay

/-! A permanently retired uncancelled ref cannot acquire a later cancellation marker. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Retirement and cancellation exclusion concern permanent existing queue fields only. -/
def UncancelledRetirement (queue : State) (ref : NodeRef) : Prop :=
  queue.RetiredGroup ref ∧ ref ∉ queue.cancelledGroups

theorem UncancelledRetirement.retired {queue ref}
    (prior : UncancelledRetirement queue ref)
    : queue.RetiredGroup ref :=
  prior.1

theorem UncancelledRetirement.uncancelled {queue ref}
    (prior : UncancelledRetirement queue ref)
    : ref ∉ queue.cancelledGroups :=
  prior.2

theorem UncancelledRetirement.cacheTaskFailures {queue ref}
    (prior : UncancelledRetirement queue ref) (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.cacheTaskFailures available) ref := by
  exact ⟨
    prior.retired.cacheTaskFailures available,
    by
      rw [State.cacheTaskFailures_cancelledGroups]; exact prior.uncancelled
  ⟩

theorem UncancelledRetirement.putTaskNode {queue ref}
    (prior : UncancelledRetirement queue ref) (node : TaskNode)
    : UncancelledRetirement (queue.putTaskNode node) ref :=
  prior

theorem UncancelledRetirement.putGroupNode {queue ref}
    (prior : UncancelledRetirement queue ref) (node : GroupNode)
    : UncancelledRetirement (queue.putGroupNode node) ref :=
  ⟨prior.retired.putGroupNode node, prior.uncancelled⟩

theorem UncancelledRetirement.maybeIntegrateWork {queue ref}
    (prior : UncancelledRetirement queue ref) (incoming : Work)
    (producer : Option Occurrence := none)
    : UncancelledRetirement (queue.maybeIntegrateWork incoming producer).1 ref := by
  refine ⟨prior.retired.maybeIntegrateWork incoming producer, ?_⟩
  intro marked
  rw [State.maybeIntegrateWork_cancelledGroups _ incoming producer] at marked
  exact prior.uncancelled (queue.addGroups_registered_cancellation incoming.groups
    prior.retired.1 marked)

theorem UncancelledRetirement.pruneEmptyGroups {queue ref}
    (prior : UncancelledRetirement queue ref) (groups : List Execution.DeliveryNode)
    : UncancelledRetirement (queue.pruneEmptyGroups groups).1 ref := by
  exact ⟨
    prior.retired.pruneEmptyGroups groups,
    by
      rw [State.pruneEmptyGroups_cancelledGroups]; exact prior.uncancelled
  ⟩

theorem UncancelledRetirement.finishGroupSuccess {queue ref}
    (prior : UncancelledRetirement queue ref) (node : GroupNode)
    : UncancelledRetirement (queue.finishGroupSuccess node).1 ref := by
  exact ⟨
    prior.retired.finishGroupSuccess node,
    by
      rw [State.finishGroupSuccess_cancelledGroups]; exact prior.uncancelled
  ⟩

theorem UncancelledRetirement.removeGroup {queue ref}
    (prior : UncancelledRetirement queue ref) (root : NodeRef)
    : UncancelledRetirement (queue.removeGroup root) ref := by
  refine ⟨prior.retired.removeGroup root, ?_⟩
  intro marked
  rcases List.mem_append.mp marked with old | added
  · exact prior.uncancelled old
  · rcases State.removeGroup_collect_mem (queue.groupNodes.length + 1) queue [root] [] added with
      impossible | ⟨node, member, same⟩
    · cases impossible
    · exact prior.retired.2 (List.mem_map.mpr ⟨node, member, same⟩)

theorem UncancelledRetirement.startTask {queue ref}
    (prior : UncancelledRetirement queue ref) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.startTask occurrence available) ref := by
  unfold State.startTask
  split
  · exact prior
  · split <;> exact prior

theorem UncancelledRetirement.startGroup {queue ref}
    (prior : UncancelledRetirement queue ref) (root : NodeRef)
    (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.startGroup root available).1 ref := by
  have cached := prior.cacheTaskFailures available
  have fold (tasks : List Occurrence) (current : State)
      (frame : UncancelledRetirement current ref)
      : UncancelledRetirement (tasks.foldl
          (fun next task => next.startTask task available) current) ref := by
    induction tasks generalizing current with
    | nil => exact frame
    | cons task rest ih => exact ih _ (frame.startTask task available)
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact fold _ _ cached
    · exact cached.removeGroup _

theorem UncancelledRetirement.startNewWork {queue ref}
    (prior : UncancelledRetirement queue ref) (released : NewWork)
    (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.startNewWork released available).1 ref := by
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (frame : UncancelledRetirement acc.1 ref)
      : UncancelledRetirement (refs.foldl (fun (current, failures) root =>
          let (next, queued) := current.startGroup root available
          (next, failures ++ queued)) acc).1 ref := by
    induction refs generalizing acc with
    | nil => exact frame
    | cons root rest ih => exact ih _ (frame.startGroup root available)
  have streams (refs : NodeRefs) (current : State) (frame : UncancelledRetirement current ref)
      : UncancelledRetirement (refs.foldl State.startStream current) ref := by
    induction refs generalizing current with
    | nil => exact frame
    | cons root rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact frame
  unfold State.startNewWork
  exact streams _ _ (groups _ _ prior)

theorem UncancelledRetirement.drainReadyGroups {queue ref}
    (prior : UncancelledRetirement queue ref) (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.drainReadyGroups available).1 ref :=
  State.drainReadyGroups_preserves (fun current => UncancelledRetirement current ref)
    (fun _ node frame _ _ _ => (frame.finishGroupSuccess node).startNewWork _ available)
    prior (available := available)

theorem UncancelledRetirement.taskFailure {queue ref}
    (prior : UncancelledRetirement queue ref) (occurrence : Occurrence) (errors : Nat)
    : UncancelledRetirement (queue.taskFailure occurrence errors).1 ref := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using prior
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun current => UncancelledRetirement current ref)
        (fun _ root frame => frame.removeGroup root) _ _ _ (prior.putTaskNode _)

theorem UncancelledRetirement.taskSuccess {queue ref}
    (prior : UncancelledRetirement queue ref) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.taskSuccess occurrence result available).1 ref := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using prior
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      have fold (groups : List Execution.DeliveryNode)
          (acc : State × List Execution.WorkQueueEvent × NewWork)
          (frame : UncancelledRetirement acc.1 ref)
          : UncancelledRetirement (groups.foldl successGroupStep acc).1 ref := by
        induction groups generalizing acc with
        | nil => exact frame
        | cons group rest ih =>
            apply ih
            unfold successGroupStep
            dsimp only
            split
            · exact frame
            · split
              · exact (frame.putGroupNode _).finishGroupSuccess _
              · exact frame.putGroupNode _
      exact ((fold node.task.groups (_, [], {})
                ((prior.putTaskNode _).maybeIntegrateWork
                  result.work (some occurrence))).startNewWork
              _ available).drainReadyGroups
        available

theorem UncancelledRetirement.streamItems {queue ref}
    (prior : UncancelledRetirement queue ref) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.streamItems stream items available).1 ref := by
  have prepared := State.preparedStreamItems_preserves
    (fun current => UncancelledRetirement current ref) prior items available
    (fun _ item _ frame => ((frame.maybeIntegrateWork item.work).pruneEmptyGroups _
      ).startNewWork _ available)
  rw [queue.streamItems_eq stream items available]
  split
  · exact prior
  · exact prepared.drainReadyGroups available

theorem UncancelledRetirement.handleGraphEvent {queue ref}
    (prior : UncancelledRetirement queue ref) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.handleGraphEvent event available).1 ref := by
  have cached := prior.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result => exact cached.taskSuccess occurrence result available
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items => exact cached.streamItems stream items available
  | streamSuccess stream =>
      change UncancelledRetirement ((queue.cacheTaskFailures available).streamSuccess stream).1 ref
      unfold State.streamSuccess
      split <;> exact cached
  | streamFailure stream errors =>
      change UncancelledRetirement
        ((queue.cacheTaskFailures available).streamFailure stream errors).1 ref
      unfold State.streamFailure
      split <;> exact cached
  | groupFailure notice =>
      change UncancelledRetirement ((queue.cacheTaskFailures available).groupFailure notice).1 ref
      unfold ReferenceWorkQueue.State.groupFailure
      split
      · exact cached
      · split <;> exact cached

/-- Realized internal notices change no retirement or cancellation observation. -/
theorem UncancelledRetirement.dispatchGraphEvent {queue ref}
    (prior : UncancelledRetirement queue ref) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.dispatchGraphEvent event available).1 ref :=
  prior.handleGraphEvent event available

theorem UncancelledRetirement.replayGraphEvents {queue ref}
    (prior : UncancelledRetirement queue ref) (events : List GraphEvent)
    (available : List (Occurrence × Nat))
    : UncancelledRetirement (queue.replayGraphEvents events available) ref := by
  induction events generalizing queue with
  | nil => exact prior
  | cons event rest ih => exact ih (prior.dispatchGraphEvent event available)

theorem UncancelledRetirement.withTerminated {queue ref}
    (prior : UncancelledRetirement queue ref) (terminated : Bool)
    : UncancelledRetirement { queue with terminated := terminated } ref :=
  prior

theorem UncancelledRetirement.handleGraphEvents {queue ref}
    (prior : UncancelledRetirement queue ref) (events : List GraphEvent)
    : UncancelledRetirement (queue.handleGraphEvents events).1 ref := by
  by_cases ended : queue.terminated = true
  · simpa only [State.handleGraphEvents, ended, ite_true] using prior
  · obtain ⟨terminal, same⟩ :=
      queue.handleGraphEvents_stateCore events (Bool.eq_false_iff.mpr ended)
    rw [same]
    exact (prior.replayGraphEvents events
      (GraphEvent.availableFailures events)).withTerminated terminal

theorem UncancelledRetirement.replayBatches {queue ref}
    (prior : UncancelledRetirement queue ref) (batches : List (List GraphEvent))
    : UncancelledRetirement (queue.replayBatches batches) ref := by
  induction batches generalizing queue with
  | nil => exact prior
  | cons batch rest ih => exact ih (prior.handleGraphEvents batch)

/-- Once retired without cancellation, a ref stays so through arbitrary later host batches.
Witness: registration cannot remark an old registered ref, and failure collection visits
only live records. Successful cleanup, startup, notification and termination preserve it.
No source validity, matching, output-admission or fairness premise is needed.
-/
theorem UncancelledRetirement.runNormalized {queue ref}
    (prior : UncancelledRetirement queue ref) (batches : List (List GraphEvent))
    : UncancelledRetirement (queue.runNormalized batches).1 ref := by
  rw [State.runNormalized_replayBatches]
  exact prior.replayBatches batches

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
