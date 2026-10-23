import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationScopeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections

/-! Registration and delayed starts preserve the origins of retained task rejections. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)

/-- Delayed task registration changes no computation node. -/
theorem State.addTask_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.TaskRejectionsSatisfy property := by
  intro node member
  rw [State.addTask_taskNodes] at member
  exact prior node member

/-- Delayed integration preserves every retained computation rejection. -/
theorem State.maybeIntegrateWork_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property)
    (work : ReferenceWorkQueue.Work) (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.TaskRejectionsSatisfy property := by
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (supported : acc.1.queue.TaskRejectionsSatisfy property)
      : (tasks.foldl registerTaskStep acc).1.queue.TaskRejectionsSatisfy property := by
    induction tasks generalizing acc with
    | nil => exact supported
    | cons task rest ih =>
        apply ih
        unfold registerTaskStep
        dsimp only
        split <;> exact State.addTask_taskRejections supported task
  exact (loop work.tasks _ (prior.addGroups work.groups)).addStreams work.streams parent

/-- Fused removal only deletes task nodes, preserving every retained rejection fact.
This field frame holds at every finite budget, including malformed raw group graphs.
-/
theorem State.removeGroup_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property) (ref : Nat)
    (targets : List CleanupTarget := [])
    : (state.removeGroup ref targets).1.queue.TaskRejectionsSatisfy property := by
  have step (acc : State × List CleanupTarget) (occurrence : Occurrence)
      (supported : acc.1.queue.TaskRejectionsSatisfy property)
      : (fusedRemovalTaskStep acc occurrence).1.queue.TaskRejectionsSatisfy property := by
    unfold fusedRemovalTaskStep
    split
    · exact supported
    · split
      · exact supported.removeTask occurrence
      · exact supported
  have tasks (more : List Occurrence) (acc : State × List CleanupTarget)
      (supported : acc.1.queue.TaskRejectionsSatisfy property)
      : (more.foldl fusedRemovalTaskStep acc).1.queue.TaskRejectionsSatisfy property := by
    induction more generalizing acc with
    | nil => exact supported
    | cons occurrence rest ih => exact ih _ (step acc occurrence supported)
  have loop (fuel : Nat) (current : State) (pending removed) (targets)
      (supported : current.queue.TaskRejectionsSatisfy property)
      : let final := State.removeGroup.walk fuel current pending removed targets
        final.1.queue.TaskRejectionsSatisfy property := by
    induction fuel generalizing current pending removed targets with
    | zero => simpa only [State.removeGroup.walk] using supported
    | succ fuel ih =>
        induction pending generalizing current removed targets with
        | nil => simpa only [State.removeGroup.walk] using supported
        | cons key rest tailIH =>
            cases found : current.queue.groupNode? key with
            | none =>
                simpa only [State.removeGroup.walk, found] using tailIH _ _ _ supported
            | some group =>
                rw [State.removeGroup.walk, found]
                let erased := eraseRemovalGroup current key
                let folded := group.tasks.foldl fusedRemovalTaskStep (erased, targets)
                exact ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2
                  (tasks group.tasks (erased, targets) supported)
  exact loop _ state [ref] [] targets prior

/-- Cache-aware fused startup retains only licensed computation rejection facts. -/
theorem State.startGroup_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property) (ref : Nat)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors)
    : (state.startGroup ref targets available).1.queue.TaskRejectionsSatisfy
        property := by
  have cached := prior.cacheTaskFailures available licensed
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · have loop (more : List Occurrence) (queue : ReferenceWorkQueue.State)
          (supported : queue.TaskRejectionsSatisfy property)
          : (more.foldl (fun current task => current.startTask task available)
              queue).TaskRejectionsSatisfy property := by
        induction more generalizing queue with
        | nil => exact supported
        | cons occurrence rest ih =>
            exact ih _ (supported.startTask occurrence available licensed)
      exact loop _ _ cached
    · exact State.removeGroup_taskRejections cached _ _

/-- Delayed activation preserves prior rejections and licenses cache-exposed outcomes.
The proof follows actual field changes and fused removal; no full queue projection or
finite-forest premise is needed for rejection provenance alone.
-/
theorem State.startNewWork_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := []) (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors := by
        intro occurrence errors member; cases member)
    : (state.startNewWork roots integrated targets
        available).1.queue.TaskRejectionsSatisfy
        property := by
  have streams (more : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      (supported : queue.TaskRejectionsSatisfy property)
      : (more.foldl (fun current stream => current.startStream stream.ref)
          queue).TaskRejectionsSatisfy property := by
    induction more generalizing queue with
    | nil => exact supported
    | cons stream rest ih =>
        apply ih
        change (queue.startStream stream.ref).TaskRejectionsSatisfy property
        unfold ReferenceWorkQueue.State.startStream
        split <;> exact supported
  have tasks (more : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      (supported : queue.TaskRejectionsSatisfy property)
      : (more.foldl (fun current task => current.startTask task.occurrence available)
          queue).TaskRejectionsSatisfy property := by
    induction more generalizing queue with
    | nil => exact supported
    | cons task rest ih =>
        exact ih _ (supported.startTask task.occurrence available licensed)
  have groups (more : WorkQueueSemantics.NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      (supported : acc.1.queue.TaskRejectionsSatisfy property)
      : (more.foldl
          (fun (current, targets, failures) ref =>
            let (next, targets, queued) := current.startGroup ref targets available
            (next, targets, failures ++ queued))
          acc).1.queue.TaskRejectionsSatisfy
          property := by
    induction more generalizing acc with
    | nil => exact supported
    | cons ref rest ih =>
        exact ih _ (State.startGroup_taskRejections supported ref _ _ licensed)
  unfold State.startNewWork
  split
  · exact prior
  · exact groups _ _ (tasks _ _ (streams _ _ prior))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
