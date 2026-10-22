import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedStartupProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationActivation

/-! Source-first release projects through actual cache-aware fused group startup. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

private theorem activeTasks_rootGroups (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (roots : NodeRefs)
    (available : List (Occurrence × Nat))
    : tasks.foldl (fun current task => current.startTask task.occurrence available)
        { queue with rootGroups := roots }
      = {
        tasks.foldl (fun current task => current.startTask task.occurrence available)
            queue with
          rootGroups := roots
      } := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      have head : ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).startTask
          task.occurrence available
          = { queue.startTask task.occurrence available with rootGroups := roots } := by
        unfold ReferenceWorkQueue.State.startTask
        rw [show ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).taskNode?
          task.occurrence = queue.taskNode? task.occurrence from rfl,
          show ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).task?
          task.occurrence = queue.task? task.occurrence from rfl]
        split
        · rfl
        · split <;> rfl
      rw [List.foldl_cons, head, ih, List.foldl_cons]

private theorem activeTasks_startStream (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (key : Nat)
    (available : List (Occurrence × Nat))
    : tasks.foldl (fun current task => current.startTask task.occurrence available)
        (queue.startStream key)
      = (tasks.foldl (fun current task => current.startTask task.occurrence available)
          queue).startStream
          key := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, startTask_startStream queue task.occurrence key available,
        ih, List.foldl_cons]

private theorem activeTasks_startStreams (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (streams : List Execution.DeliveryNode)
    (available : List (Occurrence × Nat))
    : tasks.foldl (fun current task => current.startTask task.occurrence available)
        (streams.foldl (fun current stream => current.startStream stream.ref) queue)
      = streams.foldl (fun current stream => current.startStream stream.ref)
          (tasks.foldl (fun current task => current.startTask task.occurrence available)
            queue) := by
  induction streams generalizing queue with
  | nil => rfl
  | cons stream rest ih =>
      rw [List.foldl_cons, ih, activeTasks_startStream, List.foldl_cons]

/-- Complete release projects to reference startup after the delayed active-task fold.
The live-task and finite-forest premises concern that concrete pre-startup queue; they
justify every subsequent fused removal without assuming its projected endpoint.
-/
theorem State.startNewWork_projects (state : State) {work : Work}
    {parents : Nat → NodeRefs} (newWork : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (running : state.stopped = false) (available : List (Occurrence × Nat))
    (frame
      : (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).TaskOwnerFrame
          work)
    (forest
      : (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).RemovalForest
          parents)
    : (
        (state.startNewWork newWork integrated targets available).1.queue,
        (state.startNewWork newWork integrated targets available).2.2
      )
      = (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).startNewWork
          newWork available := by
  let active := integrated.activeTasks.foldl
    (fun current task => current.startTask task.occurrence available) state.queue
  let roots : ReferenceWorkQueue.State :=
    { active with rootGroups := active.rootGroups
        ++ newWork.newGroups.map Execution.DeliveryNode.ref }
  let sources := newWork.newStreams.foldl
    (fun current stream => current.startStream stream.ref) roots
  let originalRoots : ReferenceWorkQueue.State :=
    { state.queue with rootGroups := state.queue.rootGroups
        ++ newWork.newGroups.map Execution.DeliveryNode.ref }
  let installedQueue := newWork.newStreams.foldl
    (fun current stream => current.startStream stream.ref) originalRoots
  let installed : State := { state with queue := installedQueue }
  let startedQueue := integrated.activeTasks.foldl
    (fun current task => current.startTask task.occurrence available) installed.queue
  let starting : State := { installed with queue := startedQueue }
  have activeRoots : active.rootGroups = state.queue.rootGroups := by
    have loop (more : List ReferenceWorkQueue.Task) (current : ReferenceWorkQueue.State)
        : (more.foldl (fun current task => current.startTask task.occurrence available)
            current).rootGroups = current.rootGroups := by
      induction more generalizing current with
      | nil => rfl
      | cons task rest ih =>
          rw [List.foldl_cons, ih]
          unfold ReferenceWorkQueue.State.startTask
          split
          · rfl
          · split <;> rfl
    exact loop _ _
  have startingQueue : starting.queue = sources := by
    dsimp only [starting, startedQueue, installed, installedQueue, originalRoots, sources, roots]
    rw [activeTasks_startStreams, activeTasks_rootGroups, activeRoots]
  have sourceFrames (more : List Execution.DeliveryNode) (current : ReferenceWorkQueue.State)
      (known : current.TaskOwnerFrame work) (finite : current.RemovalForest parents)
      : (more.foldl (fun current stream => current.startStream stream.ref)
          current).TaskOwnerFrame work
        ∧ (more.foldl (fun current stream => current.startStream stream.ref)
          current).RemovalForest parents := by
    induction more generalizing current with
    | nil => exact ⟨known, finite⟩
    | cons stream rest ih =>
        apply ih
        · change (current.startStream stream.ref).TaskOwnerFrame work
          unfold ReferenceWorkQueue.State.startStream
          split <;> exact ⟨known.owners, known.disposition, known.keys, known.registered,
            known.matching, known.sound⟩
        · change (current.startStream stream.ref).RemovalForest parents
          unfold ReferenceWorkQueue.State.startStream
          split <;> exact ⟨finite.uniqueChildren, finite.canonical, finite.increasing⟩
  have rootFrame : roots.TaskOwnerFrame work :=
    ⟨frame.owners, frame.disposition, frame.keys, frame.registered, frame.matching, frame.sound⟩
  have rootForest : roots.RemovalForest parents :=
    ⟨forest.uniqueChildren, forest.canonical, forest.increasing⟩
  have known := sourceFrames newWork.newStreams roots rootFrame rootForest
  have startingFrame : starting.queue.TaskOwnerFrame work := by
    rw [startingQueue]
    exact known.1
  have startingForest : starting.queue.RemovalForest parents := by
    rw [startingQueue]
    exact known.2
  have projected := State.startGroups_projects startingFrame startingForest
    (newWork.newGroups.map Execution.DeliveryNode.ref)
    (installed.disposeRejectedTasks integrated targets) [] available
  rw [startingQueue] at projected
  have commuted := startGroups_startStreams roots
    (newWork.newGroups.map Execution.DeliveryNode.ref) newWork.newStreams available
  change (newWork.newGroups.map Execution.DeliveryNode.ref).foldl
      (fun (current, failures) ref =>
        let (next, queued) := current.startGroup ref available
        (next, failures ++ queued)) (sources, [])
      = (newWork.newStreams.foldl (fun current stream => current.startStream stream.ref)
          ((newWork.newGroups.map Execution.DeliveryNode.ref).foldl
            (fun (current, failures) ref =>
              let (next, queued) := current.startGroup ref available
              (next, failures ++ queued)) (roots, [])).1,
          ((newWork.newGroups.map Execution.DeliveryNode.ref).foldl
            (fun (current, failures) ref =>
              let (next, queued) := current.startGroup ref available
              (next, failures ++ queued)) (roots, [])).2) at commuted
  have projected' : ((state.startNewWork newWork integrated targets available).1.queue,
        (state.startNewWork newWork integrated targets available).2.2)
      = (newWork.newGroups.map Execution.DeliveryNode.ref).foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued)) (sources, []) := by
    simpa only [State.startNewWork, running, Bool.false_eq_true, ite_false, installed,
      installedQueue, originalRoots, starting, startedQueue, startingQueue]
      using projected
  exact projected'.trans
    (by
      simpa only [ReferenceWorkQueue.State.startNewWork, List.foldl_map, roots]
        using commuted)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
