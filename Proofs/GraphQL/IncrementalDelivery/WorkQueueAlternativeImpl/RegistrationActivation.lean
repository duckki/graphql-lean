import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalInterruption
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections

/-! Root-source ownership installation commutes with the reference's task starts. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Source activation and computation activation touch independent fields
-----------------------------------------------------------------------------------------

/-- Installing a root source does not affect task lookup or the task-start decision.
Witness: source activation updates only rootStreams; task activation only taskNodes.
-/
theorem startTask_startStream (queue : ReferenceWorkQueue.State)
    (occurrence : WorkQueueSemantics.Occurrence) (key : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (queue.startStream key).startTask occurrence available
      = (queue.startTask occurrence available).startStream key := by
  have nodes : (queue.startStream key).taskNode? occurrence = queue.taskNode? occurrence := by
    unfold ReferenceWorkQueue.State.startStream
    split <;> rfl
  have tasks : (queue.startStream key).task? occurrence = queue.task? occurrence := by
    unfold ReferenceWorkQueue.State.startStream
    split <;> rfl
  unfold ReferenceWorkQueue.State.startTask
  rw [nodes, tasks]
  split
  · rfl
  · split
    · rfl
    · unfold ReferenceWorkQueue.State.startStream
      dsimp only [ReferenceWorkQueue.State.stream?]
      by_cases gate : ((queue.streams.find? (fun stream => stream.node.ref == key)).isNone
        || queue.rootStreams.contains key) = true
      · simp only [gate, ↓reduceIte]
      · simp only [gate, Bool.false_eq_true, ↓reduceIte]

private theorem startTask_rootStreams (queue : ReferenceWorkQueue.State)
    (occurrence : WorkQueueSemantics.Occurrence) (roots : WorkQueueSemantics.NodeRefs)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : ({ queue with rootStreams := roots } : ReferenceWorkQueue.State).startTask
        occurrence available
      = { queue.startTask occurrence available with rootStreams := roots } := by
  unfold ReferenceWorkQueue.State.startTask
  rw [show ({ queue with rootStreams := roots } : ReferenceWorkQueue.State).taskNode?
      occurrence = queue.taskNode? occurrence from rfl,
    show ({ queue with rootStreams := roots } : ReferenceWorkQueue.State).task?
      occurrence = queue.task? occurrence from rfl]
  split
  · rfl
  · split <;> rfl

private theorem cacheTaskFailures_rootStreams (queue : ReferenceWorkQueue.State)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (roots : WorkQueueSemantics.NodeRefs)
    : ({ queue with rootStreams := roots } : ReferenceWorkQueue.State).cacheTaskFailures
        available
      = { queue.cacheTaskFailures available with rootStreams := roots } := by
  unfold ReferenceWorkQueue.State.cacheTaskFailures
  induction available generalizing queue with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      rw [show ({ queue with rootStreams := roots } : ReferenceWorkQueue.State).taskNode?
        entry.1 = queue.taskNode? entry.1 from rfl]
      cases found : queue.taskNode? entry.1 with
      | none => exact ih queue
      | some node => exact ih (queue.putTaskNode { node with rejection := some entry.2 })

private theorem removeGroup_rootStreams (queue : ReferenceWorkQueue.State)
    (ref : Nat) (roots : WorkQueueSemantics.NodeRefs)
    : ({ queue with rootStreams := roots } : ReferenceWorkQueue.State).removeGroup ref
      = { queue.removeGroup ref with rootStreams := roots } := by
  have collect (fuel : Nat) (pending removed : WorkQueueSemantics.NodeRefs)
      : ReferenceWorkQueue.State.removeGroup.collect fuel { queue with rootStreams := roots }
          pending removed
        = ReferenceWorkQueue.State.removeGroup.collect fuel queue pending removed := by
    induction fuel generalizing pending removed with
    | zero => simp only [ReferenceWorkQueue.State.removeGroup.collect]
    | succ fuel ih =>
        induction pending generalizing removed with
        | nil => simp only [ReferenceWorkQueue.State.removeGroup.collect]
        | cons key rest tailIH =>
            simp only [ReferenceWorkQueue.State.removeGroup.collect,
              ReferenceWorkQueue.State.groupNode?]
            split
            · exact tailIH removed
            · exact ih _ _
  unfold ReferenceWorkQueue.State.removeGroup
  simp only [collect]

private theorem startGroup_rootStreams (queue : ReferenceWorkQueue.State)
    (ref : Nat) (roots : WorkQueueSemantics.NodeRefs)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : ({ queue with rootStreams := roots } : ReferenceWorkQueue.State).startGroup ref
        available
      = (
        { (queue.startGroup ref available).1 with rootStreams := roots },
        (queue.startGroup ref available).2
      ) := by
  have tasks (more : List WorkQueueSemantics.Occurrence) (current : ReferenceWorkQueue.State)
      : more.foldl (fun current task => current.startTask task available)
          { current with rootStreams := roots }
        = { more.foldl (fun current task => current.startTask task available) current with
            rootStreams := roots } := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, startTask_rootStreams, ih, List.foldl_cons]
  unfold ReferenceWorkQueue.State.startGroup
  rw [cacheTaskFailures_rootStreams]
  dsimp only
  rw [show ({ queue.cacheTaskFailures available with rootStreams := roots }
    : ReferenceWorkQueue.State).groupNode? ref =
      (queue.cacheTaskFailures available).groupNode? ref from rfl]
  cases found : (queue.cacheTaskFailures available).groupNode? ref with
  | none => rfl
  | some node =>
      dsimp only
      have errorsEq : node.tasks.filterMap (fun task =>
          (({ queue.cacheTaskFailures available with rootStreams := roots }
            : ReferenceWorkQueue.State).taskNode? task).bind (·.rejection))
          = node.tasks.filterMap (fun task =>
            ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection)) := rfl
      rw [errorsEq]
      by_cases healthy : (node.tasks.filterMap (fun task =>
        ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection))).isEmpty = true
      · simp only [healthy, ite_true, tasks]
      · simp only [healthy, Bool.false_eq_true, ite_false,
          ReferenceWorkQueue.State.finishGroupFailure,
          removeGroup_rootStreams]

private theorem startGroup_sourceFrame (queue : ReferenceWorkQueue.State) (ref : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (queue.startGroup ref available).1.streams = queue.streams
      ∧ (queue.startGroup ref available).1.rootStreams = queue.rootStreams := by
  have cacheFrame := queue.cacheTaskFailures_frame available
  have streams := congrArg ReferenceWorkQueue.State.streams cacheFrame
  have roots := congrArg ReferenceWorkQueue.State.rootStreams cacheFrame
  have tasks (more : List WorkQueueSemantics.Occurrence) (current : ReferenceWorkQueue.State)
      : (more.foldl (fun current task => current.startTask task available) current).streams
          = current.streams
        ∧ (more.foldl (fun current task => current.startTask task available) current).rootStreams
          = current.rootStreams := by
    induction more generalizing current with
    | nil => exact ⟨rfl, rfl⟩
    | cons task rest ih =>
        have unchanged : (current.startTask task available).streams = current.streams
            ∧ (current.startTask task available).rootStreams = current.rootStreams := by
          unfold ReferenceWorkQueue.State.startTask
          split
          · exact ⟨rfl, rfl⟩
          · split <;> exact ⟨rfl, rfl⟩
        have next := ih (current.startTask task available)
        exact ⟨next.1.trans unchanged.1, next.2.trans unchanged.2⟩
  unfold ReferenceWorkQueue.State.startGroup
  dsimp only
  split
  · exact ⟨streams, roots⟩
  · rename_i node found
    split
    · have next := tasks node.tasks (queue.cacheTaskFailures available)
      exact ⟨next.1.trans streams, next.2.trans roots⟩
    · exact ⟨streams, roots⟩

/-- Root-source installation commutes with complete cache-aware group startup. -/
theorem startGroup_startStream (queue : ReferenceWorkQueue.State) (group key : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (queue.startStream key).startGroup group available
      = (
        (queue.startGroup group available).1.startStream key,
        (queue.startGroup group available).2
      ) := by
  have frame := startGroup_sourceFrame queue group available
  unfold ReferenceWorkQueue.State.startStream
  simp only [ReferenceWorkQueue.State.stream?, frame.1, frame.2]
  by_cases gate : ((queue.streams.find? (fun stream => stream.node.ref == key)).isNone
      || queue.rootStreams.contains key) = true
  · simp only [gate, ite_true]
  · simp only [gate, Bool.false_eq_true, ite_false]
    rw [startGroup_rootStreams]
    simp only [frame.1]

private def startReferenceGroups (queue : ReferenceWorkQueue.State)
    (groups : List Nat) (available : List (WorkQueueSemantics.Occurrence × Nat))
    : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent :=
  groups.foldl
    (fun (current, failures) ref =>
      let (next, queued) := current.startGroup ref available
      (next, failures ++ queued))
    (queue, [])

private theorem startReferenceGroups_startStream (queue : ReferenceWorkQueue.State)
    (groups : List Nat) (key : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : startReferenceGroups (queue.startStream key) groups available
      = (
        (startReferenceGroups queue groups available).1.startStream key,
        (startReferenceGroups queue groups available).2
      ) := by
  have loop (more : List Nat)
      (acc : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent)
      : (more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) (acc.1.startStream key, acc.2))
        = (let result := more.foldl (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued)) acc
          (result.1.startStream key, result.2)) := by
    induction more generalizing acc with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons, startGroup_startStream]
        simpa only using ih ((acc.1.startGroup ref available).1,
          acc.2 ++ (acc.1.startGroup ref available).2)
  exact loop groups (queue, [])

/-- Source-first and group-first activation preserve both state and queued failures. -/
theorem startGroups_startStreams (queue : ReferenceWorkQueue.State)
    (groups : List Nat) (streams : List Execution.DeliveryNode)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : startReferenceGroups
        (streams.foldl (fun current stream => current.startStream stream.ref) queue)
        groups available
      = (
        streams.foldl (fun current stream => current.startStream stream.ref)
          (startReferenceGroups queue groups available).1,
        (startReferenceGroups queue groups available).2
      ) := by
  induction streams generalizing queue with
  | nil => rfl
  | cons stream rest ih =>
      rw [List.foldl_cons, ih, startReferenceGroups_startStream]
      rfl

private theorem clean_startGroup (queue : ReferenceWorkQueue.State) (ref : Nat)
    (clean : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : ∀ node ∈ (queue.startGroup ref).1.taskNodes, node.rejection = none := by
  have valid : queue.TaskRejectionsSatisfy (fun _ _ => False) := by
    intro node member errors rejected
    rw [clean node member] at rejected
    cases rejected
  have next := valid.startGroup ref
  intro node member
  cases rejected : node.rejection with
  | none => rfl
  | some errors => exact (next node member errors rejected).elim

private theorem State.startGroup_queue_of_no_cached_failures (state : State) (ref : Nat)
    (targets : List CleanupTarget)
    (clean : ∀ node ∈ state.queue.taskNodes, node.rejection = none)
    : (state.startGroup ref targets).1.queue = (state.queue.startGroup ref).1
      ∧ (state.startGroup ref targets).2.2 = (state.queue.startGroup ref).2 := by
  cases found : state.queue.groupNode? ref with
  | none =>
      simp only [State.startGroup, ReferenceWorkQueue.State.startGroup,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil, found]
      constructor <;> first | rfl | trivial
  | some group =>
      have errors : group.tasks.filterMap
          (fun task => (state.queue.taskNode? task).bind (·.rejection)) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro task member
        cases known : state.queue.taskNode? task with
        | none => rfl
        | some node => exact clean node (List.mem_of_find?_eq_some known)
      simp only [State.startGroup, ReferenceWorkQueue.State.startGroup,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil, found, errors,
        List.isEmpty_nil, ite_true]
      constructor <;> first | rfl | trivial

/-- Initial activation projects exactly when no old or available rejection can trigger
fused removal. The clean-cache premise is derived from actual initialization.
-/
theorem State.startNewWork_queue_and_notices_of_no_active (state : State)
    (newWork : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (running : state.stopped = false)
    (inactive : integrated.activeTasks = [])
    (clean : ∀ node ∈ state.queue.taskNodes, node.rejection = none)
    : (
        (state.startNewWork newWork integrated targets).1.queue,
        (state.startNewWork newWork integrated targets).2.2
      )
      = state.queue.startNewWork newWork := by
  have groups (more : List Nat)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      (prior : ∀ node ∈ acc.1.queue.taskNodes, node.rejection = none)
      : let alternative := more.foldl (fun (current, targets, failures) ref =>
          let (next, targets, queued) := current.startGroup ref targets
          (next, targets, failures ++ queued)) acc
        let reference := more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref
          (next, failures ++ queued)) (acc.1.queue, acc.2.2)
        (alternative.1.queue, alternative.2.2) = reference := by
    induction more generalizing acc with
    | nil => rfl
    | cons ref rest ih =>
        have same := acc.1.startGroup_queue_of_no_cached_failures ref acc.2.1 prior
        have nextClean : ∀ node ∈ (acc.1.startGroup ref acc.2.1).1.queue.taskNodes,
            node.rejection = none := by
          rw [same.1]
          exact clean_startGroup _ ref prior
        simpa only [List.foldl_cons, same.1, same.2]
          using ih
            (
              (acc.1.startGroup ref acc.2.1).1,
              (acc.1.startGroup ref acc.2.1).2.1,
              acc.2.2 ++ (acc.1.startGroup ref acc.2.1).2.2
            )
            nextClean
  have streams (more : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      (prior : ∀ node ∈ queue.taskNodes, node.rejection = none)
      : ∀ node ∈ (more.foldl (fun current stream => current.startStream stream.ref)
          queue).taskNodes, node.rejection = none := by
    induction more generalizing queue with
    | nil => exact prior
    | cons stream rest ih =>
        apply ih
        change ∀ node ∈ (queue.startStream stream.ref).taskNodes, node.rejection = none
        unfold ReferenceWorkQueue.State.startStream
        split <;> exact prior
  let installed := newWork.newStreams.foldl
    (fun current stream => current.startStream stream.ref)
    { state.queue with rootGroups := state.queue.rootGroups
        ++ newWork.newGroups.map Execution.DeliveryNode.ref }
  have projected := groups (newWork.newGroups.map Execution.DeliveryNode.ref)
    (({ state with queue := installed } : State),
      ({ state with queue := installed } : State).disposeRejectedTasks integrated targets, [])
    (streams newWork.newStreams _ clean)
  have commuted := startGroups_startStreams
    { state.queue with rootGroups := state.queue.rootGroups
        ++ newWork.newGroups.map Execution.DeliveryNode.ref }
    (newWork.newGroups.map Execution.DeliveryNode.ref) newWork.newStreams
  simp only [State.startNewWork, running, Bool.false_eq_true, ite_false,
    inactive, List.foldl_nil, ReferenceWorkQueue.State.startNewWork]
  have result := projected.trans commuted
  simpa only [running, installed, startReferenceGroups, List.foldl_map] using result

/-- Empty-snapshot activation has the same kernel as the reference start fold. -/
theorem State.startNewWork_queue_of_no_active (state : State)
    (newWork : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (running : state.stopped = false)
    (inactive : integrated.activeTasks = [])
    (clean : ∀ node ∈ state.queue.taskNodes, node.rejection = none)
    : (state.startNewWork newWork integrated targets).1.queue
      = (state.queue.startNewWork newWork).1 :=
  congrArg Prod.fst
    (state.startNewWork_queue_and_notices_of_no_active newWork integrated
      targets running inactive clean)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
