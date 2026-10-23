import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections

/-! Empty startup observations retain the original asynchronous activation transition. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)

private theorem startTask_clean (queue : State) (task : Occurrence)
    (clean : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : ∀ node ∈ (queue.startTask task).taskNodes, node.rejection = none := by
  unfold State.startTask
  split
  · exact clean
  · split
    · exact clean
    · intro node member
      rcases List.mem_append.mp member with prior | fresh
      · exact clean node prior
      · cases List.mem_singleton.mp fresh
        rfl

private theorem startGroup_clean (queue : State) (ref : NodeRef)
    (clean : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : (∀ node ∈ (queue.startGroup ref).1.taskNodes, node.rejection = none)
      ∧ (queue.startGroup ref).2 = [] := by
  have tasks (remaining : List Occurrence) (current : State)
      (clear : ∀ node ∈ current.taskNodes, node.rejection = none)
      : ∀ node ∈ (remaining.foldl (fun state task => state.startTask task) current).taskNodes,
          node.rejection = none := by
    induction remaining generalizing current with
    | nil => exact clear
    | cons task rest ih => exact ih _ (startTask_clean current task clear)
  cases found : queue.groupNode? ref with
  | none =>
      simpa only [State.startGroup, State.cacheTaskFailures, List.foldl_nil, found]
        using And.intro clean (Eq.refl ([] : List GroupFailureEvent))
  | some group =>
      have errors : group.tasks.filterMap
          (fun task => (queue.taskNode? task).bind (·.rejection)) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro task _
        cases selected : queue.taskNode? task with
        | none => rfl
        | some node => exact clean node (List.mem_of_find?_eq_some selected)
      simpa only [State.startGroup, State.cacheTaskFailures, List.foldl_nil, found,
        errors, List.isEmpty_nil, ite_true]
        using And.intro (tasks group.tasks queue clean)
          (Eq.refl ([] : List GroupFailureEvent))

/-- Empty-cache activation cannot enqueue an internal failure notice. -/
theorem State.startNewWork_noFailures (queue : State) (work : NewWork)
    (clean : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : (queue.startNewWork work).2 = [] := by
  have groups (refs : List NodeRef) (current : State) (notices : List GroupFailureEvent)
      (clear : ∀ node ∈ current.taskNodes, node.rejection = none)
      : (refs.foldl (fun (state, failures) ref =>
          let (next, queued) := state.startGroup ref
          (next, failures ++ queued)) (current, notices)).2 = notices := by
    induction refs generalizing current notices with
    | nil => rfl
    | cons ref rest ih =>
        have next := startGroup_clean current ref clear
        rw [List.foldl_cons, ih _ _ next.1, next.2, List.append_nil]
  unfold State.startNewWork
  exact groups _ _ [] clean

/-- Empty startup is exactly the former registration/pruning/activation expression.
No emitted output or source-admission premise is used; the equality covers every raw Work.
-/
theorem State.initialize_empty_eq_activation (work : Work)
    : State.initialize work {}
      = let (integrated, newWork) := ({} : State).maybeIntegrateWork work
        let (pruned, groups) := integrated.pruneEmptyGroups newWork.newGroups
        let roots := { newWork with newGroups := groups }
        let (started, _) := pruned.startNewWork roots
        { started with initialGroups := groups, initialStreams := roots.newStreams } := by
  let integrated := ({} : State).maybeIntegrateWork work
  let prepared := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have clear : prepared.1.TaskRejectionsSatisfy (fun _ _ => False) :=
    ((show ({} : State).TaskRejectionsSatisfy (fun _ _ => False) from
      fun _ impossible => by cases impossible).maybeIntegrateWork work).pruneEmptyGroups _
  have clean : ∀ node ∈ prepared.1.taskNodes, node.rejection = none := by
    intro node member
    cases rejected : node.rejection with
    | none => rfl
    | some errors => exact (clear node member errors rejected).elim
  unfold State.initialize
  dsimp only
  rw [State.startNewWork_noFailures _ _ clean]
  simp only [State.enqueueGroupFailures, List.append_nil]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
