import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Structural frames for cache exposure and group startup. Runtime failure reporting
changes no existing group record and can only remove groups during activation.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)

/-- Cache exposure changes only retained task-node outcomes. -/
theorem State.cacheTaskFailures_frame (queue : State)
    (available : List (Occurrence × Nat))
    : { queue.cacheTaskFailures available with taskNodes := [] }
      = { queue with taskNodes := [] } := by
  induction available generalizing queue with
  | nil => rfl
  | cons entry rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih queue
      · exact (ih _).trans rfl

/-- Computation availability leaves the internal notice FIFO unchanged. -/
theorem State.cacheTaskFailures_groupFailureEvents (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).groupFailureEvents
      = queue.groupFailureEvents := by
  have frame := congrArg State.groupFailureEvents (queue.cacheTaskFailures_frame available)
  exact frame

/-- Exposing cached outcomes preserves all live group records. -/
theorem State.cacheTaskFailures_groupNodes (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).groupNodes = queue.groupNodes := by
  have frame := congrArg State.groupNodes (queue.cacheTaskFailures_frame available)
  exact frame

/-- Exposing cached outcomes preserves the active group roots. -/
theorem State.cacheTaskFailures_rootGroups (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).rootGroups = queue.rootGroups := by
  have frame := congrArg State.rootGroups (queue.cacheTaskFailures_frame available)
  exact frame

/-- Cached outcomes do not change the permanent registration history. -/
theorem State.cacheTaskFailures_registeredGroups (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).registeredGroups = queue.registeredGroups := by
  have frame := congrArg State.registeredGroups (queue.cacheTaskFailures_frame available)
  exact frame

/-- Starting computations preserves registration history, including cached failures. -/
theorem State.startGroup_registeredGroups (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.registeredGroups = queue.registeredGroups := by
  have tasks (more : List Occurrence) (current : State)
      : (more.foldl (fun current task => current.startTask task available)
          current).registeredGroups = current.registeredGroups := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startTask
        split
        · rfl
        · split <;> rfl
  unfold State.startGroup
  dsimp only
  split
  · exact queue.cacheTaskFailures_registeredGroups available
  · split
    · exact (tasks _ _).trans (queue.cacheTaskFailures_registeredGroups available)
    · exact queue.cacheTaskFailures_registeredGroups available

/-- Starting a task changes no group record, regardless of its available rejection. -/
theorem State.startTask_groupNodes (queue : State) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    : (queue.startTask occurrence available).groupNodes = queue.groupNodes := by
  unfold State.startTask
  split
  · rfl
  · split <;> rfl

private theorem startTasks_groupNodes (tasks : List Occurrence) (queue : State)
    (available : List (Occurrence × Nat))
    : (tasks.foldl (fun current task => current.startTask task available)
        queue).groupNodes
      = queue.groupNodes := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      simp only [List.foldl_cons]
      rw [ih, State.startTask_groupNodes]

/-- Startup either retains all group records or removes failed groups and descendants. -/
theorem State.startGroup_groupNodes_sublist (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.groupNodes.Sublist queue.groupNodes := by
  cases found : (queue.cacheTaskFailures available).groupNode? ref with
  | none =>
      simp only [State.startGroup, found, State.cacheTaskFailures_groupNodes]
      exact List.Sublist.refl _
  | some group =>
      simp only [State.startGroup, found]
      split
      · simp only [startTasks_groupNodes, State.cacheTaskFailures_groupNodes]
        exact List.Sublist.refl _
      · have retained :
            ((queue.cacheTaskFailures available).removeGroup
              group.group.node.ref).groupNodes.Sublist
              (queue.cacheTaskFailures available).groupNodes := List.filter_sublist
        simpa only [State.finishGroupFailure, State.cacheTaskFailures_groupNodes] using retained

/-- Stream activation leaves all live group records unchanged. -/
theorem State.startStream_groupNodes (queue : State) (ref : NodeRef)
    : (queue.startStream ref).groupNodes = queue.groupNodes := by
  unfold State.startStream
  split <;> rfl

private theorem startStreams_groupNodes (refs : NodeRefs) (queue : State)
    : (refs.foldl State.startStream queue).groupNodes = queue.groupNodes := by
  induction refs generalizing queue with
  | nil => rfl
  | cons ref rest ih =>
      simp only [List.foldl_cons]
      rw [ih, State.startStream_groupNodes]

/-- Activating released work only removes existing group records; notices are separate. -/
theorem State.startNewWork_groupNodes_sublist (queue : State) (work : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork work available).1.groupNodes.Sublist queue.groupNodes := by
  have groupFold (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      : (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued))
          (current, failures)).1.groupNodes.Sublist current.groupNodes := by
    induction refs generalizing current failures with
    | nil => exact List.Sublist.refl _
    | cons ref rest ih =>
        simp only [List.foldl_cons]
        exact (ih _ _).trans (current.startGroup_groupNodes_sublist ref available)
  unfold State.startNewWork
  simp only [startStreams_groupNodes]
  exact groupFold _ _ []

/-- Activation may remove live groups but never changes their permanent registration. -/
theorem State.startNewWork_registeredGroups (queue : State) (work : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork work available).1.registeredGroups
      = queue.registeredGroups := by
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).registeredGroups = current.registeredGroups := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startStream
        split <;> rfl
  have groups (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      : (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued)) (current, failures)).1.registeredGroups
        = current.registeredGroups := by
    induction refs generalizing current failures with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons]
        exact (ih _ _).trans (current.startGroup_registeredGroups ref available)
  unfold State.startNewWork
  simp only [streams]
  exact groups _ _ []

/-- Cache exposure preserves the permanent task catalogue. -/
theorem State.cacheTaskFailures_tasks (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).tasks = queue.tasks := by
  have frame := congrArg State.tasks (queue.cacheTaskFailures_frame available)
  exact frame

/-- Group startup never changes registered task definitions. -/
theorem State.startGroup_tasks (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.tasks = queue.tasks := by
  have tasks (more : List Occurrence) (current : State)
      : (more.foldl (fun current task => current.startTask task available)
          current).tasks = current.tasks := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startTask
        split
        · rfl
        · split <;> rfl
  unfold State.startGroup
  dsimp only
  split
  · exact queue.cacheTaskFailures_tasks available
  · split
    · exact (tasks _ _).trans (queue.cacheTaskFailures_tasks available)
    · exact queue.cacheTaskFailures_tasks available

/-- Released-work activation preserves the permanent task catalogue. -/
theorem State.startNewWork_tasks (queue : State) (work : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork work available).1.tasks = queue.tasks := by
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).tasks = current.tasks := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startStream
        split <;> rfl
  have groups (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      : (refs.foldl
          (fun (current, failures) ref =>
            let (next, queued) := current.startGroup ref available
            (next, failures ++ queued)) (current, failures)).1.tasks
        = current.tasks := by
    induction refs generalizing current failures with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons]
        exact (ih _ _).trans (current.startGroup_tasks ref available)
  unfold State.startNewWork
  simp only [streams]
  exact groups _ _ []

/-- Startup retains a sublist of the previous roots when it rejects a group. -/
theorem State.startGroup_rootGroups_sublist (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    : (queue.startGroup ref available).1.rootGroups.Sublist queue.rootGroups := by
  have tasks (more : List Occurrence) (current : State)
      : (more.foldl (fun current task => current.startTask task available)
          current).rootGroups = current.rootGroups := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startTask
        split
        · rfl
        · split <;> rfl
  unfold State.startGroup
  dsimp only
  split
  · rw [State.cacheTaskFailures_rootGroups]
    exact List.Sublist.refl _
  · split
    · rw [tasks, State.cacheTaskFailures_rootGroups]
      exact List.Sublist.refl _
    · exact (List.filter_sublist.trans (by
        rw [State.cacheTaskFailures_rootGroups]
        exact List.Sublist.refl _))

/-- Active roots after release come from the old roots or the newly announced groups. -/
theorem State.startNewWork_rootGroups_sublist (queue : State) (work : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork work available).1.rootGroups.Sublist
        (queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref) := by
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).rootGroups = current.rootGroups := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih =>
        simp only [List.foldl_cons, ih]
        unfold State.startStream
        split <;> rfl
  have groups (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      : (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) (current, failures)).1.rootGroups.Sublist
          current.rootGroups := by
    induction refs generalizing current failures with
    | nil => exact List.Sublist.refl _
    | cons ref rest ih =>
        exact (ih _ _).trans (current.startGroup_rootGroups_sublist ref available)
  unfold State.startNewWork
  rw [streams]
  exact groups _ _ []

/-- With no cached rejection and no available input, activation only starts work. -/
theorem State.startNewWork_groupCore_of_no_cached_failures (queue : State)
    (work : NewWork) (clean : ∀ node ∈ queue.taskNodes, node.rejection = none)
    : (queue.startNewWork work).1.groupNodes = queue.groupNodes
      ∧ (queue.startNewWork work).1.rootGroups
        = queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref := by
  have taskStep (current : State) (task : Occurrence)
      (unrejected : ∀ node ∈ current.taskNodes, node.rejection = none)
      : (current.startTask task).groupNodes = current.groupNodes
        ∧ (current.startTask task).rootGroups = current.rootGroups
        ∧ ∀ node ∈ (current.startTask task).taskNodes, node.rejection = none := by
    unfold State.startTask
    split
    · exact ⟨rfl, rfl, unrejected⟩
    · split
      · exact ⟨rfl, rfl, unrejected⟩
      · refine ⟨rfl, rfl, ?_⟩
        intro node member
        rcases List.mem_append.mp member with old | added
        · exact unrejected node old
        · cases List.mem_singleton.mp added
          rfl
  have groupStep (current : State) (ref : NodeRef)
      (unrejected : ∀ node ∈ current.taskNodes, node.rejection = none)
      : (current.startGroup ref).1.groupNodes = current.groupNodes
        ∧ (current.startGroup ref).1.rootGroups = current.rootGroups
        ∧ ∀ node ∈ (current.startGroup ref).1.taskNodes, node.rejection = none := by
    have tasks (more : List Occurrence) (state : State)
        (unrejected : ∀ node ∈ state.taskNodes, node.rejection = none)
        : (more.foldl (fun current task => current.startTask task) state).groupNodes
            = state.groupNodes
          ∧ (more.foldl (fun current task => current.startTask task) state).rootGroups
            = state.rootGroups
          ∧ ∀ node ∈ (more.foldl (fun current task => current.startTask task) state).taskNodes,
              node.rejection = none := by
      induction more generalizing state with
      | nil => exact ⟨rfl, rfl, unrejected⟩
      | cons task rest ih =>
          have next := taskStep state task unrejected
          have later := ih _ next.2.2
          exact ⟨later.1.trans next.1, later.2.1.trans next.2.1, later.2.2⟩
    cases found : current.groupNode? ref with
    | none =>
        simpa only [State.startGroup, State.cacheTaskFailures, List.foldl_nil, found]
          using And.intro (Eq.refl current.groupNodes)
            (And.intro (Eq.refl current.rootGroups) unrejected)
    | some group =>
        have errors : group.tasks.filterMap
            (fun task => (current.taskNode? task).bind (·.rejection)) = [] := by
          apply List.filterMap_eq_nil_iff.mpr
          intro task member
          cases known : current.taskNode? task with
          | none => rfl
          | some node =>
              simp only [Option.bind_some]
              exact unrejected node (List.mem_of_find?_eq_some known)
        simpa only [State.startGroup, State.cacheTaskFailures, List.foldl_nil, found,
          errors, List.isEmpty_nil, ite_true]
          using tasks group.tasks current unrejected
  have groups (refs : NodeRefs) (current : State) (failures : List GroupFailureEvent)
      (unrejected : ∀ node ∈ current.taskNodes, node.rejection = none)
      : (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref
          (next, failures ++ queued)) (current, failures)).1.groupNodes = current.groupNodes
        ∧ (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref
          (next, failures ++ queued)) (current, failures)).1.rootGroups = current.rootGroups := by
    induction refs generalizing current failures with
    | nil => exact ⟨rfl, rfl⟩
    | cons ref rest ih =>
        have next := groupStep current ref unrejected
        have later := ih (current.startGroup ref).1
          (failures ++ (current.startGroup ref).2) next.2.2
        exact ⟨later.1.trans next.1, later.2.trans next.2.1⟩
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).groupNodes = current.groupNodes
        ∧ (refs.foldl State.startStream current).rootGroups = current.rootGroups := by
    induction refs generalizing current with
    | nil => exact ⟨rfl, rfl⟩
    | cons ref rest ih =>
        have next : (current.startStream ref).groupNodes = current.groupNodes
            ∧ (current.startStream ref).rootGroups = current.rootGroups := by
          unfold State.startStream
          split <;> exact ⟨rfl, rfl⟩
        exact ⟨(ih _).1.trans next.1, (ih _).2.trans next.2⟩
  let initial : State :=
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref }
  have groupFrame := groups (work.newGroups.map Execution.DeliveryNode.ref) initial [] clean
  unfold State.startNewWork
  exact ⟨(streams _ _).1.trans groupFrame.1, (streams _ _).2.trans groupFrame.2⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
