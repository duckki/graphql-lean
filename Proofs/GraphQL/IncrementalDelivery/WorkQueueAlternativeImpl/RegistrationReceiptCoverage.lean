import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskRetention

/-! Receipt-wide rejected-task coverage follows actual per-item registration and disposal.
An earlier item's linked owner cannot become an empty shell in later item preparation.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)
private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Per-item metadata retains the reference membership frame
-----------------------------------------------------------------------------------------

/-- The actual item step appends its task catalogue without requiring eager node equality. -/
theorem streamRegistrationStep_tasks (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem)
    : (streamRegistrationStep acc item).1.queue.tasks
      = acc.1.queue.tasks ++ item.work.tasks := by
  change (({ (acc.1.maybeIntegrateWork item.work).1 with queue :=
    ((acc.1.maybeIntegrateWork item.work).1.queue.pruneEmptyGroups
      (acc.1.maybeIntegrateWork item.work).2.newGroups).1 }).startNewWork _ _ _).1.queue.tasks = _
  rw [(State.startNewWork_catalogues _ _ _ _).1,
    ReferenceWorkQueue.State.pruneEmptyGroups_tasks, State.maybeIntegrateWork_tasks]

/-- The actual item fold appends each immediate task chunk exactly once in receipt order. -/
theorem streamRegistrationFold_tasks (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc)
    : (items.foldl streamRegistrationStep acc).1.queue.tasks
      = acc.1.queue.tasks ++ items.flatMap (fun item => item.work.tasks) := by
  induction items generalizing acc with
  | nil => simp
  | cons item rest ih =>
      rw [List.foldl_cons, ih, streamRegistrationStep_tasks]
      simp only [List.flatMap_cons, List.append_assoc]

/-- Each item's registration, shell pruning and delayed starts retain the whole frame. -/
theorem streamRegistrationStep_frame {acc : StreamRegistrationAcc} {settled}
    (frame : RegistrationFrame acc.1.queue settled) (item : ReferenceWorkQueue.StreamItem)
    (covered
      : ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    : RegistrationFrame (streamRegistrationStep acc item).1.queue settled :=
  ((frame.integrate item.work covered).prune _).start _ _ _

/-- Receipt preparation preserves occurrence-indexed rejection facts independently of links. -/
theorem streamRegistrationStep_taskRejections {acc : StreamRegistrationAcc} {property}
    (prior : acc.1.queue.TaskRejectionsSatisfy property)
    (item : ReferenceWorkQueue.StreamItem)
    : (streamRegistrationStep acc item).1.queue.TaskRejectionsSatisfy property :=
  State.startNewWork_taskRejections
    ((State.maybeIntegrateWork_taskRejections prior item.work).pruneEmptyGroups _) _ _ _

/-- A previously linked, unsettled task retains each live contributing owner across an item. -/
theorem streamRegistrationStep_ownerPresent {acc : StreamRegistrationAcc}
    {settled task key} (frame : RegistrationFrame acc.1.queue settled)
    (member : task ∈ acc.1.queue.tasks) (fresh : task.occurrence ∉ settled)
    (contributes : key ∈ task.groups.map DeliveryNode.ref)
    (present : key ∈ acc.1.queue.groupNodes.map (fun node => node.group.node.ref))
    (item : ReferenceWorkQueue.StreamItem)
    (covered
      : ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    : key
      ∈ (streamRegistrationStep acc item).1.queue.groupNodes.map
          (fun node => node.group.node.ref) := by
  let registered := acc.1.maybeIntegrateWork item.work
  have registeredFrame := frame.integrate item.work covered
  have registeredMember : task ∈ registered.1.queue.tasks := by
    rw [State.maybeIntegrateWork_tasks]; exact List.mem_append_left _ member
  have registeredPresent : key ∈ registered.1.queue.groupNodes.map (fun node => node.group.node.ref) := by
    have groups := congrArg ReferenceWorkQueue.State.groupNodes
      (acc.1.maybeIntegrateWork_registrationCore item.work)
    change registered.1.queue.groupNodes = (acc.1.queue.maybeIntegrateWork item.work).1.groupNodes at groups
    rw [groups]
    exact acc.1.queue.maybeIntegrateWork_includesRefs item.work none key present
  have pruned := pruneEmptyGroups_linkedOwner_present
    (registeredFrame.links task registeredMember fresh) contributes registeredPresent registered.2.newGroups
  change key ∈ (({ registered.1 with queue := (registered.1.queue.pruneEmptyGroups
    registered.2.newGroups).1 }).startNewWork _ _ _).1.queue.groupNodes.map _
  rw [State.startNewWork_groupNodes _ _ _ acc.2.2.2.2.1]
  exact pruned

-----------------------------------------------------------------------------------------
-- Later items retain earlier ownership, so endpoint absence implies inline rejection
-----------------------------------------------------------------------------------------

/-- An existing live task owner survives the complete remaining preparation fold. -/
theorem streamRegistrationFold_ownerPresent (items : List ReferenceWorkQueue.StreamItem)
    (acc : StreamRegistrationAcc) {settled task key}
    (frame : RegistrationFrame acc.1.queue settled) (member : task ∈ acc.1.queue.tasks)
    (fresh : task.occurrence ∉ settled)
    (contributes : key ∈ task.groups.map DeliveryNode.ref)
    (present : key ∈ acc.1.queue.groupNodes.map (fun node => node.group.node.ref))
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    : key
      ∈ (items.foldl streamRegistrationStep acc).1.queue.groupNodes.map
          (fun node => node.group.node.ref) := by
  induction items generalizing acc with
  | nil => exact present
  | cons item rest ih =>
      have itemCoverage := covered item List.mem_cons_self
      have nextFrame := streamRegistrationStep_frame frame item itemCoverage
      have nextMember : task ∈ (streamRegistrationStep acc item).1.queue.tasks := by
        rw [streamRegistrationStep_tasks]; exact List.mem_append_left _ member
      exact ih _ nextFrame nextMember
        (streamRegistrationStep_ownerPresent frame member fresh contributes present item
          itemCoverage)
        (fun item listed => covered item (List.mem_cons_of_mem _ listed))

/-- If an item's newly returned task has no owner after shell pruning, it was rejected
during that item's actual registration and contributes its inline cleanup target.
-/
theorem streamRegistrationStep_ownerless_target {acc : StreamRegistrationAcc}
    {settled task} (frame : RegistrationFrame acc.1.queue settled)
    (item : ReferenceWorkQueue.StreamItem)
    (covered
      : ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (returned : task ∈ item.work.tasks) (fresh : task.occurrence ∉ settled)
    (rejections
      : acc.1.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (running : acc.1.stopped = false)
    (missing
      : ∀ owner ∈ task.groups,
          (streamRegistrationStep acc item).1.queue.groupNode? owner.ref = none)
    : .task task.occurrence ∈ (streamRegistrationStep acc item).2.2.2.2.1 := by
  let registered := acc.1.maybeIntegrateWork item.work
  have registeredFrame := frame.integrate item.work covered
  have registeredMember : task ∈ registered.1.queue.tasks := by
    rw [State.maybeIntegrateWork_tasks]; exact List.mem_append_right _ returned
  have absent : ∀ owner ∈ task.groups, registered.1.queue.groupNode? owner.ref = none := by
    intro owner contributes
    cases found : registered.1.queue.groupNode? owner.ref with
    | none => rfl
    | some node =>
        have present : owner.ref ∈ registered.1.queue.groupNodes.map (fun node => node.group.node.ref) :=
          List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found,
            ReferenceWorkQueue.State.groupNode?_ref found⟩
        have kept := pruneEmptyGroups_linkedOwner_present
          (registeredFrame.links task registeredMember fresh)
          (List.mem_map.mpr ⟨owner, contributes, rfl⟩) present registered.2.newGroups
        have nextPresent : owner.ref ∈ (streamRegistrationStep acc item).1.queue.groupNodes.map
            (fun node => node.group.node.ref) := by
          change owner.ref ∈ (({ registered.1 with queue := (registered.1.queue.pruneEmptyGroups
            registered.2.newGroups).1 }).startNewWork _ _ _).1.queue.groupNodes.map _
          rw [State.startNewWork_groupNodes _ _ _ acc.2.2.2.2.1]; exact kept
        exact False.elim (((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp
          (missing owner contributes)) nextPresent)
  have rejected := State.maybeIntegrateWork_rejected item.work none task returned absent
  have guard : registered.1.stopped = false :=
    (State.maybeIntegrateWork_stopped acc.1 item.work).trans running
  exact State.startNewWork_rejected
    {
      registered.1 with
        queue := (registered.1.queue.pruneEmptyGroups registered.2.newGroups).1
    }
    {
      registered.2.newWork with
        newGroups := (registered.1.queue.pruneEmptyGroups registered.2.newGroups).2
    }
    registered.2 acc.2.2.2.2.1 guard task rejected
    ((State.maybeIntegrateWork_taskRejections rejections item.work).pruneEmptyGroups _)
    fresh

/-- Final registration-snapshot owner absence constructs a cumulative actual cleanup target.
Later preparation cannot erase a real unsettled membership; receipt-wide deduplication
may reuse an earlier target, but cannot lose it.
-/
theorem streamRegistrationFold_ownerless_target
    (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
    {settled task} (frame : RegistrationFrame acc.1.queue settled)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (returned : task ∈ items.flatMap (fun item => item.work.tasks))
    (fresh : task.occurrence ∉ settled)
    (rejections
      : acc.1.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (running : acc.1.stopped = false)
    (unique : acc.2.2.2.2.1.Nodup)
    (missing
      : ∀ owner ∈ task.groups,
          (items.foldl streamRegistrationStep acc).1.queue.groupNode? owner.ref = none)
    : .task task.occurrence ∈ (items.foldl streamRegistrationStep acc).2.2.2.2.1 := by
  induction items generalizing acc with
  | nil => cases returned
  | cons item rest ih =>
      let next := streamRegistrationStep acc item
      have itemCoverage := covered item List.mem_cons_self
      have nextFrame := streamRegistrationStep_frame frame item itemCoverage
      have nextRunning : next.1.stopped = false :=
        (streamRegistrationStep_stopped acc item).trans running
      have nextUnique : next.2.2.2.2.1.Nodup :=
        State.startNewWork_targets_nodup _ _ _ _ unique
      have restCoverage := fun entry listed => covered entry (List.mem_cons_of_mem _ listed)
      rcases List.mem_append.mp returned with immediate | later
      · have nextMember : task ∈ next.1.queue.tasks := by
          rw [streamRegistrationStep_tasks]; exact List.mem_append_right _ immediate
        have absent : ∀ owner ∈ task.groups, next.1.queue.groupNode? owner.ref = none := by
          intro owner contributes
          cases found : next.1.queue.groupNode? owner.ref with
          | none => rfl
          | some node =>
              have present : owner.ref ∈ next.1.queue.groupNodes.map (fun node => node.group.node.ref) :=
                List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found,
                  ReferenceWorkQueue.State.groupNode?_ref found⟩
              have final := streamRegistrationFold_ownerPresent rest next nextFrame nextMember fresh
                (List.mem_map.mpr ⟨owner, contributes, rfl⟩) present restCoverage
              exact False.elim (((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp
                (missing owner contributes)) final)
        exact (streamRegistrationFold_targets_prefix rest next nextUnique).subset
          (streamRegistrationStep_ownerless_target frame item itemCoverage immediate fresh
            rejections running absent)
      · exact ih next nextFrame restCoverage later (streamRegistrationStep_taskRejections rejections item)
          nextRunning nextUnique missing

/-- A consumed receipt emits the abort of each immediate task absent at its actual
pre-drain endpoint. The proof follows the interleaved trace, not a post-hoc owner scan.
-/
theorem streamItems_ownerless_aborted {queue : Kernel} {settled stream items task}
    (frame : RegistrationFrame queue settled)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (active : queue.rootStreams.contains stream.ref = true)
    (returned : task ∈ items.flatMap (fun item => item.work.tasks))
    (fresh : task.occurrence ∉ settled)
    (rejections : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (missing
      : ∀ owner ∈ task.groups,
          (items.foldl streamRegistrationStep
            ({ queue }, [], [], [], [], [])).1.queue.groupNode?
            owner.ref
          = none)
    : .abortTask task.occurrence
      ∈ (({ queue } : State).streamItems stream items).2.2 := by
  let initial : StreamRegistrationAcc := ({ queue }, [], [], [], [], [])
  let final := items.foldl streamRegistrationStep initial
  have target := streamRegistrationFold_ownerless_target items initial frame covered returned fresh rejections
    rfl List.nodup_nil missing
  have tracked := (streamRegistrationFold_cleanupTargets items initial List.nodup_nil rfl).2
  have started : .task task.occurrence ∈ final.2.2.2.2.2.filterMap HostEffect.cleanupStart? :=
    tracked.symm ▸ target
  obtain ⟨effect, emitted, selected⟩ := List.mem_filterMap.mp started
  have same : effect = .abortTask task.occurrence := by
    cases effect <;> simp_all [HostEffect.cleanupStart?]
  rw [same] at emitted
  unfold State.streamItems
  simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_left _ (List.mem_append_left _ emitted)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
