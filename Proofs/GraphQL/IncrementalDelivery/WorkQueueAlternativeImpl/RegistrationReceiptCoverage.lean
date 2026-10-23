import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReceiptCatalogues
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StartupTaskProgress

/-! Actual receipt preparation retains an incoming task owner or aborts the task inline.
Cached startup may remove owners; source consistency and the literal cleanup fold account
for that removal without a blanket owner-survival assumption.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)
private abbrev Kernel := ReferenceWorkQueue.State

private theorem taskCatalogue {queue : Kernel} {work task}
    (matching : queue.RegisteredTasksMatch work) (member : task ∈ queue.tasks)
    : queue.task? task.occurrence = some task := by
  cases found : queue.task? task.occurrence with
  | none =>
      exact False.elim ((List.find?_eq_none.mp found task member)
        ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr rfl))
  | some canonical =>
      have same := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : ReferenceWorkQueue.Task =>
          candidate.occurrence == task.occurrence) found)
      have identical := matchedTasks_eq_of_occurrence_eq
        (matching canonical (List.mem_of_find?_eq_some found)) (matching task member) same
      exact congrArg some identical

private theorem ownerLookup {queue : Kernel} {key}
    (present : key ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : ∃ node, queue.groupNode? key = some node := by
  cases found : queue.groupNode? key with
  | some node => exact ⟨node, rfl⟩
  | none =>
      obtain ⟨node, member, same⟩ := List.mem_map.mp present
      exact False.elim (List.find?_eq_none.mp found node member (by simp [same]))

/-- Per-item registration, pruning and cached starts retain source consistency. -/
theorem streamRegistrationStep_frame {acc : StreamRegistrationAcc} {settled work}
    (frame : SourceRegistrationFrame acc.1.queue settled work)
    (item : ReferenceWorkQueue.StreamItem)
    (covered
      : ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    : SourceRegistrationFrame (streamRegistrationStep acc item available).1.queue settled
        work :=
  ((frame.integrate item.work
      (by
        intro task member key contributes; exact .inr (covered task member key contributes))
      matching).prune
    _).start
    _ _ _ available

private theorem streamRegistrationStep_taskProgress {acc : StreamRegistrationAcc}
    {settled work task} (frame : SourceRegistrationFrame acc.1.queue settled work)
    (item : ReferenceWorkQueue.StreamItem)
    (covered
      : ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (prior
      : task ∈ item.work.tasks
        ∨ (task ∈ acc.1.queue.tasks
            ∧ ∃ owner ∈ task.groups,
                ∃ group, acc.1.queue.groupNode? owner.ref = some group))
    (fresh : task.occurrence ∉ settled)
    (rejections
      : acc.1.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (running : acc.1.stopped = false) (unique : acc.2.2.2.2.1.Nodup)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ settled := by
        intro occurrence errors member; cases member)
    : (∃ owner ∈ task.groups,
        ∃ group,
          (streamRegistrationStep acc item available).1.queue.groupNode? owner.ref
          = some group)
      ∨ .task task.occurrence
        ∈ (streamRegistrationStep acc item available).2.2.2.2.1 := by
  let registered := acc.1.maybeIntegrateWork item.work
  let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
  let preparing : State := { registered.1 with queue := pruned.1 }
  let roots := { registered.2.newWork with newGroups := pruned.2 }
  have registeredFrame := frame.integrate item.work
      (by intro task member key contributes; exact .inr (covered task member key contributes)) matching
  have preparedFrame := registeredFrame.prune registered.2.newGroups
  have registeredMember : task ∈ registered.1.queue.tasks := by
    rw [State.maybeIntegrateWork_tasks]
    rcases prior with incoming | ⟨old, _⟩
    · exact List.mem_append_right _ incoming
    · exact List.mem_append_left _ old
  have preparedMember : task ∈ preparing.queue.tasks := by
    rw [ReferenceWorkQueue.State.pruneEmptyGroups_tasks]
    exact registeredMember
  have preparedRejections : preparing.queue.TaskRejectionsSatisfy
      (fun occurrence _ => occurrence ∈ settled) :=
    (State.maybeIntegrateWork_taskRejections rejections item.work).pruneEmptyGroups _
  change (∃ owner ∈ task.groups, ∃ group,
      (preparing.startNewWork roots registered.2 acc.2.2.2.2.1 available).1.queue.groupNode?
        owner.ref =
        some group)
    ∨ .task task.occurrence
        ∈ (preparing.startNewWork roots registered.2 acc.2.2.2.2.1 available).2.1
  by_cases owned :
    ∃ owner ∈ task.groups, ∃ group, registered.1.queue.groupNode? owner.ref = some group
  · obtain ⟨owner, contributes, node, lookup⟩ := owned
    have present := pruneEmptyGroups_linkedOwner_present
      (registeredFrame.links task registeredMember fresh)
      (List.mem_map.mpr ⟨owner, contributes, rfl⟩)
      (List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some lookup,
        ReferenceWorkQueue.State.groupNode?_ref lookup⟩) registered.2.newGroups
    have preparedOwned : ∃ owner ∈ task.groups, ∃ group,
        preparing.queue.groupNode? owner.ref = some group := ⟨owner, contributes, ownerLookup
          present⟩
    have unrejected : preparing.queue.TaskRejectionsSatisfy
        (fun rejected _ => rejected ≠ task.occurrence) := by
      intro node member errors rejected same
      exact fresh (same ▸ preparedRejections node member errors rejected)
    rcases startNewWork_linkedTask_progress_available preparing roots registered.2 task
        acc.2.2.2.2.1
        unique (taskCatalogue preparedFrame.matching preparedMember)
        (preparedFrame.links task preparedMember fresh) preparedOwned unrejected available
        (fun occurrence errors member same => fresh (same ▸ licensed occurrence errors member))
          with kept |
          requested
    · exact .inl kept.2
    · exact .inr requested
  · have absent
        : ∀ owner ∈ task.groups, registered.1.queue.groupNode? owner.ref = none := by
      intro owner member
      cases found : registered.1.queue.groupNode? owner.ref with
      | none => rfl
      | some group => exact False.elim (owned ⟨owner, member, group, found⟩)
    have returned : task ∈ item.work.tasks := by
      rcases prior with returned | ⟨old, owner, contributes, node, lookup⟩
      · exact returned
      · have beforePresent : owner.ref ∈ acc.1.queue.groupNodes.map (fun node =>
        node.group.node.ref) :=
          List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some lookup,
            ReferenceWorkQueue.State.groupNode?_ref lookup⟩
        have groups := congrArg ReferenceWorkQueue.State.groupNodes
          (acc.1.maybeIntegrateWork_registrationCore item.work)
        change registered.1.queue.groupNodes = (acc.1.queue.maybeIntegrateWork
          item.work).1.groupNodes
          at groups
        have afterPresent : owner.ref ∈ registered.1.queue.groupNodes.map (fun node =>
          node.group.node.ref) := by
          rw [groups]
          exact acc.1.queue.maybeIntegrateWork_includesRefs item.work none owner.ref beforePresent
        exact False.elim (((ReferenceWorkQueue.State.groupNode?_eq_none_iff _ _).mp
          (absent owner contributes)) afterPresent)
    have rejected := State.maybeIntegrateWork_rejected item.work none task returned absent
    have guard : preparing.stopped = false := (State.maybeIntegrateWork_stopped acc.1
      item.work).trans running
    exact .inr (State.startNewWork_rejected preparing roots registered.2 acc.2.2.2.2.1
      guard task rejected preparedRejections fresh available)

/-- Receipt preparation preserves an old fresh task owner or records its inline abort. -/
theorem streamRegistrationFold_existingTask_progress
    (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
    {settled work task} (frame : SourceRegistrationFrame acc.1.queue settled work)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (member : task ∈ acc.1.queue.tasks) (fresh : task.occurrence ∉ settled)
    (owned
      : ∃ owner ∈ task.groups, ∃ group, acc.1.queue.groupNode? owner.ref = some group)
    (rejections
      : acc.1.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (running : acc.1.stopped = false) (unique : acc.2.2.2.2.1.Nodup)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ settled := by
        intro occurrence errors member; cases member)
    : (∃ owner ∈ task.groups,
        ∃ group,
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc).1.queue.groupNode?
            owner.ref
          = some group)
      ∨ .task task.occurrence
        ∈ (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc).2.2.2.2.1 := by
  induction items generalizing acc with
  | nil => exact .inl owned
  | cons item rest ih =>
      let next := streamRegistrationStep acc item available
      have nextFrame := streamRegistrationStep_frame frame item (covered item List.mem_cons_self)
        (matching item List.mem_cons_self) available
      have nextUnique : next.2.2.2.2.1.Nodup :=
        State.startNewWork_targets_nodup _ _ _ _ unique available
      rcases streamRegistrationStep_taskProgress frame item (covered item List.mem_cons_self)
          (matching item List.mem_cons_self) (.inr ⟨member, owned⟩) fresh rejections running
            unique available licensed with
          kept | requested
      · have nextMember : task ∈ next.1.queue.tasks := by
          rw [streamRegistrationStep_tasks _ _ available]; exact List.mem_append_left _ member
        exact ih next nextFrame (fun item member => covered item (List.mem_cons_of_mem _ member))
          (fun item member => matching item (List.mem_cons_of_mem _ member)) nextMember kept
          (streamRegistrationStep_taskRejections rejections item available licensed)
          ((streamRegistrationStep_stopped acc item available).trans running) nextUnique
      · exact .inr ((streamRegistrationFold_targets_prefix rest next nextUnique
          available).subset requested)

private theorem streamRegistrationFold_returnedTask_progress
    (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
    {settled work task} (frame : SourceRegistrationFrame acc.1.queue settled work)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (returned : task ∈ items.flatMap (fun item => item.work.tasks))
    (fresh : task.occurrence ∉ settled)
    (rejections
      : acc.1.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (running : acc.1.stopped = false) (unique : acc.2.2.2.2.1.Nodup)
    (available : List (Occurrence × Nat) := [])
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ settled := by
        intro occurrence errors member; cases member)
    : (∃ owner ∈ task.groups,
        ∃ group,
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc).1.queue.groupNode?
            owner.ref
          = some group)
      ∨ .task task.occurrence
        ∈ (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc).2.2.2.2.1 := by
  induction items generalizing acc with
  | nil => cases returned
  | cons item rest ih =>
      let next := streamRegistrationStep acc item available
      have nextFrame := streamRegistrationStep_frame frame item (covered item List.mem_cons_self)
        (matching item List.mem_cons_self) available
      have nextUnique : next.2.2.2.2.1.Nodup :=
        State.startNewWork_targets_nodup _ _ _ _ unique available
      have restCoverage := fun item member => covered item (List.mem_cons_of_mem _ member)
      have restMatching := fun item member => matching item (List.mem_cons_of_mem _ member)
      have nextRejections :=
        streamRegistrationStep_taskRejections rejections item available licensed
      have nextRunning := (streamRegistrationStep_stopped acc item available).trans running
      rcases List.mem_append.mp returned with immediate | later
      · rcases streamRegistrationStep_taskProgress frame item (covered item List.mem_cons_self)
            (matching item List.mem_cons_self) (.inl immediate) fresh rejections running
            unique available licensed with
            kept | requested
        · have nextMember : task ∈ next.1.queue.tasks := by
            rw [streamRegistrationStep_tasks _ _ available]; exact List.mem_append_right _ immediate
          exact streamRegistrationFold_existingTask_progress rest next nextFrame restCoverage
            restMatching nextMember fresh kept nextRejections nextRunning nextUnique
            available licensed
        · exact .inr ((streamRegistrationFold_targets_prefix rest next nextUnique
          available).subset requested)
      · exact ih next nextFrame restCoverage restMatching later nextRejections nextRunning
          nextUnique

/-- Endpoint owner absence yields the task's actual cumulative inline cleanup target.
Every item's child descriptors are source-matched; cached startup failures are allowed.
-/
theorem streamRegistrationFold_ownerless_target_available
    (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
    {settled work task} (frame : SourceRegistrationFrame acc.1.queue settled work)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (returned : task ∈ items.flatMap (fun item => item.work.tasks))
    (fresh : task.occurrence ∉ settled)
    (rejections
      : acc.1.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (running : acc.1.stopped = false) (unique : acc.2.2.2.2.1.Nodup)
    (available : List (Occurrence × Nat))
    (missing
      : ∀ owner ∈ task.groups,
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            acc).1.queue.groupNode?
            owner.ref
          = none)
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ settled := by
        intro occurrence errors member; cases member)
    : .task task.occurrence
      ∈ (items.foldl (fun acc item => streamRegistrationStep acc item available)
          acc).2.2.2.2.1 := by
  rcases streamRegistrationFold_returnedTask_progress items acc frame covered matching returned
    fresh
      rejections running unique available licensed with kept | requested
  · obtain ⟨owner, member, node, found⟩ := kept
    rw [missing owner member] at found
    contradiction
  · exact requested

/-- A cumulative preparation target appears in the consumed receipt’s actual effects. -/
theorem streamItems_target_aborted_available {queue : Kernel} {stream items occurrence}
    (active : queue.rootStreams.contains stream.ref = true)
    (available : List (Occurrence × Nat))
    (target
      : .task occurrence
        ∈ (items.foldl (fun acc item => streamRegistrationStep acc item available)
            (({ queue } : State), [], [], [], [], [], [])).2.2.2.2.1)
    : .abortTask occurrence
      ∈ (({ queue } : State).streamItems stream items available).2.2.1 := by
  let initial : StreamRegistrationAcc := ({ queue }, [], [], [], [], [], [])
  let final := items.foldl (fun acc item => streamRegistrationStep acc item available) initial
  have tracked :=
    (streamRegistrationFold_cleanupTargets items initial List.nodup_nil rfl available).2
  have started : .task occurrence ∈ final.2.2.2.2.2.1.filterMap HostEffect.cleanupStart? :=
    tracked.symm ▸ target
  obtain ⟨effect, emitted, selected⟩ := List.mem_filterMap.mp started
  have same : effect = .abortTask occurrence := by
    cases effect <;> simp_all [HostEffect.cleanupStart?]
  rw [same] at emitted
  unfold State.streamItems
  simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_left _ (List.mem_append_left _ emitted)

/-- Receipt-wide owner loss emits the abort in actual preparation effects before draining. -/
theorem streamItems_ownerless_aborted_available {queue : Kernel}
    {settled work stream items task} (frame : SourceRegistrationFrame queue settled work)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (active : queue.rootStreams.contains stream.ref = true)
    (returned : task ∈ items.flatMap (fun item => item.work.tasks))
    (fresh : task.occurrence ∉ settled)
    (rejections : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (available : List (Occurrence × Nat))
    (missing
      : ∀ owner ∈ task.groups,
          (items.foldl (fun acc item => streamRegistrationStep acc item available)
            ({ queue }, [], [], [], [], [], [])).1.queue.groupNode?
            owner.ref
          = none)
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ settled := by
        intro occurrence errors member; cases member)
    : .abortTask task.occurrence
      ∈ (({ queue } : State).streamItems stream items available).2.2.1 := by
  exact streamItems_target_aborted_available active available
    (streamRegistrationFold_ownerless_target_available items
      (({ queue } : State), [], [], [], [], [], []) frame covered matching returned fresh
      rejections rfl List.nodup_nil available missing licensed)

/-- Empty-snapshot specialization for existing eventwise task receipt proofs. -/
theorem streamRegistrationFold_ownerless_target
    (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
    {settled work task} (frame : SourceRegistrationFrame acc.1.queue settled work)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (returned : task ∈ items.flatMap (fun item => item.work.tasks))
    (fresh : task.occurrence ∉ settled)
    (rejections
      : acc.1.queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (running : acc.1.stopped = false) (unique : acc.2.2.2.2.1.Nodup)
    (missing
      : ∀ owner ∈ task.groups,
          (items.foldl streamRegistrationStep acc).1.queue.groupNode? owner.ref = none)
    : .task task.occurrence ∈ (items.foldl streamRegistrationStep acc).2.2.2.2.1 :=
  streamRegistrationFold_ownerless_target_available items acc frame covered matching
    returned fresh rejections running unique [] missing

/-- Empty-snapshot specialization of the actual receipt effect projection. -/
theorem streamItems_target_aborted {queue : Kernel} {stream items occurrence}
    (active : queue.rootStreams.contains stream.ref = true)
    (target
      : .task occurrence
        ∈ (items.foldl streamRegistrationStep
            (({ queue } : State), [], [], [], [], [], [])).2.2.2.2.1)
    : .abortTask occurrence ∈ (({ queue } : State).streamItems stream items).2.2.1 :=
  streamItems_target_aborted_available active [] target

/-- Empty-snapshot specialization for existing owner-loss callers. -/
theorem streamItems_ownerless_aborted {queue : Kernel} {settled work stream items task}
    (frame : SourceRegistrationFrame queue settled work)
    (covered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = key)
    (matching
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (active : queue.rootStreams.contains stream.ref = true)
    (returned : task ∈ items.flatMap (fun item => item.work.tasks))
    (fresh : task.occurrence ∉ settled)
    (rejections : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∈ settled))
    (missing
      : ∀ owner ∈ task.groups,
          (items.foldl streamRegistrationStep
            ({ queue }, [], [], [], [], [], [])).1.queue.groupNode?
            owner.ref
          = none)
    : .abortTask task.occurrence ∈ (({ queue } : State).streamItems stream items).2.2.1 :=
  streamItems_ownerless_aborted_available frame covered matching active returned fresh
    rejections [] missing

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
