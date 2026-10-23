import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationMonotonicity
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Announced group refs remain active, complete, or carry a concrete cancellation marker. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Track notices without assuming they are fresh or admitted by the abstract scheduler
-----------------------------------------------------------------------------------------

/-- Every ref in `initial` or the segment's notices has a concrete endpoint explanation.
The alternatives are an active root, a recorded cancellation, or a completion in this
segment. This proof certificate allows temporary released roots and duplicate notices;
it neither assumes nor proves their semantic eligibility.
-/
def GroupNoticeTracking (initial : NodeRefs) (result : State × List WorkQueueEvent)
    : Prop :=
  ∀ ref ∈ initial ++ result.2.flatMap rawGroupNoticeRefs,
    ref ∈ result.1.rootGroups
    ∨ ref ∈ result.1.cancelledGroups
    ∨ ref ∈ result.2.flatMap rawGroupClosureRefs

/-- An unchanged root set accounts for an output-free segment.
Witness: each initial root remains active; no new notice needs an explanation.
-/
theorem GroupNoticeTracking.silent {initial queue}
    (included : initial.Subset queue.rootGroups)
    : GroupNoticeTracking initial (queue, []) := by
  intro ref member
  exact .inl (included (by simpa using member))

/-- Tracking for a larger initial notice set implies tracking for a smaller one.
Witness: new notices are unchanged, and old membership transports through the subset.
-/
theorem GroupNoticeTracking.mono {initial more result}
    (tracked : GroupNoticeTracking more result) (included : initial.Subset more)
    : GroupNoticeTracking initial result := by
  intro ref member
  apply tracked
  exact (List.mem_append.mp member).elim
    (fun old => List.mem_append_left _ (included old)) (List.mem_append_right _)

/-- An announced group that is neither active nor cancelled has an emitted completion.
Witness: eliminate the two concrete endpoint alternatives. Applying this at a notice's
exact internal boundary still requires the corresponding state and retirement evidence.
-/
theorem GroupNoticeTracking.completed_of_inactive_uncancelled {initial result ref}
    (tracked : GroupNoticeTracking initial result)
    (announced : ref ∈ initial ++ result.2.flatMap rawGroupNoticeRefs)
    (inactive : ref ∉ result.1.rootGroups)
    (uncancelled : ref ∉ result.1.cancelledGroups)
    : ref ∈ result.2.flatMap rawGroupClosureRefs :=
  ((tracked ref announced).resolve_left inactive).resolve_left uncancelled

/-- Consecutive segments retain earlier notices and their endpoint explanations.
Witness: active roots feed the next segment, cancellation markers persist, and earlier
completions remain in the concatenated output. No publication matching is involved.
-/
theorem GroupNoticeTracking.append {initial first second}
    (left : GroupNoticeTracking initial first)
    (right : GroupNoticeTracking first.1.rootGroups second)
    (cancelled : first.1.cancelledGroups.Subset second.1.cancelledGroups)
    : GroupNoticeTracking initial (second.1, first.2 ++ second.2) := by
  intro ref member
  have later (member : ref ∈ first.1.rootGroups ++ second.2.flatMap rawGroupNoticeRefs) :=
    (right ref member).imp_right
      (Or.imp_right (List.mem_append_right (first.2.flatMap rawGroupClosureRefs)))
  simp only [List.flatMap_append] at member ⊢
  rcases List.mem_append.mp member with old | noticed
  · rcases left ref (List.mem_append_left _ old) with active | removed | closed
    · exact later (List.mem_append_left _ active)
    · exact .inr (.inl (cancelled removed))
    · exact .inr (.inr (List.mem_append_left _ closed))
  · rcases List.mem_append.mp noticed with earlier | next
    · rcases left ref (List.mem_append_right _ earlier) with active | removed | closed
      · exact later (List.mem_append_left _ active)
      · exact .inr (.inl (cancelled removed))
      · exact .inr (.inr (List.mem_append_left _ closed))
    · exact later (List.mem_append_right _ next)

-----------------------------------------------------------------------------------------
-- Successful release and failure cleanup explain every removed active ref
-----------------------------------------------------------------------------------------

/-- Successful release retains every active ref except its explicitly completed group.
Witness: flushing preserves roots, pruning leaves that list unchanged, and the one-ref
filter removes exactly the ref named by the success control.
-/
theorem State.finishGroupSuccess_tracks_roots (queue : State) (node : GroupNode)
    : ∀ ref ∈ queue.rootGroups,
        ref ∈ (queue.finishGroupSuccess node).1.rootGroups
        ∨ ref ∈ (queue.finishGroupSuccess node).2.1.flatMap rawGroupClosureRefs := by
  intro ref member
  by_cases same : ref = node.group.node.ref
  · exact .inr (by rw [queue.finishGroupSuccess_groupClosureRefs node]; simp [same])
  · exact .inl (by rw [queue.finishGroupSuccess_rootGroups node]; simp [member, same])

/-- Failure removal retains an active ref or records it as cancelled.
Witness: the same removal-ref list filters roots and is appended to cancellation history.
This holds for arbitrary queue states, including stale links and shared tasks.
-/
theorem State.removeGroup_tracks_roots (queue : State) (root : Nat)
    : ∀ ref ∈ queue.rootGroups,
        ref ∈ (queue.removeGroup root).rootGroups
        ∨ ref ∈ (queue.removeGroup root).cancelledGroups := by
  intro ref member
  unfold State.removeGroup
  dsimp only
  by_cases removed :
    ref ∈ removeGroup.collect (queue.groupNodes.length + 1) queue [root] []
  · exact .inr (List.mem_append_right _ removed)
  · exact .inl (List.mem_filter.mpr ⟨member, by simpa using removed⟩)

/-- Starting a released group retains each old root or records its cancellation.
Witness: cache exposure and task starts preserve root refs; failed startup uses the exact
same removed-ref list for the root filter and cancellation history.
-/
theorem State.startGroup_tracks_roots (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : ∀ root ∈ queue.rootGroups,
        root ∈ (queue.startGroup ref available).1.rootGroups
        ∨ root ∈ (queue.startGroup ref available).1.cancelledGroups := by
  have cachedRoots := queue.cacheTaskFailures_rootGroups available
  unfold State.startGroup
  dsimp only
  split
  · intro root member; exact .inl (by rwa [cachedRoots])
  · rename_i node found
    split
    · have roots := fold_projection State.rootGroups
        (fun current task => current.startTask task available)
        (fun current task => by unfold State.startTask; split; rfl; split <;> rfl)
        node.tasks (queue.cacheTaskFailures available)
      intro root member
      exact .inl (by rwa [roots, cachedRoots])
    · intro root member
      exact (queue.cacheTaskFailures available).removeGroup_tracks_roots _ root
        (by rwa [cachedRoots])

/-- Startup retains or cancels every old and newly announced root ref.
Witness: compose actual group startup while retaining all earlier cancellation markers;
stream activation leaves both group fields unchanged.
-/
theorem State.startNewWork_tracks_roots (queue : State) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : ∀ ref ∈ queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref,
        ref ∈ (queue.startNewWork released available).1.rootGroups
        ∨ ref ∈ (queue.startNewWork released available).1.cancelledGroups := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent) (target : NodeRef)
      (prior : target ∈ acc.1.rootGroups ∨ target ∈ acc.1.cancelledGroups)
      : target ∈ (refs.foldl step acc).1.rootGroups
        ∨ target ∈ (refs.foldl step acc).1.cancelledGroups := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        exact prior.elim (acc.1.startGroup_tracks_roots ref available target)
          (fun removed => .inr
            ((acc.1.startGroup_cancelledGroups_prefix ref available).subset removed))
  intro ref member
  let initial : State := { queue with rootGroups :=
    queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref }
  let folded := (released.newGroups.map Execution.DeliveryNode.ref).foldl step (initial, [])
  have groups := loop (released.newGroups.map Execution.DeliveryNode.ref)
    (initial, []) ref (.inl member)
  have roots := fold_projection State.rootGroups State.startStream
    (fun current ref => by unfold State.startStream; split <;> rfl)
    (released.newStreams.map Execution.DeliveryNode.ref) folded.1
  have cancelled := fold_projection State.cancelledGroups State.startStream
    (fun current ref => by unfold State.startStream; split <;> rfl)
    (released.newStreams.map Execution.DeliveryNode.ref) folded.1
  change ref ∈ ((released.newStreams.map Execution.DeliveryNode.ref).foldl
      State.startStream folded.1).rootGroups
    ∨ ref ∈ ((released.newStreams.map Execution.DeliveryNode.ref).foldl
      State.startStream folded.1).cancelledGroups
  rwa [roots, cancelled]

/-- Success and activation account for old roots and each new group notice.
Witness: success closes its removed root; startup retains or cancels every remaining and
released ref. Queued startup failures need no completion yet because removal is recorded.
-/
theorem State.finishGroupSuccess_groupNoticeTracking (queue : State) (node : GroupNode)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeTracking queue.rootGroups
        (
          ((queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2 available).1,
          (queue.finishGroupSuccess node).2.1
        ) := by
  intro ref member
  have tracked := (queue.finishGroupSuccess node).1.startNewWork_tracks_roots
    (queue.finishGroupSuccess node).2.2 available
  rcases List.mem_append.mp member with old | noticed
  · rcases queue.finishGroupSuccess_tracks_roots node ref old with active | closed
    · exact (tracked ref (List.mem_append_left _ active)).imp_right Or.inl
    · exact .inr (.inr closed)
  · exact (tracked ref (List.mem_append_right _
      (by rwa [queue.finishGroupSuccess_groupNotices]))).imp_right Or.inl

/-- Failed closure accounts for the affected roots without inventing child notices.
Witness: removal retains or marks each old root; the failure's notice list is empty.
-/
theorem State.finishGroupFailure_groupNoticeTracking (queue : State) (node : GroupNode)
    (errors : Nat)
    : GroupNoticeTracking queue.rootGroups
        (
          (queue.finishGroupFailure node errors).1,
          [.groupFailure (queue.finishGroupFailure node errors).2.group
            (queue.finishGroupFailure node errors).2.errors]
        ) := by
  intro ref member
  have old : ref ∈ queue.rootGroups := by
    simpa [State.finishGroupFailure, rawGroupNoticeRefs] using member
  exact (queue.removeGroup_tracks_roots node.group.node.ref ref old).imp_right Or.inl

/-- Each failed-owner step retains earlier notice status while closing or caching this owner.
Witness: active removal records cancelled refs; a missing or unannounced owner changes
neither roots nor output. Earlier cancellation markers remain present in every branch.
-/
theorem GroupNoticeTracking.failedOwner {initial acc}
    (tracked : GroupNoticeTracking initial acc) (errors : Nat)
    (group : Execution.DeliveryNode)
    : GroupNoticeTracking initial (failureGroupStep errors acc group) := by
  obtain ⟨queue, events⟩ := acc
  unfold failureGroupStep
  dsimp only
  split
  · exact tracked
  · rename_i node found
    split
    · exact tracked.append (queue.finishGroupFailure_groupNoticeTracking node errors)
        (List.subset_append_left _ _)
    · exact tracked

/-- Failed task handling preserves every notice's active/completed/cancelled alternative.
Witness: absent inputs preserve roots; present inputs retain the rejection on the task
before folding the checked per-owner failure rule.
-/
theorem State.taskFailure_groupNoticeTracking (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : GroupNoticeTracking queue.rootGroups (queue.taskFailure occurrence errors) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskFailure, found]
      exact .silent (List.Subset.refl _)
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent)
          (tracked : GroupNoticeTracking queue.rootGroups acc)
          : GroupNoticeTracking queue.rootGroups
              (groups.foldl (failureGroupStep errors) acc) := by
        induction groups generalizing acc with
        | nil => exact tracked
        | cons group rest ih => exact ih _ (tracked.failedOwner errors group)
      exact loop _ _ (.silent (List.Subset.refl _))

/-- Every bounded ready-group drain retains the status of all earlier and new notices.
Witness: compose actual success/failure branches and monotone cancellation history at
each recursive step. Internal notice carriers are processed before later drain output.
-/
theorem State.drainReadyGroups_go_groupNoticeTracking (fuel : Nat) (queue : State)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeTracking queue.rootGroups
        (
          (State.drainReadyGroups.go available fuel queue).1,
          (State.drainReadyGroups.go available fuel queue).2.1
        ) := by
  induction fuel generalizing queue with
  | zero => exact .silent (List.Subset.refl _)
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .silent (List.Subset.refl _)
      · rename_i node selected
        exact (queue.finishGroupSuccess_groupNoticeTracking node available).append (ih _)
          (State.drainReadyGroups_go_cancelledGroups_subset _ _ (available := available))

-----------------------------------------------------------------------------------------
-- Single-pass task handlers retain the same status before their final drain
-----------------------------------------------------------------------------------------

/-- The successful-owner fold retains each old root or emits its completion.
Witness: follow the original single-pass loop. Pending release lists do not need to be
activated between contributors, and later steps retain earlier completion events.
-/
theorem State.successGroupFold_tracks_roots (queue : State)
    (groups : List Execution.DeliveryNode)
    : ∀ ref ∈ queue.rootGroups,
        ref ∈ (groups.foldl successGroupStep (queue, [], {})).1.rootGroups
        ∨ ref
          ∈ (groups.foldl successGroupStep (queue, [], {})).2.1.flatMap
              rawGroupClosureRefs := by
  have loop (remaining : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (prior : ∀ ref ∈ queue.rootGroups,
        ref ∈ acc.1.rootGroups ∨ ref ∈ acc.2.1.flatMap rawGroupClosureRefs)
      : ∀ ref ∈ queue.rootGroups,
          ref ∈ (remaining.foldl successGroupStep acc).1.rootGroups
            ∨ ref ∈ (remaining.foldl successGroupStep acc).2.1.flatMap
                rawGroupClosureRefs := by
    induction remaining generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, events, released⟩ := acc
        unfold successGroupStep
        dsimp only
        split
        · exact prior
        · rename_i node found
          split
          · intro ref member
            rcases prior ref member with active | closed
            · rcases (current.putGroupNode
                { node with pending := node.pending - 1 }).finishGroupSuccess_tracks_roots
                  { node with pending := node.pending - 1 }
                  ref active with kept | finished
              · exact .inl kept
              · exact .inr (by rw [List.flatMap_append]; exact List.mem_append_right _ finished)
            · exact .inr (by rw [List.flatMap_append]; exact List.mem_append_left _ closed)
          · exact prior
  exact loop groups (queue, [], {}) (fun _ member => .inl member)

/-- Task success accounts for old and newly announced groups across owner release and drain.
Witness: preparation preserves roots, the owner fold closes removed roots, and activation
adds exactly its accumulated notice list before the checked recursive drain.
-/
theorem State.taskSuccess_groupNoticeTracking (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : GroupNoticeTracking queue.rootGroups
        (
          (queue.taskSuccess occurrence result available).1,
          (queue.taskSuccess occurrence result available).2.1
        ) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact .silent (List.Subset.refl _)
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let prepared := ((queue.putTaskNode
        { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let folded := node.task.groups.foldl successGroupStep (prepared, [], {})
      have roots : prepared.rootGroups = queue.rootGroups :=
        State.maybeIntegrateWork_rootGroups _ _ _
      have first : GroupNoticeTracking queue.rootGroups
          ((folded.1.startNewWork folded.2.2 available).1, folded.2.1) := by
        intro ref member
        have tracked := folded.1.startNewWork_tracks_roots folded.2.2 available
        rcases List.mem_append.mp member with old | noticed
        · rcases prepared.successGroupFold_tracks_roots node.task.groups ref
              (roots.symm ▸ old) with active | closed
          · exact (tracked ref (List.mem_append_left _ active)).imp_right Or.inl
          · exact .inr (.inr closed)
        · exact (tracked ref (List.mem_append_right _
            ((successGroupFold_groupNotices prepared node.task.groups).symm
              ▸ noticed))).imp_right Or.inl
      exact first.append (State.drainReadyGroups_go_groupNoticeTracking _ _ available)
        (State.drainReadyGroups_go_cancelledGroups_subset _ _ (available := available))

-----------------------------------------------------------------------------------------
-- Item carriers activate their notices before draining or processing the next source event
-----------------------------------------------------------------------------------------

/-- Item preparation retains each old or announced root as active or cancelled.
Witness: every item's real activation has that alternative; later integration and startup
retain earlier cancellation markers. No equality of pre- and post-startup roots is used.
-/
theorem State.streamItemFold_rootGroups (queue : State) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : let prepared :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      (queue.rootGroups ++ prepared.2.1.map Execution.DeliveryNode.ref).Subset
        (prepared.1.rootGroups ++ prepared.1.cancelledGroups) := by
  have loop (remaining : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue × List GroupFailureEvent)
      (prior : (queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.ref).Subset
        (acc.1.rootGroups ++ acc.1.cancelledGroups))
      : let final := remaining.foldl (fun acc item => streamItemStep acc item available) acc
        (queue.rootGroups ++ final.2.1.map Execution.DeliveryNode.ref).Subset
          (final.1.rootGroups ++ final.1.cancelledGroups) := by
    induction remaining generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released : NewWork := { integrated.2 with newGroups := pruned.2 }
        have roots : pruned.1.rootGroups = acc.1.rootGroups := by
          rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups]
        have tracked := pruned.1.startNewWork_tracks_roots released available
        have cancelled : acc.1.cancelledGroups.Subset
            (pruned.1.startNewWork released available).1.cancelledGroups := by
          apply List.Subset.trans _ (State.startNewWork_cancelledGroups_subset _ _ available)
          rw [State.pruneEmptyGroups_cancelledGroups, State.maybeIntegrateWork_cancelledGroups]
          exact acc.1.addGroups_cancelledGroups_subset item.work.groups
        intro ref member
        change ref ∈ queue.rootGroups ++ (acc.2.1 ++ pruned.2).map
          Execution.DeliveryNode.ref at member
        rw [List.map_append, ← List.append_assoc] at member
        rcases List.mem_append.mp member with earlier | new
        · rcases List.mem_append.mp (prior earlier) with active | removed
          · exact List.mem_append.mpr (tracked ref
              (List.mem_append_left _ (roots.symm ▸ active)))
          · exact List.mem_append_right _ (cancelled removed)
        · exact List.mem_append.mpr (tracked ref (List.mem_append_right _ new))
  exact loop items (queue, [], [], [], [])
    (by
      intro ref member
      exact List.mem_append_left _ (by simpa using member))

/-- An item batch accounts for its carrier notices before the subsequent drain.
Witness: preparation retains or cancels each carried ref; the following drain preserves
those alternatives while accounting for its own successful closures and new releases.
-/
theorem State.streamItems_groupNoticeTracking (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeTracking queue.rootGroups
        (
          (queue.streamItems stream items available).1,
          (queue.streamItems stream items available).2.1
        ) := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact .silent (List.Subset.refl _)
  · let prepared := items.foldl (fun acc item => streamItemStep acc item available)
      (queue, [], [], [], [])
    have first : GroupNoticeTracking queue.rootGroups
        (prepared.1, [.streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1]) := by
      intro ref member
      have source : ref ∈ queue.rootGroups ++ prepared.2.1.map Execution.DeliveryNode.ref := by
        simpa only [List.flatMap_singleton, rawGroupNoticeRefs] using member
      exact (List.mem_append.mp
              (queue.streamItemFold_rootGroups items available source)).imp_right
        Or.inl
    exact first.append (State.drainReadyGroups_go_groupNoticeTracking _ _ available)
      (State.drainReadyGroups_go_cancelledGroups_subset _ _ (available := available))

/-- Every source handler retains a concrete explanation for all prior and new group notices.
Witness: the three notice/accounting handlers above; stream completions do not change
group roots or announce groups. The theorem needs no validity or generated-work premise.
-/
theorem State.handleGraphEvent_groupNoticeTracking (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeTracking queue.rootGroups
        (
          (queue.handleGraphEvent event available).1,
          (queue.handleGraphEvent event available).2.1
        ) := by
  have roots := queue.cacheTaskFailures_rootGroups available
  rw [← roots]
  unfold State.handleGraphEvent
  cases event with
  | taskSuccess occurrence result =>
      exact (queue.cacheTaskFailures available).taskSuccess_groupNoticeTracking _ _ available
  | taskFailure occurrence errors =>
      exact (queue.cacheTaskFailures available).taskFailure_groupNoticeTracking _ _
  | streamItems stream items =>
      exact (queue.cacheTaskFailures available).streamItems_groupNoticeTracking _ _ available
  | streamSuccess stream =>
      simp only [State.streamSuccess]
      split <;> intro ref member <;> exact .inl (by simpa [rawGroupNoticeRefs] using member)
  | streamFailure stream errors =>
      simp only [State.streamFailure]
      split <;> intro ref member <;> exact .inl (by simpa [rawGroupNoticeRefs] using member)
  | groupFailure failure =>
      simp only [State.groupFailure]
      split
      · exact .silent (List.Subset.refl _)
      · split <;> intro ref member <;> exact .inl (by simpa [rawGroupNoticeRefs] using member)

/-- Dispatch retains notice status while storing its internal failure controls. -/
theorem State.dispatchGraphEvent_groupNoticeTracking (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeTracking queue.rootGroups (queue.dispatchGraphEvent event available) :=
  queue.handleGraphEvent_groupNoticeTracking event available

/-- Raw source replay retains every announced group until closure or recorded cancellation.
Witness: compose actual handler tracking with monotone cancellation markers. This is
one direction of concrete lifecycle accounting, not a proof of semantic cancellation,
notice freshness, or terminal completeness.
-/
theorem State.rawEventReplay_groupNoticeTracking (queue : State)
    (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeTracking queue.rootGroups (queue.rawEventReplay events available) := by
  induction events generalizing queue with
  | nil => exact .silent (List.Subset.refl _)
  | cons event rest ih =>
      rw [queue.rawEventReplay_cons _ _ available]
      exact (queue.dispatchGraphEvent_groupNoticeTracking event available).append (ih _)
        (by
          rw [State.rawEventReplay_state _ _ available]
          exact State.replayGraphEvents_cancelledGroups_subset
            (queue.dispatchGraphEvent event available).1 rest available)

/-- Appending controls with no new group notices preserves endpoint tracking.
Witness: old completions remain in the concatenated history; every still-active root
supplies the silent second segment, irrespective of its additional closing controls.
-/
theorem GroupNoticeTracking.append_noticeFree {initial result}
    (tracked : GroupNoticeTracking initial result) (controls : List WorkQueueEvent)
    (noNotices : controls.flatMap rawGroupNoticeRefs = [])
    : GroupNoticeTracking initial (result.1, result.2 ++ controls) := by
  have right : GroupNoticeTracking result.1.rootGroups (result.1, controls) := by
    intro ref member
    exact .inl (by simpa only [noNotices, List.append_nil] using member)
  exact tracked.append right (List.Subset.refl _)

/-- Actual batch replay and termination retain every announced group's status.
Witness: fixed-snapshot handler replay supplies active, completed or cancelled evidence;
termination adds no group notice and preserves queue fields.
-/
theorem State.handleGraphEvents_groupNoticeTracking (queue : State)
    (events : List GraphEvent)
    : GroupNoticeTracking queue.rootGroups (queue.handleGraphEvents events) := by
  have prior := queue.rawEventReplay_groupNoticeTracking events
    (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact .silent (List.Subset.refl _)
  · dsimp only
    split
    · exact prior.append_noticeFree [.workQueueTermination] rfl
    · exact prior

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
