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

/-- Activating a successful release accounts for both old roots and its new notices.
Witness: the success closes its sole removed root; its exact notice frontier is appended
to the active roots by `startNewWork`.
-/
theorem State.finishGroupSuccess_groupNoticeTracking (queue : State) (node : GroupNode)
    : GroupNoticeTracking queue.rootGroups
        (
          (queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2,
          (queue.finishGroupSuccess node).2.1
        ) := by
  intro ref member
  rw [((queue.finishGroupSuccess node).1.startNewWork_groupCore _).2.2]
  rcases List.mem_append.mp member with old | noticed
  · rcases queue.finishGroupSuccess_tracks_roots node ref old with active | closed
    · exact .inl (List.mem_append_left _ active)
    · exact .inr (.inr closed)
  · exact .inl (List.mem_append_right _
      (by rwa [queue.finishGroupSuccess_groupNotices]))

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

/-- Failed closure accounts for the affected roots without inventing child notices.
Witness: removal retains or marks each old root; the failure's notice list is empty.
-/
theorem State.finishGroupFailure_groupNoticeTracking (queue : State) (node : GroupNode)
    (errors : Nat)
    : GroupNoticeTracking queue.rootGroups
        (
          (queue.finishGroupFailure node errors).1,
          [(queue.finishGroupFailure node errors).2]
        ) := by
  intro ref member
  have old : ref ∈ queue.rootGroups := by
    simpa [State.finishGroupFailure, rawGroupNoticeRefs] using member
  exact (queue.removeGroup_tracks_roots node.group.node.ref ref old).imp_right Or.inl

/-- Every bounded ready-group drain retains the status of all earlier and new notices.
Witness: compose actual success/failure branches and monotone cancellation history at
each recursive step. Internal notice carriers are processed before later drain output.
-/
theorem State.drainReadyGroups_go_groupNoticeTracking (fuel : Nat) (queue : State)
    : GroupNoticeTracking queue.rootGroups (State.drainReadyGroups.go fuel queue) := by
  induction fuel generalizing queue with
  | zero => exact .silent (List.Subset.refl _)
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .silent (List.Subset.refl _)
      · rename_i node selected
        cases cached : node.failure with
        | none =>
            exact (queue.finishGroupSuccess_groupNoticeTracking node).append (ih _)
              (State.drainReadyGroups_go_cancelledGroups_subset _ _)
        | some errors =>
            exact (queue.finishGroupFailure_groupNoticeTracking node errors).append (ih _)
              (State.drainReadyGroups_go_cancelledGroups_subset _ _)

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
    (result : TaskResult)
    : GroupNoticeTracking queue.rootGroups (queue.taskSuccess occurrence result) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact .silent (List.Subset.refl _)
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact .silent (List.Subset.refl _)
      · let prepared := ((queue.putTaskNode
          { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1
        let folded := node.task.groups.foldl successGroupStep (prepared, [], {})
        have roots : prepared.rootGroups = queue.rootGroups :=
          State.maybeIntegrateWork_rootGroups _ _ _
        have first : GroupNoticeTracking queue.rootGroups
            (folded.1.startNewWork folded.2.2, folded.2.1) := by
          intro ref member
          rw [(folded.1.startNewWork_groupCore _).2.2]
          rcases List.mem_append.mp member with old | noticed
          · rcases prepared.successGroupFold_tracks_roots node.task.groups ref
                (roots.symm ▸ old) with active | closed
            · exact .inl (List.mem_append_left _ active)
            · exact .inr (.inr closed)
          · exact .inl (List.mem_append_right _
              ((successGroupFold_groupNotices prepared node.task.groups).symm ▸ noticed))
        exact first.append (State.drainReadyGroups_go_groupNoticeTracking _ _)
          (State.drainReadyGroups_go_cancelledGroups_subset _ _)

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
Witness: ignored inputs preserve roots; accepted inputs remove only task memberships
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
      split
      · exact .silent (List.Subset.refl _)
      · have loop (groups : List Execution.DeliveryNode)
            (acc : State × List WorkQueueEvent)
            (tracked : GroupNoticeTracking queue.rootGroups acc)
            : GroupNoticeTracking queue.rootGroups
                (groups.foldl (failureGroupStep errors) acc) := by
          induction groups generalizing acc with
          | nil => exact tracked
          | cons group rest ih => exact ih _ (tracked.failedOwner errors group)
        exact loop _ _ (.silent (List.Subset.refl _))

-----------------------------------------------------------------------------------------
-- Item carriers activate their notices before draining or processing the next source event
-----------------------------------------------------------------------------------------

/-- Item preparation appends exactly its combined group-notice frontier to active roots.
Witness: group/task registration and pruning leave the old root list unchanged; each
item's activation appends its own retained frontier in order.
-/
theorem State.streamItemFold_rootGroups (queue : State) (items : List StreamItem)
    : let prepared := items.foldl streamItemStep (queue, [], [], [])
      prepared.1.rootGroups
      = queue.rootGroups ++ prepared.2.1.map Execution.DeliveryNode.ref := by
  have loop (remaining : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue)
      (prior : acc.1.rootGroups = queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.ref)
      : (remaining.foldl streamItemStep acc).1.rootGroups
        = queue.rootGroups ++ (remaining.foldl streamItemStep acc).2.1.map
            Execution.DeliveryNode.ref := by
    induction remaining generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        apply ih
        obtain ⟨current, groups, streams, values⟩ := acc
        dsimp only [streamItemStep]
        rw [(State.startNewWork_groupCore _ _).2.2, State.pruneEmptyGroups_rootGroups,
          State.maybeIntegrateWork_rootGroups, prior, List.map_append, List.append_assoc]
  exact loop items (queue, [], [], []) (by simp)

/-- An item batch retains notice status across its leading carrier and subsequent drain.
Witness: the leading carrier lists exactly the roots activated by the item fold, then
the checked drain accounts for every further release, completion, or cancellation.
-/
theorem State.streamItems_groupNoticeTracking (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : GroupNoticeTracking queue.rootGroups (queue.streamItems stream items) := by
  rw [queue.streamItems_eq stream items]
  split
  · exact .silent (List.Subset.refl _)
  · let prepared := items.foldl streamItemStep (queue, [], [], [])
    have first : GroupNoticeTracking queue.rootGroups
        (prepared.1, [.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1]) := by
      intro ref member
      exact .inl (by
        rw [queue.streamItemFold_rootGroups items]
        simpa only [List.flatMap_singleton, rawGroupNoticeRefs] using member)
    exact first.append (State.drainReadyGroups_go_groupNoticeTracking _ _)
      (State.drainReadyGroups_go_cancelledGroups_subset _ _)

/-- Every source handler retains a concrete explanation for all prior and new group notices.
Witness: the three notice/accounting handlers above; stream completions do not change
group roots or announce groups. The theorem needs no validity or generated-work premise.
-/
theorem State.handleGraphEvent_groupNoticeTracking (queue : State) (event : GraphEvent)
    : GroupNoticeTracking queue.rootGroups (queue.handleGraphEvent event) := by
  cases event with
  | taskSuccess occurrence result => exact queue.taskSuccess_groupNoticeTracking _ _
  | taskFailure occurrence errors => exact queue.taskFailure_groupNoticeTracking _ _
  | streamItems stream items => exact queue.streamItems_groupNoticeTracking _ _
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> intro ref member <;> exact .inl (by simpa [rawGroupNoticeRefs] using member)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> intro ref member <;> exact .inl (by simpa [rawGroupNoticeRefs] using member)

/-- Raw source replay retains every announced group until closure or recorded cancellation.
Witness: compose actual handler tracking with monotone cancellation markers. This is
one direction of concrete lifecycle accounting, not a proof of semantic cancellation,
notice freshness, or terminal completeness.
-/
theorem State.rawEventReplay_groupNoticeTracking (queue : State)
    (events : List GraphEvent)
    : GroupNoticeTracking queue.rootGroups (queue.rawEventReplay events) := by
  induction events generalizing queue with
  | nil => exact .silent (List.Subset.refl _)
  | cons event rest ih =>
      rw [queue.rawEventReplay_cons]
      exact (queue.handleGraphEvent_groupNoticeTracking event).append (ih _)
        (by
          rw [State.rawEventReplay_state]
          exact (queue.handleGraphEvent event).1.replayGraphEvents_cancelledGroups_subset rest)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
