import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedNoticeReplay

/-! Different carriers of an owner fold or drain cannot repeat a group notice. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Separation between carriers is independent of uniqueness inside each notice list
-----------------------------------------------------------------------------------------

/-- Distinct ordered events in `events` have disjoint group-notice refs.
This proof-only property permits repeated descriptors inside one carrier; per-carrier
uniqueness is a separate obligation and is not assumed here.
-/
def GroupNoticesSeparated (events : List WorkQueueEvent) : Prop :=
  events.Pairwise
    (fun first later =>
      ∀ ref ∈ rawGroupNoticeRefs first, ref ∉ rawGroupNoticeRefs later)

/-- Two separated output segments compose when later notices exclude all earlier refs.
Witness: the pairwise append theorem, with each cross-segment ref located by flatMap.
-/
theorem GroupNoticesSeparated.append {first later}
    (left : GroupNoticesSeparated first) (right : GroupNoticesSeparated later)
    (fresh
      : ∀ ref ∈ first.flatMap rawGroupNoticeRefs, ref ∉ later.flatMap rawGroupNoticeRefs)
    : GroupNoticesSeparated (first ++ later) := by
  apply List.pairwise_append.mpr
  refine ⟨left, right, ?_⟩
  intro event member next included ref noticed repeated
  exact fresh ref (List.mem_flatMap.mpr ⟨event, member, noticed⟩)
    (List.mem_flatMap.mpr ⟨next, included, repeated⟩)

/-- An output list with no group notices has separated carriers.
Witness: any alleged notice would belong to its empty flatMap projection.
-/
theorem GroupNoticesSeparated.of_noNotices {events}
    (empty : events.flatMap rawGroupNoticeRefs = [])
    : GroupNoticesSeparated events := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj _ ref noticed
  have impossible : ref ∈ events.flatMap rawGroupNoticeRefs :=
    List.mem_flatMap.mpr ⟨events[i], List.getElem_mem hi, noticed⟩
  rw [empty] at impossible
  cases impossible

/-- A successful flush has at most one group-notice carrier.
Witness: its optional value event has no notices and its final control is a singleton.
-/
theorem State.finishGroupSuccess_groupNoticesSeparated (queue : State) (group : GroupNode)
    : GroupNoticesSeparated (queue.finishGroupSuccess group).2.1 := by
  unfold State.finishGroupSuccess
  dsimp only
  split <;> simp [GroupNoticesSeparated, rawGroupNoticeRefs]

-----------------------------------------------------------------------------------------
-- Single-pass owners protect each new carrier before processing the next owner
-----------------------------------------------------------------------------------------

/-- One owner step preserves separation and protects every accumulated notice.
Witness: a successful flush excludes all previously protected refs and immediately
certifies the ancestry of its new frontier; a counter-only step preserves both facts.
-/
theorem LiveRootFrame.successGroupStep_noticeSeparation
    {acc : State × List WorkQueueEvent × NewWork} {work parents}
    (frame : LiveRootFrame acc.1 work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (protectedNotices : acc.1.GroupNoticeAncestorsRetired work acc.2.1)
    (separated : GroupNoticesSeparated acc.2.1) (owner : Execution.DeliveryNode)
    : LiveRootFrame (successGroupStep acc owner).1 work parents
      ∧ (successGroupStep acc owner).1.GroupNoticeAncestorsRetired work
          (successGroupStep acc owner).2.1
      ∧ GroupNoticesSeparated (successGroupStep acc owner).2.1 := by
  obtain ⟨queue, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨frame, protectedNotices, separated⟩
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    let next := queue.putGroupNode updated
    have member := List.mem_of_find?_eq_some found
    have roots : next.RootAncestorsRetired work := frame.roots.mono
      (fun _ active => active) (fun _ retired => retired.putGroupNode updated)
    have present : next.RootGroupsPresent := by
      intro ref active
      rw [State.putGroupNode_refs]
      exact frame.present ref active
    have nextFrame : LiveRootFrame next work parents :=
      ⟨frame.refs.putGroupNode updated,
        frame.records.putGroupNode updated (frame.records node member),
        frame.links.putGroupNode updated (frame.links node member),
        frame.registered.putGroupNode updated (frame.registered node member),
        frame.tasks, roots,
        frame.support.putGroupNode updated (frame.support.contents node member), present⟩
    have nextProtected : next.GroupNoticeAncestorsRetired work events :=
      protectedNotices.mono (fun _ retired => retired.putGroupNode updated)
    split
    · rename_i finishes
      have active : updated.group.node.ref ∈ next.rootGroups := by
        have flags := Bool.and_eq_true_iff.mp finishes
        have same := State.groupNode?_ref found
        simpa only [updated, same, List.contains_iff_mem]
          using (Bool.and_eq_true_iff.mp flags.1).1
      have updatedMember : updated ∈ next.groupNodes :=
        List.mem_map.mpr ⟨node, member, by simp [updated]⟩
      have lookup := nextFrame.refs.groupNode?_of_mem updatedMember
      have protectedNew := State.finishGroupSuccess_noticeAncestorRetirement
        (next.finishGroupSuccess_ancestorsRetired generated nextFrame.records nextFrame.links
          canonical nextFrame.registered updatedMember (roots _ active)).2.2
      refine ⟨nextFrame.finishGroupSuccess_unactivated generated canonical lookup active,
        (nextProtected.mono (fun _ retired => retired.finishGroupSuccess updated)).append
          protectedNew, ?_⟩
      exact separated.append (next.finishGroupSuccess_groupNoticesSeparated updated)
        (fun ref noticed => nextFrame.finishGroupSuccess_noProtectedNotice generated
          canonical lookup active (nextProtected ref noticed))
    · exact ⟨nextFrame, nextProtected, separated⟩

/-- All carriers of an owner fold have disjoint group-notice refs.
Witness: each actual owner step preserves the live-root frame, protects its notices, and
excludes previous carriers, including releases waiting for end-of-fold activation.
-/
theorem LiveRootFrame.successGroupFold_noticeSeparation
    {queue work parents} (frame : LiveRootFrame queue work parents)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (owners : List Execution.DeliveryNode)
    : let folded := owners.foldl successGroupStep (queue, [], {})
      LiveRootFrame folded.1 work parents
      ∧ folded.1.GroupNoticeAncestorsRetired work folded.2.1
      ∧ GroupNoticesSeparated folded.2.1 := by
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (current : LiveRootFrame acc.1 work parents)
      (protectedNotices : acc.1.GroupNoticeAncestorsRetired work acc.2.1)
      (separated : GroupNoticesSeparated acc.2.1)
      : let folded := more.foldl successGroupStep acc
        LiveRootFrame folded.1 work parents
        ∧ folded.1.GroupNoticeAncestorsRetired work folded.2.1
        ∧ GroupNoticesSeparated folded.2.1 := by
    induction more generalizing acc with
    | nil => exact ⟨current, protectedNotices, separated⟩
    | cons owner rest ih =>
        obtain ⟨next, protectedNext, separatedNext⟩ := current.successGroupStep_noticeSeparation
          generated canonical protectedNotices separated owner
        exact ih _ next protectedNext separatedNext
  exact loop owners
    (queue, [], {})
    frame
    (by intro ref member; cases member)
    (by simp [GroupNoticesSeparated])

-----------------------------------------------------------------------------------------
-- Every bounded recursive drain excludes notices from earlier iterations
-----------------------------------------------------------------------------------------

/-- Distinct carriers in any bounded drain have disjoint group-notice refs.
Witness: each successful frontier acquires permanent ancestor protection before recursive
draining; failure cleanup emits no notices. Cached failures and taskless paths are allowed.
-/
theorem LiveRootFrame.drainReadyGroups_go_groupNoticesSeparated
    {queue work parents} (frame : LiveRootFrame queue work parents)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat)
    : GroupNoticesSeparated (State.drainReadyGroups.go fuel queue).2 := by
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go, GroupNoticesSeparated]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp [GroupNoticesSeparated]
      · rename_i node selected
        obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? ref with
        | none => simp [found] at choice
        | some candidate =>
            simp only [found] at choice
            change (if candidate.failure.isSome || candidate.pending == 0 then
              some candidate else none) = some node at choice
            split at choice
            · cases Option.some.inj choice
              have same := State.groupNode?_ref found
              cases cached : node.failure with
              | none =>
                  have next := frame.finishGroupSuccess generated canonical
                    (same ▸ found) (same ▸ active)
                  have protection := State.finishGroupSuccess_noticeAncestorRetirement
                    (queue.finishGroupSuccess_ancestorsRetired generated frame.records frame.links
                      canonical frame.registered (List.mem_of_find?_eq_some found)
                      (frame.roots _ (same ▸ active))).2.2
                  apply (queue.finishGroupSuccess_groupNoticesSeparated node).append (ih next)
                  intro child noticed
                  exact next.drainReadyGroups_go_noProtectedNotice generated canonical
                    ((protection child noticed).mono (fun _ retired => retired.startNewWork _)) fuel
              | some errors =>
                  apply (show GroupNoticesSeparated [.groupFailure node.group.node errors]
                    from by simp [GroupNoticesSeparated]).append
                      (ih (frame.removeGroup node.group.node.ref))
                  simp [rawGroupNoticeRefs]
            · contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
