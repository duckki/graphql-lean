import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledClosure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementStability

/-! Notice frontiers retain uncancelled task-bearing ancestor retirements. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each noticed group's task-bearing ancestors have retired without cancellation. -/
def State.NoticeAncestorRetirements (queue : State) (work : Execution.Work)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ ref ∈ events.flatMap rawGroupNoticeRefs,
    ∀ record dependencies,
      GroupRecordAt work record dependencies
      → record.ref = ref
      → ∀ ancestor ∈ dependencies,
          ∀ occurrence owners,
            TaskHasOwners work occurrence owners
            → ancestor ∈ owners
            → UncancelledRetirement queue ancestor

/-- Durable uncancelled retirement transports an already emitted notice frontier. -/
theorem State.NoticeAncestorRetirements.post {before after work events}
    (prior : State.NoticeAncestorRetirements before work events)
    (preserved
      : ∀ ref, UncancelledRetirement before ref → UncancelledRetirement after ref)
    : after.NoticeAncestorRetirements work events := by
  intro ref noticed record dependencies known same ancestor included occurrence owners
  intro task contributes
  exact preserved ancestor
    (prior ref noticed record dependencies known same ancestor included occurrence owners
      task contributes)

/-- A notice certificate depends only on its projected group refs. -/
theorem State.NoticeAncestorRetirements.of_noticeRefs {queue work first second}
    (prior : State.NoticeAncestorRetirements queue work first)
    (included
      : (second.flatMap rawGroupNoticeRefs).Subset (first.flatMap rawGroupNoticeRefs))
    : queue.NoticeAncestorRetirements work second :=
  fun ref noticed => prior ref (included noticed)

/-- Consecutive notice segments keep the same ancestor-retirement certificate. -/
theorem State.NoticeAncestorRetirements.append {queue work first second}
    (left : State.NoticeAncestorRetirements queue work first)
    (right : queue.NoticeAncestorRetirements work second)
    : queue.NoticeAncestorRetirements work (first ++ second) := by
  intro ref noticed
  rw [List.flatMap_append, List.mem_append] at noticed
  exact noticed.elim (left ref) (right ref)

/-- An output segment with no group notices has no ancestor-retirement obligation. -/
theorem State.NoticeAncestorRetirements.of_noNotices {queue work events}
    (absent : ∀ event ∈ events, rawGroupNoticeRefs event = [])
    : State.NoticeAncestorRetirements queue work events := by
  intro ref noticed
  obtain ⟨event, member, included⟩ := List.mem_flatMap.mp noticed
  rw [absent event member] at included
  cases included

/-- A live released frontier inherits both retired and uncancelled ancestry.
The marker certificate follows each live child's exact parent chain; no source-failure
inventory or reporting cut is needed to establish this structural fact. -/
theorem State.NoticeAncestorRetirements.of_frontier {queue work parents events}
    {frontier : List Execution.DeliveryNode} (parent : ParentCutFrame queue work parents)
    (markers : queue.UncancelledRetiredMarkers work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (notices
      : frontier.map Execution.DeliveryNode.ref = events.flatMap rawGroupNoticeRefs)
    (retired : ∀ child ∈ frontier, queue.AncestorsRetired work child.ref)
    (present
      : ∀ child ∈ frontier,
          child.ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : queue.NoticeAncestorRetirements work events := by
  intro ref noticed record dependencies known same ancestor included occurrence owners
  intro task contributes
  rw [← notices] at noticed
  obtain ⟨child, member, sameRef⟩ := List.mem_map.mp noticed
  have identity : record.ref = child.ref := same.trans sameRef.symm
  obtain ⟨node, live, atRef⟩ := List.mem_map.mp (present child member)
  exact ⟨retired child member record dependencies known identity ancestor included occurrence
    owners task contributes,
    markers.live_record_ancestors parent.safe parent.fields parent.closed parent.live canonical
      known ⟨node, live, atRef.trans identity.symm⟩ ancestor included occurrence owners
        task contributes⟩

/-- Successful closure's promoted frontier has uncancelled retired ancestors before startup. -/
theorem State.finishGroupSuccess_noticeAncestorRetirements {queue work parents}
    (parent : ParentCutFrame queue work parents)
    (markers : queue.UncancelledRetiredMarkers work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (group : GroupNode) (member : group ∈ queue.groupNodes)
    (ancestry : queue.AncestorsRetired work group.group.node.ref)
    : (queue.finishGroupSuccess group).1.NoticeAncestorRetirements work
        (queue.finishGroupSuccess group).2.1 := by
  have finalMarkers := markers.finishGroupSuccess parent.safe parent.fields parent.closed
    parent.live canonical group member
  have protectedRoots := State.finishGroupSuccess_ancestorsRetired generated parent.records
    parent.links canonical parent.live member ancestry
  exact State.NoticeAncestorRetirements.of_frontier (parent.finishGroupSuccess group) finalMarkers
    canonical (queue.finishGroupSuccess_groupNotices group) protectedRoots.2.2
    (fun child included => State.finishGroupSuccess_newGroupsPresent parent.keys group child.ref
      (List.mem_map_of_mem included))

/-- An owner fold's entire released frontier has uncancelled retired ancestry before startup. -/
theorem State.successGroupFold_noticeAncestorRetirements {queue work parents}
    (parent : ParentCutFrame queue work parents)
    (markers : queue.UncancelledRetiredMarkers work)
    (roots : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (groups : List Execution.DeliveryNode)
    : let released := groups.foldl successGroupStep (queue, [], {})
      released.1.NoticeAncestorRetirements work released.2.1 := by
  have folded := markers.successGroupFold parent canonical groups
  have present := successGroupFold_supported_rootsPresent generated parent.keys parent.records
    parent.links canonical parent.live parent.tasks roots.live.roots roots.live.support
    roots.live.present groups
  exact State.NoticeAncestorRetirements.of_frontier folded.2 folded.1 canonical
    (successGroupFold_groupNotices queue groups) (fun child member => (present.2 child member).1)
    (fun child member => (present.2 child member).2.1)

/-- Every bounded successful drain retains its notices' uncancelled ancestor retirements.
The source-derived closure frame supplies each selected group's ancestry. After that
frontier is emitted, permanent retirement carries its certificate through cached startup
and the remaining drain, independently of later notifications. -/
theorem ClosureContext.drainReadyGroups_noticeAncestorRetirements
    {queue work parents settled} (frame : ClosureContext queue work parents settled)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∉ settled)
    : (State.drainReadyGroups.go available fuel queue).1.NoticeAncestorRetirements work
        (State.drainReadyGroups.go available fuel queue).2.1 := by
  induction fuel generalizing queue with
  | zero => exact .of_noNotices (by intro event impossible; cases impossible)
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .of_noNotices (by intro event impossible; cases impossible)
      · rename_i node selected
        obtain ⟨ref, active, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? ref with
        | none => simp [found] at choice
        | some chosen =>
            simp only [found] at choice
            change (if chosen.pending == 0 then some chosen else none) = some node at choice
            split at choice
            · rename_i ready
              cases Option.some.inj choice
              have member := List.mem_of_find?_eq_some found
              have same := State.groupNode?_ref found
              have active := same ▸ active
              have zero : node.pending = 0 := beq_iff_eq.mp ready
              have closed := State.finishGroupSuccess_noticeAncestorRetirements frame.parent
                frame.markers generated canonical node member (frame.roots.live.roots _ active)
              have started := frame.finishStart generated canonical node member active zero
                available licensed
              have rest := ih started
              apply State.NoticeAncestorRetirements.append
              · apply closed.post
                intro ancestor prior
                have activeRetirement := prior.startNewWork
                  (queue.finishGroupSuccess node).2.2 available
                exact State.drainReadyGroups_go_preserves
                  (fun current => UncancelledRetirement current ancestor)
                  (fun _ group prior _ _ _ =>
                    (prior.finishGroupSuccess group).startNewWork _ available)
                  activeRetirement fuel (available := available)
              · exact rest
            · cases choice

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
