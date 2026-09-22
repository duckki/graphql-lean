import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulGroupHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainClosureBoundaries

/-! Root-ancestor and retired-record health through the actual success and item handlers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Internal fixed-inventory evidence threaded through registration, closure, and draining.
Each component is independently meaningful; no observable admission predicate is included.
-/
private structure HealthFrame (queue : State) (work : Execution.Work)
    (parents : Nat → Keys) (failed : List Occurrence)
    : Prop where
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  counts : queue.GroupErrorAccounting work failed
  retired : queue.UncancelledRetiredHealthy work failed
  roots : queue.RootAncestorsHealthy work failed

/-- Arbitrary matching registration leaves roots unchanged and preserves retired health.
Witness: combine independent metadata, exact-error, and retirement registration theorems.
-/
private theorem HealthFrame.maybeIntegrateWork {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (newWork : Work)
    (known
      : ∀ group ∈ newWork.groups,
          ∃ dependencies, GroupRecordAt work group.node dependencies)
    (parentLinks
      : ∀ group ∈ newWork.groups, group.parent = (parents group.node.key).head?)
    (producer : Option Occurrence := none)
    : HealthFrame (queue.maybeIntegrateWork newWork producer).1 work parents failed := by
  refine ⟨prior.groups.maybeIntegrateWork newWork known producer,
    prior.links.maybeIntegrateWork newWork parentLinks producer,
    prior.counts.maybeIntegrateWork newWork producer,
    prior.retired.maybeIntegrateWork newWork producer, ?_⟩
  intro key active
  rw [State.maybeIntegrateWork_rootGroups] at active
  exact prior.roots key active

/-- Activation retains the frame when released groups have healthy ancestry.
Witness: group fields and error caches are unchanged, and the new root list is explicit.
-/
private theorem HealthFrame.startNewWork {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (released : NewWork)
    (healthy : ∀ group ∈ released.newGroups, GroupAncestorsHealthy work failed group.key)
    : HealthFrame (queue.startNewWork released) work parents failed :=
  ⟨
    prior.groups.startNewWork released,
    prior.links.startNewWork released,
    prior.counts.startNewWork released,
    prior.retired.startNewWork released,
    prior.roots.startNewWork released healthy
  ⟩

/-- The recursive drain retains state health and certifies every successful carrier.
Witness: induct through the actual ready selections. Each uncached active group is healthy
by exact errors and root ancestry; its released children retain the next-step premises.
-/
private theorem HealthFrame.drainReadyGroups_go {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (fuel : Nat)
    : HealthFrame (State.drainReadyGroups.go fuel queue).1 work parents failed
      ∧ SuccessfulGroupsHealthy work failed (State.drainReadyGroups.go fuel queue).2 := by
  have loop (fuel : Nat) (current : State) (frame : HealthFrame current work parents failed)
      : HealthFrame (State.drainReadyGroups.go fuel current).1 work parents failed
        ∧ SuccessfulGroupsHealthy work failed (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => exact ⟨frame, .nil work failed⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨frame, .nil work failed⟩
        · rename_i node selected
          obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? key with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.failure.isSome || candidate.pending == 0 then
                some candidate else none) = some node at choice
              split at choice
              · cases Option.some.inj choice
                have live := List.mem_of_find?_eq_some found
                have roots := frame.roots _ (current.groupNode?_key found ▸ active)
                cases cached : node.failure with
                | none =>
                    have closed := frame.retired.finishGroupSuccess generated frame.groups
                      frame.links canonical frame.counts failedKnown live cached roots
                    have next : HealthFrame (current.finishGroupSuccess node).1
                        work parents failed :=
                      ⟨frame.groups.finishGroupSuccess _, frame.links.finishGroupSuccess _,
                        frame.counts.finishGroupSuccess _, closed.1,
                        fun key member => frame.roots key
                          (current.finishGroupSuccess_rootsSubset _ member)⟩
                    obtain ⟨final, output⟩ := ih _ (next.startNewWork _ closed.2)
                    obtain ⟨dependencies, known⟩ := frame.groups node live
                    exact ⟨final,
                      (current.finishGroupSuccess_successfulGroupsHealthy generated frame.counts
                        failedKnown live known cached roots).append output⟩
                | some errors =>
                    have next : HealthFrame (current.finishGroupFailure node errors).1
                        work parents failed :=
                      ⟨frame.groups.removeGroup _, frame.links.removeGroup _,
                        frame.counts.removeGroup _, frame.retired.removeGroup _,
                        fun key member => frame.roots key
                          (current.removeGroup_rootsSubset _ member)⟩
                    obtain ⟨final, output⟩ := ih _ next
                    exact ⟨
                      final,
                      (SuccessfulGroupsHealthy.of_noGroupSuccess
                        (by intros; simp [State.finishGroupFailure])).append
                        output
                    ⟩
              · contradiction
  exact loop fuel queue prior

/-- The full drain uses the same fixed-inventory health frame as every bounded prefix.
Witness: instantiate the executable traversal's initial live-node budget.
-/
private theorem HealthFrame.drainReadyGroups {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    : HealthFrame queue.drainReadyGroups.1 work parents failed
      ∧ SuccessfulGroupsHealthy work failed queue.drainReadyGroups.2 :=
  prior.drainReadyGroups_go generated canonical failedKnown queue.groupNodes.length

/-- Every drain group notice has healthy ancestry at its actual emission boundary.
Witness: locate the successful carrier, recover the health frame of its earlier bounded
prefix, and use that closure's pruned-frontier health. Later drain cleanup is irrelevant.
-/
private theorem HealthFrame.drainReadyGroups_noticeHealth {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    : GroupNoticeAncestorsHealthy work failed queue.drainReadyGroups.2 := by
  intro key member
  obtain ⟨event, included, noticed⟩ := List.mem_flatMap.mp member
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp included
  cases event with
  | groupSuccess group groups streams =>
      obtain ⟨steps, node, before, _, found, active, uncached, _, _, output, _⟩ :=
        State.drainReadyGroups_go_success_boundary queue.groupNodes.length queue selected
      have frame := (prior.drainReadyGroups_go generated canonical failedKnown steps).1
      have released := frame.retired.finishGroupSuccess generated frame.groups frame.links
        canonical frame.counts failedKnown (List.mem_of_find?_eq_some found) uncached
        (frame.roots _ active)
      apply State.finishGroupSuccess_noticeAncestorHealth released.2 key
      rw [output, List.flatMap_append]
      exact List.mem_append_right _ (List.mem_append_left _ noticed)
  | streamValues stream values groups streams =>
      exact False.elim (queue.drainReadyGroups_noStreamValues stream values groups streams
        (List.mem_of_getElem? selected))
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases noticed

-----------------------------------------------------------------------------------------
-- The single-pass success fold proves health at each intermediate closure
-----------------------------------------------------------------------------------------

/-- One contributor decrement either retains the frame or closes a certified healthy root.
Witness: only the pending count changes before closure; exact errors and root ancestry
justify success, including cached-failed children in the accumulated release frontier.
-/
private theorem HealthFrame.contributor {acc : State × List WorkQueueEvent × NewWork}
    {work parents failed} (prior : HealthFrame acc.1 work parents failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (released : ∀ group ∈ acc.2.2.newGroups, GroupAncestorsHealthy work failed group.key)
    (output : SuccessfulGroupsHealthy work failed acc.2.1)
    (group : Execution.DeliveryNode)
    : HealthFrame (successGroupStep acc group).1 work parents failed
      ∧ (∀ child ∈ (successGroupStep acc group).2.2.newGroups,
          GroupAncestorsHealthy work failed child.key)
      ∧ SuccessfulGroupsHealthy work failed (successGroupStep acc group).2.1 := by
  obtain ⟨current, events, newWork⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨prior, released, output⟩
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    let next := current.putGroupNode updated
    have member := List.mem_of_find?_eq_some found
    have nextFrame : HealthFrame next work parents failed :=
      ⟨prior.groups.putGroupNode _ (prior.groups node member),
        prior.links.putGroupNode _ (prior.links node member),
        prior.counts.putGroupNode _ (prior.counts.live node member),
        prior.retired.putGroupNode _, prior.roots⟩
    split
    · rename_i finishes
      have flags := Bool.and_eq_true_iff.mp finishes
      have active : node.group.node.key ∈ next.rootGroups := by
        simpa only [State.groupNode?_key found, List.contains_iff_mem]
          using (Bool.and_eq_true_iff.mp flags.1).1
      have uncached : updated.failure = none := Option.isNone_iff_eq_none.mp flags.2
      have updatedMember : updated ∈ next.groupNodes :=
        List.mem_map.mpr ⟨node, member, by simp [updated]⟩
      have closed := nextFrame.retired.finishGroupSuccess generated nextFrame.groups
        nextFrame.links canonical nextFrame.counts failedKnown updatedMember uncached
        (nextFrame.roots _ active)
      refine ⟨
        ⟨
          nextFrame.groups.finishGroupSuccess _,
          nextFrame.links.finishGroupSuccess _,
          nextFrame.counts.finishGroupSuccess _,
          closed.1,
          fun key included =>
            nextFrame.roots key (next.finishGroupSuccess_rootsSubset _ included)
        ⟩,
        ?_,
        ?_
      ⟩
      · intro child included
        exact (List.mem_append.mp included).elim (released child) (closed.2 child)
      · obtain ⟨dependencies, known⟩ := nextFrame.groups updated updatedMember
        exact output.append (next.finishGroupSuccess_successfulGroupsHealthy generated
          nextFrame.counts failedKnown updatedMember known uncached (nextFrame.roots _ active))
    · exact ⟨nextFrame, released, output⟩

/-- The actual contributor fold preserves earlier releases and the joint health frame.
Witness: induction over the single-pass fold, threading every real intermediate state.
-/
private theorem HealthFrame.successGroupFold {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    (groups : List Execution.DeliveryNode)
    : let final := groups.foldl successGroupStep (queue, [], {})
      HealthFrame final.1 work parents failed
      ∧ (∀ child ∈ final.2.2.newGroups, GroupAncestorsHealthy work failed child.key)
      ∧ SuccessfulGroupsHealthy work failed final.2.1 := by
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (frame : HealthFrame acc.1 work parents failed)
      (released : ∀ group ∈ acc.2.2.newGroups, GroupAncestorsHealthy work failed group.key)
      (output : SuccessfulGroupsHealthy work failed acc.2.1)
      : HealthFrame (more.foldl successGroupStep acc).1 work parents failed
        ∧ (∀ child ∈ (more.foldl successGroupStep acc).2.2.newGroups,
            GroupAncestorsHealthy work failed child.key)
        ∧ SuccessfulGroupsHealthy work failed (more.foldl successGroupStep acc).2.1 := by
    induction more generalizing acc with
    | nil => exact ⟨frame, released, output⟩
    | cons group rest ih =>
        have next := frame.contributor generated canonical failedKnown released output group
        exact ih _ next.1 next.2.1 next.2.2
  exact loop groups (queue, [], {}) prior (by intro group member; cases member)
    (.nil work failed)

/-- A matched task success preserves state health and certifies successful output carriers.
Witness: work integration, the actual single-pass contributor fold, activation, and the
recursive drain. No all-roots-healthy, output-admission, or availability premise is assumed.
-/
theorem State.taskSuccess_releaseHealth {queue : State} {work parents failed}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {occurrence result}
    (eventMatches : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : (queue.taskSuccess occurrence result).1.UncancelledRetiredHealthy work failed
      ∧ (queue.taskSuccess occurrence result).1.RootAncestorsHealthy work failed
      ∧ SuccessfulGroupsHealthy work failed (queue.taskSuccess occurrence result).2 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found] using And.intro retired ⟨roots, .nil work failed⟩
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact ⟨retired.removeTask _, roots, .nil work failed⟩
      · let stored := queue.putTaskNode { node with value := some result.value }
        have frame : HealthFrame stored work parents failed :=
          ⟨matching, links, counts, retired, roots⟩
        have integrated := frame.maybeIntegrateWork result.work
          (fun _ member => eventMatches.taskChildGroups_recordAt member)
          (fun _ member => eventMatches.taskChildGroups_parentCanonical canonical member)
          (some occurrence)
        have folded := integrated.successGroupFold generated canonical failedKnown node.task.groups
        have finished := (folded.1.startNewWork _ folded.2.1).drainReadyGroups
          generated canonical failedKnown
        exact ⟨finished.1.retired, finished.1.roots, folded.2.2.append finished.2⟩

/-- Task success retains the original state-health interface.
Witness: project the strengthened theorem that also certifies emitted success carriers.
-/
theorem State.taskSuccess_retiredHealth {queue : State} {work parents failed}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {occurrence result}
    (eventMatches : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : (queue.taskSuccess occurrence result).1.UncancelledRetiredHealthy work failed
      ∧ (queue.taskSuccess occurrence result).1.RootAncestorsHealthy work failed := by
  have health := queue.taskSuccess_releaseHealth retired roots generated matching links canonical
    counts failedKnown eventMatches
  exact ⟨health.1, health.2.1⟩

/-- Every task-success notice retains healthy ancestry under the accepted failure inventory.
Witness: the fold's exact release frontier supplies early notices; bounded-drain health
supplies later notices. Cached failure of the noticed child itself is permitted.
-/
theorem State.taskSuccess_noticeAncestorHealth {queue : State} {work parents failed}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {occurrence result}
    (eventMatches : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : GroupNoticeAncestorsHealthy work failed
        (queue.taskSuccess occurrence result).2 := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found, GroupNoticeAncestorsHealthy]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · simp [GroupNoticeAncestorsHealthy]
      · let stored := queue.putTaskNode { node with value := some result.value }
        have frame : HealthFrame stored work parents failed :=
          ⟨matching, links, counts, retired, roots⟩
        have integrated := frame.maybeIntegrateWork result.work
          (fun _ member => eventMatches.taskChildGroups_recordAt member)
          (fun _ member => eventMatches.taskChildGroups_parentCanonical canonical member)
          (some occurrence)
        have folded := integrated.successGroupFold generated canonical failedKnown node.task.groups
        exact (State.successGroupFold_noticeAncestorHealth folded.2.1).append
          ((folded.1.startNewWork _ folded.2.1).drainReadyGroups_noticeHealth
            generated canonical failedKnown)

-----------------------------------------------------------------------------------------
-- Stream items integrate parentless candidates, prune wrappers, and activate descendants
-----------------------------------------------------------------------------------------

/-- A matching streamed item preserves both health certificates through real pruning.
Witness: initially parentless candidates have healthy ancestry, and pruning propagates
it to descendants before activation; no no-pruning assumption is imposed.
-/
private theorem HealthFrame.integrateStreamItem_with_notices {queue work parents failed}
    (prior : HealthFrame queue work parents failed) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : HealthFrame (queue.integrateStreamItem item) work parents failed
      ∧ ∀ child ∈
          ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (queue.maybeIntegrateWork item.work).2.newGroups).2,
          GroupAncestorsHealthy work failed child.key := by
  let integrated := queue.maybeIntegrateWork item.work
  have known : ∀ group ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work group.node dependencies :=
    fun _ candidate => matching.streamItem_childGroups_recordAt member candidate
  have parentLinks : ∀ group ∈ item.work.groups,
      group.parent = (parents group.node.key).head? :=
    fun _ candidate => matching.streamItem_childGroups_parentCanonical canonical member candidate
  have frame : HealthFrame integrated.1 work parents failed :=
    prior.maybeIntegrateWork item.work known parentLinks
  have candidates := queue.maybeIntegrateWork_newGroups_ancestorsHealthy (failed := failed)
    generated canonical
    item.work known parentLinks
  have pruned := frame.retired.pruneEmptyGroups generated frame.groups frame.links canonical
    frame.counts failedKnown integrated.2.newGroups candidates
  have afterPruning : HealthFrame (integrated.1.pruneEmptyGroups integrated.2.newGroups).1
      work parents failed :=
    ⟨frame.groups.pruneEmptyGroups _, frame.links.pruneEmptyGroups _,
      frame.counts.pruneEmptyGroups _, pruned.1, by
        intro key active
        rw [State.pruneEmptyGroups_rootGroups] at active
        exact frame.roots key active⟩
  exact ⟨afterPruning.startNewWork _ pruned.2, pruned.2⟩

/-- A matching item batch preserves state health and certifies the final drain's carriers.
Witness: the exact item fold threads the same frame before activating or draining any
released group; the failed-record and root-ancestor obligations stay separate.
-/
theorem State.streamItems_releaseHealth {queue : State} {work parents failed}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.UncancelledRetiredHealthy work failed
      ∧ (queue.streamItems stream items).1.RootAncestorsHealthy work failed
      ∧ SuccessfulGroupsHealthy work failed (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, released) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups released.newGroups
    (pruned.startNewWork { released with newGroups := nonempty },
      groups ++ nonempty, streams ++ released.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (frame : HealthFrame acc.1 work parents failed)
      : HealthFrame (more.foldl step acc).1 work parents failed := by
    induction more generalizing acc with
    | nil => exact frame
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.integrateStreamItem_with_notices generated canonical failedKnown eventMatches
            (included List.mem_cons_self)).1
  unfold State.streamItems
  split
  · exact ⟨retired, roots, .nil work failed⟩
  · have frame := (loop items (fun _ member => member) (queue, [], [], [])
        ⟨matching, links, counts, retired, roots⟩).drainReadyGroups generated canonical failedKnown
    refine ⟨frame.1.retired, frame.1.roots, ?_⟩
    intro group groups streams member
    exact frame.2 group groups streams
      ((List.mem_cons.mp member).resolve_left (by intro impossible; cases impossible))

/-- Every item-carried or recursively drained group notice has healthy defer ancestry.
Witness: each item's real pruning frontier supplies its own certificate, retained in
the accumulated leading carrier; the final drain uses its exact bounded health frames.
-/
theorem State.streamItems_noticeAncestorHealth {queue : State} {work parents failed}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    : GroupNoticeAncestorsHealthy work failed (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, released) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups released.newGroups
    (pruned.startNewWork { released with newGroups := nonempty },
      groups ++ nonempty, streams ++ released.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (frame : HealthFrame acc.1 work parents failed)
      (healthy : ∀ child ∈ acc.2.1, GroupAncestorsHealthy work failed child.key)
      : HealthFrame (more.foldl step acc).1 work parents failed
        ∧ ∀ child ∈ (more.foldl step acc).2.1,
            GroupAncestorsHealthy work failed child.key := by
    induction more generalizing acc with
    | nil => exact ⟨frame, healthy⟩
    | cons item rest ih =>
        have next := frame.integrateStreamItem_with_notices generated canonical failedKnown
          eventMatches (included List.mem_cons_self)
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) _ next.1
        intro child member
        exact (List.mem_append.mp member).elim (healthy child) (next.2 child)
  unfold State.streamItems
  split
  · simp [GroupNoticeAncestorsHealthy]
  · obtain ⟨frame, healthy⟩ := loop items (fun _ member => member) (queue, [], [], [])
      ⟨matching, links, counts, retired, roots⟩ (by simp)
    have drain := frame.drainReadyGroups_noticeHealth generated canonical failedKnown
    intro key member
    rcases List.mem_append.mp member with leading | later
    · obtain ⟨child, noticed, same⟩ := List.mem_map.mp leading
      exact same ▸ healthy child noticed
    · exact drain key later

/-- Item batches retain the original state-health interface.
Witness: project the strengthened item theorem, including its final-drain carrier health.
-/
theorem State.streamItems_retiredHealth {queue : State} {work parents failed}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (counts : queue.GroupErrorAccounting work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.UncancelledRetiredHealthy work failed
      ∧ (queue.streamItems stream items).1.RootAncestorsHealthy work failed := by
  have health := queue.streamItems_releaseHealth retired roots generated matching links canonical
    counts failedKnown eventMatches
  exact ⟨health.1, health.2.1⟩

-----------------------------------------------------------------------------------------
-- Failure cleanup itself changes no previously established health fact
-----------------------------------------------------------------------------------------

/-- At a fixed failure inventory, cleanup preserves healthy uncancelled retirement.
Witness: ignored outcomes remove task memberships; the contributor fold only updates
live caches or removes groups while recording their cancellation.
-/
theorem State.UncancelledRetiredHealthy.taskFailure {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.UncancelledRetiredHealthy work failed := by
  have step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode)
      (invariant : acc.1.UncancelledRetiredHealthy work failed)
      : (failureGroupStep errors acc group).1.UncancelledRetiredHealthy work failed := by
    obtain ⟨current, events⟩ := acc
    dsimp only [failureGroupStep]
    split
    · exact invariant
    · split
      · exact invariant.removeGroup _
      · exact invariant.putGroupNode _
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (invariant : acc.1.UncancelledRetiredHealthy work failed)
      : (groups.foldl (failureGroupStep errors) acc).1.UncancelledRetiredHealthy work
          failed := by
    induction groups generalizing acc with
    | nil => exact invariant
    | cons group rest ih => exact ih _ (step acc group invariant)
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using prior
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      split
      · exact prior.removeTask occurrence
      · exact loop node.task.groups _ (prior.removeTask occurrence)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
