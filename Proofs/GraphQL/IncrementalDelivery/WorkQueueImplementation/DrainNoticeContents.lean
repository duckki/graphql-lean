import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionBoundaries

/-! Drain notices retain their exact child contents before cache-aware startup removal. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A flush notice copies the nonempty child frontier retained by pruning before startup. -/
theorem State.finishGroupSuccess_pruned_noticeContents {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (node : GroupNode) {index : Nat} {group groups streams child}
    (selected
      : (queue.finishGroupSuccess node).2.1[index]?
        = some (Execution.WorkQueueEvent.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : let finished := queue.finishGroupSuccess node
      let current := finished.1
      (∃ dependencies producer, NodeAt work child .group dependencies producer)
      ∧ ∃ kept,
          current.groupNode? child.ref = some kept
          ∧ kept.group.node = child
          ∧ kept.tasks ≠ [] := by
  have member := List.mem_of_getElem? selected
  obtain ⟨values, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output] at member
  rcases List.mem_append.mp member with value | closure
  · split at value
    · cases value
    · have impossible := List.mem_singleton.mp value
      cases impossible
  · have same := Execution.WorkQueueEvent.groupSuccess.inj (List.mem_singleton.mp closure)
    obtain ⟨known, kept, found, descriptor, contents⟩ :=
      queue.finishGroupSuccess_noticeContents generated refs records support node
        (same.2.1 ▸ noticed)
    exact ⟨known, kept, found, descriptor, contents⟩

/-- A selected drain carrier has concrete child contents before its cached child startup.
The exact ready-record witness and output prefix come from the executable drain.
-/
theorem State.drainReadyGroups_go_noticeContents {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (fuel : Nat) (available : List (Occurrence × Nat) := [])
    {index group groups streams child}
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : ∃ steps closing,
        steps < fuel
        ∧ let segment := State.drainReadyGroups.go available steps queue
          let closed := segment.1.finishGroupSuccess closing
          segment.1.rootGroups.findSome?
              (fun ref => do
                let candidate ← segment.1.groupNode? ref
                if candidate.pending == 0 then some candidate else none)
            = some closing
          ∧ (State.drainReadyGroups.go available fuel queue).2.1.take (index + 1)
            = segment.2.1 ++ closed.2.1
          ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
          ∧ ∃ node,
              closed.1.groupNode? child.ref = some node
              ∧ node.group.node = child
              ∧ node.tasks ≠ [] := by
  obtain ⟨steps, closing, strict, bound, chosen, _, _, _, _, output, exactPrefix, _⟩ :=
    State.drainReadyGroups_go_success_boundary_selected fuel queue available selected
  have metadata := State.drainReadyGroups_go_preserves
    (fun current => current.GroupRefsUnique ∧ current.GroupNodesMatchWork work
      ∧ current.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (available := available)
    (fun current node facts _ _ _ => current.finishGroupSuccess_activated_noticeMetadata
      generated facts.1 facts.2.1 facts.2.2 node available)
    ⟨refs, records, support⟩ steps
  have atFlush : ((State.drainReadyGroups.go available steps queue).1.finishGroupSuccess
      closing).2.1[strict.length]? = some (.groupSuccess group groups streams) := by
    rw [output]
    simp
  obtain ⟨located, node, found, same, contents⟩ :=
    State.finishGroupSuccess_pruned_noticeContents generated metadata.1 metadata.2.1
      metadata.2.2 closing atFlush noticed
  refine ⟨steps, closing, bound, chosen, ?_, located, node, found, same, contents⟩
  rw [List.take_add_one, selected, Option.toList_some, exactPrefix,
    List.append_assoc, ← output]

/-- Pre-startup contents exclude the same full-history publication prefix.
The certificate is taken before cancellation can remove the noticed child record.
-/
theorem State.drainReadyGroups_go_noticeContents_excluding {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (fuel : Nat) {published : List ObjectPublication} {prior : List WorkQueueEvent}
    (available : List (Occurrence × Nat) := [])
    (excluded : queue.DrainStartupMembershipsCleared fuel published available prior)
    {index group groups streams child}
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : ∃ steps closing,
        steps < fuel
        ∧ let segment := State.drainReadyGroups.go available steps queue
          let closed := segment.1.finishGroupSuccess closing
          segment.1.rootGroups.findSome?
              (fun ref => do
                let candidate ← segment.1.groupNode? ref
                if candidate.pending == 0 then some candidate else none)
            = some closing
          ∧ (State.drainReadyGroups.go available fuel queue).2.1.take (index + 1)
            = segment.2.1 ++ closed.2.1
          ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
          ∧ ∃ node,
              closed.1.groupNode? child.ref = some node
              ∧ node.group.node = child
              ∧ node.tasks ≠ []
              ∧ ∀ publication ∈
                  published.take
                    ((prior
                      ++ (State.drainReadyGroups.go available fuel queue).2.1.take
                          index).flatMap
                      WorkQueueEvent.objectValues).length,
                  publication.1 ∉ node.tasks := by
  obtain ⟨steps, closing, bound, chosen, exactPrefix, located, node, found, same, contents⟩ :=
    State.drainReadyGroups_go_noticeContents generated refs records support fuel available
      selected noticed
  refine ⟨
    steps,
    closing,
    bound,
    chosen,
    exactPrefix,
    located,
    node,
    found,
    same,
    contents,
    ?_
  ⟩
  have count : ((prior ++ (State.drainReadyGroups.go available steps queue).2.1
      ++ (State.finishGroupSuccess
        (State.drainReadyGroups.go available steps queue).1 closing).2.1).flatMap
      WorkQueueEvent.objectValues).length
      = ((prior ++ (State.drainReadyGroups.go available fuel queue).2.1.take index).flatMap
        WorkQueueEvent.objectValues).length := by
    rw [List.append_assoc, ← exactPrefix]
    simp only [List.take_add_one, selected, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil]
  intro publication member
  apply excluded steps bound closing chosen publication ?_ node
    (List.mem_of_find?_eq_some found)
  rwa [count]

/-- Generated task-success drains retain pre-startup notice contents on the shared ledger.
The eventwise source prefix and owner fold contribute their original output offsets.
-/
theorem ExecutedWork.taskSuccess_drainNoticeContents
    {work before occurrence result after published incoming index group groups streams
      child}
    (generated : ExecutedWork work)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .taskSuccess occurrence result :: after) published)
    (valid : ValidGraphEvents work (before ++ .taskSuccess occurrence result :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (released.1.startNewWork released.2.2).1
      current.taskNode? occurrence = some incoming
      → active.drainReadyGroups.2.1[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ∃ steps closing,
          steps < active.groupNodes.length
          ∧ let segment := State.drainReadyGroups.go [] steps active
            let closed := segment.1.finishGroupSuccess closing
            segment.1.rootGroups.findSome?
                (fun ref => do
                  let candidate ← segment.1.groupNode? ref
                  if candidate.pending == 0 then some candidate else none)
              = some closing
            ∧ (State.drainReadyGroups.go [] active.groupNodes.length active).2.1.take
                (index + 1)
              = segment.2.1 ++ closed.2.1
            ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
            ∧ ∃ node,
                closed.1.groupNode? child.ref = some node
                ∧ node.group.node = child
                ∧ node.tasks ≠ []
                ∧ ∀ publication ∈
                    published.take
                      (((((State.initialize (Work.fromExecution work)).rawEventReplay
                            before).2
                          ++ released.2.1)
                        ++ (State.drainReadyGroups.go [] active.groupNodes.length
                              active).2.1.take
                            index).flatMap
                        WorkQueueEvent.objectValues).length,
                    publication.1 ∉ node.tasks := by
  intro current stored prepared released active found selected noticed
  have priorValid :=
    valid.prefix (List.prefix_append before (.taskSuccess occurrence result :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.taskSuccess occurrence result]).IsPrefix
      (before ++ GraphEvent.taskSuccess occurrence result :: after) from ⟨after, by simp⟩)
  obtain ⟨refs, records, support⟩ := generated.taskSuccess_drain_noticeMetadata
    (fun _ member => priorValid.eachMatches member) matching incoming
  exact State.drainReadyGroups_go_noticeContents_excluding generated refs records support
    active.groupNodes.length []
    (createWorkQueue_taskSuccess_drainStartupMemberships covered valid found) selected
    noticed

/-- Generated item drains retain pre-startup notice contents on the shared ledger.
The leading item event contributes no object value; earlier source output keeps its offset.
-/
theorem ExecutedWork.streamItems_drainNoticeContents
    {work before stream items after published index group groups streams child}
    (generated : ExecutedWork work)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ .streamItems stream items :: after) published)
    (valid : ValidGraphEvents work (before ++ .streamItems stream items :: after))
    : let current := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared := current.preparedStreamItems items
      current.rootStreams.contains stream.ref = true
      → prepared.drainReadyGroups.2.1[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ∃ steps closing,
          steps < prepared.groupNodes.length
          ∧ let segment := State.drainReadyGroups.go [] steps prepared
            let closed := segment.1.finishGroupSuccess closing
            segment.1.rootGroups.findSome?
                (fun ref => do
                  let candidate ← segment.1.groupNode? ref
                  if candidate.pending == 0 then some candidate else none)
              = some closing
            ∧ (State.drainReadyGroups.go [] prepared.groupNodes.length prepared).2.1.take
                (index + 1)
              = segment.2.1 ++ closed.2.1
            ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
            ∧ ∃ node,
                closed.1.groupNode? child.ref = some node
                ∧ node.group.node = child
                ∧ node.tasks ≠ []
                ∧ ∀ publication ∈
                    published.take
                      ((((State.initialize (Work.fromExecution work)).rawEventReplay
                          before).2
                        ++ (State.drainReadyGroups.go [] prepared.groupNodes.length
                              prepared).2.1.take
                            index).flatMap
                        WorkQueueEvent.objectValues).length,
                    publication.1 ∉ node.tasks := by
  intro current prepared active selected noticed
  have priorValid := valid.prefix (List.prefix_append before (.streamItems stream items :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.streamItems stream items]).IsPrefix
      (before ++ GraphEvent.streamItems stream items :: after) from ⟨after, by simp⟩)
  obtain ⟨refs, records, support⟩ := generated.streamItems_prepared_noticeMetadata
    (fun _ member => priorValid.eachMatches member) matching
  exact State.drainReadyGroups_go_noticeContents_excluding generated refs records support
    prepared.groupNodes.length []
    (createWorkQueue_streamItems_drainStartupMemberships covered valid active) selected
    noticed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
