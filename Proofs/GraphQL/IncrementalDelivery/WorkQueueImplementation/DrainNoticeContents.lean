import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionBoundaries

/-! Recursive-drain carriers retain notice contents at their actual emitting boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A selected flush carrier copies the exact pruned child frontier
-----------------------------------------------------------------------------------------

/-- An indexed successful flush notice has concrete contents immediately after activation.
Witness: its carrier copies the pruning result; starting released work changes no group
records. Values preceding the carrier cannot masquerade as another successful closure.
-/
theorem State.finishGroupSuccess_activated_noticeContents {queue : State} {work}
    (generated : ExecutedWork work) (keys : queue.GroupKeysUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupKeySupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    (node : GroupNode) {index : Nat} {group groups streams child}
    (selected
      : (queue.finishGroupSuccess node).2.1[index]?
        = some (Execution.WorkQueueEvent.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : let finished := queue.finishGroupSuccess node
      let current := finished.1.startNewWork finished.2.2
      (∃ dependencies producer, NodeAt work child .group dependencies producer)
      ∧ ∃ kept,
          current.groupNode? child.key = some kept
          ∧ kept.group.node = child
          ∧ (kept.tasks ≠ [] ∨ kept.failure.isSome = true) := by
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
      queue.finishGroupSuccess_noticeContents generated keys records support node
        (same.2.1 ▸ noticed)
    refine ⟨known, kept, ?_, descriptor, contents⟩
    simpa only [State.groupNode?, (State.startNewWork_groupCore _ _).1] using found

-----------------------------------------------------------------------------------------
-- The recursive loop retains the emitting state even after earlier failure cleanup
-----------------------------------------------------------------------------------------

/-- A drain notice retains concrete child contents at the exact prefix ending at its carrier.
Witness: recurse through actual success/failure blocks. A selected successful flush ends
at its carrier; preceding blocks extend both the output offset and the iteration count.
The recovered state is before any later iteration, including later cancellation cleanup.
-/
theorem State.drainReadyGroups_go_noticeContents {queue : State} {work}
    (generated : ExecutedWork work) (keys : queue.GroupKeysUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupKeySupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    (fuel : Nat) {index group groups streams child}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : ∃ steps,
        steps < fuel
        ∧ let boundary := State.drainReadyGroups.go (steps + 1) queue
          (State.drainReadyGroups.go fuel queue).2.take (index + 1) = boundary.2
          ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
          ∧ ∃ node,
              boundary.1.groupNode? child.key = some node
              ∧ node.group.node = child
              ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true) := by
  induction fuel generalizing queue index with
  | zero => simp [State.drainReadyGroups.go] at selected
  | succ fuel ih =>
      cases ready
            : queue.rootGroups.findSome?
                (fun key => do
                  let node ← queue.groupNode? key
                  if node.failure.isSome || node.pending == 0 then
                    some node
                  else
                    none) with
      | none =>
          simp only [State.drainReadyGroups.go, ready, List.getElem?_nil] at selected
          contradiction
      | some node =>
          cases cached : node.failure with
          | none =>
              let next := (queue.finishGroupSuccess node).1.startNewWork
                (queue.finishGroupSuccess node).2.2
              let emitted := (queue.finishGroupSuccess node).2.1
              have step (count : Nat) : State.drainReadyGroups.go (count + 1) queue =
                  ((State.drainReadyGroups.go count next).1,
                    emitted ++ (State.drainReadyGroups.go count next).2) := by
                simp only [State.drainReadyGroups.go, ready, cached]
                rfl
              rw [step fuel] at selected
              by_cases inside : index < emitted.length
              · have atFlush := selected
                rw [List.getElem?_append_left inside] at atFlush
                have last := queue.finishGroupSuccess_carrier_last node atFlush
                have contents := queue.finishGroupSuccess_activated_noticeContents generated
                  keys records support node atFlush noticed
                refine ⟨0, by omega, ?_, ?_⟩
                · rw [step fuel, step 0]
                  simp only [State.drainReadyGroups.go, List.append_nil]
                  rw [last, List.take_left]
                · simpa only [State.drainReadyGroups.go, ready, cached] using contents
              · have outside : emitted.length ≤ index := by omega
                rw [List.getElem?_append_right outside] at selected
                obtain ⟨nextKeys, nextRecords, nextSupport⟩ :=
                  queue.finishGroupSuccess_activated_noticeMetadata generated
                    keys records support node
                obtain ⟨steps, bound, exactPrefix, contents⟩ :=
                  ih nextKeys nextRecords nextSupport selected
                refine ⟨steps + 1, by omega, ?_, ?_⟩
                · rw [step fuel, List.take_append,
                    List.take_of_length_le (by omega : emitted.length ≤ index + 1),
                    show index + 1 - emitted.length = index - emitted.length + 1 by omega,
                    exactPrefix, step]
                · simpa only [step] using contents
          | some errors =>
              let next := (queue.finishGroupFailure node errors).1
              have step (count : Nat) : State.drainReadyGroups.go (count + 1) queue =
                  ((State.drainReadyGroups.go count next).1,
                    [.groupFailure node.group.node errors]
                      ++ (State.drainReadyGroups.go count next).2) := by
                simp only [State.drainReadyGroups.go, ready, cached]
                rfl
              rw [step fuel] at selected
              simp only [List.singleton_append] at selected
              cases index with
              | zero => cases selected
              | succ index =>
                  obtain ⟨steps, bound, exactPrefix, contents⟩ :=
                    ih (queue := next) (keys.removeGroup _) (records.removeGroup _)
                      (support.removeGroup _)
                      selected
                  refine ⟨steps + 1, by omega, ?_, ?_⟩
                  · simp only [step, List.cons_append, List.nil_append,
                      List.take_succ_cons, exactPrefix]
                  · simpa only [step] using contents

-----------------------------------------------------------------------------------------
-- Contents and publication exclusion use the same selected drain boundary
-----------------------------------------------------------------------------------------

/-- The exact drain-notice record excludes all publications preceding its carrier.
Witness: use the recovered post-carrier iteration and the supplied common prefix ledger.
The carrier contributes no object value, so its strict prefix selects the same labels.
`offset` counts object values emitted before this drain starts.
-/
theorem State.drainReadyGroups_go_noticeContents_excluding {queue : State} {work}
    (generated : ExecutedWork work) (keys : queue.GroupKeysUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupKeySupport
          (fun key => ∃ dependencies, NodeHasDependencies work key .group dependencies))
    (fuel : Nat) {published : List ObjectPublication} {offset : Nat}
    (excluded
      : ∀ steps,
          steps ≤ fuel
          → ∀ publication ∈
              published.take
                (offset
                  + ((State.drainReadyGroups.go steps queue).2.flatMap
                      WorkQueueEvent.objectValues).length),
              (State.drainReadyGroups.go steps queue).1.TaskMembershipAbsent
                publication.1)
    {index group groups streams child}
    (selected
      : (State.drainReadyGroups.go fuel queue).2[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : ∃ steps,
        steps < fuel
        ∧ let boundary := State.drainReadyGroups.go (steps + 1) queue
          (State.drainReadyGroups.go fuel queue).2.take (index + 1) = boundary.2
          ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
          ∧ ∃ node,
              boundary.1.groupNode? child.key = some node
              ∧ node.group.node = child
              ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
              ∧ ∀ publication ∈
                  published.take
                    (offset
                      + (((State.drainReadyGroups.go fuel queue).2.take index).flatMap
                          WorkQueueEvent.objectValues).length),
                  publication.1 ∉ node.tasks := by
  obtain ⟨steps, bound, exactPrefix, located, node, found, same, contents⟩ :=
    State.drainReadyGroups_go_noticeContents generated keys records support fuel selected noticed
  refine ⟨steps, bound, exactPrefix, located, node, found, same, contents, ?_⟩
  have count : ((State.drainReadyGroups.go (steps + 1) queue).2.flatMap
      WorkQueueEvent.objectValues).length
      = (((State.drainReadyGroups.go fuel queue).2.take index).flatMap
        WorkQueueEvent.objectValues).length := by
    rw [← exactPrefix]
    simp only [List.take_add_one, selected, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil]
  have cleared := excluded (steps + 1) (by omega)
  rw [count] at cleared
  intro publication member
  exact cleared publication member node (List.mem_of_find?_eq_some found)

/-- Generated task-success drains retain child contents excluding the full prior history.
Witness: derive the activated notice frame from actual replay, combine the owner-fold
offset with earlier source output, and apply the same ledger's bounded-drain exclusion.
Only the actual handler guard and indexed carrier are supplied as local observations.
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
      let active := released.1.startNewWork released.2.2
      current.taskNode? occurrence = some incoming
      → current.taskHasHealthyOwner incoming.task = true
      → active.drainReadyGroups.2[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ∃ steps,
          steps < active.groupNodes.length
          ∧ let boundary := State.drainReadyGroups.go (steps + 1) active
            active.drainReadyGroups.2.take (index + 1) = boundary.2
            ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
            ∧ ∃ node,
                boundary.1.groupNode? child.key = some node
                ∧ node.group.node = child
                ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
                ∧ ∀ publication ∈
                    published.take
                      ((((State.initialize (Work.fromExecution work)).rawEventReplay
                          before).2.flatMap
                          WorkQueueEvent.objectValues).length
                        + ((released.2.1 ++ active.drainReadyGroups.2.take index).flatMap
                            WorkQueueEvent.objectValues).length),
                    publication.1 ∉ node.tasks := by
  intro current stored prepared released active found healthy selected noticed
  have prior := valid.prefix (List.prefix_append before (.taskSuccess occurrence result :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.taskSuccess occurrence result]).IsPrefix
      (before ++ GraphEvent.taskSuccess occurrence result :: after) from ⟨after, by simp⟩)
  obtain ⟨keys, records, support⟩ := generated.taskSuccess_drain_noticeMetadata
    (fun _ member => prior.eachMatches member) matching incoming
  have excluded := createWorkQueue_taskSuccess_drainMemberships covered valid found healthy
  simp only [List.flatMap_append, List.length_append, ← Nat.add_assoc] at excluded ⊢
  exact State.drainReadyGroups_go_noticeContents_excluding generated keys records support
    active.groupNodes.length excluded selected noticed

/-- Generated item-handler drains retain child contents excluding the full prior history.
Witness: matching item integration derives the prepared frame. The leading item event
adds no object offset, and the same replay ledger excludes earlier and newly drained
object publications at the selected carrier's actual intermediate queue.
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
      current.rootStreams.contains stream.key = true
      → prepared.drainReadyGroups.2[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ∃ steps,
          steps < prepared.groupNodes.length
          ∧ let boundary := State.drainReadyGroups.go (steps + 1) prepared
            prepared.drainReadyGroups.2.take (index + 1) = boundary.2
            ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
            ∧ ∃ node,
                boundary.1.groupNode? child.key = some node
                ∧ node.group.node = child
                ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
                ∧ ∀ publication ∈
                    published.take
                      ((((State.initialize (Work.fromExecution work)).rawEventReplay
                          before).2.flatMap
                          WorkQueueEvent.objectValues).length
                        + ((prepared.drainReadyGroups.2.take index).flatMap
                            WorkQueueEvent.objectValues).length),
                    publication.1 ∉ node.tasks := by
  intro current prepared active selected noticed
  have prior := valid.prefix (List.prefix_append before (.streamItems stream items :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.streamItems stream items]).IsPrefix
      (before ++ GraphEvent.streamItems stream items :: after) from ⟨after, by simp⟩)
  obtain ⟨keys, records, support⟩ := generated.streamItems_prepared_noticeMetadata
    (fun _ member => prior.eachMatches member) matching
  exact State.drainReadyGroups_go_noticeContents_excluding generated keys records support
    prepared.groupNodes.length
    (createWorkQueue_streamItems_drainMemberships covered valid active) selected noticed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
