import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionBoundaries

/-! Owner-fold notices retain concrete contents at their actual intermediate boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Invert the new carrier emitted by one successful owner step
-----------------------------------------------------------------------------------------

/-- A newly emitted owner-step notice has concrete contents in that step's resulting queue.
Witness: exclude prior accumulated output, then invert the actual successful flush and
its pruned frontier. Taskless ancestor promotion is covered by the same contents theorem.
-/
theorem successGroupStep_noticeContents {work : Execution.Work}
    (generated : ExecutedWork work) (acc : State × List WorkQueueEvent × NewWork)
    (owner : Execution.DeliveryNode) (refs : acc.1.GroupRefsUnique)
    (records : acc.1.GroupNodesMatchWork work)
    (support
      : acc.1.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    {index group groups streams child}
    (selected
      : (successGroupStep acc owner).2.1[index]?
        = some (.groupSuccess group groups streams))
    (newOutput : acc.2.1.length ≤ index) (noticed : child ∈ groups)
    : (∃ dependencies producer, NodeAt work child .group dependencies producer)
      ∧ ∃ node,
          (successGroupStep acc owner).1.groupNode? child.ref = some node
          ∧ node.group.node = child
          ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true) := by
  obtain ⟨queue, events, released⟩ := acc
  dsimp only at refs records support newOutput
  dsimp only [successGroupStep] at selected ⊢
  cases found : queue.groupNode? owner.ref with
  | none =>
      simp only [found] at selected
      have inside := (List.getElem?_eq_some_iff.mp selected).1
      omega
  | some node =>
      simp only [found] at selected ⊢
      split at selected
      · rename_i ready
        simp only [ready, ↓reduceIte]
        rw [List.getElem?_append_right newOutput] at selected
        let updated := { node with pending := node.pending - 1 }
        let current := queue.putGroupNode updated
        have live := List.mem_of_find?_eq_some found
        have nextRefs : current.GroupRefsUnique := refs.putGroupNode updated
        have nextRecords : current.GroupNodesMatchWork work :=
          records.putGroupNode updated (records node live)
        have nextSupport : current.GroupRefSupport
            (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
          support.putGroupNode updated (fun empty => support.contents node live empty)
        have member := List.mem_of_getElem? selected
        obtain ⟨values, _, _, output, _, _⟩ := current.finishGroupSuccess_publications updated
        rw [output] at member
        rcases List.mem_append.mp member with value | closure
        · split at value
          · cases value
          · have impossible := List.mem_singleton.mp value
            cases impossible
        · have same := Execution.WorkQueueEvent.groupSuccess.inj (List.mem_singleton.mp closure)
          exact current.finishGroupSuccess_noticeContents generated nextRefs nextRecords
            nextSupport updated (same.2.1 ▸ noticed)
      · have inside := (List.getElem?_eq_some_iff.mp selected).1
        dsimp only at inside
        omega

-----------------------------------------------------------------------------------------
-- Recover those contents before any later owner can change the membership lists
-----------------------------------------------------------------------------------------

/-- Every carried group notice has retained tasks or a cache at its own owner boundary.
Witness: locate the emitting owner step, preserve metadata through its preceding prefix,
and inspect that step's pruned contents. The same boundary ends at the indexed carrier;
neither the final owner-fold state nor the later drain is substituted for it.
-/
theorem State.successGroupFold_noticeContents {queue : State} {work}
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (owners : List Execution.DeliveryNode) {index group groups streams child}
    (selected
      : (owners.foldl successGroupStep (queue, [], {})).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : ∃ steps,
        steps < owners.length
        ∧ let boundary := (owners.take (steps + 1)).foldl successGroupStep (queue, [], {})
          (owners.foldl successGroupStep (queue, [], {})).2.1.take (index + 1)
            = boundary.2.1
          ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
          ∧ ∃ node,
              boundary.1.groupNode? child.ref = some node
              ∧ node.group.node = child
              ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true) := by
  obtain ⟨steps, bound, lower, _, found, exactPrefix⟩ :=
    successGroupFold_event_boundary owners (queue, [], {}) selected (Nat.zero_le _)
  have next : (owners.take (steps + 1)).foldl successGroupStep (queue, [], {})
      = successGroupStep ((owners.take steps).foldl successGroupStep (queue, [], {}))
          owners[steps] := by
    rw [List.take_succ_eq_append_getElem bound, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
  rw [next] at found
  have last := successGroupStep_carrier_last _ _ found lower
  obtain ⟨currentRefs, currentRecords, currentSupport⟩ :=
    State.successGroupFold_noticeMetadata generated refs records support (owners.take steps)
  have contents := successGroupStep_noticeContents generated _ owners[steps]
    currentRefs currentRecords currentSupport found lower noticed
  refine ⟨steps, bound, ?_, ?_⟩
  · exact exactPrefix.trans (by rw [next, last, List.take_length])
  · simpa only [next] using contents

-----------------------------------------------------------------------------------------
-- Generated replay derives contents and prior-publication exclusion at the same boundary
-----------------------------------------------------------------------------------------

/-- A generated carrier retains a real child with contents and no published memberships.
Witness: generated metadata identifies the actual emitting owner boundary; the common
replay ledger excludes all prior publications there. Neither property is borrowed from
another boundary or an independently chosen publication matching. Causal readiness and
notice freshness are still separate semantic obligations.
-/
theorem ExecutedWork.taskSuccess_ownerNoticeContents
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
      let output := (incoming.task.groups.foldl successGroupStep (prepared, [], {})).2.1
      current.taskNode? occurrence = some incoming
      → current.taskHasHealthyOwner incoming.task = true
      → output[index]? = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ∃ steps,
          steps < incoming.task.groups.length
          ∧ let boundary :=
              (incoming.task.groups.take (steps + 1)).foldl successGroupStep
                (prepared, [], {})
            output.take (index + 1) = boundary.2.1
            ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
            ∧ ∃ node,
                boundary.1.groupNode? child.ref = some node
                ∧ node.group.node = child
                ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
                ∧ ∀ publication ∈
                    published.take
                      ((((State.initialize (Work.fromExecution work)).rawEventReplay
                          before).2.flatMap
                          WorkQueueEvent.objectValues).length
                        + ((output.take index).flatMap
                            WorkQueueEvent.objectValues).length),
                    publication.1 ∉ node.tasks := by
  intro current stored prepared output found healthy selected noticed
  have prior := valid.prefix (List.prefix_append before (.taskSuccess occurrence result :: after))
  obtain ⟨matching, _, _⟩ := valid.atPrefix (show
    (before ++ [GraphEvent.taskSuccess occurrence result]).IsPrefix
      (before ++ GraphEvent.taskSuccess occurrence result :: after) from ⟨after, by simp⟩)
  obtain ⟨refs, records, support⟩ :=
    generated.taskSuccess_prepared_noticeMetadata (fun _ member => prior.eachMatches member)
      matching incoming
  obtain ⟨steps, bounded, exactPrefix, located, node, lookup, same, contents⟩ :=
    State.successGroupFold_noticeContents generated refs records support incoming.task.groups
      selected noticed
  refine ⟨steps, bounded, exactPrefix, located, node, lookup, same, contents, ?_⟩
  have count : (((incoming.task.groups.take (steps + 1)).foldl successGroupStep
      (prepared, [], {})).2.1.flatMap WorkQueueEvent.objectValues).length
      = ((output.take index).flatMap WorkQueueEvent.objectValues).length := by
    rw [← exactPrefix]
    change ((output.take (index + 1)).flatMap WorkQueueEvent.objectValues).length = _
    simp only [List.take_add_one, selected, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil]
  have excluded := createWorkQueue_taskSuccess_foldMemberships covered valid found healthy
    (steps + 1) (by omega)
  dsimp only [prepared, stored, current] at count
  simp only [count] at excluded
  intro publication member
  exact excluded publication member node (List.mem_of_find?_eq_some lookup)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
