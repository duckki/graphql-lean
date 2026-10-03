import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasePublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainClosureBoundaries

/-! Actual owner-fold carriers identify the intermediate queue that emitted their notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Locate the unique processed-owner boundary containing a selected raw output position
-----------------------------------------------------------------------------------------

/-- An output appended by the owner fold belongs to a concrete processed-owner interval.
Witness: the accumulating output is prefix-monotone. Follow the first step whose output
contains the index, retaining its actual queue and unchanged full-output prefix.
-/
theorem successGroupFold_event_boundary (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × NewWork) {index event}
    (selected : (groups.foldl successGroupStep acc).2.1[index]? = some event)
    (newOutput : acc.2.1.length ≤ index)
    : ∃ steps,
        steps < groups.length
        ∧ let before := (groups.take steps).foldl successGroupStep acc
          let after := (groups.take (steps + 1)).foldl successGroupStep acc
          before.2.1.length ≤ index
          ∧ index < after.2.1.length
          ∧ after.2.1[index]? = some event
          ∧ (groups.foldl successGroupStep acc).2.1.take (index + 1)
            = after.2.1.take (index + 1) := by
  induction groups generalizing acc with
  | nil =>
      have inside := (List.getElem?_eq_some_iff.mp selected).1
      simp only [List.foldl_nil] at inside
      omega
  | cons group rest ih =>
      let next := successGroupStep acc group
      by_cases inside : index < next.2.1.length
      · obtain ⟨later, same⟩ := successGroupFold_outputPrefix rest next
        have atNext : next.2.1[index]? = some event := by
          change (rest.foldl successGroupStep next).2.1[index]? = some event at selected
          rw [← same, List.getElem?_append_left inside] at selected
          exact selected
        refine ⟨0, by simp, newOutput, inside, atNext, ?_⟩
        change (rest.foldl successGroupStep next).2.1.take (index + 1)
          = next.2.1.take (index + 1)
        rw [← same, List.take_append_of_le_length (by omega)]
      · obtain ⟨steps, bound, lower, upper, found, exactPrefix⟩ :=
          ih next selected (by omega)
        refine ⟨steps + 1, by simp; omega, ?_⟩
        simpa only [List.take_succ_cons, List.foldl_cons]
          using And.intro lower (And.intro upper (And.intro found exactPrefix))

-----------------------------------------------------------------------------------------
-- A successful carrier ends its flush and therefore ends its exact owner step
-----------------------------------------------------------------------------------------

/-- A successful flush's completion carrier is its last raw event.
Witness: its exact prefix consists only of its optional value block. The carrier index
and output length follow from that prefix and the successful indexed lookup.
-/
theorem State.finishGroupSuccess_carrier_last (queue : State) (node : GroupNode)
    {index group groups streams}
    (selected
      : (queue.finishGroupSuccess node).2.1[index]?
        = some (.groupSuccess group groups streams))
    : index + 1 = (queue.finishGroupSuccess node).2.1.length := by
  obtain ⟨before, _, output, exactPrefix⟩ := queue.finishGroupSuccess_index_prefix node selected
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have prefixSize := congrArg List.length exactPrefix
  have totalSize := congrArg List.length output
  simp only [List.length_take] at prefixSize
  simp only [List.length_append, List.length_cons, List.length_nil] at totalSize
  omega

/-- A new successful carrier ends the single owner step that emitted it.
Witness: missing and counter-only owner steps append no output; the successful branch
appends exactly one flush, whose carrier is last. Earlier accumulated events are excluded
by `newOutput`, without requiring distinct descriptors or event payloads.
-/
theorem successGroupStep_carrier_last (acc : State × List WorkQueueEvent × NewWork)
    (owner : Execution.DeliveryNode) {index group groups streams}
    (selected
      : (successGroupStep acc owner).2.1[index]?
        = some (.groupSuccess group groups streams))
    (newOutput : acc.2.1.length ≤ index)
    : index + 1 = (successGroupStep acc owner).2.1.length := by
  obtain ⟨queue, events, released⟩ := acc
  dsimp only at newOutput
  dsimp only [successGroupStep] at selected ⊢
  cases found : queue.groupNode? owner.ref with
  | none =>
      simp only [found] at selected ⊢
      have inside := (List.getElem?_eq_some_iff.mp selected).1
      omega
  | some node =>
      simp only [found] at selected ⊢
      split at selected
      · rename_i ready
        simp only [ready, ↓reduceIte]
        rw [List.getElem?_append_right newOutput] at selected
        let updated := queue.putGroupNode { node with pending := node.pending - 1 }
        have last := updated.finishGroupSuccess_carrier_last
          { node with pending := node.pending - 1 } selected
        simp only [List.length_append]
        change index + 1 = events.length +
          (updated.finishGroupSuccess { node with pending := node.pending - 1 }).2.1.length
        omega
      · rename_i notReady
        simp only [notReady, Bool.false_eq_true, ↓reduceIte]
        have inside := (List.getElem?_eq_some_iff.mp selected).1
        dsimp only at inside
        omega

/-- A selected owner-fold carrier ends an exact executable prefix of the fold.
Witness: locate its processed-owner interval and use that successful step's last-event
property. The resulting queue precedes all later owners and the recursive drain.
-/
theorem successGroupFold_carrier_boundary (queue : State)
    (owners : List Execution.DeliveryNode) {index group groups streams}
    (selected
      : (owners.foldl successGroupStep (queue, [], {})).2.1[index]?
        = some (.groupSuccess group groups streams))
    : ∃ steps,
        steps < owners.length
        ∧ (owners.foldl successGroupStep (queue, [], {})).2.1.take (index + 1)
          = ((owners.take (steps + 1)).foldl successGroupStep (queue, [], {})).2.1 := by
  obtain ⟨steps, bound, lower, _, found, exactPrefix⟩ :=
    successGroupFold_event_boundary owners (queue, [], {}) selected (Nat.zero_le _)
  have next : (owners.take (steps + 1)).foldl successGroupStep (queue, [], {})
      = successGroupStep ((owners.take steps).foldl successGroupStep (queue, [], {}))
          owners[steps] := by
    rw [List.take_succ_eq_append_getElem bound, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
  rw [next] at found
  have last := successGroupStep_carrier_last _ _ found lower
  refine ⟨steps, bound, exactPrefix.trans ?_⟩
  rw [next, last, List.take_length]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
