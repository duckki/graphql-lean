import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.KeyRenamingCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutKeySupply
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Causality

/-! Delivery-key maps keep structural occurrences and fixed metadata unchanged. -/

namespace AlternativeKeyRenamingChecks

open GraphQL.IncrementalDelivery Execution WorkQueueSemantics
open AlternativeWorkQueue.NativeRefinement.KeyRenaming

private def parent : DeliveryNode := ⟨4, [.field "parent"], some "deferred"⟩
private def childNode : DeliveryNode := ⟨8, [.field "parent", .field "items"], none⟩

private def nested : Work :=
  .executionGroup [⟨parent, []⟩] parent.path (.ok ([], 1))
    (.stream childNode [(.ok (.null, 2), .empty), (.error 3, .empty)])

-- Group-child edge zero is not its allocation key; stream position one is unchanged.
example
    : TaskAt (work (fun key => key + 10) nested) (.item [0] 1) [18]
        (some (.executionGroup []))
        (.item (node (fun key => key + 10) childNode) (.error 3)) := by
  refine TaskAt.item (items := [(.ok (.null, 2), .empty), (.error 3, .empty)])
    (address := [0]) (index := 1) (node := node (fun key => key + 10) childNode)
    (result := .error 3) (children := .empty) (owners := [14]) ?_ (by rfl)
  cbv

example
    : NodeAt (work (fun key => key + 10) nested) (node (fun key => key + 10) childNode)
        .stream [14] (some (.executionGroup [])) := by
  refine NodeAt.stream (address := [0])
    (items := [(.ok (.null, 2), .empty), (.error 3, .empty)]) ?_
  cbv

example : locateWork (work (fun key => key + 10) nested) [0, 2] = none := by cbv
example : (node (fun key => key + 10) parent).path = parent.path := rfl
example : (node (fun key => key + 10) parent).label = parent.label := rfl

example : (payload (fun key => key + 10) (.item childNode (.error 3))).failure = some 3 :=
  rfl

-- Soundness/coverage work even for collisions, but do not assert identity preservation.
example : StructuralKeyRenaming := structuralKeyRenaming_holds
example : (node (fun _ => 0) parent).ref = (node (fun _ => 0) childNode).ref := rfl
example : parent.ref ≠ childNode.ref := by decide

private theorem shift_injective : Function.Injective (fun key : Nat => key + 10) := by
  intro left right same
  dsimp only at same
  omega

private theorem original_item (index : Nat) (result : Result ResponseValue)
    (entry
      : [(.ok (.null, 2), Work.empty), (.error 3, .empty)][index]?
        = some (result, .empty))
    : TaskAt nested (.item [0] index) [8] (some (.executionGroup []))
        (.item childNode result) := by
  exact TaskAt.item (work := nested) (address := [0]) (node := childNode)
    (producer := some (.executionGroup [])) (owners := [4]) (by cbv) entry

private theorem original_failure
    : Causality.NodeFailed nested [.item [0] 1] (fun _ => False) 8 :=
  .task ⟨_, _, original_item 1 (.error 3) rfl⟩ (by simp) (by simp)

private theorem original_cancelled
    : Causality.TaskCancelled nested [.item [0] 1] (fun _ => False) (.item [0] 0) := by
  refine .owners ⟨_, _, original_item 0 (.ok (.null, 2)) rfl⟩ (by simp) (by simp) ?_
  intro key member
  have same : key = 8 := by simpa using member
  subst key
  exact original_failure

example
    : Causality.NodeFailed (work (fun key => key + 10) nested) [.item [0] 1]
        (fun _ => False) 18 :=
  node_failed_forward shift_injective original_failure

example
    : Causality.TaskCancelled (work (fun key => key + 10) nested) [.item [0] 1]
        (fun _ => False) (.item [0] 0) :=
  task_cancelled_forward shift_injective original_cancelled

-- Once published, this exact occurrence is protected on both sides of the same cut.
example
    : ¬Causality.TaskCancelled (work (fun key => key + 10) nested) [.item [0] 1]
        (fun occurrence => occurrence = .item [0] 0) (.item [0] 0) := by
  intro cancelled
  exact cancelled.unpublished rfl

example : CausalKeyRenaming := causalKeyRenaming_holds

example : ¬Function.Injective (fun _ : Nat => 0) := by
  intro injective
  have impossible : (4 : Nat) = 8 := injective rfl
  contradiction

-- Already-known owners/ancestors need the earlier-key branch of a piecewise map.
example : insertGap 8 2 parent.ref = parent.ref := by decide
example : insertGap 8 2 childNode.ref = 10 := by decide

example : Function.Injective (extendAtCut (insertGap 8 2) 12 3) :=
  extendAtCut_injective (insertGap_injective 8 2) 12 3

example
    : work (insertGap 8 2) (work (insertGap 12 3) nested)
      = work (extendAtCut (insertGap 8 2) 12 3) nested :=
  work_comp ..

#print axioms structuralKeyRenaming_holds
#print axioms causalKeyRenaming_holds

end AlternativeKeyRenamingChecks
