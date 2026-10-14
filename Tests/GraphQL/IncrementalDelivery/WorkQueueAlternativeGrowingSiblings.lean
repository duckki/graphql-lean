import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GrowingSiblingRefinement
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Constructed growing child witnesses from actual field execution and nested sibling
cuts. A caught inner cut shifts a later stream while preserving an earlier stream image.
No paired-child/output relation is assumed by the final witness. -/

namespace AlternativeGrowingSiblingChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors ScheduledWork

private def details (name : GraphQL.Name) (directives : List DirectiveApplication := [])
    : List FieldDetails :=
  [{ fieldName := name, arguments := [], selectionSet := [], directives := directives }]

private def cutStream (name : GraphQL.Name) :=
  ScheduledExecution.executeResponseField Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) name (details "values" [.stream]) [] [] []

private def eagerStream (name : GraphQL.Name) :=
  Semantics.executeResponseField Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) name (details "values" [.stream]) [] [] []

private def cutRequired :=
  ScheduledExecution.executeResponseField Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) "required" (details "required") [] [] []

private def eagerRequired :=
  Semantics.executeResponseField Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) "required" (details "required") [] [] []

private def streamed (name : GraphQL.Name) (key : Nat)
    : Completion (List (GraphQL.Name × ResponseValue)) :=
  {
    result := .ok ([(name, .list [])], 0),
    work :=
      .combine .empty
        (.stream { ref := key, path := [.field name] }
          [
            (.ok (.scalar "x", 0), .empty),
            (.ok (.null, 0), .empty),
            (.ok (.scalar "z", 0), .empty)
          ])
  }

private theorem cutStream_run (name : GraphQL.Name) (supply : Nat)
    : (cutStream name).run supply = (streamed name supply, supply + 1) := by cbv

private theorem eagerStream_run (name : GraphQL.Name) (supply : Nat)
    : (eagerStream name).run supply = (streamed name supply, supply + 1) := by cbv

private theorem cutRequired_run (supply : Nat)
    : cutRequired.run supply = (.error 1, supply) := by cbv

private theorem eagerRequired_run (supply : Nat)
    : eagerRequired.run supply = (.error 1, supply) := by cbv

private def continues (_ : Nat → Nat) (_ _ : Nat) : Prop := True

private theorem stream_growing (name : GraphQL.Name)
    : GrowingActionRefines continues (cutStream name) (eagerStream name) := by
  intro keys left right supplies _
  rw [cutStream_run, eagerStream_run]
  have later := supplies.advance (Nat.le_succ left)
  have boundary : keys (left + 1) = right + 1 := (supplies.fresh 1).trans
    (congrArg (· + 1) supplies.boundary)
  rw [boundary] at later
  refine ⟨
    ?_,
    keys,
    ⟨fun _ _ => rfl, later, Nat.le_succ _, Nat.le_succ _, ?_, ?_⟩,
    trivial
  ⟩
  · simp [BasicErrors.PositiveFailure, streamed]
  · intro key member
    simp [streamed, allRefs, rootRefs, hiddenRegions] at member
    subst key
    omega
  · refine ⟨ResultRefines.refl _, ?_⟩
    have descriptor : { ref := right, path := [.field name] : DeliveryNode }
        = node keys { ref := left, path := [.field name] } := by
      simp only [node, supplies.boundary]
    change WorkRefines keys (.combine .empty (.stream _ _)) (.combine .empty (.stream _ _))
    rw [descriptor]
    exact .combine .empty (.stream (.cons (ResultRefines.refl _) .empty
      (.cons (ResultRefines.refl _) .empty (.cons (ResultRefines.refl _) .empty .nil))))

private theorem required_growing
    : GrowingActionRefines continues cutRequired eagerRequired := by
  intro keys left right supplies _
  rw [cutRequired_run, eagerRequired_run]
  refine ⟨?_, keys, ⟨fun _ _ => rfl, supplies, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩,
    trivial⟩
  · simp [BasicErrors.PositiveFailure, Completion.error]
  · simp [Completion.error, allRefs, rootRefs, hiddenRegions]
  · exact ⟨ResultRefines.refl _, .empty⟩

private def innerCut := [cutRequired, cutRequired, cutStream "skipped"]
private def innerEager := [eagerRequired, eagerRequired, eagerStream "skipped"]

private theorem inner_paired : PairedGrowingActions continues innerCut innerEager :=
  .cons required_growing (.cons required_growing (.cons (stream_growing _) .nil))

private theorem inner_monotone : MonotoneAbove 0 innerEager := by
  intro action member supply _
  simp only [innerEager, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [eagerRequired_run]; exact Nat.le_refl _
  · rw [eagerRequired_run]; exact Nat.le_refl _
  · rw [eagerStream_run]
    exact Nat.le_succ _

private def wrap
    (action : StateM Nat (Completion (List (GraphQL.Name × ResponseValue)))) := do
  return (← action).catchNull ResponseValue.object
  |>.map (fun value => [("caught", value)])

private def caughtCut := wrap (cutActions List.append [] innerCut)
private def caughtEager := wrap (executeActions List.append [] innerEager)

private theorem caught_growing
    : GrowingActionRefines continues caughtCut caughtEager := by
  intro keys left right supplies _
  obtain ⟨next, related, _⟩ := growingSiblingRefinement_holds _ _ continues List.append []
    innerCut innerEager keys left right 0 inner_paired supplies trivial inner_monotone
    (Nat.zero_le _)
  refine ⟨?_, next, ?_, trivial⟩
  · change BasicErrors.PositiveFailure (caughtCut.run left).1.result
    simp only [caughtCut, wrap, innerCut, cutActions_cons, cutRequired_run, run_bind,
      StateT.run_pure, id_pure_eq, Completion.error, Completion.catchNull, Completion.map]
    simp [BasicErrors.PositiveFailure]
  · simpa only [caughtCut, caughtEager, wrap, run_bind, StateT.run_pure, id_pure_eq]
      using (related.catchNull ResponseValue.object).map
        (fun value => [("caught", value)])

private def outerCut := [cutStream "early", caughtCut, cutStream "late"]
private def outerEager := [eagerStream "early", caughtEager, eagerStream "late"]

private theorem outer_paired : PairedGrowingActions continues outerCut outerEager :=
  .cons (stream_growing _) (.cons caught_growing (.cons (stream_growing _) .nil))

private theorem outer_monotone : MonotoneAbove 0 outerEager := by
  intro action member supply _
  simp only [outerEager, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [eagerStream_run]; exact Nat.le_succ _
  · have actual : caughtEager.run supply =
        ({ result := .ok ([("caught", .null)], 2), work := .empty }, supply + 1) := by
      simp only [caughtEager, wrap, innerEager, executeActions, run_bind,
        eagerRequired_run, eagerStream_run, StateT.run_pure, id_pure_eq]
      rfl
    rw [actual]
    exact Nat.le_succ _
  · rw [eagerStream_run]; exact Nat.le_succ _

private theorem initial : SupplyMap id 17 17 :=
  ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩

-- The one existential comes outside every conclusion. Inner witnesses are constructed
-- from actual field runs and the same nested driver, not supplied as desired relations.
private theorem constructed
    : ∃ next,
        RunRefines id next 17 17 ((cutActions List.append [] outerCut).run 17)
          ((executeActions List.append [] outerEager).run 17) := by
  obtain ⟨next, related, _⟩ := growingSiblingRefinement_holds _ _ continues List.append []
    outerCut outerEager id 17 17 0 outer_paired initial trivial outer_monotone (by omega)
  exact ⟨next, related⟩

private theorem cut_final : ((cutActions List.append [] outerCut).run 17).2 = 19 := by cbv

private theorem eager_final
    : ((executeActions List.append [] outerEager).run 17).2 = 20 := by cbv

example : countedErrors ((cutActions List.append [] outerCut).run 17).1.result = 1 := by
  cbv

example
    : countedErrors ((executeActions List.append [] outerEager).run 17).1.result = 2 := by
  cbv

private theorem stream_key {keys : Nat → Nat} {before after : DeliveryNode}
    {items eagerItems}
    (known : WorkRefines keys (.stream before items) (.stream after eagerItems))
    : keys before.ref = after.ref := by
  cases known
  rfl

example
    : ∃ next,
        next 17 = 17
        ∧ next 18 = 19
        ∧ next 19 = 20
        ∧ CompletionRefines next ((cutActions List.append [] outerCut).run 17).1
            ((executeActions List.append [] outerEager).run 17).1 := by
  obtain ⟨next, related⟩ := constructed
  have endKey : next 19 = 20 := by
    simpa only [cut_final, eager_final] using related.supplies.boundary
  have before := related.completion.2.locate [0, 1]
  have after := related.completion.2.locate [1, 1, 0, 1]
  cbv at before after
  exact ⟨next, stream_key before.1, stream_key after.1, endKey, related.completion⟩

example : GrowingSiblingRefinement := growingSiblingRefinement_holds

#print axioms growingSiblingRefinement_holds
#print axioms executeCollectedFields_growing_of_children
#print axioms completeListValue_growing_of_children
#print axioms constructed

end AlternativeGrowingSiblingChecks
