import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.KeyTailExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledExecutor
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Successive actual recursive cuts retain earlier stream images and later allocate
fresh object/defer metadata. One constructed map relates the entire generated Work. -/

namespace AlternativeKeyExtensionChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement WorkQueueSemantics
open KeyRenaming ScheduledWork
open GraphQL.IncrementalDelivery.Semantics.RefRegions

private def requiredPair : List Selection :=
  [
    Tests.field "required" [] [] (some "first"),
    Tests.field "required" [] [] (some "second")
  ]

private def scope (userAlias valuesAlias : GraphQL.Name) : Selection :=
  Tests.defer
    [
      Tests.field "user" (requiredPair ++ [Tests.field "values" [] [.stream]]) []
        (some userAlias),
      Tests.field "values" [] [.stream] (some valuesAlias)
    ]

private def selections : List Selection :=
  [
    scope "firstUser" "firstValues",
    scope "secondUser" "secondValues",
    Tests.defer [Tests.field "user" [Tests.defer [Tests.field "values" [] [.stream]]]]
  ]

private def eager :=
  (executeRootSelectionSetCore Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) selections).run
    17

private def scheduled :=
  (ScheduledExecution.executeRootSelectionSetCore Tests.schema Tests.resolvers [] 7
    "Query" (.object "Query" 0) selections).run
    17

-- Each constructor uses actual boundaries after the cancelled allocation. The second
-- extension leaves the first surviving stream key's image intact.
private def firstKeys : Nat → Nat := retargetTail id 20 21
private def keys : Nat → Nat := retargetTail firstKeys 21 23

private theorem first_injective : Function.Injective firstKeys :=
  retargetTail_injective (fun _ _ same => same) (by intro key earlier; dsimp; omega)

private theorem first_prefix : PrefixBelow firstKeys 21 23 := by
  intro key earlier
  unfold firstKeys retargetTail
  split
  · change key < 23
    omega
  · omega

private theorem keys_injective : Function.Injective keys :=
  retargetTail_injective first_injective first_prefix

example : scheduled.2 = 24 ∧ eager.2 = 26 := by cbv

example
    : keys 17 = 17
      ∧ keys 18 = 18
      ∧ keys 19 = 19
      ∧ keys 20 = 21
      ∧ keys 21 = 23
      ∧ keys 22 = 24
      ∧ keys 23 = 25 := by cbv

private theorem actual_refinement : CompletionRefines keys scheduled.1 eager.1 := by
  cbv
  repeat first | constructor! | trivial

-- This is actual retained Work from the first completed deferred partition, not an
-- independent synthetic tree. The lookup is checked to be present below.
private def firstScheduled : Completion (List (GraphQL.Name × ResponseValue)) :=
  {
    result := .ok ([], 0),
    work :=
      ((locateWork scheduled.1.work [1, 0]).getD ⟨.empty, none, []⟩).current
  }

private def firstEager : Completion (List (GraphQL.Name × ResponseValue)) :=
  {
    result := .ok ([], 0),
    work :=
      ((locateWork eager.1.work [1, 0]).getD ⟨.empty, none, []⟩).current
  }

example : (locateWork scheduled.1.work [1, 0]).isSome = true := by cbv
example : (locateWork eager.1.work [1, 0]).isSome = true := by cbv

private theorem first_related
    : CompletionRefines firstKeys firstScheduled firstEager := by
  cbv
  repeat first | constructor! | trivial

private theorem first_bound : ∀ key ∈ allRefs firstScheduled.work, key < 21 := by
  intro key member
  cbv at member
  rcases List.mem_cons.mp member with same | rest
  · omega
  · have same := List.mem_singleton.mp rest
    omega

-- Extension preserves a previous relation rather than selecting a new unrelated witness
-- for that partition. Earlier defer key 17 and stream key 20 remain mapped identically.
example : CompletionRefines keys firstScheduled firstEager :=
  (prefixWorkExtension_holds _ firstKeys 21 23 firstScheduled firstEager first_injective
    first_prefix first_bound first_related).2.2.2.2

-- Nested item keys are included: agreement on only the root region is insufficient.
private def hidden : Work :=
  .stream { ref := 0, path := [] }
    [({ result := .ok (.null, 0) }, .stream { ref := 8, path := [.index 0] } [])]

example : allRefs hidden = [0, 8] := by cbv
example : 8 ∉ rootRefs hidden := by simp [hidden, rootRefs]

example : ¬WorkRefines (retargetTail id 8 9) hidden hidden := by
  intro related
  cases related with
  | stream items =>
      cases items with
      | cons payload nested tail => cases nested

-- The prefix-image bound prevents collision with an already allocated image.
example : ¬Function.Injective (retargetTail (fun key => key + 10) 1 10) := by
  intro injective
  have impossible := injective (a₁ := 0) (a₂ := 1) (by cbv)
  omega

-- The same map and generated Work pair feed the existing causal kernel proof.
example (failed : List Occurrence) (published : Occurrence → Prop)
    : ∀ occurrence,
        Causality.TaskCancelled eager.1.work failed published occurrence
        ↔ Causality.TaskCancelled scheduled.1.work failed published occurrence :=
  (recursiveWorkCausality_holds keys keys_injective _ _ actual_refinement.2.1 failed
    published).2.2

example : PrefixWorkExtension := prefixWorkExtension_holds

#print axioms prefixWorkExtension_holds
#print axioms WorkRefines.rekey
#print axioms actual_refinement
#print axioms first_related

end AlternativeKeyExtensionChecks
