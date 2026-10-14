import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.KeyRenamingCollection
import Tests.GraphQL.IncrementalDelivery.Execution

/-! The actual object boundary uses one map across several gaps, inherited ancestors,
duplicate usages and ordered planning. A noninjective map changes partitioning. -/

namespace AlternativeKeyMetadataChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open KeyRenaming

private def keys : Nat → Nat := extendAtCut (insertGap 18 1) 21 2

private theorem keys_injective : Function.Injective keys :=
  extendAtCut_injective (insertGap_injective 18 1) 21 2

private theorem keys_fresh : FreshTail keys 21 :=
  FreshTail.extendAtCut ((FreshTail.insertGap 18 1).advance (by omega))

example : keys 17 = 17 ∧ keys 18 = 19 ∧ keys 20 = 21 ∧ keys 21 = 24 := by cbv

private def inherited : DeferUsage :=
  { ref := 20, ancestors := [18, 17], label := some "parent" }

private def selected : List Selection :=
  [
    Tests.field "name",
    Tests.defer
      [
        Tests.field "values" [] [.stream],
        Tests.defer [Tests.field "name" [] [] (some "nested")]
      ],
    Tests.defer [Tests.field "values" [] [] (some "other")]
  ]

private def original : List FieldDetails :=
  [{
    fieldName := "user",
    arguments := [],
    selectionSet := selected,
    deferUsage := some inherited
  }]

private def context : DeferMap :=
  [
    { node := { ref := 17, path := [], label := some "root" } },
    { node := { ref := 18, path := [] }, ancestors := [{ ref := 17, path := [] }] },
    {
      node := { ref := 20, path := [.field "user"] },
      ancestors := [{ ref := 18, path := [] }, { ref := 17, path := [] }]
    }
  ]

private def before :=
  (collectSubfields Tests.schema [] "User" (.object "User" (0 : Nat)) original).run 21

private def after :=
  (collectSubfields Tests.schema [] "User" (.object "User" (0 : Nat))
    (original.map (field keys))).run
    (keys 21)

-- The witness is constructed by the recursive theorem at arbitrary metadata, not by
-- assuming related collected outputs, plan partitions or ancestor lookups.
private theorem actual_boundary
    : after = (collection keys before.1, keys before.2)
      ∧ FreshTail keys before.2
      ∧ buildExecutionPlan after.1.collectedFieldsMap ([20].map keys)
        = plan keys (buildExecutionPlan before.1.collectedFieldsMap [20])
      ∧ getNewDeferMap after.1.newDeferUsages [.field "user"]
          (context.map (fragment keys))
        = (getNewDeferMap before.1.newDeferUsages [.field "user"] context).map
            (fragment keys) :=
  objectCollectionRenaming_holds Nat keys Tests.schema [] "User" (.object "User" 0)
    original 21 [20] [.field "user"] context keys_injective keys_fresh

example : before.2 = 24 ∧ after.2 = 27 := by cbv

example : before.1.newDeferUsages.map DeferUsage.ref = [21, 22, 23] := by cbv
example : after.1.newDeferUsages.map DeferUsage.ref = [24, 25, 26] := by cbv

example
    : after.1.newDeferUsages.map DeferUsage.ancestors
      = [[21, 19, 17], [24, 21, 19, 17], [21, 19, 17]] := by cbv

-- Repeated contributor identities and ancestor suppression are preserved, not sorted.
private def repeated : List FieldDetails :=
  [
    {
      fieldName := "name",
      arguments := [],
      selectionSet := [],
      deferUsage := some { ref := 20, ancestors := [18] }
    },
    {
      fieldName := "name",
      arguments := [],
      selectionSet := [],
      deferUsage := some { ref := 18, ancestors := [17] }
    },
    {
      fieldName := "name",
      arguments := [],
      selectionSet := [],
      deferUsage := some { ref := 20, ancestors := [18] }
    }
  ]

example : getFilteredDeferUsageSet repeated = [18] := by cbv
example : getFilteredDeferUsageSet (repeated.map (field keys)) = [19] := by cbv

example
    : getFilteredDeferUsageSet (repeated.map (field keys))
      = (getFilteredDeferUsageSet repeated).map keys :=
  filtered_usages keys_injective _

-- Lookup remains first-match, including duplicate contexts and missing ancestors.
example (first second : DeferredFragment)
    : lookupDeferredFragment? ([first, second].map (fragment keys)) (keys first.node.ref)
      = some (fragment keys first) := by
  rw [lookup_fragment keys_injective]
  simp [lookupDeferredFragment?]

-- A collision changes the algorithm: two deferred partitions collapse into one.
private def detail (key : Nat) : FieldDetails :=
  {
    fieldName := "name",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key }
  }

private def separate : CollectedFieldsMap := [("a", [detail 1]), ("b", [detail 2])]

example : (buildExecutionPlan separate []).newCollectedFieldsMaps.length = 2 := by cbv

example
    : (buildExecutionPlan (fields (fun _ => 0) separate) []).newCollectedFieldsMaps.length
      = 1 := by cbv

example
    : buildExecutionPlan (fields (fun _ => 0) separate) []
      ≠ plan (fun _ => 0) (buildExecutionPlan separate []) := by
  intro equal
  have impossible := congrArg (fun value => value.newCollectedFieldsMaps.length) equal
  cbv at impossible

example : ObjectMetadataRenaming := objectMetadataRenaming_holds
example : ObjectCollectionRenaming := objectCollectionRenaming_holds

#print axioms objectMetadataRenaming_holds
#print axioms objectCollectionRenaming_holds
#print axioms actual_boundary

end AlternativeKeyMetadataChecks
