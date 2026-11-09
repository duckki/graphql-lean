import GraphQL
import Proofs.GraphQL.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Execution.Typename

/-! A constant built-in leaf invalidates unrestricted normal-form uniqueness.
Swapping non-null fields with the same concrete return type preserves both data
and counted errors when their only selected child is `__typename`.
-/

open GraphQL GraphQL.Execution

namespace GraphQL.Tests.NormalForm.Typename

def schema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "f", outputType := .nonNull (.named "Person") },
                { name := "g", outputType := .nonNull (.named "Person") }
              ]
          },
        .object
          {
            name := "Person", fields := [{ name := "id", outputType := .named "String" }]
          }
      ]
  }

def children : List Selection := [.field "kind" "__typename" [] [] []]

def left : Operation :=
  { selectionSet := [.field "a" "f" [] [] children, .field "b" "g" [] [] children] }

def right : Operation :=
  { selectionSet := [.field "a" "g" [] [] children, .field "b" "f" [] [] children] }

def completed : ResponseValue := .object [("kind", .scalar "Person")]

attribute [local simp] Schema.lookupType Schema.allTypes Schema.builtinScalarDefinitions
  TypeDefinition.name BuiltinScalar.name List.find? schema TypeRef.namedType
  Schema.typeIncludesObjectBool Schema.getPossibleTypes selectionDirectivesAllowBool

theorem completion_is_fixed_or_error {ObjectRef : Type}
    (resolvers : Resolvers ObjectRef) (values : VariableValues) (fuel : Nat)
    (fieldName : Name) (value : ResolverValue ObjectRef)
    : (∃ errors,
        completeValue schema resolvers values fuel (.nonNull (.named "Person"))
          [{ fieldName, arguments := [], selectionSet := children }] value
        = .error errors)
      ∨ completeValue schema resolvers values fuel (.nonNull (.named "Person"))
          [{ fieldName, arguments := [], selectionSet := children }] value
        = .ok (completed, 0) := by
  cases fuel with
  | zero => exact Or.inl ⟨1, by simp_all [completeValue, outOfFuel]⟩
  | succ fuel =>
      cases value with
      | null => exact Or.inl ⟨1, by simp_all [completeValue, nonNullCompletion]⟩
      | scalar value =>
          exact Or.inl
            ⟨1, by simp_all [completeValue, nonNullCompletion, TypeRef.isCompositeBool]⟩
      | list values => exact Or.inl ⟨1, by simp_all [completeValue, nonNullCompletion]⟩
      | object runtimeType ref =>
          by_cases hincludes : schema.typeIncludesObjectBool "Person" runtimeType = true
          · have hruntime : runtimeType = "Person" := by
              simpa [Schema.typeIncludesObjectBool, Schema.getPossibleTypes]
                using hincludes
            subst runtimeType
            cases fuel with
            | zero =>
                exact Or.inl
                  ⟨
                    1,
                    by simp_all [completeValue, collectSubfields,
                      children, collectFields, collectSelection, mergeExecutableGroups,
                      executeCollectedFields, executeField,
                      outOfFuel, Result.combine, catchBubbleAsNull, nonNullCompletion]
                  ⟩
            | succ fuel =>
                cases fuel with
                | zero =>
                    exact Or.inl
                      ⟨
                        1,
                        by
                          simp_all [completeValue, collectSubfields,
                            children, collectFields, collectSelection, mergeExecutableGroups,
                            executeCollectedFields, executeField,
                            Schema.lookupField, Schema.typenameFieldDefinition, coerceArgumentValues,
                            resolveFieldValue, resolveTypenameField, singleFieldResult,
                            outOfFuel, Result.combine, catchBubbleAsNull, nonNullCompletion]
                      ⟩
                | succ fuel =>
                    right
                    simp_all [completeValue, collectSubfields, children,
                      collectFields, collectSelection, mergeExecutableGroups,
                      executeCollectedFields, executeField, Schema.lookupField,
                      Schema.typenameFieldDefinition, coerceArgumentValues, resolveFieldValue,
                      resolveTypenameField, singleFieldResult, Result.combine, catchBubbleAsNull,
                      nonNullCompletion, TypeRef.isCompositeBool, completed]
          · exact Or.inl ⟨1, by simp_all [completeValue, nonNullCompletion]⟩

def fieldOutcome {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    (values : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (fieldName : Name)
    : Result ResponseValue :=
  match resolvers.resolve "Query" fieldName [] source with
  | none => .error 1
  | some value =>
      completeValue schema resolvers values fuel (.nonNull (.named "Person"))
        [{ fieldName, arguments := [], selectionSet := children }] value

theorem fieldOutcome_fixed_or_error {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    (values : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (fieldName : Name)
    : (∃ errors, fieldOutcome resolvers values fuel source fieldName = .error errors)
      ∨ fieldOutcome resolvers values fuel source fieldName = .ok (completed, 0) := by
  cases hresolve : resolvers.resolve "Query" fieldName [] source with
  | none => exact Or.inl ⟨1, by simp [fieldOutcome, hresolve]⟩
  | some value =>
      simpa [fieldOutcome, hresolve]
        using completion_is_fixed_or_error resolvers values fuel fieldName value

theorem executeField_eq_outcome {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    (values : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (responseName fieldName : Name) (hname : fieldName = "f" ∨ fieldName = "g")
    : executeField schema resolvers values (fuel + 1) "Query" source responseName
        [{ fieldName, arguments := [], selectionSet := children }]
      = singleFieldResult responseName
          (fieldOutcome resolvers values fuel source fieldName) := by
  rcases hname with rfl | rfl <;>
    simp [executeField, Schema.lookupField, Schema.lookupDeclaredField, TypeDefinition.fields?,
      coerceArgumentValues, resolveFieldValue, fieldOutcome, handleFieldError] <;>
    split <;> simp_all

theorem swap_equal {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    (values : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    : executeSelectionSetAsResponse schema resolvers values fuel "Query" source
        left.selectionSet
      = executeSelectionSetAsResponse schema resolvers values fuel "Query" source
          right.selectionSet := by
  have hleft : collectFields schema values "Query" source left.selectionSet =
      [("a", [{ fieldName := "f", arguments := [], selectionSet := children }]),
       ("b", [{ fieldName := "g", arguments := [], selectionSet := children }])] := by
    simp [left, collectFields, collectSelection, mergeExecutableGroups, addExecutableGroup]
  have hright : collectFields schema values "Query" source right.selectionSet =
      [("a", [{ fieldName := "g", arguments := [], selectionSet := children }]),
       ("b", [{ fieldName := "f", arguments := [], selectionSet := children }])] := by
    simp [right, collectFields, collectSelection, mergeExecutableGroups, addExecutableGroup]
  cases fuel with
  | zero =>
      simp only [executeSelectionSetAsResponse, executeSelectionSet, executeRootSelectionSet,
        hleft, hright, executeCollectedFields, executeField, outOfFuel, Result.combine,
        selectionSetResultToResponse, Nat.add_zero]
  | succ fuel =>
      simp only [executeSelectionSetAsResponse, executeSelectionSet, executeRootSelectionSet,
        hleft, hright, executeCollectedFields]
      rw [executeField_eq_outcome resolvers values fuel source "a" "f" (Or.inl rfl),
        executeField_eq_outcome resolvers values fuel source "b" "g" (Or.inr rfl),
        executeField_eq_outcome resolvers values fuel source "a" "g" (Or.inr rfl),
        executeField_eq_outcome resolvers values fuel source "b" "f" (Or.inl rfl)]
      rcases fieldOutcome_fixed_or_error resolvers values fuel source "f" with ⟨ferrors, hf⟩ | hf <;>
        rcases fieldOutcome_fixed_or_error resolvers values fuel source "g" with ⟨gerrors, hg⟩ | hg <;>
        simp [hf, hg, singleFieldResult, Result.combine, selectionSetResultToResponse, Nat.add_comm]

#print axioms swap_equal

theorem operations_equal {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    (values : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    : executeQueryWithFuel schema resolvers values left fuel source
      = executeQueryWithFuel schema resolvers values right fuel source := by
  have hroot : rootSourceAppliesBool schema left source
      = rootSourceAppliesBool schema right source := rfl
  unfold executeQueryWithFuel
  rw [← hroot]
  split
  · change executeSelectionSetAsResponse schema resolvers values fuel "Query" source left.selectionSet
      = executeSelectionSetAsResponse schema resolvers values fuel "Query" source right.selectionSet
    exact swap_equal resolvers values fuel source
  · rfl

theorem semantically_equivalent
    : NormalForm.operationsSemanticallyEquivalent schema left right := by
  intro ObjectRef resolvers values fuel source _ _
  rw [operations_equal]
  exact ⟨rfl, rfl⟩

theorem not_reordered
    : ¬ NormalForm.SelectionSetEqualUpToReorderingWithCoercion
          schema [] [] "Query" left.selectionSet right.selectionSet := by
  let head : Selection -> Option (Name × Name) := fun selection =>
    match selection with
    | .field responseName fieldName _ _ _ => some (responseName, fieldName)
    | _ => none
  have hheads : ∀ {first second : Selection},
      NormalForm.SelectionEqualUpToReorderingWithCoercion schema [] [] "Query" first second
      -> head first = head second := by
    intro first second h
    cases h <;> rfl
  intro h
  cases h with
  | paired pairs hleft hright hfields =>
      have hmem : Selection.field "a" "f" [] [] children ∈ pairs.map Prod.fst :=
        hleft.mem_iff.mpr (by simp [left])
      obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp hmem
      have hrightMem : pair.2 ∈ right.selectionSet :=
        hright.mem_iff.mp (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
      have hrel := hfields pair hpair
      rcases pair with ⟨first, second⟩
      dsimp only at heq hrightMem hrel
      subst first
      simp only [right, List.mem_cons, List.not_mem_nil, or_false] at hrightMem
      have heq := hheads hrel
      rcases hrightMem with rfl | rfl <;> simp [head] at heq

theorem left_normal : NormalForm.operationNormal schema left := by
  simp [NormalForm.operationNormal, Operation.rootType, OperationType.rootType, left, children,
    NormalForm.selectionSetNormal, NormalForm.selectionSetGroundTyped, NormalForm.selectionGroundTyped,
    NormalForm.selectionsAllFields, NormalForm.selectionsAllInlineFragments, NormalForm.objectTypeNameBool,
    Schema.fieldReturnType?, Schema.lookupField, Schema.lookupDeclaredField, TypeDefinition.fields?,
    NormalForm.selectionSetNonRedundant, NormalForm.selectionNonRedundant, NormalForm.responseNamesNodup,
    NormalForm.inlineFragmentTypeConditionsNodup, NormalForm.inlineFragmentTypeCondition?,
    Selection.responseName?, Selection.isField, Selection.isInlineFragment, List.filterMap]

theorem right_normal : NormalForm.operationNormal schema right := by
  simp [NormalForm.operationNormal, Operation.rootType, OperationType.rootType, right, children,
    NormalForm.selectionSetNormal, NormalForm.selectionSetGroundTyped, NormalForm.selectionGroundTyped,
    NormalForm.selectionsAllFields, NormalForm.selectionsAllInlineFragments, NormalForm.objectTypeNameBool,
    Schema.fieldReturnType?, Schema.lookupField, Schema.lookupDeclaredField, TypeDefinition.fields?,
    NormalForm.selectionSetNonRedundant, NormalForm.selectionNonRedundant, NormalForm.responseNamesNodup,
    NormalForm.inlineFragmentTypeConditionsNodup, NormalForm.inlineFragmentTypeCondition?,
    Selection.responseName?, Selection.isField, Selection.isInlineFragment, List.filterMap]

theorem left_not_typenameFree : ¬ NormalForm.operationTypenameFree left := by
  simp [NormalForm.operationTypenameFree, NormalForm.selectionSetTypenameFree,
    NormalForm.selectionTypenameFree, left, children]

theorem right_not_typenameFree : ¬ NormalForm.operationTypenameFree right := by
  simp [NormalForm.operationTypenameFree, NormalForm.selectionSetTypenameFree,
    NormalForm.selectionTypenameFree, right, children]

example : NormalForm.selectionSetTypenameFree [.field "__typename" "id" [] [] []] := by
  simp [NormalForm.selectionSetTypenameFree, NormalForm.selectionTypenameFree]

example
    : ¬ NormalForm.selectionSetTypenameFree
          [.inlineFragment none [] [.field "aliased" "__typename" [] [] []]] := by
  simp [NormalForm.selectionSetTypenameFree, NormalForm.selectionTypenameFree]

#print axioms semantically_equivalent
#print axioms not_reordered

end GraphQL.Tests.NormalForm.Typename
