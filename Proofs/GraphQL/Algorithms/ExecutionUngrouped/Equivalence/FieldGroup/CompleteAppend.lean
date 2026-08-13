import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup

/-!
Complete-value append-one proofs for executable field groups.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

attribute [local simp] TypeRef.namedType

local instance fieldGroupCompleteAppendResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem completeValue_nonNull_append_result_aligned_of_inner
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (inner : TypeRef) (resolved : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (hinner
      : ResponseValueResultAlignedEquivalent
          (GraphQL.Execution.Result.combine mergeResponse
            (GraphQL.Execution.completeValue schema resolvers variableValues
              depth inner prefixFields resolved)
            (completeResolvedValue schema resolvers variableValues depth inner
              later.selectionSet resolved
              (some
                (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers variableValues
                    depth inner prefixFields resolved)))))
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            inner (prefixFields ++ [later]) resolved))
    : ResponseValueResultAlignedEquivalent
        (GraphQL.Execution.Result.combine mergeResponse
          (GraphQL.Execution.completeValue schema resolvers variableValues depth
            (.nonNull inner) prefixFields resolved)
          (completeResolvedValue schema resolvers variableValues depth
            (.nonNull inner) later.selectionSet resolved
            (some
              (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues depth
                  (.nonNull inner) prefixFields resolved)))))
        (GraphQL.Execution.completeValue schema resolvers variableValues depth
          (.nonNull inner) (prefixFields ++ [later]) resolved) := by
  cases depth with
  | zero =>
      cases resolved <;>
        simp [GraphQL.Execution.completeValue, outOfFuel,
          completeResolvedValue_previous_null, resultValueOrNull,
          GraphQL.Execution.Result.combine,
          ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | succ childDepth =>
      let innerPrefix :=
        GraphQL.Execution.completeValue schema resolvers variableValues
          (childDepth + 1) inner prefixFields resolved
      let innerRight :=
        completeResolvedValue schema resolvers variableValues (childDepth + 1)
          inner later.selectionSet resolved
          (some (resultValueOrNull innerPrefix))
      have hwrappedNull :
          resultValueOrNull innerPrefix = .null ->
            completeResolvedValue schema resolvers variableValues
              (childDepth + 1) (.nonNull inner) later.selectionSet resolved
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  (childDepth + 1) (.nonNull inner) prefixFields resolved))) =
            .ok (.null, 0) := by
        intro hnull
        have houterNull :
            resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues
                (childDepth + 1) (.nonNull inner) prefixFields resolved) =
            .null := by
          simp [GraphQL.Execution.completeValue,
            resultValueOrNull_nonNullCompletion, innerPrefix, hnull]
        simpa [houterNull] using
          completeResolvedValue_previous_null schema resolvers variableValues
            (childDepth + 1) (.nonNull inner) later.selectionSet resolved
      have hwrappedNonNull :
          resultValueOrNull innerPrefix ≠ .null ->
            completeResolvedValue schema resolvers variableValues
              (childDepth + 1) (.nonNull inner) later.selectionSet resolved
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  (childDepth + 1) (.nonNull inner) prefixFields resolved))) =
            nonNullCompletion innerRight := by
        intro hnonNull
        have hprevious :
            (some (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues
                (childDepth + 1) (.nonNull inner) prefixFields resolved)) :
              Option ResponseValue) ≠ some .null := by
          intro hsome
          have houterNull :
              resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  (childDepth + 1) (.nonNull inner) prefixFields resolved) =
              .null := by
            simpa using Option.some.inj hsome
          exact hnonNull (by
            simpa [GraphQL.Execution.completeValue,
              resultValueOrNull_nonNullCompletion, innerPrefix] using
              houterNull)
        simpa [innerRight, GraphQL.Execution.completeValue,
          resultValueOrNull_nonNullCompletion, innerPrefix] using
          completeResolvedValue_nonNull_eq_nonNullCompletion_of_previous_ne_null
            schema resolvers variableValues (childDepth + 1) inner
            later.selectionSet resolved
            (some (resultValueOrNull
              (GraphQL.Execution.completeValue schema resolvers variableValues
                (childDepth + 1) (.nonNull inner) prefixFields resolved)))
            hprevious
      have hmerge :
          ResponseValueResultAlignedEquivalent
            (GraphQL.Execution.Result.combine mergeResponse
              (nonNullCompletion innerPrefix)
              (completeResolvedValue schema resolvers variableValues
                (childDepth + 1) (.nonNull inner) later.selectionSet resolved
                (some (resultValueOrNull
                  (GraphQL.Execution.completeValue schema resolvers
                    variableValues (childDepth + 1) (.nonNull inner)
                    prefixFields resolved)))))
            (nonNullCompletion
              (GraphQL.Execution.Result.combine mergeResponse innerPrefix
                innerRight)) :=
        ResponseValueResultAlignedEquivalent.nonNull_merge_inner
          (left := innerPrefix) (right := innerRight)
          (wrappedRight :=
            completeResolvedValue schema resolvers variableValues
              (childDepth + 1) (.nonNull inner) later.selectionSet resolved
              (some (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  (childDepth + 1) (.nonNull inner) prefixFields resolved))))
          (by
            intro errors herror
            exact
              specCompleteValue_error_positive schema resolvers variableValues
                (childDepth + 1) inner prefixFields resolved errors
                (by simpa [innerPrefix] using herror))
          (by
            intro errors herror
            exact
              completeResolvedValue_error_positive schema resolvers
                variableValues (childDepth + 1) inner later.selectionSet
                resolved (some (resultValueOrNull innerPrefix)) errors
                (by simpa [innerRight] using herror))
          hwrappedNull hwrappedNonNull
      have hwrappedInner :=
        ResponseValueResultAlignedEquivalent.nonNullCompletion_aligned
          (ungrouped :=
            GraphQL.Execution.Result.combine mergeResponse innerPrefix
              innerRight)
          (spec :=
            GraphQL.Execution.completeValue schema resolvers variableValues
              (childDepth + 1) inner (prefixFields ++ [later]) resolved)
          (by simpa [innerPrefix, innerRight] using hinner)
      simpa [GraphQL.Execution.completeValue, innerPrefix, innerRight] using
        ResponseValueResultAlignedEquivalent.trans hmerge hwrappedInner

theorem completeValue_group_append_one_result_aligned_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (fieldType : TypeRef)
    : ∀ (depth : Nat) (resolved : ResolverValue ObjectIdentity)
        (prefixFields : List ExecutableField) (later : ExecutableField),
        (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
        -> (∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject resolved runtimeType identity
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                      (.object []))))
        -> (∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject resolved runtimeType identity
              -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
              -> ExecutionStateEquivalent
                  {
                    window :=
                      {
                        schema := schema
                        resolvers := resolvers
                        variableValues := variableValues
                        depth := childDepth
                        parentType := runtimeType
                        source := .object runtimeType identity
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            (prefixFields ++ [later])
                      }
                    initial := .object []
                  })
        -> ResponseValueResultAlignedEquivalent
            (GraphQL.Execution.Result.combine mergeResponse
              (GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldType prefixFields resolved)
              (completeResolvedValue schema resolvers variableValues depth fieldType
                later.selectionSet resolved
                (some
                  (resultValueOrNull
                    (GraphQL.Execution.completeValue schema resolvers variableValues
                      depth fieldType prefixFields resolved)))))
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              fieldType (prefixFields ++ [later]) resolved) := by
  induction fieldType with
  | named typeName =>
      intro depth resolved prefixFields later hprefixChildren hobjects
        hchildren
      exact
        completeValue_named_group_append_one_result_aligned_spec_of_contained
          schema resolvers variableValues depth typeName resolved
          prefixFields later
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hprefixChildren childDepth runtimeType identity hlt
              hcontains (by simpa using hincludes))
          hobjects
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hchildren childDepth runtimeType identity hlt
              hcontains (by simpa using hincludes))
  | list inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects
        hchildren
      cases depth with
      | zero =>
          cases resolved <;>
            simp [GraphQL.Execution.completeValue,
              completeResolvedValue_previous_null, outOfFuel,
              resultValueOrNull, GraphQL.Execution.Result.combine,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | succ childDepth =>
          cases resolved with
          | null =>
              simp [GraphQL.Execution.completeValue,
                completeResolvedValue_previous_null, resultValueOrNull,
                GraphQL.Execution.Result.combine, mergeResponse,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | scalar value =>
              simp [GraphQL.Execution.completeValue,
                completeResolvedValue_previous_null, resultValueOrNull,
                GraphQL.Execution.Result.combine,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | object runtimeType identity =>
              simp [GraphQL.Execution.completeValue,
                completeResolvedValue_previous_null, resultValueOrNull,
                GraphQL.Execution.Result.combine,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | list values =>
              have hvalueAppend :
                  ∀ value : ResolverValue ObjectIdentity,
                  value ∈ values ->
                    ResponseValueResultAlignedEquivalent
                      (GraphQL.Execution.Result.combine mergeResponse
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner prefixFields value)
                        (completeResolvedValue schema resolvers variableValues
                          childDepth inner later.selectionSet value
                          (some (resultValueOrNull
                            (GraphQL.Execution.completeValue schema resolvers
                              variableValues childDepth inner prefixFields
                              value)))))
                      (GraphQL.Execution.completeValue schema resolvers
                        variableValues childDepth inner
                        (prefixFields ++ [later]) value) := by
                intro value hmem
                exact ih childDepth value prefixFields later
                  (by
                    intro childDepth' runtimeType identity hlt hcontains
                      hincludes
                    exact hprefixChildren childDepth' runtimeType identity
                      (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                      (ValueContainsObject.list hmem hcontains)
                      (by simpa using hincludes))
                  (by
                    intro childDepth' runtimeType identity hlt hcontains
                    exact hobjects childDepth' runtimeType identity
                      (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                      (ValueContainsObject.list hmem hcontains))
                  (by
                    intro childDepth' runtimeType identity hlt hcontains
                      hincludes
                    exact hchildren childDepth' runtimeType identity
                      (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                      (ValueContainsObject.list hmem hcontains)
                      (by simpa using hincludes))
              cases hcontains : inner.isCompositeBool schema with
              | false =>
                  have happendedPrefix :
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues childDepth inner
                        (prefixFields ++ [later]) values =
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues childDepth inner prefixFields values :=
                    specCompleteValueList_eq_of_no_object schema resolvers
                      variableValues childDepth inner (prefixFields ++ [later])
                      prefixFields values hcontains
                  cases hprefixList
                        : GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                  | error prefixErrors =>
                      have happended :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner
                            (prefixFields ++ [later]) values =
                          .error prefixErrors := by
                        rw [happendedPrefix, hprefixList]
                      simp [GraphQL.Execution.completeValue,
                        completeResolvedValue_previous_null, hprefixList,
                        happended, resultValueOrNull,
                        GraphQL.Execution.Result.combine, mergeResponse,
                        catchBubbleAsNull, ResponseValueResultAlignedEquivalent,
                        ErrorPresenceEquivalent]
                  | ok prefixResult =>
                      rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                      have happended :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner
                            (prefixFields ++ [later]) values =
                          .ok (prefixValues, prefixErrors) := by
                        rw [happendedPrefix, hprefixList]
                      have hprefixReady :
                          ∀ response, response ∈ prefixValues ->
                            ResponseMergeReady response :=
                        specCompleteValueList_values_ready schema resolvers
                          variableValues childDepth inner prefixFields values
                          prefixValues prefixErrors hprefixList
                      have hself :
                          mergeResponseLists prefixValues prefixValues =
                            prefixValues :=
                        mergeResponseLists_self_of_ready prefixValues
                          hprefixReady
                      have houterContains :
                          (TypeRef.list inner).isCompositeBool schema =
                            false := by
                        simpa [TypeRef.isCompositeBool, TypeRef.namedType]
                          using hcontains
                      simp [GraphQL.Execution.completeValue,
                        completeResolvedValue, reusablePreviousValue?,
                        hprefixList, happended, houterContains, hself,
                        resultValueOrNull, GraphQL.Execution.Result.combine,
                        mergeResponse, catchBubbleAsNull,
                        ResponseValueResultAlignedEquivalent,
                        ErrorPresenceEquivalent]
              | true =>
                  have hlistAppend :=
                    completeValueList_append_result_aligned_of_mem schema
                      resolvers variableValues childDepth inner prefixFields
                      later values hcontains hvalueAppend
                  have houterContains :
                      (TypeRef.list inner).isCompositeBool schema = true := by
                    simpa [TypeRef.isCompositeBool, TypeRef.namedType]
                      using hcontains
                  cases hprefixList
                        : GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                  | error prefixErrors =>
                      have hlistAppend' := hlistAppend
                      simp [hprefixList] at hlistAppend'
                      simpa [GraphQL.Execution.completeValue,
                        completeResolvedValue, reusablePreviousValue?,
                        houterContains, resultValueOrNull,
                        GraphQL.Execution.Result.combine, catchBubbleAsNull,
                        completeValue, reuseOrCreateList?, hprefixList,
                        mergeResponse]
                        using
                          ListResponseResultAlignedEquivalent.catchBubbleAsNull_mergeResponse
                            (by
                              intro errors hbase
                              cases hbase
                              rfl)
                            hlistAppend'
                  | ok prefixResult =>
                      rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                      have hlistAppend' := hlistAppend
                      simp [hprefixList] at hlistAppend'
                      simpa [GraphQL.Execution.completeValue,
                        completeResolvedValue, reusablePreviousValue?,
                        houterContains, resultValueOrNull,
                        GraphQL.Execution.Result.combine, catchBubbleAsNull,
                        completeValue, reuseOrCreateList?, hprefixList,
                        mergeResponse]
                        using
                          ListResponseResultAlignedEquivalent.catchBubbleAsNull_mergeResponse
                            (by
                              intro errors hbase
                              cases hbase)
                            hlistAppend'
  | nonNull inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects
        hchildren
      exact
        completeValue_nonNull_append_result_aligned_of_inner schema resolvers
          variableValues depth inner resolved prefixFields later
          (ih depth resolved prefixFields later
            (by
              intro childDepth runtimeType identity hlt hcontains hincludes
              exact hprefixChildren childDepth runtimeType identity hlt
                hcontains (by simpa using hincludes))
            hobjects
            (by
              intro childDepth runtimeType identity hlt hcontains hincludes
              exact hchildren childDepth runtimeType identity hlt hcontains
                (by simpa using hincludes)))

theorem completeValue_group_append_one_result_aligned_spec_of_aligned_children
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (fieldType : TypeRef)
    : ∀ (depth : Nat) (resolved : ResolverValue ObjectIdentity)
        (prefixFields : List ExecutableField) (later : ExecutableField),
        (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)))
        -> (∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject resolved runtimeType identity
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                      (.object []))))
        -> (∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject resolved runtimeType identity
              -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
              -> RootSelectionResultAlignedEquivalent
                  (executeRootSelectionSet schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (prefixFields ++ [later])))
                  (GraphQL.Execution.executeRootSelectionSet schema resolvers
                    variableValues childDepth runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet
                      (prefixFields ++ [later]))))
        -> ResponseValueResultAlignedEquivalent
            (GraphQL.Execution.Result.combine mergeResponse
              (GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldType prefixFields resolved)
              (completeResolvedValue schema resolvers variableValues depth fieldType
                later.selectionSet resolved
                (some
                  (resultValueOrNull
                    (GraphQL.Execution.completeValue schema resolvers variableValues
                      depth fieldType prefixFields resolved)))))
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              fieldType (prefixFields ++ [later]) resolved) := by
  induction fieldType with
  | named typeName =>
      intro depth resolved prefixFields later hprefixChildren hobjects
        hchildren
      exact
        completeValue_named_group_append_one_result_aligned_spec_of_contained_aligned
          schema resolvers variableValues depth typeName resolved
          prefixFields later
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hprefixChildren childDepth runtimeType identity hlt
              hcontains (by simpa using hincludes))
          hobjects
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hchildren childDepth runtimeType identity hlt
              hcontains (by simpa using hincludes))
  | list inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects
        hchildren
      cases depth with
      | zero =>
          cases resolved <;>
            simp [GraphQL.Execution.completeValue,
              completeResolvedValue_previous_null, outOfFuel,
              resultValueOrNull, GraphQL.Execution.Result.combine,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | succ childDepth =>
          cases resolved with
          | null =>
              simp [GraphQL.Execution.completeValue,
                completeResolvedValue_previous_null, resultValueOrNull,
                GraphQL.Execution.Result.combine, mergeResponse,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | scalar value =>
              simp [GraphQL.Execution.completeValue,
                completeResolvedValue_previous_null, resultValueOrNull,
                GraphQL.Execution.Result.combine,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | object runtimeType identity =>
              simp [GraphQL.Execution.completeValue,
                completeResolvedValue_previous_null, resultValueOrNull,
                GraphQL.Execution.Result.combine,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | list values =>
              have hvalueAppend :
                  ∀ value : ResolverValue ObjectIdentity,
                  value ∈ values ->
                    ResponseValueResultAlignedEquivalent
                      (GraphQL.Execution.Result.combine mergeResponse
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner prefixFields value)
                        (completeResolvedValue schema resolvers variableValues
                          childDepth inner later.selectionSet value
                          (some (resultValueOrNull
                            (GraphQL.Execution.completeValue schema resolvers
                              variableValues childDepth inner prefixFields
                              value)))))
                      (GraphQL.Execution.completeValue schema resolvers
                        variableValues childDepth inner
                        (prefixFields ++ [later]) value) := by
                intro value hmem
                exact ih childDepth value prefixFields later
                  (by
                    intro childDepth' runtimeType identity hlt hcontains
                      hincludes
                    exact hprefixChildren childDepth' runtimeType identity
                      (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                      (ValueContainsObject.list hmem hcontains)
                      (by simpa using hincludes))
                  (by
                    intro childDepth' runtimeType identity hlt hcontains
                    exact hobjects childDepth' runtimeType identity
                      (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                      (ValueContainsObject.list hmem hcontains))
                  (by
                    intro childDepth' runtimeType identity hlt hcontains
                      hincludes
                    exact hchildren childDepth' runtimeType identity
                      (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                      (ValueContainsObject.list hmem hcontains)
                      (by simpa using hincludes))
              cases hcontains : inner.isCompositeBool schema with
              | false =>
                  have happendedPrefix :
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues childDepth inner
                        (prefixFields ++ [later]) values =
                      GraphQL.Execution.completeValueList schema resolvers
                        variableValues childDepth inner prefixFields values :=
                    specCompleteValueList_eq_of_no_object schema resolvers
                      variableValues childDepth inner (prefixFields ++ [later])
                      prefixFields values hcontains
                  cases hprefixList
                        : GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                  | error prefixErrors =>
                      have happended :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner
                            (prefixFields ++ [later]) values =
                          .error prefixErrors := by
                        rw [happendedPrefix, hprefixList]
                      simp [GraphQL.Execution.completeValue,
                        completeResolvedValue_previous_null, hprefixList,
                        happended, resultValueOrNull,
                        GraphQL.Execution.Result.combine, mergeResponse,
                        catchBubbleAsNull, ResponseValueResultAlignedEquivalent,
                        ErrorPresenceEquivalent]
                  | ok prefixResult =>
                      rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                      have happended :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner
                            (prefixFields ++ [later]) values =
                          .ok (prefixValues, prefixErrors) := by
                        rw [happendedPrefix, hprefixList]
                      have hprefixReady :
                          ∀ response, response ∈ prefixValues ->
                            ResponseMergeReady response :=
                        specCompleteValueList_values_ready schema resolvers
                          variableValues childDepth inner prefixFields values
                          prefixValues prefixErrors hprefixList
                      have hself :
                          mergeResponseLists prefixValues prefixValues =
                            prefixValues :=
                        mergeResponseLists_self_of_ready prefixValues
                          hprefixReady
                      have houterContains :
                          (TypeRef.list inner).isCompositeBool schema =
                            false := by
                        simpa [TypeRef.isCompositeBool, TypeRef.namedType]
                          using hcontains
                      simp [GraphQL.Execution.completeValue,
                        completeResolvedValue, reusablePreviousValue?,
                        hprefixList, happended, houterContains, hself,
                        resultValueOrNull, GraphQL.Execution.Result.combine,
                        mergeResponse, catchBubbleAsNull,
                        ResponseValueResultAlignedEquivalent,
                        ErrorPresenceEquivalent]
              | true =>
                  have hlistAppend :=
                    completeValueList_append_result_aligned_of_mem schema
                      resolvers variableValues childDepth inner prefixFields
                      later values hcontains hvalueAppend
                  have houterContains :
                      (TypeRef.list inner).isCompositeBool schema = true := by
                    simpa [TypeRef.isCompositeBool, TypeRef.namedType]
                      using hcontains
                  cases hprefixList
                        : GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                  | error prefixErrors =>
                      have hlistAppend' := hlistAppend
                      simp [hprefixList] at hlistAppend'
                      simpa [GraphQL.Execution.completeValue,
                        completeResolvedValue, reusablePreviousValue?,
                        houterContains, resultValueOrNull,
                        GraphQL.Execution.Result.combine, catchBubbleAsNull,
                        completeValue, reuseOrCreateList?, hprefixList,
                        mergeResponse]
                        using
                          ListResponseResultAlignedEquivalent.catchBubbleAsNull_mergeResponse
                            (by
                              intro errors hbase
                              cases hbase
                              rfl)
                            hlistAppend'
                  | ok prefixResult =>
                      rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                      have hlistAppend' := hlistAppend
                      simp [hprefixList] at hlistAppend'
                      simpa [GraphQL.Execution.completeValue,
                        completeResolvedValue, reusablePreviousValue?,
                        houterContains, resultValueOrNull,
                        GraphQL.Execution.Result.combine, catchBubbleAsNull,
                        completeValue, reuseOrCreateList?, hprefixList,
                        mergeResponse]
                        using
                          ListResponseResultAlignedEquivalent.catchBubbleAsNull_mergeResponse
                            (by
                              intro errors hbase
                              cases hbase)
                            hlistAppend'
  | nonNull inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects
        hchildren
      exact
        completeValue_nonNull_append_result_aligned_of_inner schema resolvers
          variableValues depth inner resolved prefixFields later
          (ih depth resolved prefixFields later
            (by
              intro childDepth runtimeType identity hlt hcontains hincludes
              exact hprefixChildren childDepth runtimeType identity hlt
                hcontains (by simpa using hincludes))
            hobjects
            (by
              intro childDepth runtimeType identity hlt hcontains hincludes
              exact hchildren childDepth runtimeType identity hlt hcontains
                (by simpa using hincludes)))

theorem completeValue_group_append_one_result_eq_spec_and_status
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (fieldType : TypeRef)
    : ∀ (depth : Nat) (resolved : ResolverValue ObjectIdentity)
        (prefixFields : List ExecutableField) (later : ExecutableField),
        (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet prefixFields
                  }
                initial := .object []
              })
        -> (∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject resolved runtimeType identity
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                      (.object []))))
        -> (∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject resolved runtimeType identity
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                    (.object [])))
        -> (∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject resolved runtimeType identity
              -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
              -> ExecutionStateEquivalent
                  {
                    window :=
                      {
                        schema := schema
                        resolvers := resolvers
                        variableValues := variableValues
                        depth := childDepth
                        parentType := runtimeType
                        source := .object runtimeType identity
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            (prefixFields ++ [later])
                      }
                    initial := .object []
                  })
        -> GraphQL.Execution.Result.combine mergeResponse
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth fieldType prefixFields resolved)
                (completeResolvedValue schema resolvers variableValues depth fieldType
                  later.selectionSet resolved
                  (some
                    (resultValueOrNull
                      (GraphQL.Execution.completeValue schema resolvers variableValues
                        depth fieldType prefixFields resolved))))
              = GraphQL.Execution.completeValue schema resolvers variableValues depth
                  fieldType (prefixFields ++ [later]) resolved
            ∧ resultStatus
                (completeResolvedValue schema resolvers variableValues depth fieldType
                  later.selectionSet resolved
                  (some
                    (resultValueOrNull
                      (GraphQL.Execution.completeValue schema resolvers variableValues
                        depth fieldType prefixFields resolved))))
              = visitOk
            ∧ (resultValueOrNull
                    (GraphQL.Execution.completeValue schema resolvers variableValues
                      depth fieldType prefixFields resolved)
                  ≠ .null
                -> resultValueOrNull
                      (completeResolvedValue schema resolvers variableValues depth
                        fieldType later.selectionSet resolved
                        (some
                          (resultValueOrNull
                            (GraphQL.Execution.completeValue schema resolvers
                              variableValues depth fieldType prefixFields resolved))))
                    ≠ .null) := by
  induction fieldType with
  | named typeName =>
      intro depth resolved prefixFields later hprefixChildren hobjects herrors
        hchildren
      constructor
      · exact completeValue_named_group_append_one_result_eq_spec_of_contained schema
          resolvers variableValues depth typeName resolved prefixFields later
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hprefixChildren childDepth runtimeType identity hlt
              hcontains
              (by simpa using hincludes))
          hobjects herrors
          (by
            intro childDepth runtimeType identity hlt hcontains hincludes
            exact hchildren childDepth runtimeType identity hlt
              hcontains
              (by simpa using hincludes))
      · constructor
        · exact resultStatus_completeValue_named_group_append_second_eq_ok_of_contained
            schema resolvers variableValues depth typeName resolved prefixFields
            later
            (by
              intro childDepth runtimeType identity hlt hcontains hincludes
              exact hprefixChildren childDepth runtimeType identity hlt
                hcontains
                (by simpa using hincludes))
            herrors
        · intro hprefixNonNull
          cases depth with
          | zero =>
              cases resolved <;>
                simp [GraphQL.Execution.completeValue, outOfFuel,
                  resultValueOrNull] at hprefixNonNull
          | succ childDepth =>
              cases resolved with
              | null =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | scalar value =>
                  by_cases hcomposite :
                      (TypeRef.named typeName).isCompositeBool schema = true
                  · simp [GraphQL.Execution.completeValue, resultValueOrNull,
                      hcomposite] at hprefixNonNull
                  · simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_scalar, resultValueOrNull, hcomposite]
              | list values =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | object runtimeType identity =>
                  by_cases hincludes :
                      schema.typeIncludesObjectBool typeName runtimeType = true
                  · have hrightStatus :
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            (childDepth + 1) (.named typeName)
                            later.selectionSet (.object runtimeType identity)
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema
                                resolvers variableValues (childDepth + 1)
                                (.named typeName) prefixFields
                                (.object runtimeType identity))))) =
                        visitOk :=
                      resultStatus_completeValue_named_group_append_second_eq_ok_of_contained
                        schema resolvers variableValues (childDepth + 1)
                        typeName (.object runtimeType identity) prefixFields
                        later
                        (by
                          intro childDepth' runtimeType' identity' hlt
                            hcontains hincludes'
                          exact hprefixChildren childDepth' runtimeType'
                            identity' hlt hcontains
                            (by simpa using hincludes'))
                        herrors
                    cases hprevious :
                        resultValueOrNull
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues (childDepth + 1) (.named typeName)
                            prefixFields (.object runtimeType identity)) with
                    | null =>
                        exact False.elim (hprefixNonNull hprevious)
                    | scalar previousValue =>
                        cases hcompleted :
                            GraphQL.Execution.executeCollectedFields schema
                              resolvers variableValues childDepth
                              (.object runtimeType identity)
                              (GraphQL.Execution.collectFields schema
                                variableValues runtimeType
                                (.object runtimeType identity)
                                (GraphQL.Execution.mergedFieldSelectionSet
                                  prefixFields)) with
                        | error prefixErrors =>
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                        | ok prefixResult =>
                            rcases prefixResult with
                              ⟨prefixOutput, prefixErrors⟩
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                    | object previousFields =>
                        obtain ⟨outputFields, hvisited⟩ :=
                          visitSubfields_preserves_object schema resolvers
                            variableValues childDepth runtimeType
                            (.object runtimeType identity)
                            later.selectionSet previousFields
                        have hstatus' :
                            (visitSubfields schema resolvers variableValues
                              childDepth runtimeType
                              (.object runtimeType identity)
                              later.selectionSet
                              (.object previousFields)).snd =
                            visitOk := by
                          have hprefixEq :
                              completeValue schema resolvers variableValues
                                (childDepth + 1) (.named typeName)
                                  (GraphQL.Execution.mergedFieldSelectionSet
                                    prefixFields)
                                  (.object runtimeType identity) none =
                              GraphQL.Execution.completeValue schema resolvers
                                variableValues (childDepth + 1)
                                (.named typeName) prefixFields
                                (.object runtimeType identity) :=
                            completeValue_group_eq_spec_of_contained_child_states
                              schema resolvers variableValues prefixFields
                              (childDepth + 1) typeName
                              (.object runtimeType identity)
                              (by
                                intro childDepth' runtimeType' identity' hlt
                                  hcontains hincludes'
                                exact hprefixChildren childDepth' runtimeType'
                                  identity' hlt hcontains
                                  (by simpa using hincludes'))
                          have hprefixPrev :
                              resultValueOrNull
                                (completeValue schema resolvers variableValues
                                  (childDepth + 1) (.named typeName)
                                    (GraphQL.Execution.mergedFieldSelectionSet
                                      prefixFields)
                                    (.object runtimeType identity) none) =
                              .object previousFields := by
                            rw [hprefixEq]
                            exact hprevious
                          cases hfirst :
                              visitSubfields schema resolvers variableValues
                                childDepth runtimeType
                                (.object runtimeType identity)
                                (GraphQL.Execution.mergedFieldSelectionSet
                                  prefixFields)
                                (.object []) with
                          | mk firstOutput firstStatus =>
                              cases firstStatus with
                              | error firstErrors =>
                                  simp [completeValue, hincludes,
                                    reuseOrCreateObject?, hfirst,
                                    catchVisitBubbleAsNull, resultValueOrNull]
                                    at hprefixPrev
                              | ok firstStatusResult =>
                                  rcases firstStatusResult with
                                    ⟨unitValue, firstErrors⟩
                                  cases unitValue
                                  have hfirstOutput :
                                      firstOutput = .object previousFields := by
                                    simpa [completeValue, hincludes,
                                      reuseOrCreateObject?, hfirst,
                                      catchVisitBubbleAsNull,
                                      resultValueOrNull]
                                      using hprefixPrev
                                  have herrors' :=
                                    herrors childDepth runtimeType identity
                                      (Nat.lt_succ_self childDepth)
                                      ValueContainsObject.here
                                  unfold VisitSubfieldsErrorNeutral at herrors'
                                  simpa [hfirst, hfirstOutput] using herrors'
                        have hparentComposite :
                            (TypeRef.named typeName).isCompositeBool schema =
                              true := by
                          cases hlookup : schema.lookupType typeName with
                          | none =>
                              simp [Schema.typeIncludesObjectBool,
                                Schema.getPossibleTypes, hlookup] at hincludes
                          | some typeDefinition =>
                              cases typeDefinition <;>
                                simp [TypeRef.isCompositeBool,
                                  TypeRef.namedType,
                                  Schema.typeIncludesObjectBool,
                                  Schema.getPossibleTypes, hlookup]
                                  at hincludes ⊢
                        simp [completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateObject?, hincludes, hparentComposite, hvisited, hstatus', resultValueOrNull, catchVisitBubbleAsNull, visitOk]
                    | list previousValues =>
                        cases hcompleted :
                            GraphQL.Execution.executeCollectedFields schema
                              resolvers variableValues childDepth
                              (.object runtimeType identity)
                              (GraphQL.Execution.collectFields schema
                                variableValues runtimeType
                                (.object runtimeType identity)
                                (GraphQL.Execution.mergedFieldSelectionSet
                                  prefixFields)) with
                        | error prefixErrors =>
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                        | ok prefixResult =>
                            rcases prefixResult with
                              ⟨prefixOutput, prefixErrors⟩
                            simp [GraphQL.Execution.completeValue, hincludes,
                              hcompleted, catchBubbleAsNull,
                              resultValueOrNull] at hprevious
                  · have hnotIncludes :
                        schema.typeIncludesObjectBool typeName runtimeType =
                          false := by
                      cases h :
                          schema.typeIncludesObjectBool typeName runtimeType <;>
                        simp [h] at hincludes ⊢
                    simp [GraphQL.Execution.completeValue, hnotIncludes,
                      resultValueOrNull] at hprefixNonNull
  | list inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects herrors
        hchildren
      constructor
      · cases depth with
          | zero =>
            cases resolved <;>
              simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, GraphQL.Execution.Result.combine]
          | succ childDepth =>
            cases resolved with
            | null =>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse]
            | scalar value =>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
            | object runtimeType identity =>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, GraphQL.Execution.Result.combine]
            | list values =>
                have hvalueAppend :
                    ∀ value : ResolverValue ObjectIdentity,
                    value ∈ values ->
                      GraphQL.Execution.Result.combine mergeResponse
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner prefixFields value)
                        (completeResolvedValue schema resolvers variableValues
                          childDepth inner later.selectionSet value
                          (some (resultValueOrNull
                            (GraphQL.Execution.completeValue schema resolvers
                              variableValues childDepth inner prefixFields
                              value)))) =
                      GraphQL.Execution.completeValue schema resolvers
                        variableValues childDepth inner (prefixFields ++ [later])
                        value := by
                  intro value hmem
                  exact (ih childDepth value prefixFields later
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hprefixChildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact hobjects childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact herrors childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hchildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))).left
                have hvalueStatus :
                    ∀ value : ResolverValue ObjectIdentity,
                    value ∈ values ->
                      resultStatus
                        (completeResolvedValue schema resolvers variableValues
                          childDepth inner later.selectionSet value
                          (some (resultValueOrNull
                            (GraphQL.Execution.completeValue schema resolvers
                              variableValues childDepth inner prefixFields
                          value)))) =
                        visitOk := by
                  intro value hmem
                  exact (ih childDepth value prefixFields later
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hprefixChildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact hobjects childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                      exact herrors childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains))
                    (by
                      intro childDepth' runtimeType identity hlt hcontains
                        hincludes
                      exact hchildren childDepth' runtimeType identity
                        (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                        (ValueContainsObject.list hmem hcontains)
                        (by simpa using hincludes))).right.left
                cases hcontains : inner.isCompositeBool schema with
                | false =>
                    have happendedPrefix :
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner
                          (prefixFields ++ [later]) values =
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner prefixFields values :=
                      specCompleteValueList_eq_of_no_object schema resolvers
                        variableValues childDepth inner (prefixFields ++ [later])
                        prefixFields values hcontains
                    cases hprefixList :
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner prefixFields values with
                    | error prefixErrors =>
                        have happended :
                            GraphQL.Execution.completeValueList schema
                              resolvers variableValues childDepth inner
                              (prefixFields ++ [later]) values =
                            .error prefixErrors := by
                          rw [happendedPrefix, hprefixList]
                        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefixList, happended, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                    | ok prefixResult =>
                        rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                        have happended :
                            GraphQL.Execution.completeValueList schema
                              resolvers variableValues childDepth inner
                              (prefixFields ++ [later]) values =
                            .ok (prefixValues, prefixErrors) := by
                          rw [happendedPrefix, hprefixList]
                        have hprefixReady :
                            ∀ response, response ∈ prefixValues ->
                              ResponseMergeReady response :=
                          specCompleteValueList_values_ready schema resolvers
                            variableValues childDepth inner prefixFields values
                            prefixValues prefixErrors hprefixList
                        have hself :
                            mergeResponseLists prefixValues prefixValues =
                              prefixValues :=
                          mergeResponseLists_self_of_ready prefixValues
                            hprefixReady
                        have houterContains :
                            (TypeRef.list inner).isCompositeBool schema =
                              false := by
                          simpa [TypeRef.isCompositeBool,
                            TypeRef.namedType] using hcontains
                        simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, hprefixList, happended, houterContains, hself, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                | true =>
                    have hlistAppend :=
                      completeValueList_append_result_eq_spec_of_mem schema
                        resolvers variableValues childDepth inner prefixFields
                        later values hcontains hvalueAppend hvalueStatus
                    cases hprefixList :
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner prefixFields values with
                    | error prefixErrors =>
                        have happended :
                            GraphQL.Execution.completeValueList schema resolvers
                              variableValues childDepth inner
                              (prefixFields ++ [later]) values =
                            .error prefixErrors := by
                          have hcombined := hlistAppend
                          simp [hprefixList, GraphQL.Execution.Result.combine]
                            at hcombined
                          simpa using hcombined.symm
                        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefixList, happended, resultValueOrNull, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                    | ok prefixResult =>
                        rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                        have hlistStatus :=
                          resultStatus_completeValueList_append_second_eq_ok_of_mem
                            schema resolvers variableValues childDepth inner
                            prefixFields later values hcontains hvalueStatus
                        have hrightStatus :
                            resultStatus
                              (completeValueList schema resolvers
                                variableValues childDepth inner
                                later.selectionSet values prefixValues) =
                            visitOk := by
                          simpa [hprefixList] using hlistStatus
                        cases hrightList :
                            completeValueList schema resolvers variableValues
                              childDepth inner later.selectionSet values
                              prefixValues with
                        | error rightErrors =>
                            simp [hrightList, resultStatus, visitOk]
                              at hrightStatus
                        | ok rightResult =>
                            rcases rightResult with ⟨rightValues, rightErrors⟩
                            cases rightErrors with
                            | zero =>
                                have happended :
                                    GraphQL.Execution.completeValueList schema
                                      resolvers variableValues childDepth inner
                                      (prefixFields ++ [later]) values =
                                    .ok (mergeResponseLists prefixValues
                                      rightValues, prefixErrors) := by
                                  simpa [hprefixList, hrightList,
                                    GraphQL.Execution.Result.combine]
                                    using hlistAppend.symm
                                have houterContains :
                                    (TypeRef.list inner).isCompositeBool
                                        schema =
                                      true := by
                                  simpa [TypeRef.isCompositeBool,
                                    TypeRef.namedType] using hcontains
                                simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateList?, hprefixList, hrightList, happended, resultValueOrNull, houterContains, GraphQL.Execution.Result.combine, mergeResponse, catchBubbleAsNull]
                            | succ rightErrors =>
                                simp [hrightList, resultStatus, visitOk]
                                  at hrightStatus
      · constructor
        · cases depth with
          | zero =>
              cases resolved <;>
                simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk]
          | succ childDepth =>
              cases resolved with
              | null =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
              | scalar value =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
              | object runtimeType identity =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, resultValueOrNull, resultStatus, visitOk]
              | list values =>
                  have hvalueStatus :
                      ∀ value : ResolverValue ObjectIdentity,
                      value ∈ values ->
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            childDepth inner later.selectionSet value
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema resolvers
                                variableValues childDepth inner prefixFields
                            value)))) =
                          visitOk := by
                    intro value hmem
                    exact (ih childDepth value prefixFields later
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hprefixChildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact hobjects childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact herrors childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hchildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))).right.left
                  cases hcontains : inner.isCompositeBool schema with
                  | false =>
                      have houterContains :
                          (TypeRef.list inner).isCompositeBool schema =
                            false := by
                        simpa [TypeRef.isCompositeBool,
                          TypeRef.namedType] using hcontains
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields
                            values <;>
                        simp [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, reusablePreviousValue?, houterContains, hprefixList, resultValueOrNull, resultStatus, visitOk, catchBubbleAsNull]
                  | true =>
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                      | error prefixErrors =>
                          simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefixList, resultValueOrNull, resultStatus, visitOk, catchBubbleAsNull]
                      | ok prefixResult =>
                          rcases prefixResult with ⟨prefixValues, prefixErrors⟩
                          have hlistStatus :=
                            resultStatus_completeValueList_append_second_eq_ok_of_mem
                              schema resolvers variableValues childDepth inner
                              prefixFields later values hcontains hvalueStatus
                          have hrightStatus :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues childDepth inner
                                  later.selectionSet values prefixValues) =
                              visitOk := by
                            simpa [hprefixList] using hlistStatus
                          cases hrightList :
                              completeValueList schema resolvers variableValues
                                childDepth inner later.selectionSet values
                                prefixValues with
                          | error rightErrors =>
                              simp [hrightList, resultStatus, visitOk]
                                at hrightStatus
                          | ok rightResult =>
                              rcases rightResult with
                                ⟨rightValues, rightErrors⟩
                              cases rightErrors with
                              | zero =>
                                  have houterContains :
                                      (TypeRef.list inner).isCompositeBool
                                          schema =
                                        true := by
                                    simpa [TypeRef.isCompositeBool,
                                      TypeRef.namedType] using hcontains
                                  simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateList?, houterContains, hprefixList, hrightList, resultValueOrNull, resultStatus, visitOk, catchBubbleAsNull]
                              | succ rightErrors =>
                                  simp [hrightList, resultStatus, visitOk]
                                    at hrightStatus
        · intro hprefixNonNull
          cases depth with
          | zero =>
              cases resolved <;>
                simp [GraphQL.Execution.completeValue, outOfFuel,
                  resultValueOrNull] at hprefixNonNull
          | succ childDepth =>
              cases resolved with
              | null =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | scalar value =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | object runtimeType identity =>
                  simp [GraphQL.Execution.completeValue, resultValueOrNull]
                    at hprefixNonNull
              | list values =>
                  have hvalueStatus :
                      ∀ value : ResolverValue ObjectIdentity,
                      value ∈ values ->
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            childDepth inner later.selectionSet value
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema resolvers
                                variableValues childDepth inner prefixFields
                            value)))) =
                          visitOk := by
                    intro value hmem
                    exact (ih childDepth value prefixFields later
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hprefixChildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact hobjects childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                        exact herrors childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains))
                      (by
                        intro childDepth' runtimeType identity hlt hcontains
                          hincludes
                        exact hchildren childDepth' runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list hmem hcontains)
                          (by simpa using hincludes))).right.left
                  cases hcontains : inner.isCompositeBool schema with
                  | false =>
                      have houterContains :
                          (TypeRef.list inner).isCompositeBool schema =
                            false := by
                        simpa [TypeRef.isCompositeBool,
                          TypeRef.namedType] using hcontains
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields
                            values with
                      | error prefixErrors =>
                          simp [GraphQL.Execution.completeValue, hprefixList, resultValueOrNull, catchBubbleAsNull]
                            at hprefixNonNull
                      | ok prefixResult =>
                          rcases prefixResult with
                            ⟨prefixValues, prefixErrors⟩
                          simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, houterContains, hprefixList, resultValueOrNull, catchBubbleAsNull]
                  | true =>
                      cases hprefixList :
                          GraphQL.Execution.completeValueList schema resolvers
                            variableValues childDepth inner prefixFields values with
                      | error prefixErrors =>
                          simp [GraphQL.Execution.completeValue, hprefixList, resultValueOrNull, catchBubbleAsNull]
                            at hprefixNonNull
                      | ok prefixResult =>
                          rcases prefixResult with
                            ⟨prefixValues, prefixErrors⟩
                          have hlistStatus :=
                            resultStatus_completeValueList_append_second_eq_ok_of_mem
                              schema resolvers variableValues childDepth inner
                              prefixFields later values hcontains hvalueStatus
                          have hrightStatus :
                              resultStatus
                                (completeValueList schema resolvers
                                  variableValues childDepth inner
                                  later.selectionSet values prefixValues) =
                              visitOk := by
                            simpa [hprefixList] using hlistStatus
                          cases hrightList :
                              completeValueList schema resolvers variableValues
                                childDepth inner later.selectionSet values
                                prefixValues with
                          | error rightErrors =>
                              simp [hrightList, resultStatus, visitOk]
                                at hrightStatus
                          | ok rightResult =>
                              rcases rightResult with
                                ⟨rightValues, rightErrors⟩
                              cases rightErrors with
                              | zero =>
                                  have houterContains :
                                      (TypeRef.list inner).isCompositeBool
                                          schema =
                                        true := by
                                    simpa [TypeRef.isCompositeBool,
                                      TypeRef.namedType] using hcontains
                                  simp [GraphQL.Execution.completeValue, completeResolvedValue, reusablePreviousValue?, completeValue, reuseOrCreateList?, houterContains, hprefixList, hrightList, resultValueOrNull, catchBubbleAsNull]
                              | succ rightErrors =>
                                  simp [hrightList, resultStatus, visitOk]
                                    at hrightStatus
  | nonNull inner ih =>
      intro depth resolved prefixFields later hprefixChildren hobjects herrors
        hchildren
      cases depth with
      | zero =>
          constructor <;>
            cases resolved <;>
              simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, outOfFuel, resultValueOrNull, resultStatus, visitOk, GraphQL.Execution.Result.combine]
      | succ depth =>
          have hinner :=
            ih (depth + 1) resolved prefixFields later
              (by
                intro childDepth runtimeType identity hlt hcontains hincludes
                exact hprefixChildren childDepth runtimeType identity hlt
                  hcontains
                  (by simpa using hincludes))
              hobjects herrors
              (by
                intro childDepth runtimeType identity hlt hcontains hincludes
                exact hchildren childDepth runtimeType identity hlt
                  hcontains
                  (by simpa using hincludes))
          rcases hinner with ⟨hcombine, hstatus, hnonnull⟩
          constructor
          · cases hprefix :
              GraphQL.Execution.completeValue schema resolvers variableValues
                (depth + 1) inner prefixFields resolved with
            | error prefixErrors =>
                cases hright :
                    completeResolvedValue schema resolvers variableValues
                      (depth + 1) inner later.selectionSet resolved
                      (some (resultValueOrNull
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues (depth + 1) inner prefixFields
                          resolved))) with
                | error rightErrors =>
                    have hrightStatus :
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            (depth + 1) inner later.selectionSet resolved
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema
                                resolvers variableValues (depth + 1) inner
                                prefixFields resolved)))) =
                        visitOk := hstatus
                    simp [hright, resultStatus, visitOk] at hrightStatus
                | ok rightResult =>
                    rcases rightResult with ⟨rightValue, rightErrors⟩
                    cases rightErrors with
                    | zero =>
                        have hright' :
                            completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some .null) =
                            .ok (rightValue, 0) := by
                          simpa [hprefix, resultValueOrNull,
                            completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar, reusablePreviousValue?]
                            using hright
                        have happended :
                            GraphQL.Execution.completeValue schema resolvers
                              variableValues (depth + 1) inner
                              (prefixFields ++ [later]) resolved =
                            .error prefixErrors := by
                          have hcombined := hcombine
                          simp [hprefix, hright', resultValueOrNull,
                            GraphQL.Execution.Result.combine] at hcombined
                          simpa using hcombined.symm
                        simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine]
                    | succ rightErrors =>
                        have hrightStatus :
                            resultStatus
                              (completeResolvedValue schema resolvers variableValues
                                (depth + 1) inner later.selectionSet resolved
                                (some (resultValueOrNull
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (depth + 1)
                                    inner prefixFields resolved)))) =
                            visitOk := hstatus
                        simp [hright, resultStatus, visitOk] at hrightStatus
            | ok prefixResult =>
                rcases prefixResult with ⟨prefixValue, prefixErrors⟩
                cases hright :
                    completeResolvedValue schema resolvers variableValues
                      (depth + 1) inner later.selectionSet resolved
                      (some (resultValueOrNull
                        (GraphQL.Execution.completeValue schema resolvers
                          variableValues (depth + 1) inner prefixFields
                          resolved))) with
                | error rightErrors =>
                    have hrightStatus :
                        resultStatus
                          (completeResolvedValue schema resolvers variableValues
                            (depth + 1) inner later.selectionSet resolved
                            (some (resultValueOrNull
                              (GraphQL.Execution.completeValue schema
                                resolvers variableValues (depth + 1) inner
                                prefixFields resolved)))) =
                        visitOk := hstatus
                    simp [hright, resultStatus, visitOk] at hrightStatus
                | ok rightResult =>
                    rcases rightResult with ⟨rightValue, rightErrors⟩
                    cases rightErrors with
                    | zero =>
                        have hright' :
                            completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some prefixValue) =
                            .ok (rightValue, 0) := by
                          simpa [hprefix, resultValueOrNull,
                            completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar, reusablePreviousValue?]
                            using hright
                        have happended :
                            GraphQL.Execution.completeValue schema resolvers
                              variableValues (depth + 1) inner
                              (prefixFields ++ [later]) resolved =
                            .ok (mergeResponse prefixValue rightValue,
                              prefixErrors) := by
                          have hcombined := hcombine
                          simp [hprefix, hright', resultValueOrNull,
                            GraphQL.Execution.Result.combine] at hcombined
                          simpa using hcombined.symm
                        cases prefixValue with
                        | null =>
                            cases rightValue <;>
                                simp [completeResolvedValue_previous_null] at hright'
                            simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                        | scalar prefixScalar =>
                            have hrightNonNullRaw :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues (depth + 1)
                                        inner prefixFields resolved)))) ≠
                                .null :=
                              hnonnull (by
                                simp [hprefix, resultValueOrNull])
                            have hrightNonNull :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved (some (.scalar prefixScalar))) ≠
                                .null :=
                              by
                                simpa [hprefix, resultValueOrNull]
                                  using hrightNonNullRaw
                            have hwrapped :
                                completeResolvedValue schema resolvers variableValues
                                  (depth + 1) inner.nonNull later.selectionSet
                                  resolved (some (.scalar prefixScalar)) =
                                .ok (rightValue, 0) :=
                              have hrightValueNonNull : rightValue ≠ .null := by
                                intro hnull
                                exact hrightNonNull (by
                                  simp [hright', hnull, resultValueOrNull])
                              completeResolvedValue_nonNull_ok_of_inner_ok
                                schema resolvers variableValues (depth + 1)
                                inner later.selectionSet resolved
                                (some (.scalar prefixScalar)) rightValue 0
                                hright' hrightValueNonNull
                            cases rightValue with
                            | null =>
                                exact False.elim (by
                                  have hrightValueNonNull : ResponseValue.null ≠ .null := by
                                    intro hnull
                                    exact hrightNonNull (by
                                      simp [hright', resultValueOrNull])
                                  exact hrightValueNonNull rfl)
                            | scalar rightScalar =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | object rightFields =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | list rightValues =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                        | object prefixFieldsValue =>
                            have hrightNonNullRaw :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues (depth + 1)
                                        inner prefixFields resolved)))) ≠
                                .null :=
                              hnonnull (by
                                simp [hprefix, resultValueOrNull])
                            have hrightNonNull :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved (some (.object prefixFieldsValue))) ≠
                                .null :=
                              by
                                simpa [hprefix, resultValueOrNull]
                                  using hrightNonNullRaw
                            have hwrapped :
                                completeResolvedValue schema resolvers variableValues
                                  (depth + 1) inner.nonNull later.selectionSet
                                  resolved (some (.object prefixFieldsValue)) =
                                .ok (rightValue, 0) :=
                              have hrightValueNonNull : rightValue ≠ .null := by
                                intro hnull
                                exact hrightNonNull (by
                                  simp [hright', hnull, resultValueOrNull])
                              completeResolvedValue_nonNull_ok_of_inner_ok
                                schema resolvers variableValues (depth + 1)
                                inner later.selectionSet resolved
                                (some (.object prefixFieldsValue)) rightValue 0
                                hright' hrightValueNonNull
                            cases rightValue with
                            | null =>
                                exact False.elim (by
                                  have hrightValueNonNull : ResponseValue.null ≠ .null := by
                                    intro hnull
                                    exact hrightNonNull (by
                                      simp [hright', resultValueOrNull])
                                  exact hrightValueNonNull rfl)
                            | scalar rightScalar =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | object rightFields =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | list rightValues =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                        | list prefixValues =>
                            have hrightNonNullRaw :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved
                                    (some (resultValueOrNull
                                      (GraphQL.Execution.completeValue schema
                                        resolvers variableValues (depth + 1)
                                        inner prefixFields resolved)))) ≠
                                .null :=
                              hnonnull (by
                                simp [hprefix, resultValueOrNull])
                            have hrightNonNull :
                                resultValueOrNull
                                  (completeResolvedValue schema resolvers variableValues
                                    (depth + 1) inner later.selectionSet
                                    resolved (some (.list prefixValues))) ≠
                                .null :=
                              by
                                simpa [hprefix, resultValueOrNull]
                                  using hrightNonNullRaw
                            have hwrapped :
                                completeResolvedValue schema resolvers variableValues
                                  (depth + 1) inner.nonNull later.selectionSet
                                  resolved (some (.list prefixValues)) =
                                .ok (rightValue, 0) :=
                              have hrightValueNonNull : rightValue ≠ .null := by
                                intro hnull
                                exact hrightNonNull (by
                                  simp [hright', hnull, resultValueOrNull])
                              completeResolvedValue_nonNull_ok_of_inner_ok
                                schema resolvers variableValues (depth + 1)
                                inner later.selectionSet resolved
                                (some (.list prefixValues)) rightValue 0
                                hright' hrightValueNonNull
                            cases rightValue with
                            | null =>
                                exact False.elim (by
                                  have hrightValueNonNull : ResponseValue.null ≠ .null := by
                                    intro hnull
                                    exact hrightNonNull (by
                                      simp [hright', resultValueOrNull])
                                  exact hrightValueNonNull rfl)
                            | scalar rightScalar =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | object rightFields =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                            | list rightValues =>
                                simp [GraphQL.Execution.completeValue, hprefix, hwrapped, happended, resultValueOrNull, nonNullCompletion, GraphQL.Execution.Result.combine, mergeResponse]
                    | succ rightErrors =>
                        have hrightStatus :
                            resultStatus
                              (completeResolvedValue schema resolvers variableValues
                                (depth + 1) inner later.selectionSet resolved
                                (some (resultValueOrNull
                                  (GraphQL.Execution.completeValue schema
                                    resolvers variableValues (depth + 1)
                                    inner prefixFields resolved)))) =
                            visitOk := hstatus
                        simp [hright, resultStatus, visitOk] at hrightStatus
          · constructor
            · cases hprefix :
                GraphQL.Execution.completeValue schema resolvers variableValues
                  (depth + 1) inner prefixFields resolved with
              | error prefixErrors =>
                  simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, resultValueOrNull, resultStatus, nonNullCompletion, visitOk]
              | ok prefixResult =>
                  rcases prefixResult with ⟨prefixValue, prefixErrors⟩
                  cases prefixValue with
                  | null =>
                      simp [GraphQL.Execution.completeValue, completeResolvedValue_previous_null, hprefix, resultValueOrNull, resultStatus, nonNullCompletion, visitOk]
                  | scalar prefixScalar =>
                      have hrightStatus :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.scalar prefixScalar))) =
                          visitOk := by
                        simpa [hprefix, resultValueOrNull] using hstatus
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.scalar prefixScalar))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion, resultStatus, visitOk]
                        using
                          resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.scalar prefixScalar))
                            hrightStatus hrightNonNull
                  | object prefixFieldsValue =>
                      have hrightStatus :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.object prefixFieldsValue))) =
                          visitOk := by
                        simpa [hprefix, resultValueOrNull] using hstatus
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.object prefixFieldsValue))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using
                          resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.object prefixFieldsValue))
                            hrightStatus hrightNonNull
                  | list prefixValues =>
                      have hrightStatus :
                          resultStatus
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.list prefixValues))) =
                          visitOk := by
                        simpa [hprefix, resultValueOrNull] using hstatus
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.list prefixValues))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using
                          resultStatus_completeResolvedValue_nonNull_eq_ok_of_inner_status_eq_ok_of_nonNull
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.list prefixValues))
                            hrightStatus hrightNonNull
            · intro hprefixNonNull
              cases hprefix :
                  GraphQL.Execution.completeValue schema resolvers variableValues
                    (depth + 1) inner prefixFields resolved with
              | error prefixErrors =>
                  simp [GraphQL.Execution.completeValue, hprefix, resultValueOrNull, nonNullCompletion]
                    at hprefixNonNull
              | ok prefixResult =>
                  rcases prefixResult with ⟨prefixValue, prefixErrors⟩
                  cases prefixValue with
                  | null =>
                      simp [GraphQL.Execution.completeValue, hprefix, resultValueOrNull, nonNullCompletion]
                        at hprefixNonNull
                  | scalar prefixScalar =>
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.scalar prefixScalar))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      have hproject :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner.nonNull later.selectionSet
                              resolved (some (.scalar prefixScalar))) ≠
                          .null := by
                        exact
                          resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.scalar prefixScalar)) hrightNonNull
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using hproject
                  | object prefixFieldsValue =>
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.object prefixFieldsValue))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      have hproject :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner.nonNull later.selectionSet
                              resolved (some (.object prefixFieldsValue))) ≠
                          .null := by
                        exact
                          resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.object prefixFieldsValue)) hrightNonNull
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using hproject
                  | list prefixValues =>
                      have hrightNonNullRaw :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (resultValueOrNull
                                (GraphQL.Execution.completeValue schema
                                  resolvers variableValues (depth + 1) inner
                                  prefixFields resolved)))) ≠
                          .null :=
                        hnonnull (by simp [hprefix, resultValueOrNull])
                      have hrightNonNull :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner later.selectionSet resolved
                              (some (.list prefixValues))) ≠
                          .null := by
                        simpa [hprefix, resultValueOrNull]
                          using hrightNonNullRaw
                      have hproject :
                          resultValueOrNull
                            (completeResolvedValue schema resolvers variableValues
                              (depth + 1) inner.nonNull later.selectionSet
                              resolved (some (.list prefixValues))) ≠
                          .null := by
                        exact
                          resultValueOrNull_completeResolvedValue_nonNull_ne_null_of_inner_ne_null
                            schema resolvers variableValues (depth + 1) inner
                            later.selectionSet resolved
                            (some (.list prefixValues)) hrightNonNull
                      simpa [GraphQL.Execution.completeValue, completeResolvedValue, completeResolvedValue_previous_null, completeResolvedValue_previous_scalar,
                        completeValue, hprefix, resultValueOrNull,
                        nonNullCompletion]
                        using hproject
end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
