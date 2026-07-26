import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection.State

/-!
Single-field and single-group execution bridges for append-selection equivalence.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hcomplete
      : GraphQL.Execution.singleFieldResult responseName
          (executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments selectionSet))
        = GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
            source responseName
            [executableField parentType responseName fieldName arguments selectionSet])
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet] := by
  have hleft :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]
        =
      GraphQL.Execution.singleFieldResult responseName
        (executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)) := by
    cases hfield :
        executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet) <;>
      simp only [executableField] at hfield <;>
      simp [executeRootSelectionSet, visitSubfields, visitSelection, hallowed,
        executableField, GraphQL.Execution.singleFieldResult,
        mergeResponseFieldResult, mergeResponseFieldIntoObject,
        mergeResponseField, responseObjectField?, lookupResponseField?, resultValueOrNull,
        resultStatus, visitOk, combineVisitStatus, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  have hright :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet]
        =
      GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName
        [executableField parentType responseName fieldName arguments
          selectionSet] := by
    cases hspec :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName
          [executableField parentType responseName fieldName arguments
            selectionSet] <;>
      simp only [executableField] at hspec <;>
      simp [GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        GraphQL.Execution.executeCollectedFields,
        Result.combine,
        GraphQL.Execution.Result.combine, hallowed, hspec]
  exact hleft.trans (hcomplete.trans hright.symm)

theorem executeRootSelectionSet_single_field_succ_aligned_of_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (haligned
      : RootSelectionResultAlignedEquivalent
          (GraphQL.Execution.singleFieldResult responseName
            (executeField schema resolvers variableValues depth source none
              (executableField parentType responseName fieldName arguments selectionSet)))
          (GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
            source responseName
            [executableField parentType responseName fieldName arguments selectionSet]))
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet])
        (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet]) := by
  have hleft :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]
        =
      GraphQL.Execution.singleFieldResult responseName
        (executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)) := by
    cases hfield :
        executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet) <;>
      simp only [executableField] at hfield <;>
      simp [executeRootSelectionSet, visitSubfields, visitSelection, hallowed,
        executableField, GraphQL.Execution.singleFieldResult,
        mergeResponseFieldResult, mergeResponseFieldIntoObject,
        mergeResponseField, responseObjectField?, lookupResponseField?,
        resultValueOrNull, resultStatus, visitOk, combineVisitStatus,
        Result.combine, GraphQL.Execution.Result.combine, hfield]
  have hright :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet]
        =
      GraphQL.Execution.executeField schema resolvers variableValues (depth + 1)
        source responseName
        [executableField parentType responseName fieldName arguments
          selectionSet] := by
    cases hspec :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName
          [executableField parentType responseName fieldName arguments
            selectionSet] <;>
      simp only [executableField] at hspec <;>
      simp [GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        GraphQL.Execution.executeCollectedFields,
        Result.combine,
        GraphQL.Execution.Result.combine, hallowed, hspec]
  exact
    RootSelectionResultAlignedEquivalent.trans
      (RootSelectionResultAlignedEquivalent.of_eq hleft)
      (RootSelectionResultAlignedEquivalent.trans haligned
        (RootSelectionResultAlignedEquivalent.of_eq hright.symm))

theorem completeValue_object_group_eq_spec_of_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (hchild
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
              }
            initial := .object []
          })
    : completeValue schema resolvers variableValues (childDepth + 1)
        parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
        (.object runtimeType identity) none
      = GraphQL.Execution.completeValue schema resolvers variableValues
          (childDepth + 1) parentType fields (.object runtimeType identity) := by
  cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, hincludes]
  | true =>
      unfold ExecutionStateEquivalent ResponseResultEquivalent at hchild
      unfold ExecutionEquivalenceState.ungroupedProjectionResult at hchild
      unfold ExecutionEquivalenceState.specProjectionResult at hchild
      unfold ExecutionWindow.visitSubfieldsResult at hchild
      simp only [hincludes, GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, reuseOrCreateObject?]
      rw [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
      cases hvisit :
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet fields) (.object []) with
      | mk output status =>
          cases hcompleted :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues childDepth (.object runtimeType identity)
                (GraphQL.Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet fields)) with
          | error errors =>
              cases status with
              | error visitErrors =>
                  simpa [hvisit, hcompleted, reuseOrCreateObject?,
                    catchVisitBubbleAsNull,
                    GraphQL.Execution.catchBubbleAsNull] using hchild
              | ok statusResult =>
                  rcases statusResult with ⟨unitValue, visitErrors⟩
                  cases unitValue
                  simp [hvisit, hcompleted] at hchild
          | ok completed =>
              rcases completed with ⟨completedFields, completedErrors⟩
              have hnodup : PairKeysNodup completedFields := by
                have hcollected :=
                  executeCollectedFields_collectFields_pairKeysNodup schema
                    resolvers variableValues childDepth runtimeType
                    (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet fields)
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.Result.getD, hcompleted] using hcollected
              have hmerge :
                  mergeResponse (.object []) (.object completedFields) =
                    .object completedFields :=
                mergeResponse_empty_object_left_of_pairKeysNodup completedFields
                  hnodup
              cases status with
              | error visitErrors =>
                  simp [hvisit, hcompleted, hmerge] at hchild
              | ok statusResult =>
                  rcases statusResult with ⟨unitValue, visitErrors⟩
                  cases unitValue
                  simpa [hvisit, hcompleted, hmerge, reuseOrCreateObject?,
                    catchVisitBubbleAsNull,
                    GraphQL.Execution.catchBubbleAsNull] using hchild

theorem completeValue_object_group_eq_spec_of_guarded_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (hchild
      : schema.typeIncludesObjectBool parentType runtimeType = true
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
                  selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                }
              initial := .object []
            })
    : completeValue schema resolvers variableValues (childDepth + 1)
        parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
        (.object runtimeType identity) none
      = GraphQL.Execution.completeValue schema resolvers variableValues
          (childDepth + 1) parentType fields (.object runtimeType identity) := by
  cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, hincludes]
  | true =>
      exact
        completeValue_object_group_eq_spec_of_merged_child_state schema
          resolvers variableValues childDepth parentType runtimeType identity
          fields (hchild hincludes)

theorem completeValue_object_group_aligned_of_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (hchild
      : RootSelectionResultAlignedEquivalent
          (executeRootSelectionSet schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet fields))
          (GraphQL.Execution.executeRootSelectionSet schema resolvers
            variableValues childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet fields)))
    : ResponseValueResultAlignedEquivalent
        (completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) (GraphQL.Execution.mergedFieldSelectionSet fields)
          (.object runtimeType identity) none)
        (GraphQL.Execution.completeValue schema resolvers variableValues
          (childDepth + 1) (.named parentType) fields
          (.object runtimeType identity)) := by
  cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, hincludes,
        ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | true =>
      unfold executeRootSelectionSet GraphQL.Execution.executeRootSelectionSet
        at hchild
      simp only [hincludes, GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, reuseOrCreateObject?]
      rw [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
      cases hvisit :
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet fields) (.object []) with
      | mk output status =>
          obtain ⟨outputFields, houtput⟩ :=
            visitSubfields_preserves_object schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet fields) []
          rw [hvisit] at houtput
          simp at houtput
          subst output
          cases hcompleted :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues childDepth (.object runtimeType identity)
                (GraphQL.Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet fields)) with
          | error completedErrors =>
              cases status with
              | error visitErrors =>
                  simpa [hvisit, hcompleted, catchVisitBubbleAsNull,
                    GraphQL.Execution.catchBubbleAsNull,
                    ResponseValueResultAlignedEquivalent,
                    RootSelectionResultAlignedEquivalent,
                    ErrorPresenceEquivalent] using hchild
              | ok statusResult =>
                  rcases statusResult with ⟨unitValue, visitErrors⟩
                  cases unitValue
                  simp [hvisit, hcompleted,
                    RootSelectionResultAlignedEquivalent] at hchild
          | ok completed =>
              rcases completed with ⟨completedFields, completedErrors⟩
              cases status with
              | error visitErrors =>
                  simp [hvisit, hcompleted,
                    RootSelectionResultAlignedEquivalent] at hchild
              | ok statusResult =>
                  rcases statusResult with ⟨unitValue, visitErrors⟩
                  cases unitValue
                  simpa [hvisit, hcompleted, catchVisitBubbleAsNull,
                    GraphQL.Execution.catchBubbleAsNull,
                    ResponseValueResultAlignedEquivalent,
                    RootSelectionResultAlignedEquivalent,
                    ErrorPresenceEquivalent] using hchild

theorem completeValue_object_group_aligned_of_guarded_merged_child_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (fields : List ExecutableField)
    (hchild
      : schema.typeIncludesObjectBool parentType runtimeType = true
        -> RootSelectionResultAlignedEquivalent
            (executeRootSelectionSet schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet fields))
            (GraphQL.Execution.executeRootSelectionSet schema resolvers
              variableValues childDepth runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet fields)))
    : ResponseValueResultAlignedEquivalent
        (completeValue schema resolvers variableValues (childDepth + 1)
          (.named parentType) (GraphQL.Execution.mergedFieldSelectionSet fields)
          (.object runtimeType identity) none)
        (GraphQL.Execution.completeValue schema resolvers variableValues
          (childDepth + 1) (.named parentType) fields
          (.object runtimeType identity)) := by
  cases hincludes :
      schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
        GraphQL.Execution.completeValue, hincludes,
        ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | true =>
      exact
        completeValue_object_group_aligned_of_merged_child_state schema
          resolvers variableValues childDepth parentType runtimeType identity
          fields (hchild hincludes)

theorem completeValue_named_group_aligned_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : ∀ (depth : Nat) (parentType : Name) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool parentType runtimeType = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet fields))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet fields)))
        -> ResponseValueResultAlignedEquivalent
            (completeValue schema resolvers variableValues depth (.named parentType)
              (GraphQL.Execution.mergedFieldSelectionSet fields) value none)
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              (.named parentType) fields value) := by
  intro depth parentType value hchildren
  cases depth with
  | zero =>
      cases value <;>
        simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
          GraphQL.Execution.completeValue, outOfFuel,
          ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | succ childDepth =>
      cases value with
      | null =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue, ResponseValueResultAlignedEquivalent,
            ErrorPresenceEquivalent]
      | scalar value =>
          by_cases hcomposite :
              (TypeRef.named parentType).isCompositeBool schema = true
          · simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, hcomposite,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          · simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, hcomposite,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | object runtimeType identity =>
          exact
            completeValue_object_group_aligned_of_guarded_merged_child_state
              schema resolvers variableValues childDepth parentType runtimeType
              identity fields
              (by
                intro hincludes
                exact hchildren childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth) hincludes)
      | list values =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue, ResponseValueResultAlignedEquivalent,
            ErrorPresenceEquivalent]

theorem completeValue_group_aligned_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : ∀ (fieldType : TypeRef) (depth : Nat) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet fields))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet fields)))
        -> ResponseValueResultAlignedEquivalent
            (completeValue schema resolvers variableValues depth fieldType
              (GraphQL.Execution.mergedFieldSelectionSet fields) value none)
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              fieldType fields value) := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro depth value hchildren
      exact
        completeValue_named_group_aligned_of_guarded_merged_child_states
          schema resolvers variableValues fields depth typeName value
          (by
            intro childDepth runtimeType identity hlt hincludes
            exact hchildren childDepth runtimeType identity hlt hincludes)
  | list inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | scalar scalarValue =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | object runtimeType identity =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | list values =>
              have hlist :
                  ListResponseResultAlignedEquivalent
                    (completeValueList schema resolvers variableValues childDepth
                      inner (GraphQL.Execution.mergedFieldSelectionSet fields)
                      values [])
                    (GraphQL.Execution.completeValueList schema resolvers
                      variableValues childDepth inner fields values) := by
                induction values with
                | nil =>
                    simp [completeValueList,
                      GraphQL.Execution.completeValueList,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent]
                | cons head tail ihTail =>
                    have hhead :
                        ResponseValueResultAlignedEquivalent
                          (completeValue schema resolvers variableValues
                            childDepth inner
                            (GraphQL.Execution.mergedFieldSelectionSet fields)
                            head none)
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues childDepth inner fields head) :=
                      ih childDepth head
                        (by
                          intro grandChildDepth runtimeType identity hlt
                            hincludes
                          exact hchildren grandChildDepth runtimeType identity
                            (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                            (by simpa [TypeRef.namedType] using hincludes))
                    have htail : ListResponseResultAlignedEquivalent
                        (completeValueList schema resolvers variableValues
                          childDepth inner
                          (GraphQL.Execution.mergedFieldSelectionSet fields)
                          tail [])
                        (GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner fields tail) :=
                      ihTail
                    simpa [completeValueList,
                      GraphQL.Execution.completeValueList,
                      GraphQL.Execution.Result.combine] using
                      ListResponseResultAlignedEquivalent.combine_cons
                        hhead htail
              simpa [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue, reuseOrCreateList?] using
                ListResponseResultAlignedEquivalent.catchBubbleAsNull hlist
  | nonNull inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [completeValue, GraphQL.Execution.completeValue, outOfFuel,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | succ depth =>
          have hinner :
              ResponseValueResultAlignedEquivalent
                (completeValue schema resolvers variableValues (depth + 1)
                  inner (GraphQL.Execution.mergedFieldSelectionSet fields)
                  value none)
                (GraphQL.Execution.completeValue schema resolvers
                  variableValues (depth + 1) inner fields value) :=
            ih (depth + 1) value
              (by
                intro childDepth runtimeType identity hlt hincludes
                exact hchildren childDepth runtimeType identity hlt
                  (by simpa [TypeRef.namedType] using hincludes))
          simpa [completeValue, GraphQL.Execution.completeValue] using
            ResponseValueResultAlignedEquivalent.nonNullCompletion_aligned hinner

theorem completeValue_group_aligned_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : ∀ (fieldType : TypeRef) (depth : Nat) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject value runtimeType identity
          -> schema.typeIncludesObjectBool fieldType.namedType runtimeType = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet fields))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet fields)))
        -> ResponseValueResultAlignedEquivalent
            (completeValue schema resolvers variableValues depth fieldType
              (GraphQL.Execution.mergedFieldSelectionSet fields) value none)
            (GraphQL.Execution.completeValue schema resolvers variableValues depth
              fieldType fields value) := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | scalar value =>
              by_cases hcomposite :
                  (TypeRef.named typeName).isCompositeBool schema = true
              · simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                  GraphQL.Execution.completeValue, hcomposite,
                  ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
              · simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                  GraphQL.Execution.completeValue, hcomposite,
                  ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | object runtimeType identity =>
              exact
                completeValue_object_group_aligned_of_guarded_merged_child_state
                  schema resolvers variableValues childDepth typeName
                  runtimeType identity fields
                  (by
                    intro hincludes
                    exact hchildren childDepth runtimeType identity
                      (Nat.lt_succ_self childDepth)
                      ValueContainsObject.here hincludes)
          | list values =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
  | list inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | scalar scalarValue =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | object runtimeType identity =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue,
                ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
          | list values =>
              have hlist :
                  ListResponseResultAlignedEquivalent
                    (completeValueList schema resolvers variableValues childDepth
                      inner (GraphQL.Execution.mergedFieldSelectionSet fields)
                      values [])
                    (GraphQL.Execution.completeValueList schema resolvers
                      variableValues childDepth inner fields values) := by
                induction values with
                | nil =>
                    simp [completeValueList,
                      GraphQL.Execution.completeValueList,
                      ListResponseResultAlignedEquivalent,
                      ErrorPresenceEquivalent]
                | cons head tail ihTail =>
                    have hhead :
                        ResponseValueResultAlignedEquivalent
                          (completeValue schema resolvers variableValues
                            childDepth inner
                            (GraphQL.Execution.mergedFieldSelectionSet fields)
                            head none)
                          (GraphQL.Execution.completeValue schema resolvers
                            variableValues childDepth inner fields head) :=
                      ih childDepth head
                        (by
                          intro grandChildDepth runtimeType identity hlt
                            hcontains hincludes
                          exact hchildren grandChildDepth runtimeType identity
                            (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                            (ValueContainsObject.list (by simp) hcontains)
                            (by simpa [TypeRef.namedType] using hincludes))
                    have htail : ListResponseResultAlignedEquivalent
                        (completeValueList schema resolvers variableValues
                          childDepth inner
                          (GraphQL.Execution.mergedFieldSelectionSet fields)
                          tail [])
                        (GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner fields tail) := by
                      apply ihTail
                      intro grandChildDepth runtimeType identity hlt hcontains
                        hincludes
                      cases hcontains with
                      | list hmem hinner =>
                          exact hchildren grandChildDepth runtimeType identity
                            hlt
                            (ValueContainsObject.list (by simp [hmem])
                              hinner)
                            (by simpa [TypeRef.namedType] using hincludes)
                    simpa [completeValueList,
                      GraphQL.Execution.completeValueList,
                      GraphQL.Execution.Result.combine] using
                      ListResponseResultAlignedEquivalent.combine_cons
                        hhead htail
              simpa [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue, reuseOrCreateList?] using
                ListResponseResultAlignedEquivalent.catchBubbleAsNull hlist
  | nonNull inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [completeValue, GraphQL.Execution.completeValue, outOfFuel,
              ResponseValueResultAlignedEquivalent, ErrorPresenceEquivalent]
      | succ depth =>
          have hinner :
              ResponseValueResultAlignedEquivalent
                (completeValue schema resolvers variableValues (depth + 1)
                  inner (GraphQL.Execution.mergedFieldSelectionSet fields)
                  value none)
                (GraphQL.Execution.completeValue schema resolvers
                  variableValues (depth + 1) inner fields value) :=
            ih (depth + 1) value
              (by
                intro childDepth runtimeType identity hlt hcontains hincludes
                exact hchildren childDepth runtimeType identity hlt hcontains
                  (by simpa [TypeRef.namedType] using hincludes))
          simpa [completeValue, GraphQL.Execution.completeValue] using
            ResponseValueResultAlignedEquivalent.nonNullCompletion_aligned hinner

theorem completeValueList_object_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    : ∀ (objects : List (Name × ObjectIdentity)),
        (∀ object,
          object ∈ objects
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := object.fst
                    source := .object object.fst object.snd
                    selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                  }
                initial := .object []
              })
        -> completeValueList schema resolvers variableValues (childDepth + 1)
              parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
              (objects.map
                (fun object =>
                  (.object object.fst object.snd : ResolverValue ObjectIdentity)))
              []
            = GraphQL.Execution.completeValueList schema resolvers variableValues
                (childDepth + 1) parentType fields
                (objects.map
                  (fun object =>
                    (.object object.fst object.snd : ResolverValue ObjectIdentity)))
  | [], _hchildren => by
      simp [completeValueList, GraphQL.Execution.completeValueList]
  | object :: rest, hchildren => by
      have hhead :
          completeValue schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (.object object.fst object.snd) none =
          GraphQL.Execution.completeValue schema resolvers variableValues
            (childDepth + 1) parentType fields
            (.object object.fst object.snd) :=
        completeValue_object_group_eq_spec_of_merged_child_state schema
          resolvers variableValues childDepth parentType object.fst object.snd
          fields (hchildren object (by simp))
      have hrest :
          completeValueList schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity)))
            [] =
          GraphQL.Execution.completeValueList schema resolvers variableValues
            (childDepth + 1) parentType fields
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity))) :=
        completeValueList_object_group_eq_spec_of_merged_child_states schema
          resolvers variableValues childDepth parentType fields rest
          (by
            intro restObject hmem
            exact hchildren restObject (by simp [hmem]))
      simp [List.map_cons, completeValueList,
        GraphQL.Execution.completeValueList, hhead, hrest, Result.combine,
        GraphQL.Execution.Result.combine]

theorem completeValueList_object_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    : ∀ (objects : List (Name × ObjectIdentity)),
        (∀ object,
          object ∈ objects
          -> schema.typeIncludesObjectBool parentType object.fst = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := object.fst
                    source := .object object.fst object.snd
                    selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                  }
                initial := .object []
              })
        -> completeValueList schema resolvers variableValues (childDepth + 1)
              parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
              (objects.map
                (fun object =>
                  (.object object.fst object.snd : ResolverValue ObjectIdentity)))
              []
            = GraphQL.Execution.completeValueList schema resolvers variableValues
                (childDepth + 1) parentType fields
                (objects.map
                  (fun object =>
                    (.object object.fst object.snd : ResolverValue ObjectIdentity)))
  | [], _hchildren => by
      simp [completeValueList, GraphQL.Execution.completeValueList]
  | object :: rest, hchildren => by
      have hhead :
          completeValue schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (.object object.fst object.snd) none =
          GraphQL.Execution.completeValue schema resolvers variableValues
            (childDepth + 1) parentType fields
            (.object object.fst object.snd) :=
        completeValue_object_group_eq_spec_of_guarded_merged_child_state schema
          resolvers variableValues childDepth parentType object.fst object.snd
          fields
          (by
            intro hincludes
            exact hchildren object (by simp) hincludes)
      have hrest :
          completeValueList schema resolvers variableValues (childDepth + 1)
            parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity)))
            [] =
          GraphQL.Execution.completeValueList schema resolvers variableValues
            (childDepth + 1) parentType fields
            (rest.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity))) :=
        completeValueList_object_group_eq_spec_of_guarded_merged_child_states
          schema resolvers variableValues childDepth parentType fields rest
          (by
            intro restObject hmem hincludes
            exact hchildren restObject (by simp [hmem]) hincludes)
      simp [List.map_cons, completeValueList,
        GraphQL.Execution.completeValueList, hhead, hrest, Result.combine,
        GraphQL.Execution.Result.combine]

theorem completeValue_object_list_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    (objects : List (Name × ObjectIdentity))
    (_hchildren
      : ∀ object,
          object ∈ objects
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := object.fst
                    source := .object object.fst object.snd
                    selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                  }
                initial := .object []
              })
    : completeValue schema resolvers variableValues (childDepth + 2)
        parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
        (.list
          (objects.map
            (fun object =>
              (.object object.fst object.snd : ResolverValue ObjectIdentity))))
        none
      = GraphQL.Execution.completeValue schema resolvers variableValues
          (childDepth + 2) parentType fields
          (.list
            (objects.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity)))) := by
  simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
    GraphQL.Execution.completeValue]

theorem completeValue_object_list_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (childDepth : Nat)
    (parentType : Name) (fields : List ExecutableField)
    (objects : List (Name × ObjectIdentity))
    (_hchildren
      : ∀ object,
          object ∈ objects
          -> schema.typeIncludesObjectBool parentType object.fst = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := object.fst
                    source := .object object.fst object.snd
                    selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                  }
                initial := .object []
              })
    : completeValue schema resolvers variableValues (childDepth + 2)
        parentType (GraphQL.Execution.mergedFieldSelectionSet fields)
        (.list
          (objects.map
            (fun object =>
              (.object object.fst object.snd : ResolverValue ObjectIdentity))))
        none
      = GraphQL.Execution.completeValue schema resolvers variableValues
          (childDepth + 2) parentType fields
          (.list
            (objects.map
              (fun object =>
                (.object object.fst object.snd : ResolverValue ObjectIdentity)))) := by
  simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
    GraphQL.Execution.completeValue]

theorem completeValue_group_eq_spec_of_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : ∀ (depth : Nat) (parentType : Name) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
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
                    selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                  }
                initial := .object []
              })
        -> completeValue schema resolvers variableValues depth parentType
              (GraphQL.Execution.mergedFieldSelectionSet fields) value none
            = GraphQL.Execution.completeValue schema resolvers variableValues depth
                parentType fields value := by
  intro depth parentType value hchildren
  cases depth with
  | zero =>
      cases value <;>
        simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
          GraphQL.Execution.completeValue, outOfFuel]
  | succ childDepth =>
      cases value with
      | null =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | scalar value =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_merged_child_state schema
              resolvers variableValues childDepth parentType runtimeType
              identity fields
              (hchildren childDepth runtimeType identity
                (Nat.lt_succ_self childDepth))
      | list values =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]

theorem completeValue_group_eq_spec_of_guarded_merged_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : ∀ (depth : Nat) (parentType : Name) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                  }
                initial := .object []
              })
        -> completeValue schema resolvers variableValues depth parentType
              (GraphQL.Execution.mergedFieldSelectionSet fields) value none
            = GraphQL.Execution.completeValue schema resolvers variableValues depth
                parentType fields value := by
  intro depth parentType value hchildren
  cases depth with
  | zero =>
      cases value <;>
        simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
          GraphQL.Execution.completeValue, outOfFuel]
  | succ childDepth =>
      cases value with
      | null =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | scalar value =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_guarded_merged_child_state
              schema resolvers variableValues childDepth parentType runtimeType
              identity fields
              (by
                intro hincludes
                exact hchildren childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth) hincludes)
      | list values =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]

theorem completeValue_group_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (fields : List ExecutableField)
    : ∀ (depth : Nat) (parentType : Name) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject value runtimeType identity
          -> schema.typeIncludesObjectBool parentType runtimeType = true
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
                    selectionSet := GraphQL.Execution.mergedFieldSelectionSet fields
                  }
                initial := .object []
              })
        -> completeValue schema resolvers variableValues depth parentType
              (GraphQL.Execution.mergedFieldSelectionSet fields) value none
            = GraphQL.Execution.completeValue schema resolvers variableValues depth
                parentType fields value := by
  intro depth parentType value hchildren
  cases depth with
  | zero =>
      cases value <;>
        simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
          GraphQL.Execution.completeValue, outOfFuel]
  | succ childDepth =>
      cases value with
      | null =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | scalar value =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]
      | object runtimeType identity =>
          exact
            completeValue_object_group_eq_spec_of_guarded_merged_child_state
              schema resolvers variableValues childDepth parentType runtimeType
              identity fields
              (by
                intro hincludes
                exact hchildren childDepth runtimeType identity
                  (Nat.lt_succ_self childDepth)
                  ValueContainsObject.here hincludes)
      | list values =>
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue]

theorem completeValue_single_field_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (field : ExecutableField)
    : ∀ (fieldType : TypeRef) (depth : Nat) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
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
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
        -> completeValue schema resolvers variableValues depth fieldType
              field.selectionSet value none
            = GraphQL.Execution.completeValue schema resolvers variableValues depth
                fieldType [field] value := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                completeValue_object_group_eq_spec_of_guarded_merged_child_state
                  schema
                  resolvers variableValues childDepth typeName runtimeType
                  identity [field]
                  (by
                    intro hincludes
                    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                      hchildren childDepth runtimeType identity
                        (Nat.lt_succ_self childDepth) hincludes)
          | list values =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
  | list inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | list values =>
              have hlist :
                  completeValueList schema resolvers variableValues childDepth
                    inner field.selectionSet values [] =
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues childDepth inner [field] values := by
                induction values with
                | nil =>
                    simp [completeValueList, GraphQL.Execution.completeValueList]
                | cons value rest ihValues =>
                    have hhead :
                        completeValue schema resolvers variableValues
                          childDepth inner field.selectionSet value
                          none =
                        GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner [field] value :=
                      ih childDepth value (by
                        intro grandChildDepth runtimeType identity hlt
                          hincludes
                        exact hchildren grandChildDepth runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          hincludes)
                    have htail :
                        completeValueList schema resolvers variableValues
                          childDepth inner field.selectionSet rest [] =
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner [field] rest :=
                      ihValues
                    simp [completeValueList, GraphQL.Execution.completeValueList, hhead, htail, GraphQL.Execution.Result.combine]
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue, reuseOrCreateList?, hlist,
                catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull]
  | nonNull inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          have hinner :
              completeValue schema resolvers variableValues (childDepth + 1)
                inner field.selectionSet value none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                (childDepth + 1) inner [field] value :=
            ih (childDepth + 1) value (by
              intro grandChildDepth runtimeType identity hlt hincludes
              exact hchildren grandChildDepth runtimeType identity hlt
                hincludes)
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue, hinner]

theorem completeValue_single_field_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (field : ExecutableField)
    : ∀ (fieldType : TypeRef) (depth : Nat) (value : ResolverValue ObjectIdentity),
        (∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject value runtimeType identity
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
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
        -> completeValue schema resolvers variableValues depth fieldType
              field.selectionSet value none
            = GraphQL.Execution.completeValue schema resolvers variableValues depth
                fieldType [field] value := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                completeValue_object_group_eq_spec_of_guarded_merged_child_state
                  schema
                  resolvers variableValues childDepth typeName runtimeType
                  identity [field]
                  (by
                    intro hincludes
                    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
                      hchildren childDepth runtimeType identity
                        (Nat.lt_succ_self childDepth)
                        ValueContainsObject.here hincludes)
          | list values =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
  | list inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          cases value with
          | null =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | scalar value =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | object runtimeType identity =>
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue]
          | list values =>
              have hlist :
                  completeValueList schema resolvers variableValues childDepth
                    inner field.selectionSet values [] =
                  GraphQL.Execution.completeValueList schema resolvers
                    variableValues childDepth inner [field] values := by
                induction values with
                | nil =>
                    simp [completeValueList, GraphQL.Execution.completeValueList]
                | cons value rest ihValues =>
                    have hhead :
                        completeValue schema resolvers variableValues
                          childDepth inner field.selectionSet value
                          none =
                        GraphQL.Execution.completeValue schema resolvers
                          variableValues childDepth inner [field] value :=
                      ih childDepth value (by
                        intro grandChildDepth runtimeType identity hlt
                          hcontains hincludes
                        exact hchildren grandChildDepth runtimeType identity
                          (Nat.lt_trans hlt (Nat.lt_succ_self childDepth))
                          (ValueContainsObject.list (by simp) hcontains)
                          hincludes)
                    have htail :
                        completeValueList schema resolvers variableValues
                          childDepth inner field.selectionSet rest [] =
                        GraphQL.Execution.completeValueList schema resolvers
                          variableValues childDepth inner [field] rest := by
                      apply ihValues
                      intro grandChildDepth runtimeType identity hlt hcontains
                        hincludes
                      have hcontainsCons :
                          ValueContainsObject (.list (value :: rest))
                            runtimeType identity := by
                        cases hcontains with
                        | list hmem hvalue =>
                            exact ValueContainsObject.list (by simp [hmem])
                              hvalue
                      exact hchildren grandChildDepth runtimeType identity hlt
                        hcontainsCons hincludes
                    simp [completeValueList, GraphQL.Execution.completeValueList, hhead, htail, GraphQL.Execution.Result.combine]
              simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
                GraphQL.Execution.completeValue, reuseOrCreateList?, hlist,
                catchBubbleAsNull, GraphQL.Execution.catchBubbleAsNull]
  | nonNull inner ih =>
      intro depth value hchildren
      cases depth with
      | zero =>
          cases value <;>
            simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
              GraphQL.Execution.completeValue, outOfFuel]
      | succ childDepth =>
          have hinner :
              completeValue schema resolvers variableValues (childDepth + 1)
                inner field.selectionSet value none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                (childDepth + 1) inner [field] value :=
            ih (childDepth + 1) value (by
              intro grandChildDepth runtimeType identity hlt hcontains
                hincludes
              exact hchildren grandChildDepth runtimeType identity hlt
                hcontains hincludes)
          simp [GraphQL.Algorithms.ExecutionUngrouped.completeValue,
            GraphQL.Execution.completeValue, hinner]

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
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
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [executeField, GraphQL.Execution.executeField, executableField,
        hlookup, GraphQL.Execution.singleFieldResult]
  | some fieldDefinition =>
      cases resolved with
      | none =>
          simp [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult]
      | some resolvedValue =>
          have hcomplete :
              completeValue schema resolvers variableValues depth
                fieldDefinition.outputType selectionSet resolvedValue
                none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldDefinition.outputType
                [executableField parentType responseName fieldName arguments
                  selectionSet]
                resolvedValue :=
            completeValue_single_field_eq_spec_of_guarded_child_states schema
              resolvers variableValues
              (executableField parentType responseName fieldName arguments
                selectionSet)
              fieldDefinition.outputType depth resolvedValue
              (by
                intro childDepth runtimeType identity hlt _hincludes
                exact hchildren childDepth runtimeType identity hlt)
          simpa [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult] using
            congrArg (GraphQL.Execution.singleFieldResult responseName)
              hcomplete

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                runtimeType
              = true
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
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [executeField, GraphQL.Execution.executeField, executableField,
        hlookup, GraphQL.Execution.singleFieldResult]
  | some fieldDefinition =>
      cases resolved with
      | none =>
          simp [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult]
      | some resolvedValue =>
          have hcomplete :
              completeValue schema resolvers variableValues depth
                fieldDefinition.outputType selectionSet resolvedValue
                none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldDefinition.outputType
                [executableField parentType responseName fieldName arguments
                  selectionSet]
                resolvedValue :=
            completeValue_single_field_eq_spec_of_guarded_child_states schema
              resolvers variableValues
              (executableField parentType responseName fieldName arguments
                selectionSet)
              fieldDefinition.outputType depth resolvedValue
              (by
                intro childDepth runtimeType identity hlt hincludes
                exact hchildren childDepth runtimeType identity hlt
                  (by simpa [Schema.fieldReturnType?, hlookup] using hincludes))
          simpa [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult] using
            congrArg (GraphQL.Execution.singleFieldResult responseName)
              hcomplete

theorem executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                runtimeType
              = true
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
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet] := by
  apply executeRootSelectionSet_single_field_succ_eq_spec_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [executeField, GraphQL.Execution.executeField, executableField,
        hlookup, GraphQL.Execution.singleFieldResult]
  | some fieldDefinition =>
      cases resolved with
      | none =>
          simp [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult]
      | some resolvedValue =>
          have hcomplete :
              completeValue schema resolvers variableValues depth
                fieldDefinition.outputType selectionSet resolvedValue
                none =
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth fieldDefinition.outputType
                [executableField parentType responseName fieldName arguments
                  selectionSet]
                resolvedValue :=
            completeValue_single_field_eq_spec_of_contained_child_states schema
              resolvers variableValues
              (executableField parentType responseName fieldName arguments
                selectionSet)
              fieldDefinition.outputType depth resolvedValue
              (by
                intro childDepth runtimeType identity hlt hcontains hincludes
                exact hchildren childDepth runtimeType identity hlt hcontains
                  (by simpa [Schema.fieldReturnType?, hlookup] using hincludes))
          simpa [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult] using
            congrArg (GraphQL.Execution.singleFieldResult responseName)
              hcomplete

theorem executeRootSelectionSet_single_field_succ_aligned_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) selectionSet)
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                selectionSet))
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet])
        (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet]) := by
  apply executeRootSelectionSet_single_field_succ_aligned_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments directives selectionSet hallowed
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [executeField, GraphQL.Execution.executeField, executableField,
        hlookup, GraphQL.Execution.singleFieldResult,
        RootSelectionResultAlignedEquivalent, ErrorPresenceEquivalent]
  | some fieldDefinition =>
      cases resolved with
      | none =>
          cases fieldDefinition with
          | mk definitionName outputType definitionArguments =>
              cases outputType <;>
                simp [executeField, GraphQL.Execution.executeField,
                  executableField, reusablePreviousValue?_none, hlookup,
                  hresolve, handleFieldError,
                  GraphQL.Execution.singleFieldResult,
                  RootSelectionResultAlignedEquivalent,
                  ErrorPresenceEquivalent]
      | some resolvedValue =>
          have hcomplete :
              ResponseValueResultAlignedEquivalent
                (completeValue schema resolvers variableValues depth
                  fieldDefinition.outputType selectionSet resolvedValue none)
                (GraphQL.Execution.completeValue schema resolvers variableValues
                  depth fieldDefinition.outputType
                  [executableField parentType responseName fieldName arguments
                    selectionSet]
                  resolvedValue) := by
            have hgroup :=
              completeValue_group_aligned_of_contained_child_states schema
                resolvers variableValues
                [executableField parentType responseName fieldName arguments
                  selectionSet]
                fieldDefinition.outputType depth resolvedValue
                (by
                  intro childDepth runtimeType identity hlt hcontains hincludes
                  simpa [GraphQL.Execution.mergedFieldSelectionSet,
                    executableField] using
                    hchildren childDepth runtimeType identity hlt hcontains
                      (by simpa [Schema.fieldReturnType?, hlookup] using
                        hincludes))
            simpa [GraphQL.Execution.mergedFieldSelectionSet, executableField]
              using hgroup
          simpa [executeField, GraphQL.Execution.executeField, executableField,
            reusablePreviousValue?_none, hlookup, hresolve,
            GraphQL.Execution.singleFieldResult] using
            ResponseValueResultAlignedEquivalent.singleFieldResult responseName
              hcomplete

end ExecutionUngrouped
end Algorithms

end GraphQL
