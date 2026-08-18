import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionSuccess
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SemanticSeparation

/-!
Singleton response projection lemmas.

These are algebraic/execution facts used to recover a singleton target field from
a whole selection-set response after successful tail execution has been appended.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem executeField_ok_responseFields_singleton
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (responseName : Name) (fields : List Execution.ExecutableField)
    (responseFields : List (Name × Execution.ResponseValue))
    (errors : Nat)
    : Execution.executeField schema resolvers variableValues fuel source
          responseName fields
        = .ok (responseFields, errors)
      -> ∃ responseValue, responseFields = [(responseName, responseValue)] := by
  intro hok
  cases fields with
  | nil =>
      simp [Execution.executeField] at hok
  | cons field rest =>
      cases fuel with
      | zero =>
          simp [Execution.executeField, Execution.outOfFuel] at hok
      | succ fuel =>
          cases hlookup : schema.lookupField field.parentType field.fieldName with
          | none =>
              simp [Execution.executeField, hlookup] at hok
          | some fieldDefinition =>
              cases hresolve
                    : Execution.coerceAndResolveFieldValue schema resolvers variableValues
                        fieldDefinition field.parentType field.fieldName
                        field.arguments source with
              | none =>
                  cases hhandled
                        : Execution.handleFieldError fieldDefinition.outputType with
                  | error handledErrors =>
                      simp [hlookup, hresolve,
                        Execution.singleFieldResult, hhandled] at hok
                  | ok handled =>
                      rcases handled with ⟨responseValue, handledErrors⟩
                      simp [hlookup, hresolve,
                        Execution.singleFieldResult, hhandled] at hok
                      exact ⟨responseValue, hok.1.symm⟩
              | some resolved =>
                  cases hcomplete
                        : Execution.completeValue schema resolvers variableValues
                            fuel fieldDefinition.outputType (field :: rest)
                            resolved with
                  | error completeErrors =>
                      simp [hlookup, hresolve,
                        Execution.singleFieldResult, hcomplete] at hok
                  | ok completed =>
                      rcases completed with ⟨responseValue, completeErrors⟩
                      simp [hlookup, hresolve,
                        Execution.singleFieldResult, hcomplete] at hok
                      exact ⟨responseValue, hok.1.symm⟩

theorem executeSelectionSetAsResponse_singleton_field_eq_executeField
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection)
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
        parentType source
        [Selection.field responseName fieldName arguments [] childSelectionSet]
      = Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]) := by
  cases hfield
        : Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }] with
  | error errors =>
      simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        Execution.collectFields, Execution.collectSelection,
        Execution.selectionDirectivesAllowBool,
        Execution.mergeExecutableGroups, Execution.executeCollectedFields,
        hfield, Execution.Result.combine]
  | ok result =>
      rcases result with ⟨fields, errors⟩
      simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        Execution.collectFields, Execution.collectSelection,
        Execution.selectionDirectivesAllowBool,
        Execution.mergeExecutableGroups, Execution.executeCollectedFields,
        hfield, Execution.Result.combine]

theorem executeSelectionSet_normal_object_field_head_eq_combine
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet rest : List Selection)
    : selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments [] childSelectionSet :: rest)
      -> selectionSetNormal schema parentType
          (Selection.field responseName fieldName arguments [] childSelectionSet :: rest)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source
            (Selection.field responseName fieldName arguments [] childSelectionSet
              :: rest)
          = Execution.Result.combine List.append
              (Execution.executeField schema resolvers variableValues fuel source
                responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }])
              (Execution.executeSelectionSet schema resolvers variableValues fuel
                parentType source rest) := by
  intro hfree hnormal hobject
  have hcollect :
      Execution.collectFields schema variableValues parentType source
        (Selection.field responseName fieldName arguments [] childSelectionSet
          :: rest)
      =
      (responseName, [{
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := childSelectionSet
      }])
        :: Execution.collectFields schema variableValues parentType source
          rest :=
    ExecutionKeys.collectFields_normal_object_field_head schema
      variableValues parentType source responseName fieldName arguments
      childSelectionSet rest hfree hnormal hobject
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hcollect, Execution.executeCollectedFields]

theorem result_combine_responseFields_append_assoc
    (left middle right : Execution.Result (List (Name × Execution.ResponseValue)))
    : Execution.Result.combine List.append left
        (Execution.Result.combine List.append middle right)
      = Execution.Result.combine List.append
          (Execution.Result.combine List.append left middle) right := by
  cases left with
  | error leftErrors =>
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [Execution.Result.combine, Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨middleFields, middleErrors⟩
          cases right with
          | error rightErrors =>
              simp [Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [Execution.Result.combine, Nat.add_assoc]
  | ok leftResult =>
      rcases leftResult with ⟨leftFields, leftErrors⟩
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [Execution.Result.combine, Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨middleFields, middleErrors⟩
          cases right with
          | error rightErrors =>
              simp [Execution.Result.combine, Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [Execution.Result.combine, List.append_assoc,
                Nat.add_assoc]

theorem result_combine_responseFields_append_nil_left
    (result : Execution.Result (List (Name × Execution.ResponseValue)))
    : Execution.Result.combine List.append (.ok ([], 0)) result = result := by
  cases result with
  | error errors =>
      simp [Execution.Result.combine]
  | ok result =>
      rcases result with ⟨fields, errors⟩
      simp [Execution.Result.combine]

theorem executeSelectionSet_normal_object_field_split_eq_context_combine
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (pref : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet suffix : List Selection)
    : selectionSetDirectiveFree
        (pref
          ++ Selection.field responseName fieldName arguments [] childSelectionSet
              :: suffix)
      -> selectionSetNormal schema parentType
          (pref
            ++ Selection.field responseName fieldName arguments [] childSelectionSet
                :: suffix)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source
            (pref
              ++ Selection.field responseName fieldName arguments [] childSelectionSet
                  :: suffix)
          = Execution.Result.combine List.append
              (Execution.executeSelectionSet schema resolvers variableValues fuel
                parentType source pref)
              (Execution.Result.combine List.append
                (Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }])
                (Execution.executeSelectionSet schema resolvers variableValues fuel
                  parentType source suffix)) := by
  induction pref with
  | nil =>
      intro hfree hnormal hobject
      have hhead :=
        executeSelectionSet_normal_object_field_head_eq_combine schema
          resolvers variableValues fuel parentType source responseName
          fieldName arguments childSelectionSet suffix hfree hnormal hobject
      let targetAndSuffix :=
        Execution.Result.combine List.append
          (Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }])
          (Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source suffix)
      calc
        Execution.executeSelectionSet schema resolvers variableValues fuel
              parentType source
              (Selection.field responseName fieldName arguments [] childSelectionSet
                :: suffix)
            = targetAndSuffix := by
          simpa [targetAndSuffix] using hhead
        _ = Execution.Result.combine List.append
              (Execution.executeSelectionSet schema resolvers variableValues fuel
                parentType source [])
              targetAndSuffix := by
          have hnil :=
            result_combine_responseFields_append_nil_left targetAndSuffix
          simpa [targetAndSuffix, Execution.executeSelectionSet,
            Execution.executeRootSelectionSet, Execution.collectFields,
            Execution.executeCollectedFields] using hnil.symm
  | cons selection rest ih =>
      intro hfree hnormal hobject
      have hallFields :
          selectionsAllFields
            (selection :: rest ++
              Selection.field responseName fieldName arguments []
                childSelectionSet :: suffix) :=
        selectionSetNormal_allFields_of_object hnormal hobject
      have hselectionField : Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | field headResponseName headFieldName headArguments headDirectives
          headChildSelectionSet =>
          have hheadDirectives : headDirectives = [] :=
            (selectionSetDirectiveFree_head hfree).1
          subst headDirectives
          have htailFree :
              selectionSetDirectiveFree
                (rest ++ Selection.field responseName fieldName arguments []
                  childSelectionSet :: suffix) :=
            selectionSetDirectiveFree_tail hfree
          have htailNormal :
              selectionSetNormal schema parentType
                (rest ++ Selection.field responseName fieldName arguments []
                  childSelectionSet :: suffix) :=
            selectionSetNormal_tail hnormal
          have hfullHead :=
            executeSelectionSet_normal_object_field_head_eq_combine schema
              resolvers variableValues fuel parentType source
              headResponseName headFieldName headArguments
              headChildSelectionSet
              (rest ++ Selection.field responseName fieldName arguments []
                childSelectionSet :: suffix)
              hfree hnormal hobject
          have hprefixFree :
              selectionSetDirectiveFree
                (Selection.field headResponseName headFieldName
                  headArguments [] headChildSelectionSet :: rest) := by
            exact
              selectionSetDirectiveFree_append_left
                (left := Selection.field headResponseName headFieldName
                  headArguments [] headChildSelectionSet :: rest)
                (right := Selection.field responseName fieldName arguments []
                  childSelectionSet :: suffix)
                (by simpa using hfree)
          have hprefixNormal :
              selectionSetNormal schema parentType
                (Selection.field headResponseName headFieldName
                  headArguments [] headChildSelectionSet :: rest) := by
            exact
              selectionSetNormal_append_left
                (left := Selection.field headResponseName headFieldName
                  headArguments [] headChildSelectionSet :: rest)
                (right := Selection.field responseName fieldName arguments []
                  childSelectionSet :: suffix)
                (by simpa using hnormal)
          have hprefHead :=
            executeSelectionSet_normal_object_field_head_eq_combine schema
              resolvers variableValues fuel parentType source
              headResponseName headFieldName headArguments
              headChildSelectionSet rest hprefixFree hprefixNormal hobject
          have htailSplit :=
            ih htailFree htailNormal hobject
          calc
            Execution.executeSelectionSet schema resolvers variableValues fuel
                  parentType source
                  (Selection.field headResponseName headFieldName
                        headArguments [] headChildSelectionSet
                      :: rest
                    ++ Selection.field responseName fieldName arguments []
                          childSelectionSet
                        :: suffix)
                = Execution.Result.combine List.append
                    (Execution.executeField schema resolvers variableValues fuel
                      source headResponseName
                      [{
                        parentType := parentType,
                        responseName := headResponseName,
                        fieldName := headFieldName,
                        arguments := headArguments,
                        selectionSet := headChildSelectionSet
                      }])
                    (Execution.executeSelectionSet schema resolvers variableValues
                      fuel parentType source
                      (rest
                        ++ Selection.field responseName fieldName arguments []
                              childSelectionSet
                            :: suffix)) :=
              hfullHead
            _ = Execution.Result.combine List.append
                  (Execution.executeField schema resolvers variableValues fuel
                    source headResponseName
                    [{
                      parentType := parentType,
                      responseName := headResponseName,
                      fieldName := headFieldName,
                      arguments := headArguments,
                      selectionSet := headChildSelectionSet
                    }])
                  (Execution.Result.combine List.append
                    (Execution.executeSelectionSet schema resolvers
                      variableValues fuel parentType source rest)
                    (Execution.Result.combine List.append
                      (Execution.executeField schema resolvers variableValues
                        fuel source responseName
                        [{
                          parentType := parentType,
                          responseName := responseName,
                          fieldName := fieldName,
                          arguments := arguments,
                          selectionSet := childSelectionSet
                        }])
                      (Execution.executeSelectionSet schema resolvers
                        variableValues fuel parentType source suffix))) := by
              rw [htailSplit]
            _ = Execution.Result.combine List.append
                  (Execution.Result.combine List.append
                    (Execution.executeField schema resolvers variableValues fuel
                      source headResponseName
                      [{
                        parentType := parentType,
                        responseName := headResponseName,
                        fieldName := headFieldName,
                        arguments := headArguments,
                        selectionSet := headChildSelectionSet
                      }])
                    (Execution.executeSelectionSet schema resolvers
                      variableValues fuel parentType source rest))
                  (Execution.Result.combine List.append
                    (Execution.executeField schema resolvers variableValues fuel
                      source responseName
                      [{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        selectionSet := childSelectionSet
                      }])
                    (Execution.executeSelectionSet schema resolvers variableValues
                      fuel parentType source suffix)) := by
              rw [result_combine_responseFields_append_assoc]
            _ = Execution.Result.combine List.append
                  (Execution.executeSelectionSet schema resolvers variableValues
                    fuel parentType source
                    (Selection.field headResponseName headFieldName
                        headArguments [] headChildSelectionSet
                      :: rest))
                  (Execution.Result.combine List.append
                    (Execution.executeField schema resolvers variableValues fuel
                      source responseName
                      [{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        selectionSet := childSelectionSet
                      }])
                    (Execution.executeSelectionSet schema resolvers variableValues
                      fuel parentType source suffix)) := by
              rw [← hprefHead]
      | inlineFragment typeCondition directives inlineChildSelectionSet =>
          simp [Selection.isField] at hselectionField

theorem executeSelectionSet_ok_head_cons_tail_responseFields_nodup_of_normal_object
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (childSelectionSet rest : List Selection)
    (headValue : Execution.ResponseValue)
    (tailFields : List (Name × Execution.ResponseValue))
    (tailErrors : Nat)
    : selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments directives childSelectionSet
          :: rest)
      -> selectionSetNormal schema parentType
          (Selection.field responseName fieldName arguments directives childSelectionSet
            :: rest)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source rest
          = .ok (tailFields, tailErrors)
      -> (((responseName, headValue) :: tailFields).map Prod.fst).Nodup := by
  intro hfree hnormal hobject htail
  have htailKeys :
      tailFields.map Prod.fst =
        (Execution.collectFields schema variableValues parentType source
          rest).map Prod.fst := by
    have htailCollected :
        Execution.executeCollectedFields schema resolvers variableValues fuel
          source
          (Execution.collectFields schema variableValues parentType source
            rest)
        =
        .ok (tailFields, tailErrors) := by
      simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
        using htail
    exact
      ExecutionResponseKeys.executeCollectedFields_ok_keys schema resolvers
        variableValues fuel source
        (Execution.collectFields schema variableValues parentType source rest)
        tailFields tailErrors htailCollected
  have hrestKeys :
      (Execution.collectFields schema variableValues parentType source
        rest).map Prod.fst
      =
      rest.filterMap Selection.responseName? :=
    ExecutionKeys.collectFields_normal_object_keys_eq_responseNames schema
      variableValues parentType source rest
      (selectionSetDirectiveFree_tail hfree)
      (selectionSetNormal_tail hnormal) hobject
  have htailNodup : (tailFields.map Prod.fst).Nodup := by
    rw [htailKeys, hrestKeys]
    exact selectionSetNormal_responseNamesNodup
      (selectionSetNormal_tail hnormal)
  have hnotTail : responseName ∉ tailFields.map Prod.fst := by
    intro hmem
    have hnames :
        (responseName :: rest.filterMap Selection.responseName?).Nodup := by
      simpa [responseNamesNodup, Selection.responseName?] using
        selectionSetNormal_responseNamesNodup hnormal
    have hnotRest : responseName ∉ rest.filterMap Selection.responseName? :=
      (List.nodup_cons.mp hnames).1
    exact hnotRest (by simpa [htailKeys, hrestKeys] using hmem)
  exact List.nodup_cons.mpr ⟨hnotTail, htailNodup⟩

theorem executeSelectionSet_ok_field_split_responseFields_nodup_of_normal_object
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (pref : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet suffix : List Selection)
    (prefixFields suffixFields : List (Name × Execution.ResponseValue))
    (prefixErrors suffixErrors : Nat)
    (headValue : Execution.ResponseValue) (headErrors : Nat)
    : selectionSetDirectiveFree
        (pref
          ++ Selection.field responseName fieldName arguments [] childSelectionSet
              :: suffix)
      -> selectionSetNormal schema parentType
          (pref
            ++ Selection.field responseName fieldName arguments [] childSelectionSet
                :: suffix)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source pref
          = .ok (prefixFields, prefixErrors)
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, headValue)], headErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source suffix
          = .ok (suffixFields, suffixErrors)
      -> ((prefixFields ++ [(responseName, headValue)] ++ suffixFields).map
            Prod.fst).Nodup := by
  intro hfree hnormal hobject hprefix hhead hsuffix
  let fullSelectionSet :=
    pref ++ Selection.field responseName fieldName arguments []
      childSelectionSet :: suffix
  have hsplit :=
    executeSelectionSet_normal_object_field_split_eq_context_combine schema
      resolvers variableValues fuel parentType source pref responseName
      fieldName arguments childSelectionSet suffix hfree hnormal hobject
  have hfullExecute :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        parentType source fullSelectionSet =
        .ok (prefixFields ++ [(responseName, headValue)] ++ suffixFields,
          prefixErrors + (headErrors + suffixErrors)) := by
    rw [hsplit, hprefix, hhead, hsuffix]
    simp [Execution.Result.combine, List.append_assoc]
  have hcollected :
      Execution.executeCollectedFields schema resolvers variableValues fuel
        source
        (Execution.collectFields schema variableValues parentType source
          fullSelectionSet)
      =
      .ok (prefixFields ++ [(responseName, headValue)] ++ suffixFields,
        prefixErrors + (headErrors + suffixErrors)) := by
    simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
      using hfullExecute
  have hkeys :
      (prefixFields ++ [(responseName, headValue)] ++
          suffixFields).map Prod.fst
        =
        (Execution.collectFields schema variableValues parentType source
          fullSelectionSet).map Prod.fst :=
    ExecutionResponseKeys.executeCollectedFields_ok_keys schema resolvers
      variableValues fuel source
      (Execution.collectFields schema variableValues parentType source
        fullSelectionSet)
      (prefixFields ++ [(responseName, headValue)] ++ suffixFields)
      (prefixErrors + (headErrors + suffixErrors)) hcollected
  rw [hkeys]
  exact
    ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source fullSelectionSet hfree hnormal hobject

theorem responseValue_semanticEquivalent_singleton_object_field_of_canonical_eq
    {responseName : Name} {left right : Execution.ResponseValue}
    : Execution.ResponseValue.canonical left = Execution.ResponseValue.canonical right
      -> Execution.ResponseValue.semanticEquivalent
          (.object [(responseName, left)])
          (.object [(responseName, right)]) := by
  intro hcanonical
  simp [Execution.ResponseValue.semanticEquivalent,
    Execution.ResponseValue.canonical,
    Execution.ResponseValue.canonicalObjectFields,
    Execution.ResponseValue.sortObjectFieldsByName,
    Execution.ResponseValue.insertObjectFieldSorted, hcanonical]

theorem responseValue_semanticEquivalent_of_singleFieldResult_data
    (responseName : Name)
    (left right : Execution.Result Execution.ResponseValue)
    : Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.singleFieldResult responseName left)).data
        (Execution.selectionSetResultToResponse
          (Execution.singleFieldResult responseName right)).data
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.Result.getD .null left)
          (Execution.Result.getD .null right) := by
  intro hsemantic
  cases hleft : left with
  | error leftErrors =>
      cases hright : right with
      | error rightErrors =>
          simp [Execution.ResponseValue.semanticEquivalent,
            Execution.Result.getD]
      | ok rightResult =>
          rcases rightResult with ⟨rightValue, rightErrors⟩
          simp [Execution.selectionSetResultToResponse, Execution.singleFieldResult,
            hleft, hright] at hsemantic
          exact False.elim
            (SemanticSeparation.responseValue_null_not_semanticEquivalent_object_cons
              hsemantic)
  | ok leftResult =>
      rcases leftResult with ⟨leftValue, leftErrors⟩
      cases hright : right with
      | error rightErrors =>
          simp [Execution.selectionSetResultToResponse, Execution.singleFieldResult,
            hleft, hright] at hsemantic
          exact False.elim
            (SemanticSeparation.responseValue_object_cons_not_semanticEquivalent_null
              hsemantic)
      | ok rightResult =>
          rcases rightResult with ⟨rightValue, rightErrors⟩
          have hobject :
              Execution.ResponseValue.semanticEquivalent
                (.object [(responseName, leftValue)])
                (.object [(responseName, rightValue)]) := by
            simpa [Execution.selectionSetResultToResponse, Execution.singleFieldResult,
              hleft, hright] using hsemantic
          simpa [Execution.Result.getD, hleft, hright] using
            SemanticSeparation.responseValue_semanticEquivalent_singleton_object_field
              hobject

theorem not_wrapTypeRefSelectionSetResponse_data_semanticEquivalent_of_child
    (responseName : Name) (outputType : TypeRef) {left right : Execution.Response}
    : ¬ Execution.ResponseValue.semanticEquivalent left.data right.data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (wrapTypeRefSelectionSetResponse responseName outputType left).data
            (wrapTypeRefSelectionSetResponse responseName outputType right).data := by
  intro hchild hwrapped
  apply hchild
  exact
    wrapTypeRefSelectionSetDataValue_semanticEquivalent_injective outputType
      (responseValue_semanticEquivalent_of_singleFieldResult_data responseName
        (wrapTypeRefSelectionSetResult outputType left)
        (wrapTypeRefSelectionSetResult outputType right)
        (by
          simpa [wrapTypeRefSelectionSetResponse,
            wrapTypeRefSelectionSetDataValue] using hwrapped))

theorem dataEquivalent_singleton_response_of_combine_ok_tail
    (responseName : Name)
    (leftHead rightHead : Execution.Result (List (Name × Execution.ResponseValue)))
    (leftTailFields rightTailFields : List (Name × Execution.ResponseValue))
    (leftTailErrors rightTailErrors : Nat)
    : (∀ fields errors,
        leftHead = .ok (fields, errors) -> ∃ value, fields = [(responseName, value)])
      -> (∀ fields errors,
            rightHead = .ok (fields, errors) -> ∃ value, fields = [(responseName, value)])
      -> (∀ value errors,
            leftHead = .ok ([(responseName, value)], errors)
            -> (((responseName, value) :: leftTailFields).map Prod.fst).Nodup)
      -> (∀ value errors,
            rightHead = .ok ([(responseName, value)], errors)
            -> (((responseName, value) :: rightTailFields).map Prod.fst).Nodup)
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.selectionSetResultToResponse
            (Execution.Result.combine List.append leftHead
              (.ok (leftTailFields, leftTailErrors)))).data
          (Execution.selectionSetResultToResponse
            (Execution.Result.combine List.append rightHead
              (.ok (rightTailFields, rightTailErrors)))).data
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.selectionSetResultToResponse leftHead).data
          (Execution.selectionSetResultToResponse rightHead).data := by
  intro hleftSingleton hrightSingleton hleftNodup hrightNodup hdata
  cases hleftHead : leftHead with
  | error leftErrors =>
      cases hrightHead : rightHead with
      | error rightErrors =>
          simp [Execution.ResponseValue.semanticEquivalent,
            Execution.selectionSetResultToResponse]
      | ok rightResult =>
          rcases rightResult with ⟨rightFields, rightErrors⟩
          rcases hrightSingleton rightFields rightErrors hrightHead with
            ⟨rightValue, hrightFields⟩
          subst rightFields
          simp [Execution.selectionSetResultToResponse, Execution.Result.combine,
            hleftHead, hrightHead] at hdata
          exact False.elim
            (SemanticSeparation.responseValue_null_not_semanticEquivalent_object_cons
              hdata)
  | ok leftResult =>
      rcases leftResult with ⟨leftFields, leftErrors⟩
      rcases hleftSingleton leftFields leftErrors hleftHead with
        ⟨leftValue, hleftFields⟩
      subst leftFields
      cases hrightHead : rightHead with
      | error rightErrors =>
          simp [Execution.selectionSetResultToResponse, Execution.Result.combine,
            hleftHead, hrightHead] at hdata
          exact False.elim
            (SemanticSeparation.responseValue_object_cons_not_semanticEquivalent_null
              hdata)
      | ok rightResult =>
          rcases rightResult with ⟨rightFields, rightErrors⟩
          rcases hrightSingleton rightFields rightErrors hrightHead with
            ⟨rightValue, hrightFields⟩
          subst rightFields
          have hdataObject :
              Execution.ResponseValue.semanticEquivalent
                (.object ((responseName, leftValue) :: leftTailFields))
                (.object ((responseName, rightValue) :: rightTailFields)) := by
            simpa [Execution.selectionSetResultToResponse, Execution.Result.combine,
              hleftHead, hrightHead] using hdata
          have hvalueCanonical :
              Execution.ResponseValue.canonical leftValue =
                Execution.ResponseValue.canonical rightValue :=
            ResponseKeys.ResponseValue.semanticEquivalent_object_field_canonical_eq
              hdataObject
              (hleftNodup leftValue leftErrors hleftHead)
              (hrightNodup rightValue rightErrors hrightHead)
              List.mem_cons_self
              List.mem_cons_self
          simp [Execution.selectionSetResultToResponse]
          exact
            responseValue_semanticEquivalent_singleton_object_field_of_canonical_eq
              hvalueCanonical

theorem responseValue_null_not_semanticEquivalent_object_append_singleton
    {pref suffix : List (Name × Execution.ResponseValue)}
    {responseName : Name} {value : Execution.ResponseValue}
    : ¬ Execution.ResponseValue.semanticEquivalent .null
          (.object (pref ++ [(responseName, value)] ++ suffix)) := by
  intro hsemantic
  cases pref with
  | nil =>
      exact
        SemanticSeparation.responseValue_null_not_semanticEquivalent_object_cons
          (by simpa using hsemantic)
  | cons field rest =>
      exact
        SemanticSeparation.responseValue_null_not_semanticEquivalent_object_cons
          (by simpa [List.cons_append, List.append_assoc] using hsemantic)

theorem responseValue_object_append_singleton_not_semanticEquivalent_null
    {pref suffix : List (Name × Execution.ResponseValue)}
    {responseName : Name} {value : Execution.ResponseValue}
    : ¬ Execution.ResponseValue.semanticEquivalent
          (.object (pref ++ [(responseName, value)] ++ suffix)) .null := by
  intro hsemantic
  cases pref with
  | nil =>
      exact
        SemanticSeparation.responseValue_object_cons_not_semanticEquivalent_null
          (by simpa using hsemantic)
  | cons field rest =>
      exact
        SemanticSeparation.responseValue_object_cons_not_semanticEquivalent_null
          (by simpa [List.cons_append, List.append_assoc] using hsemantic)

theorem dataEquivalent_singleton_response_of_context_ok
    (responseName : Name)
    (leftHead rightHead : Execution.Result (List (Name × Execution.ResponseValue)))
    (leftPrefixFields rightPrefixFields leftSuffixFields rightSuffixFields
      : List (Name × Execution.ResponseValue))
    (leftPrefixErrors rightPrefixErrors leftSuffixErrors rightSuffixErrors : Nat)
    : (∀ fields errors,
        leftHead = .ok (fields, errors) -> ∃ value, fields = [(responseName, value)])
      -> (∀ fields errors,
            rightHead = .ok (fields, errors) -> ∃ value, fields = [(responseName, value)])
      -> (∀ value errors,
            leftHead = .ok ([(responseName, value)], errors)
            -> ((leftPrefixFields ++ [(responseName, value)] ++ leftSuffixFields).map
                  Prod.fst).Nodup)
      -> (∀ value errors,
            rightHead = .ok ([(responseName, value)], errors)
            -> ((rightPrefixFields ++ [(responseName, value)] ++ rightSuffixFields).map
                  Prod.fst).Nodup)
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.selectionSetResultToResponse
            (Execution.Result.combine List.append
              (.ok (leftPrefixFields, leftPrefixErrors))
              (Execution.Result.combine List.append leftHead
                (.ok (leftSuffixFields, leftSuffixErrors))))).data
          (Execution.selectionSetResultToResponse
            (Execution.Result.combine List.append
              (.ok (rightPrefixFields, rightPrefixErrors))
              (Execution.Result.combine List.append rightHead
                (.ok (rightSuffixFields, rightSuffixErrors))))).data
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.selectionSetResultToResponse leftHead).data
          (Execution.selectionSetResultToResponse rightHead).data := by
  intro hleftSingleton hrightSingleton hleftNodup hrightNodup hdata
  cases hleftHead : leftHead with
  | error leftErrors =>
      cases hrightHead : rightHead with
      | error rightErrors =>
          simp [Execution.ResponseValue.semanticEquivalent,
            Execution.selectionSetResultToResponse]
      | ok rightResult =>
          rcases rightResult with ⟨rightFields, rightErrors⟩
          rcases hrightSingleton rightFields rightErrors hrightHead with
            ⟨rightValue, hrightFields⟩
          subst rightFields
          have hnullObject :
              Execution.ResponseValue.semanticEquivalent .null
                (.object (rightPrefixFields ++
                  [(responseName, rightValue)] ++ rightSuffixFields)) := by
            simpa [Execution.selectionSetResultToResponse, Execution.Result.combine,
              hleftHead, hrightHead, List.append_assoc] using hdata
          exact False.elim
            (responseValue_null_not_semanticEquivalent_object_append_singleton
              hnullObject)
  | ok leftResult =>
      rcases leftResult with ⟨leftFields, leftErrors⟩
      rcases hleftSingleton leftFields leftErrors hleftHead with
        ⟨leftValue, hleftFields⟩
      subst leftFields
      cases hrightHead : rightHead with
      | error rightErrors =>
          have hobjectNull :
              Execution.ResponseValue.semanticEquivalent
                (.object (leftPrefixFields ++
                  [(responseName, leftValue)] ++ leftSuffixFields))
                .null := by
            simpa [Execution.selectionSetResultToResponse, Execution.Result.combine,
              hleftHead, hrightHead, List.append_assoc] using hdata
          exact False.elim
            (responseValue_object_append_singleton_not_semanticEquivalent_null
              hobjectNull)
      | ok rightResult =>
          rcases rightResult with ⟨rightFields, rightErrors⟩
          rcases hrightSingleton rightFields rightErrors hrightHead with
            ⟨rightValue, hrightFields⟩
          subst rightFields
          have hdataObject :
              Execution.ResponseValue.semanticEquivalent
                (.object (leftPrefixFields ++
                  [(responseName, leftValue)] ++ leftSuffixFields))
                (.object (rightPrefixFields ++
                  [(responseName, rightValue)] ++ rightSuffixFields)) := by
            simpa [Execution.selectionSetResultToResponse, Execution.Result.combine,
              hleftHead, hrightHead, List.append_assoc] using hdata
          have hvalueCanonical :
              Execution.ResponseValue.canonical leftValue =
                Execution.ResponseValue.canonical rightValue :=
            ResponseKeys.ResponseValue.semanticEquivalent_object_field_canonical_eq
              (name := responseName)
              hdataObject
              (hleftNodup leftValue leftErrors hleftHead)
              (hrightNodup rightValue rightErrors hrightHead)
              (by simp)
              (by simp)
          simp [Execution.selectionSetResultToResponse]
          exact
            responseValue_semanticEquivalent_singleton_object_field_of_canonical_eq
              hvalueCanonical

theorem
    target_split_singleton_response_dataEquivalent_of_selectionSetsDataEquivalent_context_ok
    {ObjectRef : Type} {schema : Schema} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection)
    (leftPrefixFields rightPrefixFields leftSuffixFields rightSuffixFields
      : List (Name × Execution.ResponseValue))
    (leftPrefixErrors rightPrefixErrors leftSuffixErrors rightSuffixErrors : Nat)
    : (∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName leftField leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName rightField rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName leftField leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName rightField rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source leftPref
          = .ok (leftPrefixFields, leftPrefixErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source rightPref
          = .ok (rightPrefixFields, rightPrefixErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source leftSuffix
          = .ok (leftSuffixFields, leftSuffixErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source rightSuffix
          = .ok (rightSuffixFields, rightSuffixErrors)
      -> selectionSetsDataEquivalent schema parentType
          (leftPref
            ++ Selection.field responseName leftField leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
          (rightPref
            ++ Selection.field responseName rightField rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.selectionSetResultToResponse
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := leftField,
                arguments := leftArguments,
                selectionSet := leftChildSelectionSet
              }])).data
          (Execution.selectionSetResultToResponse
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := rightField,
                arguments := rightArguments,
                selectionSet := rightChildSelectionSet
              }])).data := by
  intro hsource hleftFree hrightFree hleftNormal hrightNormal hobject
    hleftPrefix hrightPrefix hleftSuffix hrightSuffix hdata
  let leftHead :=
    Execution.executeField schema resolvers variableValues fuel source
      responseName
      [{
        parentType := parentType,
        responseName := responseName,
        fieldName := leftField,
        arguments := leftArguments,
        selectionSet := leftChildSelectionSet
      }]
  let rightHead :=
    Execution.executeField schema resolvers variableValues fuel source
      responseName
      [{
        parentType := parentType,
        responseName := responseName,
        fieldName := rightField,
        arguments := rightArguments,
        selectionSet := rightChildSelectionSet
      }]
  have hleftSplit :=
    executeSelectionSet_normal_object_field_split_eq_context_combine schema
      resolvers variableValues fuel parentType source leftPref responseName
      leftField leftArguments leftChildSelectionSet leftSuffix hleftFree
      hleftNormal hobject
  have hrightSplit :=
    executeSelectionSet_normal_object_field_split_eq_context_combine schema
      resolvers variableValues fuel parentType source rightPref responseName
      rightField rightArguments rightChildSelectionSet rightSuffix hrightFree
      hrightNormal hobject
  have hcontextData :
      Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.Result.combine List.append
            (.ok (leftPrefixFields, leftPrefixErrors))
            (Execution.Result.combine List.append leftHead
              (.ok (leftSuffixFields, leftSuffixErrors))))).data
        (Execution.selectionSetResultToResponse
          (Execution.Result.combine List.append
            (.ok (rightPrefixFields, rightPrefixErrors))
            (Execution.Result.combine List.append rightHead
              (.ok (rightSuffixFields, rightSuffixErrors))))).data := by
    have hparentData :=
      hdata resolvers variableValues fuel source hsource
    simpa [Execution.executeSelectionSetAsResponse, leftHead, rightHead, hleftSplit,
      hrightSplit, hleftPrefix, hrightPrefix, hleftSuffix, hrightSuffix]
      using hparentData
  exact
    dataEquivalent_singleton_response_of_context_ok responseName leftHead
      rightHead leftPrefixFields rightPrefixFields leftSuffixFields
      rightSuffixFields leftPrefixErrors rightPrefixErrors leftSuffixErrors
      rightSuffixErrors
      (by
        intro fields errors hok
        exact
          executeField_ok_responseFields_singleton schema resolvers
            variableValues fuel source responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := leftField,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
            fields errors (by simpa [leftHead] using hok))
      (by
        intro fields errors hok
        exact
          executeField_ok_responseFields_singleton schema resolvers
            variableValues fuel source responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := rightField,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
            fields errors (by simpa [rightHead] using hok))
      (by
        intro value errors hok
        exact
          executeSelectionSet_ok_field_split_responseFields_nodup_of_normal_object
            schema resolvers variableValues fuel parentType source leftPref
            responseName leftField leftArguments leftChildSelectionSet
            leftSuffix leftPrefixFields leftSuffixFields leftPrefixErrors
            leftSuffixErrors value errors hleftFree hleftNormal hobject
            hleftPrefix (by simpa [leftHead] using hok) hleftSuffix)
      (by
        intro value errors hok
        exact
          executeSelectionSet_ok_field_split_responseFields_nodup_of_normal_object
            schema resolvers variableValues fuel parentType source rightPref
            responseName rightField rightArguments rightChildSelectionSet
            rightSuffix rightPrefixFields rightSuffixFields rightPrefixErrors
            rightSuffixErrors value errors hrightFree hrightNormal hobject
            hrightPrefix (by simpa [rightHead] using hok) hrightSuffix)
      hcontextData

theorem target_split_singleton_response_dataEquivalent_of_responseData_context_ok
    {ObjectRef : Type} {schema : Schema}
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection)
    (leftPrefixFields rightPrefixFields leftSuffixFields rightSuffixFields
      : List (Name × Execution.ResponseValue))
    (leftPrefixErrors rightPrefixErrors leftSuffixErrors rightSuffixErrors : Nat)
    : (∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName leftField leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName rightField rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName leftField leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName rightField rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source leftPref
          = .ok (leftPrefixFields, leftPrefixErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source rightPref
          = .ok (rightPrefixFields, rightPrefixErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source leftSuffix
          = .ok (leftSuffixFields, leftSuffixErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source rightSuffix
          = .ok (rightSuffixFields, rightSuffixErrors)
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema resolvers variableValues
            fuel parentType source
            (leftPref
              ++ Selection.field responseName leftField leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)).data
          (Execution.executeSelectionSetAsResponse schema resolvers variableValues
            fuel parentType source
            (rightPref
              ++ Selection.field responseName rightField rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix)).data
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.selectionSetResultToResponse
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := leftField,
                arguments := leftArguments,
                selectionSet := leftChildSelectionSet
              }])).data
          (Execution.selectionSetResultToResponse
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := rightField,
                arguments := rightArguments,
                selectionSet := rightChildSelectionSet
              }])).data := by
  intro hsource hleftFree hrightFree hleftNormal hrightNormal hobject
    hleftPrefix hrightPrefix hleftSuffix hrightSuffix hdata
  let leftHead :=
    Execution.executeField schema resolvers variableValues fuel source
      responseName
      [{
        parentType := parentType,
        responseName := responseName,
        fieldName := leftField,
        arguments := leftArguments,
        selectionSet := leftChildSelectionSet
      }]
  let rightHead :=
    Execution.executeField schema resolvers variableValues fuel source
      responseName
      [{
        parentType := parentType,
        responseName := responseName,
        fieldName := rightField,
        arguments := rightArguments,
        selectionSet := rightChildSelectionSet
      }]
  have hleftSplit :=
    executeSelectionSet_normal_object_field_split_eq_context_combine schema
      resolvers variableValues fuel parentType source leftPref responseName
      leftField leftArguments leftChildSelectionSet leftSuffix hleftFree
      hleftNormal hobject
  have hrightSplit :=
    executeSelectionSet_normal_object_field_split_eq_context_combine schema
      resolvers variableValues fuel parentType source rightPref responseName
      rightField rightArguments rightChildSelectionSet rightSuffix hrightFree
      hrightNormal hobject
  have hcontextData :
      Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.Result.combine List.append
            (.ok (leftPrefixFields, leftPrefixErrors))
            (Execution.Result.combine List.append leftHead
              (.ok (leftSuffixFields, leftSuffixErrors))))).data
        (Execution.selectionSetResultToResponse
          (Execution.Result.combine List.append
            (.ok (rightPrefixFields, rightPrefixErrors))
            (Execution.Result.combine List.append rightHead
              (.ok (rightSuffixFields, rightSuffixErrors))))).data := by
    simpa [Execution.executeSelectionSetAsResponse, leftHead, rightHead, hleftSplit,
      hrightSplit, hleftPrefix, hrightPrefix, hleftSuffix, hrightSuffix]
      using hdata
  exact
    dataEquivalent_singleton_response_of_context_ok responseName leftHead
      rightHead leftPrefixFields rightPrefixFields leftSuffixFields
      rightSuffixFields leftPrefixErrors rightPrefixErrors leftSuffixErrors
      rightSuffixErrors
      (by
        intro fields errors hok
        exact
          executeField_ok_responseFields_singleton schema resolvers
            variableValues fuel source responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := leftField,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
            fields errors (by simpa [leftHead] using hok))
      (by
        intro fields errors hok
        exact
          executeField_ok_responseFields_singleton schema resolvers
            variableValues fuel source responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := rightField,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
            fields errors (by simpa [rightHead] using hok))
      (by
        intro value errors hok
        exact
          executeSelectionSet_ok_field_split_responseFields_nodup_of_normal_object
            schema resolvers variableValues fuel parentType source leftPref
            responseName leftField leftArguments leftChildSelectionSet
            leftSuffix leftPrefixFields leftSuffixFields leftPrefixErrors
            leftSuffixErrors value errors hleftFree hleftNormal hobject
            hleftPrefix (by simpa [leftHead] using hok) hleftSuffix)
      (by
        intro value errors hok
        exact
          executeSelectionSet_ok_field_split_responseFields_nodup_of_normal_object
            schema resolvers variableValues fuel parentType source rightPref
            responseName rightField rightArguments rightChildSelectionSet
            rightSuffix rightPrefixFields rightSuffixFields rightPrefixErrors
            rightSuffixErrors value errors hrightFree hrightNormal hobject
            hrightPrefix (by simpa [rightHead] using hok) hrightSuffix)
      hcontextData

theorem
    target_head_singleton_response_dataEquivalent_of_selectionSetsDataEquivalent_tail_ok
    {ObjectRef : Type} {schema : Schema} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet leftRest rightRest : List Selection)
    (leftTailFields rightTailFields : List (Name × Execution.ResponseValue))
    (leftTailErrors rightTailErrors : Nat)
    : (∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree
          (Selection.field responseName leftField leftArguments [] leftChildSelectionSet
            :: leftRest)
      -> selectionSetDirectiveFree
          (Selection.field responseName rightField rightArguments []
              rightChildSelectionSet
            :: rightRest)
      -> selectionSetNormal schema parentType
          (Selection.field responseName leftField leftArguments [] leftChildSelectionSet
            :: leftRest)
      -> selectionSetNormal schema parentType
          (Selection.field responseName rightField rightArguments []
              rightChildSelectionSet
            :: rightRest)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source leftRest
          = .ok (leftTailFields, leftTailErrors)
      -> Execution.executeSelectionSet schema resolvers variableValues fuel
            parentType source rightRest
          = .ok (rightTailFields, rightTailErrors)
      -> selectionSetsDataEquivalent schema parentType
          (Selection.field responseName leftField leftArguments [] leftChildSelectionSet
            :: leftRest)
          (Selection.field responseName rightField rightArguments []
              rightChildSelectionSet
            :: rightRest)
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.selectionSetResultToResponse
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := leftField,
                arguments := leftArguments,
                selectionSet := leftChildSelectionSet
              }])).data
          (Execution.selectionSetResultToResponse
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := rightField,
                arguments := rightArguments,
                selectionSet := rightChildSelectionSet
              }])).data := by
  intro hsource hleftFree hrightFree hleftNormal hrightNormal hobject
    hleftTail hrightTail hdata
  have hwhole :
      Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source
          (Selection.field responseName leftField leftArguments []
            leftChildSelectionSet :: leftRest)).data
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source
          (Selection.field responseName rightField rightArguments []
            rightChildSelectionSet :: rightRest)).data :=
    hdata resolvers variableValues fuel source hsource
  have hleftSplit :=
    executeSelectionSet_normal_object_field_head_eq_combine schema resolvers
      variableValues fuel parentType source responseName leftField
      leftArguments leftChildSelectionSet leftRest hleftFree hleftNormal
      hobject
  have hrightSplit :=
    executeSelectionSet_normal_object_field_head_eq_combine schema resolvers
      variableValues fuel parentType source responseName rightField
      rightArguments rightChildSelectionSet rightRest hrightFree hrightNormal
      hobject
  have hprojected :
      Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.Result.combine List.append
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := leftField,
                arguments := leftArguments,
                selectionSet := leftChildSelectionSet
              }])
            (.ok (leftTailFields, leftTailErrors)))).data
        (Execution.selectionSetResultToResponse
          (Execution.Result.combine List.append
            (Execution.executeField schema resolvers variableValues fuel source
              responseName
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := rightField,
                arguments := rightArguments,
                selectionSet := rightChildSelectionSet
              }])
            (.ok (rightTailFields, rightTailErrors)))).data := by
    simpa [Execution.executeSelectionSetAsResponse, hleftSplit, hrightSplit,
      hleftTail, hrightTail] using hwhole
  exact
    dataEquivalent_singleton_response_of_combine_ok_tail responseName
      (Execution.executeField schema resolvers variableValues fuel source
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := leftField,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }])
      (Execution.executeField schema resolvers variableValues fuel source
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := rightField,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }])
      leftTailFields rightTailFields leftTailErrors rightTailErrors
      (by
        intro fields errors hhead
        exact
          executeField_ok_responseFields_singleton schema resolvers
            variableValues fuel source responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := leftField,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }] fields errors hhead)
      (by
        intro fields errors hhead
        exact
          executeField_ok_responseFields_singleton schema resolvers
            variableValues fuel source responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := rightField,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }] fields errors hhead)
      (by
        intro value errors _hhead
        exact
          executeSelectionSet_ok_head_cons_tail_responseFields_nodup_of_normal_object
            schema resolvers variableValues fuel parentType source
            responseName leftField leftArguments [] leftChildSelectionSet
            leftRest value leftTailFields leftTailErrors hleftFree
            hleftNormal hobject hleftTail)
      (by
        intro value errors _hhead
        exact
          executeSelectionSet_ok_head_cons_tail_responseFields_nodup_of_normal_object
            schema resolvers variableValues fuel parentType source
            responseName rightField rightArguments [] rightChildSelectionSet
            rightRest value rightTailFields rightTailErrors hrightFree
            hrightNormal hobject hrightTail)
      hprojected

theorem executeSelectionSetAsResponse_normal_object_field_split_error_data_null
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (pref : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet suffix : List Selection) {errors : Nat}
    : selectionSetDirectiveFree
        (pref
          ++ Selection.field responseName fieldName arguments [] childSelectionSet
              :: suffix)
      -> selectionSetNormal schema parentType
          (pref
            ++ Selection.field responseName fieldName arguments [] childSelectionSet
                :: suffix)
      -> objectTypeNameBool schema parentType = true
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .error errors
      -> (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source
            (pref
              ++ Selection.field responseName fieldName arguments [] childSelectionSet
                  :: suffix)).data
          = Execution.ResponseValue.null := by
  intro hfree hnormal hobject htarget
  have hsplit :=
    executeSelectionSet_normal_object_field_split_eq_context_combine schema
      resolvers variableValues fuel parentType source pref responseName
      fieldName arguments childSelectionSet suffix hfree hnormal hobject
  rw [Execution.executeSelectionSetAsResponse, hsplit]
  cases hpref :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        parentType source pref <;>
    cases hsuffix :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        parentType source suffix <;>
    simp [Execution.selectionSetResultToResponse, htarget, Execution.Result.combine]

theorem executeSelectionSetAsResponse_normal_object_field_mem_error_data_null
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (childSelectionSet : List Selection) {errors : Nat}
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .error errors
      -> (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source selectionSet).data
          = Execution.ResponseValue.null := by
  intro hfree hnormal hobject hmem htarget
  have hdirectives :
      directives = [] :=
    selectionSetDirectiveFree_field_directives_nil_of_mem hfree hmem
  subst directives
  rcases List.mem_iff_append.mp hmem with ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  exact
    executeSelectionSetAsResponse_normal_object_field_split_error_data_null
      schema resolvers variableValues fuel parentType source pref
      responseName fieldName arguments childSelectionSet suffix hfree
      hnormal hobject htarget

end GroundTypeNormalization

end NormalForm

end GraphQL
