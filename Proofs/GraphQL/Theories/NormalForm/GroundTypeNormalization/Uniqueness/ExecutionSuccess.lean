import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionKeys
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionResponseKeys

/-!
Successful execution shape lemmas for uniqueness probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

namespace ExecutionSuccess

variable {ObjectRef : Type}

theorem executeSelectionSet_ok_of_field_ok
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    : ∀ selectionSet,
        selectionSetDirectiveFree selectionSet
        -> selectionSetNormal schema parentType selectionSet
        -> objectTypeNameBool schema parentType = true
        -> (∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ selectionSet
              -> ∃ responseValue fieldErrors,
                  Execution.executeField schema resolvers variableValues fuel source
                    responseName
                    [{
                      parentType := parentType,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet := childSelectionSet
                    }]
                  = .ok ([(responseName, responseValue)], fieldErrors))
        -> ∃ responseFields errors,
            Execution.executeSelectionSet schema resolvers variableValues fuel
              parentType source selectionSet
            = .ok (responseFields, errors)
  | [], _hfree, _hnormal, _hobject, _hfieldOk => by
      exact ⟨[], 0, by
        simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
          Execution.collectFields, Execution.executeCollectedFields]⟩
  | selection :: rest, hfree, hnormal, hobject, hfieldOk => by
      have hallFields :
          selectionsAllFields (selection :: rest) :=
        selectionSetNormal_allFields_of_object hnormal hobject
      have hselectionField :
          Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hdirectives : directives = [] :=
            (selectionSetDirectiveFree_head hfree).1
          subst directives
          rcases hfieldOk responseName fieldName arguments []
              childSelectionSet (by simp) with
            ⟨headValue, headErrors, hheadExecute⟩
          rcases
              executeSelectionSet_ok_of_field_ok schema resolvers
                variableValues fuel parentType source rest
                (selectionSetDirectiveFree_tail hfree)
                (selectionSetNormal_tail hnormal)
                hobject
                (by
                  intro tailResponseName tailFieldName tailArguments
                    tailDirectives tailChildSelectionSet htailMem
                  exact hfieldOk tailResponseName tailFieldName tailArguments
                    tailDirectives tailChildSelectionSet
                    (List.mem_cons_of_mem
                      (Selection.field responseName fieldName arguments []
                        childSelectionSet) htailMem)) with
            ⟨tailFields, tailErrors, htailExecute⟩
          have htailCollected :
              Execution.executeCollectedFields schema resolvers variableValues
                fuel source
                (Execution.collectFields schema variableValues parentType
                  source rest)
              =
              .ok (tailFields, tailErrors) := by
            simpa [Execution.executeSelectionSet,
              Execution.executeRootSelectionSet] using htailExecute
          have hcollect :
              Execution.collectFields schema variableValues parentType source
                (Selection.field responseName fieldName arguments []
                  childSelectionSet :: rest)
              =
              (responseName, [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }])
                :: Execution.collectFields schema variableValues parentType
                  source rest :=
            ExecutionKeys.collectFields_normal_object_field_head schema
              variableValues parentType source responseName fieldName
              arguments childSelectionSet rest hfree hnormal hobject
          exact
            ⟨(responseName, headValue) :: tailFields,
              headErrors + tailErrors, by
                simp [Execution.executeSelectionSet,
                  Execution.executeRootSelectionSet, hcollect,
                  Execution.executeCollectedFields, hheadExecute,
                  htailCollected, Execution.Result.combine]⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField

theorem executeSelectionSetAsResponse_object_of_field_ok
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source selectionSet
          = ({ data := .object responseFields, errors := errors }
              : Execution.Response) := by
  intro hfree hnormal hobject hfieldOk
  rcases executeSelectionSet_ok_of_field_ok schema resolvers variableValues
      fuel parentType source selectionSet hfree hnormal hobject hfieldOk with
    ⟨responseFields, errors, hexecute⟩
  exact
    ⟨responseFields, errors,
      ExecutionResponseKeys.executeSelectionSetAsResponse_eq_object_of_executeSelectionSet_ok
        hexecute⟩

theorem executeSelectionSet_ok_field_mem_of_field_ok
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (targetResponseName targetFieldName : Name)
    (targetArguments : List Argument)
    (targetDirectives : List DirectiveApplication)
    (targetChildSelectionSet : List Selection)
    (targetValue : Execution.ResponseValue)
    (targetErrors : Nat)
    : ∀ selectionSet,
        selectionSetDirectiveFree selectionSet
        -> selectionSetNormal schema parentType selectionSet
        -> objectTypeNameBool schema parentType = true
        -> Selection.field targetResponseName targetFieldName targetArguments
              targetDirectives targetChildSelectionSet
            ∈ selectionSet
        -> Execution.executeField schema resolvers variableValues fuel source
              targetResponseName
              [{
                parentType := parentType,
                responseName := targetResponseName,
                fieldName := targetFieldName,
                arguments := targetArguments,
                selectionSet := targetChildSelectionSet
              }]
            = .ok ([(targetResponseName, targetValue)], targetErrors)
        -> (∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ selectionSet
              -> ∃ responseValue fieldErrors,
                  Execution.executeField schema resolvers variableValues fuel source
                    responseName
                    [{
                      parentType := parentType,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet := childSelectionSet
                    }]
                  = .ok ([(responseName, responseValue)], fieldErrors))
        -> ∃ responseFields errors,
            Execution.executeSelectionSet schema resolvers variableValues fuel
                parentType source selectionSet
              = .ok (responseFields, errors)
            ∧ (targetResponseName, targetValue) ∈ responseFields
  | [], _hfree, _hnormal, _hobject, htargetMem, _htargetExecute,
      _hfieldOk => by
      simp at htargetMem
  | selection :: rest, hfree, hnormal, hobject, htargetMem, htargetExecute,
      hfieldOk => by
      have hallFields :
          selectionsAllFields (selection :: rest) :=
        selectionSetNormal_allFields_of_object hnormal hobject
      have hselectionField :
          Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hdirectives : directives = [] :=
            (selectionSetDirectiveFree_head hfree).1
          subst directives
          rcases hfieldOk responseName fieldName arguments []
              childSelectionSet (by simp) with
            ⟨headValue, headErrors, hheadExecute⟩
          rcases
              executeSelectionSet_ok_of_field_ok schema resolvers
                variableValues fuel parentType source rest
                (selectionSetDirectiveFree_tail hfree)
                (selectionSetNormal_tail hnormal)
                hobject
                (by
                  intro tailResponseName tailFieldName tailArguments
                    tailDirectives tailChildSelectionSet htailMem
                  exact hfieldOk tailResponseName tailFieldName tailArguments
                    tailDirectives tailChildSelectionSet
                    (List.mem_cons_of_mem
                      (Selection.field responseName fieldName arguments []
                        childSelectionSet) htailMem)) with
            ⟨tailFields, tailErrors, htailExecute⟩
          have htailCollected :
              Execution.executeCollectedFields schema resolvers variableValues
                fuel source
                (Execution.collectFields schema variableValues parentType
                  source rest)
              =
              .ok (tailFields, tailErrors) := by
            simpa [Execution.executeSelectionSet,
              Execution.executeRootSelectionSet] using htailExecute
          have hcollect :
              Execution.collectFields schema variableValues parentType source
                (Selection.field responseName fieldName arguments []
                  childSelectionSet :: rest)
              =
              (responseName, [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }])
                :: Execution.collectFields schema variableValues parentType
                  source rest :=
            ExecutionKeys.collectFields_normal_object_field_head schema
              variableValues parentType source responseName fieldName
              arguments childSelectionSet rest hfree hnormal hobject
          rcases List.mem_cons.mp htargetMem with htargetHead | htargetTail
          · cases htargetHead
            exact
              ⟨(targetResponseName, targetValue) :: tailFields,
                targetErrors + tailErrors,
                by
                  constructor
                  · simp [Execution.executeSelectionSet,
                      Execution.executeRootSelectionSet, hcollect,
                      Execution.executeCollectedFields, htargetExecute,
                      htailCollected, Execution.Result.combine]
                  · simp⟩
          · rcases
              executeSelectionSet_ok_field_mem_of_field_ok schema resolvers
                variableValues fuel parentType source targetResponseName
                targetFieldName targetArguments targetDirectives
                targetChildSelectionSet targetValue targetErrors rest
                (selectionSetDirectiveFree_tail hfree)
                (selectionSetNormal_tail hnormal)
                hobject htargetTail htargetExecute
                (by
                  intro tailResponseName tailFieldName tailArguments
                    tailDirectives tailChildSelectionSet htailMem
                  exact hfieldOk tailResponseName tailFieldName tailArguments
                    tailDirectives tailChildSelectionSet
                    (List.mem_cons_of_mem
                      (Selection.field responseName fieldName arguments []
                        childSelectionSet) htailMem)) with
                ⟨tailFields', tailErrors', htailExecute', htargetInTail⟩
            have htailCollected' :
                Execution.executeCollectedFields schema resolvers variableValues
                  fuel source
                  (Execution.collectFields schema variableValues parentType
                    source rest)
                =
                .ok (tailFields', tailErrors') := by
              simpa [Execution.executeSelectionSet,
                Execution.executeRootSelectionSet] using htailExecute'
            exact
              ⟨(responseName, headValue) :: tailFields',
                headErrors + tailErrors',
                by
                  constructor
                  · simp [Execution.executeSelectionSet,
                      Execution.executeRootSelectionSet, hcollect,
                      Execution.executeCollectedFields, hheadExecute,
                      htailCollected', Execution.Result.combine]
                  · exact List.mem_cons_of_mem
                      (responseName, headValue) htargetInTail⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField

theorem executeSelectionSetAsResponse_object_field_mem_of_field_ok
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (targetResponseName targetFieldName : Name)
    (targetArguments : List Argument)
    (targetDirectives : List DirectiveApplication)
    (targetChildSelectionSet : List Selection)
    (targetValue : Execution.ResponseValue)
    (targetErrors : Nat)
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> Selection.field targetResponseName targetFieldName targetArguments
            targetDirectives targetChildSelectionSet
          ∈ selectionSet
      -> Execution.executeField schema resolvers variableValues fuel source
            targetResponseName
            [{
              parentType := parentType,
              responseName := targetResponseName,
              fieldName := targetFieldName,
              arguments := targetArguments,
              selectionSet := targetChildSelectionSet
            }]
          = .ok ([(targetResponseName, targetValue)], targetErrors)
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
              parentType source selectionSet
            = ({ data := .object responseFields, errors := errors } : Execution.Response)
          ∧ (targetResponseName, targetValue) ∈ responseFields := by
  intro hfree hnormal hobject htargetMem htargetExecute hfieldOk
  rcases
      executeSelectionSet_ok_field_mem_of_field_ok schema resolvers
        variableValues fuel parentType source targetResponseName
        targetFieldName targetArguments targetDirectives
        targetChildSelectionSet targetValue targetErrors selectionSet
        hfree hnormal hobject htargetMem htargetExecute hfieldOk with
    ⟨responseFields, errors, hexecute, htargetInFields⟩
  exact
    ⟨responseFields, errors,
      ExecutionResponseKeys.executeSelectionSetAsResponse_eq_object_of_executeSelectionSet_ok
        hexecute,
      htargetInFields⟩

end ExecutionSuccess

end GroundTypeNormalization

end NormalForm

end GraphQL
