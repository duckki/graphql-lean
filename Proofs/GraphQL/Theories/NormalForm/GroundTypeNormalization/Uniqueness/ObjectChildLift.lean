import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ObjectProbeLift
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Projection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ProbeTags
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SingletonProjection

/-!
Object-child lifting helpers for uniqueness probes.

These lemmas compose the root projection fallback resolver with the parent-object
probe resolver. At the selected parent field, execution is reduced to the child
selection-set response produced by an arbitrary base resolver environment.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def selectionSetFieldsExecuteOk {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Prop :=
  ∀ responseName fieldName arguments directives childSelectionSet,
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
        = .ok ([(responseName, responseValue)], fieldErrors)

theorem selectionSetFieldsExecuteOk_nil
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    : selectionSetFieldsExecuteOk schema resolvers variableValues fuel
        parentType source [] := by
  intro responseName fieldName arguments directives childSelectionSet hmem
  cases hmem

theorem executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_response
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent targetField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    : Argument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent targetField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent targetField
                runtimeType ref fieldDefinition.outputType)
              targetParent targetField targetField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := targetField,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema base variableValues fuel
                  runtimeType (.object runtimeType ref) childSelectionSet)) := by
  intro harguments hlookup hinclude
  let parentBase :=
    parentObjectProbeFieldResolvers base targetParent targetField runtimeType
      ref fieldDefinition.outputType
  have hroot :
      Execution.executeField schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet parentBase
          targetParent targetField targetField leftArguments rightArguments)
        variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        (projectionRootResolverValue
          (.object targetParent (none : Option ObjectRef)))
        responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := targetField,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      Execution.executeField schema parentBase variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        (.object targetParent (none : Option ObjectRef))
        responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := targetField,
          arguments := arguments,
          selectionSet := childSelectionSet
        }] :=
    executeField_fieldPairOrDeepSuccessResolvers_left_root schema
      rootSelectionSet parentBase variableValues targetParent targetField
      targetField responseName leftArguments rightArguments arguments
      (.object targetParent (none : Option ObjectRef)) childSelectionSet
      harguments (fuel + leafProbeFuel fieldDefinition.outputType + 1)
  rw [hroot]
  have hchildResponse :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema parentBase variableValues
          fuel (.object runtimeType (some ref))
          (Execution.collectFields schema variableValues runtimeType
            (.object runtimeType (some ref)) childSelectionSet))
      =
      Execution.executeSelectionSetAsResponse schema base variableValues fuel
        runtimeType (.object runtimeType ref) childSelectionSet := by
    have hparentLift :=
      executeSelectionSetAsResponse_parentObjectProbeFieldResolvers_liftResolverValue
        schema base variableValues fuel targetParent targetField runtimeType
        ref fieldDefinition.outputType runtimeType
        (.object runtimeType ref) childSelectionSet
    have hlift :=
      executeSelectionSetAsResponse_liftResolvers schema base variableValues
        fuel runtimeType (.object runtimeType ref) childSelectionSet
    have hparentToBase :
        Execution.executeSelectionSetAsResponse schema parentBase variableValues fuel
          runtimeType (liftResolverValue (.object runtimeType ref))
          childSelectionSet
        =
        Execution.executeSelectionSetAsResponse schema base variableValues fuel
          runtimeType (.object runtimeType ref) childSelectionSet := by
      rw [hparentLift, hlift]
    simpa [parentBase, Execution.executeSelectionSetAsResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      liftResolverValue] using hparentToBase
  have hparentField :=
    executeField_objectProbeWithRuntime_response schema parentBase
      variableValues fuel (.object targetParent (none : Option ObjectRef))
      responseName targetParent targetField arguments childSelectionSet
      fieldDefinition runtimeType (some ref) hlookup
      (parentObjectProbeFieldResolvers_target base targetParent targetField
        runtimeType ref fieldDefinition.outputType arguments)
      hinclude
  simpa [parentBase, hchildResponse] using hparentField

theorem executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_response
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent targetField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    : Argument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent targetField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent targetField
                runtimeType ref fieldDefinition.outputType)
              targetParent targetField targetField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := targetField,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema base variableValues fuel
                  runtimeType (.object runtimeType ref) childSelectionSet)) := by
  intro harguments hlookup hinclude
  let parentBase :=
    parentObjectProbeFieldResolvers base targetParent targetField runtimeType
      ref fieldDefinition.outputType
  have hroot :
      Execution.executeField schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet parentBase
          targetParent targetField targetField leftArguments rightArguments)
        variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        (projectionRootResolverValue
          (.object targetParent (none : Option ObjectRef)))
        responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := targetField,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      Execution.executeField schema parentBase variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        (.object targetParent (none : Option ObjectRef))
        responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := targetField,
          arguments := arguments,
          selectionSet := childSelectionSet
        }] :=
    executeField_fieldPairOrDeepSuccessResolvers_right_root schema
      rootSelectionSet parentBase variableValues targetParent targetField
      targetField responseName leftArguments rightArguments arguments
      (.object targetParent (none : Option ObjectRef)) childSelectionSet
      harguments (fuel + leafProbeFuel fieldDefinition.outputType + 1)
  rw [hroot]
  have hchildResponse :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema parentBase variableValues
          fuel (.object runtimeType (some ref))
          (Execution.collectFields schema variableValues runtimeType
            (.object runtimeType (some ref)) childSelectionSet))
      =
      Execution.executeSelectionSetAsResponse schema base variableValues fuel
        runtimeType (.object runtimeType ref) childSelectionSet := by
    have hparentLift :=
      executeSelectionSetAsResponse_parentObjectProbeFieldResolvers_liftResolverValue
        schema base variableValues fuel targetParent targetField runtimeType
        ref fieldDefinition.outputType runtimeType
        (.object runtimeType ref) childSelectionSet
    have hlift :=
      executeSelectionSetAsResponse_liftResolvers schema base variableValues
        fuel runtimeType (.object runtimeType ref) childSelectionSet
    have hparentToBase :
        Execution.executeSelectionSetAsResponse schema parentBase variableValues fuel
          runtimeType (liftResolverValue (.object runtimeType ref))
          childSelectionSet
        =
        Execution.executeSelectionSetAsResponse schema base variableValues fuel
          runtimeType (.object runtimeType ref) childSelectionSet := by
      rw [hparentLift, hlift]
    simpa [parentBase, Execution.executeSelectionSetAsResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      liftResolverValue] using hparentToBase
  have hparentField :=
    executeField_objectProbeWithRuntime_response schema parentBase
      variableValues fuel (.object targetParent (none : Option ObjectRef))
      responseName targetParent targetField arguments childSelectionSet
      fieldDefinition runtimeType (some ref) hlookup
      (parentObjectProbeFieldResolvers_target base targetParent targetField
        runtimeType ref fieldDefinition.outputType arguments)
      hinclude
  simpa [parentBase, hchildResponse] using hparentField

theorem executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_ok_of_child_object_response
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent targetField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : Argument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent targetField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent targetField
                runtimeType ref fieldDefinition.outputType)
              targetParent targetField targetField leftArguments
              rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := targetField,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro harguments hlookup hinclude hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  rw [
    executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_response
      schema rootSelectionSet base variableValues fuel targetParent
      targetField responseName leftArguments rightArguments arguments
      childSelectionSet fieldDefinition runtimeType ref harguments hlookup
      hinclude]
  simp [hchildResponse, hwrapped, Execution.singleFieldResult]

theorem executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_ok_of_child_object_response
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent targetField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : Argument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent targetField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent targetField
                runtimeType ref fieldDefinition.outputType)
              targetParent targetField targetField leftArguments
              rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := targetField,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro harguments hlookup hinclude hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  rw [
    executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_response
      schema rootSelectionSet base variableValues fuel targetParent
      targetField responseName leftArguments rightArguments arguments
      childSelectionSet fieldDefinition runtimeType ref harguments hlookup
      hinclude]
  simp [hchildResponse, hwrapped, Execution.singleFieldResult]

theorem selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_field_cases
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent targetField : Name)
    (leftArguments rightArguments : List Argument) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    : schema.lookupField targetParent targetField = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName targetField arguments directives
                childSelectionSet
              ∈ selectionSet
            -> Argument.argumentsEquivalent arguments leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema base variableValues fuel
                  runtimeType (.object runtimeType ref) childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName targetField arguments directives
                childSelectionSet
              ∈ selectionSet
            -> Argument.argumentsEquivalent arguments rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema base variableValues fuel
                  runtimeType (.object runtimeType ref) childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ¬ fieldPairProjectionTarget targetParent targetField targetField
                  leftArguments rightArguments targetParent fieldName arguments
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base targetParent targetField
                      runtimeType ref fieldDefinition.outputType)
                    targetParent targetField targetField leftArguments
                    rightArguments)
                  variableValues
                  (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                  (projectionRootResolverValue
                    (.object targetParent (none : Option ObjectRef)))
                  responseName
                  [{
                    parentType := targetParent,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (parentObjectProbeFieldResolvers base targetParent targetField
              runtimeType ref fieldDefinition.outputType)
            targetParent targetField targetField leftArguments rightArguments)
          variableValues
          (fuel + leafProbeFuel fieldDefinition.outputType + 1)
          targetParent
          (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
          selectionSet := by
  intro hlookup hinclude hleftChildResponse hrightChildResponse hother
  intro responseName fieldName arguments directives childSelectionSet hmem
  by_cases hleftTarget :
      fieldProbeTarget targetParent targetField leftArguments targetParent
        fieldName arguments
  · rcases hleftTarget with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    rcases
        hleftChildResponse responseName arguments directives
          childSelectionSet hmem harguments with
      ⟨childFields, childErrors, hchildResponse⟩
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_ok_of_child_object_response
        schema rootSelectionSet base variableValues fuel targetParent
        targetField responseName leftArguments rightArguments arguments
        childSelectionSet fieldDefinition runtimeType ref childFields
        childErrors harguments hlookup hinclude hchildResponse
  · by_cases hrightTarget :
        fieldProbeTarget targetParent targetField rightArguments targetParent
          fieldName arguments
    · rcases hrightTarget with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      rcases
          hrightChildResponse responseName arguments directives
            childSelectionSet hmem harguments with
        ⟨childFields, childErrors, hchildResponse⟩
      exact
        executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_ok_of_child_object_response
          schema rootSelectionSet base variableValues fuel targetParent
          targetField responseName leftArguments rightArguments arguments
          childSelectionSet fieldDefinition runtimeType ref childFields
          childErrors harguments hlookup hinclude hchildResponse
    · have hnotProjection :
          ¬ fieldPairProjectionTarget targetParent targetField targetField
            leftArguments rightArguments targetParent fieldName arguments := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact hleftTarget ⟨rfl, hleft.1, hleft.2⟩
        · exact hrightTarget ⟨rfl, hright.1, hright.2⟩
      exact
        hother responseName fieldName arguments directives childSelectionSet
          hmem hnotProjection

theorem executeField_fieldPairOrDeepSuccess_parentObjectProbe_other_root_ok_of_deepSuccessWithRef_ok
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (parentFuel : Nat) (targetParent targetField childRuntimeType : Name)
    (ref : ObjectRef) (outputType : TypeRef)
    (leftArguments rightArguments arguments : List Argument)
    (responseName fieldName : Name) (childSelectionSet : List Selection)
    (responseValue : Execution.ResponseValue) (fieldErrors : Nat)
    : ¬ fieldPairProjectionTarget targetParent targetField targetField
          leftArguments rightArguments targetParent fieldName arguments
      -> Execution.executeField schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              (ProjectionResolverRef.filler : ProjectionResolverRef (Option ObjectRef)))
            variableValues parentFuel
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors)
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent targetField
                childRuntimeType ref outputType)
              targetParent targetField targetField leftArguments rightArguments)
            variableValues parentFuel
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotProjection hdeep
  simp only [projectionRootResolverValue, projectionResolverValue] at hdeep ⊢
  rw [executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
    schema rootSelectionSet
    (parentObjectProbeFieldResolvers base targetParent targetField
      childRuntimeType ref outputType)
    variableValues targetParent targetField targetField targetParent
    fieldName targetParent responseName leftArguments rightArguments
    arguments (none : Option ObjectRef) childSelectionSet
    hnotProjection parentFuel]
  exact hdeep

theorem selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_deepSuccessWithRef_ok
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (parentFuel : Nat) (targetParent targetField childRuntimeType : Name)
    (ref : ObjectRef) (outputType : TypeRef)
    (leftArguments rightArguments : List Argument) (selectionSet : List Selection)
    : (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> ∃ responseValue fieldErrors,
            Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                (ProjectionResolverRef.filler : ProjectionResolverRef (Option ObjectRef)))
              variableValues parentFuel
              (projectionRootResolverValue
                (.object targetParent (none : Option ObjectRef)))
              responseName
              [{
                parentType := targetParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors))
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ¬ fieldPairProjectionTarget targetParent targetField targetField
                leftArguments rightArguments targetParent fieldName arguments
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent targetField
                    childRuntimeType ref outputType)
                  targetParent targetField targetField leftArguments
                  rightArguments)
                variableValues parentFuel
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                responseName
                [{
                  parentType := targetParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hdeep responseName fieldName arguments directives childSelectionSet
    hmem hnotProjection
  rcases hdeep responseName fieldName arguments directives childSelectionSet
      hmem with
    ⟨responseValue, fieldErrors, hdeepOk⟩
  exact
    ⟨responseValue, fieldErrors,
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_other_root_ok_of_deepSuccessWithRef_ok
        schema rootSelectionSet base variableValues parentFuel targetParent
        targetField childRuntimeType ref outputType leftArguments
        rightArguments arguments responseName fieldName childSelectionSet
        responseValue fieldErrors hnotProjection hdeepOk⟩

theorem selectionSetsDataEquivalent_object_child_of_parent_tail_ok
    {schema : Schema}
    (rootSelectionSet : List Selection)
    (targetParent responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet leftRest rightRest : List Selection)
    (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : Argument.argumentsEquivalent leftArguments rightArguments
      -> schema.lookupField targetParent fieldName = some fieldDefinition
      -> selectionSetDirectiveFree
          (Selection.field responseName fieldName leftArguments [] leftChildSelectionSet
            :: leftRest)
      -> selectionSetDirectiveFree
          (Selection.field responseName fieldName rightArguments [] rightChildSelectionSet
            :: rightRest)
      -> selectionSetNormal schema targetParent
          (Selection.field responseName fieldName leftArguments [] leftChildSelectionSet
            :: leftRest)
      -> selectionSetNormal schema targetParent
          (Selection.field responseName fieldName rightArguments [] rightChildSelectionSet
            :: rightRest)
      -> objectTypeNameBool schema targetParent = true
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
              (variableValues : Execution.VariableValues) (fuel : Nat)
              (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            -> ∃ leftTailFields leftTailErrors rightTailFields rightTailErrors,
                Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base targetParent fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      targetParent fieldName fieldName leftArguments rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    targetParent
                    (projectionRootResolverValue
                      (.object targetParent (none : Option ObjectRef)))
                    leftRest
                  = .ok (leftTailFields, leftTailErrors)
                ∧ Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base targetParent fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      targetParent fieldName fieldName leftArguments
                      rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    targetParent
                    (projectionRootResolverValue
                      (.object targetParent (none : Option ObjectRef)))
                    rightRest
                  = .ok (rightTailFields, rightTailErrors))
      -> selectionSetsDataEquivalent schema targetParent
          (Selection.field responseName fieldName leftArguments [] leftChildSelectionSet
            :: leftRest)
          (Selection.field responseName fieldName rightArguments [] rightChildSelectionSet
            :: rightRest)
      -> selectionSetsDataEquivalent schema runtimeType
          leftChildSelectionSet rightChildSelectionSet := by
  intro harguments hlookup hleftFree hrightFree hleftNormal hrightNormal
    hobject hruntimeObject hfieldInclude htail hparentData ObjectRef base
    variableValues fuel source hsource
  rcases hsource with ⟨sourceRuntimeType, ref, hsourceEq, hsourceInclude⟩
  subst source
  have hsourceRuntimeEq : sourceRuntimeType = runtimeType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hruntimeObject hsourceInclude
  subst sourceRuntimeType
  let parentBase :=
    parentObjectProbeFieldResolvers base targetParent fieldName runtimeType ref
      fieldDefinition.outputType
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet parentBase
      targetParent fieldName fieldName leftArguments rightArguments
  let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
  let parentSource : Execution.ResolverValue
      (ProjectionResolverRef (Option ObjectRef)) :=
    projectionRootResolverValue
      (.object targetParent (none : Option ObjectRef))
  have hparentSource :
      ∃ sourceRuntime sourceRef,
        parentSource =
          Execution.ResolverValue.object sourceRuntime sourceRef
          ∧ schema.typeIncludesObjectBool targetParent sourceRuntime =
            true := by
    exact
      ⟨targetParent, ProjectionResolverRef.root (none : Option ObjectRef),
        by
          simp [parentSource, projectionRootResolverValue,
            projectionResolverValue],
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  rcases htail base variableValues fuel runtimeType ref hfieldInclude with
    ⟨leftTailFields, leftTailErrors, rightTailFields, rightTailErrors,
      hleftTail, hrightTail⟩
  have hhead :
      Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }])).data
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }])).data :=
    target_head_singleton_response_dataEquivalent_of_selectionSetsDataEquivalent_tail_ok
      resolvers variableValues parentFuel targetParent parentSource
      responseName fieldName fieldName leftArguments rightArguments
      leftChildSelectionSet rightChildSelectionSet leftRest rightRest
      leftTailFields rightTailFields leftTailErrors rightTailErrors
      hparentSource hleftFree hrightFree hleftNormal hrightNormal hobject
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hleftTail)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hrightTail)
      hparentData
  have hleftField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments leftArguments
        leftChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hlookup
        hfieldInclude
  have hrightField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments rightArguments
        rightChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hlookup
        hfieldInclude
  have hwrapped :
      Execution.ResponseValue.semanticEquivalent
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    exact
      responseValue_semanticEquivalent_of_singleFieldResult_data responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet))
        (by simpa [hleftField, hrightField] using hhead)
  exact
    wrapTypeRefSelectionSetDataValue_semanticEquivalent_injective
      fieldDefinition.outputType hwrapped

theorem split_context_selectionSets_ok_of_field_ok
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (leftPref rightPref leftSuffix rightSuffix : List Selection)
    : selectionSetDirectiveFree leftPref
      -> selectionSetDirectiveFree rightPref
      -> selectionSetDirectiveFree leftSuffix
      -> selectionSetDirectiveFree rightSuffix
      -> selectionSetNormal schema parentType leftPref
      -> selectionSetNormal schema parentType rightPref
      -> selectionSetNormal schema parentType leftSuffix
      -> selectionSetNormal schema parentType rightSuffix
      -> objectTypeNameBool schema parentType = true
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ leftPref
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
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ rightPref
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
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ leftSuffix
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
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ rightSuffix
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
      -> ∃ leftPrefixFields leftPrefixErrors rightPrefixFields
            rightPrefixErrors leftSuffixFields leftSuffixErrors
            rightSuffixFields rightSuffixErrors,
          Execution.executeSelectionSet schema resolvers variableValues fuel
              parentType source leftPref
            = .ok (leftPrefixFields, leftPrefixErrors)
          ∧ Execution.executeSelectionSet schema resolvers variableValues fuel
              parentType source rightPref
            = .ok (rightPrefixFields, rightPrefixErrors)
          ∧ Execution.executeSelectionSet schema resolvers variableValues fuel
              parentType source leftSuffix
            = .ok (leftSuffixFields, leftSuffixErrors)
          ∧ Execution.executeSelectionSet schema resolvers variableValues fuel
              parentType source rightSuffix
            = .ok (rightSuffixFields, rightSuffixErrors) := by
  intro hleftPrefFree hrightPrefFree hleftSuffixFree hrightSuffixFree
    hleftPrefNormal hrightPrefNormal hleftSuffixNormal hrightSuffixNormal
    hobject hleftPrefFieldOk hrightPrefFieldOk hleftSuffixFieldOk
    hrightSuffixFieldOk
  rcases
      ExecutionSuccess.executeSelectionSet_ok_of_field_ok schema resolvers
        variableValues fuel parentType source leftPref hleftPrefFree
        hleftPrefNormal hobject hleftPrefFieldOk with
    ⟨leftPrefixFields, leftPrefixErrors, hleftPrefix⟩
  rcases
      ExecutionSuccess.executeSelectionSet_ok_of_field_ok schema resolvers
        variableValues fuel parentType source rightPref hrightPrefFree
        hrightPrefNormal hobject hrightPrefFieldOk with
    ⟨rightPrefixFields, rightPrefixErrors, hrightPrefix⟩
  rcases
      ExecutionSuccess.executeSelectionSet_ok_of_field_ok schema resolvers
        variableValues fuel parentType source leftSuffix hleftSuffixFree
        hleftSuffixNormal hobject hleftSuffixFieldOk with
    ⟨leftSuffixFields, leftSuffixErrors, hleftSuffix⟩
  rcases
      ExecutionSuccess.executeSelectionSet_ok_of_field_ok schema resolvers
        variableValues fuel parentType source rightSuffix hrightSuffixFree
        hrightSuffixNormal hobject hrightSuffixFieldOk with
    ⟨rightSuffixFields, rightSuffixErrors, hrightSuffix⟩
  exact
    ⟨leftPrefixFields, leftPrefixErrors, rightPrefixFields,
      rightPrefixErrors, leftSuffixFields, leftSuffixErrors,
      rightSuffixFields, rightSuffixErrors, hleftPrefix, hrightPrefix,
      hleftSuffix, hrightSuffix⟩

theorem object_child_split_context_ok_of_fieldsExecuteOk
    {schema : Schema}
    (rootSelectionSet : List Selection)
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetDirectiveFree
        (leftPref
          ++ Selection.field responseName fieldName leftArguments [] leftChildSelectionSet
              :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
              (variableValues : Execution.VariableValues) (fuel : Nat)
              (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            ->  let resolvers :=
                  fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments rightArguments
                let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
                let parentSource :=
                  projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef))
                selectionSetFieldsExecuteOk schema resolvers variableValues parentFuel
                  parentType parentSource leftPref
                ∧ selectionSetFieldsExecuteOk schema resolvers variableValues
                    parentFuel parentType parentSource rightPref
                ∧ selectionSetFieldsExecuteOk schema resolvers variableValues
                    parentFuel parentType parentSource leftSuffix
                ∧ selectionSetFieldsExecuteOk schema resolvers variableValues
                    parentFuel parentType parentSource rightSuffix)
      -> ∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (childRuntimeType : Name) (ref : ObjectRef),
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
              childRuntimeType
            = true
          -> ∃ leftPrefixFields leftPrefixErrors rightPrefixFields
                rightPrefixErrors leftSuffixFields leftSuffixErrors
                rightSuffixFields rightSuffixErrors,
              Execution.executeSelectionSet schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments rightArguments)
                  variableValues
                  (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                  parentType
                  (projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef)))
                  leftPref
                = .ok (leftPrefixFields, leftPrefixErrors)
              ∧ Execution.executeSelectionSet schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments
                    rightArguments)
                  variableValues
                  (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                  parentType
                  (projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef)))
                  rightPref
                = .ok (rightPrefixFields, rightPrefixErrors)
              ∧ Execution.executeSelectionSet schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments
                    rightArguments)
                  variableValues
                  (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                  parentType
                  (projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef)))
                  leftSuffix
                = .ok (leftSuffixFields, leftSuffixErrors)
              ∧ Execution.executeSelectionSet schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments
                    rightArguments)
                  variableValues
                  (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                  parentType
                  (projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef)))
                  rightSuffix
                = .ok (rightSuffixFields, rightSuffixErrors) := by
  intro hleftFree hrightFree hleftNormal hrightNormal hobject
  dsimp only
  intro hfieldsOk
    ObjectRef base variableValues fuel childRuntimeType ref hinclude
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (parentObjectProbeFieldResolvers base parentType fieldName
        childRuntimeType ref fieldDefinition.outputType)
      parentType fieldName fieldName leftArguments rightArguments
  let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
  let parentSource : Execution.ResolverValue
      (ProjectionResolverRef (Option ObjectRef)) :=
    projectionRootResolverValue
      (.object parentType (none : Option ObjectRef))
  have hleftPrefFree : selectionSetDirectiveFree leftPref :=
    selectionSetDirectiveFree_append_left hleftFree
  have hrightPrefFree : selectionSetDirectiveFree rightPref :=
    selectionSetDirectiveFree_append_left hrightFree
  have hleftTargetSuffixFree :
      selectionSetDirectiveFree
        (Selection.field responseName fieldName leftArguments []
          leftChildSelectionSet :: leftSuffix) :=
    selectionSetDirectiveFree_append_right (left := leftPref) hleftFree
  have hrightTargetSuffixFree :
      selectionSetDirectiveFree
        (Selection.field responseName fieldName rightArguments []
          rightChildSelectionSet :: rightSuffix) :=
    selectionSetDirectiveFree_append_right (left := rightPref) hrightFree
  have hleftSuffixFree : selectionSetDirectiveFree leftSuffix :=
    selectionSetDirectiveFree_tail hleftTargetSuffixFree
  have hrightSuffixFree : selectionSetDirectiveFree rightSuffix :=
    selectionSetDirectiveFree_tail hrightTargetSuffixFree
  have hleftPrefNormal : selectionSetNormal schema parentType leftPref :=
    selectionSetNormal_append_left hleftNormal
  have hrightPrefNormal : selectionSetNormal schema parentType rightPref :=
    selectionSetNormal_append_left hrightNormal
  have hleftTargetSuffixNormal :
      selectionSetNormal schema parentType
        (Selection.field responseName fieldName leftArguments []
          leftChildSelectionSet :: leftSuffix) :=
    selectionSetNormal_append_right (left := leftPref) hleftNormal
  have hrightTargetSuffixNormal :
      selectionSetNormal schema parentType
        (Selection.field responseName fieldName rightArguments []
          rightChildSelectionSet :: rightSuffix) :=
    selectionSetNormal_append_right (left := rightPref) hrightNormal
  have hleftSuffixNormal : selectionSetNormal schema parentType leftSuffix :=
    selectionSetNormal_tail hleftTargetSuffixNormal
  have hrightSuffixNormal : selectionSetNormal schema parentType rightSuffix :=
    selectionSetNormal_tail hrightTargetSuffixNormal
  have hfields :=
    hfieldsOk base variableValues fuel childRuntimeType ref hinclude
  rcases hfields with
    ⟨hleftPrefFieldsOk, hrightPrefFieldsOk, hleftSuffixFieldsOk,
      hrightSuffixFieldsOk⟩
  exact
    split_context_selectionSets_ok_of_field_ok schema resolvers
      variableValues parentFuel parentType parentSource leftPref rightPref
      leftSuffix rightSuffix hleftPrefFree hrightPrefFree hleftSuffixFree
      hrightSuffixFree hleftPrefNormal hrightPrefNormal hleftSuffixNormal
      hrightSuffixNormal hobject hleftPrefFieldsOk hrightPrefFieldsOk
      hleftSuffixFieldsOk hrightSuffixFieldsOk

theorem object_child_split_context_ok_of_concrete_fieldsExecuteOk
    {ObjectRef : Type} {schema : Schema}
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat)
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {fieldDefinition : FieldDefinition}
    (childRuntimeType : Name) (ref : ObjectRef)
    : selectionSetDirectiveFree
        (leftPref
          ++ Selection.field responseName fieldName leftArguments [] leftChildSelectionSet
              :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> selectionSetFieldsExecuteOk schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base parentType fieldName
                childRuntimeType ref fieldDefinition.outputType)
              parentType fieldName fieldName leftArguments rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            parentType
            (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
            leftPref
          ∧ selectionSetFieldsExecuteOk schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base parentType fieldName
                  childRuntimeType ref fieldDefinition.outputType)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              parentType
              (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
              rightPref
          ∧ selectionSetFieldsExecuteOk schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base parentType fieldName
                  childRuntimeType ref fieldDefinition.outputType)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              parentType
              (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
              leftSuffix
          ∧ selectionSetFieldsExecuteOk schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base parentType fieldName
                  childRuntimeType ref fieldDefinition.outputType)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              parentType
              (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
              rightSuffix
      -> ∃ leftPrefixFields leftPrefixErrors rightPrefixFields
            rightPrefixErrors leftSuffixFields leftSuffixErrors
            rightSuffixFields rightSuffixErrors,
          Execution.executeSelectionSet schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base parentType fieldName
                  childRuntimeType ref fieldDefinition.outputType)
                parentType fieldName fieldName leftArguments rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              parentType
              (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
              leftPref
            = .ok (leftPrefixFields, leftPrefixErrors)
          ∧ Execution.executeSelectionSet schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base parentType fieldName
                  childRuntimeType ref fieldDefinition.outputType)
                parentType fieldName fieldName leftArguments
                rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              parentType
              (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
              rightPref
            = .ok (rightPrefixFields, rightPrefixErrors)
          ∧ Execution.executeSelectionSet schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base parentType fieldName
                  childRuntimeType ref fieldDefinition.outputType)
                parentType fieldName fieldName leftArguments
                rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              parentType
              (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
              leftSuffix
            = .ok (leftSuffixFields, leftSuffixErrors)
          ∧ Execution.executeSelectionSet schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base parentType fieldName
                  childRuntimeType ref fieldDefinition.outputType)
                parentType fieldName fieldName leftArguments
                rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              parentType
              (projectionRootResolverValue (.object parentType (none : Option ObjectRef)))
              rightSuffix
            = .ok (rightSuffixFields, rightSuffixErrors) := by
  intro hleftFree hrightFree hleftNormal hrightNormal hobject hfieldsOk
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (parentObjectProbeFieldResolvers base parentType fieldName
        childRuntimeType ref fieldDefinition.outputType)
      parentType fieldName fieldName leftArguments rightArguments
  let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
  let parentSource : Execution.ResolverValue
      (ProjectionResolverRef (Option ObjectRef)) :=
    projectionRootResolverValue
      (.object parentType (none : Option ObjectRef))
  have hleftPrefFree : selectionSetDirectiveFree leftPref :=
    selectionSetDirectiveFree_append_left hleftFree
  have hrightPrefFree : selectionSetDirectiveFree rightPref :=
    selectionSetDirectiveFree_append_left hrightFree
  have hleftTargetSuffixFree :
      selectionSetDirectiveFree
        (Selection.field responseName fieldName leftArguments []
          leftChildSelectionSet :: leftSuffix) :=
    selectionSetDirectiveFree_append_right (left := leftPref) hleftFree
  have hrightTargetSuffixFree :
      selectionSetDirectiveFree
        (Selection.field responseName fieldName rightArguments []
          rightChildSelectionSet :: rightSuffix) :=
    selectionSetDirectiveFree_append_right (left := rightPref) hrightFree
  have hleftSuffixFree : selectionSetDirectiveFree leftSuffix :=
    selectionSetDirectiveFree_tail hleftTargetSuffixFree
  have hrightSuffixFree : selectionSetDirectiveFree rightSuffix :=
    selectionSetDirectiveFree_tail hrightTargetSuffixFree
  have hleftPrefNormal : selectionSetNormal schema parentType leftPref :=
    selectionSetNormal_append_left hleftNormal
  have hrightPrefNormal : selectionSetNormal schema parentType rightPref :=
    selectionSetNormal_append_left hrightNormal
  have hleftTargetSuffixNormal :
      selectionSetNormal schema parentType
        (Selection.field responseName fieldName leftArguments []
          leftChildSelectionSet :: leftSuffix) :=
    selectionSetNormal_append_right (left := leftPref) hleftNormal
  have hrightTargetSuffixNormal :
      selectionSetNormal schema parentType
        (Selection.field responseName fieldName rightArguments []
          rightChildSelectionSet :: rightSuffix) :=
    selectionSetNormal_append_right (left := rightPref) hrightNormal
  have hleftSuffixNormal : selectionSetNormal schema parentType leftSuffix :=
    selectionSetNormal_tail hleftTargetSuffixNormal
  have hrightSuffixNormal : selectionSetNormal schema parentType rightSuffix :=
    selectionSetNormal_tail hrightTargetSuffixNormal
  rcases hfieldsOk with
    ⟨hleftPrefFieldsOk, hrightPrefFieldsOk, hleftSuffixFieldsOk,
      hrightSuffixFieldsOk⟩
  exact
    split_context_selectionSets_ok_of_field_ok schema resolvers
      variableValues parentFuel parentType parentSource leftPref rightPref
      leftSuffix rightSuffix hleftPrefFree hrightPrefFree hleftSuffixFree
      hrightSuffixFree hleftPrefNormal hrightPrefNormal hleftSuffixNormal
      hrightSuffixNormal hobject hleftPrefFieldsOk hrightPrefFieldsOk
      hleftSuffixFieldsOk hrightSuffixFieldsOk

theorem responseData_semanticEquivalent_object_child_of_parent_split_context_ok
    {ObjectRef : Type} {schema : Schema}
    (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat)
    (targetParent responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection)
    (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    : schema.lookupField targetParent fieldName = some fieldDefinition
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema targetParent
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema targetParent
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema targetParent = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> (∃ leftPrefixFields leftPrefixErrors rightPrefixFields
              rightPrefixErrors leftSuffixFields leftSuffixErrors
              rightSuffixFields rightSuffixErrors,
            Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                leftPref
              = .ok (leftPrefixFields, leftPrefixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                rightPref
              = .ok (rightPrefixFields, rightPrefixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                leftSuffix
              = .ok (leftSuffixFields, leftSuffixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                rightSuffix
              = .ok (rightSuffixFields, rightSuffixErrors))
      -> selectionSetsDataEquivalent schema targetParent
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet).data
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet).data := by
  intro hlookup hleftFree hrightFree hleftNormal hrightNormal hobject
    hfieldInclude hcontext hparentData
  let parentBase :=
    parentObjectProbeFieldResolvers base targetParent fieldName runtimeType ref
      fieldDefinition.outputType
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet parentBase
      targetParent fieldName fieldName leftArguments rightArguments
  let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
  let parentSource : Execution.ResolverValue
      (ProjectionResolverRef (Option ObjectRef)) :=
    projectionRootResolverValue
      (.object targetParent (none : Option ObjectRef))
  have hparentSource :
      ∃ sourceRuntime sourceRef,
        parentSource =
          Execution.ResolverValue.object sourceRuntime sourceRef
          ∧ schema.typeIncludesObjectBool targetParent sourceRuntime =
            true := by
    exact
      ⟨targetParent, ProjectionResolverRef.root (none : Option ObjectRef),
        by
          simp [parentSource, projectionRootResolverValue,
            projectionResolverValue],
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  rcases hcontext with
    ⟨leftPrefixFields, leftPrefixErrors, rightPrefixFields,
      rightPrefixErrors, leftSuffixFields, leftSuffixErrors,
      rightSuffixFields, rightSuffixErrors, hleftPrefix, hrightPrefix,
      hleftSuffix, hrightSuffix⟩
  have hhead :
      Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }])).data
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }])).data :=
    target_split_singleton_response_dataEquivalent_of_selectionSetsDataEquivalent_context_ok
      resolvers variableValues parentFuel targetParent parentSource
      responseName fieldName fieldName leftArguments rightArguments
      leftChildSelectionSet rightChildSelectionSet leftPref rightPref
      leftSuffix rightSuffix leftPrefixFields rightPrefixFields
      leftSuffixFields rightSuffixFields leftPrefixErrors rightPrefixErrors
      leftSuffixErrors rightSuffixErrors hparentSource hleftFree hrightFree
      hleftNormal hrightNormal hobject
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hleftPrefix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hrightPrefix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hleftSuffix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hrightSuffix)
      hparentData
  have hleftField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments leftArguments
        leftChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hlookup
        hfieldInclude
  have hrightField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments rightArguments
        rightChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hlookup
        hfieldInclude
  have hwrapped :
      Execution.ResponseValue.semanticEquivalent
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    exact
      responseValue_semanticEquivalent_of_singleFieldResult_data responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet))
        (by simpa [hleftField, hrightField] using hhead)
  exact
    wrapTypeRefSelectionSetDataValue_semanticEquivalent_injective
      fieldDefinition.outputType hwrapped

theorem responseData_semanticEquivalent_object_child_of_parent_responseData_split_context_ok
    {ObjectRef : Type} {schema : Schema} (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection)
    (fieldDefinition : FieldDefinition) (runtimeType : Name) (ref : ObjectRef)
    : schema.lookupField targetParent fieldName = some fieldDefinition
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema targetParent
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema targetParent
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema targetParent = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> (∃ leftPrefixFields leftPrefixErrors rightPrefixFields
              rightPrefixErrors leftSuffixFields leftSuffixErrors
              rightSuffixFields rightSuffixErrors,
            Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                leftPref
              = .ok (leftPrefixFields, leftPrefixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                rightPref
              = .ok (rightPrefixFields, rightPrefixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                leftSuffix
              = .ok (leftSuffixFields, leftSuffixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                rightSuffix
              = .ok (rightSuffixFields, rightSuffixErrors))
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent fieldName
                runtimeType ref fieldDefinition.outputType)
              targetParent fieldName fieldName leftArguments rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            targetParent
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)).data
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent fieldName
                runtimeType ref fieldDefinition.outputType)
              targetParent fieldName fieldName leftArguments rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            targetParent
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix)).data
      -> Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet).data
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet).data := by
  intro hlookup hleftFree hrightFree hleftNormal hrightNormal hobject
    hfieldInclude hcontext hparentData
  let parentBase :=
    parentObjectProbeFieldResolvers base targetParent fieldName runtimeType ref
      fieldDefinition.outputType
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet parentBase
      targetParent fieldName fieldName leftArguments rightArguments
  let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
  let parentSource : Execution.ResolverValue
      (ProjectionResolverRef (Option ObjectRef)) :=
    projectionRootResolverValue
      (.object targetParent (none : Option ObjectRef))
  have hparentSource :
      ∃ sourceRuntime sourceRef,
        parentSource =
          Execution.ResolverValue.object sourceRuntime sourceRef
          ∧ schema.typeIncludesObjectBool targetParent sourceRuntime =
            true := by
    exact
      ⟨targetParent, ProjectionResolverRef.root (none : Option ObjectRef),
        by
          simp [parentSource, projectionRootResolverValue,
            projectionResolverValue],
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  rcases hcontext with
    ⟨leftPrefixFields, leftPrefixErrors, rightPrefixFields,
      rightPrefixErrors, leftSuffixFields, leftSuffixErrors,
      rightSuffixFields, rightSuffixErrors, hleftPrefix, hrightPrefix,
      hleftSuffix, hrightSuffix⟩
  have hhead :
      Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }])).data
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }])).data :=
    target_split_singleton_response_dataEquivalent_of_responseData_context_ok
      resolvers variableValues parentFuel targetParent parentSource
      responseName fieldName fieldName leftArguments rightArguments
      leftChildSelectionSet rightChildSelectionSet leftPref rightPref
      leftSuffix rightSuffix leftPrefixFields rightPrefixFields
      leftSuffixFields rightSuffixFields leftPrefixErrors rightPrefixErrors
      leftSuffixErrors rightSuffixErrors hparentSource hleftFree hrightFree
      hleftNormal hrightNormal hobject
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hleftPrefix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hrightPrefix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hleftSuffix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hrightSuffix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hparentData)
  have hleftField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments leftArguments
        leftChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hlookup
        hfieldInclude
  have hrightField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments rightArguments
        rightChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hlookup
        hfieldInclude
  have hwrapped :
      Execution.ResponseValue.semanticEquivalent
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    exact
      responseValue_semanticEquivalent_of_singleFieldResult_data responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet))
        (by simpa [hleftField, hrightField] using hhead)
  exact
    wrapTypeRefSelectionSetDataValue_semanticEquivalent_injective
      fieldDefinition.outputType hwrapped

theorem not_selectionSetsDataEquivalent_of_object_child_responseData_diff_split_context_ok
    {ObjectRef : Type} {schema : Schema} (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection)
    (fieldDefinition : FieldDefinition) (runtimeType : Name) (ref : ObjectRef)
    : schema.lookupField targetParent fieldName = some fieldDefinition
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema targetParent
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema targetParent
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema targetParent = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> (∃ leftPrefixFields leftPrefixErrors rightPrefixFields
              rightPrefixErrors leftSuffixFields leftSuffixErrors
              rightSuffixFields rightSuffixErrors,
            Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                leftPref
              = .ok (leftPrefixFields, leftPrefixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                rightPref
              = .ok (rightPrefixFields, rightPrefixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                leftSuffix
              = .ok (leftSuffixFields, leftSuffixErrors)
            ∧ Execution.executeSelectionSet schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (parentObjectProbeFieldResolvers base targetParent fieldName
                    runtimeType ref fieldDefinition.outputType)
                  targetParent fieldName fieldName leftArguments rightArguments)
                variableValues
                (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                targetParent
                (projectionRootResolverValue
                  (.object targetParent (none : Option ObjectRef)))
                rightSuffix
              = .ok (rightSuffixFields, rightSuffixErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema base variableValues fuel
              runtimeType (.object runtimeType ref) leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema base variableValues fuel
              runtimeType (.object runtimeType ref) rightChildSelectionSet).data
      -> ¬ selectionSetsDataEquivalent schema targetParent
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix) := by
  intro hlookup hleftFree hrightFree hleftNormal hrightNormal hobject
    hfieldInclude hcontext hchildNot hparentData
  exact hchildNot
    (responseData_semanticEquivalent_object_child_of_parent_split_context_ok
      rootSelectionSet base variableValues fuel targetParent responseName
      fieldName leftArguments rightArguments leftChildSelectionSet
      rightChildSelectionSet leftPref rightPref leftSuffix rightSuffix
      fieldDefinition runtimeType ref hlookup hleftFree hrightFree
      hleftNormal hrightNormal hobject hfieldInclude hcontext hparentData)

theorem selectionSetsDataEquivalent_object_child_of_parent_split_context_ok
    {schema : Schema}
    (rootSelectionSet : List Selection)
    (targetParent responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection)
    (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : Argument.argumentsEquivalent leftArguments rightArguments
      -> schema.lookupField targetParent fieldName = some fieldDefinition
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema targetParent
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema targetParent
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema targetParent = true
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
              (variableValues : Execution.VariableValues) (fuel : Nat)
              (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            -> ∃ leftPrefixFields leftPrefixErrors rightPrefixFields
                  rightPrefixErrors leftSuffixFields leftSuffixErrors
                  rightSuffixFields rightSuffixErrors,
                Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base targetParent fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      targetParent fieldName fieldName leftArguments rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    targetParent
                    (projectionRootResolverValue
                      (.object targetParent (none : Option ObjectRef)))
                    leftPref
                  = .ok (leftPrefixFields, leftPrefixErrors)
                ∧ Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base targetParent fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      targetParent fieldName fieldName leftArguments
                      rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    targetParent
                    (projectionRootResolverValue
                      (.object targetParent (none : Option ObjectRef)))
                    rightPref
                  = .ok (rightPrefixFields, rightPrefixErrors)
                ∧ Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base targetParent fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      targetParent fieldName fieldName leftArguments
                      rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    targetParent
                    (projectionRootResolverValue
                      (.object targetParent (none : Option ObjectRef)))
                    leftSuffix
                  = .ok (leftSuffixFields, leftSuffixErrors)
                ∧ Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base targetParent fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      targetParent fieldName fieldName leftArguments
                      rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    targetParent
                    (projectionRootResolverValue
                      (.object targetParent (none : Option ObjectRef)))
                    rightSuffix
                  = .ok (rightSuffixFields, rightSuffixErrors))
      -> selectionSetsDataEquivalent schema targetParent
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetsDataEquivalent schema runtimeType
          leftChildSelectionSet rightChildSelectionSet := by
  intro harguments hlookup hleftFree hrightFree hleftNormal hrightNormal
    hobject hruntimeObject hfieldInclude hcontext hparentData ObjectRef base
    variableValues fuel source hsource
  rcases hsource with ⟨sourceRuntimeType, ref, hsourceEq, hsourceInclude⟩
  subst source
  have hsourceRuntimeEq : sourceRuntimeType = runtimeType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hruntimeObject hsourceInclude
  subst sourceRuntimeType
  let parentBase :=
    parentObjectProbeFieldResolvers base targetParent fieldName runtimeType ref
      fieldDefinition.outputType
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet parentBase
      targetParent fieldName fieldName leftArguments rightArguments
  let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
  let parentSource : Execution.ResolverValue
      (ProjectionResolverRef (Option ObjectRef)) :=
    projectionRootResolverValue
      (.object targetParent (none : Option ObjectRef))
  have hparentSource :
      ∃ sourceRuntime sourceRef,
        parentSource =
          Execution.ResolverValue.object sourceRuntime sourceRef
          ∧ schema.typeIncludesObjectBool targetParent sourceRuntime =
            true := by
    exact
      ⟨targetParent, ProjectionResolverRef.root (none : Option ObjectRef),
        by
          simp [parentSource, projectionRootResolverValue,
            projectionResolverValue],
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  rcases hcontext base variableValues fuel runtimeType ref hfieldInclude with
    ⟨leftPrefixFields, leftPrefixErrors, rightPrefixFields,
      rightPrefixErrors, leftSuffixFields, leftSuffixErrors,
      rightSuffixFields, rightSuffixErrors, hleftPrefix, hrightPrefix,
      hleftSuffix, hrightSuffix⟩
  have hhead :
      Execution.ResponseValue.semanticEquivalent
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }])).data
        (Execution.selectionSetResultToResponse
          (Execution.executeField schema resolvers variableValues parentFuel
            parentSource responseName
            [{
              parentType := targetParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }])).data :=
    target_split_singleton_response_dataEquivalent_of_selectionSetsDataEquivalent_context_ok
      resolvers variableValues parentFuel targetParent parentSource
      responseName fieldName fieldName leftArguments rightArguments
      leftChildSelectionSet rightChildSelectionSet leftPref rightPref
      leftSuffix rightSuffix leftPrefixFields rightPrefixFields
      leftSuffixFields rightSuffixFields leftPrefixErrors rightPrefixErrors
      leftSuffixErrors rightSuffixErrors hparentSource hleftFree hrightFree
      hleftNormal hrightNormal hobject
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hleftPrefix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hrightPrefix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hleftSuffix)
      (by simpa [resolvers, parentBase, parentFuel, parentSource] using
        hrightSuffix)
      hparentData
  have hleftField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_left_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments leftArguments
        leftChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hlookup
        hfieldInclude
  have hrightField :
      Execution.executeField schema resolvers variableValues parentFuel
        parentSource responseName
        [{
          parentType := targetParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    dsimp [resolvers, parentBase, parentFuel, parentSource]
    exact
      executeField_fieldPairOrDeepSuccess_parentObjectProbe_right_root_response
        schema rootSelectionSet base variableValues fuel targetParent
        fieldName responseName leftArguments rightArguments rightArguments
        rightChildSelectionSet fieldDefinition runtimeType ref
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hlookup
        hfieldInclude
  have hwrapped :
      Execution.ResponseValue.semanticEquivalent
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetDataValue fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet)) := by
    exact
      responseValue_semanticEquivalent_of_singleFieldResult_data responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) leftChildSelectionSet))
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.executeSelectionSetAsResponse schema base variableValues fuel
            runtimeType (.object runtimeType ref) rightChildSelectionSet))
        (by simpa [hleftField, hrightField] using hhead)
  exact
    wrapTypeRefSelectionSetDataValue_semanticEquivalent_injective
      fieldDefinition.outputType hwrapped

theorem selectionSetsDataEquivalent_object_child_of_parent_empty_tail
    {schema : Schema}
    (rootSelectionSet : List Selection)
    (targetParent responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : Argument.argumentsEquivalent leftArguments rightArguments
      -> schema.lookupField targetParent fieldName = some fieldDefinition
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName leftArguments [] leftChildSelectionSet]
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName rightArguments []
            rightChildSelectionSet]
      -> selectionSetNormal schema targetParent
          [Selection.field responseName fieldName leftArguments [] leftChildSelectionSet]
      -> selectionSetNormal schema targetParent
          [Selection.field responseName fieldName rightArguments []
            rightChildSelectionSet]
      -> objectTypeNameBool schema targetParent = true
      -> objectTypeNameBool schema runtimeType = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> selectionSetsDataEquivalent schema targetParent
          [Selection.field responseName fieldName leftArguments [] leftChildSelectionSet]
          [Selection.field responseName fieldName rightArguments []
            rightChildSelectionSet]
      -> selectionSetsDataEquivalent schema runtimeType
          leftChildSelectionSet rightChildSelectionSet := by
  intro harguments hlookup hleftFree hrightFree hleftNormal hrightNormal
    hobject hruntimeObject hfieldInclude hparentData
  exact
    selectionSetsDataEquivalent_object_child_of_parent_tail_ok
      rootSelectionSet targetParent responseName fieldName leftArguments
      rightArguments leftChildSelectionSet rightChildSelectionSet [] []
      fieldDefinition runtimeType harguments hlookup hleftFree hrightFree
      hleftNormal hrightNormal hobject hruntimeObject hfieldInclude
      (by
        intro ObjectRef base variableValues fuel childRuntimeType ref
          hchildInclude
        refine ⟨[], 0, [], 0, ?_, ?_⟩
        · simp [Execution.executeSelectionSet,
            Execution.executeRootSelectionSet, Execution.collectFields,
            Execution.executeCollectedFields]
        · simp [Execution.executeSelectionSet,
            Execution.executeRootSelectionSet, Execution.collectFields,
            Execution.executeCollectedFields])
      hparentData

end GroundTypeNormalization

end NormalForm

end GraphQL
