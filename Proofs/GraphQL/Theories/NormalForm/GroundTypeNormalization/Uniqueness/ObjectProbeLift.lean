import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Probes
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ResolverLift

/-!
Wrapper-aware parent resolver probes.

`parentObjectFieldResolvers` is enough for named object fields. This module
generalizes the parent probe to fields whose output type wraps the same composite
named type in list/non-null constructors, while preserving the existing resolver
lifting behavior inside the child object.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def parentObjectProbeFieldResolvers {ObjectRef : Type}
    (base : Execution.Resolvers ObjectRef)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    (outputType : TypeRef)
    : Execution.Resolvers (Option ObjectRef) where
  resolve parentType fieldName arguments source :=
    match source with
    | .object _ none =>
        if parentType == targetParent && fieldName == targetField then
          some (objectProbeResolverValueWithRuntime runtimeType (some ref) outputType)
        else
          none
    | _ =>
        (liftResolvers base).resolve parentType fieldName arguments source
  resolve_argumentsEquivalent := by
    intro parentType fieldName firstArguments laterArguments source harguments
    cases source with
    | null =>
        exact (liftResolvers base).resolve_argumentsEquivalent parentType
          fieldName firstArguments laterArguments .null harguments
    | scalar value =>
        exact (liftResolvers base).resolve_argumentsEquivalent parentType
          fieldName firstArguments laterArguments (.scalar value) harguments
    | list values =>
        exact (liftResolvers base).resolve_argumentsEquivalent parentType
          fieldName firstArguments laterArguments (.list values) harguments
    | object sourceType sourceRef =>
        cases sourceRef with
        | none =>
            by_cases htarget :
                parentType == targetParent && fieldName == targetField
            · simp [htarget]
            · simp [htarget]
        | some sourceRef =>
            exact (liftResolvers base).resolve_argumentsEquivalent parentType
              fieldName firstArguments laterArguments
              (.object sourceType (some sourceRef)) harguments

theorem parentObjectProbeFieldResolvers_target
    {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    (outputType : TypeRef) (arguments : Execution.CoercedArguments)
    : (parentObjectProbeFieldResolvers base targetParent targetField
        runtimeType ref outputType).resolve
        targetParent targetField arguments (.object targetParent none)
      = some (objectProbeResolverValueWithRuntime runtimeType (some ref) outputType) := by
  simp [parentObjectProbeFieldResolvers]

theorem parentObjectProbeFieldResolvers_resolve_liftResolverValue
    {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    (outputType : TypeRef) (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue ObjectRef)
    : (parentObjectProbeFieldResolvers base targetParent targetField
        runtimeType ref outputType).resolve
        parentType fieldName arguments (liftResolverValue source)
      = (liftResolvers base).resolve parentType fieldName arguments
          (liftResolverValue source) := by
  cases source <;> simp [parentObjectProbeFieldResolvers, liftResolverValue]

mutual
  theorem executeCollectedFields_parentObjectProbeFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      (outputType : TypeRef)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
          (fields : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema
            (parentObjectProbeFieldResolvers base targetParent targetField
              runtimeType ref outputType)
            variableValues fuel (liftResolverValue source) fields
          = Execution.executeCollectedFields schema (liftResolvers base)
              variableValues fuel (liftResolverValue source) fields
    | fuel, source, [] => by
        simp [Execution.executeCollectedFields]
    | fuel, source, (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          executeField_parentObjectProbeFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref outputType fuel source responseName fields,
          executeCollectedFields_parentObjectProbeFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref outputType fuel source rest]

  theorem executeField_parentObjectProbeFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      (outputType : TypeRef)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
          (responseName : Name) (fields : List Execution.ExecutableField),
          Execution.executeField schema
            (parentObjectProbeFieldResolvers base targetParent targetField
              runtimeType ref outputType)
            variableValues fuel (liftResolverValue source) responseName fields
          = Execution.executeField schema (liftResolvers base) variableValues fuel
              (liftResolverValue source) responseName fields
    | fuel, source, responseName, [] => by
        simp [Execution.executeField]
    | 0, source, responseName, field :: fields => by
        simp [Execution.executeField]
    | fuel + 1, source, responseName, field :: fields => by
        cases hlookup : schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, hlookup]
        | some fieldDefinition =>
            cases hcoerce : Execution.coerceArgumentValues schema variableValues
                fieldDefinition.arguments field.arguments with
            | error =>
                simp [Execution.executeField, Execution.resolveFieldValue, hlookup,
                  hcoerce]
            | success coercedArguments =>
            have hresolveEq :=
              parentObjectProbeFieldResolvers_resolve_liftResolverValue base
                targetParent targetField runtimeType ref outputType
                field.parentType field.fieldName coercedArguments source
            have hliftResolve :=
              liftResolvers_resolve_liftResolverValue base field.parentType
                field.fieldName coercedArguments source
            cases hresolve :
                base.resolve field.parentType field.fieldName
                  coercedArguments source with
            | none =>
                simp [Execution.executeField, Execution.resolveFieldValue, hlookup,
                  hcoerce, hresolveEq,
                  hliftResolve, hresolve]
            | some resolved =>
                simp [Execution.executeField, Execution.resolveFieldValue, hlookup,
                  hcoerce, hresolveEq,
                  hliftResolve, hresolve,
                  completeValue_parentObjectProbeFieldResolvers_liftResolverValue
                    schema base variableValues targetParent targetField
                    runtimeType ref outputType fuel fieldDefinition.outputType
                    (field :: fields) resolved]

  theorem completeValue_parentObjectProbeFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      (outputType : TypeRef)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
          (fields : List Execution.ExecutableField)
          (value : Execution.ResolverValue ObjectRef),
          Execution.completeValue schema
            (parentObjectProbeFieldResolvers base targetParent targetField
              runtimeType ref outputType)
            variableValues fuel fieldType fields (liftResolverValue value)
          = Execution.completeValue schema (liftResolvers base) variableValues
              fuel fieldType fields (liftResolverValue value)
    | 0, fieldType, fields, value => by
        simp [Execution.completeValue, Execution.outOfFuel]
    | fuel + 1, .nonNull inner, fields, value => by
        simp [Execution.completeValue,
          completeValue_parentObjectProbeFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref outputType (fuel + 1) inner fields value]
    | fuel + 1, .named typeName, fields, .null => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .named typeName, fields, .scalar value => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .named typeName, fields, .object objectType objectRef => by
        by_cases hinclude :
            schema.typeIncludesObjectBool typeName objectType = true
        · simp [liftResolverValue, Execution.completeValue, hinclude]
          have hexecute :
              Execution.executeCollectedFields schema
                (parentObjectProbeFieldResolvers base targetParent targetField
                  runtimeType ref outputType)
                variableValues fuel
                (Execution.ResolverValue.object objectType (some objectRef))
                (Execution.collectFields schema variableValues objectType
                  (Execution.ResolverValue.object objectType (some objectRef))
                  (Execution.mergedFieldSelectionSet fields))
              =
              Execution.executeCollectedFields schema (liftResolvers base)
                variableValues fuel
                (Execution.ResolverValue.object objectType (some objectRef))
                (Execution.collectFields schema variableValues objectType
                  (Execution.ResolverValue.object objectType (some objectRef))
                  (Execution.mergedFieldSelectionSet fields)) := by
            simpa [liftResolverValue] using
              executeCollectedFields_parentObjectProbeFieldResolvers_liftResolverValue
                schema base variableValues targetParent targetField
                runtimeType ref outputType fuel
                (Execution.ResolverValue.object objectType objectRef)
                (Execution.collectFields schema variableValues objectType
                  (liftResolverValue
                    (Execution.ResolverValue.object objectType objectRef))
                  (Execution.mergedFieldSelectionSet fields))
          rw [hexecute]
        · have hincludeFalse :
              schema.typeIncludesObjectBool typeName objectType = false := by
            cases h : schema.typeIncludesObjectBool typeName objectType
            · rfl
            · contradiction
          simp [liftResolverValue, Execution.completeValue, hincludeFalse]
    | fuel + 1, .named typeName, fields, .list values => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .null => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .scalar value => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .object objectType objectRef => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .list values => by
        simp [liftResolverValue, Execution.completeValue,
          completeValueList_parentObjectProbeFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref outputType fuel inner fields values]

  theorem completeValueList_parentObjectProbeFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      (outputType : TypeRef)
      : ∀ (fuel : Nat) (itemType : TypeRef)
          (fields : List Execution.ExecutableField)
          (values : List (Execution.ResolverValue ObjectRef)),
          Execution.completeValueList schema
            (parentObjectProbeFieldResolvers base targetParent targetField
              runtimeType ref outputType)
            variableValues fuel itemType fields (values.map liftResolverValue)
          = Execution.completeValueList schema (liftResolvers base) variableValues
              fuel itemType fields (values.map liftResolverValue)
    | fuel, itemType, fields, [] => by
        simp [Execution.completeValueList]
    | fuel, itemType, fields, value :: values => by
        simp [Execution.completeValueList,
          completeValue_parentObjectProbeFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref outputType fuel itemType fields value,
          completeValueList_parentObjectProbeFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref outputType fuel itemType fields values]
end

theorem executeSelectionSetAsResponse_parentObjectProbeFieldResolvers_liftResolverValue
    {ObjectRef : Type} (schema : Schema)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    (outputType : TypeRef) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.executeSelectionSetAsResponse schema
        (parentObjectProbeFieldResolvers base targetParent targetField
          runtimeType ref outputType)
        variableValues fuel parentType (liftResolverValue source) selectionSet
      = Execution.executeSelectionSetAsResponse schema (liftResolvers base)
          variableValues fuel parentType (liftResolverValue source)
          selectionSet := by
  simp [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
    Execution.executeRootSelectionSet,
    executeCollectedFields_parentObjectProbeFieldResolvers_liftResolverValue
      schema base variableValues targetParent targetField runtimeType ref
      outputType fuel source
      (Execution.collectFields schema variableValues parentType
        (liftResolverValue source) selectionSet)]

end GroundTypeNormalization

end NormalForm

end GraphQL
