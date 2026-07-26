import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Statements

/-!
Resolver lifting helpers for uniqueness probes.

These lemmas let a parent-level probe use `Option ObjectRef` to reserve `none`
for the synthetic parent source while delegating child execution at `some ref`
back to an arbitrary base resolver environment.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def liftResolverValue {ObjectRef : Type}
    : Execution.ResolverValue ObjectRef -> Execution.ResolverValue (Option ObjectRef)
  | .null => .null
  | .scalar value => .scalar value
  | .object typeName ref => .object typeName (some ref)
  | .list values => .list (values.map liftResolverValue)

def lowerResolverValue? {ObjectRef : Type}
    : Execution.ResolverValue (Option ObjectRef)
      -> Option (Execution.ResolverValue ObjectRef)
  | .null => some .null
  | .scalar value => some (.scalar value)
  | .object typeName (some ref) => some (.object typeName ref)
  | .object _typeName none => none
  | .list values =>
      (values.mapM lowerResolverValue?).map Execution.ResolverValue.list

mutual
  theorem lowerResolverValue?_liftResolverValue {ObjectRef : Type}
      : ∀ value : Execution.ResolverValue ObjectRef,
          lowerResolverValue? (liftResolverValue value) = some value
    | .null => by
        simp [liftResolverValue, lowerResolverValue?]
    | .scalar value => by
        simp [liftResolverValue, lowerResolverValue?]
    | .object typeName ref => by
        simp [liftResolverValue, lowerResolverValue?]
    | .list values => by
        simp [liftResolverValue, lowerResolverValue?,
          lowerResolverValues?_map_liftResolverValue values]

  theorem lowerResolverValues?_map_liftResolverValue {ObjectRef : Type}
      : ∀ values : List (Execution.ResolverValue ObjectRef),
          (values.map liftResolverValue).mapM lowerResolverValue? = some values
    | [] => by
        simp
    | value :: rest => by
        simp [lowerResolverValue?_liftResolverValue value,
          lowerResolverValues?_map_liftResolverValue rest]
end

def liftResolvers {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
    : Execution.Resolvers (Option ObjectRef) where
  resolve parentType fieldName arguments source :=
    match lowerResolverValue? source with
    | none => none
    | some lowered =>
        (base.resolve parentType fieldName arguments lowered).map
          liftResolverValue
  resolve_argumentsEquivalent := by
    intro parentType fieldName firstArguments laterArguments source harguments
    change
      (match lowerResolverValue? source with
      | none => none
      | some lowered =>
          (base.resolve parentType fieldName firstArguments lowered).map
            liftResolverValue)
      =
      (match lowerResolverValue? source with
      | none => none
      | some lowered =>
          (base.resolve parentType fieldName laterArguments lowered).map
            liftResolverValue)
    cases hlower : lowerResolverValue? source with
    | none =>
        rfl
    | some lowered =>
        simp [base.resolve_argumentsEquivalent parentType fieldName
          firstArguments laterArguments lowered harguments]

theorem liftResolvers_resolve_liftResolverValue
    {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    : (liftResolvers base).resolve parentType fieldName arguments
        (liftResolverValue source)
      = (base.resolve parentType fieldName arguments source).map liftResolverValue := by
  simp [liftResolvers, lowerResolverValue?_liftResolverValue]

theorem runtimeObjectType?_liftResolverValue
    {ObjectRef : Type} (value : Execution.ResolverValue ObjectRef)
    : Execution.runtimeObjectType? (liftResolverValue value)
      = Execution.runtimeObjectType? value := by
  cases value <;> simp [liftResolverValue, Execution.runtimeObjectType?]

theorem doesFragmentTypeApplyBool_liftResolverValue
    {ObjectRef : Type} (schema : Schema) (parentType typeCondition : Name)
    (source : Execution.ResolverValue ObjectRef)
    : Execution.doesFragmentTypeApplyBool schema parentType
        (liftResolverValue source) typeCondition
      = Execution.doesFragmentTypeApplyBool schema parentType source typeCondition := by
  simp [Execution.doesFragmentTypeApplyBool,
    runtimeObjectType?_liftResolverValue]

mutual
  theorem collectSelection_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (variableValues : Execution.VariableValues)
      : ∀ (parentType : Name) (source : Execution.ResolverValue ObjectRef)
            (selection : Selection),
          Execution.collectSelection schema variableValues parentType
            (liftResolverValue source) selection
          = Execution.collectSelection schema variableValues parentType source selection
    | parentType, source,
      .field responseName fieldName arguments directives selectionSet => by
        simp [Execution.collectSelection]
    | parentType, source, .inlineFragment none directives selectionSet => by
        by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · simp [Execution.collectSelection, hallow,
            collectFields_liftResolverValue schema variableValues parentType
              source selectionSet]
        · have hallowFalse :
              Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
            cases h :
                Execution.selectionDirectivesAllowBool variableValues
                  directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hallowFalse]
    | parentType, source, .inlineFragment (some typeCondition) directives
        selectionSet => by
        by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · by_cases happly :
              Execution.doesFragmentTypeApplyBool schema parentType source
                typeCondition = true
          · have happlyLift :
                Execution.doesFragmentTypeApplyBool schema parentType
                  (liftResolverValue source) typeCondition = true := by
              simpa [doesFragmentTypeApplyBool_liftResolverValue] using happly
            simp [Execution.collectSelection, hallow, happly, happlyLift,
              collectFields_liftResolverValue schema variableValues parentType
                source selectionSet]
          · have happlyFalse :
                Execution.doesFragmentTypeApplyBool schema parentType source
                  typeCondition = false := by
              cases h :
                  Execution.doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · rfl
              · contradiction
            have happlyLiftFalse :
                Execution.doesFragmentTypeApplyBool schema parentType
                  (liftResolverValue source) typeCondition = false := by
              simpa [doesFragmentTypeApplyBool_liftResolverValue]
                using happlyFalse
            simp [Execution.collectSelection, hallow, happlyFalse,
              happlyLiftFalse]
        · have hallowFalse :
              Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
            cases h :
                Execution.selectionDirectivesAllowBool variableValues
                  directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hallowFalse]

  theorem collectFields_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (variableValues : Execution.VariableValues)
      : ∀ (parentType : Name) (source : Execution.ResolverValue ObjectRef)
            (selectionSet : List Selection),
          Execution.collectFields schema variableValues parentType
            (liftResolverValue source) selectionSet
          = Execution.collectFields schema variableValues parentType source selectionSet
    | parentType, source, [] => by
        simp [Execution.collectFields]
    | parentType, source, selection :: rest => by
        simp [Execution.collectFields,
          collectSelection_liftResolverValue schema variableValues parentType
            source selection,
          collectFields_liftResolverValue schema variableValues parentType
            source rest]
end

theorem collectSubfields_liftResolverValue
    {ObjectRef : Type} (schema : Schema)
    (variableValues : Execution.VariableValues)
    : ∀ (objectType : Name) (source : Execution.ResolverValue ObjectRef)
          (fields : List Execution.ExecutableField),
        Execution.collectSubfields schema variableValues objectType
          (liftResolverValue source) fields
        = Execution.collectSubfields schema variableValues objectType source fields
  | objectType, source, [] => by
      simp [Execution.collectSubfields]
  | objectType, source, field :: fields => by
      simp [Execution.collectSubfields,
        collectFields_liftResolverValue schema variableValues objectType
          source field.selectionSet,
        collectFields_liftResolverValue schema variableValues objectType
          source (Execution.mergedFieldSelectionSet fields)]

mutual
  theorem executeCollectedFields_liftResolvers
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
            (fields : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema (liftResolvers base)
            variableValues fuel (liftResolverValue source) fields
          = Execution.executeCollectedFields schema base variableValues fuel source fields
    | fuel, source, [] => by
        simp [Execution.executeCollectedFields]
    | fuel, source, (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          executeField_liftResolvers schema base variableValues fuel source
            responseName fields,
          executeCollectedFields_liftResolvers schema base variableValues fuel
            source rest]

  theorem executeField_liftResolvers
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
            (responseName : Name) (fields : List Execution.ExecutableField),
          Execution.executeField schema (liftResolvers base) variableValues fuel
            (liftResolverValue source) responseName fields
          = Execution.executeField schema base variableValues fuel source
              responseName fields
    | fuel, source, responseName, [] => by
        simp [Execution.executeField]
    | 0, source, responseName, field :: fields => by
        simp [Execution.executeField]
    | fuel + 1, source, responseName, field :: fields => by
        cases hlookup : schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, hlookup]
        | some fieldDefinition =>
            cases hresolve :
                base.resolve field.parentType field.fieldName field.arguments
                  source with
            | none =>
                simp [Execution.executeField, hlookup,
                  liftResolvers_resolve_liftResolverValue base
                    field.parentType field.fieldName field.arguments source,
                  hresolve]
            | some resolved =>
                simp [Execution.executeField, hlookup,
                  liftResolvers_resolve_liftResolverValue base
                    field.parentType field.fieldName field.arguments source,
                  hresolve,
                  completeValue_liftResolvers schema base variableValues fuel
                    fieldDefinition.outputType (field :: fields) resolved]

  theorem completeValue_liftResolvers
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
            (fields : List Execution.ExecutableField)
            (value : Execution.ResolverValue ObjectRef),
          Execution.completeValue schema (liftResolvers base) variableValues
            fuel fieldType fields (liftResolverValue value)
          = Execution.completeValue schema base variableValues fuel fieldType fields value
    | 0, fieldType, fields, value => by
        simp [Execution.completeValue, Execution.outOfFuel]
    | fuel + 1, .nonNull inner, fields, value => by
        simp [Execution.completeValue,
          completeValue_liftResolvers schema base variableValues (fuel + 1)
            inner fields value]
    | fuel + 1, .named typeName, fields, .null => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .named typeName, fields, .scalar value => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .named typeName, fields, .object runtimeType ref => by
        by_cases hinclude :
            schema.typeIncludesObjectBool typeName runtimeType = true
        · simp [liftResolverValue, Execution.completeValue, hinclude]
          have hcollect :
              Execution.collectFields schema variableValues runtimeType
                (Execution.ResolverValue.object runtimeType (some ref))
                (Execution.mergedFieldSelectionSet fields)
              =
              Execution.collectFields schema variableValues runtimeType
                (Execution.ResolverValue.object runtimeType ref)
                (Execution.mergedFieldSelectionSet fields) := by
            simpa [liftResolverValue] using
              collectFields_liftResolverValue schema variableValues
                runtimeType
                (Execution.ResolverValue.object runtimeType ref)
                (Execution.mergedFieldSelectionSet fields)
          rw [hcollect]
          have hexecute :
              Execution.executeCollectedFields schema (liftResolvers base)
                variableValues fuel
                (Execution.ResolverValue.object runtimeType (some ref))
                (Execution.collectFields schema variableValues runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (Execution.mergedFieldSelectionSet fields))
              =
              Execution.executeCollectedFields schema base variableValues fuel
                (Execution.ResolverValue.object runtimeType ref)
                (Execution.collectFields schema variableValues runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (Execution.mergedFieldSelectionSet fields)) := by
            simpa [liftResolverValue] using
              executeCollectedFields_liftResolvers schema base variableValues
                fuel (Execution.ResolverValue.object runtimeType ref)
                (Execution.collectFields schema variableValues runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (Execution.mergedFieldSelectionSet fields))
          rw [hexecute]
        · have hincludeFalse :
              schema.typeIncludesObjectBool typeName runtimeType = false := by
            cases h : schema.typeIncludesObjectBool typeName runtimeType
            · rfl
            · contradiction
          simp [liftResolverValue, Execution.completeValue, hincludeFalse]
    | fuel + 1, .named typeName, fields, .list values => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .null => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .scalar value => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .object runtimeType ref => by
        simp [liftResolverValue, Execution.completeValue]
    | fuel + 1, .list inner, fields, .list values => by
        simp [liftResolverValue, Execution.completeValue,
          completeValueList_liftResolvers schema base variableValues fuel inner
            fields values]

  theorem completeValueList_liftResolvers
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (itemType : TypeRef)
            (fields : List Execution.ExecutableField)
            (values : List (Execution.ResolverValue ObjectRef)),
          Execution.completeValueList schema (liftResolvers base)
            variableValues fuel itemType fields (values.map liftResolverValue)
          = Execution.completeValueList schema base variableValues fuel itemType
              fields values
    | fuel, itemType, fields, [] => by
        simp [Execution.completeValueList]
    | fuel, itemType, fields, value :: values => by
        simp [Execution.completeValueList,
          completeValue_liftResolvers schema base variableValues fuel itemType
            fields value,
          completeValueList_liftResolvers schema base variableValues fuel
            itemType fields values]
end

theorem executeSelectionSet_liftResolvers
    {ObjectRef : Type} (schema : Schema)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.executeSelectionSet schema (liftResolvers base) variableValues
        fuel parentType (liftResolverValue source) selectionSet
      = Execution.executeSelectionSet schema base variableValues fuel parentType
          source selectionSet := by
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
  rw [collectFields_liftResolverValue schema variableValues parentType source
    selectionSet]
  exact executeCollectedFields_liftResolvers schema base variableValues fuel
    source
    (Execution.collectFields schema variableValues parentType source
      selectionSet)

theorem executeSelectionSetAsResponse_liftResolvers
    {ObjectRef : Type} (schema : Schema)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.executeSelectionSetAsResponse schema (liftResolvers base)
        variableValues fuel parentType (liftResolverValue source) selectionSet
      = Execution.executeSelectionSetAsResponse schema base variableValues fuel
          parentType source selectionSet := by
  simp [Execution.executeSelectionSetAsResponse,
    executeSelectionSet_liftResolvers schema base variableValues fuel
      parentType source selectionSet]

def parentObjectFieldResolvers {ObjectRef : Type}
    (base : Execution.Resolvers ObjectRef)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    : Execution.Resolvers (Option ObjectRef) where
  resolve parentType fieldName arguments source :=
    match source with
    | .object _ none =>
        if parentType == targetParent && fieldName == targetField then
          some (.object runtimeType (some ref))
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

theorem parentObjectFieldResolvers_target
    {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    (arguments : List Argument)
    : (parentObjectFieldResolvers base targetParent targetField runtimeType ref).resolve
        targetParent targetField arguments (.object targetParent none)
      = some (.object runtimeType (some ref)) := by
  simp [parentObjectFieldResolvers]

theorem parentObjectFieldResolvers_resolve_liftResolverValue
    {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    : (parentObjectFieldResolvers base targetParent targetField runtimeType ref).resolve
        parentType fieldName arguments (liftResolverValue source)
      = (liftResolvers base).resolve parentType fieldName arguments
          (liftResolverValue source) := by
  cases source <;> simp [parentObjectFieldResolvers, liftResolverValue]

mutual
  theorem executeCollectedFields_parentObjectFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
            (fields : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema
            (parentObjectFieldResolvers base targetParent targetField runtimeType ref)
            variableValues fuel (liftResolverValue source) fields
          = Execution.executeCollectedFields schema (liftResolvers base)
              variableValues fuel (liftResolverValue source) fields
    | fuel, source, [] => by
        simp [Execution.executeCollectedFields]
    | fuel, source, (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          executeField_parentObjectFieldResolvers_liftResolverValue schema
            base variableValues targetParent targetField runtimeType ref fuel
            source responseName fields,
          executeCollectedFields_parentObjectFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref fuel source rest]

  theorem executeField_parentObjectFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      : ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
            (responseName : Name) (fields : List Execution.ExecutableField),
          Execution.executeField schema
            (parentObjectFieldResolvers base targetParent targetField runtimeType ref)
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
            have hresolveEq :=
              parentObjectFieldResolvers_resolve_liftResolverValue base
                targetParent targetField runtimeType ref field.parentType
                field.fieldName field.arguments source
            have hliftResolve :=
              liftResolvers_resolve_liftResolverValue base field.parentType
                field.fieldName field.arguments source
            cases hresolve :
                base.resolve field.parentType field.fieldName field.arguments
                  source with
            | none =>
                simp [Execution.executeField, hlookup, hresolveEq,
                  hliftResolve, hresolve]
            | some resolved =>
                simp [Execution.executeField, hlookup, hresolveEq,
                  hliftResolve, hresolve,
                  completeValue_parentObjectFieldResolvers_liftResolverValue
                    schema base variableValues targetParent targetField
                    runtimeType ref fuel fieldDefinition.outputType
                    (field :: fields) resolved]

  theorem completeValue_parentObjectFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
            (fields : List Execution.ExecutableField)
            (value : Execution.ResolverValue ObjectRef),
          Execution.completeValue schema
            (parentObjectFieldResolvers base targetParent targetField runtimeType ref)
            variableValues fuel fieldType fields (liftResolverValue value)
          = Execution.completeValue schema (liftResolvers base) variableValues
              fuel fieldType fields (liftResolverValue value)
    | 0, fieldType, fields, value => by
        simp [Execution.completeValue, Execution.outOfFuel]
    | fuel + 1, .nonNull inner, fields, value => by
        simp [Execution.completeValue,
          completeValue_parentObjectFieldResolvers_liftResolverValue schema
            base variableValues targetParent targetField runtimeType ref
            (fuel + 1) inner fields value]
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
                (parentObjectFieldResolvers base targetParent targetField
                  runtimeType ref)
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
              executeCollectedFields_parentObjectFieldResolvers_liftResolverValue
                schema base variableValues targetParent targetField
                runtimeType ref fuel
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
          completeValueList_parentObjectFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType ref
            fuel inner fields values]

  theorem completeValueList_parentObjectFieldResolvers_liftResolverValue
      {ObjectRef : Type} (schema : Schema)
      (base : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (targetParent targetField runtimeType : Name) (ref : ObjectRef)
      : ∀ (fuel : Nat) (itemType : TypeRef)
            (fields : List Execution.ExecutableField)
            (values : List (Execution.ResolverValue ObjectRef)),
          Execution.completeValueList schema
            (parentObjectFieldResolvers base targetParent targetField runtimeType ref)
            variableValues fuel itemType fields (values.map liftResolverValue)
          = Execution.completeValueList schema (liftResolvers base) variableValues
              fuel itemType fields (values.map liftResolverValue)
    | fuel, itemType, fields, [] => by
        simp [Execution.completeValueList]
    | fuel, itemType, fields, value :: values => by
        simp [Execution.completeValueList,
          completeValue_parentObjectFieldResolvers_liftResolverValue schema
            base variableValues targetParent targetField runtimeType ref fuel
            itemType fields value,
          completeValueList_parentObjectFieldResolvers_liftResolverValue
            schema base variableValues targetParent targetField runtimeType
            ref fuel itemType fields values]
end

theorem executeSelectionSetAsResponse_parentObjectFieldResolvers_liftResolverValue
    {ObjectRef : Type} (schema : Schema)
    (base : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent targetField runtimeType : Name) (ref : ObjectRef)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.executeSelectionSetAsResponse schema
        (parentObjectFieldResolvers base targetParent targetField runtimeType ref)
        variableValues fuel parentType (liftResolverValue source) selectionSet
      = Execution.executeSelectionSetAsResponse schema (liftResolvers base)
          variableValues fuel parentType (liftResolverValue source) selectionSet := by
  simp [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
    Execution.executeRootSelectionSet,
    executeCollectedFields_parentObjectFieldResolvers_liftResolverValue
      schema base variableValues targetParent targetField runtimeType ref fuel
      source
      (Execution.collectFields schema variableValues parentType
        (liftResolverValue source) selectionSet)]

end GroundTypeNormalization

end NormalForm

end GraphQL
