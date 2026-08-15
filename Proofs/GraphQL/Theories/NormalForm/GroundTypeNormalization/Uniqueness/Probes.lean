import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.OperationBridge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionKeys
import Proofs.GraphQL.Validation.FieldMerge

/-!
Resolver probes used by the semantic-separation part of uniqueness.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem argumentsEquivalent_trans {left middle right : List Argument}
    : Argument.argumentsEquivalent left middle
      -> Argument.argumentsEquivalent middle right
      -> Argument.argumentsEquivalent left right :=
  Execution.argumentsEquivalent_trans_forCoercion

def fieldFailureResolvers {ObjectRef : Type} (targetParent targetField : Name)
    : Execution.Resolvers ObjectRef where
  resolve parentType fieldName _arguments _source :=
    if parentType == targetParent && fieldName == targetField then
      none
    else
      Execution.Option.null
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

def schemaSuccessResolverValue (schema : Schema)
    : TypeRef -> Execution.ResolverValue PUnit
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        .object typeName PUnit.unit
      else
        .scalar "success"
  | .list _inner => .list []
  | .nonNull inner => schemaSuccessResolverValue schema inner

def schemaSuccessResolverValueWithRef {ObjectRef : Type}
    (schema : Schema) (objectRef : ObjectRef)
    : TypeRef -> Execution.ResolverValue ObjectRef
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        .object typeName objectRef
      else
        .scalar "success"
  | .list _inner => .list []
  | .nonNull inner =>
      schemaSuccessResolverValueWithRef schema objectRef inner

def schemaSuccessResolvers (schema : Schema) : Execution.Resolvers PUnit where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => none
    | some fieldDefinition =>
        some (schemaSuccessResolverValue schema fieldDefinition.outputType)
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

def schemaSuccessResolversWithRef {ObjectRef : Type}
    (schema : Schema) (objectRef : ObjectRef)
    : Execution.Resolvers ObjectRef where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => none
    | some fieldDefinition =>
        some
          (schemaSuccessResolverValueWithRef schema objectRef fieldDefinition.outputType)
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

def firstInlineFragmentTypeCondition? : List Selection -> Option Name
  | [] => none
  | Selection.inlineFragment (some typeCondition) _directives _selectionSet :: _rest =>
      some typeCondition
  | _selection :: rest => firstInlineFragmentTypeCondition? rest

def abstractRuntimeForField? (fieldName : Name) : List Selection -> Option Name
  | [] => none
  | Selection.field _responseName candidateFieldName _arguments
      _directives childSelectionSet
    :: rest =>
      if candidateFieldName == fieldName then
        match firstInlineFragmentTypeCondition? childSelectionSet with
        | some runtimeType => some runtimeType
        | none => abstractRuntimeForField? fieldName rest
      else
        abstractRuntimeForField? fieldName rest
  | _selection :: rest => abstractRuntimeForField? fieldName rest

def abstractRuntimeForFieldDeep? (schema : Schema) (targetParent targetField : Name)
    : Name -> List Selection -> Option Name
  | _currentParent, [] => none
  | currentParent,
    Selection.field _responseName candidateFieldName _arguments
      _directives childSelectionSet
    :: rest =>
      let current :=
        if currentParent == targetParent && candidateFieldName == targetField then
          firstInlineFragmentTypeCondition? childSelectionSet
        else
          none
      match current with
      | some runtimeType => some runtimeType
      | none =>
          match abstractRuntimeForFieldDeep? schema targetParent targetField
                  currentParent rest with
          | some runtimeType => some runtimeType
          | none =>
              match schema.lookupField currentParent candidateFieldName with
              | none => none
              | some fieldDefinition =>
                  abstractRuntimeForFieldDeep? schema targetParent targetField
                    fieldDefinition.outputType.namedType childSelectionSet
  | currentParent,
    Selection.inlineFragment none _directives childSelectionSet :: rest =>
      match abstractRuntimeForFieldDeep? schema targetParent targetField
              currentParent rest with
      | some runtimeType => some runtimeType
      | none =>
          abstractRuntimeForFieldDeep? schema targetParent targetField
            currentParent childSelectionSet
  | currentParent,
    Selection.inlineFragment (some typeCondition) _directives childSelectionSet :: rest =>
      match abstractRuntimeForFieldDeep? schema targetParent targetField
              currentParent rest with
      | some runtimeType => some runtimeType
      | none =>
          abstractRuntimeForFieldDeep? schema targetParent targetField
            typeCondition childSelectionSet
termination_by _currentParent selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

noncomputable def abstractRuntimeForFieldHeadDeep? (schema : Schema)
    (targetParent targetField : Name) (targetArguments : List Argument)
    : Name -> List Selection -> Option Name
  | _currentParent, [] => none
  | currentParent,
      Selection.field _responseName candidateFieldName arguments
        _directives childSelectionSet :: rest =>
      let current := by
        classical
        exact
          if currentParent = targetParent
              ∧ candidateFieldName = targetField
              ∧ Argument.argumentsEquivalent arguments targetArguments then
            firstInlineFragmentTypeCondition? childSelectionSet
          else
            none
      match current with
      | some runtimeType => some runtimeType
      | none =>
          match
            abstractRuntimeForFieldHeadDeep? schema targetParent targetField
              targetArguments currentParent rest with
          | some runtimeType => some runtimeType
          | none =>
              match schema.lookupField currentParent candidateFieldName with
              | none => none
              | some fieldDefinition =>
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments
                    fieldDefinition.outputType.namedType childSelectionSet
  | currentParent,
      Selection.inlineFragment none _directives childSelectionSet :: rest =>
      match
        abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments currentParent rest with
      | some runtimeType => some runtimeType
      | none =>
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent childSelectionSet
  | currentParent,
      Selection.inlineFragment (some typeCondition) _directives
        childSelectionSet :: rest =>
      match
        abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments currentParent rest with
      | some runtimeType => some runtimeType
      | none =>
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments typeCondition childSelectionSet
termination_by _currentParent selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
    (schema : Schema) (targetParent targetField : Name)
    {firstArguments laterArguments : List Argument}
    (hequivalent : Argument.argumentsEquivalent firstArguments laterArguments)
    : ∀ currentParent selectionSet,
        abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          firstArguments currentParent selectionSet
        = abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            laterArguments currentParent selectionSet
  | _currentParent, [] => by
      simp [abstractRuntimeForFieldHeadDeep?]
  | currentParent, selection :: rest => by
      cases selection with
      | field responseName candidateFieldName arguments directives childSelectionSet =>
          have hrest :
              abstractRuntimeForFieldHeadDeep? schema targetParent targetField
                firstArguments currentParent rest
              =
              abstractRuntimeForFieldHeadDeep? schema targetParent targetField
                laterArguments currentParent rest := by
            exact
              abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
                schema targetParent targetField hequivalent currentParent rest
          have hmatchIff :
              (currentParent = targetParent
                  ∧ candidateFieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments firstArguments)
                ↔
                (currentParent = targetParent
                  ∧ candidateFieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments laterArguments) := by
            constructor
            · intro h
              exact ⟨h.1, h.2.1,
                argumentsEquivalent_trans h.2.2 hequivalent⟩
            · intro h
              exact ⟨h.1, h.2.1,
                argumentsEquivalent_trans h.2.2
                  (FieldMerge.argumentsEquivalent_symm hequivalent)⟩
          by_cases hmatchFirst :
              currentParent = targetParent
                ∧ candidateFieldName = targetField
                ∧ Argument.argumentsEquivalent arguments firstArguments
          · have hmatchLater :
                currentParent = targetParent
                  ∧ candidateFieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments laterArguments :=
              hmatchIff.mp hmatchFirst
            have hcurrent : currentParent = targetParent := hmatchFirst.1
            have hcandidate : candidateFieldName = targetField :=
              hmatchFirst.2.1
            have hrestTarget :
                abstractRuntimeForFieldHeadDeep? schema targetParent
                  targetField firstArguments targetParent rest
                =
                abstractRuntimeForFieldHeadDeep? schema targetParent
                  targetField laterArguments targetParent rest := by
              simpa [hcurrent] using hrest
            cases hfirst :
                firstInlineFragmentTypeCondition? childSelectionSet with
            | none =>
                cases htail :
                    abstractRuntimeForFieldHeadDeep? schema targetParent
                      targetField laterArguments targetParent rest with
                | some runtimeType =>
                    simp [abstractRuntimeForFieldHeadDeep?, hmatchFirst,
                      hmatchLater, hfirst, hrestTarget, htail]
                | none =>
                    cases hlookup : schema.lookupField targetParent
                        targetField with
                    | none =>
                        simp [abstractRuntimeForFieldHeadDeep?, hmatchFirst,
                          hmatchLater, hfirst, hrestTarget, htail, hlookup]
                    | some fieldDefinition =>
                        have hchild :
                            abstractRuntimeForFieldHeadDeep? schema
                              targetParent targetField firstArguments
                              fieldDefinition.outputType.namedType
                              childSelectionSet
                            =
                            abstractRuntimeForFieldHeadDeep? schema
                              targetParent targetField laterArguments
                              fieldDefinition.outputType.namedType
                              childSelectionSet := by
                          exact
                            abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
                              schema targetParent targetField hequivalent
                              fieldDefinition.outputType.namedType
                              childSelectionSet
                        simp [abstractRuntimeForFieldHeadDeep?, hmatchFirst,
                          hmatchLater, hfirst, hrestTarget, htail, hlookup,
                          hchild]
            | some runtimeType =>
                simp [abstractRuntimeForFieldHeadDeep?, hmatchFirst,
                  hmatchLater, hfirst]
          · have hmatchLater :
                ¬ (currentParent = targetParent
                  ∧ candidateFieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments laterArguments) := by
              intro h
              exact hmatchFirst (hmatchIff.mpr h)
            cases htail :
                abstractRuntimeForFieldHeadDeep? schema targetParent
                  targetField laterArguments currentParent rest with
            | some runtimeType =>
                simp [abstractRuntimeForFieldHeadDeep?, hmatchFirst,
                  hmatchLater, hrest, htail]
            | none =>
                cases hlookup : schema.lookupField currentParent
                    candidateFieldName with
                | none =>
                    simp [abstractRuntimeForFieldHeadDeep?, hmatchFirst,
                      hmatchLater, hrest, htail, hlookup]
                | some fieldDefinition =>
                    have hchild :
                        abstractRuntimeForFieldHeadDeep? schema targetParent
                          targetField firstArguments
                          fieldDefinition.outputType.namedType
                          childSelectionSet
                        =
                        abstractRuntimeForFieldHeadDeep? schema targetParent
                          targetField laterArguments
                          fieldDefinition.outputType.namedType
                          childSelectionSet := by
                      exact
                        abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
                          schema targetParent targetField hequivalent
                          fieldDefinition.outputType.namedType
                          childSelectionSet
                    simp [abstractRuntimeForFieldHeadDeep?, hmatchFirst,
                      hmatchLater, hrest, htail, hlookup, hchild]
      | inlineFragment typeCondition directives childSelectionSet =>
          cases typeCondition with
          | none =>
              have hrest :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField firstArguments currentParent rest
                  =
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField laterArguments currentParent rest := by
                exact
                  abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
                    schema targetParent targetField hequivalent currentParent
                    rest
              have hchild :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField firstArguments currentParent childSelectionSet
                  =
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField laterArguments currentParent childSelectionSet := by
                exact
                  abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
                    schema targetParent targetField hequivalent currentParent
                    childSelectionSet
              cases htail :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField laterArguments currentParent rest with
              | some runtimeType =>
                  simp [abstractRuntimeForFieldHeadDeep?, hrest, htail]
              | none =>
                  simp [abstractRuntimeForFieldHeadDeep?, hrest, htail,
                    hchild]
          | some typeCondition =>
              have hrest :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField firstArguments currentParent rest
                  =
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField laterArguments currentParent rest := by
                exact
                  abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
                    schema targetParent targetField hequivalent currentParent
                    rest
              have hchild :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField firstArguments typeCondition childSelectionSet
                  =
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField laterArguments typeCondition childSelectionSet := by
                exact
                  abstractRuntimeForFieldHeadDeep?_eq_of_argumentsEquivalent
                    schema targetParent targetField hequivalent typeCondition
                    childSelectionSet
              cases htail :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField laterArguments currentParent rest with
              | some runtimeType =>
                  simp [abstractRuntimeForFieldHeadDeep?, hrest, htail]
              | none =>
                  simp [abstractRuntimeForFieldHeadDeep?, hrest, htail,
                    hchild]
termination_by _currentParent selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

def selectionSetSuccessResolverValue (schema : Schema)
    (rootSelectionSet : List Selection) (fieldName : Name)
    : TypeRef -> Execution.ResolverValue PUnit
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName PUnit.unit
        else
          match abstractRuntimeForField? fieldName rootSelectionSet with
          | some runtimeType => .object runtimeType PUnit.unit
          | none => .object typeName PUnit.unit
      else
        .scalar "success"
  | .list _inner => .list []
  | .nonNull inner =>
      selectionSetSuccessResolverValue schema rootSelectionSet fieldName inner

def deepSelectionSetSuccessResolverValue (schema : Schema)
    (rootSelectionSet : List Selection) (parentType fieldName : Name)
    : TypeRef -> Execution.ResolverValue PUnit
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName PUnit.unit
        else
          match abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet with
          | some runtimeType => .object runtimeType PUnit.unit
          | none => .object typeName PUnit.unit
      else
        .scalar "success"
  | .list _inner => .list []
  | .nonNull inner =>
      deepSelectionSetSuccessResolverValue schema rootSelectionSet parentType
        fieldName inner

def deepSelectionSetSuccessResolverValueWithRef {ObjectRef : Type}
    (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (parentType fieldName : Name)
    : TypeRef -> Execution.ResolverValue ObjectRef
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName objectRef
        else
          match abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet with
          | some runtimeType => .object runtimeType objectRef
          | none => .object typeName objectRef
      else
        .scalar "success"
  | .list _inner => .list []
  | .nonNull inner =>
      deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
        objectRef parentType fieldName inner

def deepSelectionSetProbeResolverValue (schema : Schema)
    (rootSelectionSet : List Selection) (parentType fieldName : Name)
    : TypeRef -> Execution.ResolverValue PUnit
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName PUnit.unit
        else
          match abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet with
          | some runtimeType => .object runtimeType PUnit.unit
          | none => .object typeName PUnit.unit
      else
        .scalar "success"
  | .list inner =>
      .list
        [deepSelectionSetProbeResolverValue schema rootSelectionSet
          parentType fieldName inner]
  | .nonNull inner =>
      deepSelectionSetProbeResolverValue schema rootSelectionSet parentType
        fieldName inner

def selectionSetSuccessResolvers (schema : Schema) (rootSelectionSet : List Selection)
    : Execution.Resolvers PUnit where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => none
    | some fieldDefinition =>
        some
          (selectionSetSuccessResolverValue schema rootSelectionSet fieldName
            fieldDefinition.outputType)
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

def deepSelectionSetSuccessResolvers (schema : Schema) (rootSelectionSet : List Selection)
    : Execution.Resolvers PUnit where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => none
    | some fieldDefinition =>
        some
          (deepSelectionSetSuccessResolverValue schema rootSelectionSet
            parentType fieldName fieldDefinition.outputType)
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

def deepSelectionSetSuccessResolversWithRef {ObjectRef : Type}
    (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef)
    : Execution.Resolvers ObjectRef where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => none
    | some fieldDefinition =>
        some
          (deepSelectionSetSuccessResolverValueWithRef schema
            rootSelectionSet objectRef parentType fieldName
            fieldDefinition.outputType)
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

def deepSelectionSetProbeResolvers (schema : Schema) (rootSelectionSet : List Selection)
    : Execution.Resolvers PUnit where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => none
    | some fieldDefinition =>
        some
          (deepSelectionSetProbeResolverValue schema rootSelectionSet
            parentType fieldName fieldDefinition.outputType)
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

theorem schemaSuccessResolvers_resolve_lookup
    (schema : Schema) (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue PUnit)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (schemaSuccessResolvers schema).resolve parentType fieldName arguments source
          = some (schemaSuccessResolverValue schema fieldDefinition.outputType) := by
  intro hlookup
  simp [schemaSuccessResolvers, hlookup]

theorem schemaSuccessResolversWithRef_resolve_lookup
    {ObjectRef : Type} (schema : Schema) (objectRef : ObjectRef)
    (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (schemaSuccessResolversWithRef schema objectRef).resolve parentType
            fieldName arguments source
          = some
              (schemaSuccessResolverValueWithRef schema objectRef
                fieldDefinition.outputType) := by
  intro hlookup
  simp [schemaSuccessResolversWithRef, hlookup]

theorem selectionSetSuccessResolvers_resolve_lookup
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue PUnit)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (selectionSetSuccessResolvers schema rootSelectionSet).resolve
            parentType fieldName arguments source
          = some
              (selectionSetSuccessResolverValue schema rootSelectionSet fieldName
                fieldDefinition.outputType) := by
  intro hlookup
  simp [selectionSetSuccessResolvers, hlookup]

theorem deepSelectionSetSuccessResolvers_resolve_lookup
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue PUnit)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (deepSelectionSetSuccessResolvers schema rootSelectionSet).resolve
            parentType fieldName arguments source
          = some
              (deepSelectionSetSuccessResolverValue schema rootSelectionSet
                parentType fieldName fieldDefinition.outputType) := by
  intro hlookup
  simp [deepSelectionSetSuccessResolvers, hlookup]

theorem deepSelectionSetSuccessResolversWithRef_resolve_lookup
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
            objectRef).resolve
            parentType fieldName arguments source
          = some
              (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
                objectRef parentType fieldName fieldDefinition.outputType) := by
  intro hlookup
  simp [deepSelectionSetSuccessResolversWithRef, hlookup]

theorem deepSelectionSetProbeResolvers_resolve_lookup
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue PUnit)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (deepSelectionSetProbeResolvers schema rootSelectionSet).resolve
            parentType fieldName arguments source
          = some
              (deepSelectionSetProbeResolverValue schema rootSelectionSet
                parentType fieldName fieldDefinition.outputType) := by
  intro hlookup
  simp [deepSelectionSetProbeResolvers, hlookup]

theorem deepSelectionSetSuccessResolverValueWithRef_named_object
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (parentType fieldName typeName : Name)
    : objectTypeNameBool schema typeName = true
      -> deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
            objectRef parentType fieldName (.named typeName)
          = .object typeName objectRef := by
  intro hobject
  have hcomposite :
      (TypeRef.named typeName).isCompositeBool schema = true := by
    unfold objectTypeNameBool at hobject
    unfold TypeRef.isCompositeBool TypeRef.namedType
    cases hlookup : schema.lookupType typeName with
    | none =>
        simp [hlookup] at hobject
    | some typeDefinition =>
        cases typeDefinition <;> simp [hlookup] at hobject ⊢
  simp [deepSelectionSetSuccessResolverValueWithRef, hcomposite, hobject]

theorem deepSelectionSetSuccessResolverValueWithRef_named_leaf
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (parentType fieldName typeName : Name)
    : (TypeRef.named typeName).isCompositeBool schema = false
      -> deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
            objectRef parentType fieldName (.named typeName)
          = .scalar "success" := by
  intro hleaf
  simp [deepSelectionSetSuccessResolverValueWithRef, hleaf]

theorem deepSelectionSetSuccessResolverValueWithRef_named_abstract
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (parentType fieldName typeName runtimeType : Name)
    : (TypeRef.named typeName).isCompositeBool schema = true
      -> objectTypeNameBool schema typeName = false
      -> abstractRuntimeForFieldDeep? schema parentType fieldName parentType
            rootSelectionSet
          = some runtimeType
      -> deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
            objectRef parentType fieldName (.named typeName)
          = .object runtimeType objectRef := by
  intro hcomposite hnonObject hruntime
  simp [deepSelectionSetSuccessResolverValueWithRef, hcomposite, hnonObject,
    hruntime]

theorem deepSelectionSetSuccessResolverValue_named_object
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName typeName : Name)
    : objectTypeNameBool schema typeName = true
      -> deepSelectionSetSuccessResolverValue schema rootSelectionSet parentType
            fieldName (.named typeName)
          = .object typeName PUnit.unit := by
  intro hobject
  simpa [deepSelectionSetSuccessResolverValue,
    deepSelectionSetSuccessResolverValueWithRef] using
    deepSelectionSetSuccessResolverValueWithRef_named_object schema
      rootSelectionSet PUnit.unit parentType fieldName typeName hobject

theorem deepSelectionSetSuccessResolverValue_named_leaf
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName typeName : Name)
    : (TypeRef.named typeName).isCompositeBool schema = false
      -> deepSelectionSetSuccessResolverValue schema rootSelectionSet parentType
            fieldName (.named typeName)
          = .scalar "success" := by
  intro hleaf
  simpa [deepSelectionSetSuccessResolverValue,
    deepSelectionSetSuccessResolverValueWithRef] using
    deepSelectionSetSuccessResolverValueWithRef_named_leaf schema
      rootSelectionSet PUnit.unit parentType fieldName typeName hleaf

theorem deepSelectionSetSuccessResolverValue_named_abstract
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName typeName runtimeType : Name)
    : (TypeRef.named typeName).isCompositeBool schema = true
      -> objectTypeNameBool schema typeName = false
      -> abstractRuntimeForFieldDeep? schema parentType fieldName parentType
            rootSelectionSet
          = some runtimeType
      -> deepSelectionSetSuccessResolverValue schema rootSelectionSet parentType
            fieldName (.named typeName)
          = .object runtimeType PUnit.unit := by
  intro hcomposite hnonObject hruntime
  simpa [deepSelectionSetSuccessResolverValue,
    deepSelectionSetSuccessResolverValueWithRef] using
    deepSelectionSetSuccessResolverValueWithRef_named_abstract schema
      rootSelectionSet PUnit.unit parentType fieldName typeName runtimeType
      hcomposite hnonObject hruntime

noncomputable def argumentClassScalarResolvers {ObjectRef : Type}
    (targetParent targetField : Name)
    (targetArguments : Execution.CoercedArguments)
    (matched missed : String)
    : Execution.Resolvers ObjectRef where
  resolve parentType fieldName arguments _source := by
    classical
    exact
      if parentType == targetParent then
        if fieldName == targetField then
          if Execution.CoercedArgument.argumentsEquivalent arguments
              targetArguments then
            Execution.Option.scalar matched
          else
            Execution.Option.scalar missed
        else
          Execution.Option.null
      else
        Execution.Option.null
  resolve_argumentsEquivalent := by
    classical
    intro parentType fieldName firstArguments laterArguments _source
      harguments
    have hiff :
        Execution.CoercedArgument.argumentsEquivalent firstArguments targetArguments
          ↔ Execution.CoercedArgument.argumentsEquivalent laterArguments
              targetArguments := by
      constructor
      · intro hfirst
        exact Execution.CoercedArgument.argumentsEquivalent_trans
          (Execution.CoercedArgument.argumentsEquivalent_symm harguments) hfirst
      · intro hlater
        exact Execution.CoercedArgument.argumentsEquivalent_trans harguments hlater
    by_cases hparent : parentType == targetParent
    · by_cases hfield : fieldName == targetField
      · by_cases hfirst :
          Execution.CoercedArgument.argumentsEquivalent firstArguments
            targetArguments
        · have hlater :
              Execution.CoercedArgument.argumentsEquivalent laterArguments
                targetArguments :=
            hiff.mp hfirst
          simp [hparent, hfield, hfirst, hlater]
        · have hlater :
              ¬ Execution.CoercedArgument.argumentsEquivalent laterArguments
                  targetArguments := by
            intro hlater
            exact hfirst (hiff.mpr hlater)
          simp [hparent, hfield, hfirst, hlater]
      · simp [hparent, hfield]
    · simp [hparent]

theorem argumentClassScalarResolvers_target
    {ObjectRef : Type} (targetParent targetField : Name)
    (targetArguments : Execution.CoercedArguments) (matched missed : String)
    (source : Execution.ResolverValue ObjectRef)
    : (argumentClassScalarResolvers targetParent targetField targetArguments
        matched missed).resolve
        targetParent targetField targetArguments source
      = Execution.Option.scalar matched := by
  classical
  simp [argumentClassScalarResolvers,
    Execution.CoercedArgument.argumentsEquivalent_refl targetArguments]

theorem argumentClassScalarResolvers_equivalent
    {ObjectRef : Type} (targetParent targetField : Name)
    (targetArguments arguments : Execution.CoercedArguments)
    (matched missed : String)
    (source : Execution.ResolverValue ObjectRef)
    : Execution.CoercedArgument.argumentsEquivalent arguments targetArguments
      -> (argumentClassScalarResolvers targetParent targetField targetArguments
            matched missed).resolve
            targetParent targetField arguments source
          = Execution.Option.scalar matched := by
  intro harguments
  classical
  simp [argumentClassScalarResolvers, harguments]

theorem argumentClassScalarResolvers_not_equivalent
    {ObjectRef : Type} (targetParent targetField : Name)
    (targetArguments arguments : Execution.CoercedArguments)
    (matched missed : String)
    (source : Execution.ResolverValue ObjectRef)
    : ¬ Execution.CoercedArgument.argumentsEquivalent arguments targetArguments
      -> (argumentClassScalarResolvers targetParent targetField targetArguments
            matched missed).resolve
            targetParent targetField arguments source
          = Execution.Option.scalar missed := by
  intro harguments
  classical
  simp [argumentClassScalarResolvers, harguments]

theorem argumentClassScalarResolvers_other_field
    {ObjectRef : Type} (targetParent targetField fieldName : Name)
    (targetArguments arguments : Execution.CoercedArguments)
    (matched missed : String)
    (source : Execution.ResolverValue ObjectRef)
    : (fieldName == targetField) = false
      -> (argumentClassScalarResolvers targetParent targetField targetArguments
            matched missed).resolve
            targetParent fieldName arguments source
          = Execution.Option.null := by
  intro hfield
  classical
  have hfieldNe : fieldName ≠ targetField := by
    intro heq
    subst fieldName
    simp at hfield
  simp [argumentClassScalarResolvers, hfieldNe]

def fieldScalarResolvers {ObjectRef : Type}
    (targetParent targetField : Name) (value : String)
    : Execution.Resolvers ObjectRef where
  resolve parentType fieldName _arguments _source :=
    if parentType == targetParent then
      if fieldName == targetField then
        Execution.Option.scalar value
      else
        Execution.Option.null
    else
      Execution.Option.null
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

theorem fieldScalarResolvers_target
    {ObjectRef : Type} (targetParent targetField : Name) (value : String)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue ObjectRef)
    : (fieldScalarResolvers targetParent targetField value).resolve
        targetParent targetField arguments source
      = Execution.Option.scalar value := by
  simp [fieldScalarResolvers]

def leafProbeResolverValue {ObjectRef : Type}
    : TypeRef -> String -> Execution.ResolverValue ObjectRef
  | .named _typeName, value => .scalar value
  | .list inner, value => .list [leafProbeResolverValue inner value]
  | .nonNull inner, value => leafProbeResolverValue inner value

def leafProbeResponseValue : TypeRef -> String -> Execution.ResponseValue
  | .named _typeName, value => .scalar value
  | .list inner, value => .list [leafProbeResponseValue inner value]
  | .nonNull inner, value => leafProbeResponseValue inner value

theorem leafProbeResponseValue_ne_null (outputType : TypeRef) (value : String)
    : leafProbeResponseValue outputType value ≠ .null := by
  induction outputType with
  | named _typeName =>
      simp [leafProbeResponseValue]
  | list inner _ih =>
      simp [leafProbeResponseValue]
  | nonNull inner ih =>
      simpa [leafProbeResponseValue] using ih

theorem leafProbeResponseValue_semanticEquivalent_eq
    (outputType : TypeRef) {left right : String}
    : Execution.ResponseValue.semanticEquivalent
        (leafProbeResponseValue outputType left)
        (leafProbeResponseValue outputType right)
      -> left = right := by
  intro hsemantic
  induction outputType with
  | named _typeName =>
      simpa [leafProbeResponseValue,
        Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical] using hsemantic
  | list inner ih =>
      apply ih
      simpa [leafProbeResponseValue,
        Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical,
        Execution.ResponseValue.canonicalList] using hsemantic
  | nonNull inner ih =>
      exact ih (by simpa [leafProbeResponseValue] using hsemantic)

theorem leafProbeResponseValue_not_semanticEquivalent_of_ne
    (outputType : TypeRef) {left right : String}
    : left ≠ right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (leafProbeResponseValue outputType left)
            (leafProbeResponseValue outputType right) := by
  intro hne hsemantic
  exact hne (leafProbeResponseValue_semanticEquivalent_eq outputType hsemantic)

theorem leafProbeResponseValue_not_semanticEquivalent_of_ne_any
    (leftType rightType : TypeRef) {left right : String}
    : left ≠ right
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (leafProbeResponseValue leftType left)
            (leafProbeResponseValue rightType right) := by
  intro hne hsemantic
  cases leftType with
  | named leftName =>
      cases rightType with
      | named _rightName =>
          exact hne (by
            simpa [leafProbeResponseValue,
              Execution.ResponseValue.semanticEquivalent,
              Execution.ResponseValue.canonical] using hsemantic)
      | list _rightInner =>
          simp [leafProbeResponseValue,
            Execution.ResponseValue.semanticEquivalent,
            Execution.ResponseValue.canonical,
            Execution.ResponseValue.canonicalList] at hsemantic
      | nonNull rightInner =>
          exact leafProbeResponseValue_not_semanticEquivalent_of_ne_any
            (.named leftName) rightInner hne hsemantic
  | list leftInner =>
      cases rightType with
      | named _rightName =>
          simp [leafProbeResponseValue,
            Execution.ResponseValue.semanticEquivalent,
            Execution.ResponseValue.canonical,
            Execution.ResponseValue.canonicalList] at hsemantic
      | list rightInner =>
          exact leafProbeResponseValue_not_semanticEquivalent_of_ne_any
            leftInner rightInner hne (by
              simpa [leafProbeResponseValue,
                Execution.ResponseValue.semanticEquivalent,
                Execution.ResponseValue.canonical,
                Execution.ResponseValue.canonicalList] using hsemantic)
      | nonNull rightInner =>
          exact leafProbeResponseValue_not_semanticEquivalent_of_ne_any
            (.list leftInner) rightInner hne hsemantic
  | nonNull leftInner =>
      exact leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftInner rightType hne hsemantic
termination_by sizeOf leftType + sizeOf rightType
decreasing_by
  all_goals
    simp_all
    try omega

def leafProbeFuel : TypeRef -> Nat
  | .named _typeName => 1
  | .list inner => leafProbeFuel inner + 1
  | .nonNull inner => leafProbeFuel inner

theorem leafProbeFuel_pos (outputType : TypeRef) : 0 < leafProbeFuel outputType := by
  induction outputType with
  | named _typeName =>
      simp [leafProbeFuel]
  | list inner _ih =>
      simp [leafProbeFuel]
  | nonNull inner ih =>
      simpa [leafProbeFuel] using ih

theorem completeValue_nonNull_ok_of_ne_null
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (inner : TypeRef)
    (fields : List Execution.ExecutableField)
    (resolved : Execution.ResolverValue ObjectRef)
    (responseValue : Execution.ResponseValue) (errors : Nat)
    : Execution.completeValue schema resolvers variableValues fuel inner fields resolved
        = .ok (responseValue, errors)
      -> responseValue ≠ .null
      -> Execution.completeValue schema resolvers variableValues fuel
            (.nonNull inner) fields resolved
          = .ok (responseValue, errors) := by
  intro hcomplete hnonNull
  cases fuel with
  | zero =>
      simp [Execution.completeValue, Execution.outOfFuel] at hcomplete
  | succ fuel =>
      cases hresponse : responseValue <;>
        simp [Execution.completeValue, hcomplete, hresponse,
          Execution.nonNullCompletion] at hnonNull ⊢

theorem completeValue_leafProbe
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    : ∀ (outputType : TypeRef) (fields : List Execution.ExecutableField) (value : String),
        (TypeRef.named outputType.namedType).isCompositeBool schema = false
        -> Execution.completeValue schema resolvers variableValues
              (leafProbeFuel outputType) outputType fields
              (leafProbeResolverValue outputType value)
            = .ok (leafProbeResponseValue outputType value, 0)
  | .named typeName, fields, value, hleaf => by
      simpa [leafProbeFuel, leafProbeResolverValue, leafProbeResponseValue,
        TypeRef.namedType, Execution.completeValue, hleaf]
  | .list inner, fields, value, hleaf => by
      have hinner :
          Execution.completeValue schema resolvers variableValues
            (leafProbeFuel inner) inner fields
            (leafProbeResolverValue inner value)
            =
          .ok (leafProbeResponseValue inner value, 0) :=
        completeValue_leafProbe schema resolvers variableValues inner fields
          value (by simpa [TypeRef.namedType] using hleaf)
      simp [leafProbeFuel, leafProbeResolverValue, leafProbeResponseValue,
        Execution.completeValue, Execution.completeValueList, hinner,
        Execution.Result.combine, Execution.catchBubbleAsNull]
  | .nonNull inner, fields, value, hleaf => by
      have hinner :
          Execution.completeValue schema resolvers variableValues
            (leafProbeFuel inner) inner fields
            (leafProbeResolverValue inner value)
            =
          .ok (leafProbeResponseValue inner value, 0) :=
        completeValue_leafProbe schema resolvers variableValues inner fields
          value (by simpa [TypeRef.namedType] using hleaf)
      have hnonNull :
          leafProbeResponseValue inner value ≠ .null :=
        leafProbeResponseValue_ne_null inner value
      cases hfuel : leafProbeFuel inner with
      | zero =>
          have hpos := leafProbeFuel_pos inner
          rw [hfuel] at hpos
          exact False.elim (Nat.not_lt_zero 0 hpos)
      | succ fuel =>
          rw [hfuel] at hinner
          cases hresponse : leafProbeResponseValue inner value <;>
            simp [leafProbeFuel, leafProbeResolverValue,
              leafProbeResponseValue, hfuel, Execution.completeValue, hinner,
              hresponse, Execution.nonNullCompletion] at hnonNull ⊢

theorem completeValue_leafProbe_of_fuel_ge
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    : ∀ (outputType : TypeRef) (fields : List Execution.ExecutableField)
        (value : String) (fuel : Nat),
        leafProbeFuel outputType ≤ fuel
        -> (TypeRef.named outputType.namedType).isCompositeBool schema = false
        -> Execution.completeValue schema resolvers variableValues
              fuel outputType fields
              (leafProbeResolverValue outputType value)
            = .ok (leafProbeResponseValue outputType value, 0)
  | .named typeName, fields, value, fuel, hfuel, hleaf => by
      cases fuel with
      | zero =>
          simp [leafProbeFuel] at hfuel
      | succ fuel' =>
          have hleafNamed :
              (TypeRef.named typeName).isCompositeBool schema = false := by
            simpa [TypeRef.namedType] using hleaf
          simp [leafProbeResolverValue, leafProbeResponseValue,
            Execution.completeValue, hleafNamed]
  | .list inner, fields, value, fuel, hfuel, hleaf => by
      cases fuel with
      | zero =>
          simp [leafProbeFuel] at hfuel
      | succ fuel' =>
          have hinnerFuel :
              leafProbeFuel inner ≤ fuel' := by
            simp [leafProbeFuel] at hfuel
            omega
          have hinner :
              Execution.completeValue schema resolvers variableValues
                fuel' inner fields
                (leafProbeResolverValue inner value)
                =
              .ok (leafProbeResponseValue inner value, 0) :=
            completeValue_leafProbe_of_fuel_ge schema resolvers variableValues
              inner fields value fuel' hinnerFuel
              (by simpa [TypeRef.namedType] using hleaf)
          simp [leafProbeResolverValue, leafProbeResponseValue,
            Execution.completeValue, Execution.completeValueList, hinner,
            Execution.Result.combine, Execution.catchBubbleAsNull]
  | .nonNull inner, fields, value, fuel, hfuel, hleaf => by
      have hinnerFuel :
          leafProbeFuel inner ≤ fuel := by
        simpa [leafProbeFuel] using hfuel
      have hinner :
          Execution.completeValue schema resolvers variableValues
            fuel inner fields
            (leafProbeResolverValue inner value)
            =
          .ok (leafProbeResponseValue inner value, 0) :=
        completeValue_leafProbe_of_fuel_ge schema resolvers variableValues
          inner fields value fuel hinnerFuel
          (by simpa [TypeRef.namedType] using hleaf)
      have hnonNull :
          leafProbeResponseValue inner value ≠ .null :=
        leafProbeResponseValue_ne_null inner value
      cases fuel with
      | zero =>
          have hpos := leafProbeFuel_pos inner
          omega
      | succ fuel' =>
          cases hresponse : leafProbeResponseValue inner value <;>
            simp [leafProbeResolverValue, leafProbeResponseValue,
              Execution.completeValue, hinner, hresponse,
              Execution.nonNullCompletion] at hnonNull ⊢

theorem completeValue_deepSelectionSetSuccessWithRef_leaf_ok
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType fieldName : Name)
    (fields : List Execution.ExecutableField)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = false
        -> ∃ responseValue errors,
            Execution.completeValue schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues (fuel + leafProbeFuel outputType) outputType fields
                (deepSelectionSetSuccessResolverValueWithRef schema
                  rootSelectionSet objectRef parentType fieldName outputType)
              = .ok (responseValue, errors)
            ∧ responseValue ≠ .null
  | .named typeName, hleaf => by
      refine ⟨.scalar "success", 0, ?_, ?_⟩
      · have hvalue :
            deepSelectionSetSuccessResolverValueWithRef schema
                rootSelectionSet objectRef parentType fieldName
                (.named typeName)
              =
              .scalar "success" :=
          deepSelectionSetSuccessResolverValueWithRef_named_leaf schema
            rootSelectionSet objectRef parentType fieldName typeName hleaf
        have hleafNamed :
            (TypeRef.named typeName).isCompositeBool schema = false := by
          simpa [TypeRef.namedType] using hleaf
        simp [leafProbeFuel, hvalue, Execution.completeValue, hleafNamed]
      · simp
  | .list inner, _hleaf => by
      refine ⟨.list [], 0, ?_, ?_⟩
      · have hfuel :
            fuel + (leafProbeFuel inner + 1) =
              fuel + leafProbeFuel inner + 1 := by
          omega
        simp [leafProbeFuel, deepSelectionSetSuccessResolverValueWithRef,
          hfuel, Execution.completeValue, Execution.completeValueList,
          Execution.catchBubbleAsNull]
      · simp
  | .nonNull inner, hleaf => by
      rcases
          completeValue_deepSelectionSetSuccessWithRef_leaf_ok schema
            rootSelectionSet objectRef variableValues fuel parentType
            fieldName fields inner (by simpa [TypeRef.namedType] using hleaf)
        with
        ⟨innerResponseValue, innerErrors, hinnerComplete,
          hinnerNonNull⟩
      refine ⟨innerResponseValue, innerErrors, ?_, hinnerNonNull⟩
      have hnonNullComplete :
          Execution.completeValue schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + leafProbeFuel inner) (.nonNull inner)
            fields
            (deepSelectionSetSuccessResolverValueWithRef schema
              rootSelectionSet objectRef parentType fieldName inner)
          =
          .ok (innerResponseValue, innerErrors) :=
        completeValue_nonNull_ok_of_ne_null schema
          (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
            objectRef)
          variableValues (fuel + leafProbeFuel inner) inner fields
          (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
            objectRef parentType fieldName inner)
          innerResponseValue innerErrors hinnerComplete hinnerNonNull
      simpa [leafProbeFuel, deepSelectionSetSuccessResolverValueWithRef] using
        hnonNullComplete

theorem completeValue_deepSelectionSetSuccessWithRef_object_of_executeCollectedFields_ok
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType fieldName : Name)
    (fields : List Execution.ExecutableField)
    (responseFields : List (Name × Execution.ResponseValue))
    (errors : Nat)
    : ∀ outputType,
        objectTypeNameBool schema outputType.namedType = true
        -> Execution.executeCollectedFields schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues fuel
              (.object outputType.namedType objectRef)
              (Execution.collectSubfields schema variableValues outputType.namedType
                (.object outputType.namedType objectRef) fields)
            = .ok (responseFields, errors)
        -> ∃ responseValue completeErrors,
            Execution.completeValue schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues (fuel + leafProbeFuel outputType) outputType fields
                (deepSelectionSetSuccessResolverValueWithRef schema
                  rootSelectionSet objectRef parentType fieldName outputType)
              = .ok (responseValue, completeErrors)
            ∧ responseValue ≠ .null
  | .named typeName, hobject, hfields => by
      have hinclude :
          schema.typeIncludesObjectBool typeName typeName = true :=
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
      have hvalue :
          deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
              objectRef parentType fieldName (.named typeName)
            =
            .object typeName objectRef :=
        deepSelectionSetSuccessResolverValueWithRef_named_object schema
          rootSelectionSet objectRef parentType fieldName typeName hobject
      refine ⟨.object responseFields, errors, ?_, ?_⟩
      · have hfieldsMerged :
            Execution.executeCollectedFields schema
              (deepSelectionSetSuccessResolversWithRef schema
                rootSelectionSet objectRef)
              variableValues fuel (.object typeName objectRef)
              (Execution.collectFields schema variableValues typeName
                (.object typeName objectRef)
                (Execution.mergedFieldSelectionSet fields))
            =
            .ok (responseFields, errors) := by
          simpa [TypeRef.namedType,
            collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hfields
        simp [leafProbeFuel, hvalue, Execution.completeValue, hinclude,
          hfieldsMerged, Execution.catchBubbleAsNull]
      · simp
  | .list inner, _hobject, _hfields => by
      refine ⟨.list [], 0, ?_, ?_⟩
      · have hfuel :
            fuel + (leafProbeFuel inner + 1) =
              fuel + leafProbeFuel inner + 1 := by
          omega
        simp [leafProbeFuel, deepSelectionSetSuccessResolverValueWithRef,
          hfuel, Execution.completeValue, Execution.completeValueList,
          Execution.catchBubbleAsNull]
      · simp
  | .nonNull inner, hobject, hfields => by
      rcases
          completeValue_deepSelectionSetSuccessWithRef_object_of_executeCollectedFields_ok
            schema rootSelectionSet objectRef variableValues fuel parentType
            fieldName fields responseFields errors inner
            (by simpa [TypeRef.namedType] using hobject)
            (by simpa [TypeRef.namedType] using hfields)
        with
        ⟨innerResponseValue, innerErrors, hinnerComplete,
          hinnerNonNull⟩
      refine ⟨innerResponseValue, innerErrors, ?_, hinnerNonNull⟩
      have hnonNullComplete :
          Execution.completeValue schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + leafProbeFuel inner) (.nonNull inner)
            fields
            (deepSelectionSetSuccessResolverValueWithRef schema
              rootSelectionSet objectRef parentType fieldName inner)
          =
          .ok (innerResponseValue, innerErrors) :=
        completeValue_nonNull_ok_of_ne_null schema
          (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
            objectRef)
          variableValues (fuel + leafProbeFuel inner) inner fields
          (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
            objectRef parentType fieldName inner)
          innerResponseValue innerErrors hinnerComplete hinnerNonNull
      simpa [leafProbeFuel, deepSelectionSetSuccessResolverValueWithRef] using
        hnonNullComplete

theorem completeValue_deepSelectionSetSuccessWithRef_abstract_of_executeCollectedFields_ok
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType fieldName runtimeType : Name) (fields : List Execution.ExecutableField)
    (responseFields : List (Name × Execution.ResponseValue)) (errors : Nat)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = true
        -> objectTypeNameBool schema outputType.namedType = false
        -> abstractRuntimeForFieldDeep? schema parentType fieldName parentType
              rootSelectionSet
            = some runtimeType
        -> schema.typeIncludesObjectBool outputType.namedType runtimeType = true
        -> Execution.executeCollectedFields schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues fuel
              (.object runtimeType objectRef)
              (Execution.collectSubfields schema variableValues runtimeType
                (.object runtimeType objectRef) fields)
            = .ok (responseFields, errors)
        -> ∃ responseValue completeErrors,
            Execution.completeValue schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues (fuel + leafProbeFuel outputType) outputType fields
                (deepSelectionSetSuccessResolverValueWithRef schema
                  rootSelectionSet objectRef parentType fieldName outputType)
              = .ok (responseValue, completeErrors)
            ∧ responseValue ≠ .null
  | .named typeName, hcomposite, hnonObject, hruntime, hinclude,
      hfields => by
      have hvalue :
          deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
              objectRef parentType fieldName (.named typeName)
            =
            .object runtimeType objectRef :=
        deepSelectionSetSuccessResolverValueWithRef_named_abstract schema
          rootSelectionSet objectRef parentType fieldName typeName
          runtimeType hcomposite hnonObject hruntime
      refine ⟨.object responseFields, errors, ?_, ?_⟩
      · have hincludeNamed :
            schema.typeIncludesObjectBool typeName runtimeType = true := by
          simpa [TypeRef.namedType] using hinclude
        have hfieldsMerged :
            Execution.executeCollectedFields schema
              (deepSelectionSetSuccessResolversWithRef schema
                rootSelectionSet objectRef)
              variableValues fuel (.object runtimeType objectRef)
              (Execution.collectFields schema variableValues runtimeType
                (.object runtimeType objectRef)
                (Execution.mergedFieldSelectionSet fields))
            =
            .ok (responseFields, errors) := by
          simpa [collectSubfields_eq_collectFields_mergedFieldSelectionSet]
            using hfields
        simp [leafProbeFuel, hvalue, Execution.completeValue, hincludeNamed,
          hfieldsMerged, Execution.catchBubbleAsNull]
      · simp
  | .list inner, _hcomposite, _hnonObject, _hruntime, _hinclude,
      _hfields => by
      refine ⟨.list [], 0, ?_, ?_⟩
      · have hfuel :
            fuel + (leafProbeFuel inner + 1) =
              fuel + leafProbeFuel inner + 1 := by
          omega
        simp [leafProbeFuel, deepSelectionSetSuccessResolverValueWithRef,
          hfuel, Execution.completeValue, Execution.completeValueList,
          Execution.catchBubbleAsNull]
      · simp
  | .nonNull inner, hcomposite, hnonObject, hruntime, hinclude,
      hfields => by
      rcases
          completeValue_deepSelectionSetSuccessWithRef_abstract_of_executeCollectedFields_ok
            schema rootSelectionSet objectRef variableValues fuel parentType
            fieldName runtimeType fields responseFields errors inner
            (by simpa [TypeRef.namedType] using hcomposite)
            (by simpa [TypeRef.namedType] using hnonObject)
            hruntime
            (by simpa [TypeRef.namedType] using hinclude)
            hfields
        with
        ⟨innerResponseValue, innerErrors, hinnerComplete,
          hinnerNonNull⟩
      refine ⟨innerResponseValue, innerErrors, ?_, hinnerNonNull⟩
      have hnonNullComplete :
          Execution.completeValue schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + leafProbeFuel inner) (.nonNull inner)
            fields
            (deepSelectionSetSuccessResolverValueWithRef schema
              rootSelectionSet objectRef parentType fieldName inner)
          =
          .ok (innerResponseValue, innerErrors) :=
        completeValue_nonNull_ok_of_ne_null schema
          (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
            objectRef)
          variableValues (fuel + leafProbeFuel inner) inner fields
          (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
            objectRef parentType fieldName inner)
          innerResponseValue innerErrors hinnerComplete hinnerNonNull
      simpa [leafProbeFuel, deepSelectionSetSuccessResolverValueWithRef] using
        hnonNullComplete

theorem executeField_deepSelectionSetSuccessWithRef_of_lookup
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> Execution.executeField schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
            variableValues (fuel + 1) source responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (Execution.completeValue schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues fuel fieldDefinition.outputType
                [{
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := childSelectionSet
                }]
                (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
                  objectRef parentType fieldName fieldDefinition.outputType)) := by
  intro hlookup hcoerce
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoerce with
    ⟨coercedArguments, hcoercionResult⟩
  have hresolve :
      Execution.coerceAndResolveFieldValue schema
        (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
        variableValues fieldDefinition parentType fieldName arguments source
        =
      some
        (deepSelectionSetSuccessResolverValueWithRef schema rootSelectionSet
          objectRef parentType fieldName fieldDefinition.outputType) :=
    by
      simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
        hcoercionResult]
      exact deepSelectionSetSuccessResolversWithRef_resolve_lookup schema
        rootSelectionSet objectRef parentType fieldName
        coercedArguments source fieldDefinition hlookup
  simp [Execution.executeField, hlookup, hresolve]

theorem executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ ∃ responseFields errors,
                Execution.executeCollectedFields schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    objectRef)
                  variableValues fuel
                  (.object fieldDefinition.outputType.namedType objectRef)
                  (Execution.collectSubfields schema variableValues
                    fieldDefinition.outputType.namedType
                    (.object fieldDefinition.outputType.namedType objectRef)
                    [{
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := childSelectionSet
                    }])
                = .ok (responseFields, errors))
          ∨ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
            = false
          ∨ ∃ runtimeType responseFields errors,
              (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet
                = some runtimeType
              ∧ schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType runtimeType
                = true
              ∧ Execution.executeCollectedFields schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    objectRef)
                  variableValues fuel (.object runtimeType objectRef)
                  (Execution.collectSubfields schema variableValues runtimeType
                    (.object runtimeType objectRef)
                    [{
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := childSelectionSet
                    }])
                = .ok (responseFields, errors))
      -> ∃ responseValue errors,
          Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              source responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], errors)
          ∧ responseValue ≠ .null := by
  intro hlookup hcoerce hkind
  have hfield :=
    executeField_deepSelectionSetSuccessWithRef_of_lookup schema
      rootSelectionSet objectRef variableValues
      (fuel + leafProbeFuel fieldDefinition.outputType) source responseName
      parentType fieldName arguments childSelectionSet fieldDefinition
      hlookup hcoerce
  rcases hkind with hobjectKind | hleafOrAbstract
  · rcases hobjectKind with ⟨hobject, responseFields, childErrors,
      hfields⟩
    rcases
        completeValue_deepSelectionSetSuccessWithRef_object_of_executeCollectedFields_ok
          schema rootSelectionSet objectRef variableValues fuel parentType
          fieldName
          [{
            parentType := parentType
            responseName := responseName
            fieldName := fieldName
            arguments := arguments
            selectionSet := childSelectionSet
          }]
          responseFields childErrors fieldDefinition.outputType hobject
          hfields
      with
      ⟨responseValue, errors, hcomplete, hnonNull⟩
    refine ⟨responseValue, errors, ?_, hnonNull⟩
    simpa [hcomplete, Execution.singleFieldResult] using hfield
  · rcases hleafOrAbstract with hleaf | habstract
    · rcases
          completeValue_deepSelectionSetSuccessWithRef_leaf_ok schema
            rootSelectionSet objectRef variableValues fuel parentType
            fieldName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
            fieldDefinition.outputType hleaf
        with
        ⟨responseValue, errors, hcomplete, hnonNull⟩
      refine ⟨responseValue, errors, ?_, hnonNull⟩
      simpa [hcomplete, Execution.singleFieldResult] using hfield
    · rcases habstract with
        ⟨runtimeType, responseFields, childErrors, hcomposite, hnonObject,
          hruntime, hinclude, hfields⟩
      rcases
          completeValue_deepSelectionSetSuccessWithRef_abstract_of_executeCollectedFields_ok
            schema rootSelectionSet objectRef variableValues fuel parentType
            fieldName runtimeType
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
            responseFields childErrors fieldDefinition.outputType hcomposite
            hnonObject hruntime hinclude hfields
        with
        ⟨responseValue, errors, hcomplete, hnonNull⟩
      refine ⟨responseValue, errors, ?_, hnonNull⟩
      simpa [hcomplete, Execution.singleFieldResult] using hfield

theorem
    executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_child_executeSelectionSet_ok
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ ∃ responseFields errors,
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    objectRef)
                  variableValues fuel fieldDefinition.outputType.namedType
                  (.object fieldDefinition.outputType.namedType objectRef)
                  childSelectionSet
                = .ok (responseFields, errors))
          ∨ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
            = false
          ∨ ∃ runtimeType responseFields errors,
              (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet
                = some runtimeType
              ∧ schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType runtimeType
                = true
              ∧ Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    objectRef)
                  variableValues fuel runtimeType
                  (.object runtimeType objectRef) childSelectionSet
                = .ok (responseFields, errors))
      -> ∃ responseValue errors,
          Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              source responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], errors)
          ∧ responseValue ≠ .null := by
  intro hlookup hcoerce hkind
  have hcollectedKind :
      (objectTypeNameBool schema fieldDefinition.outputType.namedType = true
          ∧ ∃ responseFields errors,
            Execution.executeCollectedFields schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                objectRef)
              variableValues fuel
              (.object fieldDefinition.outputType.namedType objectRef)
              (Execution.collectSubfields schema variableValues
                fieldDefinition.outputType.namedType
                (.object fieldDefinition.outputType.namedType objectRef)
                [{
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := childSelectionSet
                }])
            =
            .ok (responseFields, errors))
        ∨ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
            schema = false
        ∨ ∃ runtimeType responseFields errors,
            (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
              schema = true
            ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType =
              false
            ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
              parentType rootSelectionSet = some runtimeType
            ∧ schema.typeIncludesObjectBool
              fieldDefinition.outputType.namedType runtimeType = true
            ∧ Execution.executeCollectedFields schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                objectRef)
              variableValues fuel (.object runtimeType objectRef)
              (Execution.collectSubfields schema variableValues runtimeType
                (.object runtimeType objectRef)
                [{
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := childSelectionSet
                }])
            =
            .ok (responseFields, errors) := by
    rcases hkind with hobject | hleafOrAbstract
    · rcases hobject with ⟨hobject, responseFields, errors,
        hselectionSet⟩
      refine Or.inl ⟨hobject, responseFields, errors, ?_⟩
      simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        collectSubfields_eq_collectFields_mergedFieldSelectionSet,
        Execution.mergedFieldSelectionSet] using hselectionSet
    · rcases hleafOrAbstract with hleaf | habstract
      · exact Or.inr (Or.inl hleaf)
      · rcases habstract with
          ⟨runtimeType, responseFields, errors, hcomposite, hnonObject,
            hruntime, hinclude, hselectionSet⟩
        refine
          Or.inr
            (Or.inr
              ⟨runtimeType, responseFields, errors, hcomposite, hnonObject,
                hruntime, hinclude, ?_⟩)
        simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
          collectSubfields_eq_collectFields_mergedFieldSelectionSet,
          Execution.mergedFieldSelectionSet] using hselectionSet
  exact
    executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok schema
      rootSelectionSet objectRef variableValues fuel source responseName
      parentType fieldName arguments childSelectionSet fieldDefinition
      hlookup hcoerce hcollectedKind

theorem
    executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_child_executeSelectionSet_ok_fuel_ge
    {ObjectRef : Type} (schema : Schema) (rootSelectionSet : List Selection)
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ ∃ responseFields errors,
                Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    objectRef)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  fieldDefinition.outputType.namedType
                  (.object fieldDefinition.outputType.namedType objectRef)
                  childSelectionSet
                = .ok (responseFields, errors))
          ∨ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
            = false
          ∨ ∃ runtimeType responseFields errors,
              (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet
                = some runtimeType
              ∧ schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType runtimeType
                = true
              ∧ Execution.executeSelectionSet schema
                  (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                    objectRef)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType (.object runtimeType objectRef) childSelectionSet
                = .ok (responseFields, errors))
      -> ∃ responseValue errors,
          Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues (fuel + 1) source responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], errors)
          ∧ responseValue ≠ .null := by
  intro hlookup hcoerce hfuel hkind
  rcases
      executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_child_executeSelectionSet_ok
        schema rootSelectionSet objectRef variableValues
        (fuel - leafProbeFuel fieldDefinition.outputType) source
        responseName parentType fieldName arguments childSelectionSet
        fieldDefinition hlookup hcoerce hkind
    with
    ⟨responseValue, errors, hexecute, hnonNull⟩
  refine ⟨responseValue, errors, ?_, hnonNull⟩
  have hfuelEq :
      fuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      fuel + 1 := by
    omega
  simpa [hfuelEq] using hexecute

def deepFieldSelectionSetExecutionReadyWithRef
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType _responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : Prop :=
  (Execution.coerceArgumentValues schema variableValues
      fieldDefinition.arguments arguments).isSuccess
    = true
  ∧ ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
        ∧ ∃ responseFields errors,
            Execution.executeSelectionSet schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues fuel fieldDefinition.outputType.namedType
              (.object fieldDefinition.outputType.namedType objectRef)
              childSelectionSet
            = .ok (responseFields, errors))
      ∨ (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
        = false
      ∨ ∃ runtimeType responseFields errors,
          (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
            = true
          ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
          ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
              parentType rootSelectionSet
            = some runtimeType
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true
          ∧ Execution.executeSelectionSet schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues fuel runtimeType
              (.object runtimeType objectRef) childSelectionSet
            = .ok (responseFields, errors))

theorem executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> deepFieldSelectionSetExecutionReadyWithRef schema rootSelectionSet
          objectRef variableValues
          (fuel - leafProbeFuel fieldDefinition.outputType)
          parentType responseName fieldName arguments childSelectionSet
          fieldDefinition
      -> ∃ responseValue errors,
          Execution.executeField schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues (fuel + 1) source responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], errors)
          ∧ responseValue ≠ .null := by
  intro hlookup hfuel hready
  rcases hready with ⟨hcoerce, hready⟩
  exact
    executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_child_executeSelectionSet_ok_fuel_ge
      schema rootSelectionSet objectRef variableValues fuel source
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition hlookup hcoerce hfuel
      (by
        simpa [deepFieldSelectionSetExecutionReadyWithRef] using hready)

theorem executeSelectionSet_deepSelectionSetSuccessWithRef_deepFieldReady
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    : ∀ selectionSet,
        selectionSetDirectiveFree selectionSet
        -> selectionSetNormal schema parentType selectionSet
        -> objectTypeNameBool schema parentType = true
        -> (∃ runtimeType ref,
              source = Execution.ResolverValue.object runtimeType ref
              ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
        -> (∀ responseName fieldName arguments directives childSelectionSet,
              Selection.field responseName fieldName arguments directives
                  childSelectionSet
                ∈ selectionSet
              -> ∃ fieldDefinition,
                  schema.lookupField parentType fieldName = some fieldDefinition
                  ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
                  ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                      rootSelectionSet objectRef variableValues
                      (fuel - leafProbeFuel fieldDefinition.outputType)
                      parentType responseName fieldName arguments childSelectionSet
                      fieldDefinition)
        -> ∃ responseFields errors,
            Execution.executeSelectionSet schema
                (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
                  objectRef)
                variableValues (fuel + 1) parentType source selectionSet
              = .ok (responseFields, errors)
            ∧ responseFields.map Prod.fst = selectionSet.filterMap Selection.responseName?
  | [], _hfree, _hnormal, _hobject, _hsource, _hready => by
      refine ⟨[], 0, ?_, ?_⟩
      · simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
          Execution.collectFields, Execution.executeCollectedFields]
      · simp
  | selection :: rest, hfree, hnormal, hobject, hsource, hready => by
      have hallFields :
          selectionsAllFields (selection :: rest) :=
        selectionSetNormal_allFields_of_object hnormal hobject
      have hselectionField :
          Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField
      | field responseName fieldName arguments directives childSelectionSet =>
      have hdirectives : directives = [] :=
        (selectionSetDirectiveFree_head hfree).1
      subst directives
      rcases hready responseName fieldName arguments [] childSelectionSet
          (by simp) with
        ⟨fieldDefinition, hlookup, hfuel, hfieldReady⟩
      rcases
          executeSelectionSet_deepSelectionSetSuccessWithRef_deepFieldReady
            schema rootSelectionSet objectRef variableValues fuel parentType
            source rest (selectionSetDirectiveFree_tail hfree)
            (selectionSetNormal_tail hnormal) hobject hsource
            (by
              intro tailResponseName tailFieldName tailArguments
                tailDirectives tailChildSelectionSet htailMem
              exact hready tailResponseName tailFieldName tailArguments
                tailDirectives tailChildSelectionSet
                (List.mem_cons_of_mem
                  (Selection.field responseName fieldName arguments []
                    childSelectionSet) htailMem)) with
        ⟨tailFields, tailErrors, htailExecute, htailNames⟩
      rcases
          executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
            schema rootSelectionSet objectRef variableValues fuel source
            responseName parentType fieldName arguments childSelectionSet
            fieldDefinition hlookup hfuel hfieldReady with
        ⟨headValue, headErrors, hheadExecute, _hheadNonNull⟩
      have htailCollected :
          Execution.executeCollectedFields schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
              objectRef)
            variableValues (fuel + 1) source
            (Execution.collectFields schema variableValues parentType source
              rest)
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
            parentType := parentType
            responseName := responseName
            fieldName := fieldName
            arguments := arguments
            selectionSet := childSelectionSet
          }])
            :: Execution.collectFields schema variableValues parentType source
              rest :=
        ExecutionKeys.collectFields_normal_object_field_head schema
          variableValues parentType source responseName fieldName arguments
          childSelectionSet rest hfree hnormal hobject
      refine
        ⟨(responseName, headValue) :: tailFields,
          headErrors + tailErrors, ?_, ?_⟩
      · simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
          hcollect, Execution.executeCollectedFields, hheadExecute,
          htailCollected, Execution.Result.combine]
      · simp [Selection.responseName?, htailNames]

theorem deepFieldSelectionSetExecutionReadyWithRef_leaf
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments).isSuccess
        = true
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> deepFieldSelectionSetExecutionReadyWithRef schema rootSelectionSet
          objectRef variableValues fuel parentType responseName fieldName
          arguments childSelectionSet fieldDefinition := by
  intro hcoerce hleaf
  exact ⟨hcoerce, Or.inr (Or.inl hleaf)⟩

theorem deepFieldSelectionSetExecutionReadyWithRef_object_of_child_deepFieldReady
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments).isSuccess
        = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> selectionSetDirectiveFree childSelectionSet
      -> selectionSetNormal schema fieldDefinition.outputType.namedType childSelectionSet
      -> (∀ childResponseName childFieldName childArguments childDirectives
            grandChildSelectionSet,
            Selection.field childResponseName childFieldName childArguments
                childDirectives grandChildSelectionSet
              ∈ childSelectionSet
            -> ∃ childFieldDefinition,
                schema.lookupField fieldDefinition.outputType.namedType childFieldName
                  = some childFieldDefinition
                ∧ leafProbeFuel childFieldDefinition.outputType ≤ fuel
                ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                    rootSelectionSet objectRef variableValues
                    (fuel - leafProbeFuel childFieldDefinition.outputType)
                    fieldDefinition.outputType.namedType childResponseName
                    childFieldName childArguments grandChildSelectionSet
                    childFieldDefinition)
      -> deepFieldSelectionSetExecutionReadyWithRef schema rootSelectionSet
          objectRef variableValues (fuel + 1) parentType responseName fieldName
          arguments childSelectionSet fieldDefinition := by
  intro hcoerce hobject hchildFree hchildNormal hchildReady
  have hsource :
      ∃ runtimeType ref,
        (Execution.ResolverValue.object
            fieldDefinition.outputType.namedType objectRef :
          Execution.ResolverValue ObjectRef)
          = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool
            fieldDefinition.outputType.namedType runtimeType = true := by
    exact ⟨
      fieldDefinition.outputType.namedType,
      objectRef,
      rfl,
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
    ⟩
  rcases
      executeSelectionSet_deepSelectionSetSuccessWithRef_deepFieldReady
        schema rootSelectionSet objectRef variableValues fuel
        fieldDefinition.outputType.namedType
        (Execution.ResolverValue.object
          fieldDefinition.outputType.namedType objectRef)
        childSelectionSet hchildFree hchildNormal hobject hsource
        hchildReady with
    ⟨responseFields, errors, hexecute, _hnames⟩
  exact ⟨hcoerce, Or.inl ⟨hobject, responseFields, errors, hexecute⟩⟩

theorem deepFieldSelectionSetExecutionReadyWithRef_abstract_of_execute
    {ObjectRef : Type} (schema : Schema)
    (rootSelectionSet : List Selection) (objectRef : ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (responseFields : List (Name × Execution.ResponseValue))
    (errors : Nat)
    : (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments).isSuccess
        = true
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema parentType fieldName parentType
            rootSelectionSet
          = some runtimeType
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeSelectionSet schema
            (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
            variableValues fuel runtimeType (.object runtimeType objectRef)
            childSelectionSet
          = .ok (responseFields, errors)
      -> deepFieldSelectionSetExecutionReadyWithRef schema rootSelectionSet
          objectRef variableValues fuel parentType responseName fieldName
          arguments childSelectionSet fieldDefinition := by
  intro hcoerce hcomposite hnonObject hruntime hinclude hexecute
  exact ⟨
    hcoerce,
    Or.inr
      (Or.inr
        ⟨
          runtimeType,
          responseFields,
          errors,
          hcomposite,
          hnonObject,
          hruntime,
          hinclude,
          hexecute
        ⟩)
  ⟩

theorem deepFieldSelectionSetExecutionReadyWithRef_composite_execute
    {ObjectRef : Type} {schema : Schema} {rootSelectionSet : List Selection}
    {objectRef : ObjectRef}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : deepFieldSelectionSetExecutionReadyWithRef schema rootSelectionSet
        objectRef variableValues fuel parentType responseName fieldName
        arguments childSelectionSet fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ runtimeType responseFields errors,
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true
          ∧ Execution.executeSelectionSet schema
              (deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef)
              variableValues fuel runtimeType
              (.object runtimeType objectRef) childSelectionSet
            = .ok (responseFields, errors) := by
  intro hready hcomposite
  rcases hready with ⟨_hcoerce, hready⟩
  rcases hready with hobject | hleafOrAbstract
  · rcases hobject with ⟨hobject, responseFields, errors, hexecute⟩
    exact ⟨
      fieldDefinition.outputType.namedType,
      responseFields,
      errors,
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject,
      hexecute
    ⟩
  · rcases hleafOrAbstract with hleaf | habstract
    · rw [hcomposite] at hleaf
      cases hleaf
    · rcases habstract with
        ⟨runtimeType, responseFields, errors, _habstract, _hnonObject,
          _hruntime, hinclude, hexecute⟩
      exact ⟨runtimeType, responseFields, errors, hinclude, hexecute⟩

def schemaLeafProbeResolvers {ObjectRef : Type} (schema : Schema) (value : String)
    : Execution.Resolvers ObjectRef where
  resolve parentType fieldName _arguments _source :=
    match schema.lookupField parentType fieldName with
    | none => Execution.Option.null
    | some fieldDefinition =>
        some (leafProbeResolverValue fieldDefinition.outputType value)
  resolve_argumentsEquivalent := by
    intro _parentType _fieldName _firstArguments _laterArguments _source
      _harguments
    rfl

theorem schemaLeafProbeResolvers_resolve_lookup
    {ObjectRef : Type} (schema : Schema) (value : String)
    (parentType fieldName : Name) (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (schemaLeafProbeResolvers schema value).resolve parentType fieldName
            arguments source
          = some (leafProbeResolverValue fieldDefinition.outputType value) := by
  intro hlookup
  simp [schemaLeafProbeResolvers, hlookup]

noncomputable def argumentClassLeafProbeValue
    (targetParent targetField : Name)
    (targetArguments : Execution.CoercedArguments)
    (matched missed fallback : String)
    (parentType fieldName : Name) (arguments : Execution.CoercedArguments)
    : String := by
  classical
  exact
    if parentType == targetParent then
      if fieldName == targetField then
        if Execution.CoercedArgument.argumentsEquivalent arguments
            targetArguments then
          matched
        else
          missed
      else
        fallback
    else
      fallback

theorem argumentClassLeafProbeValue_target_equivalent
    (targetParent targetField : Name)
    (targetArguments arguments : Execution.CoercedArguments)
    (matched missed fallback : String)
    : Execution.CoercedArgument.argumentsEquivalent arguments targetArguments
      -> argumentClassLeafProbeValue targetParent targetField targetArguments
            matched missed fallback targetParent targetField arguments
          = matched := by
  intro harguments
  classical
  simp [argumentClassLeafProbeValue, harguments]

theorem argumentClassLeafProbeValue_target_not_equivalent
    (targetParent targetField : Name)
    (targetArguments arguments : Execution.CoercedArguments)
    (matched missed fallback : String)
    : ¬ Execution.CoercedArgument.argumentsEquivalent arguments targetArguments
      -> argumentClassLeafProbeValue targetParent targetField targetArguments
            matched missed fallback targetParent targetField arguments
          = missed := by
  intro harguments
  classical
  simp [argumentClassLeafProbeValue, harguments]

theorem argumentClassLeafProbeValue_other_field
    (targetParent targetField fieldName : Name)
    (targetArguments arguments : Execution.CoercedArguments)
    (matched missed fallback : String)
    : (fieldName == targetField) = false
      -> argumentClassLeafProbeValue targetParent targetField targetArguments
            matched missed fallback targetParent fieldName arguments
          = fallback := by
  intro hfield
  classical
  have hfieldNe : fieldName ≠ targetField := by
    intro heq
    subst fieldName
    simp at hfield
  simp [argumentClassLeafProbeValue, hfieldNe]

noncomputable def schemaArgumentClassLeafProbeResolvers {ObjectRef : Type}
    (schema : Schema) (targetParent targetField : Name)
    (targetArguments : Execution.CoercedArguments)
    (matched missed fallback : String)
    : Execution.Resolvers ObjectRef where
  resolve parentType fieldName arguments _source := by
    classical
    exact
      match schema.lookupField parentType fieldName with
      | none => Execution.Option.null
      | some fieldDefinition =>
          some
            (leafProbeResolverValue fieldDefinition.outputType
              (argumentClassLeafProbeValue targetParent targetField
                targetArguments matched missed fallback parentType fieldName
                arguments))
  resolve_argumentsEquivalent := by
    classical
    intro parentType fieldName firstArguments laterArguments _source
      harguments
    have hiff :
        Execution.CoercedArgument.argumentsEquivalent firstArguments targetArguments
          ↔ Execution.CoercedArgument.argumentsEquivalent laterArguments
              targetArguments := by
      constructor
      · intro hfirst
        exact Execution.CoercedArgument.argumentsEquivalent_trans
          (Execution.CoercedArgument.argumentsEquivalent_symm harguments) hfirst
      · intro hlater
        exact Execution.CoercedArgument.argumentsEquivalent_trans harguments hlater
    cases hlookup : schema.lookupField parentType fieldName with
    | none =>
        simp
    | some fieldDefinition =>
        by_cases hparent : parentType == targetParent
        · by_cases hfield : fieldName == targetField
          · by_cases hfirst :
              Execution.CoercedArgument.argumentsEquivalent firstArguments
                targetArguments
            · have hlater :
                  Execution.CoercedArgument.argumentsEquivalent laterArguments
                    targetArguments :=
                hiff.mp hfirst
              simp [argumentClassLeafProbeValue, hparent, hfield, hfirst,
                hlater]
            · have hlater :
                  ¬ Execution.CoercedArgument.argumentsEquivalent laterArguments
                      targetArguments := by
                intro hlater
                exact hfirst (hiff.mpr hlater)
              simp [argumentClassLeafProbeValue, hparent, hfield, hfirst,
                hlater]
          · simp [argumentClassLeafProbeValue, hparent, hfield]
        · simp [argumentClassLeafProbeValue, hparent]

theorem schemaArgumentClassLeafProbeResolvers_resolve_lookup
    {ObjectRef : Type} (schema : Schema) (targetParent targetField : Name)
    (targetArguments : Execution.CoercedArguments) (matched missed fallback : String)
    (parentType fieldName : Name) (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (schemaArgumentClassLeafProbeResolvers schema targetParent targetField
            targetArguments matched missed fallback).resolve
            parentType fieldName arguments source
          = some
              (leafProbeResolverValue fieldDefinition.outputType
                (argumentClassLeafProbeValue targetParent targetField
                  targetArguments matched missed fallback parentType fieldName
                  arguments)) := by
  intro hlookup
  simp [schemaArgumentClassLeafProbeResolvers, hlookup]

theorem executeField_leafProbe_singleton_of_resolve_fuel_ge
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (value : String)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> Execution.coerceAndResolveFieldValue schema resolvers variableValues
            fieldDefinition parentType fieldName arguments source
          = some (leafProbeResolverValue fieldDefinition.outputType value)
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema resolvers variableValues (fuel + 1) source
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := selectionSet
            }]
          = .ok
              (
                [(responseName, leafProbeResponseValue fieldDefinition.outputType value)],
                0
              ) := by
  intro hlookup hresolve hfuel hleaf
  have hcomplete :
      Execution.completeValue schema resolvers variableValues fuel
        fieldDefinition.outputType
        [{
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := arguments
          selectionSet := selectionSet
        }]
        (leafProbeResolverValue (ObjectRef := ObjectRef)
          fieldDefinition.outputType value)
        =
      .ok (leafProbeResponseValue fieldDefinition.outputType value, 0) :=
    completeValue_leafProbe_of_fuel_ge schema resolvers variableValues
      fieldDefinition.outputType
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := selectionSet
      }]
      value fuel hfuel hleaf
  simp [Execution.executeField, hlookup, hresolve, hcomplete,
    Execution.singleFieldResult]

theorem executeField_schemaLeafProbe_singleton_of_fuel_ge
    {ObjectRef : Type} (schema : Schema)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (value : String)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (schemaLeafProbeResolvers (ObjectRef := ObjectRef) schema value)
            variableValues (fuel + 1) source responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := selectionSet
            }]
          = .ok
              (
                [(responseName, leafProbeResponseValue fieldDefinition.outputType value)],
                0
              ) := by
  intro hlookup hcoerce hfuel hleaf
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoerce with
    ⟨coercedArguments, hcoercionResult⟩
  have hresolve :
      Execution.coerceAndResolveFieldValue schema
        (schemaLeafProbeResolvers (ObjectRef := ObjectRef) schema value)
        variableValues fieldDefinition parentType fieldName arguments source
        =
      some (leafProbeResolverValue (ObjectRef := ObjectRef)
        fieldDefinition.outputType value) :=
    by
      simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
        hcoercionResult]
      exact schemaLeafProbeResolvers_resolve_lookup schema value parentType
        fieldName coercedArguments source fieldDefinition hlookup
  exact
    executeField_leafProbe_singleton_of_resolve_fuel_ge schema
      (schemaLeafProbeResolvers (ObjectRef := ObjectRef) schema value)
      variableValues fuel source responseName parentType fieldName arguments
      selectionSet fieldDefinition value hlookup hresolve hfuel hleaf

theorem executeField_named_object_of_resolve
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (definitionName returnType : Name)
    (definitionArguments : List InputValueDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : schema.lookupField parentType fieldName
        = some
            {
              name := definitionName
              outputType := .named returnType
              arguments := definitionArguments
            }
      -> schema.typeIncludesObjectBool returnType runtimeType = true
      -> Execution.coerceAndResolveFieldValue schema resolvers variableValues
            {
              name := definitionName,
              outputType := .named returnType,
              arguments := definitionArguments
            }
            parentType fieldName arguments source
          = some (.object runtimeType ref)
      -> Execution.executeField schema resolvers variableValues (fuel + 2)
            source responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  (Execution.executeSelectionSetAsResponse schema resolvers
                    variableValues fuel runtimeType (.object runtimeType ref)
                    childSelectionSet).data
                )],
                (Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  fuel runtimeType (.object runtimeType ref) childSelectionSet).errors
              ) := by
  intro hlookup hinclude hresolve
  cases hchild
        : Execution.executeCollectedFields schema resolvers variableValues fuel
            (Execution.ResolverValue.object runtimeType ref)
            (Execution.collectFields schema variableValues runtimeType
              (Execution.ResolverValue.object runtimeType ref)
              childSelectionSet) with
  | error errors =>
      simp [Execution.executeField, hlookup, hresolve,
        Execution.completeValue, hinclude,
        Execution.catchBubbleAsNull, Execution.singleFieldResult,
        Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        Execution.collectSubfields, Execution.mergeExecutableGroups, hchild]
  | ok result =>
      rcases result with ⟨fields, errors⟩
      simp [Execution.executeField, hlookup, hresolve,
        Execution.completeValue, hinclude,
        Execution.catchBubbleAsNull, Execution.singleFieldResult,
        Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        Execution.collectSubfields, Execution.mergeExecutableGroups, hchild]

theorem executeSelectionSetAsResponse_singleton_named_object_of_resolve
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType responseName fieldName : Name)
    (arguments : List Argument) (definitionName returnType : Name)
    (definitionArguments : List InputValueDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    (source : Execution.ResolverValue ObjectRef)
    (childSelectionSet : List Selection)
    : schema.lookupField parentType fieldName
        = some
            {
              name := definitionName
              outputType := .named returnType
              arguments := definitionArguments
            }
      -> schema.typeIncludesObjectBool returnType runtimeType = true
      -> Execution.coerceAndResolveFieldValue schema resolvers variableValues
            {
              name := definitionName,
              outputType := .named returnType,
              arguments := definitionArguments
            }
            parentType fieldName arguments source
          = some (.object runtimeType ref)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues
            (fuel + 2) parentType source
            [Selection.field responseName fieldName arguments [] childSelectionSet]
          = {
            data :=
              .object
                [(
                  responseName,
                  (Execution.executeSelectionSetAsResponse schema resolvers
                    variableValues fuel runtimeType (.object runtimeType ref)
                    childSelectionSet).data
                )]
            errors :=
              (Execution.executeSelectionSetAsResponse schema resolvers variableValues
                fuel runtimeType (.object runtimeType ref) childSelectionSet).errors
          } := by
  intro hlookup hinclude hresolve
  have hfield :
      Execution.executeField schema resolvers variableValues (fuel + 2)
        source responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := childSelectionSet
        }]
      =
      .ok
        ([(responseName,
          (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            runtimeType (.object runtimeType ref) childSelectionSet).data)],
          (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            runtimeType (.object runtimeType ref) childSelectionSet).errors) :=
    executeField_named_object_of_resolve schema resolvers variableValues fuel
      source responseName parentType fieldName arguments definitionName
      returnType definitionArguments runtimeType ref childSelectionSet
      hlookup hinclude hresolve
  simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
    Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool,
    Execution.mergeExecutableGroups, Execution.executeCollectedFields,
    hfield, Execution.Result.combine]

def selectionSetDeepProbeFuel (schema : Schema) (parentType : Name)
    : List Selection -> Nat
  | [] => 1
  | Selection.field _responseName fieldName _arguments _directives childSelectionSet
    :: rest =>
      match schema.lookupField parentType fieldName with
      | none => selectionSetDeepProbeFuel schema parentType rest
      | some fieldDefinition =>
          max
            (leafProbeFuel fieldDefinition.outputType
              + selectionSetDeepProbeFuel schema
                  fieldDefinition.outputType.namedType childSelectionSet
              + 1)
            (selectionSetDeepProbeFuel schema parentType rest)
  | Selection.inlineFragment (some typeCondition) _directives childSelectionSet :: rest =>
      max (selectionSetDeepProbeFuel schema typeCondition childSelectionSet)
        (selectionSetDeepProbeFuel schema parentType rest)
  | Selection.inlineFragment none _directives childSelectionSet :: rest =>
      max (selectionSetDeepProbeFuel schema parentType childSelectionSet)
        (selectionSetDeepProbeFuel schema parentType rest)
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    try
      simp [SelectionSet.size, Selection.size]
      omega

theorem selectionSetDeepProbeFuel_field_mem (schema : Schema) (parentType : Name)
    : ∀ selectionSet responseName fieldName arguments directives childSelectionSet
        fieldDefinition,
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> schema.lookupField parentType fieldName = some fieldDefinition
        -> leafProbeFuel fieldDefinition.outputType
              + selectionSetDeepProbeFuel schema
                  fieldDefinition.outputType.namedType childSelectionSet
              + 1
            ≤ selectionSetDeepProbeFuel schema parentType selectionSet
  | [], _responseName, _fieldName, _arguments, _directives,
      _childSelectionSet, _fieldDefinition, hmem, _hlookup => by
      simp at hmem
  | Selection.field headResponseName headFieldName headArguments headDirectives
      headChildSelectionSet :: rest,
      responseName, fieldName, arguments, directives, childSelectionSet,
      fieldDefinition, hmem, hlookup => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simp [selectionSetDeepProbeFuel, hlookup]
        omega
      · cases hheadLookup : schema.lookupField parentType headFieldName with
        | none =>
            simp [selectionSetDeepProbeFuel, hheadLookup]
            exact
              selectionSetDeepProbeFuel_field_mem schema parentType rest
                responseName fieldName arguments directives childSelectionSet
                fieldDefinition htail hlookup
        | some headFieldDefinition =>
            have htailFuel :
                leafProbeFuel fieldDefinition.outputType
                  + selectionSetDeepProbeFuel schema
                    fieldDefinition.outputType.namedType childSelectionSet
                  + 1
                  ≤ selectionSetDeepProbeFuel schema parentType rest :=
              selectionSetDeepProbeFuel_field_mem schema parentType rest
                responseName fieldName arguments directives childSelectionSet
                fieldDefinition htail hlookup
            simp [selectionSetDeepProbeFuel, hheadLookup]
            omega
  | Selection.inlineFragment typeCondition headDirectives headChildSelectionSet
      :: rest,
      responseName, fieldName, arguments, directives, childSelectionSet,
      fieldDefinition, hmem, hlookup => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · simp at hhead
      · cases typeCondition with
        | none =>
            have htailFuel :
                leafProbeFuel fieldDefinition.outputType
                  + selectionSetDeepProbeFuel schema
                    fieldDefinition.outputType.namedType childSelectionSet
                  + 1
                  ≤ selectionSetDeepProbeFuel schema parentType rest :=
              selectionSetDeepProbeFuel_field_mem schema parentType rest
                responseName fieldName arguments directives childSelectionSet
                fieldDefinition htail hlookup
            simp [selectionSetDeepProbeFuel]
            exact Nat.le_trans htailFuel (Nat.le_max_right _ _)
        | some typeCondition =>
            have htailFuel :
                leafProbeFuel fieldDefinition.outputType
                  + selectionSetDeepProbeFuel schema
                    fieldDefinition.outputType.namedType childSelectionSet
                  + 1
                  ≤ selectionSetDeepProbeFuel schema parentType rest :=
              selectionSetDeepProbeFuel_field_mem schema parentType rest
                responseName fieldName arguments directives childSelectionSet
                fieldDefinition htail hlookup
            simp [selectionSetDeepProbeFuel]
            exact Nat.le_trans htailFuel (Nat.le_max_right _ _)

theorem selectionSetDeepProbeFuel_inlineFragment_some_mem
    (schema : Schema) (parentType : Name)
    : ∀ selectionSet typeCondition directives childSelectionSet,
        Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
        -> selectionSetDeepProbeFuel schema typeCondition childSelectionSet
            ≤ selectionSetDeepProbeFuel schema parentType selectionSet
  | [], _typeCondition, _directives, _childSelectionSet, hmem => by
      simp at hmem
  | Selection.field headResponseName headFieldName headArguments headDirectives
      headChildSelectionSet :: rest,
      typeCondition, directives, childSelectionSet, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · simp at hhead
      · cases hheadLookup : schema.lookupField parentType headFieldName with
        | none =>
            simp [selectionSetDeepProbeFuel, hheadLookup]
            exact
              selectionSetDeepProbeFuel_inlineFragment_some_mem schema
                parentType rest typeCondition directives childSelectionSet
                htail
        | some headFieldDefinition =>
            have htailFuel :
                selectionSetDeepProbeFuel schema typeCondition childSelectionSet
                  ≤ selectionSetDeepProbeFuel schema parentType rest :=
              selectionSetDeepProbeFuel_inlineFragment_some_mem schema
                parentType rest typeCondition directives childSelectionSet
                htail
            simp [selectionSetDeepProbeFuel, hheadLookup]
            exact Nat.le_trans htailFuel (Nat.le_max_right _ _)
  | Selection.inlineFragment headTypeCondition headDirectives
      headChildSelectionSet :: rest,
      typeCondition, directives, childSelectionSet, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simpa [selectionSetDeepProbeFuel] using
          (Nat.le_max_left
            (selectionSetDeepProbeFuel schema typeCondition
              headChildSelectionSet)
            (selectionSetDeepProbeFuel schema parentType rest))
      · cases headTypeCondition with
        | none =>
            have htailFuel :
                selectionSetDeepProbeFuel schema typeCondition childSelectionSet
                  ≤ selectionSetDeepProbeFuel schema parentType rest :=
              selectionSetDeepProbeFuel_inlineFragment_some_mem schema
                parentType rest typeCondition directives childSelectionSet
                htail
            simp [selectionSetDeepProbeFuel]
            exact Nat.le_trans htailFuel (Nat.le_max_right _ _)
        | some headTypeCondition =>
            have htailFuel :
                selectionSetDeepProbeFuel schema typeCondition childSelectionSet
                  ≤ selectionSetDeepProbeFuel schema parentType rest :=
              selectionSetDeepProbeFuel_inlineFragment_some_mem schema
                parentType rest typeCondition directives childSelectionSet
                htail
            simp [selectionSetDeepProbeFuel]
            exact Nat.le_trans htailFuel (Nat.le_max_right _ _)

theorem selectionSetDeepProbeFuel_pos (schema : Schema) (parentType : Name)
    : ∀ selectionSet, 0 < selectionSetDeepProbeFuel schema parentType selectionSet
  | [] => by
      simp [selectionSetDeepProbeFuel]
  | Selection.field _responseName fieldName _arguments _directives
      childSelectionSet :: rest => by
      cases hlookup : schema.lookupField parentType fieldName with
      | none =>
          simpa [selectionSetDeepProbeFuel, hlookup] using
            selectionSetDeepProbeFuel_pos schema parentType rest
      | some fieldDefinition =>
          have hrest := selectionSetDeepProbeFuel_pos schema parentType rest
          simp [selectionSetDeepProbeFuel, hlookup]
          exact Nat.lt_of_lt_of_le hrest (Nat.le_max_right _ _)
  | Selection.inlineFragment (some typeCondition) _directives
      childSelectionSet :: rest => by
      have hrest := selectionSetDeepProbeFuel_pos schema parentType rest
      simp [selectionSetDeepProbeFuel]
      exact Nat.lt_of_lt_of_le hrest (Nat.le_max_right _ _)
  | Selection.inlineFragment none _directives childSelectionSet :: rest => by
      have hrest := selectionSetDeepProbeFuel_pos schema parentType rest
      simp [selectionSetDeepProbeFuel]
      exact Nat.lt_of_lt_of_le hrest (Nat.le_max_right _ _)

def wrapTypeRefSingletonResponse
    : TypeRef -> Execution.ResponseValue -> Execution.ResponseValue
  | .named _typeName, response => response
  | .list inner, response =>
      .list [wrapTypeRefSingletonResponse inner response]
  | .nonNull inner, response =>
      wrapTypeRefSingletonResponse inner response

def wrapTypeRefSelectionSetResult
    : TypeRef -> Execution.Response -> Execution.Result Execution.ResponseValue
  | .named _typeName, response => .ok (response.data, response.errors)
  | .list inner, response =>
      match wrapTypeRefSelectionSetResult inner response with
      | .ok (value, errors) => .ok (.list [value], errors)
      | .error errors => .ok (.null, errors)
  | .nonNull inner, response =>
      Execution.nonNullCompletion (wrapTypeRefSelectionSetResult inner response)

def wrapTypeRefSelectionSetResponse
    (responseName : Name) (outputType : TypeRef)
    (response : Execution.Response)
    : Execution.Response :=
  Execution.selectionSetResultToResponse
    (Execution.singleFieldResult responseName
      (wrapTypeRefSelectionSetResult outputType response))

def wrapTypeRefSelectionSetDataValue
    (outputType : TypeRef) (response : Execution.Response)
    : Execution.ResponseValue :=
  Execution.Result.getD .null (wrapTypeRefSelectionSetResult outputType response)

theorem wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
    : ∀ outputType fields errors,
        ∃ value wrappedErrors,
          wrapTypeRefSelectionSetResult outputType
              ({ data := Execution.ResponseValue.object fields, errors := errors }
                : Execution.Response)
            = .ok (value, wrappedErrors)
          ∧ value ≠ Execution.ResponseValue.null
  | .named _typeName, fields, errors => by
      exact ⟨Execution.ResponseValue.object fields, errors, rfl,
        by simp⟩
  | .list inner, fields, errors => by
      rcases
          wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response inner
            fields errors with
        ⟨innerValue, innerErrors, hinner, _hinnerNonNull⟩
      exact
        ⟨Execution.ResponseValue.list [innerValue], innerErrors,
          by simp [wrapTypeRefSelectionSetResult, hinner],
          by simp⟩
  | .nonNull inner, fields, errors => by
      rcases
          wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response inner
            fields errors with
        ⟨innerValue, innerErrors, hinner, hinnerNonNull⟩
      refine ⟨innerValue, innerErrors, ?_, hinnerNonNull⟩
      cases innerValue <;>
        simp [wrapTypeRefSelectionSetResult, hinner,
          Execution.nonNullCompletion] at hinnerNonNull ⊢

theorem leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
    (schema : Schema)
    : ∀ (leftType rightType : TypeRef) (value : String)
        (rightValue : Execution.ResponseValue) (rightErrors : Nat)
        (fields : List (Name × Execution.ResponseValue)) (errors : Nat),
        (TypeRef.named leftType.namedType).isCompositeBool schema = false
        -> (TypeRef.named rightType.namedType).isCompositeBool schema = true
        -> wrapTypeRefSelectionSetResult rightType
              ({ data := Execution.ResponseValue.object fields, errors := errors }
                : Execution.Response)
            = .ok (rightValue, rightErrors)
        -> ¬ Execution.ResponseValue.semanticEquivalent
              (leafProbeResponseValue leftType value) rightValue
  | .named _leftName, .named _rightName, value, rightValue, rightErrors,
      fields, errors, _hleftLeaf, _hrightComposite, hwrapped => by
      intro hsemantic
      cases hwrapped
      simp [leafProbeResponseValue,
        Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical] at hsemantic
  | .named leftName, .list rightInner, value, rightValue, rightErrors,
      fields, errors, hleftLeaf, hrightComposite, hwrapped => by
      intro hsemantic
      rcases
          wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
            rightInner fields errors with
        ⟨innerValue, innerErrors, hinner, _hinnerNonNull⟩
      simp [wrapTypeRefSelectionSetResult, hinner] at hwrapped
      rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
      subst rightValue
      simp [leafProbeResponseValue,
        Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical,
        Execution.ResponseValue.canonicalList] at hsemantic
  | .named leftName, .nonNull rightInner, value, rightValue, rightErrors,
      fields, errors, hleftLeaf, hrightComposite, hwrapped => by
      intro hsemantic
      rcases
          wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
            rightInner fields errors with
        ⟨innerValue, innerErrors, hinner, hinnerNonNull⟩
      cases innerValue with
      | null =>
          exact hinnerNonNull rfl
      | scalar innerScalar =>
        simp [wrapTypeRefSelectionSetResult, hinner,
          Execution.nonNullCompletion] at hwrapped
        rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
        subst rightValue
        exact
          leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
            schema (.named leftName) rightInner value
            (Execution.ResponseValue.scalar innerScalar) innerErrors fields errors
            hleftLeaf hrightComposite hinner hsemantic
      | object innerFields =>
        simp [wrapTypeRefSelectionSetResult, hinner,
          Execution.nonNullCompletion] at hwrapped
        rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
        subst rightValue
        exact
          leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
            schema (.named leftName) rightInner value
            (Execution.ResponseValue.object innerFields) innerErrors fields errors
            hleftLeaf hrightComposite hinner hsemantic
      | list innerValues =>
        simp [wrapTypeRefSelectionSetResult, hinner,
          Execution.nonNullCompletion] at hwrapped
        rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
        subst rightValue
        exact
          leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
            schema (.named leftName) rightInner value
            (Execution.ResponseValue.list innerValues) innerErrors fields errors
            hleftLeaf hrightComposite hinner hsemantic
  | .list leftInner, .named _rightName, value, rightValue, rightErrors,
      fields, errors, _hleftLeaf, _hrightComposite, hwrapped => by
      intro hsemantic
      cases hwrapped
      simp [leafProbeResponseValue,
        Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical,
        Execution.ResponseValue.canonicalList] at hsemantic
  | .list leftInner, .list rightInner, value, rightValue, rightErrors,
      fields, errors, hleftLeaf, hrightComposite, hwrapped => by
      intro hsemantic
      rcases
          wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
            rightInner fields errors with
        ⟨innerValue, innerErrors, hinner, _hinnerNonNull⟩
      simp [wrapTypeRefSelectionSetResult, hinner] at hwrapped
      rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
      subst rightValue
      exact
        leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
          schema leftInner rightInner value innerValue innerErrors fields
          errors hleftLeaf hrightComposite hinner
          (by
            simpa [leafProbeResponseValue,
              Execution.ResponseValue.semanticEquivalent,
              Execution.ResponseValue.canonical,
              Execution.ResponseValue.canonicalList] using hsemantic)
  | .list leftInner, .nonNull rightInner, value, rightValue, rightErrors,
      fields, errors, hleftLeaf, hrightComposite, hwrapped => by
      intro hsemantic
      rcases
          wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
            rightInner fields errors with
        ⟨innerValue, innerErrors, hinner, hinnerNonNull⟩
      cases innerValue with
      | null =>
          exact hinnerNonNull rfl
      | scalar innerScalar =>
        simp [wrapTypeRefSelectionSetResult, hinner,
          Execution.nonNullCompletion] at hwrapped
        rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
        subst rightValue
        exact
          leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
            schema (.list leftInner) rightInner value
            (Execution.ResponseValue.scalar innerScalar) innerErrors fields errors
            hleftLeaf hrightComposite hinner hsemantic
      | object innerFields =>
        simp [wrapTypeRefSelectionSetResult, hinner,
          Execution.nonNullCompletion] at hwrapped
        rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
        subst rightValue
        exact
          leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
            schema (.list leftInner) rightInner value
            (Execution.ResponseValue.object innerFields) innerErrors fields errors
            hleftLeaf hrightComposite hinner hsemantic
      | list innerValues =>
        simp [wrapTypeRefSelectionSetResult, hinner,
          Execution.nonNullCompletion] at hwrapped
        rcases hwrapped with ⟨hrightValue, _hrightErrors⟩
        subst rightValue
        exact
          leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
            schema (.list leftInner) rightInner value
            (Execution.ResponseValue.list innerValues) innerErrors fields errors
            hleftLeaf hrightComposite hinner hsemantic
  | .nonNull leftInner, rightType, value, rightValue, rightErrors, fields,
      errors, hleftLeaf, hrightComposite, hwrapped => by
      intro hsemantic
      exact
        leafProbeResponseValue_not_semanticEquivalent_wrapped_object_of_composite
          schema leftInner rightType value rightValue rightErrors fields
          errors hleftLeaf hrightComposite hwrapped
          (by simpa [leafProbeResponseValue] using hsemantic)
termination_by leftType rightType _value _rightValue _rightErrors _fields _errors =>
  sizeOf leftType + sizeOf rightType
decreasing_by
  all_goals
    simp_wf
    try omega

def objectProbeResolverValueWithRuntime {ObjectRef : Type}
    (runtimeType : Name) (ref : ObjectRef)
    : TypeRef -> Execution.ResolverValue ObjectRef
  | .named _typeName => .object runtimeType ref
  | .list inner =>
      .list [objectProbeResolverValueWithRuntime runtimeType ref inner]
  | .nonNull inner =>
      objectProbeResolverValueWithRuntime runtimeType ref inner

theorem selectionSetResultToResponse_combine_append_nil
    (result : Execution.Result (List (Name × Execution.ResponseValue)))
    : Execution.selectionSetResultToResponse
        (Execution.Result.combine List.append result (.ok ([], 0)))
      = Execution.selectionSetResultToResponse result := by
  cases result with
  | error errors =>
      simp [Execution.selectionSetResultToResponse, Execution.Result.combine]
  | ok result =>
      rcases result with ⟨fields, errors⟩
      simp [Execution.selectionSetResultToResponse, Execution.Result.combine]

theorem wrapTypeRefSelectionSetDataValue_nonNull
    (inner : TypeRef) (response : Execution.Response)
    : wrapTypeRefSelectionSetDataValue (.nonNull inner) response
      = wrapTypeRefSelectionSetDataValue inner response := by
  cases hwrapped : wrapTypeRefSelectionSetResult inner response with
  | error errors =>
      simp [wrapTypeRefSelectionSetDataValue, wrapTypeRefSelectionSetResult,
        Execution.nonNullCompletion, Execution.Result.getD, hwrapped]
  | ok result =>
      rcases result with ⟨value, errors⟩
      cases value <;>
        simp [wrapTypeRefSelectionSetDataValue, wrapTypeRefSelectionSetResult,
          Execution.nonNullCompletion, Execution.Result.getD, hwrapped]

theorem semanticEquivalent_singleton_list_data {left right : Execution.ResponseValue}
    : Execution.ResponseValue.semanticEquivalent (.list [left]) (.list [right])
      -> Execution.ResponseValue.semanticEquivalent left right := by
  intro hsemantic
  simpa [Execution.ResponseValue.semanticEquivalent,
    Execution.ResponseValue.canonical,
    Execution.ResponseValue.canonicalList] using hsemantic

theorem wrapTypeRefSingletonResponse_object_ne_null
    : ∀ outputType fields,
        wrapTypeRefSingletonResponse outputType (Execution.ResponseValue.object fields)
        ≠ Execution.ResponseValue.null
  | .named _typeName, fields => by
      simp [wrapTypeRefSingletonResponse]
  | .list inner, fields => by
      simp [wrapTypeRefSingletonResponse]
  | .nonNull inner, fields => by
      simpa [wrapTypeRefSingletonResponse] using
        wrapTypeRefSingletonResponse_object_ne_null inner fields

theorem wrapTypeRefSelectionSetResult_object_response
    : ∀ outputType fields errors,
        wrapTypeRefSelectionSetResult outputType
          ({ data := Execution.ResponseValue.object fields, errors := errors }
            : Execution.Response)
        = .ok
            (
              wrapTypeRefSingletonResponse outputType
                (Execution.ResponseValue.object fields),
              errors
            )
  | .named _typeName, fields, errors => by
      simp [wrapTypeRefSelectionSetResult, wrapTypeRefSingletonResponse]
  | .list inner, fields, errors => by
      simp [wrapTypeRefSelectionSetResult,
        wrapTypeRefSelectionSetResult_object_response inner fields errors,
        wrapTypeRefSingletonResponse]
  | .nonNull inner, fields, errors => by
      have hinner :=
        wrapTypeRefSelectionSetResult_object_response inner fields errors
      have hnonNull :=
        wrapTypeRefSingletonResponse_object_ne_null inner fields
      cases hvalue :
          wrapTypeRefSingletonResponse inner
            (Execution.ResponseValue.object fields) <;>
        simp [wrapTypeRefSelectionSetResult, hinner,
          wrapTypeRefSingletonResponse, Execution.nonNullCompletion,
          hvalue] at hnonNull ⊢

theorem wrapTypeRefSingletonResponse_object_semanticEquivalent_injective
    : ∀ leftType rightType leftFields rightFields,
        Execution.ResponseValue.semanticEquivalent
          (wrapTypeRefSingletonResponse leftType
            (Execution.ResponseValue.object leftFields))
          (wrapTypeRefSingletonResponse rightType
            (Execution.ResponseValue.object rightFields))
        -> Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftFields)
            (Execution.ResponseValue.object rightFields)
  | .named _leftName, .named _rightName, leftFields, rightFields,
      hsemantic => by
      simpa [wrapTypeRefSingletonResponse] using hsemantic
  | .named _leftName, .list rightInner, leftFields, rightFields,
      hsemantic => by
      have hfalse : False := by
        simp [wrapTypeRefSingletonResponse,
          Execution.ResponseValue.semanticEquivalent,
          Execution.ResponseValue.canonical,
          Execution.ResponseValue.canonicalList] at hsemantic
      exact False.elim hfalse
  | .named leftName, .nonNull rightInner, leftFields, rightFields,
      hsemantic => by
      exact
        wrapTypeRefSingletonResponse_object_semanticEquivalent_injective
          (.named leftName) rightInner leftFields rightFields
          (by simpa [wrapTypeRefSingletonResponse] using hsemantic)
  | .list leftInner, .named _rightName, leftFields, rightFields,
      hsemantic => by
      have hfalse : False := by
        simp [wrapTypeRefSingletonResponse,
          Execution.ResponseValue.semanticEquivalent,
          Execution.ResponseValue.canonical,
          Execution.ResponseValue.canonicalList] at hsemantic
      exact False.elim hfalse
  | .list leftInner, .list rightInner, leftFields, rightFields,
      hsemantic => by
      exact
        wrapTypeRefSingletonResponse_object_semanticEquivalent_injective
          leftInner rightInner leftFields rightFields
          (semanticEquivalent_singleton_list_data
            (by simpa [wrapTypeRefSingletonResponse] using hsemantic))
  | .list leftInner, .nonNull rightInner, leftFields, rightFields,
      hsemantic => by
      exact
        wrapTypeRefSingletonResponse_object_semanticEquivalent_injective
          (.list leftInner) rightInner leftFields rightFields
          (by simpa [wrapTypeRefSingletonResponse] using hsemantic)
  | .nonNull leftInner, rightType, leftFields, rightFields,
      hsemantic => by
      exact
        wrapTypeRefSingletonResponse_object_semanticEquivalent_injective
          leftInner rightType leftFields rightFields
          (by simpa [wrapTypeRefSingletonResponse] using hsemantic)
termination_by leftType rightType _leftFields _rightFields =>
  sizeOf leftType + sizeOf rightType
decreasing_by
  all_goals
    simp_wf
    try omega

theorem wrapped_object_values_not_semanticEquivalent_of_child
    (leftType rightType : TypeRef)
    {leftValue rightValue : Execution.ResponseValue}
    {leftFieldErrors rightFieldErrors : Nat}
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat}
    : wrapTypeRefSelectionSetResult leftType
          ({ data := Execution.ResponseValue.object leftFields, errors := leftErrors }
            : Execution.Response)
        = .ok (leftValue, leftFieldErrors)
      -> wrapTypeRefSelectionSetResult rightType
            ({ data := Execution.ResponseValue.object rightFields, errors := rightErrors }
              : Execution.Response)
          = .ok (rightValue, rightFieldErrors)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.ResponseValue.object leftFields)
            (Execution.ResponseValue.object rightFields)
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue := by
  intro hleft hright hchild hsemantic
  have hleftExact :=
    wrapTypeRefSelectionSetResult_object_response
      leftType leftFields leftErrors
  have hrightExact :=
    wrapTypeRefSelectionSetResult_object_response
      rightType rightFields rightErrors
  rw [hleftExact] at hleft
  rw [hrightExact] at hright
  cases hleft
  cases hright
  exact hchild
    (wrapTypeRefSingletonResponse_object_semanticEquivalent_injective
      leftType rightType leftFields rightFields hsemantic)

theorem wrapTypeRefSelectionSetDataValue_semanticEquivalent_injective
    (outputType : TypeRef) {left right : Execution.Response}
    : Execution.ResponseValue.semanticEquivalent
        (wrapTypeRefSelectionSetDataValue outputType left)
        (wrapTypeRefSelectionSetDataValue outputType right)
      -> Execution.ResponseValue.semanticEquivalent left.data right.data := by
  intro hsemantic
  induction outputType with
  | named typeName =>
      simpa [wrapTypeRefSelectionSetDataValue,
        wrapTypeRefSelectionSetResult, Execution.Result.getD] using hsemantic
  | list inner ih =>
      cases hleft : wrapTypeRefSelectionSetResult inner left with
      | error leftErrors =>
          cases hright : wrapTypeRefSelectionSetResult inner right with
          | error rightErrors =>
              apply ih
              simp [wrapTypeRefSelectionSetDataValue, Execution.Result.getD,
                hleft, hright, Execution.ResponseValue.semanticEquivalent,
                Execution.ResponseValue.canonical]
          | ok rightResult =>
              rcases rightResult with ⟨rightValue, rightErrors⟩
              simp [wrapTypeRefSelectionSetDataValue,
                wrapTypeRefSelectionSetResult, Execution.Result.getD,
                hleft, hright, Execution.ResponseValue.semanticEquivalent,
                Execution.ResponseValue.canonical,
                Execution.ResponseValue.canonicalList] at hsemantic
      | ok leftResult =>
          rcases leftResult with ⟨leftValue, leftErrors⟩
          cases hright : wrapTypeRefSelectionSetResult inner right with
          | error rightErrors =>
              simp [wrapTypeRefSelectionSetDataValue,
                wrapTypeRefSelectionSetResult, Execution.Result.getD,
                hleft, hright, Execution.ResponseValue.semanticEquivalent,
                Execution.ResponseValue.canonical,
                Execution.ResponseValue.canonicalList] at hsemantic
          | ok rightResult =>
              rcases rightResult with ⟨rightValue, rightErrors⟩
              apply ih
              apply semanticEquivalent_singleton_list_data
              simpa [wrapTypeRefSelectionSetDataValue,
                wrapTypeRefSelectionSetResult, Execution.Result.getD,
                hleft, hright] using hsemantic
  | nonNull inner ih =>
      rw [wrapTypeRefSelectionSetDataValue_nonNull inner left,
        wrapTypeRefSelectionSetDataValue_nonNull inner right] at hsemantic
      exact ih hsemantic

theorem completeValue_objectProbeWithRuntime_response
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (runtimeType : Name) (ref : ObjectRef)
    (fields : List Execution.ExecutableField)
    : ∀ outputType,
        schema.typeIncludesObjectBool outputType.namedType runtimeType = true
        -> Execution.completeValue schema resolvers variableValues
              (fuel + leafProbeFuel outputType) outputType fields
              (objectProbeResolverValueWithRuntime runtimeType ref outputType)
            = wrapTypeRefSelectionSetResult outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema resolvers
                    variableValues fuel (.object runtimeType ref)
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType ref)
                      (Execution.mergedFieldSelectionSet fields))))
  | .named typeName, hinclude => by
      have hincludeNamed :
          schema.typeIncludesObjectBool typeName runtimeType = true := by
        simpa [TypeRef.namedType] using hinclude
      cases hchild :
          Execution.executeCollectedFields schema resolvers variableValues fuel
            (.object runtimeType ref)
            (Execution.collectFields schema variableValues runtimeType
              (.object runtimeType ref)
              (Execution.mergedFieldSelectionSet fields)) with
      | error errors =>
          simp [leafProbeFuel, objectProbeResolverValueWithRuntime,
            wrapTypeRefSelectionSetResult, Execution.selectionSetResultToResponse,
            Execution.completeValue, hincludeNamed,
            Execution.catchBubbleAsNull, hchild]
      | ok result =>
          rcases result with ⟨responseFields, errors⟩
          simp [leafProbeFuel, objectProbeResolverValueWithRuntime,
            wrapTypeRefSelectionSetResult, Execution.selectionSetResultToResponse,
            Execution.completeValue, hincludeNamed,
            Execution.catchBubbleAsNull, hchild]
  | .list inner, hinclude => by
      have hinnerInclude :
          schema.typeIncludesObjectBool inner.namedType runtimeType = true := by
        simpa [TypeRef.namedType] using hinclude
      have hinner :=
        completeValue_objectProbeWithRuntime_response schema resolvers
          variableValues fuel runtimeType ref fields inner hinnerInclude
      cases hwrapped :
          wrapTypeRefSelectionSetResult inner
            (Execution.selectionSetResultToResponse
              (Execution.executeCollectedFields schema resolvers
                variableValues fuel (.object runtimeType ref)
                (Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType ref)
                  (Execution.mergedFieldSelectionSet fields)))) with
      | error errors =>
          have hcomplete :
              Execution.completeValue schema resolvers variableValues
                (fuel + leafProbeFuel inner) inner fields
                (objectProbeResolverValueWithRuntime runtimeType ref inner)
              =
              .error errors := by
            simpa [hwrapped] using hinner
          have hfuel :
              fuel + (leafProbeFuel inner + 1) =
                fuel + leafProbeFuel inner + 1 := by
            omega
          rw [leafProbeFuel, hfuel]
          simp [objectProbeResolverValueWithRuntime,
            wrapTypeRefSelectionSetResult, hwrapped,
            Execution.completeValue, Execution.completeValueList,
            hcomplete, Execution.Result.combine, Execution.catchBubbleAsNull]
      | ok result =>
          rcases result with ⟨value, errors⟩
          have hcomplete :
              Execution.completeValue schema resolvers variableValues
                (fuel + leafProbeFuel inner) inner fields
                (objectProbeResolverValueWithRuntime runtimeType ref inner)
              =
              .ok (value, errors) := by
            simpa [hwrapped] using hinner
          have hfuel :
              fuel + (leafProbeFuel inner + 1) =
                fuel + leafProbeFuel inner + 1 := by
            omega
          rw [leafProbeFuel, hfuel]
          simp [objectProbeResolverValueWithRuntime,
            wrapTypeRefSelectionSetResult, hwrapped,
            Execution.completeValue, Execution.completeValueList,
            hcomplete, Execution.Result.combine, Execution.catchBubbleAsNull]
  | .nonNull inner, hinclude => by
      have hinnerInclude :
          schema.typeIncludesObjectBool inner.namedType runtimeType = true := by
        simpa [TypeRef.namedType] using hinclude
      have hinner :=
        completeValue_objectProbeWithRuntime_response schema resolvers
          variableValues fuel runtimeType ref fields inner hinnerInclude
      have hfuelPos : 0 < fuel + leafProbeFuel inner := by
        have hinnerFuel := leafProbeFuel_pos inner
        omega
      cases hfuel : fuel + leafProbeFuel inner with
      | zero =>
          rw [hfuel] at hfuelPos
          exact False.elim (Nat.not_lt_zero 0 hfuelPos)
      | succ innerFuel =>
          have hcongr := congrArg Execution.nonNullCompletion hinner
          rw [hfuel] at hcongr
          simpa [leafProbeFuel, objectProbeResolverValueWithRuntime,
            wrapTypeRefSelectionSetResult, Execution.completeValue, hfuel,
            Execution.nonNullCompletion] using hcongr

theorem executeField_objectProbeWithRuntime_response
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> Execution.coerceAndResolveFieldValue schema resolvers variableValues
            fieldDefinition parentType fieldName arguments source
          = some
              (objectProbeResolverValueWithRuntime runtimeType ref
                fieldDefinition.outputType)
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeField schema resolvers variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            source responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := selectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema resolvers variableValues
                    fuel (.object runtimeType ref)
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType ref) selectionSet)))) := by
  intro hlookup hresolve hinclude
  have hcomplete :=
    completeValue_objectProbeWithRuntime_response schema resolvers
      variableValues fuel runtimeType ref
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := selectionSet
      }]
      fieldDefinition.outputType hinclude
  simpa [Execution.executeField, hlookup, hresolve,
    Execution.singleFieldResult, Execution.mergedFieldSelectionSet] using
    congrArg (Execution.singleFieldResult responseName) hcomplete

theorem executeField_objectProbeWithRuntime_response_of_fuel_ge
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (responseName parentType fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> Execution.coerceAndResolveFieldValue schema resolvers variableValues
            fieldDefinition parentType fieldName arguments source
          = some
              (objectProbeResolverValueWithRuntime runtimeType ref
                fieldDefinition.outputType)
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema resolvers variableValues (fuel + 1)
            source responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := selectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType (.object runtimeType ref) selectionSet)) := by
  intro hlookup hresolve hinclude hfuel
  have hexecute :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues (fuel - leafProbeFuel fieldDefinition.outputType)
      source responseName parentType fieldName arguments selectionSet
      fieldDefinition runtimeType ref hlookup hresolve hinclude
  have hfuelEq :
      fuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      fuel + 1 := by
    omega
  simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
    Execution.executeRootSelectionSet, hfuelEq] using hexecute

theorem executeSelectionSetAsResponse_singleton_objectProbeWithRuntime_response
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType responseName fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (ref : ObjectRef)
    (source : Execution.ResolverValue ObjectRef)
    (childSelectionSet : List Selection)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> Execution.coerceAndResolveFieldValue schema resolvers variableValues
            fieldDefinition parentType fieldName arguments source
          = some
              (objectProbeResolverValueWithRuntime runtimeType ref
                fieldDefinition.outputType)
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1) parentType source
            [Selection.field responseName fieldName arguments [] childSelectionSet]
          = wrapTypeRefSelectionSetResponse responseName fieldDefinition.outputType
              (Execution.executeSelectionSetAsResponse schema resolvers variableValues
                fuel runtimeType (.object runtimeType ref) childSelectionSet) := by
  intro hlookup hresolve hinclude
  have hfield :
      Execution.executeField schema resolvers variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        source responseName
        [{
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := arguments
          selectionSet := childSelectionSet
        }]
      =
      Execution.singleFieldResult responseName
        (wrapTypeRefSelectionSetResult fieldDefinition.outputType
          (Execution.selectionSetResultToResponse
            (Execution.executeCollectedFields schema resolvers variableValues
              fuel (.object runtimeType ref)
              (Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref) childSelectionSet)))) :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel source responseName parentType fieldName arguments
      childSelectionSet fieldDefinition runtimeType ref hlookup hresolve
      hinclude
  simp [Execution.executeSelectionSetAsResponse,
    Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    Execution.collectFields, Execution.collectSelection,
    Execution.selectionDirectivesAllowBool,
    Execution.mergeExecutableGroups, Execution.executeCollectedFields,
    wrapTypeRefSelectionSetResponse, hfield,
    selectionSetResultToResponse_combine_append_nil]

end GroundTypeNormalization

end NormalForm

end GraphQL
