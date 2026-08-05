import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.AbstractReturnSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness

/-!
Field execution semantic cases for ground-type normalization.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectRef : Type}

theorem normalizeSelectionSet_executeSelectionSet_field_lookup_none_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition)
    (depth : Nat) (parentType responseName fieldName : Name)
    (arguments : List Argument) (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Validation.selectionSetValid schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments [] selectionSet :: rest)
      -> schema.lookupField parentType fieldName = none
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.field responseName fieldName arguments [] selectionSet :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.field responseName fieldName arguments [] selectionSet
                :: rest) := by
  intro hvalid hlookup
  exact False.elim
    (Validation.selectionSetValid_field_head_lookup_none_false
      hvalid hlookup)

theorem normalizeSelectionSet_executeSelectionSet_field_lookup_none_lookupValid_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType responseName fieldName : Name)
    (arguments : List Argument) (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : selectionSetLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] selectionSet :: rest)
      -> schema.lookupField parentType fieldName = none
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.field responseName fieldName arguments [] selectionSet :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.field responseName fieldName arguments [] selectionSet
                :: rest) := by
  intro hvalid hlookup
  exact False.elim
    (selectionSetLookupValid_field_head_lookup_none_false hvalid hlookup)

theorem executeField_singleton_eq_group_of_completeValue
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) (responseName : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField)
    (normalizedSelectionSet : List Selection)
    : let fieldDefinition? := schema.lookupField field.parentType field.fieldName
      (match fieldDefinition? with
        | some fieldDefinition =>
            match resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
            | some value =>
                Execution.completeValue schema resolvers variableValues depth
                  fieldDefinition.outputType
                  [{ field with selectionSet := normalizedSelectionSet }] value
                = Execution.completeValue schema resolvers variableValues depth
                    fieldDefinition.outputType (field :: fields) value
            | none => True
        | none => True)
      -> Execution.executeField schema resolvers variableValues (depth + 1)
            source responseName
            [{ field with selectionSet := normalizedSelectionSet }]
          = Execution.executeField schema resolvers variableValues (depth + 1)
              source responseName (field :: fields) := by
  intro fieldDefinition? hcomplete
  simp only [Execution.executeField]
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp []
  | some fieldDefinition =>
      cases hresolved
            : resolvers.resolve field.parentType field.fieldName
                field.arguments source with
      | none =>
          simp
      | some value =>
          have hcomplete' :
              Execution.completeValue schema resolvers variableValues depth
                  fieldDefinition.outputType
                  [{ field with selectionSet := normalizedSelectionSet }] value =
                Execution.completeValue schema resolvers variableValues depth
                  fieldDefinition.outputType (field :: fields) value := by
            simpa [fieldDefinition?, hlookup, hresolved] using hcomplete
          simp [Execution.singleFieldResult, hcomplete']

theorem executeField_singleton_eq_group_of_child_object_lt
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef) (responseName : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField)
    (normalizedSelectionSet : List Selection)
    : (∀ childDepth runtimeType ref,
        childDepth < depth
        -> Execution.executeSelectionSet schema resolvers variableValues
              childDepth runtimeType (.object runtimeType ref)
              normalizedSelectionSet
            = Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType (.object runtimeType ref)
                (Execution.mergedFieldSelectionSet (field :: fields)))
      -> Execution.executeField schema resolvers variableValues (depth + 1)
            source responseName
            [{ field with selectionSet := normalizedSelectionSet }]
          = Execution.executeField schema resolvers variableValues (depth + 1)
              source responseName (field :: fields) := by
  intro hcomplete
  apply executeField_singleton_eq_group_of_completeValue
    schema resolvers variableValues depth source responseName field fields
    normalizedSelectionSet
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp []
  | some fieldDefinition =>
      cases hresolved
            : resolvers.resolve field.parentType field.fieldName
                field.arguments source with
      | none =>
          simp
      | some value =>
          simp
          apply completeValue_eq_of_child_object_lt schema resolvers variableValues
            depth fieldDefinition.outputType
            [{ field with selectionSet := normalizedSelectionSet }]
            (field :: fields) value
          intro childDepth runtimeType ref hlt
          simpa [Execution.mergedFieldSelectionSet] using
            hcomplete childDepth runtimeType ref hlt

theorem executeCollectedFields_cons_eq_of_parts
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (normalizedGroup sourceGroup : Name × List Execution.ExecutableField)
    (normalizedRest sourceRest : List (Name × List Execution.ExecutableField))
    : Execution.executeField schema resolvers variableValues depth source
          normalizedGroup.fst normalizedGroup.snd
        = Execution.executeField schema resolvers variableValues depth source
            sourceGroup.fst sourceGroup.snd
      -> Execution.executeCollectedFields schema resolvers variableValues depth
            source normalizedRest
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source sourceRest
      -> Execution.executeCollectedFields schema resolvers variableValues depth
            source (normalizedGroup :: normalizedRest)
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source (sourceGroup :: sourceRest) := by
  intro hhead htail
  cases normalizedGroup with
  | mk normalizedResponseName normalizedFields =>
      cases sourceGroup with
      | mk sourceResponseName sourceFields =>
          simp [Execution.executeCollectedFields]
          rw [hhead, htail]

theorem executeCollectedFields_zero (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef)
    : ∀ groups,
        Execution.executeCollectedFields schema resolvers variableValues 0 source groups
        = match groups with
          | [] => .ok ([], 0)
          | (_responseName, []) :: rest =>
              Execution.Result.combine
                List.append
                (Execution.outOfFuel)
                (Execution.executeCollectedFields schema resolvers variableValues 0
                  source rest)
          | (_responseName, _field :: _fields) :: rest =>
              Execution.Result.combine
                List.append
                (Execution.outOfFuel)
                (Execution.executeCollectedFields schema resolvers variableValues 0
                  source rest)
  | [] => by
      simp [Execution.executeCollectedFields]
  | (_responseName, fields) :: rest => by
      cases fields with
      | nil =>
          simp [Execution.executeCollectedFields, Execution.executeField,
            Execution.Result.combine, Execution.outOfFuel]
      | cons field fields =>
          simp [Execution.executeCollectedFields, Execution.executeField,
            Execution.Result.combine, Execution.outOfFuel]

theorem executeSelectionSet_field_head_eq_of_completeValue
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections normalizedSubselections normalizedRest rest : List Selection)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    : let sourceField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := subselections
        }
      let fieldDefinition? :=
        schema.lookupField sourceField.parentType sourceField.fieldName
      responseName
        ∉ (Execution.collectFields schema variableValues parentType source
            normalizedRest).map
            Prod.fst
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments [] subselections :: rest)
          = (responseName, sourceField :: sourceFields) :: sourceRest
      -> (match fieldDefinition? with
          | some fieldDefinition =>
              match resolvers.resolve sourceField.parentType sourceField.fieldName
                      sourceField.arguments source with
              | some value =>
                  Execution.completeValue schema resolvers variableValues (depth - 1)
                    fieldDefinition.outputType
                    [{ sourceField with selectionSet := normalizedSubselections }] value
                  = Execution.completeValue schema resolvers variableValues (depth - 1)
                      fieldDefinition.outputType (sourceField :: sourceFields) value
              | none => True
          | none => True)
      -> Execution.executeCollectedFields schema resolvers variableValues depth
            source
            (Execution.collectFields schema variableValues parentType source
              normalizedRest)
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source sourceRest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.field responseName fieldName arguments [] normalizedSubselections
              :: normalizedRest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.field responseName fieldName arguments [] subselections
                :: rest) := by
  intro sourceField fieldDefinition? hnotin hsourceCollect
    hcomplete htail
  cases depth with
  | zero =>
      let normalizedField : Execution.ExecutableField :=
        { sourceField with selectionSet := normalizedSubselections }
      have hnormalizedCollect :
          Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments []
              normalizedSubselections :: normalizedRest)
          =
          (responseName, [normalizedField])
            :: Execution.collectFields schema variableValues parentType source
              normalizedRest := by
        simpa [sourceField, normalizedField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType source responseName fieldName
            arguments normalizedSubselections normalizedRest hnotin
      simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        hnormalizedCollect, hsourceCollect, Execution.executeCollectedFields,
        Execution.executeField, Execution.Result.combine, htail]
  | succ fieldDepth =>
      let normalizedField : Execution.ExecutableField :=
        { sourceField with selectionSet := normalizedSubselections }
      have hnormalizedCollect :
          Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments []
              normalizedSubselections :: normalizedRest)
          =
          (responseName, [normalizedField])
            :: Execution.collectFields schema variableValues parentType source
              normalizedRest := by
        simpa [sourceField, normalizedField] using
          collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType source responseName fieldName
            arguments normalizedSubselections normalizedRest hnotin
      have hhead :
          Execution.executeField schema resolvers variableValues
            (fieldDepth + 1) source responseName [normalizedField]
          =
          Execution.executeField schema resolvers variableValues
            (fieldDepth + 1) source responseName
            (sourceField :: sourceFields) := by
        simpa [sourceField, normalizedField, fieldDefinition?] using
          executeField_singleton_eq_group_of_completeValue
            schema resolvers variableValues fieldDepth source responseName
            sourceField sourceFields normalizedSubselections hcomplete
      simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        hnormalizedCollect,
        hsourceCollect]
      exact executeCollectedFields_cons_eq_of_parts schema resolvers
        variableValues (fieldDepth + 1) source
        (responseName, [normalizedField])
        (responseName, sourceField :: sourceFields)
        (Execution.collectFields schema variableValues parentType source
          normalizedRest)
        sourceRest hhead htail

theorem normalizeSelectionSet_executeSelectionSet_field_head_of_completeValue
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest normalizedSubselections : List Selection)
    (fieldDefinition : FieldDefinition)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    : let sourceField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := subselections
        }
      let matching :=
        fieldSelectionsWithResponseNameInScope schema parentType responseName rest
      let mergedSubselections := subselections ++ mergeSelectionSets matching
      let returnType := fieldDefinition.outputType.namedType
      let normalizedRest :=
        normalizeSelectionSet schema parentType
          (withoutFieldSelectionsWithResponseName schema responseName rest)
      let computedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema (schema.getPossibleTypes returnType)
            mergedSubselections
      schema.lookupField parentType fieldName = some fieldDefinition
      -> normalizedSubselections = computedSubselections
      -> responseName
          ∉ (Execution.collectFields schema variableValues parentType source
              normalizedRest).map
              Prod.fst
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments [] subselections :: rest)
          = (responseName, sourceField :: sourceFields) :: sourceRest
      -> normalizedFieldWithRest schema fieldDefinition.outputType.namedType
            responseName fieldName arguments [] normalizedSubselections
            normalizedRest
          = Selection.field responseName fieldName arguments [] normalizedSubselections
            :: normalizedRest
      -> (match schema.lookupField parentType fieldName with
          | some fieldDefinition =>
              match resolvers.resolve parentType fieldName arguments source with
              | some value =>
                  Execution.completeValue schema resolvers variableValues (depth - 1)
                    fieldDefinition.outputType
                    [{ sourceField with selectionSet := normalizedSubselections }] value
                  = Execution.completeValue schema resolvers variableValues (depth - 1)
                      fieldDefinition.outputType (sourceField :: sourceFields) value
              | none => True
          | none => True)
      -> Execution.executeCollectedFields schema resolvers variableValues depth
            source
            (Execution.collectFields schema variableValues parentType source
              normalizedRest)
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source sourceRest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.field responseName fieldName arguments [] subselections :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.field responseName fieldName arguments [] subselections
                :: rest) := by
  intro sourceField matching mergedSubselections returnType normalizedRest
    computedSubselections hlookup hsubsections hnotin hsourceCollect
    hnormalizedFieldWithRest hcomplete htail
  have hnormalized :
      normalizeSelectionSet schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest)
      =
      Selection.field responseName fieldName arguments [] normalizedSubselections
        :: normalizedRest := by
    rw [normalizeSelectionSet.eq_2, hlookup]
    change normalizedFieldWithRest schema returnType responseName fieldName
      arguments [] computedSubselections normalizedRest =
      Selection.field responseName fieldName arguments [] normalizedSubselections
        :: normalizedRest
    rw [← hsubsections]
    exact hnormalizedFieldWithRest
  rw [hnormalized]
  exact executeSelectionSet_field_head_eq_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments subselections normalizedSubselections normalizedRest
    rest sourceFields sourceRest hnotin hsourceCollect
    (by simpa [sourceField] using hcomplete)
    htail

theorem normalizeSelectionSet_executeSelectionSet_field_head_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest normalizedSubselections : List Selection)
    (fieldDefinition : FieldDefinition)
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> normalizedSubselections
          = (let matching :=
                fieldSelectionsWithResponseNameInScope schema parentType responseName rest
              let mergedSubselections := subselections ++ mergeSelectionSets matching
              let returnType := fieldDefinition.outputType.namedType
              if objectTypeNameBool schema returnType then
                normalizeSelectionSet schema returnType mergedSubselections
              else
                possibleTypeNormalizations schema
                  (schema.getPossibleTypes returnType) mergedSubselections)
      -> (let returnType := fieldDefinition.outputType.namedType
          let normalizedRest :=
            normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)
          normalizedFieldWithRest schema returnType responseName fieldName
            arguments [] normalizedSubselections normalizedRest
          = Selection.field responseName fieldName arguments [] normalizedSubselections
            :: normalizedRest)
      -> (∀ childDepth runtimeType ref,
            childDepth < depth
            -> schema.typeIncludesObjectBool
                  ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                  runtimeType
                = true
            -> Execution.executeSelectionSet schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType ref)
                  normalizedSubselections
                = Execution.executeSelectionSet schema resolvers variableValues
                    childDepth runtimeType (.object runtimeType ref)
                    (subselections
                      ++ mergeSelectionSets
                          (fieldSelectionsWithResponseNameInScope schema parentType
                            responseName rest)))
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (withoutFieldSelectionsWithResponseName schema responseName rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.field responseName fieldName arguments [] subselections :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.field responseName fieldName arguments [] subselections
                :: rest) := by
  intro hobject hsource hfree hlookup hsubsections hnormalizedFieldWithRest
    hchild htail
  rcases collectFields_field_head_exists schema variableValues parentType
      source responseName fieldName arguments subselections rest with
    ⟨sourceFields, sourceRest, hsourceCollect⟩
  let sourceField : Execution.ExecutableField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      selectionSet := subselections
    }
  have hsourceValue :
      ∃ runtimeType ref,
        source = .object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    rcases hsource with ⟨runtimeType, ref, hsourceEq, hinclude⟩
    subst source
    exact ⟨runtimeType, ref, by simp [], hinclude⟩
  let normalizedRest :=
    normalizeSelectionSet schema parentType
      (withoutFieldSelectionsWithResponseName schema responseName rest)
  let matching := fieldSelectionsWithResponseNameInScope schema parentType
    responseName rest
  let mergedSubselections := subselections ++ mergeSelectionSets matching
  let returnType := fieldDefinition.outputType.namedType
  have hnotin :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source
          normalizedRest).map Prod.fst := by
    unfold normalizedRest
    exact collectFields_responseName_not_mem_of_responseNameFree schema
      variableValues parentType source responseName hobject hsourceValue
      (normalizeSelectionSet schema parentType
        (withoutFieldSelectionsWithResponseName schema responseName rest))
      (normalizeSelectionSet_directiveFree schema parentType
        (withoutFieldSelectionsWithResponseName schema responseName rest)
        (withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          (selectionSetDirectiveFree_tail hfree)))
      (normalizeSelectionSet_responseNameFree schema parentType responseName
        (withoutFieldSelectionsWithResponseName schema responseName rest)
        (withoutFieldSelectionsWithResponseName_responseNameFree schema parentType
          responseName rest))
  have hsourceRest :
      Execution.collectFields schema variableValues parentType source
        (withoutFieldSelectionsWithResponseName schema responseName rest)
      =
      sourceRest := by
    exact collectFields_withoutFieldSelectionsWithResponseName_fieldHead_rest_eq_sourceRest
      schema variableValues parentType source responseName fieldName arguments
      subselections rest sourceFields sourceRest hobject hsourceValue hfree
      (by simpa [sourceField] using hsourceCollect)
  have htailCollected :
      Execution.executeCollectedFields schema resolvers variableValues depth
        source
        (Execution.collectFields schema variableValues parentType source
          normalizedRest)
      =
      Execution.executeCollectedFields schema resolvers variableValues depth
        source sourceRest := by
    simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      normalizedRest, hsourceRest]
      using htail
  apply normalizeSelectionSet_executeSelectionSet_field_head_of_completeValue
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments subselections rest normalizedSubselections
    fieldDefinition sourceFields sourceRest
  · exact hlookup
  · exact hsubsections
  · exact hnotin
  · simpa [sourceField] using hsourceCollect
  · simpa [matching, mergedSubselections, returnType, normalizedRest]
      using hnormalizedFieldWithRest
  · rw [hlookup]
    cases hresolved :
        resolvers.resolve parentType fieldName arguments source with
    | none =>
        simp
    | some value =>
        simp
        apply completeValue_eq_of_child_object_lt_includes schema resolvers
          variableValues
          (depth - 1)
          fieldDefinition.outputType
          [{ sourceField with selectionSet := normalizedSubselections }]
          (sourceField :: sourceFields)
          value
        intro childDepth runtimeType ref hlt hinclude
        have hmerged :
            Execution.mergedFieldSelectionSet (sourceField :: sourceFields)
              =
            subselections
              ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName rest) := by
          have hprojection :=
            collectFields_fieldSelectionsWithResponseNameInScope_responseSelection schema
              variableValues parentType source responseName
              (Selection.field responseName fieldName arguments [] subselections
                :: rest)
              hobject hsourceValue hfree
          simp [collectedResponseSelectionSet, hsourceCollect,
            fieldSelectionsWithResponseNameInScope, mergeSelectionSets,
            Selection.subselections] at hprojection
          simpa [sourceField] using hprojection
        rw [hmerged]
        have hinclude' :
            schema.typeIncludesObjectBool
              ((schema.fieldReturnType? parentType fieldName).getD fieldName)
              runtimeType = true := by
          simpa [Schema.fieldReturnType?, hlookup] using hinclude
        simpa [Execution.mergedFieldSelectionSet, Schema.fieldReturnType?, hlookup]
          using hchild childDepth runtimeType ref (Nat.lt_of_lt_of_le hlt
            (Nat.sub_le depth 1)) hinclude'
  · exact htailCollected

theorem normalizeSelectionSet_executeSelectionSet_field_head_case_of_recursive
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetSemanticsReady schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (let matching :=
            fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          let mergedSubselections := subselections ++ mergeSelectionSets matching
          let returnType := fieldDefinition.outputType.namedType
          let normalizedSubselections :=
            if objectTypeNameBool schema returnType then
              normalizeSelectionSet schema returnType mergedSubselections
            else
              possibleTypeNormalizations schema (schema.getPossibleTypes returnType)
                mergedSubselections
          let normalizedRest :=
            normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)
          normalizedFieldWithRest schema returnType responseName fieldName arguments []
            normalizedSubselections normalizedRest
          = Selection.field responseName fieldName arguments [] normalizedSubselections
            :: normalizedRest)
      -> (let mergedSubselections :=
            subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)
          ∀ (childDepth : Nat) (runtimeType : Name) (ref : ObjectRef),
            childDepth < depth
            -> objectTypeNameBool schema runtimeType = true
            -> selectionSetDirectiveFree mergedSubselections
            -> selectionSetLookupValid schema runtimeType mergedSubselections
            -> selectionSetSemanticsReady schema runtimeType mergedSubselections
            -> FieldMerge.fieldsInSetCanMerge schema runtimeType mergedSubselections
            -> Execution.executeSelectionSet schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType ref)
                  (normalizeSelectionSet schema runtimeType mergedSubselections)
                = Execution.executeSelectionSet schema resolvers variableValues
                    childDepth runtimeType (.object runtimeType ref)
                    mergedSubselections)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (withoutFieldSelectionsWithResponseName schema responseName rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (normalizeSelectionSet schema parentType
              (Selection.field responseName fieldName arguments [] subselections :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (Selection.field responseName fieldName arguments [] subselections
                :: rest) := by
  intro hobject hsource hfree hready hmerge hlookup hnormalizedFieldWithRest
    hrecursive htail
  let matching := fieldSelectionsWithResponseNameInScope schema parentType responseName rest
  let mergedSubselections := subselections ++ mergeSelectionSets matching
  let returnType := fieldDefinition.outputType.namedType
  let normalizedRest :=
    normalizeSelectionSet schema parentType
      (withoutFieldSelectionsWithResponseName schema responseName rest)
  have hparentObject :
      schema.objectType parentType :=
    objectType_of_objectTypeNameBool_eq_true schema hobject
  have hmergedFree :
      selectionSetDirectiveFree mergedSubselections := by
    simpa [mergedSubselections, matching] using
      selectionSetDirectiveFree_fieldHead_merged schema parentType responseName
        fieldName arguments subselections rest hfree
  have hreturnEq :
      ((schema.fieldReturnType? parentType fieldName).getD fieldName)
        =
      returnType := by
    simp [Schema.fieldReturnType?, hlookup, returnType]
  have hlookupValid :
      selectionSetLookupValid schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) :=
    selectionSetLookupValid_of_selectionSetSemanticsReady
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hready
  apply normalizeSelectionSet_executeSelectionSet_field_head_case
    schema resolvers variableValues depth parentType source responseName
    fieldName arguments subselections rest
    (if objectTypeNameBool schema returnType then
      normalizeSelectionSet schema returnType mergedSubselections
    else
      possibleTypeNormalizations schema (schema.getPossibleTypes returnType)
        mergedSubselections)
    fieldDefinition
  · exact hobject
  · exact hsource
  · exact hfree
  · exact hlookup
  · simp [matching, mergedSubselections, returnType]
  · simpa [matching, mergedSubselections, returnType, normalizedRest]
      using hnormalizedFieldWithRest
  · intro childDepth runtimeType ref hlt hinclude
    have hincludeReturn :
        schema.typeIncludesObjectBool returnType runtimeType = true := by
      simpa [hreturnEq] using hinclude
    have hmergedReady :
        selectionSetSemanticsReady schema runtimeType mergedSubselections := by
      simpa [mergedSubselections, matching] using
        selectionSetSemanticsReady_fieldHead_merged_of_child_object schema
          parentType responseName fieldName runtimeType arguments
          subselections rest fieldDefinition hparentObject hready
          hlookupValid hmerge hlookup hincludeReturn
    have hmergedLookup :
        selectionSetLookupValid schema runtimeType mergedSubselections := by
      exact
        selectionSetLookupValid_of_selectionSetSemanticsReady
          mergedSubselections hmergedReady
    have hmergedCanMerge :
        FieldMerge.fieldsInSetCanMerge schema runtimeType
          mergedSubselections := by
      simpa [mergedSubselections, matching] using
        fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
          schema parentType responseName fieldName runtimeType arguments
          subselections rest fieldDefinition hparentObject hlookupValid hmerge
          hlookup
    by_cases hreturnObject : objectTypeNameBool schema returnType = true
    · have hruntimeEq : runtimeType = returnType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hreturnObject hincludeReturn
      subst runtimeType
      simp [hreturnObject]
      exact hrecursive childDepth returnType ref hlt hreturnObject
        hmergedFree hmergedLookup hmergedReady hmergedCanMerge
    · have hreturnObjectFalse :
          objectTypeNameBool schema returnType = false := by
        cases hmatch : objectTypeNameBool schema returnType
        · rfl
        · contradiction
      have hpossible :
          runtimeType ∈ schema.getPossibleTypes returnType :=
        List.contains_iff_mem.mp hincludeReturn
      have hobjects :
          ∀ objectType, objectType ∈ schema.getPossibleTypes returnType ->
            objectTypeNameBool schema objectType = true := by
        intro objectType hobjectType
        exact objectTypeNameBool_eq_true_of_objectType schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema returnType objectType hobjectType)
      simp [hreturnObjectFalse]
      exact executeSelectionSet_possibleTypeNormalizations_runtime_branch
        schema resolvers variableValues childDepth runtimeType (ref := ref)
        (schema.getPossibleTypes returnType) mergedSubselections hobjects
        (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
          returnType)
        hpossible
        (hrecursive childDepth runtimeType ref hlt
          (hobjects runtimeType hpossible) hmergedFree hmergedLookup
          hmergedReady hmergedCanMerge)
  · exact htail

end GroundTypeNormalization

end NormalForm

end GraphQL
