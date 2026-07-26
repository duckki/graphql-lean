import Proofs.GraphQL.Theories.NormalForm.Shared.LookupValidity
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes
import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMerge

/-!
Semantic readiness facts for ground-type normalization proofs.
-/

namespace GraphQL

namespace NormalForm

mutual
  def selectionSemanticsReady (schema : Schema) (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ ∀ runtimeType,
              schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType runtimeType
                = true
              -> selectionSetSemanticsReady schema runtimeType selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetSemanticsReady schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetLookupValid schema typeCondition selectionSet
        ∧ (schema.typesOverlapBool parentType typeCondition = true
            -> selectionSetSemanticsReady schema parentType selectionSet)

  def selectionSetSemanticsReady (schema : Schema)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet -> selectionSemanticsReady schema parentType selection
end

theorem selectionSetSemanticsReady_nil (schema : Schema) (parentType : Name)
    : selectionSetSemanticsReady schema parentType [] := by
  simp [selectionSetSemanticsReady]

theorem selectionSetSemanticsReady_append
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : selectionSetSemanticsReady schema parentType left
      -> selectionSetSemanticsReady schema parentType right
      -> selectionSetSemanticsReady schema parentType (left ++ right) := by
  intro hleft hright
  unfold selectionSetSemanticsReady at hleft hright ⊢
  intro selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem selectionSetSemanticsReady_append_left
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : selectionSetSemanticsReady schema parentType (left ++ right)
      -> selectionSetSemanticsReady schema parentType left := by
  intro hready
  unfold selectionSetSemanticsReady at hready ⊢
  intro selection hselection
  exact hready selection (List.mem_append.mpr (Or.inl hselection))

theorem selectionSetSemanticsReady_append_right
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : selectionSetSemanticsReady schema parentType (left ++ right)
      -> selectionSetSemanticsReady schema parentType right := by
  intro hready
  unfold selectionSetSemanticsReady at hready ⊢
  intro selection hselection
  exact hready selection (List.mem_append.mpr (Or.inr hselection))

theorem selectionSetSemanticsReady_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetSemanticsReady schema parentType (selection :: selectionSet)
      -> selectionSetSemanticsReady schema parentType selectionSet := by
  intro hready
  unfold selectionSetSemanticsReady at hready ⊢
  intro candidate hcandidate
  exact hready candidate (List.mem_cons_of_mem selection hcandidate)

mutual
  theorem selectionLookupValid_of_selectionSemanticsReady
      {schema : Schema} {parentType : Name}
      : ∀ selection,
          selectionSemanticsReady schema parentType selection
          -> selectionLookupValid schema parentType selection
    | .field _responseName fieldName _arguments _directives _selectionSet,
      hready => by
        simp [selectionSemanticsReady, selectionLookupValid] at hready ⊢
        rcases hready with ⟨fieldDefinition, hlookup, _hchild⟩
        exact ⟨fieldDefinition, hlookup⟩
    | .inlineFragment none _directives selectionSet, hready => by
        have hbody :
            selectionSetSemanticsReady schema parentType selectionSet := by
          simpa [selectionSemanticsReady] using hready
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
            hbody
    | .inlineFragment (some _typeCondition) _directives selectionSet,
      hready => by
        have hpair :
            selectionSetLookupValid schema _typeCondition selectionSet
              ∧ (schema.typesOverlapBool parentType _typeCondition = true ->
                selectionSetSemanticsReady schema parentType selectionSet) := by
          simpa [selectionSemanticsReady] using hready
        simpa [selectionLookupValid] using hpair.1

  theorem selectionSetLookupValid_of_selectionSetSemanticsReady
      {schema : Schema} {parentType : Name}
      : ∀ selectionSet,
          selectionSetSemanticsReady schema parentType selectionSet
          -> selectionSetLookupValid schema parentType selectionSet
    | [], _hready => by
        exact selectionSetLookupValid_nil schema parentType
    | selection :: rest, hready => by
        have hhead :
            selectionSemanticsReady schema parentType selection := by
          unfold selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htail :
            selectionSetSemanticsReady schema parentType rest :=
          selectionSetSemanticsReady_tail hready
        simp [selectionSetLookupValid]
        constructor
        · exact selectionLookupValid_of_selectionSemanticsReady selection hhead
        · simpa [selectionSetLookupValid] using
            selectionSetLookupValid_of_selectionSetSemanticsReady rest htail
end

theorem selectionSetSemanticsReady_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetSemanticsReady schema parentType selection.subselections)
        -> selectionSetSemanticsReady schema parentType (mergeSelectionSets selections)
  | [], _hready => by
      simp [mergeSelectionSets, selectionSetSemanticsReady]
  | selection :: rest, hready => by
      simp [mergeSelectionSets]
      apply selectionSetSemanticsReady_append
      · exact hready selection (by simp)
      · exact selectionSetSemanticsReady_mergeSelectionSets_of_subselections rest
          (by
            intro candidate hcandidate
            exact hready candidate (by simp [hcandidate]))

theorem selectionSetSemanticsReady_mergeSelectionSets_of_field_subselections
    {schema : Schema} {parentType responseName : Name}
    (selections : List Selection)
    : (∀ selection,
        selection ∈ selections
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections)
      -> (∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ selections
            -> selectionSetSemanticsReady schema parentType subselections)
      -> selectionSetSemanticsReady schema parentType
          (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetSemanticsReady_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name)
    : ∀ parentType selectionSet,
        selectionSetSemanticsReady schema parentType selectionSet
        -> selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | _parentType, [], _hready => by
      simp [withoutFieldSelectionsWithResponseName, selectionSetSemanticsReady]
  | parentType, selection :: rest, hready => by
      have hhead :
          selectionSemanticsReady schema parentType selection := by
        unfold selectionSetSemanticsReady at hready
        exact hready selection (by simp)
      have htail :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            simpa [selectionSetSemanticsReady] using
              selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
                schema responseName parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse,
              selectionSetSemanticsReady]
            constructor
            · exact hhead
            · simpa [selectionSetSemanticsReady] using
                selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
                  schema responseName parentType rest htail
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [withoutFieldSelectionsWithResponseName,
                selectionSetSemanticsReady, selectionSemanticsReady]
              constructor
              · simpa [selectionSetSemanticsReady] using
                  selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
                    schema responseName parentType selectionSet
                    (by simpa [selectionSemanticsReady] using hhead)
              · simpa [selectionSetSemanticsReady] using
                  selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
                    schema responseName parentType rest htail
            | some typeCondition =>
                simp [withoutFieldSelectionsWithResponseName,
                  selectionSetSemanticsReady, selectionSemanticsReady]
                constructor
                · constructor
                  · have hheadPair :
                      selectionSetLookupValid schema typeCondition
                            selectionSet
                          ∧ (schema.typesOverlapBool parentType typeCondition =
                            true ->
                            selectionSetSemanticsReady schema parentType
                              selectionSet) := by
                      simpa [selectionSemanticsReady] using hhead
                    exact
                      selectionSetLookupValid_withoutFieldSelectionsWithResponseName_core
                        schema responseName typeCondition selectionSet
                        hheadPair.1
                  · intro hoverlap
                    have hheadPair :
                      selectionSetLookupValid schema typeCondition
                            selectionSet
                          ∧ (schema.typesOverlapBool parentType typeCondition =
                            true ->
                            selectionSetSemanticsReady schema parentType
                              selectionSet) := by
                      simpa [selectionSemanticsReady] using hhead
                    simpa [selectionSetSemanticsReady] using
                      selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
                        schema responseName parentType selectionSet
                        (hheadPair.2 hoverlap)
                · simpa [selectionSetSemanticsReady] using
                    selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
                      schema responseName parentType rest htail

theorem fieldSelectionsWithResponseNameInScope_field_semanticsReady
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet fieldName arguments directives subselections,
        selectionSetSemanticsReady schema parentType selectionSet
        -> Selection.field responseName fieldName arguments directives subselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet
        -> ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            ∧ ∀ runtimeType,
                schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType runtimeType
                  = true
                -> selectionSetSemanticsReady schema runtimeType subselections
  | [], fieldName, arguments, directives, subselections, _hready, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hready, hfield => by
      have hhead :
          selectionSemanticsReady schema parentType selection := by
        unfold selectionSetSemanticsReady at hready
        exact hready selection (by simp)
      have htail :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      cases selection with
      | field fieldResponseName sourceFieldName sourceArguments
          sourceDirectives sourceSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, hname] at hfield
            rcases hfield with hfield | hfield
            · rcases hfield with
                ⟨hresponseEq, hfieldEq, hargumentsEq, hdirectivesEq,
                  hsubselectionsEq⟩
              subst fieldResponseName
              subst sourceFieldName
              subst sourceArguments
              subst sourceDirectives
              subst sourceSubselections
              simpa [selectionSemanticsReady] using hhead
            · exact
                fieldSelectionsWithResponseNameInScope_field_semanticsReady schema
                  parentType responseName rest fieldName arguments directives
                  subselections htail hfield
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_semanticsReady schema
                parentType responseName rest fieldName arguments directives
                subselections htail hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbody :
                  selectionSetSemanticsReady schema parentType selectionSet := by
                simpa [selectionSemanticsReady] using hhead
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hfield | hfield
              · exact
                  fieldSelectionsWithResponseNameInScope_field_semanticsReady schema
                    parentType responseName selectionSet fieldName arguments
                    directives subselections hbody hfield
              · exact
                  fieldSelectionsWithResponseNameInScope_field_semanticsReady schema
                    parentType responseName rest fieldName arguments directives
                    subselections htail hfield
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hbody :
                    selectionSetSemanticsReady schema parentType
                      selectionSet := by
                  have hheadPair :
                    selectionSetLookupValid schema typeCondition selectionSet
                      ∧ (schema.typesOverlapBool parentType typeCondition =
                        true ->
                        selectionSetSemanticsReady schema parentType
                          selectionSet) := by
                    simpa [selectionSemanticsReady] using hhead
                  exact hheadPair.2 hoverlap
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hfield | hfield
                · exact
                    fieldSelectionsWithResponseNameInScope_field_semanticsReady schema
                      parentType responseName selectionSet fieldName
                      arguments directives subselections hbody hfield
                · exact
                    fieldSelectionsWithResponseNameInScope_field_semanticsReady schema
                      parentType responseName rest fieldName arguments
                      directives subselections htail hfield
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_semanticsReady schema
                    parentType responseName rest fieldName arguments directives
                    subselections htail hfield

mutual
  theorem selectionSemanticsReady_of_selectionValid_object
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> schema.objectType parentType
        -> ∀ selection,
            Validation.selectionValid schema variableDefinitions parentType selection
            -> selectionSemanticsReady schema parentType selection
    | hschema, hobject,
      .field _responseName fieldName _arguments _directives selectionSet,
      hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, hchild⟩
        simp [selectionSemanticsReady]
        refine ⟨fieldDefinition, hlookup, ?_⟩
        intro runtimeType hinclude
        have hpossible :
            runtimeType ∈
              schema.getPossibleTypes fieldDefinition.outputType.namedType :=
          List.contains_iff_mem.mp hinclude
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet :=
          fieldSelectionSetValid_child_of_possibleType hchild hpossible
        exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
          schema variableDefinitions fieldDefinition.outputType.namedType
          runtimeType hschema hpossible selectionSet hchildValid
      | hschema, hobject,
        .inlineFragment none _directives selectionSet, hvalid => by
          simpa [selectionSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_object schema
              variableDefinitions parentType hschema hobject selectionSet
              (Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid)
      | hschema, hobject,
        .inlineFragment (some typeCondition) _directives selectionSet,
        hvalid => by
          simp [selectionSemanticsReady]
          constructor
          · exact selectionSetLookupValid_of_selectionSetValid selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)
          · intro hoverlap
            have hpossible :
                parentType ∈ schema.getPossibleTypes typeCondition :=
              List.contains_iff_mem.mp
                (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
                  hoverlap)
            exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
              schema variableDefinitions typeCondition parentType hschema
              hpossible selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)

  theorem selectionSetSemanticsReady_of_selectionSetValid_object
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> schema.objectType parentType
        -> ∀ selectionSet,
            Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
            -> selectionSetSemanticsReady schema parentType selectionSet
    | _hschema, _hobject, [], _hvalid => by
        exact selectionSetSemanticsReady_nil schema parentType
    | hschema, hobject, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetSemanticsReady]
        constructor
        · exact selectionSemanticsReady_of_selectionValid_object schema
            variableDefinitions parentType hschema hobject selection hhead
        · simpa [selectionSetSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_object schema
              variableDefinitions parentType hschema hobject rest htail

  theorem selectionSemanticsReady_of_selectionValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> objectType ∈ schema.getPossibleTypes parentType
        -> ∀ selection,
            Validation.selectionValid schema variableDefinitions parentType selection
            -> selectionSemanticsReady schema objectType selection
    | hschema, hpossible,
      .field _responseName fieldName _arguments _directives selectionSet,
      hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨expectedDefinition, hexpected, _harguments, hchild⟩
        rcases
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
            hschema hpossible hexpected with
          ⟨implementationDefinition, himplementation⟩
        simp [selectionSemanticsReady]
        refine ⟨implementationDefinition, himplementation, ?_⟩
        intro runtimeType hincludeImplementation
        have hsubtype :
            schema.outputTypeSubtype implementationDefinition.outputType
              expectedDefinition.outputType :=
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
            hschema hpossible hexpected himplementation
        have hincludeExpected :
            schema.typeIncludesObjectBool
              expectedDefinition.outputType.namedType runtimeType = true :=
          typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
            hsubtype hincludeImplementation
        have hpossibleExpected :
            runtimeType ∈
              schema.getPossibleTypes expectedDefinition.outputType.namedType :=
          List.contains_iff_mem.mp hincludeExpected
        have hchildValid :
            Validation.selectionSetValid schema variableDefinitions
              expectedDefinition.outputType.namedType selectionSet :=
          fieldSelectionSetValid_child_of_possibleType hchild
            hpossibleExpected
        exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
          schema variableDefinitions expectedDefinition.outputType.namedType
          runtimeType hschema hpossibleExpected selectionSet hchildValid
      | hschema, hpossible,
        .inlineFragment none _directives selectionSet, hvalid => by
          simpa [selectionSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_possibleObject
              schema variableDefinitions parentType objectType hschema
              hpossible selectionSet
              (Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid)
      | hschema, hpossible,
        .inlineFragment (some typeCondition) _directives selectionSet,
        hvalid => by
          simp [selectionSemanticsReady]
          constructor
          · exact selectionSetLookupValid_of_selectionSetValid selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)
          · intro hoverlap
            have hobject :
                schema.objectType objectType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema parentType objectType hpossible
            have hfragmentPossible :
                objectType ∈ schema.getPossibleTypes typeCondition :=
              List.contains_iff_mem.mp
                (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
                  hoverlap)
            exact selectionSetSemanticsReady_of_selectionSetValid_possibleObject
              schema variableDefinitions typeCondition objectType hschema
              hfragmentPossible selectionSet
              (Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid)

  theorem selectionSetSemanticsReady_of_selectionSetValid_possibleObject
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (parentType objectType : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> objectType ∈ schema.getPossibleTypes parentType
        -> ∀ selectionSet,
            Validation.selectionSetValid schema variableDefinitions parentType
              selectionSet
            -> selectionSetSemanticsReady schema objectType selectionSet
    | _hschema, _hpossible, [], _hvalid => by
        exact selectionSetSemanticsReady_nil schema objectType
    | hschema, hpossible, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetSemanticsReady]
        constructor
        · exact
            selectionSemanticsReady_of_selectionValid_possibleObject schema
              variableDefinitions parentType objectType hschema hpossible
              selection hhead
        · simpa [selectionSetSemanticsReady] using
            selectionSetSemanticsReady_of_selectionSetValid_possibleObject
              schema variableDefinitions parentType objectType hschema
              hpossible rest htail
end

end NormalForm

end GraphQL
