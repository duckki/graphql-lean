import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Directives
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Shape

/-!
Field-merge facts for complete-normalization Boolean branches.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem normalizedSelectionSetFieldsCanMerge_anyParent
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType mergeParent : Name} {selectionSet : List Selection}
    : GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema mergeParent selectionSet := by
  intro hvalid
  exact fieldsInSetCanMerge_append_left schema mergeParent selectionSet
    selectionSet (hvalid.fieldsCanMergeSelf mergeParent)

theorem fieldsForNameCanMerge_of_sameParent_sameSelection_source
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {leftParent rightParent : Name}
    {leftSet rightSet : List Selection}
    {left right sourceLeft sourceRight : FieldMerge.ScopedField}
    : left ∈ FieldMerge.collectFields schema leftParent leftSet
      -> right ∈ FieldMerge.collectFields schema rightParent rightSet
      -> scopedFieldSameSelection left sourceLeft
      -> scopedFieldSameSelection right sourceRight
      -> left.parentType = right.parentType
      -> sourceLeft.responseName = sourceRight.responseName
      -> (sourceLeft.parentType = sourceRight.parentType
          ∨ ¬ schema.objectType sourceLeft.parentType
          ∨ ¬ schema.objectType sourceRight.parentType)
      -> FieldMerge.fieldsForNameCanMerge schema sourceLeft sourceRight
      -> (∀ objectType,
            FieldMerge.fieldsInSetCanMerge schema objectType
              (left.selectionSet ++ right.selectionSet))
      -> FieldMerge.fieldsForNameCanMerge schema left right := by
  intro hleftMem hrightMem hleftSame hrightSame hparent
    hsourceResponse hsourceParents hsourceMerge hsubfields
  rcases hleftSame with
    ⟨hleftResponse, hleftField, hleftArguments, _hleftSelection⟩
  rcases hrightSame with
    ⟨hrightResponse, hrightField, hrightArguments, _hrightSelection⟩
  rcases
    FieldMerge.fieldsForNameCanMerge_identity hsourceMerge
      hsourceParents with
    ⟨hsourceField, hsourceArguments⟩
  have hfield :
      left.fieldName = right.fieldName :=
    hleftField.trans (hsourceField.trans hrightField.symm)
  have harguments :
      Argument.argumentsEquivalent left.arguments right.arguments := by
    simpa [hleftArguments, hrightArguments] using hsourceArguments
  have houtputEq :
      left.outputType = right.outputType :=
    fieldMerge_collectFields_outputType_eq_of_same_parent_field schema
      hleftMem hrightMem hparent hfield
  have hleftOutput :
      left.outputType.isOutputType schema := by
    rcases
      fieldMerge_collectFields_mem_lookupField_outputType schema leftParent
        leftSet left hleftMem with
      ⟨leftDefinition, hleftLookup, hleftOutputEq⟩
    rw [hleftOutputEq]
    exact
      SchemaWellFormedness.schemaWellFormed_lookupField_outputType
        hschema hleftLookup
  apply fieldsForNameCanMerge_of_sameOutput_subfields houtputEq
  · rw [← houtputEq]
    exact SchemaWellFormedness.sameTypeShape_refl schema left.outputType
      hleftOutput
  · intro _hparents
    exact ⟨hfield, harguments⟩
  · exact hsubfields left.outputType.namedType

theorem
    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
    (schema : Schema) (filterParent collectParent responseName : Name)
    : ∀ selectionSet fieldName arguments directives subselections,
        (schema.objectType filterParent
          -> schema.typeIncludesObjectBool collectParent filterParent = true)
        -> selectionSetLookupValid schema collectParent selectionSet
        -> Selection.field responseName fieldName arguments directives subselections
            ∈ fieldSelectionsWithResponseNameInScope schema filterParent responseName
                selectionSet
        -> ∃ scopedField,
            scopedField ∈ FieldMerge.collectFields schema collectParent selectionSet
            ∧ scopedField.responseName = responseName
            ∧ scopedField.fieldName = fieldName
            ∧ scopedField.arguments = arguments
            ∧ scopedField.selectionSet = subselections
            ∧ (schema.objectType filterParent
                -> schema.typeIncludesObjectBool scopedField.parentType filterParent
                    = true)
  | [], _fieldName, _arguments, _directives, _subselections,
      _hsourceScope, _hlookupValid, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, fieldName, arguments, directives, subselections,
      hsourceScope, hlookupValid, hfield => by
      have hheadLookup :
          selectionLookupValid schema collectParent selection := by
        unfold selectionSetLookupValid at hlookupValid
        exact hlookupValid selection (by simp)
      have htailLookup :
          selectionSetLookupValid schema collectParent rest :=
        selectionSetLookupValid_tail hlookupValid
      cases selection with
      | field fieldResponseName sourceFieldName sourceArguments
          sourceDirectives sourceSubselections =>
          simp [selectionLookupValid] at hheadLookup
          rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
          by_cases hname : fieldResponseName == responseName
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
              refine ⟨{
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  outputType := fieldDefinition.outputType,
                  selectionSet := subselections
                }, ?_, rfl, rfl, rfl, rfl, ?_⟩
              · simp [FieldMerge.collectFields, hlookup]
              · exact hsourceScope
            · rcases
                fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
                  schema filterParent collectParent responseName rest
                  fieldName arguments directives subselections hsourceScope
                  htailLookup hfield with
                ⟨scopedField, hscoped, hresponse, hfieldName,
                  harguments, hselectionSet, hscopedSource⟩
              refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                hselectionSet, hscopedSource⟩
              simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · exact False.elim (hname hmatch)
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            rcases
              fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
                schema filterParent collectParent responseName rest
                fieldName arguments directives subselections hsourceScope
                htailLookup hfield with
              ⟨scopedField, hscoped, hresponse, hfieldName, harguments,
                hselectionSet, hscopedSource⟩
            refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
              hselectionSet, hscopedSource⟩
            simpa [FieldMerge.collectFields, hlookup] using Or.inr hscoped
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hselectionLookup :
                  selectionSetLookupValid schema collectParent
                    selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hfield | hfield
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
                    schema filterParent collectParent responseName
                    selectionSet fieldName arguments directives
                    subselections hsourceScope hselectionLookup hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName,
                    harguments, hselectionSet, hscopedSource⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedSource⟩
                simp [FieldMerge.collectFields, hscoped]
              · rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
                    schema filterParent collectParent responseName rest
                    fieldName arguments directives subselections hsourceScope
                    htailLookup hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName,
                    harguments, hselectionSet, hscopedSource⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedSource⟩
                simp [FieldMerge.collectFields, hscoped]
          | some typeCondition =>
              have hselectionLookup :
                  selectionSetLookupValid schema typeCondition
                    selectionSet := by
                simpa [selectionLookupValid] using hheadLookup
              by_cases hoverlap :
                  schema.typesOverlapBool filterParent typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                have hfragmentSource :
                    schema.objectType filterParent ->
                      schema.typeIncludesObjectBool typeCondition
                        filterParent = true := by
                  intro hfilterObject
                  exact typeIncludesObjectBool_of_object_typesOverlapBool
                    schema hfilterObject hoverlap
                rcases hfield with hfield | hfield
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
                      schema filterParent typeCondition responseName
                      selectionSet fieldName arguments directives
                      subselections hfragmentSource hselectionLookup
                      hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName,
                      harguments, hselectionSet, hscopedSource⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName,
                    harguments, hselectionSet, hscopedSource⟩
                  simp [FieldMerge.collectFields, hscoped]
                · rcases
                    fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
                      schema filterParent collectParent responseName rest
                      fieldName arguments directives subselections
                      hsourceScope htailLookup hfield with
                    ⟨scopedField, hscoped, hresponse, hfieldName,
                      harguments, hselectionSet, hscopedSource⟩
                  refine ⟨scopedField, ?_, hresponse, hfieldName,
                    harguments, hselectionSet, hscopedSource⟩
                  simp [FieldMerge.collectFields, hscoped]
              · have hfalse :
                    schema.typesOverlapBool filterParent typeCondition =
                      false := by
                  cases hmatch : schema.typesOverlapBool filterParent
                      typeCondition
                  · rfl
                  · exact False.elim (hoverlap hmatch)
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                rcases
                  fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid_source_object
                    schema filterParent collectParent responseName rest
                    fieldName arguments directives subselections
                    hsourceScope htailLookup hfield with
                  ⟨scopedField, hscoped, hresponse, hfieldName,
                    harguments, hselectionSet, hscopedSource⟩
                refine ⟨scopedField, ?_, hresponse, hfieldName, harguments,
                  hselectionSet, hscopedSource⟩
                simp [FieldMerge.collectFields, hscoped]

theorem fieldsInSetCanMerge_field_cons_pair_of_lookup_none
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument)
    (leftSelectionSet rightSelectionSet leftRest rightRest : List Selection)
    : schema.lookupField parentType fieldName = none
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftRest ++ rightRest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          ((Selection.field responseName fieldName arguments [] leftSelectionSet
              :: leftRest)
            ++ (Selection.field responseName fieldName arguments [] rightSelectionSet
                :: rightRest)) := by
  intro hlookup hrestPair
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    ((Selection.field responseName fieldName arguments []
        leftSelectionSet :: leftRest)
      ++
      (Selection.field responseName fieldName arguments []
        rightSelectionSet :: rightRest)) ?_
  dsimp
  intro left hleft right hright hresponse
  simp [FieldMerge.collectFields, hlookup, FieldMerge.collectFields_append]
    at hleft hright
  have hleftPair :
      left ∈ FieldMerge.collectFields schema parentType
        (leftRest ++ rightRest) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append.mpr hleft
  have hrightPair :
      right ∈ FieldMerge.collectFields schema parentType
        (leftRest ++ rightRest) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append.mpr hright
  exact FieldMerge.fieldsInSetCanMerge_pair hrestPair hleftPair hrightPair
    hresponse

theorem fieldsForNameCanMerge_sameField_of_subfields
    (schema : Schema)
    (parentType responseName fieldName : Name)
    (arguments : List Argument)
    (leftSelectionSet rightSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (∀ objectType,
            FieldMerge.fieldsInSetCanMerge schema objectType
              (leftSelectionSet ++ rightSelectionSet))
      -> FieldMerge.fieldsForNameCanMerge schema
          {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := fieldDefinition.outputType,
            selectionSet := leftSelectionSet
          }
          {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := fieldDefinition.outputType,
            selectionSet := rightSelectionSet
          } := by
  intro hschema hlookup hsubfields
  refine fieldsForNameCanMerge_of_sameOutput_subfields ?_ ?_ ?_ ?_
  · rfl
  · exact SchemaWellFormedness.sameTypeShape_refl schema
      fieldDefinition.outputType
      (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
        hschema hlookup)
  · intro _hparents
    exact ⟨rfl, GroundTypeNormalization.argumentsEquivalent_refl arguments⟩
  · exact hsubfields fieldDefinition.outputType.namedType

theorem fieldsInSetCanMerge_field_cons_pair_of_rest_responseNameFree
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument)
    (leftSelectionSet rightSelectionSet leftRest rightRest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> FieldMerge.fieldsForNameCanMerge schema
          {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := fieldDefinition.outputType,
            selectionSet := leftSelectionSet
          }
          {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := fieldDefinition.outputType,
            selectionSet := rightSelectionSet
          }
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] leftSelectionSet
            :: leftRest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] rightSelectionSet
            :: rightRest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftRest ++ rightRest)
      -> selectionsAllFields leftRest
      -> selectionsAllFields rightRest
      -> selectionSetResponseNameFree schema parentType responseName leftRest
      -> selectionSetResponseNameFree schema parentType responseName rightRest
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          ((Selection.field responseName fieldName arguments [] leftSelectionSet
              :: leftRest)
            ++ (Selection.field responseName fieldName arguments [] rightSelectionSet
                :: rightRest)) := by
  intro hlookup hheadMerge hleftMerge hrightMerge hrestPair
    hallLeft hallRight hleftFree hrightFree
  apply fieldsInSetCanMerge_append_of_pairwise
  · exact hleftMerge
  · exact hrightMerge
  · intro leftField hleft rightField hright hresponse
    simp [FieldMerge.collectFields, hlookup] at hleft hright
    rcases hleft with hleftHead | hleftRest
    · subst leftField
      rcases hright with hrightHead | hrightRest
      · subst rightField
        exact hheadMerge
      · have hrightNe :
            rightField.responseName ≠ responseName :=
          GroundTypeNormalization.collectFields_responseName_ne_of_allFields_responseNameFree
            schema parentType responseName rightRest rightField hallRight
            hrightFree hrightRest
        exact False.elim (hrightNe hresponse.symm)
    · rcases hright with hrightHead | hrightRest
      · subst rightField
        have hleftNe :
            leftField.responseName ≠ responseName :=
          GroundTypeNormalization.collectFields_responseName_ne_of_allFields_responseNameFree
            schema parentType responseName leftRest leftField hallLeft
            hleftFree hleftRest
        exact False.elim (hleftNe hresponse)
      · exact FieldMerge.fieldsInSetCanMerge_pair hrestPair
          (by
            rw [FieldMerge.collectFields_append]
            exact List.mem_append_left
              (FieldMerge.collectFields schema parentType rightRest)
              hleftRest)
          (by
            rw [FieldMerge.collectFields_append]
            exact List.mem_append_right
              (FieldMerge.collectFields schema parentType leftRest)
              hrightRest)
          hresponse

theorem fieldsInSetCanMerge_field_cons_pair_of_subfields_and_rest
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument)
    (leftSelectionSet rightSelectionSet leftRest rightRest : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> (∀ objectType,
            FieldMerge.fieldsInSetCanMerge schema objectType
              (leftSelectionSet ++ rightSelectionSet))
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] leftSelectionSet
            :: leftRest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments [] rightSelectionSet
            :: rightRest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftRest ++ rightRest)
      -> selectionsAllFields leftRest
      -> selectionsAllFields rightRest
      -> selectionSetResponseNameFree schema parentType responseName leftRest
      -> selectionSetResponseNameFree schema parentType responseName rightRest
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          ((Selection.field responseName fieldName arguments [] leftSelectionSet
              :: leftRest)
            ++ (Selection.field responseName fieldName arguments [] rightSelectionSet
                :: rightRest)) := by
  intro hschema hsubfields hleftMerge hrightMerge hrestPair hallLeft
    hallRight hleftFree hrightFree
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      exact fieldsInSetCanMerge_field_cons_pair_of_lookup_none schema
        parentType responseName fieldName arguments leftSelectionSet
        rightSelectionSet leftRest rightRest hlookup hrestPair
  | some fieldDefinition =>
      have hheadMerge :
          FieldMerge.fieldsForNameCanMerge schema
            {
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := leftSelectionSet
            }
            {
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := rightSelectionSet
            } :=
        fieldsForNameCanMerge_sameField_of_subfields schema parentType
          responseName fieldName arguments leftSelectionSet
          rightSelectionSet fieldDefinition hschema hlookup hsubfields
      exact fieldsInSetCanMerge_field_cons_pair_of_rest_responseNameFree
        schema parentType responseName fieldName arguments
        leftSelectionSet rightSelectionSet leftRest rightRest fieldDefinition
        hlookup hheadMerge hleftMerge hrightMerge hrestPair hallLeft
        hallRight hleftFree hrightFree

theorem collectFields_flatten_mem (schema : Schema) (parentType : Name)
    : ∀ selectionSets scopedField,
        scopedField
          ∈ FieldMerge.collectFields schema parentType (List.flatten selectionSets)
        -> ∃ selectionSet,
            selectionSet ∈ selectionSets
            ∧ scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
  | [], scopedField, hfield => by
      simp [FieldMerge.collectFields] at hfield
  | selectionSet :: rest, scopedField, hfield => by
      simp [List.flatten] at hfield
      rw [FieldMerge.collectFields_append] at hfield
      rcases List.mem_append.mp hfield with hhead | htail
      · exact ⟨selectionSet, by simp, hhead⟩
      · rcases collectFields_flatten_mem schema parentType rest scopedField
            htail with
          ⟨sourceSet, hsourceSet, hsourceMem⟩
        exact ⟨sourceSet, by simp [hsourceSet], hsourceMem⟩

theorem fieldsInSetCanMerge_flatten_of_pairwise
    (schema : Schema) (parentType : Name)
    (selectionSets : List (List Selection))
    : (∀ leftSet,
        leftSet ∈ selectionSets
        -> ∀ rightSet,
            rightSet ∈ selectionSets
            -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet))
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (List.flatten selectionSets) := by
  intro hpairwise
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (List.flatten selectionSets) ?_
  dsimp
  intro left hleft right hright hresponse
  rcases collectFields_flatten_mem schema parentType selectionSets left
      hleft with
    ⟨leftSet, hleftSet, hleftMem⟩
  rcases collectFields_flatten_mem schema parentType selectionSets right
      hright with
    ⟨rightSet, hrightSet, hrightMem⟩
  have hpair :
      FieldMerge.fieldsInSetCanMerge schema parentType
        (leftSet ++ rightSet) :=
    hpairwise leftSet hleftSet rightSet hrightSet
  have hleftPair :
      left ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_left
      (FieldMerge.collectFields schema parentType rightSet)
      hleftMem
  have hrightPair :
      right ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_right
      (FieldMerge.collectFields schema parentType leftSet)
      hrightMem
  exact FieldMerge.fieldsInSetCanMerge_pair hpair hleftPair hrightPair
    hresponse

theorem completeNormalizeBranchPair_fieldsInSetCanMerge
    (schema : Schema) (parentType : Name)
    (leftCase rightCase : BoolCase)
    (leftBody rightBody : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftBody ++ rightBody)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          ((match leftBody with
            | [] => []
            | selection :: rest =>
                wrapWithBoolCase leftCase (selection :: rest))
            ++ (match rightBody with
                | [] => []
                | selection :: rest =>
                    wrapWithBoolCase rightCase (selection :: rest))) := by
  intro hmerge
  cases leftBody with
  | nil =>
      cases rightBody with
      | nil =>
          simpa using hmerge
      | cons right rest =>
          have hrightMerge :
              FieldMerge.fieldsInSetCanMerge schema parentType
                (right :: rest) := by
            simpa using hmerge
          simpa using
            fieldsInSetCanMerge_wrapWithBoolCase schema parentType
              rightCase (right :: rest) hrightMerge
  | cons left restLeft =>
      cases rightBody with
      | nil =>
          have hleftMerge :
              FieldMerge.fieldsInSetCanMerge schema parentType
                (left :: restLeft) := by
            simpa using hmerge
          simpa using
            fieldsInSetCanMerge_wrapWithBoolCase schema parentType
              leftCase (left :: restLeft) hleftMerge
      | cons right restRight =>
          simpa using
            fieldsInSetCanMerge_wrapWithBoolCase_pair schema parentType
              leftCase rightCase (left :: restLeft) (right :: restRight)
              hmerge

theorem completeNormalizeRootSelectionSet_fieldsInSetCanMerge_of_branchPairs
    (schema : Schema) (variables : List BoolVar)
    (parentType : Name) (selectionSet : List Selection)
    : (∀ leftCase,
        leftCase ∈ allBoolCases variables
        -> ∀ rightCase,
            rightCase ∈ allBoolCases variables
            -> FieldMerge.fieldsInSetCanMerge schema parentType
                (normalizeSelectionSet schema parentType
                    (filterSelectionSetBoolCase leftCase selectionSet)
                  ++ normalizeSelectionSet schema parentType
                      (filterSelectionSetBoolCase rightCase selectionSet)))
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (completeNormalizeRootSelectionSet schema variables parentType
            selectionSet) := by
  intro hbranchPairs
  unfold completeNormalizeRootSelectionSet
  apply fieldsInSetCanMerge_flatten_of_pairwise
  intro leftSet hleftSet rightSet hrightSet
  simp only [List.mem_map] at hleftSet hrightSet
  rcases hleftSet with ⟨leftCase, hleftCaseMem, hleftEq⟩
  rcases hrightSet with ⟨rightCase, hrightCaseMem, hrightEq⟩
  subst leftSet
  subst rightSet
  exact completeNormalizeBranchPair_fieldsInSetCanMerge schema parentType
    leftCase rightCase
    (normalizeSelectionSet schema parentType
      (filterSelectionSetBoolCase leftCase selectionSet))
    (normalizeSelectionSet schema parentType
      (filterSelectionSetBoolCase rightCase selectionSet))
    (hbranchPairs leftCase hleftCaseMem rightCase hrightCaseMem)

end CompleteNormalization

end NormalForm

end GraphQL
