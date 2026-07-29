import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness
import Proofs.GraphQL.Theories.NormalForm.Shared.ResponseNameFree

/-!
Normality, ground-typedness, and non-redundancy proofs for ground-type normalization.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem objectTypeNameBool_eq_true_of_objectType_forNormality
    (schema : Schema) {typeName : Name}
    : schema.objectType typeName -> objectTypeNameBool schema typeName = true := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  simp [objectTypeNameBool, hlookup]

def possibleTypeNormalizations (schema : Schema)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : List Selection :=
  possibleTypes.filterMap
    (fun objectType =>
      match normalizeSelectionSet schema objectType selectionSet with
      | [] => none
      | selection :: rest =>
          some (Selection.inlineFragment (some objectType) [] (selection :: rest)))

abbrev normalizedFieldWithRest
    (schema : Schema) (returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections normalizedRest : List Selection)
    : List Selection :=
  normalizedField schema returnType responseName fieldName arguments directives
    normalizedSubselections
  :: normalizedRest

theorem selectionSetDirectiveFree_normalizedFieldWithRest
    (schema : Schema) (returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections normalizedRest : List Selection)
    : selectionDirectiveFree
        (Selection.field responseName fieldName arguments directives
          normalizedSubselections)
      -> selectionSetDirectiveFree normalizedRest
      -> selectionSetDirectiveFree
          (normalizedFieldWithRest schema returnType responseName fieldName
            arguments directives normalizedSubselections normalizedRest) := by
  intro hfield hrest
  simpa [normalizedFieldWithRest, normalizedField, selectionSetDirectiveFree]
    using And.intro hfield hrest

theorem selectionsAllFields_normalizedFieldWithRest
    (schema : Schema) (returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections normalizedRest : List Selection)
    : selectionsAllFields normalizedRest
      -> selectionsAllFields
          (normalizedFieldWithRest schema returnType responseName fieldName
            arguments directives normalizedSubselections normalizedRest) := by
  intro hrest selection hmem
  simp [normalizedFieldWithRest, normalizedField] at hmem
  cases hmem with
  | inl hhead =>
      subst selection
      simp [Selection.isField]
  | inr htail =>
      exact hrest selection htail

theorem selectionSetGroundTyped_normalizedFieldWithRest
    (schema : Schema) (parentType returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections normalizedRest : List Selection)
    : objectTypeNameBool schema parentType = true
      -> schema.fieldReturnType? parentType fieldName = some returnType
      -> selectionSetGroundTyped schema returnType normalizedSubselections
      -> selectionSetGroundTyped schema parentType normalizedRest
      -> selectionsAllFields normalizedRest
      -> selectionSetGroundTyped schema parentType
          (normalizedFieldWithRest schema returnType responseName fieldName
            arguments directives normalizedSubselections normalizedRest) := by
  intro hparentObject hreturn hsub hrest hrestFields
  have hrestGround := hrest
  unfold selectionSetGroundTyped at hrestGround
  unfold selectionSetGroundTyped
  simp [hparentObject]
  constructor
  · exact
      selectionsAllFields_normalizedFieldWithRest schema returnType
        responseName fieldName arguments directives normalizedSubselections
        normalizedRest hrestFields
  · constructor
    · unfold selectionGroundTyped
      exact ⟨returnType, hreturn, hsub⟩
    · intro selection htail
      exact hrestGround.2 selection htail

theorem selectionSetResponseNameFree_normalizedFieldWithRest (schema : Schema)
    (parentType returnType responseName fieldResponseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections normalizedRest : List Selection)
    : selectionResponseNameFree schema parentType responseName
        (Selection.field fieldResponseName fieldName arguments directives
          normalizedSubselections)
      -> selectionSetResponseNameFree schema parentType responseName normalizedRest
      -> selectionSetResponseNameFree schema parentType responseName
          (normalizedFieldWithRest schema returnType fieldResponseName fieldName
            arguments directives normalizedSubselections normalizedRest) := by
  intro hfield hrest
  simpa [normalizedFieldWithRest, normalizedField] using
    selectionSetResponseNameFree_cons hfield hrest

theorem selectionSetDirectiveFree_possibleTypeNormalizations
    (schema : Schema)
    (possibleTypes : List Name) {selectionSet : List Selection}
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> selectionSetDirectiveFree
            (normalizeSelectionSet schema objectType selectionSet))
      -> selectionSetDirectiveFree
          (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  intro hnormalize
  induction possibleTypes with
  | nil =>
      exact selectionSetDirectiveFree_nil
  | cons objectType rest ih =>
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [possibleTypeNormalizations, hnormalized]
          exact ih (fun candidate hcandidate =>
            hnormalize candidate
              (List.mem_cons_of_mem objectType hcandidate))
      | cons selection restSelection =>
          have hheadFree :
              selectionSetDirectiveFree (selection :: restSelection) := by
            simpa [hnormalized] using hnormalize objectType (by simp)
          simp [possibleTypeNormalizations, hnormalized]
          exact ⟨⟨rfl, hheadFree⟩,
            ih (fun candidate hcandidate =>
              hnormalize candidate
                (List.mem_cons_of_mem objectType hcandidate))⟩

theorem normalizeSelectionSet_directiveFree (schema : Schema)
    : ∀ parentType selectionSet,
        selectionSetDirectiveFree selectionSet
        -> selectionSetDirectiveFree
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
    intro hfree
    simpa [normalizeSelectionSet] using selectionSetDirectiveFree_nil
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
    intro hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have hfilteredRestFree :
        selectionSetDirectiveFree
          (withoutFieldSelectionsWithResponseName schema responseName rest) :=
      withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest hrestFree
    simpa [normalizeSelectionSet, hlookup] using hrest hfilteredRestFree
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
    intro hfree
    let normalizedSubselections :=
      if objectTypeNameBool schema returnType then
        normalizeSelectionSet schema returnType mergedSubselections
      else
        possibleTypeNormalizations schema
          (schema.getPossibleTypes returnType) mergedSubselections
    have hselectionFree :=
      selectionSetDirectiveFree_head hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have hdirectives : directives = [] := hselectionFree.1
    subst directives
    have hsubselectionsFree : selectionSetDirectiveFree selectionSet :=
      hselectionFree.2
    have hfilteredRestFree :
        selectionSetDirectiveFree
          (withoutFieldSelectionsWithResponseName schema responseName rest) :=
      withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest hrestFree
    have hnormalizedRest :
        selectionSetDirectiveFree
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)) :=
      hrest hfilteredRestFree
    have hmatchingFree : selectionSetDirectiveFree matching := by
      subst matching
      exact fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
        responseName rest hrestFree
    have hmergedSubselectionsFree :
        selectionSetDirectiveFree mergedSubselections := by
      subst mergedSubselections
      exact selectionSetDirectiveFree_append hsubselectionsFree
        (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
    have hnormalizedSubselections :
        selectionSetDirectiveFree
          (if objectTypeNameBool schema returnType then
            normalizeSelectionSet schema returnType mergedSubselections
          else
            possibleTypeNormalizations schema
              (schema.getPossibleTypes returnType)
              mergedSubselections) := by
      by_cases hobject : objectTypeNameBool schema returnType = true
      · simp [hobject]
        exact hmerged hmergedSubselectionsFree
      · have hfalse : objectTypeNameBool schema returnType = false := by
          cases hmatch : objectTypeNameBool schema returnType
          · rfl
          · contradiction
        simp [hfalse]
        exact selectionSetDirectiveFree_possibleTypeNormalizations
          schema (schema.getPossibleTypes returnType)
          (fun objectType _hobjectType =>
            hpossible objectType hmergedSubselectionsFree)
    have hnormalizedField :
        selectionDirectiveFree
          (Selection.field responseName fieldName arguments []
            normalizedSubselections) := by
      exact ⟨rfl, hnormalizedSubselections⟩
    rw [normalizeSelectionSet.eq_2, hlookup]
    change selectionSetDirectiveFree
      (normalizedFieldWithRest schema returnType responseName fieldName
        arguments [] normalizedSubselections
        (normalizeSelectionSet schema parentType
          (withoutFieldSelectionsWithResponseName schema responseName rest)))
    exact
      selectionSetDirectiveFree_normalizedFieldWithRest schema returnType
        responseName fieldName arguments [] normalizedSubselections
        (normalizeSelectionSet schema parentType
          (withoutFieldSelectionsWithResponseName schema responseName rest))
        hnormalizedField hnormalizedRest
  | case4 parentType rest directives selectionSet happend =>
    intro hfree
    have hselectionFree :=
      selectionSetDirectiveFree_head hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have happendFree :
        selectionSetDirectiveFree (selectionSet ++ rest) :=
      selectionSetDirectiveFree_append hselectionFree.2 hrestFree
    simpa [normalizeSelectionSet] using happend happendFree
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
    intro hfree
    have hselectionFree :=
      selectionSetDirectiveFree_head hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have happendFree :
        selectionSetDirectiveFree (selectionSet ++ rest) :=
      selectionSetDirectiveFree_append hselectionFree.2 hrestFree
    simpa [normalizeSelectionSet, hoverlap] using happend happendFree
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
    intro hfree
    have hrestFree :=
      selectionSetDirectiveFree_tail hfree
    have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
      cases hmatch : schema.typesOverlapBool parentType typeCondition
      · rfl
      · contradiction
    simpa [normalizeSelectionSet, hfalse] using hrest hrestFree

theorem normalizeOperation_directiveFree (schema : Schema) (operation : Operation)
    : operationDirectiveFree operation
      -> operationDirectiveFree (normalizeOperation schema operation) := by
  intro hfree
  simp [normalizeOperation, operationDirectiveFree]
  exact normalizeSelectionSet_directiveFree schema (operation.rootType schema)
    operation.selectionSet hfree

theorem normalizeSelectionSet_allFields (schema : Schema)
    : ∀ parentType selectionSet,
        selectionsAllFields (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro selection hmem
      simp [normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      rw [normalizeSelectionSet.eq_2, hlookup]
      change selectionsAllFields
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      exact
        selectionsAllFields_normalizedFieldWithRest schema returnType
          responseName fieldName arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest))
          hrest
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest

theorem possibleTypeNormalizations_allInlineFragments
    (schema : Schema)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : selectionsAllInlineFragments
        (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  intro selection hmem
  unfold possibleTypeNormalizations at hmem
  rw [List.mem_filterMap] at hmem
  rcases hmem with ⟨objectType, _hobjectType, hselection⟩
  cases hnormalized :
      normalizeSelectionSet schema objectType selectionSet with
  | nil =>
      simp [hnormalized] at hselection
  | cons head tail =>
      simp [hnormalized] at hselection
      subst selection
      simp [Selection.isInlineFragment]

theorem possibleTypeNormalizations_groundTyped
    (schema : Schema)
    (parentType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection)
    (hparentAbstract : objectTypeNameBool schema parentType = false)
    (hpossible : ∀ objectType, objectType ∈ possibleTypes -> schema.objectType objectType)
    (_hincludes
      : ∀ objectType,
          objectType ∈ possibleTypes
          -> schema.typeIncludesObjectBool parentType objectType = true)
    (hnormalize
      : ∀ objectType,
          objectType ∈ possibleTypes
          -> selectionSetGroundTyped schema objectType
              (normalizeSelectionSet schema objectType selectionSet))
    : selectionSetGroundTyped schema parentType
        (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  unfold selectionSetGroundTyped
  simp [hparentAbstract]
  constructor
  · exact
      possibleTypeNormalizations_allInlineFragments schema possibleTypes
        selectionSet
  · intro selection hmem
    unfold possibleTypeNormalizations at hmem
    rw [List.mem_filterMap] at hmem
    rcases hmem with ⟨objectType, hobjectType, hselection⟩
    cases hnormalized :
        normalizeSelectionSet schema objectType selectionSet with
    | nil =>
        simp [hnormalized] at hselection
    | cons head tail =>
        simp [hnormalized] at hselection
        subst selection
        unfold selectionGroundTyped
        exact ⟨
          hpossible objectType hobjectType,
          by
            simpa [hnormalized] using
              hnormalize objectType hobjectType⟩

theorem normalizeSelectionSet_groundTyped (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
        objectTypeNameBool schema parentType = true
        -> selectionSetGroundTyped schema parentType
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet hparentObject
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      unfold selectionSetGroundTyped
      simp [hparentObject]
      constructor
      · exact normalizeSelectionSet_allFields schema parentType []
      · intro selection hmem
        simp [normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest hparentObject
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hsubselectionsGround :
          selectionSetGroundTyped schema returnType normalizedSubselections := by
        unfold normalizedSubselections
        by_cases hobject : objectTypeNameBool schema returnType = true
        · simp [hobject]
          exact hmerged hobject
        · have hfalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hfalse]
          exact possibleTypeNormalizations_groundTyped schema
            returnType
            (schema.getPossibleTypes returnType) mergedSubselections
            hfalse
            (fun objectType hobjectType =>
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType)
            (fun objectType hobjectType =>
              List.contains_iff_mem.mpr hobjectType)
            (fun objectType hobjectType =>
              hpossible objectType
                (objectTypeNameBool_eq_true_of_objectType_forNormality schema
                  (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                    hschema returnType objectType hobjectType)))
      have hreturn :
          schema.fieldReturnType? parentType fieldName = some returnType := by
        simp [Schema.fieldReturnType?, hlookup, returnType]
      rw [normalizeSelectionSet.eq_2, hlookup]
      change selectionSetGroundTyped schema parentType
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      exact
        selectionSetGroundTyped_normalizedFieldWithRest schema parentType returnType
          responseName fieldName arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest))
          hparentObject hreturn hsubselectionsGround (hrest hparentObject)
          (normalizeSelectionSet_allFields schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest))
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend hparentObject
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend hparentObject
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest hparentObject

theorem normalizeSelectionSet_responseNameFree (schema : Schema)
    : ∀ parentType responseName selectionSet,
        selectionSetResponseNameFree schema parentType responseName selectionSet
        -> selectionSetResponseNameFree schema parentType responseName
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType responseName selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _hfree
      simpa [normalizeSelectionSet] using
        selectionSetResponseNameFree_nil schema parentType responseName
  | case2 parentType rest fieldResponseName fieldName arguments directives
      selectionSet hlookup hrest =>
      intro hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hfiltered :=
        withoutFieldSelectionsWithResponseName_preserves_responseNameFree schema
          fieldResponseName parentType responseName rest htail
      simpa [normalizeSelectionSet, hlookup] using hrest hfiltered
  | case3 parentType rest fieldResponseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro hfree
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hhead := selectionSetResponseNameFree_head hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hfiltered :=
        withoutFieldSelectionsWithResponseName_preserves_responseNameFree schema
          fieldResponseName parentType responseName rest htail
      have hnormalizedRest := hrest hfiltered
      have hnormalizedHead :
          selectionResponseNameFree schema parentType responseName
            (Selection.field fieldResponseName fieldName arguments directives
              normalizedSubselections) := by
        simpa [selectionResponseNameFree] using hhead
      rw [normalizeSelectionSet.eq_2, hlookup]
      change selectionSetResponseNameFree schema parentType responseName
        (normalizedFieldWithRest schema returnType fieldResponseName fieldName
          arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema fieldResponseName rest)))
      exact
        selectionSetResponseNameFree_normalizedFieldWithRest schema parentType
          returnType responseName fieldResponseName fieldName arguments
          directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema fieldResponseName rest))
          hnormalizedHead hnormalizedRest
  | case4 parentType rest directives selectionSet happend =>
      intro hfree
      have hhead := selectionSetResponseNameFree_head hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hsubselections :
          selectionSetResponseNameFree schema parentType responseName
            selectionSet := by
        simpa [selectionResponseNameFree] using hhead
      have happendFree :
          selectionSetResponseNameFree schema parentType responseName
            (selectionSet ++ rest) := by
        exact selectionSetResponseNameFree_append hsubselections htail
      simpa [normalizeSelectionSet] using happend happendFree
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      intro hfree
      have hhead := selectionSetResponseNameFree_head hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hheadApplies :
          schema.typesOverlapBool parentType typeCondition = true ->
            selectionSetResponseNameFree schema parentType responseName
              selectionSet := by
        simpa [selectionResponseNameFree] using hhead
      have hsubselections :
          selectionSetResponseNameFree schema parentType responseName
            selectionSet := by
        exact hheadApplies hoverlap
      have happendFree :
          selectionSetResponseNameFree schema parentType responseName
            (selectionSet ++ rest) :=
        selectionSetResponseNameFree_append hsubselections htail
      simpa [normalizeSelectionSet, hoverlap] using happend happendFree
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      intro hfree
      have htail := selectionSetResponseNameFree_tail hfree
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest htail

theorem responseName_not_mem_filterMap_of_responseNameFree
    {schema : Schema} {parentType responseName : Name}
    : ∀ selectionSet,
        selectionSetResponseNameFree schema parentType responseName selectionSet
        -> responseName ∉ selectionSet.filterMap Selection.responseName? := by
  intro selectionSet
  induction selectionSet with
  | nil =>
      intro _hfree
      simp
  | cons selection rest ih =>
      intro hfree
      have hhead := selectionSetResponseNameFree_head hfree
      have hrest := selectionSetResponseNameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hheadNe : fieldResponseName ≠ responseName := by
            simpa [selectionResponseNameFree] using hhead
          simp [Selection.responseName?, ih hrest]
          intro heq
          exact hheadNe heq.symm
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.responseName?, ih hrest]

theorem normalizeSelectionSet_without_responseName_not_mem
    (schema : Schema) (parentType responseName : Name)
    (selectionSet : List Selection)
    : responseName
      ∉ (normalizeSelectionSet schema parentType
          (withoutFieldSelectionsWithResponseName schema responseName
            selectionSet)).filterMap
          Selection.responseName? := by
  apply responseName_not_mem_filterMap_of_responseNameFree
  exact normalizeSelectionSet_responseNameFree schema parentType responseName
    (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
    (withoutFieldSelectionsWithResponseName_responseNameFree schema parentType
      responseName selectionSet)

theorem responseNamesNodup_normalizedFieldWithRest
    (schema : Schema) (returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections normalizedRest : List Selection)
    : responseName ∉ normalizedRest.filterMap Selection.responseName?
      -> responseNamesNodup normalizedRest
      -> responseNamesNodup
          (normalizedFieldWithRest schema returnType responseName fieldName
            arguments directives normalizedSubselections normalizedRest) := by
  intro hnotMem hnodup
  unfold responseNamesNodup at hnodup ⊢
  simpa [normalizedFieldWithRest, normalizedField, Selection.responseName?] using
    List.nodup_cons.mpr ⟨hnotMem, hnodup⟩

theorem normalizeSelectionSet_responseNamesNodup (schema : Schema)
    : ∀ parentType selectionSet,
        responseNamesNodup (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      simp [normalizeSelectionSet, responseNamesNodup]
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have htailNoResponseName :=
        normalizeSelectionSet_without_responseName_not_mem schema parentType
          responseName rest
      have htailNodup := hrest
      rw [normalizeSelectionSet.eq_2, hlookup]
      change responseNamesNodup
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      exact
        responseNamesNodup_normalizedFieldWithRest schema returnType
          responseName fieldName arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest))
          htailNoResponseName htailNodup
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest

theorem inlineFragmentTypeConditionsNodup_of_selectionsAllFields
    {selectionSet : List Selection}
    : selectionsAllFields selectionSet
      -> inlineFragmentTypeConditionsNodup selectionSet := by
  intro hfields
  induction selectionSet with
  | nil =>
      simp [inlineFragmentTypeConditionsNodup]
  | cons selection rest ih =>
      have hhead : Selection.isField selection := hfields selection (by simp)
      have hrest : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hfields candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          simpa [inlineFragmentTypeConditionsNodup, inlineFragmentTypeCondition?]
            using ih hrest
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hhead

theorem selectionSetNonRedundant_selection {selectionSet : List Selection}
    {selection : Selection}
    : selectionSetNonRedundant selectionSet
      -> selection ∈ selectionSet
      -> selectionNonRedundant selection := by
  intro hnonRedundant hselection
  unfold selectionSetNonRedundant at hnonRedundant
  exact hnonRedundant.2.2 selection hselection

theorem selectionSetNonRedundant_normalizedFieldWithRest
    (schema : Schema) (returnType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (normalizedSubselections normalizedRest : List Selection)
    : responseName ∉ normalizedRest.filterMap Selection.responseName?
      -> selectionsAllFields normalizedRest
      -> selectionSetNonRedundant normalizedSubselections
      -> selectionSetNonRedundant normalizedRest
      -> selectionSetNonRedundant
          (normalizedFieldWithRest schema returnType responseName fieldName
            arguments directives normalizedSubselections normalizedRest) := by
  intro hnotMem hrestFields hsub hrest
  have hrestNonRedundant := hrest
  unfold selectionSetNonRedundant at hrestNonRedundant
  unfold selectionSetNonRedundant
  constructor
  · exact responseNamesNodup_normalizedFieldWithRest schema returnType
      responseName fieldName arguments directives normalizedSubselections
      normalizedRest hnotMem hrestNonRedundant.1
  · constructor
    · exact inlineFragmentTypeConditionsNodup_of_selectionsAllFields
        (selectionsAllFields_normalizedFieldWithRest schema returnType
          responseName fieldName arguments directives normalizedSubselections
          normalizedRest hrestFields)
    · intro selection hselection
      simp [normalizedFieldWithRest, normalizedField] at hselection
      cases hselection with
      | inl hhead =>
          subst selection
          unfold selectionNonRedundant
          exact hsub
      | inr htail =>
          exact selectionSetNonRedundant_selection hrest htail

theorem possibleTypeNormalizations_responseNamesNodup
    (schema : Schema) (possibleTypes : List Name)
    (selectionSet : List Selection)
    : responseNamesNodup
        (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  have hfilterNone :
      ∀ names : List Name,
        ((possibleTypeNormalizations schema names selectionSet).filterMap
          Selection.responseName?).Nodup := by
    intro names
    induction names with
    | nil => simp [possibleTypeNormalizations]
    | cons name rest ih =>
        cases hnormalized :
            normalizeSelectionSet schema name selectionSet with
      | nil =>
            simpa [possibleTypeNormalizations, hnormalized] using ih
      | cons head tail =>
            simpa [possibleTypeNormalizations, hnormalized,
              Selection.responseName?] using ih
  simpa [responseNamesNodup] using
    hfilterNone possibleTypes

theorem possibleTypeNormalizations_inlineFragmentTypeConditionsNodup
    (schema : Schema) (possibleTypes : List Name)
    (selectionSet : List Selection)
    : possibleTypes.Nodup
      -> inlineFragmentTypeConditionsNodup
          (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  intro hnodup
  induction possibleTypes with
  | nil =>
      simp [inlineFragmentTypeConditionsNodup, possibleTypeNormalizations]
  | cons objectType rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hobjectNotMem : objectType ∉ rest := hparts.1
      have hrestNodup : rest.Nodup := hparts.2
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simpa [inlineFragmentTypeConditionsNodup,
            possibleTypeNormalizations, hnormalized] using ih hrestNodup
      | cons head tail =>
          have hobjectNotInRestConditions :
              ∀ selection restObjectType,
                restObjectType ∈ rest ->
                  (match normalizeSelectionSet schema restObjectType
                      selectionSet with
                  | [] => none
                  | head :: tail =>
                      some (Selection.inlineFragment (some restObjectType)
                        [] (head :: tail))) =
                    some selection ->
                  (match selection with
                  | Selection.inlineFragment (some typeCondition)
                      _directives _selectionSet =>
                      some typeCondition
                  | _ => none) ≠ some objectType := by
            intro selection restObjectType hrestObjectType hbranch
              hcondition
            cases hrestNormalized :
                normalizeSelectionSet schema restObjectType selectionSet with
            | nil =>
                simp [hrestNormalized] at hbranch
            | cons restHead restTail =>
                simp [hrestNormalized] at hbranch
                subst selection
                simp at hcondition
                subst restObjectType
                exact hobjectNotMem hrestObjectType
          simp [inlineFragmentTypeConditionsNodup, inlineFragmentTypeCondition?,
            possibleTypeNormalizations, hnormalized]
          exact ⟨hobjectNotInRestConditions, ih hrestNodup⟩

theorem possibleTypeNormalizations_nonRedundant
    (schema : Schema) (possibleTypes : List Name)
    (selectionSet : List Selection)
    : possibleTypes.Nodup
      -> (∀ objectType,
            objectType ∈ possibleTypes
            -> selectionSetNonRedundant
                (normalizeSelectionSet schema objectType selectionSet))
      -> selectionSetNonRedundant
          (possibleTypeNormalizations schema possibleTypes selectionSet) := by
  intro hnodup hnormalize
  unfold selectionSetNonRedundant
  constructor
  · exact possibleTypeNormalizations_responseNamesNodup schema possibleTypes
      selectionSet
  · constructor
    · exact possibleTypeNormalizations_inlineFragmentTypeConditionsNodup
        schema possibleTypes selectionSet hnodup
    · intro selection hselection
      unfold possibleTypeNormalizations at hselection
      rw [List.mem_filterMap] at hselection
      rcases hselection with
        ⟨objectType, hobjectType, hselectionEq⟩
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simp [hnormalized] at hselectionEq
      | cons head tail =>
          simp [hnormalized] at hselectionEq
          subst selection
          unfold selectionNonRedundant
          simpa [hnormalized] using hnormalize objectType hobjectType

theorem normalizeSelectionSet_nonRedundant (schema : Schema)
    (hpossibleTypesNodup : ∀ typeName, (schema.getPossibleTypes typeName).Nodup)
    : ∀ parentType selectionSet,
        selectionSetNonRedundant
          (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      simp [normalizeSelectionSet, selectionSetNonRedundant,
        responseNamesNodup, inlineFragmentTypeConditionsNodup]
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      simpa [normalizeSelectionSet, hlookup] using hrest
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hsubselectionsNonRedundant :
          selectionSetNonRedundant normalizedSubselections := by
        unfold normalizedSubselections
        by_cases hobject : objectTypeNameBool schema returnType = true
        · simp [hobject]
          exact hmerged
        · have hfalse : objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hfalse]
          exact possibleTypeNormalizations_nonRedundant schema
            (schema.getPossibleTypes returnType) mergedSubselections
            (hpossibleTypesNodup returnType)
            (fun objectType hobjectType => hpossible objectType)
      have htailNoResponseName :=
        normalizeSelectionSet_without_responseName_not_mem schema parentType
          responseName rest
      rw [normalizeSelectionSet.eq_2, hlookup]
      change selectionSetNonRedundant
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      exact
        selectionSetNonRedundant_normalizedFieldWithRest schema returnType
          responseName fieldName arguments directives normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest))
          htailNoResponseName
          (normalizeSelectionSet_allFields schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest))
          hsubselectionsNonRedundant hrest
  | case4 parentType rest directives selectionSet happend =>
      simpa [normalizeSelectionSet] using happend
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      _hrest happend =>
      simpa [normalizeSelectionSet, hoverlap] using happend
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse] using hrest

theorem normalizeSelectionSet_normal (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name) (selectionSet : List Selection)
    (hparentObject : objectTypeNameBool schema parentType = true)
    : selectionSetNormal schema parentType
        (normalizeSelectionSet schema parentType selectionSet) := by
  exact ⟨
    normalizeSelectionSet_groundTyped schema hschema parentType selectionSet
      hparentObject,
    normalizeSelectionSet_nonRedundant schema
      (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema)
      parentType selectionSet⟩

theorem normalizeOperation_normal (schema : Schema) (operation : Operation)
    : normalizeOperationNormal schema operation := by
  intro hschema hvalid
  have hrootEq :
      (operation.rootType schema) = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  have hrootObjectBool :
      objectTypeNameBool schema (operation.rootType schema) = true :=
    objectTypeNameBool_eq_true_of_objectType_forNormality schema hrootObject
  simpa [normalizeOperation, operationNormal, Operation.rootType,
    OperationType.rootType] using
    normalizeSelectionSet_normal schema hschema (operation.rootType schema)
      operation.selectionSet hrootObjectBool

end GroundTypeNormalization

end NormalForm

end GraphQL
