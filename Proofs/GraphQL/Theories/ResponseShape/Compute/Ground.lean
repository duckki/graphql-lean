import GraphQL.Theories.ResponseShape.Compute
import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality

/-!
Actual-image facts for decoding the output of ground-type normalization.

`GroundSelectionSetImage` records exactly the structural obligations consumed by
`foldGroundSelectionSet`: object scopes contain unique directive-free fields,
while abstract scopes contain unique nonempty branches for included concrete
objects.  This predicate is deliberately proof-facing.  It characterizes the
normalizer/decoder seam without narrowing the permissive public response-shape
well-formedness predicate.
-/

namespace GraphQL

namespace ResponseShape

theorem isCompositeBool_eq_false_of_leafTypeNameBool
    (schema : Schema) {typeRef : TypeRef}
    (hleaf : NormalForm.leafTypeNameBool schema typeRef.namedType = true) :
    typeRef.isCompositeBool schema = false := by
  unfold NormalForm.leafTypeNameBool at hleaf
  unfold TypeRef.isCompositeBool
  cases hlookup : schema.lookupType typeRef.namedType with
  | none => simp [hlookup] at hleaf
  | some typeDefinition =>
      cases typeDefinition <;> simp_all

/-- The composite named types accepted as abstract scopes by the ground decoder. -/
def AbstractType (schema : Schema) (typeName : Name) : Prop :=
  schema.interfaceType typeName ∨
  ∃ unionType, schema.lookupType typeName = some (.union unionType)

mutual
  /-- Actual-image grammar for one normalized ground selection set. -/
  inductive GroundSelectionSetImage (schema : Schema) : Name -> List Selection -> Prop
    | objectNil {parentType : Name}
        (hobject : schema.objectType parentType) :
        GroundSelectionSetImage schema parentType []
    | objectField {parentType responseName fieldName : Name}
        {arguments : List Argument} {fieldDefinition : FieldDefinition}
        {selectionSet rest : List Selection}
        (hobject : schema.objectType parentType)
        (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
        (hresponseName : responseName ∉ rest.filterMap Selection.responseName?)
        (hchild : GroundFieldChildImage schema fieldDefinition selectionSet)
        (hrest : GroundSelectionSetImage schema parentType rest) :
        GroundSelectionSetImage schema parentType
          (.field responseName fieldName arguments [] selectionSet :: rest)
    | abstractNil {parentType : Name}
        (habstract : AbstractType schema parentType) :
        GroundSelectionSetImage schema parentType []
    | abstractFragment {parentType objectType : Name}
        {selection rest : List Selection}
        (habstract : AbstractType schema parentType)
        (hobject : schema.objectType objectType)
        (hincludes : schema.typeIncludesObjectBool parentType objectType = true)
        (hnonempty : selection ≠ [])
        (htypeCondition : objectType ∉
          rest.filterMap NormalForm.inlineFragmentTypeCondition?)
        (hselection : GroundSelectionSetImage schema objectType selection)
        (hrest : GroundSelectionSetImage schema parentType rest) :
        GroundSelectionSetImage schema parentType
          (.inlineFragment (some objectType) [] selection :: rest)

  /-- The child-kind obligation attached to an emitted normalized field. -/
  inductive GroundFieldChildImage (schema : Schema)
      : FieldDefinition -> List Selection -> Prop
    | composite {fieldDefinition : FieldDefinition} {selectionSet : List Selection}
        (hcomposite : fieldDefinition.outputType.isCompositeBool schema = true)
        (hselection : GroundSelectionSetImage schema
          fieldDefinition.outputType.namedType selectionSet) :
        GroundFieldChildImage schema fieldDefinition selectionSet
    | leaf {fieldDefinition : FieldDefinition}
        (hleaf : NormalForm.leafTypeNameBool schema
          fieldDefinition.outputType.namedType = true) :
        GroundFieldChildImage schema fieldDefinition []
end

private theorem compositeType_classification
    (schema : Schema) {typeRef : TypeRef}
    (hcomposite : typeRef.isCompositeBool schema = true) :
    (NormalForm.objectTypeNameBool schema typeRef.namedType = true
      ∧ schema.objectType typeRef.namedType)
    ∨ (NormalForm.objectTypeNameBool schema typeRef.namedType = false
      ∧ AbstractType schema typeRef.namedType) := by
  unfold TypeRef.isCompositeBool at hcomposite
  cases hlookup : schema.lookupType typeRef.namedType with
  | none => simp [hlookup] at hcomposite
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          left
          exact ⟨by simp [NormalForm.objectTypeNameBool, hlookup],
            ⟨objectType, hlookup⟩⟩
      | interface interfaceType =>
          right
          exact ⟨by simp [NormalForm.objectTypeNameBool, hlookup],
            Or.inl ⟨interfaceType, hlookup⟩⟩
      | union unionType =>
          right
          exact ⟨by simp [NormalForm.objectTypeNameBool, hlookup],
            Or.inr ⟨unionType, hlookup⟩⟩
      | builtinScalar scalar => simp [hlookup] at hcomposite
      | customScalar scalar => simp [hlookup] at hcomposite
      | enum enumType => simp [hlookup] at hcomposite
      | inputObject inputObjectType => simp [hlookup] at hcomposite

private theorem typeRef_isOutputType_namedType
    (schema : Schema) : ∀ {typeRef : TypeRef},
      typeRef.isOutputType schema -> schema.isOutputType typeRef.namedType
  | .named _typeName, houtput => houtput
  | .list inner, houtput =>
      typeRef_isOutputType_namedType schema (typeRef := inner) houtput
  | .nonNull inner, houtput => by
      cases inner with
      | nonNull nested => simp [TypeRef.isOutputType] at houtput
      | named typeName => exact houtput
      | list nested =>
          exact typeRef_isOutputType_namedType schema
            (typeRef := .list nested) houtput

private theorem leafTypeNameBool_of_outputType_not_composite
    (schema : Schema) {typeRef : TypeRef}
    (houtput : typeRef.isOutputType schema)
    (hcomposite : typeRef.isCompositeBool schema = false) :
    NormalForm.leafTypeNameBool schema typeRef.namedType = true := by
  rcases typeRef_isOutputType_namedType schema houtput with
    ⟨typeDefinition, hlookup, houtputDefinition⟩
  cases typeDefinition with
  | builtinScalar scalar =>
      simp [NormalForm.leafTypeNameBool, hlookup]
  | customScalar scalar =>
      simp [NormalForm.leafTypeNameBool, hlookup]
  | enum enumType =>
      simp [NormalForm.leafTypeNameBool, hlookup]
  | object objectType =>
      simp [TypeRef.isCompositeBool, hlookup] at hcomposite
  | interface interfaceType =>
      simp [TypeRef.isCompositeBool, hlookup] at hcomposite
  | union unionType =>
      simp [TypeRef.isCompositeBool, hlookup] at hcomposite
  | inputObject inputObjectType =>
      simp [TypeDefinition.isOutputType] at houtputDefinition

private theorem leafType_grounding_data
    (schema : Schema) {typeName : Name}
    (hleaf : NormalForm.leafTypeNameBool schema typeName = true) :
    NormalForm.objectTypeNameBool schema typeName = false
      ∧ schema.getPossibleTypes typeName = [] := by
  unfold NormalForm.leafTypeNameBool at hleaf
  cases hlookup : schema.lookupType typeName with
  | none => simp [hlookup] at hleaf
  | some typeDefinition =>
      cases typeDefinition <;>
        simp_all [NormalForm.objectTypeNameBool, Schema.getPossibleTypes]

private theorem typeCondition_not_mem_possibleTypeNormalizations
    (schema : Schema) (objectType : Name) (possibleTypes : List Name)
    (selectionSet : List Selection)
    (hnotMem : objectType ∉ possibleTypes) :
    objectType ∉
      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
        schema possibleTypes selectionSet).filterMap
          NormalForm.inlineFragmentTypeCondition? := by
  intro hmem
  rw [List.mem_filterMap] at hmem
  rcases hmem with ⟨selection, hselection, hcondition⟩
  unfold NormalForm.GroundTypeNormalization.possibleTypeNormalizations at hselection
  rw [List.mem_filterMap] at hselection
  rcases hselection with ⟨candidate, hcandidate, hemitted⟩
  cases hnormalized :
      NormalForm.normalizeSelectionSet schema candidate selectionSet with
  | nil => simp [hnormalized] at hemitted
  | cons head tail =>
      simp [hnormalized] at hemitted
      subst selection
      simp [NormalForm.inlineFragmentTypeCondition?] at hcondition
      subst candidate
      exact hnotMem hcandidate

private theorem possibleTypeNormalizations_image
    (schema : Schema) (parentType : Name) (possibleTypes : List Name)
    (selectionSet : List Selection)
    (habstract : AbstractType schema parentType)
    (hobjects : ∀ objectType,
      objectType ∈ possibleTypes ->
      schema.objectType objectType)
    (hincludes : ∀ objectType,
      objectType ∈ possibleTypes ->
      schema.typeIncludesObjectBool parentType objectType = true)
    (hnodup : possibleTypes.Nodup)
    (himages : ∀ objectType,
      objectType ∈ possibleTypes ->
      GroundSelectionSetImage schema objectType
        (NormalForm.normalizeSelectionSet schema objectType selectionSet)) :
    GroundSelectionSetImage schema parentType
      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
        possibleTypes selectionSet) := by
  revert hobjects hincludes hnodup himages
  induction possibleTypes with
  | nil =>
      intro _hobjects _hincludes _hnodup _himages
      simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations] using
        GroundSelectionSetImage.abstractNil habstract
  | cons objectType rest ih =>
      intro hobjects hincludes hnodup himages
      have hparts := List.nodup_cons.mp hnodup
      have hobject := hobjects objectType (by simp)
      have himage := himages objectType (by simp)
      have ih' := ih
        (fun candidate hcandidate =>
          hobjects candidate (List.mem_cons_of_mem objectType hcandidate))
        (fun candidate hcandidate =>
          hincludes candidate (List.mem_cons_of_mem objectType hcandidate))
        hparts.2
        (fun candidate hcandidate =>
          himages candidate (List.mem_cons_of_mem objectType hcandidate))
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
            hnormalized] using ih'
      | cons head tail =>
          rw [NormalForm.GroundTypeNormalization.possibleTypeNormalizations]
          simp only [hnormalized, List.filterMap_cons]
          exact GroundSelectionSetImage.abstractFragment
            habstract hobject (hincludes objectType (by simp))
            (by simp)
            (typeCondition_not_mem_possibleTypeNormalizations schema objectType
              rest selectionSet hparts.1)
            (by simpa [hnormalized] using himage)
            ih'

/-- Ground normalization lands in the decoder's actual-image grammar. -/
theorem normalizeSelectionSet_groundSelectionSetImage
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ parentType selectionSet,
      schema.objectType parentType ->
      NormalForm.selectionSetDirectiveFree selectionSet ->
      GroundSelectionSetImage schema parentType
        (NormalForm.normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet hparentObject hfree
  induction parentType, selectionSet using
      NormalForm.normalizeSelectionSet.induct schema with
  | case1 parentType =>
      simpa [NormalForm.normalizeSelectionSet] using
        GroundSelectionSetImage.objectNil hparentObject
  | case2 parentType rest responseName fieldName arguments directives
      childSelectionSet hlookup hrest =>
      have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
      have hfilteredFree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.withoutFieldSelectionsWithResponseName schema
              responseName rest) :=
        NormalForm.withoutFieldSelectionsWithResponseName_directiveFree
          schema responseName rest hrestFree
      simpa [NormalForm.normalizeSelectionSet, hlookup] using
        hrest hparentObject hfilteredFree
  | case3 parentType rest responseName fieldName arguments directives
      childSelectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      have hselectionFree := NormalForm.selectionSetDirectiveFree_head hfree
      have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hfilteredFree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.withoutFieldSelectionsWithResponseName schema
              responseName rest) :=
        NormalForm.withoutFieldSelectionsWithResponseName_directiveFree
          schema responseName rest hrestFree
      have hmatchingFree :
          NormalForm.selectionSetDirectiveFree matching := by
        subst matching
        exact NormalForm.fieldSelectionsWithResponseNameInScope_directiveFree
          schema parentType responseName rest hrestFree
      have hmergedFree :
          NormalForm.selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact NormalForm.selectionSetDirectiveFree_append hselectionFree.2
          (NormalForm.selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hnormalizedRest :
          GroundSelectionSetImage schema parentType
            (NormalForm.normalizeSelectionSet schema parentType
              (NormalForm.withoutFieldSelectionsWithResponseName schema
                responseName rest)) :=
        hrest hparentObject hfilteredFree
      let normalizedSubselections :=
        if NormalForm.objectTypeNameBool schema returnType then
          NormalForm.normalizeSelectionSet schema returnType mergedSubselections
        else
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have houtput : fieldDefinition.outputType.isOutputType schema :=
        SchemaWellFormedness.schemaWellFormed_lookupField_outputType
          hschema hlookup
      have hchild :
          GroundFieldChildImage schema fieldDefinition
            normalizedSubselections := by
        by_cases hcomposite :
            fieldDefinition.outputType.isCompositeBool schema = true
        · rcases compositeType_classification schema hcomposite with
            ⟨hreturnObjectBool, hreturnObject⟩ |
            ⟨hreturnObjectFalse, hreturnAbstract⟩
          · apply GroundFieldChildImage.composite hcomposite
            unfold normalizedSubselections
            simp only [returnType, hreturnObjectBool, if_true]
            exact hmerged hreturnObject hmergedFree
          · apply GroundFieldChildImage.composite hcomposite
            unfold normalizedSubselections
            simp only [returnType, hreturnObjectFalse]
            exact possibleTypeNormalizations_image schema returnType
              (schema.getPossibleTypes returnType) mergedSubselections
              hreturnAbstract
              (fun objectType hobjectType =>
                SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  hschema returnType objectType hobjectType)
              (fun objectType hobjectType =>
                List.contains_iff_mem.mpr hobjectType)
              (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
                hschema returnType)
              (fun objectType hobjectType =>
                hpossible objectType
                  (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                    hschema returnType objectType hobjectType)
                  hmergedFree)
        · have hcompositeFalse :
              fieldDefinition.outputType.isCompositeBool schema = false := by
            cases hmatch : fieldDefinition.outputType.isCompositeBool schema
            · rfl
            · contradiction
          have hleaf := leafTypeNameBool_of_outputType_not_composite
            schema houtput hcompositeFalse
          rcases leafType_grounding_data schema hleaf with
            ⟨hreturnObjectFalse, hpossibleTypes⟩
          have hempty : normalizedSubselections = [] := by
            unfold normalizedSubselections
            simp [returnType, hreturnObjectFalse, hpossibleTypes,
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations]
          rw [hempty]
          exact GroundFieldChildImage.leaf hleaf
      have hresponseName :=
        NormalForm.GroundTypeNormalization.normalizeSelectionSet_without_responseName_not_mem
          schema parentType responseName rest
      rw [NormalForm.normalizeSelectionSet.eq_2, hlookup]
      change GroundSelectionSetImage schema parentType
        (.field responseName fieldName arguments [] normalizedSubselections ::
          NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.withoutFieldSelectionsWithResponseName schema
              responseName rest))
      exact GroundSelectionSetImage.objectField hparentObject hlookup
        hresponseName hchild hnormalizedRest
  | case4 parentType rest directives inlineSelectionSet happend =>
      have hselectionFree := NormalForm.selectionSetDirectiveFree_head hfree
      have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
      have happendFree :
          NormalForm.selectionSetDirectiveFree (inlineSelectionSet ++ rest) :=
        NormalForm.selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      simpa [NormalForm.normalizeSelectionSet] using
        happend hparentObject happendFree
  | case5 parentType rest typeCondition directives inlineSelectionSet hoverlap
      _hrest happend =>
      have hselectionFree := NormalForm.selectionSetDirectiveFree_head hfree
      have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
      have happendFree :
          NormalForm.selectionSetDirectiveFree (inlineSelectionSet ++ rest) :=
        NormalForm.selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      simpa [NormalForm.normalizeSelectionSet, hoverlap] using
        happend hparentObject happendFree
  | case6 parentType rest typeCondition directives inlineSelectionSet hoverlap
      hrest =>
      have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [NormalForm.normalizeSelectionSet, hfalse] using
        hrest hparentObject hrestFree

/-- Absence from the response-name projection makes the duplicate-field check false. -/
theorem noResponseName_any_eq_false
    (responseName : Name) : ∀ selectionSet : List Selection,
      responseName ∉ selectionSet.filterMap Selection.responseName? ->
      selectionSet.any
        (fun selection =>
          match selection with
          | .field candidate _fieldName _arguments _directives _selectionSet =>
              candidate == responseName
          | .inlineFragment .. => false) = false
  | [], _h => by simp
  | selection :: rest, h => by
      have hrest :
          responseName ∉ rest.filterMap Selection.responseName? := by
        intro hmem
        apply h
        rw [List.mem_filterMap] at hmem ⊢
        rcases hmem with ⟨candidate, hcandidate, heq⟩
        exact ⟨candidate, by simp [hcandidate], heq⟩
      cases selection with
      | field candidate fieldName arguments directives selectionSet =>
          have hne : candidate ≠ responseName := by
            intro heq
            apply h
            simp [Selection.responseName?, heq]
          simp [hne, noResponseName_any_eq_false responseName rest hrest]
      | inlineFragment typeCondition directives selectionSet =>
          simp [noResponseName_any_eq_false responseName rest hrest]

/-- Absence from the type-condition projection makes the duplicate-branch check false. -/
theorem noTypeCondition_any_eq_false
    (typeCondition : Name) : ∀ selectionSet : List Selection,
      typeCondition ∉
        selectionSet.filterMap NormalForm.inlineFragmentTypeCondition? ->
      selectionSet.any
        (fun selection =>
          match selection with
          | .inlineFragment (some candidate) _directives _selectionSet =>
              candidate == typeCondition
          | _ => false) = false
  | [], _h => by simp
  | selection :: rest, h => by
      have hrest :
          typeCondition ∉
            rest.filterMap NormalForm.inlineFragmentTypeCondition? := by
        intro hmem
        apply h
        rw [List.mem_filterMap] at hmem ⊢
        rcases hmem with ⟨candidate, hcandidate, heq⟩
        exact ⟨candidate, by simp [hcandidate], heq⟩
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          simp [noTypeCondition_any_eq_false typeCondition rest hrest]
      | inlineFragment condition directives selectionSet =>
          cases condition with
          | none =>
              simp [noTypeCondition_any_eq_false typeCondition rest hrest]
          | some candidate =>
              have hne : candidate ≠ typeCondition := by
                intro heq
                apply h
                simp [NormalForm.inlineFragmentTypeCondition?, heq]
              simp [hne,
                noTypeCondition_any_eq_false typeCondition rest hrest]

/-- An absent type condition cannot occur as a matching inline-fragment branch. -/
theorem noTypeCondition_exists
    (typeCondition : Name) (selectionSet : List Selection)
    (hfree : typeCondition ∉
      selectionSet.filterMap NormalForm.inlineFragmentTypeCondition?) :
    ¬ ∃ selection,
      selection ∈ selectionSet ∧
      (match selection with
        | .inlineFragment (some candidate) _directives _selectionSet =>
            candidate == typeCondition
        | _ => false) = true := by
  intro hexists
  have hany : selectionSet.any
      (fun selection =>
        match selection with
        | .inlineFragment (some candidate) _directives _selectionSet =>
            candidate == typeCondition
        | _ => false) = true :=
    List.any_eq_true.mpr hexists
  rw [noTypeCondition_any_eq_false typeCondition selectionSet hfree] at hany
  contradiction

mutual
  /-- Every selection set in the actual-image grammar is accepted by the ground fold. -/
  theorem foldGroundSelectionSet_success_of_image
      (schema : Schema) (clause : Clause) :
      ∀ {parentType selectionSet},
        GroundSelectionSetImage schema parentType selectionSet ->
        ∃ shape,
          foldGroundSelectionSet schema clause parentType selectionSet = .ok shape
    | _parentType, [], .objectNil hobject => by
        rcases hobject with ⟨objectType, hlookup⟩
        refine ⟨.object [], ?_⟩
        simp [foldGroundSelectionSet, NormalForm.objectTypeNameBool, hlookup]
    | parentType,
        .field responseName fieldName arguments [] selectionSet :: rest,
        @GroundSelectionSetImage.objectField _ _ _ _ _ fieldDefinition _ _
          hobject hlookup hresponseName hchild hrest => by
        rcases hobject with ⟨parentObject, hparentLookup⟩
        have hparentObjectBool :
            NormalForm.objectTypeNameBool schema parentType = true := by
          simp [NormalForm.objectTypeNameBool, hparentLookup]
        have hduplicateFalse :=
          noResponseName_any_eq_false _ _ hresponseName
        have hnotDuplicate :
            ¬ (rest.any
              (fun selection =>
                match selection with
                | .field candidate _fieldName _arguments _directives
                    _selectionSet => candidate == responseName
                | .inlineFragment .. => false) = true) := by
          simp [hduplicateFalse]
        rcases foldGroundFieldChild_success schema clause fieldName hchild with
          ⟨subshape, hsubshape⟩
        rcases foldGroundSelectionSet_success_of_image schema clause hrest with
          ⟨restShape, hrestShape⟩
        cases hchild with
        | composite hcomposite hselection =>
            cases hfold : foldGroundSelectionSet schema clause
                fieldDefinition.outputType.namedType selectionSet with
            | error error =>
                simp [hcomposite, hfold] at hsubshape
            | ok child =>
                unfold foldGroundSelectionSet
                unfold selectionHasResponseName
                simp only [hparentObjectBool, if_true, List.isEmpty_nil,
                  Bool.not_true, Bool.false_eq_true, if_false]
                split
                · rename_i hduplicate
                  exact (hnotDuplicate hduplicate).elim
                · refine ⟨mergeResponseShapes
                    (singletonDefinitionShape parentType responseName
                      (.mk clause
                        {
                          fieldName := fieldName
                          arguments := arguments
                          outputType := fieldDefinition.outputType
                        }
                        (some child)))
                    restShape, ?_⟩
                  simp [Bind.bind, Except.bind, hlookup, hcomposite,
                    hfold, hrestShape]
        | leaf hleaf =>
            have hcomposite :=
              isCompositeBool_eq_false_of_leafTypeNameBool schema hleaf
            unfold foldGroundSelectionSet
            unfold selectionHasResponseName
            simp only [hparentObjectBool, if_true, List.isEmpty_nil,
              Bool.not_true, Bool.false_eq_true, if_false]
            split
            · rename_i hduplicate
              exact (hnotDuplicate hduplicate).elim
            · refine ⟨mergeResponseShapes
                (singletonDefinitionShape parentType responseName
                  (.mk clause
                    {
                      fieldName := fieldName
                      arguments := arguments
                      outputType := fieldDefinition.outputType
                    }
                    none))
                restShape, ?_⟩
              simp [Bind.bind, Except.bind, hlookup, hcomposite,
                hleaf, hrestShape]
    | _parentType, [], .abstractNil habstract => by
        rcases habstract with hinterface | ⟨unionType, hunion⟩
        · rcases hinterface with ⟨interfaceType, hlookup⟩
          refine ⟨.object [], ?_⟩
          unfold foldGroundSelectionSet
          unfold abstractTypeNameBool
          simp [NormalForm.objectTypeNameBool, hlookup]
        · refine ⟨.object [], ?_⟩
          unfold foldGroundSelectionSet
          unfold abstractTypeNameBool
          simp [NormalForm.objectTypeNameBool, hunion]
    | parentType,
        .inlineFragment (some objectType) [] selection :: rest,
        .abstractFragment habstract hobject hincludes hnonempty
          htypeCondition hselection hrest => by
        rcases hobject with ⟨objectDefinition, hobjectLookup⟩
        have hlookupObject :
            schema.lookupObject objectType = some objectDefinition := by
          simp [Schema.lookupObject, hobjectLookup]
        have hnotDuplicate :
            ¬ ∃ candidate,
              candidate ∈ rest ∧
              (match candidate with
                | .inlineFragment (some possible) _directives _selectionSet =>
                    possible == objectType
                | _ => false) = true :=
          noTypeCondition_exists objectType rest htypeCondition
        rcases foldGroundSelectionSet_success_of_image schema clause hselection with
          ⟨selectionShape, hselectionShape⟩
        rcases foldGroundSelectionSet_success_of_image schema clause hrest with
          ⟨restShape, hrestShape⟩
        unfold AbstractType at habstract
        rcases habstract with hinterface | hunion
        ·
            rcases hinterface with ⟨interfaceType, hparentLookup⟩
            cases hselectionSet : selection with
            | nil => simp_all
            | cons head tail =>
                refine ⟨mergeResponseShapes selectionShape restShape, ?_⟩
                unfold foldGroundSelectionSet
                unfold selectionHasTypeCondition abstractTypeNameBool
                simp [Bind.bind, Except.bind, NormalForm.objectTypeNameBool,
                  hparentLookup, hlookupObject, hincludes, hrestShape]
                split
                · rename_i hduplicate
                  exact (hnotDuplicate hduplicate).elim
                · have hselectionShape' :
                      foldGroundSelectionSet schema clause objectType
                          (head :: tail) = .ok selectionShape := by
                    simpa [hselectionSet] using hselectionShape
                  simp [hselectionShape']
        ·
            rcases hunion with ⟨unionType, hparentLookup⟩
            cases hselectionSet : selection with
            | nil => simp_all
            | cons head tail =>
                refine ⟨mergeResponseShapes selectionShape restShape, ?_⟩
                unfold foldGroundSelectionSet
                unfold selectionHasTypeCondition abstractTypeNameBool
                simp [Bind.bind, Except.bind, NormalForm.objectTypeNameBool,
                  hparentLookup, hlookupObject, hincludes, hrestShape]
                split
                · rename_i hduplicate
                  exact (hnotDuplicate hduplicate).elim
                · have hselectionShape' :
                      foldGroundSelectionSet schema clause objectType
                          (head :: tail) = .ok selectionShape := by
                    simpa [hselectionSet] using hselectionShape
                  simp [hselectionShape']

  /-- The child-kind component of the actual-image grammar is accepted by a field fold. -/
  theorem foldGroundFieldChild_success
      (schema : Schema) (clause : Clause) (fieldName : Name) :
      ∀ {fieldDefinition selectionSet},
        GroundFieldChildImage schema fieldDefinition selectionSet ->
        ∃ subshape,
          (if fieldDefinition.outputType.isCompositeBool schema then
              match foldGroundSelectionSet schema clause
                  fieldDefinition.outputType.namedType selectionSet with
              | .ok child => .ok (some child)
              | .error error => .error error
            else if NormalForm.leafTypeNameBool schema
                fieldDefinition.outputType.namedType then
              if selectionSet.isEmpty then .ok none
              else .error (.leafFieldHasSubselections fieldName)
            else
              .error (.invalidFieldOutputType fieldName
                fieldDefinition.outputType.namedType)) =
            (.ok subshape : Except ShapeBuildError (Option ResponseShape))
    | _fieldDefinition, _selectionSet, .composite hcomposite hselection => by
        rcases foldGroundSelectionSet_success_of_image schema clause hselection with
          ⟨shape, hshape⟩
        exact ⟨some shape, by simp [hcomposite, hshape]⟩
    | _fieldDefinition, [], .leaf hleaf => by
        have hcomposite :=
          isCompositeBool_eq_false_of_leafTypeNameBool schema hleaf
        exact ⟨none, by simp [hcomposite, hleaf]⟩
end

/-- Folding ground-normalizer output succeeds for every directive-free object input. -/
theorem foldGroundSelectionSet_normalizeSelectionSet_success
    (schema : Schema) (clause : Clause) (parentType : Name)
    (selectionSet : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hparentObject : schema.objectType parentType)
    (hfree : NormalForm.selectionSetDirectiveFree selectionSet) :
    ∃ shape,
      foldGroundSelectionSet schema clause parentType
          (NormalForm.normalizeSelectionSet schema parentType selectionSet) =
        .ok shape :=
  foldGroundSelectionSet_success_of_image schema clause
    (normalizeSelectionSet_groundSelectionSetImage schema hschema
      parentType selectionSet hparentObject hfree)

end ResponseShape

end GraphQL
