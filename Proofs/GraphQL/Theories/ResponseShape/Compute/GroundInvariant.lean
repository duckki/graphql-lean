import Proofs.GraphQL.Theories.ResponseShape.Compute.Ground
import Proofs.GraphQL.Theories.ResponseShape.Compute.WellFormed
import Proofs.GraphQL.Theories.ResponseShape.Compute.Merge

/-!
Decoder-invariant facts for the actual image of ground-type normalization.
-/

namespace GraphQL

namespace ResponseShape

private theorem emptyShape_clausesEqual (clause : Clause) :
    ShapeClausesEqual clause (.object []) := by
  simp [ShapeClausesEqual, ResponseShape.positions]

private theorem emptyShape_responseNamesIn (allowed : List Name) :
    ShapeResponseNamesIn allowed (.object []) := by
  simp [ShapeResponseNamesIn, ResponseShape.positions]

private theorem emptyShape_objectTypesIn (allowed : List GroundObject) :
    ShapeObjectTypesIn allowed (.object []) := by
  simp [ShapeObjectTypesIn, ResponseShape.positions]

private theorem singletonDefinitionShape_clausesEqual
    (parentObject responseName : Name) (definition : ShapeDefinition) :
    ShapeClausesEqual definition.clause
      (singletonDefinitionShape parentObject responseName definition) := by
  unfold ShapeClausesEqual singletonDefinitionShape
  intro position hposition
  simp only [ResponseShape.positions, List.mem_singleton] at hposition
  subst position
  intro possible hpossible
  simp only [ResponsePosition.possibleDefinitions, List.mem_singleton] at hpossible
  subst possible
  intro candidate hcandidate
  simp only [PossibleDefinitions.definitions, List.mem_singleton] at hcandidate
  subst candidate
  rfl

private theorem singletonDefinitionShape_responseNamesIn
    (parentObject responseName : Name) (definition : ShapeDefinition) :
    ShapeResponseNamesIn [responseName]
      (singletonDefinitionShape parentObject responseName definition) := by
  unfold ShapeResponseNamesIn singletonDefinitionShape
  intro position hposition
  simp only [ResponseShape.positions, List.mem_singleton] at hposition
  subst position
  simp [ResponsePosition.responseName]

private theorem singletonDefinitionShape_objectTypesIn
    (parentObject responseName : Name) (definition : ShapeDefinition) :
    ShapeObjectTypesIn [parentObject]
      (singletonDefinitionShape parentObject responseName definition) := by
  unfold ShapeObjectTypesIn singletonDefinitionShape
  intro position hposition
  simp only [ResponseShape.positions, List.mem_singleton] at hposition
  subst position
  intro possible hpossible
  simp only [ResponsePosition.possibleDefinitions, List.mem_singleton] at hpossible
  subst possible
  intro objectType hobjectType
  simpa [PossibleDefinitions.objectTypes] using hobjectType

private theorem ShapeResponseNamesIn.mono
    {allowed wider : List Name} {shape : ResponseShape}
    (hsub : ∀ name ∈ allowed, name ∈ wider)
    (hin : ShapeResponseNamesIn allowed shape) :
    ShapeResponseNamesIn wider shape := by
  intro position hposition
  exact hsub position.responseName (hin position hposition)

private theorem ShapeObjectTypesIn.mono
    {allowed wider : List GroundObject} {shape : ResponseShape}
    (hsub : ∀ objectType ∈ allowed, objectType ∈ wider)
    (hin : ShapeObjectTypesIn allowed shape) :
    ShapeObjectTypesIn wider shape := by
  intro position hposition possible hpossible objectType hobjectType
  exact hsub objectType
    (hin position hposition possible hpossible objectType hobjectType)

private theorem noResponseName_exists
    (responseName : Name) (selectionSet : List Selection)
    (hfree : responseName ∉
      selectionSet.filterMap Selection.responseName?) :
    ¬ ∃ selection,
      selection ∈ selectionSet ∧
      (match selection with
        | .field candidate _fieldName _arguments _directives _selectionSet =>
            candidate == responseName
        | .inlineFragment .. => false) = true := by
  intro hexists
  have hany : selectionSet.any
      (fun selection =>
        match selection with
        | .field candidate _fieldName _arguments _directives _selectionSet =>
            candidate == responseName
        | .inlineFragment .. => false) = true :=
    List.any_eq_true.mpr hexists
  have hfalse :=
    noResponseName_any_eq_false responseName selectionSet hfree
  exact Bool.false_ne_true (hfalse.symm.trans hany)

private theorem objectType_not_abstractType
    (schema : Schema) (typeName : Name)
    (hobject : schema.objectType typeName)
    (habstract : AbstractType schema typeName) : False := by
  rcases hobject with ⟨objectDefinition, hobjectLookup⟩
  rcases habstract with ⟨interfaceDefinition, hinterfaceLookup⟩ |
      ⟨unionDefinition, hunionLookup⟩
  · rw [hobjectLookup] at hinterfaceLookup
    cases hinterfaceLookup
  · rw [hobjectLookup] at hunionLookup
    cases hunionLookup

/-- A shape decoded in a concrete-object scope can be viewed in an enclosing
scope which includes that object.  The key-membership premise records that the
shape really contains only the concrete object's singleton groups. -/
private theorem DecoderShapeInvariant.reparentSingleton
    (schema : Schema) (support : List NormalForm.BoolVar)
    (parentType objectType : Name) (shape : ResponseShape)
    (hobject : schema.objectType objectType)
    (hincludes : schema.typeIncludesObjectBool parentType objectType = true)
    (hinvariant : DecoderShapeInvariant schema support objectType shape)
    (hkeys : ShapeObjectTypesIn [objectType] shape) :
    DecoderShapeInvariant schema support parentType shape := by
  cases shape with
  | object positions =>
      refine ⟨hinvariant.1, ?_⟩
      intro position hposition
      rcases hinvariant.2 position hposition with
        ⟨objects, hobjects, hnodup, hgroups⟩
      refine ⟨objects, hobjects, hnodup, ?_⟩
      intro possible hpossible
      rcases hgroups possible hpossible with
        ⟨_oldValid, hclauses, hdefinitions⟩
      have hkey : possible.objectTypes ∈
          position.possibleDefinitions.map PossibleDefinitions.objectTypes :=
        List.mem_map.mpr ⟨possible, hpossible, rfl⟩
      rw [hobjects] at hkey
      simp only [List.mem_map] at hkey
      rcases hkey with ⟨candidate, _hcandidate, hcandidate⟩
      have hcandidateMem : candidate ∈ possible.objectTypes := by
        rw [← hcandidate]
        simp
      have hcandidateEq : candidate = objectType := by
        simpa using hkeys position hposition possible hpossible candidate
          hcandidateMem
      have hpossibleObjects : possible.objectTypes = [objectType] := by
        rw [← hcandidateEq]
        exact hcandidate.symm
      refine ⟨?_, hclauses, hdefinitions⟩
      rw [hpossibleObjects]
      exact groundSetValid_singleton schema parentType objectType hobject hincludes

/-- Strengthened ground-image result.  Besides the decoder invariant and
uniform clause, the two implications expose precisely the collision metadata
needed by the enclosing scope: response names and the singleton object key in
an object scope, and fragment object keys in an abstract scope. -/
private def GroundFoldInvariantResult
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (parentType : Name) (selectionSet : List Selection)
    (shape : ResponseShape) : Prop :=
  DecoderShapeInvariant schema support parentType shape
  ∧ ShapeClausesEqual clause shape
  ∧ (schema.objectType parentType ->
    ShapeResponseNamesIn
        (selectionSet.filterMap Selection.responseName?) shape
    ∧ ShapeObjectTypesIn [parentType] shape)
  ∧ (AbstractType schema parentType ->
    ShapeObjectTypesIn
      (selectionSet.filterMap NormalForm.inlineFragmentTypeCondition?) shape)

private def GroundFieldImageResult
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (fieldDefinition : FieldDefinition) (selectionSet : List Selection) : Prop :=
  (∃ shape,
        foldGroundSelectionSet schema clause
            fieldDefinition.outputType.namedType selectionSet = .ok shape
        ∧ GroundFoldInvariantResult schema support clause
            fieldDefinition.outputType.namedType selectionSet shape)
  ∨ (NormalForm.leafTypeNameBool schema
      fieldDefinition.outputType.namedType = true ∧ selectionSet = [])

private theorem foldGroundSelectionSet_invariant_success_of_image
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (hvalid : clause.Valid support)
    (hcomplete : clause.CompleteMinterm support) :
    ∀ {parentType selectionSet},
      (himage : GroundSelectionSetImage schema parentType selectionSet) ->
      ∃ shape,
        foldGroundSelectionSet schema clause parentType selectionSet = .ok shape
        ∧ GroundFoldInvariantResult schema support clause
            parentType selectionSet shape := by
  intro _parentType _selectionSet himage
  induction himage using GroundSelectionSetImage.rec
      (motive_2 := fun fieldDefinition selectionSet _hchild =>
        GroundFieldImageResult schema support clause
          fieldDefinition selectionSet) with
  | @objectNil parentType hobject =>
      rcases hobject with ⟨objectDefinition, hlookup⟩
      refine ⟨.object [], by
        simp [foldGroundSelectionSet, NormalForm.objectTypeNameBool, hlookup], ?_⟩
      exact ⟨DecoderShapeInvariant.empty schema support parentType,
        emptyShape_clausesEqual clause,
        fun _ => ⟨emptyShape_responseNamesIn [],
          emptyShape_objectTypesIn [parentType]⟩,
        fun habstract =>
          (objectType_not_abstractType schema parentType
            ⟨objectDefinition, hlookup⟩ habstract).elim⟩
  | @objectField parentType responseName fieldName arguments fieldDefinition
      selectionSet rest hobject hlookup hresponseName hchild hrest ihchild ihrest =>
      rcases hobject with ⟨parentObject, hparentLookup⟩
      have hparentObjectBool :
          NormalForm.objectTypeNameBool schema parentType = true := by
        simp [NormalForm.objectTypeNameBool, hparentLookup]
      have hnotDuplicate : ¬ (rest.any
          (fun selection =>
            match selection with
            | .field candidate _ _ _ _ => candidate == responseName
            | .inlineFragment .. => false) = true) := by
        intro hduplicate
        have hfalse :=
          noResponseName_any_eq_false responseName rest hresponseName
        exact Bool.false_ne_true (hfalse.symm.trans hduplicate)
      rcases ihrest with ⟨restShape, hrestFold, hrestResult⟩
      rcases hrestResult with
        ⟨hrestInvariant, hrestClauses, hrestObject, _hrestAbstract⟩
      have hrestMetadata := hrestObject ⟨parentObject, hparentLookup⟩
      cases hchild with
      | composite hcomposite hselection =>
          have hnotLeaf : ¬ (NormalForm.leafTypeNameBool schema
              fieldDefinition.outputType.namedType = true ∧ selectionSet = []) := by
            intro hleaf
            have hfalse :=
              isCompositeBool_eq_false_of_leafTypeNameBool schema hleaf.1
            rw [hcomposite] at hfalse
            contradiction
          rcases ihchild.resolve_right hnotLeaf with
            ⟨childShape, hchildFold, hchildResult⟩
          let definition : ShapeDefinition :=
            .mk clause
              { fieldName := fieldName, arguments := arguments,
                outputType := fieldDefinition.outputType }
              (some childShape)
          let currentShape :=
            singletonDefinitionShape parentType responseName definition
          have hdefinition : DecoderDefinitionInvariant schema support definition :=
            DecoderDefinitionInvariant.composite schema support clause _ _
              hvalid hcomplete hcomposite hchildResult.1
          have hcurrentInvariant : DecoderShapeInvariant schema support
              parentType currentShape :=
            DecoderShapeInvariant.singletonDefinition schema support
              parentType parentType responseName definition
              (groundSetValid_objectSingleton schema parentType
                ⟨parentObject, hparentLookup⟩) hdefinition
          have hcurrentNames :=
            singletonDefinitionShape_responseNamesIn parentType responseName definition
          have hcompatible : MergeCompatible currentShape restShape :=
            mergeCompatible_of_responseNamesIn_disjoint [responseName]
              (rest.filterMap Selection.responseName?) currentShape restShape
              (by simpa using hresponseName) hcurrentNames hrestMetadata.1
          refine ⟨mergeResponseShapes currentShape restShape, ?_, ?_⟩
          · unfold foldGroundSelectionSet selectionHasResponseName
            simp only [hparentObjectBool, if_true, List.isEmpty_nil,
              Bool.not_true, Bool.false_eq_true, if_false]
            split
            · rename_i hduplicate
              exact (hnotDuplicate hduplicate).elim
            · simp [Bind.bind, Except.bind, hlookup, hcomposite,
                hchildFold, hrestFold, currentShape, definition]
          · exact ⟨mergeResponseShapes_decoderShapeInvariant schema support
                parentType currentShape restShape hcurrentInvariant
                hrestInvariant hcompatible,
              ShapeClausesEqual.merge clause currentShape restShape
                (singletonDefinitionShape_clausesEqual parentType responseName definition)
                hrestClauses,
              fun _ => ⟨ShapeResponseNamesIn.merge _ _ _
                  (hcurrentNames.mono (by simp [Selection.responseName?]))
                  (hrestMetadata.1.mono (fun name hname => by
                    simp [Selection.responseName?, hname])),
                ShapeObjectTypesIn.merge _ _ _
                  (singletonDefinitionShape_objectTypesIn
                    parentType responseName definition) hrestMetadata.2⟩,
              fun habstract =>
                (objectType_not_abstractType schema parentType
                  ⟨parentObject, hparentLookup⟩ habstract).elim⟩
      | leaf hleaf =>
          have hnotComposite :=
            isCompositeBool_eq_false_of_leafTypeNameBool schema hleaf
          let definition : ShapeDefinition :=
            .mk clause
              { fieldName := fieldName, arguments := arguments,
                outputType := fieldDefinition.outputType }
              none
          let currentShape :=
            singletonDefinitionShape parentType responseName definition
          have hdefinition : DecoderDefinitionInvariant schema support definition :=
            DecoderDefinitionInvariant.leaf schema support clause _ hvalid
              hcomplete hnotComposite hleaf
          have hcurrentInvariant : DecoderShapeInvariant schema support
              parentType currentShape :=
            DecoderShapeInvariant.singletonDefinition schema support
              parentType parentType responseName definition
              (groundSetValid_objectSingleton schema parentType
                ⟨parentObject, hparentLookup⟩) hdefinition
          have hcurrentNames :=
            singletonDefinitionShape_responseNamesIn parentType responseName definition
          have hcompatible : MergeCompatible currentShape restShape :=
            mergeCompatible_of_responseNamesIn_disjoint [responseName]
              (rest.filterMap Selection.responseName?) currentShape restShape
              (by simpa using hresponseName) hcurrentNames hrestMetadata.1
          refine ⟨mergeResponseShapes currentShape restShape, ?_, ?_⟩
          · unfold foldGroundSelectionSet selectionHasResponseName
            simp only [hparentObjectBool, if_true, List.isEmpty_nil,
              Bool.not_true, Bool.false_eq_true, if_false]
            split
            · rename_i hduplicate
              exact (hnotDuplicate hduplicate).elim
            · simp [Bind.bind, Except.bind, hlookup, hnotComposite, hleaf, hrestFold,
                currentShape, definition]
          · exact ⟨mergeResponseShapes_decoderShapeInvariant schema support
                parentType currentShape restShape hcurrentInvariant
                hrestInvariant hcompatible,
              ShapeClausesEqual.merge clause currentShape restShape
                (singletonDefinitionShape_clausesEqual parentType responseName definition)
                hrestClauses,
              fun _ => ⟨ShapeResponseNamesIn.merge _ _ _
                  (hcurrentNames.mono (by simp [Selection.responseName?]))
                  (hrestMetadata.1.mono (fun name hname => by
                    simp [Selection.responseName?, hname])),
                ShapeObjectTypesIn.merge _ _ _
                  (singletonDefinitionShape_objectTypesIn
                    parentType responseName definition) hrestMetadata.2⟩,
              fun habstract =>
                (objectType_not_abstractType schema parentType
                  ⟨parentObject, hparentLookup⟩ habstract).elim⟩
  | @abstractNil parentType habstract =>
      refine ⟨.object [], ?_, ?_⟩
      · rcases habstract with ⟨interfaceType, hlookup⟩ |
          ⟨unionType, hlookup⟩
        · simp [foldGroundSelectionSet, abstractTypeNameBool,
            NormalForm.objectTypeNameBool, hlookup]
        · simp [foldGroundSelectionSet, abstractTypeNameBool,
            NormalForm.objectTypeNameBool, hlookup]
      · exact ⟨DecoderShapeInvariant.empty schema support parentType,
          emptyShape_clausesEqual clause,
          fun _ => ⟨emptyShape_responseNamesIn [],
            emptyShape_objectTypesIn [parentType]⟩,
          fun _ => emptyShape_objectTypesIn []⟩
  | @abstractFragment parentType objectType selection rest habstract hobject
      hincludes hnonempty htypeCondition hselection hrest ihselection ihrest =>
      rcases hobject with ⟨objectDefinition, hobjectLookup⟩
      have hlookupObject : schema.lookupObject objectType = some objectDefinition := by
        simp [Schema.lookupObject, hobjectLookup]
      have hnotDuplicate : ¬ ∃ candidate,
          candidate ∈ rest ∧
          (match candidate with
            | .inlineFragment (some possible) _ _ => possible == objectType
            | _ => false) = true :=
        noTypeCondition_exists objectType rest htypeCondition
      have hduplicateFalse :=
        noTypeCondition_any_eq_false objectType rest htypeCondition
      rcases ihselection with
        ⟨selectionShape, hselectionFold, hselectionResult⟩
      rcases ihrest with ⟨restShape, hrestFold, hrestResult⟩
      rcases hselectionResult with
        ⟨hselectionInvariant, hselectionClauses, hselectionObject,
          _hselectionAbstract⟩
      rcases hrestResult with
        ⟨hrestInvariant, hrestClauses, _hrestObject, hrestAbstract⟩
      have hselectionKeys :=
        (hselectionObject ⟨objectDefinition, hobjectLookup⟩).2
      have hselectionParentInvariant :=
        hselectionInvariant.reparentSingleton schema support parentType
          objectType selectionShape ⟨objectDefinition, hobjectLookup⟩
          hincludes hselectionKeys
      have hrestKeys := hrestAbstract habstract
      have hcompatible : MergeCompatible selectionShape restShape :=
        mergeCompatible_of_objectTypesIn_disjoint schema support parentType
          [objectType] (rest.filterMap NormalForm.inlineFragmentTypeCondition?)
          selectionShape restShape (by simpa using htypeCondition)
          hselectionParentInvariant hrestInvariant hselectionKeys hrestKeys
      refine ⟨mergeResponseShapes selectionShape restShape, ?_, ?_⟩
      · cases hselectionSet : selection with
        | nil => exact (hnonempty hselectionSet).elim
        | cons head tail =>
            rcases habstract with ⟨interfaceType, hparentLookup⟩ |
              ⟨unionType, hparentLookup⟩
            · unfold foldGroundSelectionSet selectionHasTypeCondition
              simp [Bind.bind, Except.bind, NormalForm.objectTypeNameBool,
                abstractTypeNameBool, hparentLookup, hlookupObject, hincludes,
                hrestFold]
              split
              · rename_i hduplicate
                exact (hnotDuplicate hduplicate).elim
              · have hselectionFold' :
                    foldGroundSelectionSet schema clause objectType
                      (head :: tail) = .ok selectionShape := by
                  simpa [hselectionSet] using hselectionFold
                simp [hselectionFold']
            · unfold foldGroundSelectionSet selectionHasTypeCondition
              simp [Bind.bind, Except.bind, NormalForm.objectTypeNameBool,
                abstractTypeNameBool, hparentLookup, hlookupObject, hincludes,
                hrestFold]
              split
              · rename_i hduplicate
                exact (hnotDuplicate hduplicate).elim
              · have hselectionFold' :
                    foldGroundSelectionSet schema clause objectType
                      (head :: tail) = .ok selectionShape := by
                  simpa [hselectionSet] using hselectionFold
                simp [hselectionFold']
      · exact ⟨mergeResponseShapes_decoderShapeInvariant schema support
              parentType selectionShape restShape hselectionParentInvariant
              hrestInvariant hcompatible,
            ShapeClausesEqual.merge clause selectionShape restShape
              hselectionClauses hrestClauses,
            fun hparentObject =>
              (objectType_not_abstractType schema parentType
                hparentObject habstract).elim,
            fun _ => ShapeObjectTypesIn.merge _ _ _
              (hselectionKeys.mono
                (by simp [NormalForm.inlineFragmentTypeCondition?]))
              (hrestKeys.mono (fun candidate hmem => by
                simp [NormalForm.inlineFragmentTypeCondition?, hmem]))⟩
  | composite hcomposite hselection ihselection =>
      exact Or.inl ihselection
  | leaf hleaf =>
      exact Or.inr ⟨hleaf, rfl⟩

/-- Every actual ground image constructively folds to a decoder-invariant
shape.  Object scopes expose their source response names and singleton object
key; abstract scopes expose their source fragment object keys. -/
theorem foldGroundSelectionSet_success_of_image_with_invariant
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (hvalid : clause.Valid support)
    (hcomplete : clause.CompleteMinterm support)
    {parentType : Name} {selectionSet : List Selection}
    (himage : GroundSelectionSetImage schema parentType selectionSet) :
    ∃ shape,
      foldGroundSelectionSet schema clause parentType selectionSet = .ok shape
      ∧ DecoderShapeInvariant schema support parentType shape
      ∧ ShapeClausesEqual clause shape
      ∧ (schema.objectType parentType ->
        ShapeResponseNamesIn
            (selectionSet.filterMap Selection.responseName?) shape
        ∧ ShapeObjectTypesIn [parentType] shape)
      ∧ (AbstractType schema parentType ->
        ShapeObjectTypesIn
          (selectionSet.filterMap NormalForm.inlineFragmentTypeCondition?) shape) := by
  simpa [GroundFoldInvariantResult] using
    foldGroundSelectionSet_invariant_success_of_image schema support clause
      hvalid hcomplete himage

theorem foldGroundSelectionSet_invariant_of_image
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (hvalid : clause.Valid support)
    (hcomplete : clause.CompleteMinterm support)
    {parentType : Name} {selectionSet : List Selection} {shape : ResponseShape}
    (himage : GroundSelectionSetImage schema parentType selectionSet)
    (hfold : foldGroundSelectionSet schema clause parentType selectionSet = .ok shape) :
    GroundFoldInvariantResult schema support clause parentType selectionSet shape := by
  rcases foldGroundSelectionSet_invariant_success_of_image schema support clause
      hvalid hcomplete himage with ⟨resultShape, hresultFold, hresult⟩
  have heq : resultShape = shape := Except.ok.inj (hresultFold.symm.trans hfold)
  exact heq ▸ hresult

/-- The public image endpoint used by complete-normal decoding. -/
theorem foldGroundSelectionSet_decoderShapeInvariant_of_image
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (parentType : Name) (selectionSet : List Selection) (shape : ResponseShape)
    (hvalid : clause.Valid support)
    (hcomplete : clause.CompleteMinterm support)
    (himage : GroundSelectionSetImage schema parentType selectionSet)
    (hfold : foldGroundSelectionSet schema clause parentType selectionSet = .ok shape) :
    DecoderShapeInvariant schema support parentType shape
    ∧ ShapeClausesEqual clause shape := by
  have hresult := foldGroundSelectionSet_invariant_of_image schema support clause
    hvalid hcomplete himage hfold
  exact ⟨hresult.1, hresult.2.1⟩

end ResponseShape

end GraphQL
