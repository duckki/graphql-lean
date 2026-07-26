import GraphQL.NamedFragment.Inline
import GraphQL.NamedFragment.Translate
import Proofs.GraphQL.NamedFragment.Inline.Basic
import Proofs.GraphQL.Validation.FieldMerge
import Proofs.GraphQL.Validation.SelectionValidity

/-! Validation preservation facts for translating spread-free named-fragment operations. -/

namespace GraphQL
namespace NamedFragment
namespace Validation
namespace TranslateValidation

theorem reduceSelection_nonempty_of_inlined
    (selection : Selection)
    (hinlined : Semantics.selectionInlined selection)
    : Translate.reduceSelection selection ≠ [] := by
  cases selection <;>
    simp [Semantics.selectionInlined, Translate.reduceSelection] at hinlined ⊢

theorem reduceSelectionSet_nonempty_of_inlined
    {selectionSet : List Selection}
    (hnonempty : selectionSet ≠ [])
    (hinlined : Semantics.selectionSetInlined selectionSet)
    : Translate.reduceSelectionSet selectionSet ≠ [] := by
  cases selectionSet with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons selection rest =>
      cases selection <;>
        simp [Semantics.selectionSetInlined, Semantics.selectionInlined,
          Translate.reduceSelectionSet, Translate.reduceSelection]
          at hinlined ⊢

theorem selectionSetInlined_append
    {left right : List Selection}
    (hleft : Semantics.selectionSetInlined left)
    (hright : Semantics.selectionSetInlined right)
    : Semantics.selectionSetInlined (left ++ right) := by
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      simp [Semantics.selectionSetInlined] at hleft ⊢
      exact ⟨hleft.1, ih hleft.2⟩

theorem reduceSelectionSet_append (left right : List Selection)
    : Translate.reduceSelectionSet (left ++ right)
      = Translate.reduceSelectionSet left ++ Translate.reduceSelectionSet right := by
  induction left with
  | nil =>
      simp [Translate.reduceSelectionSet]
  | cons selection rest ih =>
      simp [Translate.reduceSelectionSet, ih, List.append_assoc]

mutual
  theorem inlineSelection_nil_eq_of_inlined
      : ∀ (selection : Selection),
          Semantics.selectionInlined selection
          -> Inline.inlineSelection [] selection = selection
    | .field responseName fieldName arguments directives selectionSet,
        hinlined => by
        simp [Semantics.selectionInlined] at hinlined
        simp [Inline.inlineSelection,
          inlineSelectionSet_nil_eq_of_inlined selectionSet hinlined]
    | .inlineFragment typeCondition directives selectionSet, hinlined => by
        simp [Semantics.selectionInlined] at hinlined
        simp [Inline.inlineSelection,
          inlineSelectionSet_nil_eq_of_inlined selectionSet hinlined]
    | .fragmentSpread fragmentName directives, hinlined => by
        simp [Semantics.selectionInlined] at hinlined

  theorem inlineSelectionSet_nil_eq_of_inlined
      : ∀ (selectionSet : List Selection),
          Semantics.selectionSetInlined selectionSet
          -> Inline.inlineSelectionSet [] selectionSet = selectionSet
    | [], _hinlined => by
        simp
    | selection :: rest, hinlined => by
        simp [Semantics.selectionSetInlined] at hinlined
        simp [Inline.inlineSelectionSet,
          inlineSelection_nil_eq_of_inlined selection hinlined.1,
          inlineSelectionSet_nil_eq_of_inlined rest hinlined.2]
end

mutual
  theorem selectionValid_toSpec_of_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
            {parentType : Name} {selection : Selection},
          selectionValid schema variableDefinitions [] parentType selection
          -> Semantics.selectionInlined selection
          -> GraphQL.Validation.selectionSetValid schema variableDefinitions parentType
              (Translate.reduceSelection selection)
    | schema, variableDefinitions, parentType,
        .field responseName fieldName arguments directives selectionSet,
        hvalid, hinlined => by
        simp [selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, fieldDefinition, hlookup, harguments, hfield⟩
        simp [Semantics.selectionInlined] at hinlined
        simp [Translate.reduceSelection,
          GraphQL.Validation.selectionSetValid,
          GraphQL.Validation.selectionValid]
        exact ⟨hdirectives, fieldDefinition, hlookup, harguments,
          fieldSelectionSetValid_toSpec_of_inlined hfield hinlined⟩
    | schema, variableDefinitions, parentType,
        .inlineFragment none directives selectionSet,
        hvalid, hinlined => by
        simp [selectionValid] at hvalid
        rcases hvalid with ⟨hdirectives, hnonempty, hselectionSet⟩
        simp [Semantics.selectionInlined] at hinlined
        have htranslatedNonempty :
            Translate.reduceSelectionSet selectionSet ≠ [] :=
          reduceSelectionSet_nonempty_of_inlined hnonempty hinlined
        have htranslatedValid :
            GraphQL.Validation.selectionSetValid schema variableDefinitions
              parentType (Translate.reduceSelectionSet selectionSet) :=
          selectionSetValid_toSpec_of_inlined hselectionSet hinlined
        simp [Translate.reduceSelection,
          GraphQL.Validation.selectionSetValid,
          GraphQL.Validation.selectionValid]
        exact ⟨hdirectives, htranslatedNonempty,
          by simpa [GraphQL.Validation.selectionSetValid] using htranslatedValid⟩
    | schema, variableDefinitions, parentType,
        .inlineFragment (some typeCondition) directives selectionSet,
        hvalid, hinlined => by
        simp [selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, hcomposite, hoverlap, hnonempty, hselectionSet⟩
        simp [Semantics.selectionInlined] at hinlined
        have htranslatedNonempty :
            Translate.reduceSelectionSet selectionSet ≠ [] :=
          reduceSelectionSet_nonempty_of_inlined hnonempty hinlined
        have htranslatedValid :
            GraphQL.Validation.selectionSetValid schema variableDefinitions
              typeCondition
              (Translate.reduceSelectionSet selectionSet) :=
          selectionSetValid_toSpec_of_inlined hselectionSet hinlined
        simp [Translate.reduceSelection,
          GraphQL.Validation.selectionSetValid,
          GraphQL.Validation.selectionValid]
        exact ⟨hdirectives, hcomposite, hoverlap, htranslatedNonempty,
          by simpa [GraphQL.Validation.selectionSetValid] using htranslatedValid⟩
    | _schema, _variableDefinitions, _parentType,
        .fragmentSpread _fragmentName _directives, _hvalid, hinlined => by
        simp [Semantics.selectionInlined] at hinlined

  theorem selectionSetValid_toSpec_of_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
            {parentType : Name} {selectionSet : List Selection},
          selectionSetValid schema variableDefinitions [] parentType selectionSet
          -> Semantics.selectionSetInlined selectionSet
          -> GraphQL.Validation.selectionSetValid schema variableDefinitions parentType
              (Translate.reduceSelectionSet selectionSet)
    | _schema, _variableDefinitions, _parentType, [], _hvalid, _hinlined => by
        simp [Translate.reduceSelectionSet,
          GraphQL.Validation.selectionSetValid]
    | schema, variableDefinitions, parentType, selection :: rest,
        hvalid, hinlined => by
        simp [Semantics.selectionSetInlined] at hinlined
        have hvalidPair := hvalid
        simp [selectionSetValid] at hvalidPair
        have hselectionValid :
            selectionValid schema variableDefinitions [] parentType selection :=
          hvalidPair.1
        have hrestValid :
            selectionSetValid schema variableDefinitions [] parentType rest := by
          simpa [selectionSetValid] using hvalidPair.2
        have htranslatedSelection :
            GraphQL.Validation.selectionSetValid schema variableDefinitions
              parentType (Translate.reduceSelection selection) :=
          selectionValid_toSpec_of_inlined hselectionValid hinlined.1
        have htranslatedRest :
            GraphQL.Validation.selectionSetValid schema variableDefinitions
              parentType (Translate.reduceSelectionSet rest) :=
          selectionSetValid_toSpec_of_inlined hrestValid hinlined.2
        simpa [Translate.reduceSelectionSet] using
          GraphQL.Validation.selectionSetValid_append htranslatedSelection
            htranslatedRest

  theorem fieldSelectionSetValid_toSpec_of_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
            {fieldDefinition : FieldDefinition} {selectionSet : List Selection},
          fieldSelectionSetValid schema variableDefinitions []
            fieldDefinition selectionSet
          -> Semantics.selectionSetInlined selectionSet
          -> GraphQL.Validation.fieldSelectionSetValid schema variableDefinitions
              fieldDefinition (Translate.reduceSelectionSet selectionSet)
    | schema, variableDefinitions, fieldDefinition, selectionSet,
        hvalid, hinlined => by
        simp [fieldSelectionSetValid,
          GraphQL.Validation.fieldSelectionSetValid] at hvalid ⊢
        rcases hvalid with ⟨houtput, hshape⟩
        refine ⟨houtput, ?_⟩
        cases hshape with
        | inl hleaf =>
            left
            rcases hleaf with ⟨hleafType, hselectionSetEmpty⟩
            exact ⟨hleafType, by simp [hselectionSetEmpty,
              Translate.reduceSelectionSet]⟩
        | inr hcomposite =>
            right
            rcases hcomposite with
              ⟨hcompositeType, hnonempty, hselectionSetValid⟩
            exact ⟨hcompositeType,
              reduceSelectionSet_nonempty_of_inlined hnonempty hinlined,
              selectionSetValid_toSpec_of_inlined hselectionSetValid hinlined⟩
end

def scopedFieldToSpec (field : FieldMerge.ScopedField) : GraphQL.FieldMerge.ScopedField :=
  {
    parentType := field.parentType
    responseName := field.responseName
    fieldName := field.fieldName
    arguments := field.arguments
    outputType := field.outputType
    selectionSet := Translate.reduceSelectionSet field.selectionSet
  }

private def collectExpandedFields (schema : Schema)
    : Name -> List Selection -> List FieldMerge.ScopedField
  | _parentType, [] => []
  | parentType, selection :: rest =>
      let current :=
        match selection with
        | .field responseName fieldName arguments _directives selectionSet =>
            match schema.lookupField parentType fieldName with
            | none => []
            | some fieldDefinition =>
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  outputType := fieldDefinition.outputType,
                  selectionSet := selectionSet,
                  availableFragments := []
                }]
        | .inlineFragment none _directives selectionSet =>
            collectExpandedFields schema parentType selectionSet
        | .inlineFragment (some typeCondition) _directives selectionSet =>
            collectExpandedFields schema typeCondition selectionSet
        | .fragmentSpread _fragmentName _directives => []
      current ++ collectExpandedFields schema parentType rest

theorem collectExpandedFields_toSpec_of_inlined (schema : Schema) (parentType : Name)
    : ∀ (selectionSet : List Selection),
        Semantics.selectionSetInlined selectionSet
        -> (collectExpandedFields schema parentType selectionSet).map scopedFieldToSpec
            = GraphQL.FieldMerge.collectFields schema parentType
                (Translate.reduceSelectionSet selectionSet)
  | [], _hinlined => by
      simp [collectExpandedFields, GraphQL.FieldMerge.collectFields,
        Translate.reduceSelectionSet]
  | selection :: rest, hinlined => by
      simp [Semantics.selectionSetInlined] at hinlined
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [collectExpandedFields,
                GraphQL.FieldMerge.collectFields,
                Translate.reduceSelectionSet,
                Translate.reduceSelection, hlookup,
                collectExpandedFields_toSpec_of_inlined schema parentType rest
                  hinlined.2]
          | some fieldDefinition =>
              simp [collectExpandedFields,
                GraphQL.FieldMerge.collectFields,
                Translate.reduceSelectionSet,
                Translate.reduceSelection, scopedFieldToSpec, hlookup,
                collectExpandedFields_toSpec_of_inlined schema parentType rest
                  hinlined.2]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [collectExpandedFields,
                GraphQL.FieldMerge.collectFields,
                Translate.reduceSelectionSet,
                Translate.reduceSelection, List.map_append,
                collectExpandedFields_toSpec_of_inlined schema parentType
                  selectionSet hinlined.1,
                collectExpandedFields_toSpec_of_inlined schema parentType rest
                  hinlined.2]
          | some typeCondition =>
              simp [collectExpandedFields,
                GraphQL.FieldMerge.collectFields,
                Translate.reduceSelectionSet,
                Translate.reduceSelection, List.map_append,
                collectExpandedFields_toSpec_of_inlined schema typeCondition
                  selectionSet hinlined.1,
                collectExpandedFields_toSpec_of_inlined schema parentType rest
                  hinlined.2]
      | fragmentSpread fragmentName directives =>
          simp [Semantics.selectionInlined] at hinlined

theorem collectExpandedFields_mem_selectionSetInlined
    (schema : Schema) (parentType : Name)
    : ∀ {selectionSet : List Selection} {field : FieldMerge.ScopedField},
        field ∈ collectExpandedFields schema parentType selectionSet
        -> Semantics.selectionSetInlined selectionSet
        -> Semantics.selectionSetInlined field.selectionSet
  | [], _field, hfield, _hinlined => by
      simp [collectExpandedFields] at hfield
  | selection :: rest, field, hfield, hinlined => by
      simp [Semantics.selectionSetInlined] at hinlined
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [collectExpandedFields, hlookup] at hfield
              exact collectExpandedFields_mem_selectionSetInlined schema
                parentType hfield hinlined.2
          | some fieldDefinition =>
              simp [collectExpandedFields, hlookup] at hfield
              rcases hfield with hhead | hrest
              · subst field
                simpa [Semantics.selectionInlined] using hinlined.1
              · exact collectExpandedFields_mem_selectionSetInlined schema
                  parentType hrest hinlined.2
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [collectExpandedFields] at hfield
              rcases hfield with hchild | hrest
              · exact collectExpandedFields_mem_selectionSetInlined schema
                  parentType hchild hinlined.1
              · exact collectExpandedFields_mem_selectionSetInlined schema
                  parentType hrest hinlined.2
          | some typeCondition =>
              simp [collectExpandedFields] at hfield
              rcases hfield with hchild | hrest
              · exact collectExpandedFields_mem_selectionSetInlined schema
                  typeCondition hchild hinlined.1
              · exact collectExpandedFields_mem_selectionSetInlined schema
                  parentType hrest hinlined.2
      | fragmentSpread fragmentName directives =>
          simp [Semantics.selectionInlined] at hinlined

theorem collectExpandedFields_mem_availableFragments_nil
    (schema : Schema) (parentType : Name)
    : ∀ {selectionSet : List Selection} {field : FieldMerge.ScopedField},
        field ∈ collectExpandedFields schema parentType selectionSet
        -> field.availableFragments = []
  | [], _field, hfield => by
      simp [collectExpandedFields] at hfield
  | selection :: rest, field, hfield => by
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [collectExpandedFields, hlookup] at hfield
              exact collectExpandedFields_mem_availableFragments_nil schema
                parentType hfield
          | some fieldDefinition =>
              simp [collectExpandedFields, hlookup] at hfield
              rcases hfield with hhead | hrest
              · subst field
                rfl
              · exact collectExpandedFields_mem_availableFragments_nil schema
                  parentType hrest
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [collectExpandedFields] at hfield
              rcases hfield with hchild | hrest
              · exact collectExpandedFields_mem_availableFragments_nil schema
                  parentType hchild
              · exact collectExpandedFields_mem_availableFragments_nil schema
                  parentType hrest
          | some typeCondition =>
              simp [collectExpandedFields] at hfield
              rcases hfield with hchild | hrest
              · exact collectExpandedFields_mem_availableFragments_nil schema
                  typeCondition hchild
              · exact collectExpandedFields_mem_availableFragments_nil schema
                  parentType hrest
      | fragmentSpread fragmentName directives =>
          simp [collectExpandedFields] at hfield
          exact collectExpandedFields_mem_availableFragments_nil schema
            parentType hfield

theorem collectFields_nil_eq_collectExpandedFields_of_inlined
    (schema : Schema) (parentType : Name)
    : ∀ (selectionSet : List Selection),
        Semantics.selectionSetInlined selectionSet
        -> FieldMerge.collectFields schema [] parentType selectionSet
            = collectExpandedFields schema parentType selectionSet
  | [], _hinlined => by
      simp [FieldMerge.collectFields, collectExpandedFields]
  | selection :: rest, hinlined => by
      simp [Semantics.selectionSetInlined] at hinlined
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, FieldMerge.collectSelection,
                collectExpandedFields, hlookup,
                collectFields_nil_eq_collectExpandedFields_of_inlined schema
                  parentType rest hinlined.2]
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, FieldMerge.collectSelection,
                collectExpandedFields, hlookup,
                collectFields_nil_eq_collectExpandedFields_of_inlined schema
                  parentType rest hinlined.2]
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              simp [FieldMerge.collectFields, FieldMerge.collectSelection,
                collectExpandedFields,
                collectFields_nil_eq_collectExpandedFields_of_inlined schema
                  parentType selectionSet hinlined.1,
                collectFields_nil_eq_collectExpandedFields_of_inlined schema
                  parentType rest hinlined.2]
          | some typeCondition =>
              simp [FieldMerge.collectFields, FieldMerge.collectSelection,
                collectExpandedFields,
                collectFields_nil_eq_collectExpandedFields_of_inlined schema
                  typeCondition selectionSet hinlined.1,
                collectFields_nil_eq_collectExpandedFields_of_inlined schema
                  parentType rest hinlined.2]
      | fragmentSpread fragmentName directives =>
          simp [Semantics.selectionInlined] at hinlined

theorem collectFields_toSpec_of_inlined
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    (hinlined : Semantics.selectionSetInlined selectionSet)
    : (FieldMerge.collectFields schema [] parentType selectionSet).map scopedFieldToSpec
      = GraphQL.FieldMerge.collectFields schema parentType
          (Translate.reduceSelectionSet selectionSet) := by
  rw [collectFields_nil_eq_collectExpandedFields_of_inlined schema parentType
    selectionSet hinlined]
  exact collectExpandedFields_toSpec_of_inlined schema parentType selectionSet
    hinlined

theorem collectFields_mem_selectionSetInlined
    (schema : Schema) (parentType : Name)
    {selectionSet : List Selection} {field : FieldMerge.ScopedField}
    (hfield : field ∈ FieldMerge.collectFields schema [] parentType selectionSet)
    (hinlined : Semantics.selectionSetInlined selectionSet)
    : Semantics.selectionSetInlined field.selectionSet := by
  rw [collectFields_nil_eq_collectExpandedFields_of_inlined schema parentType
    selectionSet hinlined] at hfield
  exact collectExpandedFields_mem_selectionSetInlined schema parentType hfield
    hinlined

theorem collectFields_nil_mem_availableFragments_nil
    (schema : Schema) (parentType : Name)
    {selectionSet : List Selection} {field : FieldMerge.ScopedField}
    (hfield : field ∈ FieldMerge.collectFields schema [] parentType selectionSet)
    (hinlined : Semantics.selectionSetInlined selectionSet)
    : field.availableFragments = [] := by
  rw [collectFields_nil_eq_collectExpandedFields_of_inlined schema parentType
    selectionSet hinlined] at hfield
  exact collectExpandedFields_mem_availableFragments_nil schema parentType hfield

theorem fieldsInSetCanMerge_toSpecInductive_of_inlined
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    (hinlined : Semantics.selectionSetInlined selectionSet)
    (hmerge : FieldMerge.FieldsInSetCanMerge schema [] parentType selectionSet)
    : GraphQL.FieldMerge.FieldsInSetCanMerge schema parentType
        (Translate.reduceSelectionSet selectionSet) := by
  revert hinlined
  refine FieldMerge.FieldsInSetCanMerge.rec
    (motive_1 := fun parentType selectionSet _ =>
      Semantics.selectionSetInlined selectionSet ->
        GraphQL.FieldMerge.FieldsInSetCanMerge schema parentType
          (Translate.reduceSelectionSet selectionSet))
    (motive_2 := fun left right _ =>
      left.availableFragments = [] ->
      right.availableFragments = [] ->
      Semantics.selectionSetInlined left.selectionSet ->
      Semantics.selectionSetInlined right.selectionSet ->
        GraphQL.FieldMerge.FieldsForNameCanMerge schema
          (scopedFieldToSpec left) (scopedFieldToSpec right))
    ?setCase ?fieldCase hmerge
  · intro parentType selectionSet hfields ihFields hinlined
    refine GraphQL.FieldMerge.FieldsInSetCanMerge.intro parentType
      (Translate.reduceSelectionSet selectionSet) ?_
    dsimp
    intro left hleft right hright hresponse
    have hcollect :=
      collectFields_toSpec_of_inlined schema parentType selectionSet hinlined
    rw [← hcollect] at hleft hright
    rcases List.mem_map.mp hleft with
      ⟨sourceLeft, hsourceLeft, hsourceLeftEq⟩
    rcases List.mem_map.mp hright with
      ⟨sourceRight, hsourceRight, hsourceRightEq⟩
    cases hsourceLeftEq
    cases hsourceRightEq
    exact ihFields sourceLeft hsourceLeft sourceRight hsourceRight
      (by simpa [scopedFieldToSpec] using hresponse)
      (collectFields_nil_mem_availableFragments_nil schema parentType
        hsourceLeft hinlined)
      (collectFields_nil_mem_availableFragments_nil schema parentType
        hsourceRight hinlined)
      (collectFields_mem_selectionSetInlined schema parentType
        hsourceLeft hinlined)
      (collectFields_mem_selectionSetInlined schema parentType
        hsourceRight hinlined)
  · intro left right hshape hidentity hsubfields ihSubfields hleftAvailable
      hrightAvailable hleftInlined hrightInlined
    refine GraphQL.FieldMerge.FieldsForNameCanMerge.intro
      (scopedFieldToSpec left) (scopedFieldToSpec right) ?_ ?_ ?_
    · simpa [scopedFieldToSpec, GraphQL.FieldMerge.sameResponseShape] using hshape
    · intro hparents
      simpa [scopedFieldToSpec] using hidentity hparents
    · intro hparents objectType
      refine GraphQL.FieldMerge.FieldsInSetCanMerge.intro objectType
        ((scopedFieldToSpec left).selectionSet
          ++ (scopedFieldToSpec right).selectionSet) ?_
      dsimp
      intro subLeft hsubLeft subRight hsubRight hresponse
      rw [GraphQL.FieldMerge.collectFields_append] at hsubLeft hsubRight
      have hleftCollect :=
        collectFields_toSpec_of_inlined schema objectType
          left.selectionSet hleftInlined
      have hrightCollect :=
        collectFields_toSpec_of_inlined schema objectType
          right.selectionSet hrightInlined
      rw [← hleftAvailable] at hleftCollect
      rw [← hrightAvailable] at hrightCollect
      have hcollect :
          (FieldMerge.collectFields schema left.availableFragments objectType
                left.selectionSet
              ++ FieldMerge.collectFields schema right.availableFragments
                objectType right.selectionSet).map scopedFieldToSpec
            =
          GraphQL.FieldMerge.collectFields schema objectType
              (Translate.reduceSelectionSet left.selectionSet)
            ++
          GraphQL.FieldMerge.collectFields schema objectType
              (Translate.reduceSelectionSet right.selectionSet) := by
        simp [List.map_append, hleftCollect, hrightCollect]
      change subLeft ∈
          GraphQL.FieldMerge.collectFields schema objectType
            (Translate.reduceSelectionSet left.selectionSet)
          ++ GraphQL.FieldMerge.collectFields schema objectType
            (Translate.reduceSelectionSet right.selectionSet) at hsubLeft
      change subRight ∈
          GraphQL.FieldMerge.collectFields schema objectType
            (Translate.reduceSelectionSet left.selectionSet)
          ++ GraphQL.FieldMerge.collectFields schema objectType
            (Translate.reduceSelectionSet right.selectionSet) at hsubRight
      rw [← hcollect] at hsubLeft hsubRight
      rcases List.mem_map.mp hsubLeft with
        ⟨sourceLeft, hsourceLeft, hsourceLeftEq⟩
      rcases List.mem_map.mp hsubRight with
        ⟨sourceRight, hsourceRight, hsourceRightEq⟩
      cases hsourceLeftEq
      cases hsourceRightEq
      have hsourceLeftData :
          sourceLeft.availableFragments = []
            ∧ Semantics.selectionSetInlined sourceLeft.selectionSet := by
        rw [hleftAvailable, hrightAvailable] at hsourceLeft
        simp at hsourceLeft
        rcases hsourceLeft with hsourceLeft | hsourceLeft
        · exact ⟨collectFields_nil_mem_availableFragments_nil schema
              objectType hsourceLeft hleftInlined,
            collectFields_mem_selectionSetInlined schema objectType
              hsourceLeft hleftInlined⟩
        · exact ⟨collectFields_nil_mem_availableFragments_nil schema
              objectType hsourceLeft hrightInlined,
            collectFields_mem_selectionSetInlined schema objectType
              hsourceLeft hrightInlined⟩
      have hsourceRightData :
          sourceRight.availableFragments = []
            ∧ Semantics.selectionSetInlined sourceRight.selectionSet := by
        rw [hleftAvailable, hrightAvailable] at hsourceRight
        simp at hsourceRight
        rcases hsourceRight with hsourceRight | hsourceRight
        · exact ⟨collectFields_nil_mem_availableFragments_nil schema
              objectType hsourceRight hleftInlined,
            collectFields_mem_selectionSetInlined schema objectType
              hsourceRight hleftInlined⟩
        · exact ⟨collectFields_nil_mem_availableFragments_nil schema
              objectType hsourceRight hrightInlined,
            collectFields_mem_selectionSetInlined schema objectType
              hsourceRight hrightInlined⟩
      exact ihSubfields hparents objectType sourceLeft hsourceLeft
        sourceRight hsourceRight
        (by simpa [scopedFieldToSpec] using hresponse)
        hsourceLeftData.1 hsourceRightData.1 hsourceLeftData.2
        hsourceRightData.2

theorem fieldsInSetCanMerge_toSpec_of_inlined
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    (hinlined : Semantics.selectionSetInlined selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema [] parentType selectionSet)
    : GraphQL.FieldMerge.fieldsInSetCanMerge schema parentType
        (Translate.reduceSelectionSet selectionSet) := by
  unfold FieldMerge.fieldsInSetCanMerge at hmerge
  unfold GraphQL.FieldMerge.fieldsInSetCanMerge
  exact fieldsInSetCanMerge_toSpecInductive_of_inlined hinlined hmerge

theorem operationDefinitionValid_toSpec_of_inlined
    {schema : Schema} {operation : Operation}
    (hvalid : operationDefinitionValid schema operation)
    (hinlined : Semantics.operationInlined operation)
    : GraphQL.Validation.operationDefinitionValid schema
        (Translate.reduceOperation operation) := by
  rcases hinlined with ⟨hfragments, hselectionInlined⟩
  rcases hvalid with
    ⟨hroot, hrootComposite, hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsValid, hselectionNonempty,
      hselectionValid, hmerge⟩
  rw [hfragments] at hselectionValid hmerge
  simp [Translate.reduceOperation,
    GraphQL.Validation.operationDefinitionValid]
  exact ⟨hroot, hrootComposite, hvariables,
    reduceSelectionSet_nonempty_of_inlined hselectionNonempty
      hselectionInlined,
    selectionSetValid_toSpec_of_inlined hselectionValid hselectionInlined,
    fieldsInSetCanMerge_toSpec_of_inlined hselectionInlined hmerge⟩

end TranslateValidation
end Validation
end NamedFragment
end GraphQL
