import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness
import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMergeLookup

/-!
Basic validity support facts for ground-type normalization.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

mutual
  def selectionContainsTypeConditionFeasibleField (schema : Schema)
      (typeConditions : List Name)
      : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives _selectionSet =>
        typeConditionStackFeasible schema typeConditions
    | .inlineFragment none _directives selectionSet =>
        selectionSetContainsTypeConditionFeasibleField schema typeConditions selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetContainsTypeConditionFeasibleField schema
          (typeCondition :: typeConditions) selectionSet

  def selectionSetContainsTypeConditionFeasibleField (schema : Schema)
      (typeConditions : List Name)
      : List Selection -> Prop
    | [] => False
    | selection :: rest =>
        selectionContainsTypeConditionFeasibleField schema typeConditions selection
        ∨ selectionSetContainsTypeConditionFeasibleField schema typeConditions rest
end

mutual
  def selectionInlineFragmentsNonempty : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetInlineFragmentsNonempty selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSet ≠ [] ∧ selectionSetInlineFragmentsNonempty selectionSet

  def selectionSetInlineFragmentsNonempty (selectionSet : List Selection) : Prop :=
    ∀ selection, selection ∈ selectionSet -> selectionInlineFragmentsNonempty selection
end

mutual
  theorem selectionInlineFragmentsNonempty_of_selectionValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      : ∀ parentType selection,
          Validation.selectionValid schema variableDefinitions parentType selection
          -> selectionInlineFragmentsNonempty selection
    | parentType,
      .field _responseName _fieldName _arguments _directives selectionSet,
      hvalid => by
        unfold selectionInlineFragmentsNonempty
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, _hlookup, _harguments, hchild⟩
        simp [Validation.fieldSelectionSetValid] at hchild
        rcases hchild.2 with hleaf | hcomposite
        · rw [hleaf.2]
          unfold selectionSetInlineFragmentsNonempty
          intro selection hselection
          cases hselection
        · exact
            selectionSetInlineFragmentsNonempty_of_selectionSetValid
              schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet
              hcomposite.2.2
    | parentType,
      .inlineFragment none _directives selectionSet, hvalid => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        exact ⟨hvalid'.2.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid
            schema variableDefinitions parentType selectionSet hvalid'.2.2⟩
    | _parentType,
      .inlineFragment (some typeCondition) _directives selectionSet,
      hvalid => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        exact ⟨hvalid'.2.2.2.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid
            schema variableDefinitions typeCondition selectionSet
            hvalid'.2.2.2.2⟩

  theorem selectionSetInlineFragmentsNonempty_of_selectionSetValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      : ∀ parentType selectionSet,
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetInlineFragmentsNonempty selectionSet
    | parentType, selectionSet, hvalid => by
        unfold selectionSetInlineFragmentsNonempty
        unfold Validation.selectionSetValid at hvalid
        intro selection hselection
        exact selectionInlineFragmentsNonempty_of_selectionValid schema
          variableDefinitions parentType selection (hvalid selection hselection)
end

mutual
  theorem inputValue_structuralEquivalent_refl
      : ∀ value, InputValue.structuralEquivalent value value
    | .null => by simp [InputValue.structuralEquivalent]
    | .int _ => by simp [InputValue.structuralEquivalent]
    | .float _ => by simp [InputValue.structuralEquivalent]
    | .string _ => by simp [InputValue.structuralEquivalent]
    | .boolean _ => by simp [InputValue.structuralEquivalent]
    | .enum _ => by simp [InputValue.structuralEquivalent]
    | .variable _ => by simp [InputValue.structuralEquivalent]
    | .list values => by
        simp [InputValue.structuralEquivalent,
          inputValues_structuralEquivalent_refl values]
    | .object fields => by
        simp [InputValue.structuralEquivalent,
          inputObjectFields_structuralEquivalent_refl fields]

  theorem inputValues_structuralEquivalent_refl
      : ∀ values, InputValue.structuralValuesEquivalent values values
    | [] => by simp [InputValue.structuralValuesEquivalent]
    | value :: rest => by
        simp [InputValue.structuralValuesEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputValues_structuralEquivalent_refl rest]

  theorem inputObjectFields_structuralEquivalent_refl
      : ∀ fields, InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => by simp [InputValue.structuralObjectFieldsEquivalent]
    | (name, value) :: rest => by
        simp [InputValue.structuralObjectFieldsEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputObjectFields_structuralEquivalent_refl rest]
end

theorem inputValue_equivalent_refl (value : InputValue) : value.equivalent value := by
  exact inputValue_structuralEquivalent_refl value.canonical

theorem argument_equivalent_refl (argument : Argument)
    : argument.equivalent argument := by
  exact ⟨rfl, inputValue_equivalent_refl argument.value⟩

theorem argumentsEquivalent_refl (arguments : List Argument)
    : Argument.argumentsEquivalent arguments arguments := by
  constructor
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl argument⟩
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl argument⟩

theorem objectType_isCompositeType {schema : Schema} {typeName : Name}
    : schema.objectType typeName -> schema.isCompositeType typeName := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  exact ⟨.object objectType, hlookup, by simp [TypeDefinition.isCompositeType]⟩

theorem leafTypeNameBool_eq_true_isLeafType (schema : Schema) {typeName : Name}
    : leafTypeNameBool schema typeName = true -> schema.isLeafType typeName := by
  intro hleaf
  unfold leafTypeNameBool at hleaf
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hleaf
  | some typeDefinition =>
      cases typeDefinition with
      | builtinScalar scalar =>
          exact ⟨.builtinScalar scalar, hlookup,
            by simp [TypeDefinition.isLeafType]⟩
      | customScalar scalar =>
          exact ⟨.customScalar scalar, hlookup,
            by simp [TypeDefinition.isLeafType]⟩
      | object objectType =>
          simp [hlookup] at hleaf
      | interface interfaceType =>
          simp [hlookup] at hleaf
      | union unionType =>
          simp [hlookup] at hleaf
      | enum enumType =>
          exact ⟨.enum enumType, hlookup,
            by simp [TypeDefinition.isLeafType]⟩
      | inputObject inputObjectType =>
          simp [hlookup] at hleaf

theorem leafTypeNameBool_eq_true_of_isLeafType (schema : Schema) {typeName : Name}
    : schema.isLeafType typeName -> leafTypeNameBool schema typeName = true := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, hleafDefinition⟩
  cases typeDefinition with
  | builtinScalar scalar =>
      simp [leafTypeNameBool, hlookup]
  | customScalar scalar =>
      simp [leafTypeNameBool, hlookup]
  | object objectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | interface interfaceType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | union unionType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | enum enumType =>
      simp [leafTypeNameBool, hlookup]
  | inputObject inputObjectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition

theorem isLeafType_not_isCompositeType {schema : Schema} {typeName : Name}
    : schema.isLeafType typeName -> schema.isCompositeType typeName -> False := by
  intro hleaf hcomposite
  rcases hleaf with ⟨leafDefinition, hleafLookup, hleafType⟩
  rcases hcomposite with
    ⟨compositeDefinition, hcompositeLookup, hcompositeType⟩
  rw [hleafLookup] at hcompositeLookup
  cases hcompositeLookup
  cases leafDefinition <;>
    simp [TypeDefinition.isLeafType, TypeDefinition.isCompositeType]
      at hleafType hcompositeType

theorem leafTypeNameBool_eq_false_of_isCompositeType (schema : Schema) {typeName : Name}
    : schema.isCompositeType typeName -> leafTypeNameBool schema typeName = false := by
  intro hcomposite
  cases hleaf : leafTypeNameBool schema typeName
  · rfl
  · exact False.elim
      (isLeafType_not_isCompositeType
        (leafTypeNameBool_eq_true_isLeafType schema hleaf)
        hcomposite)

theorem objectTypeNameBool_eq_false_of_isLeafType (schema : Schema) {typeName : Name}
    : schema.isLeafType typeName -> objectTypeNameBool schema typeName = false := by
  intro hleaf
  rcases hleaf with ⟨typeDefinition, hlookup, hleafDefinition⟩
  cases typeDefinition with
  | builtinScalar scalar =>
      simp [objectTypeNameBool, hlookup]
  | customScalar scalar =>
      simp [objectTypeNameBool, hlookup]
  | object objectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | interface interfaceType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | union unionType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition
  | enum enumType =>
      simp [objectTypeNameBool, hlookup]
  | inputObject inputObjectType =>
      simp [TypeDefinition.isLeafType] at hleafDefinition

theorem possibleTypes_eq_nil_of_leafTypeNameBool (schema : Schema) {typeName : Name}
    : leafTypeNameBool schema typeName = true
      -> schema.getPossibleTypes typeName = [] := by
  intro hleaf
  exact possibleTypes_eq_nil_of_isLeafType schema
    (leafTypeNameBool_eq_true_isLeafType schema hleaf)

theorem object_typeIncludesObject_self (schema : Schema) {typeName : Name}
    : schema.objectType typeName -> schema.typeIncludesObject typeName typeName := by
  intro hobject
  exact List.contains_iff_mem.mp
    (object_typeIncludesObjectBool_self schema hobject)

theorem typesOverlap_possible_object (schema : Schema) {parentType objectType : Name}
    : objectType ∈ schema.getPossibleTypes parentType
      -> schema.objectType objectType
      -> schema.typesOverlap parentType objectType := by
  intro hpossible hobject
  exact ⟨objectType, hpossible,
    object_typeIncludesObject_self schema hobject⟩

theorem typesOverlapBool_eq_true_of_typesOverlap (schema : Schema) {left right : Name}
    : schema.typesOverlap left right -> schema.typesOverlapBool left right = true := by
  intro hoverlap
  rcases hoverlap with ⟨objectName, hleft, hright⟩
  unfold Schema.typesOverlapBool
  rw [List.any_eq_true]
  exact ⟨objectName, hleft, List.contains_iff_mem.mpr hright⟩

theorem possibleTypes_ne_nil_left_of_typesOverlap (schema : Schema) {left right : Name}
    : schema.typesOverlap left right -> schema.getPossibleTypes left ≠ [] := by
  intro hoverlap hnil
  rcases hoverlap with ⟨objectName, hleft, _hright⟩
  unfold Schema.typeIncludesObject at hleft
  rw [hnil] at hleft
  cases hleft

theorem possibleTypes_ne_nil_right_of_typesOverlap (schema : Schema) {left right : Name}
    : schema.typesOverlap left right -> schema.getPossibleTypes right ≠ [] := by
  intro hoverlap hnil
  rcases hoverlap with ⟨objectName, _hleft, hright⟩
  unfold Schema.typeIncludesObject at hright
  rw [hnil] at hright
  cases hright

theorem selectionSetValidInPossibleTypes_nil
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType [] := by
  simp [Validation.selectionSetValidInPossibleTypes]

theorem selectionSetValidInPossibleTypes_cons
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType selection
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          parentType selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType (selection :: selectionSet) := by
  intro hselection hselectionSet
  simp [Validation.selectionSetValidInPossibleTypes, hselection,
    hselectionSet]

theorem selectionSetValidInPossibleTypes_head
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType (selection :: selectionSet)
      -> Validation.selectionValidInPossibleTypes schema variableDefinitions
          parentType selection := by
  intro hvalid
  simpa [Validation.selectionSetValidInPossibleTypes] using hvalid.1

theorem selectionSetValidInPossibleTypes_tail
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType (selection :: selectionSet)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType selectionSet := by
  intro hvalid
  simpa [Validation.selectionSetValidInPossibleTypes] using hvalid.2

theorem selectionSetValidInPossibleTypes_append
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType left
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType right
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      have hhead :=
        selectionSetValidInPossibleTypes_head hleft
      have htail :=
        selectionSetValidInPossibleTypes_tail hleft
      simp [Validation.selectionSetValidInPossibleTypes]
      exact ⟨hhead, ih htail⟩

theorem selectionSetValidInPossibleTypes_append_left
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType (left ++ right)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType left := by
  intro hvalid
  induction left with
  | nil =>
      exact selectionSetValidInPossibleTypes_nil schema
        variableDefinitions parentType
  | cons selection rest ih =>
      simp [Validation.selectionSetValidInPossibleTypes] at hvalid ⊢
      exact ⟨hvalid.1, ih hvalid.2⟩

theorem selectionSetValidInPossibleTypes_append_right
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : Validation.selectionSetValidInPossibleTypes schema
        variableDefinitions parentType (left ++ right)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType right := by
  intro hvalid
  induction left with
  | nil =>
      simpa using hvalid
  | cons selection rest ih =>
      exact ih (selectionSetValidInPossibleTypes_tail hvalid)

theorem selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name)
    : ∀ variableDefinitions parentType selectionSet,
        Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | _variableDefinitions, _parentType, [], _hvalid => by
      simp [withoutFieldSelectionsWithResponseName,
        Validation.selectionSetValidInPossibleTypes]
  | variableDefinitions, parentType, selection :: rest, hvalid => by
      have hhead :=
        selectionSetValidInPossibleTypes_head hvalid
      have htail :=
        selectionSetValidInPossibleTypes_tail hvalid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            exact
              selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
                schema responseName variableDefinitions parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse,
              Validation.selectionSetValidInPossibleTypes]
            exact ⟨hhead,
              selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
                schema responseName variableDefinitions parentType rest htail⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldSelectionsWithResponseName,
            Validation.selectionSetValidInPossibleTypes]
          constructor
          · cases typeCondition with
            | none =>
                intro objectType hobjectType
                have hbody :
                    Validation.selectionSetValidInPossibleTypes schema
                      variableDefinitions objectType selectionSet := by
                  simpa [Validation.selectionValidInPossibleTypes] using
                    hhead objectType hobjectType
                exact
                  selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
                    schema responseName variableDefinitions objectType
                    selectionSet hbody
            | some typeCondition =>
                intro hoverlap
                intro objectType hobjectType
                have hbody :
                    Validation.selectionSetValidInPossibleTypes schema
                      variableDefinitions objectType selectionSet := by
                  simpa [Validation.selectionValidInPossibleTypes] using
                    hhead hoverlap objectType hobjectType
                exact
                  selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
                    schema responseName variableDefinitions objectType
                    selectionSet hbody
          · exact
              selectionSetValidInPossibleTypes_withoutFieldSelectionsWithResponseName
                schema responseName variableDefinitions parentType rest htail

theorem selectionSetValidInPossibleTypes_mergeSelectionSets_of_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions parentType selection.subselections)
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets,
        Validation.selectionSetValidInPossibleTypes]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetValidInPossibleTypes_append
      · exact hvalid selection (by simp)
      · exact
          selectionSetValidInPossibleTypes_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetValidInPossibleTypes_mergeSelectionSets_of_field_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName : Name}
    (selections : List Selection)
    : (∀ selection,
        selection ∈ selections
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections)
      -> (∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ selections
            -> Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType subselections)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions parentType (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetValidInPossibleTypes_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem
    selectionSetValidInPossibleTypes_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName childType : Name} (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions childType subselections)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions childType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)) := by
  intro hfields
  apply selectionSetValidInPossibleTypes_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem selectionSetValid_of_allFields_validInPossibleTypes
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : ∀ selectionSet,
        selectionsAllFields selectionSet
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType selectionSet
        -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
  | [], _hallFields, _himplementation => by
      simp [Validation.selectionSetValid]
  | selection :: rest, hallFields, himplementation => by
      have hheadField : Selection.isField selection :=
        hallFields selection (by simp)
      have htailAllFields : selectionsAllFields rest := by
        intro candidate hcandidate
        exact hallFields candidate
          (List.mem_cons_of_mem selection hcandidate)
      have hheadImplementation :
          Validation.selectionValidInPossibleTypes schema variableDefinitions
            parentType selection :=
        selectionSetValidInPossibleTypes_head himplementation
      have htailImplementation :
          Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions parentType rest :=
        selectionSetValidInPossibleTypes_tail himplementation
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hheadValid :
              Validation.selectionValid schema variableDefinitions parentType
                (Selection.field responseName fieldName arguments directives
                  selectionSet) := by
            simpa [Validation.selectionValidInPossibleTypes] using
              hheadImplementation.1
          have htailValid :
              ∀ candidate, candidate ∈ rest ->
                Validation.selectionValid schema variableDefinitions
                  parentType candidate := by
            simpa [Validation.selectionSetValid] using
              selectionSetValid_of_allFields_validInPossibleTypes
                schema variableDefinitions parentType rest htailAllFields
                htailImplementation
          simp [Validation.selectionSetValid]
          exact ⟨hheadValid, htailValid⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

end GroundTypeNormalization

end NormalForm

end GraphQL
