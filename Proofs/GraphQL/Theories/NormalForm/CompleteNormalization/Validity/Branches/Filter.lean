import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.FieldMerge
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.FilterMerge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldProjection
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterLookup

/-!
Boolean filtering and final complete-normalization branch validity facts.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

open GroundTypeNormalization

attribute [local simp]
  selectionSetContainsTypeConditionFeasibleField selectionSetTypeConditionFeasible

/-!
`selectionSetValidInPossibleTypes` is intentionally operation-facing and
over-approximates typed inline fragments by checking every possible object of
the fragment type. Complete normalization validates one concrete ground branch
at a time, so its proof needs a current-ground-scope version: typed inline
fragments recurse only when they can apply to the current object scope.
-/

mutual
  def selectionValidInCurrentScope (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : Selection -> Prop
    | fieldSelection@(
          .field _responseName fieldName _arguments _directives selectionSet) =>
        Validation.selectionValid schema variableDefinitions parentType fieldSelection
        ∧ match schema.lookupField parentType fieldName with
          | none => False
          | some fieldDefinition =>
              ∀ objectType,
                objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
                -> selectionSetValidInCurrentScope schema
                    variableDefinitions objectType selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetValidInCurrentScope schema variableDefinitions parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typesOverlapBool parentType typeCondition = true
        -> selectionSetValidInCurrentScope schema variableDefinitions
            parentType selectionSet

  def selectionSetValidInCurrentScope (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionValidInCurrentScope schema variableDefinitions parentType selection
        ∧ selectionSetValidInCurrentScope schema variableDefinitions parentType rest
end

mutual
  theorem selectionValidInCurrentScope_of_validInPossibleTypes
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (parentType : Name)
      : schema.objectType parentType
        -> ∀ selection,
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              parentType selection
            -> selectionValidInCurrentScope schema variableDefinitions
                parentType selection
    | hobject,
      .field responseName fieldName arguments directives selectionSet,
      hvalid => by
        simp [Validation.selectionValidInPossibleTypes,
          selectionValidInCurrentScope] at hvalid ⊢
        rcases hvalid with ⟨hselection, hchildren⟩
        exact ⟨hselection, by
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [hlookup] at hchildren
          | some fieldDefinition =>
              have hchildrenForField :
                  ∀ objectType,
                    objectType ∈
                        schema.getPossibleTypes
                          fieldDefinition.outputType.namedType ->
                      Validation.selectionSetValidInPossibleTypes schema
                        variableDefinitions objectType selectionSet := by
                simpa [hlookup] using hchildren
              intro objectType hpossible
              have hchildObject :
                  schema.objectType objectType :=
                SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  hschema fieldDefinition.outputType.namedType objectType
                  hpossible
              exact
                selectionSetValidInCurrentScope_of_validInPossibleTypes
                  schema variableDefinitions hschema objectType hchildObject
                  selectionSet
                  (hchildrenForField objectType hpossible)⟩
    | hobject, .inlineFragment none directives selectionSet, hvalid => by
        simp [Validation.selectionValidInPossibleTypes,
          selectionValidInCurrentScope] at hvalid ⊢
        have hparentPossible :
            parentType ∈ schema.getPossibleTypes parentType :=
          List.contains_iff_mem.mp
            (object_typeIncludesObjectBool_self schema hobject)
        exact selectionSetValidInCurrentScope_of_validInPossibleTypes
          schema variableDefinitions hschema parentType hobject selectionSet
          (hvalid parentType hparentPossible)
    | hobject, .inlineFragment (some typeCondition) directives selectionSet,
      hvalid => by
        simp [Validation.selectionValidInPossibleTypes,
          selectionValidInCurrentScope] at hvalid ⊢
        intro hoverlap
        have hparentPossible :
            parentType ∈ schema.getPossibleTypes typeCondition :=
          List.contains_iff_mem.mp
            (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
              hoverlap)
        exact selectionSetValidInCurrentScope_of_validInPossibleTypes
          schema variableDefinitions hschema parentType hobject selectionSet
          (hvalid hoverlap parentType hparentPossible)

  theorem selectionSetValidInCurrentScope_of_validInPossibleTypes
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (parentType : Name)
      : schema.objectType parentType
        -> ∀ selectionSet,
            Validation.selectionSetValidInPossibleTypes schema variableDefinitions
              parentType selectionSet
            -> selectionSetValidInCurrentScope schema variableDefinitions
                parentType selectionSet
    | _hobject, [], _hvalid => by
        simp [selectionSetValidInCurrentScope]
    | hobject, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              parentType selection :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_head hvalid
        have htail :
            Validation.selectionSetValidInPossibleTypes schema variableDefinitions
              parentType rest :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_tail hvalid
        simp [selectionSetValidInCurrentScope]
        exact ⟨
          selectionValidInCurrentScope_of_validInPossibleTypes
            schema variableDefinitions hschema parentType hobject selection hhead,
          selectionSetValidInCurrentScope_of_validInPossibleTypes
            schema variableDefinitions hschema parentType hobject rest htail⟩
end

private theorem selection_size_pos_for_currentScopeValidity (selection : Selection)
    : 0 < selection.size := by
  cases selection <;> simp [Selection.size] <;> omega

private theorem selectionSet_size_tail_lt_cons_for_currentScopeValidity
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]
  exact Nat.lt_add_of_pos_left
    (selection_size_pos_for_currentScopeValidity selection)

private theorem selectionSet_size_child_lt_cons_field_for_currentScopeValidity
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.field responseName fieldName arguments directives selectionSet
            :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_child_lt_cons_inline_for_currentScopeValidity
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.inlineFragment typeCondition directives selectionSet :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_append_for_filterValidity (left right : List Selection)
    : SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

private theorem mergeSelectionSets_append_for_filterValidity (left right : List Selection)
    : mergeSelectionSets (left ++ right)
      = mergeSelectionSets left ++ mergeSelectionSets right := by
  induction left with
  | nil =>
      simp [mergeSelectionSets]
  | cons selection rest ih =>
      simp [mergeSelectionSets, ih, List.append_assoc]

private theorem size_withoutFieldSelectionsWithResponseName_le_for_filterValidity
    (schema : Schema) (responseName : Name)
    : ∀ selectionSet,
        SelectionSet.size
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [withoutFieldSelectionsWithResponseName, SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_withoutFieldSelectionsWithResponseName_le_for_filterValidity
              schema responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, h, SelectionSet.size,
              Selection.size]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse, SelectionSet.size,
              Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_withoutFieldSelectionsWithResponseName_le_for_filterValidity
              schema responseName selectionSet
          have hrest :=
            size_withoutFieldSelectionsWithResponseName_le_for_filterValidity
              schema responseName rest
          cases typeCondition <;>
            simp [withoutFieldSelectionsWithResponseName, SelectionSet.size,
              Selection.size]
          all_goals omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem
    size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_filterValidity
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet,
        SelectionSet.size
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet))
        ≤ SelectionSet.size selectionSet
  | [] => by
      simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets,
        SelectionSet.size]
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrest :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_filterValidity
              schema parentType responseName rest
          by_cases h : (fieldResponseName == responseName) = true
          · simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets, h,
              selectionSet_size_append_for_filterValidity,
              SelectionSet.size, Selection.size, Selection.subselections]
            omega
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse, SelectionSet.size,
              Selection.size]
            omega
      | inlineFragment typeCondition directives selectionSet =>
          have hselectionSet :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_filterValidity
              schema parentType responseName selectionSet
          have hrest :=
            size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_filterValidity
              schema parentType responseName rest
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope,
                mergeSelectionSets_append_for_filterValidity,
                selectionSet_size_append_for_filterValidity,
                SelectionSet.size, Selection.size]
              omega
          | some typeCondition =>
              by_cases h :
                  schema.typesOverlapBool parentType typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, h,
                  mergeSelectionSets_append_for_filterValidity,
                  selectionSet_size_append_for_filterValidity,
                  SelectionSet.size, Selection.size]
                omega
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch : schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse,
                  SelectionSet.size, Selection.size]
                omega
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem selectionSetValidInCurrentScope_head
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection} {rest : List Selection}
    : selectionSetValidInCurrentScope schema variableDefinitions parentType
        (selection :: rest)
      -> selectionValidInCurrentScope schema variableDefinitions parentType
          selection := by
  intro hvalid
  simpa [selectionSetValidInCurrentScope] using hvalid.1

theorem selectionSetValidInCurrentScope_tail
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection} {rest : List Selection}
    : selectionSetValidInCurrentScope schema variableDefinitions parentType
        (selection :: rest)
      -> selectionSetValidInCurrentScope schema variableDefinitions parentType rest := by
  intro hvalid
  simpa [selectionSetValidInCurrentScope] using hvalid.2

theorem selectionSetValidInCurrentScope_append
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : selectionSetValidInCurrentScope schema variableDefinitions parentType left
      -> selectionSetValidInCurrentScope schema variableDefinitions parentType right
      -> selectionSetValidInCurrentScope schema variableDefinitions parentType
          (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa [selectionSetValidInCurrentScope] using hright
  | cons selection rest ih =>
      have hhead :
          selectionValidInCurrentScope schema variableDefinitions parentType
            selection :=
        selectionSetValidInCurrentScope_head hleft
      have htail :
          selectionSetValidInCurrentScope schema variableDefinitions parentType
            rest :=
        selectionSetValidInCurrentScope_tail hleft
      simp [selectionSetValidInCurrentScope]
      exact ⟨hhead, ih htail⟩

theorem selectionSetValidInCurrentScope_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName parentType : Name)
    (variableDefinitions : List VariableDefinition)
    : ∀ selectionSet,
        selectionSetValidInCurrentScope schema variableDefinitions parentType selectionSet
        -> selectionSetValidInCurrentScope schema variableDefinitions parentType
            (withoutFieldSelectionsWithResponseName schema responseName
              selectionSet) := by
  have hmain :
      ∀ n selectionSet parentType,
        SelectionSet.size selectionSet = n ->
        selectionSetValidInCurrentScope schema variableDefinitions parentType
          selectionSet ->
        selectionSetValidInCurrentScope schema variableDefinitions parentType
          (withoutFieldSelectionsWithResponseName schema responseName
            selectionSet) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro selectionSet parentType hsize hvalid
        cases selectionSet with
        | nil =>
            simp [withoutFieldSelectionsWithResponseName,
              selectionSetValidInCurrentScope]
        | cons selection rest =>
            have hhead :
                selectionValidInCurrentScope schema variableDefinitions
                  parentType selection :=
              selectionSetValidInCurrentScope_head hvalid
            have htail :
                selectionSetValidInCurrentScope schema variableDefinitions
                  parentType rest :=
              selectionSetValidInCurrentScope_tail hvalid
            have hrestSize :
                SelectionSet.size rest < n := by
              rw [← hsize]
              exact
                selectionSet_size_tail_lt_cons_for_currentScopeValidity
                  selection rest
            cases selection with
            | field fieldResponseName fieldName arguments directives selectionSet =>
                by_cases hresponse : (fieldResponseName == responseName) = true
                · simp [withoutFieldSelectionsWithResponseName, hresponse]
                  exact ih (SelectionSet.size rest) hrestSize rest parentType
                    rfl htail
                · have hfalse : (fieldResponseName == responseName) = false := by
                    cases hmatch : fieldResponseName == responseName
                    · rfl
                    · contradiction
                  simp [withoutFieldSelectionsWithResponseName, hfalse,
                    selectionSetValidInCurrentScope]
                  exact ⟨hhead,
                    ih (SelectionSet.size rest) hrestSize rest parentType
                      rfl htail⟩
            | inlineFragment typeCondition directives selectionSet =>
                have hchildSize :
                    SelectionSet.size selectionSet < n := by
                  rw [← hsize]
                  exact
                    selectionSet_size_child_lt_cons_inline_for_currentScopeValidity
                      typeCondition directives selectionSet rest
                simp [withoutFieldSelectionsWithResponseName,
                  selectionSetValidInCurrentScope]
                constructor
                · cases typeCondition with
                  | none =>
                      simpa [selectionValidInCurrentScope]
                        using ih (SelectionSet.size selectionSet) hchildSize
                          selectionSet parentType rfl hhead
                  | some typeCondition =>
                      simpa [selectionValidInCurrentScope]
                        using (fun hoverlap =>
                                ih (SelectionSet.size selectionSet) hchildSize
                                  selectionSet parentType rfl (hhead hoverlap))
                · exact ih (SelectionSet.size rest) hrestSize rest parentType
                    rfl htail
  intro selectionSet hvalid
  exact hmain (SelectionSet.size selectionSet) selectionSet parentType rfl hvalid

theorem selectionValid_field_clear_directives
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    : Validation.selectionValid schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments directives selectionSet)
      -> Validation.selectionValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] selectionSet) := by
  intro hvalid
  rcases Validation.selectionValid_field_lookup hvalid with
    ⟨fieldDefinition, hlookup, harguments, hchildren⟩
  simp [Validation.selectionValid,
    directivesValid_nil schema variableDefinitions, hlookup]
  exact ⟨harguments, hchildren⟩

theorem selectionValidInPossibleTypes_field_clear_directives
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    : Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType
        (Selection.field responseName fieldName arguments directives selectionSet)
      -> Validation.selectionValidInPossibleTypes schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments [] selectionSet) := by
  intro hvalid
  have hsource :
      Validation.selectionValid schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    simpa [Validation.selectionValidInPossibleTypes] using hvalid.1
  rcases Validation.selectionValid_field_lookup hsource with
    ⟨fieldDefinition, hlookup, _harguments, _hchildren⟩
  have hcleared :
      Validation.selectionValid schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments [] selectionSet) :=
    selectionValid_field_clear_directives hsource
  simp [Validation.selectionValidInPossibleTypes, hlookup]
  exact ⟨
    hcleared,
    by simpa [Validation.selectionValidInPossibleTypes, hlookup] using hvalid.2
  ⟩

/-
Proof-internal source-validity witness for boolean-filtered syntax at one
concrete normalizer scope. A filtered branch can be less than spec-valid as raw
syntax: Boolean filtering can leave empty children below an infeasible
type-condition stack. For the fields that do survive in the current object
scope, this predicate records the original valid field selection with the same
response name, field name, and arguments; typed inline fragments recurse only
when they can apply to the current object scope.
-/
mutual
  def selectionFilteredCurrentSourceValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : Selection -> Prop
    | .field responseName fieldName arguments directives selectionSet =>
        directives = []
        ∧ ∃ sourceDirectives sourceSelectionSet fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            ∧ Validation.selectionValidInPossibleTypes schema
                variableDefinitions parentType
                (Selection.field responseName fieldName arguments
                  sourceDirectives sourceSelectionSet)
            ∧ ∀ objectType,
                objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
                -> selectionSetFilteredCurrentSourceValid schema
                    variableDefinitions objectType selectionSet
    | .inlineFragment none directives selectionSet =>
        directives = []
        ∧ selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        directives = []
        ∧ (schema.typesOverlapBool parentType typeCondition = true
            -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
                parentType selectionSet)

  def selectionSetFilteredCurrentSourceValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionFilteredCurrentSourceValid schema variableDefinitions
          parentType selection
        ∧ selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rest
end

attribute [local simp] selectionSetFilteredCurrentSourceValid

theorem selectionSetFilteredCurrentSourceValid_head
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection} {rest : List Selection}
    : selectionSetFilteredCurrentSourceValid schema variableDefinitions
        parentType (selection :: rest)
      -> selectionFilteredCurrentSourceValid schema variableDefinitions
          parentType selection := by
  intro hvalid
  simpa [selectionSetFilteredCurrentSourceValid] using hvalid.1

theorem selectionSetFilteredCurrentSourceValid_tail
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection} {rest : List Selection}
    : selectionSetFilteredCurrentSourceValid schema variableDefinitions
        parentType (selection :: rest)
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType rest := by
  intro hvalid
  simpa [selectionSetFilteredCurrentSourceValid] using hvalid.2

theorem selectionSetFilteredCurrentSourceValid_append
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : selectionSetFilteredCurrentSourceValid schema variableDefinitions parentType left
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType right
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa [selectionSetFilteredCurrentSourceValid] using hright
  | cons selection rest ih =>
      have hhead :
          selectionFilteredCurrentSourceValid schema variableDefinitions
            parentType selection :=
        selectionSetFilteredCurrentSourceValid_head hleft
      have htail :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rest :=
        selectionSetFilteredCurrentSourceValid_tail hleft
      simp [selectionSetFilteredCurrentSourceValid]
      exact ⟨hhead, ih htail⟩

mutual
  theorem selectionFilteredCurrentSourceValid_filterSelectionSetBoolCase
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boolCase : BoolCase)
      : ∀ parentType,
          schema.objectType parentType
          -> ∀ selection,
              Validation.selectionValidInPossibleTypes schema
                variableDefinitions parentType selection
              -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
                  parentType (filterSelectionSetBoolCase boolCase [selection])
    | parentType, hobject,
      .field responseName fieldName arguments directives selectionSet,
      hvalid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hsource :
              Validation.selectionValid schema variableDefinitions parentType
                (Selection.field responseName fieldName arguments directives
                  selectionSet) := by
            simpa [Validation.selectionValidInPossibleTypes] using hvalid.1
          rcases Validation.selectionValid_field_lookup hsource with
            ⟨fieldDefinition, hlookup, _harguments, _hchildren⟩
          have hchildren :
              ∀ objectType,
                objectType ∈
                    schema.getPossibleTypes fieldDefinition.outputType.namedType ->
                  Validation.selectionSetValidInPossibleTypes schema
                    variableDefinitions objectType selectionSet := by
            simpa [Validation.selectionValidInPossibleTypes, hlookup]
              using hvalid.2
          have hfilteredChildren :
              ∀ objectType,
                objectType ∈
                    schema.getPossibleTypes fieldDefinition.outputType.namedType ->
                  selectionSetFilteredCurrentSourceValid schema
                    variableDefinitions objectType
                    (filterSelectionSetBoolCase boolCase selectionSet) := by
            intro objectType hpossible
            have hchildObject :
                schema.objectType objectType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema fieldDefinition.outputType.namedType objectType
                hpossible
            exact
              selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
                schema variableDefinitions hschema boolCase objectType
                hchildObject selectionSet (hchildren objectType hpossible)
          cases selectionSet with
          | nil =>
              have hfield :
                  selectionFilteredCurrentSourceValid schema variableDefinitions
                    parentType
                    (Selection.field responseName fieldName arguments [] []) := by
                change [] = [] ∧
                  ∃ sourceDirectives sourceSelectionSet fieldDefinition',
                    schema.lookupField parentType fieldName =
                        some fieldDefinition'
                      ∧ Validation.selectionValidInPossibleTypes schema
                        variableDefinitions parentType
                        (Selection.field responseName fieldName arguments
                          sourceDirectives sourceSelectionSet)
                      ∧ ∀ objectType,
                        objectType ∈
                            schema.getPossibleTypes
                              fieldDefinition'.outputType.namedType ->
                          selectionSetFilteredCurrentSourceValid schema
                            variableDefinitions objectType []
                exact ⟨rfl, directives, [], fieldDefinition, hlookup,
                  hvalid, by
                  intro objectType hpossible
                  have hempty :
                      filterSelectionSetBoolCase boolCase [] = [] := by
                    simp [filterSelectionSetBoolCase]
                  rw [← hempty]
                  exact hfilteredChildren objectType hpossible⟩
              simp [filterSelectionSetBoolCase, hallow,
                selectionSetFilteredCurrentSourceValid]
              exact hfield
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  have hfield :
                      selectionFilteredCurrentSourceValid schema
                        variableDefinitions parentType
                        (Selection.field responseName fieldName arguments []
                          []) := by
                    change [] = [] ∧
                      ∃ sourceDirectives sourceSelectionSet fieldDefinition',
                        schema.lookupField parentType fieldName =
                            some fieldDefinition'
                          ∧ Validation.selectionValidInPossibleTypes schema
                            variableDefinitions parentType
                            (Selection.field responseName fieldName arguments
                              sourceDirectives sourceSelectionSet)
                          ∧ ∀ objectType,
                            objectType ∈
                                schema.getPossibleTypes
                                  fieldDefinition'.outputType.namedType ->
                              selectionSetFilteredCurrentSourceValid schema
                                variableDefinitions objectType []
                    exact ⟨rfl, directives, child :: children,
                      fieldDefinition, hlookup, hvalid, by
                      intro objectType hpossible
                      rw [← hchild]
                      exact hfilteredChildren objectType hpossible⟩
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    selectionSetFilteredCurrentSourceValid]
                  exact hfield
              | cons filteredChild filteredChildren =>
                  have hfield :
                      selectionFilteredCurrentSourceValid schema
                        variableDefinitions parentType
                        (Selection.field responseName fieldName arguments []
                          (filteredChild :: filteredChildren)) := by
                    change [] = [] ∧
                      ∃ sourceDirectives sourceSelectionSet fieldDefinition',
                        schema.lookupField parentType fieldName =
                            some fieldDefinition'
                          ∧ Validation.selectionValidInPossibleTypes schema
                            variableDefinitions parentType
                            (Selection.field responseName fieldName arguments
                              sourceDirectives sourceSelectionSet)
                          ∧ ∀ objectType,
                            objectType ∈
                                schema.getPossibleTypes
                                  fieldDefinition'.outputType.namedType ->
                              selectionSetFilteredCurrentSourceValid schema
                                variableDefinitions objectType
                                (filteredChild :: filteredChildren)
                    exact ⟨rfl, directives, child :: children,
                      fieldDefinition, hlookup, hvalid, by
                      intro objectType hpossible
                      simpa [hchild, selectionSetFilteredCurrentSourceValid] using
                        hfilteredChildren objectType hpossible⟩
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    selectionSetFilteredCurrentSourceValid]
                  exact hfield
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredCurrentSourceValid]
    | parentType, hobject,
      .inlineFragment none directives selectionSet, hvalid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hsourceChildren :
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType selectionSet := by
            have hparentPossible :
                parentType ∈ schema.getPossibleTypes parentType :=
              List.contains_iff_mem.mp
                (object_typeIncludesObjectBool_self schema hobject)
            simpa [Validation.selectionValidInPossibleTypes] using
              hvalid parentType hparentPossible
          have hfilteredChildren :
              selectionSetFilteredCurrentSourceValid schema
                variableDefinitions parentType
                (filterSelectionSetBoolCase boolCase selectionSet) :=
            selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType hobject
              selectionSet hsourceChildren
          cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCurrentSourceValid]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCurrentSourceValid,
                selectionFilteredCurrentSourceValid]
              simpa [hchild, selectionSetFilteredCurrentSourceValid]
                using hfilteredChildren
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredCurrentSourceValid]
    | parentType, hobject,
      .inlineFragment (some typeCondition) directives selectionSet, hvalid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCurrentSourceValid]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCurrentSourceValid,
                selectionFilteredCurrentSourceValid]
              intro hoverlap
              have hparentPossible :
                  parentType ∈ schema.getPossibleTypes typeCondition :=
                List.contains_iff_mem.mp
                  (typeIncludesObjectBool_of_object_typesOverlapBool schema
                    hobject hoverlap)
              have hsourceChildren :
                  Validation.selectionSetValidInPossibleTypes schema
                    variableDefinitions parentType selectionSet := by
                simpa [Validation.selectionValidInPossibleTypes, hoverlap]
                  using hvalid hoverlap parentType hparentPossible
              simpa [hchild] using
                selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
                  schema variableDefinitions hschema boolCase parentType hobject
                  selectionSet hsourceChildren
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredCurrentSourceValid]

  theorem selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boolCase : BoolCase)
      : ∀ parentType,
          schema.objectType parentType
          -> ∀ selectionSet,
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType selectionSet
              -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
                  parentType (filterSelectionSetBoolCase boolCase selectionSet)
    | _parentType, _hobject, [], _hvalid => by
        simp [filterSelectionSetBoolCase,
          selectionSetFilteredCurrentSourceValid]
    | parentType, hobject, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              parentType selection :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_head
            hvalid
        have htail :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions parentType rest :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_tail
            hvalid
        rw [filterSelectionSetBoolCase_cons]
        apply selectionSetFilteredCurrentSourceValid_append
        · exact
            selectionFilteredCurrentSourceValid_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType hobject
              selection hhead
        · exact
            selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType hobject
              rest htail
end

theorem selectionSetFilteredCurrentSourceValid_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName parentType : Name)
    (variableDefinitions : List VariableDefinition)
    : ∀ selectionSet,
        selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType selectionSet
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType
            (withoutFieldSelectionsWithResponseName schema responseName
              selectionSet) := by
  have hmain :
      ∀ n selectionSet parentType,
        SelectionSet.size selectionSet = n ->
        selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType selectionSet ->
        selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType
          (withoutFieldSelectionsWithResponseName schema responseName
            selectionSet) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro selectionSet parentType hsize hvalid
        cases selectionSet with
        | nil =>
            simp [withoutFieldSelectionsWithResponseName,
              selectionSetFilteredCurrentSourceValid]
        | cons selection rest =>
            have hhead :
                selectionFilteredCurrentSourceValid schema variableDefinitions
                  parentType selection :=
              selectionSetFilteredCurrentSourceValid_head hvalid
            have htail :
                selectionSetFilteredCurrentSourceValid schema variableDefinitions
                  parentType rest :=
              selectionSetFilteredCurrentSourceValid_tail hvalid
            have hrestSize :
                SelectionSet.size rest < n := by
              rw [← hsize]
              exact
                selectionSet_size_tail_lt_cons_for_currentScopeValidity
                  selection rest
            cases selection with
            | field fieldResponseName fieldName arguments directives selectionSet =>
                by_cases hresponse : (fieldResponseName == responseName) = true
                · simp [withoutFieldSelectionsWithResponseName, hresponse]
                  exact ih (SelectionSet.size rest) hrestSize rest parentType
                    rfl htail
                · have hfalse :
                      (fieldResponseName == responseName) = false := by
                    cases hmatch : fieldResponseName == responseName
                    · rfl
                    · contradiction
                  simp [withoutFieldSelectionsWithResponseName, hfalse,
                    selectionSetFilteredCurrentSourceValid]
                  exact ⟨hhead,
                    ih (SelectionSet.size rest) hrestSize rest parentType
                      rfl htail⟩
            | inlineFragment typeCondition directives selectionSet =>
                have hchildSize :
                    SelectionSet.size selectionSet < n := by
                  rw [← hsize]
                  exact
                    selectionSet_size_child_lt_cons_inline_for_currentScopeValidity
                      typeCondition directives selectionSet rest
                cases typeCondition with
                | none =>
                    have hparts :
                        directives = [] ∧
                          selectionSetFilteredCurrentSourceValid schema
                            variableDefinitions parentType selectionSet := by
                      simpa [selectionFilteredCurrentSourceValid] using hhead
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetFilteredCurrentSourceValid,
                      selectionFilteredCurrentSourceValid]
                    exact ⟨⟨hparts.1,
                      ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType rfl hparts.2⟩,
                      ih (SelectionSet.size rest) hrestSize rest parentType
                        rfl htail⟩
                | some typeCondition =>
                    have hparts :
                        directives = [] ∧
                          (schema.typesOverlapBool parentType typeCondition =
                            true ->
                            selectionSetFilteredCurrentSourceValid schema
                              variableDefinitions parentType selectionSet) := by
                      simpa [selectionFilteredCurrentSourceValid] using hhead
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetFilteredCurrentSourceValid,
                      selectionFilteredCurrentSourceValid]
                    exact ⟨
                      ⟨
                        hparts.1,
                        by
                          intro hoverlap
                          exact ih (SelectionSet.size selectionSet) hchildSize
                            selectionSet parentType rfl (hparts.2 hoverlap)
                      ⟩,
                      ih (SelectionSet.size rest) hrestSize rest parentType rfl htail
                    ⟩
  intro selectionSet hvalid
  exact hmain (SelectionSet.size selectionSet) selectionSet parentType rfl
    hvalid

theorem selectionSetFilteredCurrentSourceValid_mergeSelectionSets_of_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition} {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
              parentType selection.subselections)
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, selectionSetFilteredCurrentSourceValid]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetFilteredCurrentSourceValid_append
      · exact hvalid selection (by simp)
      · exact
          selectionSetFilteredCurrentSourceValid_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetFilteredCurrentSourceValid_mergeSelectionSets_of_field_subselections
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
            -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
                parentType subselections)
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetFilteredCurrentSourceValid_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections]
    using hfields fieldName arguments directives subselections hselection

theorem
    selectionSetFilteredCurrentSourceValid_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName childType : Name} (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            childType subselections)
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          childType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType
              responseName selectionSet)) := by
  intro hfields
  apply selectionSetFilteredCurrentSourceValid_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
      responseName selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType selectionSet
        -> ∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ fieldSelectionsWithResponseNameInScope schema parentType
                  responseName selectionSet
            -> selectionFilteredCurrentSourceValid schema variableDefinitions
                parentType
                (Selection.field responseName fieldName arguments directives
                  subselections)
  | [], _hvalid, _fieldName, _arguments, _directives, _subselections,
    hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, hvalid, fieldName, arguments, directives,
    subselections, hfield => by
      have hhead :
          selectionFilteredCurrentSourceValid schema variableDefinitions
            parentType selection :=
        selectionSetFilteredCurrentSourceValid_head hvalid
      have htail :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rest :=
        selectionSetFilteredCurrentSourceValid_tail hvalid
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hmatched | hrest
            · rcases hmatched with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              exact hhead
            · exact
                fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
                  schema variableDefinitions parentType responseName rest htail
                  fieldName arguments directives subselections hrest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
                schema variableDefinitions parentType responseName rest htail
                fieldName arguments directives subselections hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbody :
                  selectionSetFilteredCurrentSourceValid schema
                    variableDefinitions parentType selectionSet := by
                simpa [selectionFilteredCurrentSourceValid] using hhead.2
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbodyField | hrest
              · exact
                  fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
                    schema variableDefinitions parentType responseName
                    selectionSet hbody fieldName arguments directives
                    subselections hbodyField
              · exact
                  fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
                    schema variableDefinitions parentType responseName rest htail
                    fieldName arguments directives subselections hrest
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hbody :
                    selectionSetFilteredCurrentSourceValid schema
                      variableDefinitions parentType selectionSet := by
                  simpa [selectionFilteredCurrentSourceValid] using
                    hhead.2 hoverlap
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbodyField | hrest
                · exact
                    fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
                      schema variableDefinitions parentType responseName
                      selectionSet hbody fieldName arguments directives
                      subselections hbodyField
                · exact
                    fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
                      schema variableDefinitions parentType responseName rest htail
                      fieldName arguments directives subselections hrest
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
                    schema variableDefinitions parentType responseName rest htail
                    fieldName arguments directives subselections hfield

theorem
    fieldSelectionsWithResponseNameInScope_matching_subselections_filteredCurrentSourceValid_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name) (arguments : List Argument)
    (subselections rest : List Selection) (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
              runtimeType matchedSubselections := by
  intro hobject hlookupValid hcurrent hmerge hlookup hpossible
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailCurrent :
      selectionSetFilteredCurrentSourceValid schema variableDefinitions
        parentType rest :=
    selectionSetFilteredCurrentSourceValid_tail hcurrent
  have hmatchedCurrent :
      selectionFilteredCurrentSourceValid schema variableDefinitions parentType
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections) :=
    fieldSelectionsWithResponseNameInScope_field_filteredCurrentSourceValid
      schema variableDefinitions parentType responseName rest htailCurrent
      matchedFieldName matchedArguments matchedDirectives matchedSubselections
      hmatched
  have hsame :
      matchedFieldName = fieldName :=
    runtimeMergeSource_matching_same_field
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  have hparts :
      matchedDirectives = []
        ∧ ∃ sourceDirectives sourceSelectionSet fieldDefinition',
          schema.lookupField parentType fieldName = some fieldDefinition'
            ∧ Validation.selectionValidInPossibleTypes schema
              variableDefinitions parentType
              (Selection.field responseName fieldName matchedArguments
                sourceDirectives sourceSelectionSet)
            ∧ ∀ objectType,
              objectType ∈
                  schema.getPossibleTypes fieldDefinition'.outputType.namedType ->
                selectionSetFilteredCurrentSourceValid schema variableDefinitions
                  objectType matchedSubselections := by
    simpa [selectionFilteredCurrentSourceValid] using hmatchedCurrent
  rcases hparts with
    ⟨_hdirectives, sourceDirectives, sourceSelectionSet, matchedDefinition,
      hmatchedLookup, _hsourceValid, hchildren⟩
  have hdefinitionEq : matchedDefinition = fieldDefinition := by
    rw [hlookup] at hmatchedLookup
    cases hmatchedLookup
    rfl
  subst matchedDefinition
  exact hchildren runtimeType hpossible

theorem selectionSetFilteredCurrentSourceValid_fieldHead_merged_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          runtimeType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType
                  responseName rest)) := by
  intro hobject hlookupValid hcurrent hmerge hlookup hpossible
  apply selectionSetFilteredCurrentSourceValid_append
  · have hhead :
        selectionFilteredCurrentSourceValid schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments []
            subselections) :=
      selectionSetFilteredCurrentSourceValid_head hcurrent
    have hparts :
        ([] : List DirectiveApplication) = []
          ∧ ∃ sourceDirectives sourceSelectionSet fieldDefinition',
            schema.lookupField parentType fieldName = some fieldDefinition'
              ∧ Validation.selectionValidInPossibleTypes schema
                variableDefinitions parentType
                (Selection.field responseName fieldName arguments
                  sourceDirectives sourceSelectionSet)
              ∧ ∀ objectType,
                objectType ∈
                    schema.getPossibleTypes fieldDefinition'.outputType.namedType ->
                  selectionSetFilteredCurrentSourceValid schema
                    variableDefinitions objectType subselections := by
      simpa [selectionFilteredCurrentSourceValid] using hhead
    rcases hparts with
      ⟨_hdirectives, sourceDirectives, sourceSelectionSet,
        headDefinition, hheadLookup, _hsource, hchildren⟩
    have hdefinitionEq : headDefinition = fieldDefinition := by
      rw [hlookup] at hheadLookup
      cases hheadLookup
      rfl
    subst headDefinition
    exact hchildren runtimeType hpossible
  · apply
      selectionSetFilteredCurrentSourceValid_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_filteredCurrentSourceValid_of_child_object
        schema variableDefinitions parentType responseName fieldName
        runtimeType arguments subselections rest fieldDefinition hobject
        hlookupValid hcurrent hmerge hlookup hpossible matchedFieldName
        matchedArguments matchedDirectives matchedSubselections hmatched

mutual
  def selectionFilteredReturnLookupValid (schema : Schema) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∀ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          -> selectionSetLookupValid schema
                fieldDefinition.outputType.namedType selectionSet
              ∧ ∀ objectType,
                  objectType
                    ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
                  -> selectionSetFilteredReturnLookupValid schema objectType selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetFilteredReturnLookupValid schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typesOverlapBool parentType typeCondition = true
        -> selectionSetFilteredReturnLookupValid schema parentType selectionSet

  def selectionSetFilteredReturnLookupValid (schema : Schema) (parentType : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionFilteredReturnLookupValid schema parentType selection
        ∧ selectionSetFilteredReturnLookupValid schema parentType rest
end

attribute [local simp] selectionSetFilteredReturnLookupValid

theorem selectionSetFilteredReturnLookupValid_head
    {schema : Schema} {parentType : Name}
    {selection : Selection} {rest : List Selection}
    : selectionSetFilteredReturnLookupValid schema parentType (selection :: rest)
      -> selectionFilteredReturnLookupValid schema parentType selection := by
  intro hvalid
  simpa [selectionSetFilteredReturnLookupValid] using hvalid.1

theorem selectionSetFilteredReturnLookupValid_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {rest : List Selection}
    : selectionSetFilteredReturnLookupValid schema parentType (selection :: rest)
      -> selectionSetFilteredReturnLookupValid schema parentType rest := by
  intro hvalid
  simpa [selectionSetFilteredReturnLookupValid] using hvalid.2

theorem selectionSetFilteredReturnLookupValid_append
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : selectionSetFilteredReturnLookupValid schema parentType left
      -> selectionSetFilteredReturnLookupValid schema parentType right
      -> selectionSetFilteredReturnLookupValid schema parentType (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa [selectionSetFilteredReturnLookupValid] using hright
  | cons selection rest ih =>
      have hhead :
          selectionFilteredReturnLookupValid schema parentType selection :=
        selectionSetFilteredReturnLookupValid_head hleft
      have htail :
          selectionSetFilteredReturnLookupValid schema parentType rest :=
        selectionSetFilteredReturnLookupValid_tail hleft
      simp [selectionSetFilteredReturnLookupValid]
      exact ⟨hhead, ih htail⟩

theorem selectionSetFilteredReturnLookupValid_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName parentType : Name)
    : ∀ selectionSet,
        selectionSetFilteredReturnLookupValid schema parentType selectionSet
        -> selectionSetFilteredReturnLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName
              selectionSet) := by
  have hmain :
      ∀ n selectionSet parentType,
        SelectionSet.size selectionSet = n ->
        selectionSetFilteredReturnLookupValid schema parentType selectionSet ->
        selectionSetFilteredReturnLookupValid schema parentType
          (withoutFieldSelectionsWithResponseName schema responseName
            selectionSet) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro selectionSet parentType hsize hvalid
        cases selectionSet with
        | nil =>
            simp [withoutFieldSelectionsWithResponseName,
              selectionSetFilteredReturnLookupValid]
        | cons selection rest =>
            have hhead :
                selectionFilteredReturnLookupValid schema parentType
                  selection :=
              selectionSetFilteredReturnLookupValid_head hvalid
            have htail :
                selectionSetFilteredReturnLookupValid schema parentType
                  rest :=
              selectionSetFilteredReturnLookupValid_tail hvalid
            have hrestSize :
                SelectionSet.size rest < n := by
              rw [← hsize]
              exact
                selectionSet_size_tail_lt_cons_for_currentScopeValidity
                  selection rest
            cases selection with
            | field fieldResponseName fieldName arguments directives selectionSet =>
                by_cases hresponse : (fieldResponseName == responseName) = true
                · simp [withoutFieldSelectionsWithResponseName, hresponse]
                  exact ih (SelectionSet.size rest) hrestSize rest parentType
                    rfl htail
                · have hfalse :
                      (fieldResponseName == responseName) = false := by
                    cases hmatch : fieldResponseName == responseName
                    · rfl
                    · contradiction
                  simp [withoutFieldSelectionsWithResponseName, hfalse,
                    selectionSetFilteredReturnLookupValid]
                  exact ⟨hhead,
                    ih (SelectionSet.size rest) hrestSize rest parentType
                      rfl htail⟩
            | inlineFragment typeCondition directives selectionSet =>
                have hchildSize :
                    SelectionSet.size selectionSet < n := by
                  rw [← hsize]
                  exact
                    selectionSet_size_child_lt_cons_inline_for_currentScopeValidity
                      typeCondition directives selectionSet rest
                cases typeCondition with
                | none =>
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetFilteredReturnLookupValid,
                      selectionFilteredReturnLookupValid]
                    exact ⟨
                      ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType rfl hhead,
                      ih (SelectionSet.size rest) hrestSize rest parentType
                        rfl htail⟩
                | some typeCondition =>
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetFilteredReturnLookupValid,
                      selectionFilteredReturnLookupValid]
                    exact ⟨
                      (by
                        intro hoverlap
                        exact ih (SelectionSet.size selectionSet) hchildSize
                          selectionSet parentType rfl (hhead hoverlap)),
                      ih (SelectionSet.size rest) hrestSize rest parentType rfl htail
                    ⟩
  intro selectionSet hvalid
  exact hmain (SelectionSet.size selectionSet) selectionSet parentType rfl
    hvalid

theorem selectionSetFilteredReturnLookupValid_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetFilteredReturnLookupValid schema parentType
              selection.subselections)
        -> selectionSetFilteredReturnLookupValid schema parentType
            (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, selectionSetFilteredReturnLookupValid]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetFilteredReturnLookupValid_append
      · exact hvalid selection (by simp)
      · exact
          selectionSetFilteredReturnLookupValid_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate]))

theorem
    selectionSetFilteredReturnLookupValid_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {parentType responseName childType : Name}
    (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> selectionSetFilteredReturnLookupValid schema childType subselections)
      -> selectionSetFilteredReturnLookupValid schema childType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType
              responseName selectionSet)) := by
  intro hfields
  apply selectionSetFilteredReturnLookupValid_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases fieldSelectionsWithResponseNameInScope_mem_field schema parentType
      responseName selectionSet selection hselection with
    ⟨fieldName, arguments, directives, subselections, hshape⟩
  subst selection
  simpa [Selection.subselections]
    using hfields fieldName arguments directives subselections hselection

theorem fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
    (schema : Schema) (parentType responseName : Name)
    : schema.objectType parentType
      -> ∀ selectionSet,
          selectionSetFilteredReturnLookupValid schema parentType selectionSet
          -> ∀ fieldName arguments directives subselections,
              Selection.field responseName fieldName arguments directives subselections
                ∈ fieldSelectionsWithResponseNameInScope schema parentType
                    responseName selectionSet
              -> selectionFilteredReturnLookupValid schema parentType
                  (Selection.field responseName fieldName arguments directives
                    subselections)
  | _hobject, [], _hvalid, _fieldName, _arguments, _directives,
    _subselections, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | hobject, selection :: rest, hvalid, fieldName, arguments, directives,
    subselections, hfield => by
      have hhead :
          selectionFilteredReturnLookupValid schema parentType selection :=
        selectionSetFilteredReturnLookupValid_head hvalid
      have htail :
          selectionSetFilteredReturnLookupValid schema parentType rest :=
        selectionSetFilteredReturnLookupValid_tail hvalid
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hmatched | hrest
            · rcases hmatched with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              exact hhead
            · exact
                fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
                  schema parentType responseName hobject rest htail
                  fieldName arguments directives subselections hrest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
                schema parentType responseName hobject rest htail
                fieldName arguments directives subselections hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbody :
                  selectionSetFilteredReturnLookupValid schema parentType
                    selectionSet := by
                simpa [selectionFilteredReturnLookupValid] using hhead
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbodyField | hrest
              · exact
                  fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
                    schema parentType responseName hobject selectionSet
                    hbody fieldName arguments directives subselections
                    hbodyField
              · exact
                  fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
                    schema parentType responseName hobject rest htail
                    fieldName arguments directives subselections hrest
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hbody :
                    selectionSetFilteredReturnLookupValid schema parentType
                      selectionSet := by
                  simpa [selectionFilteredReturnLookupValid] using
                    hhead hoverlap
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbodyField | hrest
                · exact
                    fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
                      schema parentType responseName hobject selectionSet
                      hbody fieldName arguments directives subselections
                      hbodyField
                · exact
                    fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
                      schema parentType responseName hobject rest htail
                      fieldName arguments directives subselections hrest
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
                    schema parentType responseName hobject rest htail
                    fieldName arguments directives subselections hfield

theorem
    fieldSelectionsWithResponseNameInScope_matching_subselections_filteredReturnLookupValid_of_child_object
    (schema : Schema) (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetFilteredReturnLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetFilteredReturnLookupValid schema runtimeType
              matchedSubselections := by
  intro hobject hlookupValid hreturnLookup hmerge hlookup hpossible
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailLookup :
      selectionSetFilteredReturnLookupValid schema parentType rest :=
    selectionSetFilteredReturnLookupValid_tail hreturnLookup
  have hmatchedLookup :
      selectionFilteredReturnLookupValid schema parentType
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections) :=
    fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
      schema parentType responseName hobject rest htailLookup
      matchedFieldName matchedArguments matchedDirectives matchedSubselections
      hmatched
  have hsame :
      matchedFieldName = fieldName :=
    runtimeMergeSource_matching_same_field
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  exact (hmatchedLookup fieldDefinition hlookup).2 runtimeType hpossible

theorem selectionSetFilteredReturnLookupValid_fieldHead_merged_of_child_object
    (schema : Schema)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetFilteredReturnLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> selectionSetFilteredReturnLookupValid schema runtimeType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType
                  responseName rest)) := by
  intro hobject hlookupValid hreturnLookup hmerge hlookup hpossible
  apply selectionSetFilteredReturnLookupValid_append
  · have hhead :
        selectionFilteredReturnLookupValid schema parentType
          (Selection.field responseName fieldName arguments []
            subselections) :=
      selectionSetFilteredReturnLookupValid_head hreturnLookup
    exact (hhead fieldDefinition hlookup).2 runtimeType hpossible
  · apply
      selectionSetFilteredReturnLookupValid_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_filteredReturnLookupValid_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition hobject hlookupValid hreturnLookup
        hmerge hlookup hpossible matchedFieldName matchedArguments
        matchedDirectives matchedSubselections hmatched

theorem selectionSetLookupValid_fieldHead_merged_of_filteredReturnLookup
    (schema : Schema)
    (parentType responseName fieldName returnType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetFilteredReturnLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> returnType = fieldDefinition.outputType.namedType
      -> selectionSetLookupValid schema returnType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType
                  responseName rest)) := by
  intro hobject hlookupValid hreturnLookup hmerge hlookup hreturn
  subst returnType
  apply selectionSetLookupValid_fieldHead_merged_of_matching schema
    parentType responseName fieldName fieldDefinition.outputType.namedType
    arguments subselections rest
  · have hhead :
        selectionFilteredReturnLookupValid schema parentType
          (Selection.field responseName fieldName arguments []
            subselections) :=
      selectionSetFilteredReturnLookupValid_head hreturnLookup
    exact (hhead fieldDefinition hlookup).1
  · exact
        runtimeMergeSource_matching_field_shape
        schema parentType responseName fieldName arguments subselections rest
        hobject hlookupValid hmerge
  · intro matchedArguments matchedDirectives matchedSubselections hmatchedMem
    have hmatchedField :
        selectionFilteredReturnLookupValid schema parentType
          (Selection.field responseName fieldName matchedArguments
            matchedDirectives matchedSubselections) := by
      have htailLookup :
          selectionSetFilteredReturnLookupValid schema parentType rest :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      exact
        fieldSelectionsWithResponseNameInScope_field_filteredReturnLookupValid
          schema parentType responseName hobject rest htailLookup fieldName
          matchedArguments matchedDirectives matchedSubselections hmatchedMem
    exact (hmatchedField fieldDefinition hlookup).1

/-
Proof-internal nonemptiness invariant for boolean-filtered branches. It is
conditioned on the current type-condition stack: a filtered composite field is
required to keep a child only when that stack is feasible, which is exactly the
situation where ground normalization can process that field.
-/
mutual
  def selectionFilteredCompositeChildrenNonempty (schema : Schema)
      (parentType : Name) (typeConditions : List Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        typeConditionStackFeasible schema typeConditions
        -> (∀ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition
              -> schema.isCompositeType fieldDefinition.outputType.namedType
              -> selectionSet ≠ [])
            ∧ match selectionSet with
              | [] => True
              | _ :: _ =>
                  match schema.lookupField parentType fieldName with
                  | none => False
                  | some fieldDefinition =>
                      let possibleTypes :=
                        schema.getPossibleTypes fieldDefinition.outputType.namedType
                      possibleTypes ≠ []
                      ∧ ∀ objectType,
                          objectType ∈ possibleTypes
                          -> selectionSetContainsTypeConditionFeasibleField schema
                                [objectType] selectionSet
                              ∧ selectionSetFilteredCompositeChildrenNonempty schema
                                  objectType [objectType] selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typesOverlapBool parentType typeCondition = true
        -> selectionSetFilteredCompositeChildrenNonempty schema parentType
            (typeCondition :: typeConditions) selectionSet

  def selectionSetFilteredCompositeChildrenNonempty (schema : Schema)
      (parentType : Name) (typeConditions : List Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionFilteredCompositeChildrenNonempty schema parentType
          typeConditions selection
        ∧ selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions rest
end

attribute [local simp] selectionSetFilteredCompositeChildrenNonempty

theorem selectionSetFilteredCompositeChildrenNonempty_head
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {selection : Selection} {rest : List Selection}
    : selectionSetFilteredCompositeChildrenNonempty schema parentType
        typeConditions (selection :: rest)
      -> selectionFilteredCompositeChildrenNonempty schema parentType
          typeConditions selection := by
  intro hvalid
  simpa [selectionSetFilteredCompositeChildrenNonempty] using hvalid.1

theorem selectionSetFilteredCompositeChildrenNonempty_tail
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {selection : Selection} {rest : List Selection}
    : selectionSetFilteredCompositeChildrenNonempty schema parentType
        typeConditions (selection :: rest)
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions rest := by
  intro hvalid
  simpa [selectionSetFilteredCompositeChildrenNonempty] using hvalid.2

theorem selectionSetFilteredCompositeChildrenNonempty_append
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {left right : List Selection}
    : selectionSetFilteredCompositeChildrenNonempty schema parentType typeConditions left
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions right
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa [selectionSetFilteredCompositeChildrenNonempty] using hright
  | cons selection rest ih =>
      have hhead :
          selectionFilteredCompositeChildrenNonempty schema parentType
            typeConditions selection :=
        selectionSetFilteredCompositeChildrenNonempty_head hleft
      have htail :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions rest :=
        selectionSetFilteredCompositeChildrenNonempty_tail hleft
      simp [selectionSetFilteredCompositeChildrenNonempty]
      exact ⟨hhead, ih htail⟩

mutual
  theorem selectionFilteredCompositeChildrenNonempty_of_stack_subset
      (schema : Schema) (parentType : Name)
      {sourceConditions targetConditions : List Name}
      : (∀ typeCondition,
          typeCondition ∈ sourceConditions -> typeCondition ∈ targetConditions)
        -> ∀ selection,
            selectionFilteredCompositeChildrenNonempty schema parentType
              sourceConditions selection
            -> selectionFilteredCompositeChildrenNonempty schema parentType
                targetConditions selection
    | hsubset,
      .field responseName fieldName arguments directives selectionSet,
      hnonempty => by
        simp [selectionFilteredCompositeChildrenNonempty]
        intro htargetFeasible
        have hsourceFeasible :
            typeConditionStackFeasible schema sourceConditions :=
          GroundTypeNormalization.typeConditionStackFeasible_of_subset_forValidity
            htargetFeasible hsubset
        exact hnonempty hsourceFeasible
    | hsubset, .inlineFragment none directives selectionSet, hnonempty => by
        simpa [selectionFilteredCompositeChildrenNonempty] using
          selectionSetFilteredCompositeChildrenNonempty_of_stack_subset
            schema parentType hsubset selectionSet hnonempty
    | hsubset, .inlineFragment (some typeCondition) directives selectionSet,
      hnonempty => by
        simp [selectionFilteredCompositeChildrenNonempty]
        intro hoverlap
        exact selectionSetFilteredCompositeChildrenNonempty_of_stack_subset
          schema parentType
          (sourceConditions := typeCondition :: sourceConditions)
          (targetConditions := typeCondition :: targetConditions)
          (by
            intro candidate hcandidate
            simp at hcandidate ⊢
            exact hcandidate.elim (fun hhead => Or.inl hhead)
              (fun htail => Or.inr (hsubset candidate htail)))
          selectionSet (hnonempty hoverlap)

  theorem selectionSetFilteredCompositeChildrenNonempty_of_stack_subset
      (schema : Schema) (parentType : Name)
      {sourceConditions targetConditions : List Name}
      : (∀ typeCondition,
          typeCondition ∈ sourceConditions -> typeCondition ∈ targetConditions)
        -> ∀ selectionSet,
            selectionSetFilteredCompositeChildrenNonempty schema parentType
              sourceConditions selectionSet
            -> selectionSetFilteredCompositeChildrenNonempty schema parentType
                targetConditions selectionSet
    | _hsubset, [], _hnonempty => by
        simp [selectionSetFilteredCompositeChildrenNonempty]
    | hsubset, selection :: rest, hnonempty => by
        have hhead :
            selectionFilteredCompositeChildrenNonempty schema parentType
              sourceConditions selection :=
          selectionSetFilteredCompositeChildrenNonempty_head hnonempty
        have htail :
            selectionSetFilteredCompositeChildrenNonempty schema parentType
              sourceConditions rest :=
          selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
        simp [selectionSetFilteredCompositeChildrenNonempty]
        exact ⟨
          selectionFilteredCompositeChildrenNonempty_of_stack_subset
            schema parentType hsubset selection hhead,
          selectionSetFilteredCompositeChildrenNonempty_of_stack_subset
            schema parentType hsubset rest htail⟩
end

theorem
    selectionSetFilteredCompositeChildrenNonempty_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName parentType : Name) (typeConditions : List Name)
    : ∀ selectionSet,
        selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions selectionSet
        -> selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions
            (withoutFieldSelectionsWithResponseName schema responseName
              selectionSet) := by
  have hmain :
      ∀ n selectionSet parentType typeConditions,
        SelectionSet.size selectionSet = n ->
        selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions selectionSet ->
        selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions
          (withoutFieldSelectionsWithResponseName schema responseName
            selectionSet) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro selectionSet parentType typeConditions hsize hvalid
        cases selectionSet with
        | nil =>
            simp [withoutFieldSelectionsWithResponseName,
              selectionSetFilteredCompositeChildrenNonempty]
        | cons selection rest =>
            have hhead :
                selectionFilteredCompositeChildrenNonempty schema parentType
                  typeConditions selection :=
              selectionSetFilteredCompositeChildrenNonempty_head hvalid
            have htail :
                selectionSetFilteredCompositeChildrenNonempty schema parentType
                  typeConditions rest :=
              selectionSetFilteredCompositeChildrenNonempty_tail hvalid
            have hrestSize :
                SelectionSet.size rest < n := by
              rw [← hsize]
              exact
                selectionSet_size_tail_lt_cons_for_currentScopeValidity
                  selection rest
            cases selection with
            | field fieldResponseName fieldName arguments directives selectionSet =>
                by_cases hresponse : (fieldResponseName == responseName) = true
                · simp [withoutFieldSelectionsWithResponseName, hresponse]
                  exact ih (SelectionSet.size rest) hrestSize rest
                    parentType typeConditions rfl htail
                · have hfalse :
                      (fieldResponseName == responseName) = false := by
                    cases hmatch : fieldResponseName == responseName
                    · rfl
                    · contradiction
                  simp [withoutFieldSelectionsWithResponseName, hfalse,
                    selectionSetFilteredCompositeChildrenNonempty]
                  exact ⟨hhead,
                    ih (SelectionSet.size rest) hrestSize rest parentType
                      typeConditions rfl htail⟩
            | inlineFragment typeCondition directives selectionSet =>
                have hchildSize :
                    SelectionSet.size selectionSet < n := by
                  rw [← hsize]
                  exact
                    selectionSet_size_child_lt_cons_inline_for_currentScopeValidity
                      typeCondition directives selectionSet rest
                cases typeCondition with
                | none =>
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetFilteredCompositeChildrenNonempty,
                      selectionFilteredCompositeChildrenNonempty]
                    exact ⟨
                      ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType typeConditions rfl hhead,
                      ih (SelectionSet.size rest) hrestSize rest parentType
                        typeConditions rfl htail⟩
                | some typeCondition =>
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetFilteredCompositeChildrenNonempty,
                      selectionFilteredCompositeChildrenNonempty]
                    exact ⟨
                      (by
                        intro hoverlap
                        exact ih (SelectionSet.size selectionSet) hchildSize
                          selectionSet parentType (typeCondition :: typeConditions)
                          rfl (hhead hoverlap)),
                      ih (SelectionSet.size rest) hrestSize rest parentType
                        typeConditions rfl htail
                    ⟩
  intro selectionSet hvalid
  exact hmain (SelectionSet.size selectionSet) selectionSet parentType
    typeConditions rfl hvalid

theorem selectionSetFilteredCompositeChildrenNonempty_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetFilteredCompositeChildrenNonempty schema parentType
              typeConditions selection.subselections)
        -> selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, selectionSetFilteredCompositeChildrenNonempty]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetFilteredCompositeChildrenNonempty_append
      · exact hvalid selection (by simp)
      · exact
          selectionSetFilteredCompositeChildrenNonempty_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate]))

theorem
    selectionSetFilteredCompositeChildrenNonempty_mergeSelectionSets_of_field_subselections
    {schema : Schema} {parentType responseName : Name} {typeConditions : List Name}
    (selections : List Selection)
    : (∀ selection,
        selection ∈ selections
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections)
      -> (∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ selections
            -> selectionSetFilteredCompositeChildrenNonempty schema parentType
                typeConditions subselections)
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions (mergeSelectionSets selections) := by
  intro hshape hfields
  apply
    selectionSetFilteredCompositeChildrenNonempty_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections]
    using hfields fieldName arguments directives subselections hselection

theorem
    selectionSetFilteredCompositeChildrenNonempty_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {parentType responseName childType : Name}
    {typeConditions : List Name} (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> selectionSetFilteredCompositeChildrenNonempty schema childType
            typeConditions subselections)
      -> selectionSetFilteredCompositeChildrenNonempty schema childType
          typeConditions
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType
              responseName selectionSet)) := by
  intro hfields
  apply
    selectionSetFilteredCompositeChildrenNonempty_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
      responseName selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
    (schema : Schema) (parentType responseName : Name) (typeConditions : List Name)
    : schema.objectType parentType
      -> GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
          parentType typeConditions
      -> ∀ selectionSet,
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions selectionSet
          -> ∀ fieldName arguments directives subselections,
              Selection.field responseName fieldName arguments directives subselections
                ∈ fieldSelectionsWithResponseNameInScope schema parentType
                    responseName selectionSet
              -> selectionFilteredCompositeChildrenNonempty schema parentType
                  typeConditions
                  (Selection.field responseName fieldName arguments directives
                    subselections)
  | _hobject, _hstack, [], _hvalid, _fieldName, _arguments, _directives, _subselections,
    hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | hobject, hstack, selection :: rest, hvalid, fieldName, arguments, directives,
    subselections, hfield => by
      have hhead :
          selectionFilteredCompositeChildrenNonempty schema parentType
            typeConditions selection :=
        selectionSetFilteredCompositeChildrenNonempty_head hvalid
      have htail :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions rest :=
        selectionSetFilteredCompositeChildrenNonempty_tail hvalid
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hmatched | hrest
            · rcases hmatched with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              exact hhead
            · exact
                fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
                  schema parentType responseName typeConditions hobject
                  hstack rest htail fieldName arguments directives
                  subselections hrest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
                schema parentType responseName typeConditions hobject hstack
                rest htail fieldName arguments directives subselections hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbody :
                  selectionSetFilteredCompositeChildrenNonempty schema
                    parentType typeConditions selectionSet := by
                simpa [selectionFilteredCompositeChildrenNonempty] using hhead
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbodyField | hrest
              · exact
                  fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
                    schema parentType responseName typeConditions hobject
                    hstack selectionSet hbody fieldName arguments directives
                    subselections hbodyField
              · exact
                  fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
                    schema parentType responseName typeConditions hobject
                    hstack rest htail fieldName arguments directives
                    subselections hrest
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hbody :
                    selectionSetFilteredCompositeChildrenNonempty schema
                      parentType (typeCondition :: typeConditions)
                      selectionSet := by
                  simpa [selectionFilteredCompositeChildrenNonempty] using
                    hhead hoverlap
                have hstackBody :
                    GroundTypeNormalization.objectSatisfiesTypeConditionStack
                      schema parentType (typeCondition :: typeConditions) :=
                  GroundTypeNormalization.objectSatisfiesTypeConditionStack_cons_of_overlap_forValidity
                    schema hobject hstack hoverlap
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbodyField | hrest
                · have hstrict :
                      selectionFilteredCompositeChildrenNonempty schema
                        parentType (typeCondition :: typeConditions)
                        (Selection.field responseName fieldName arguments
                          directives subselections) :=
                    fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
                      schema parentType responseName
                      (typeCondition :: typeConditions) hobject hstackBody
                      selectionSet hbody fieldName arguments directives
                      subselections hbodyField
                  intro _houterFeasible
                  exact hstrict
                    (GroundTypeNormalization.typeConditionStackFeasible_of_objectSatisfies_forValidity
                      hstackBody)
                · exact
                    fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
                      schema parentType responseName typeConditions hobject
                      hstack rest htail fieldName arguments directives
                      subselections hrest
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
                    schema parentType responseName typeConditions hobject
                    hstack rest htail fieldName arguments directives
                    subselections hfield

theorem
    fieldSelectionsWithResponseNameInScope_matching_subselections_filteredCompositeChildrenNonempty_of_child_object
    (schema : Schema) (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) (typeConditions : List Name)
    : schema.objectType parentType
      -> GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
          parentType typeConditions
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetFilteredCompositeChildrenNonempty schema runtimeType
              [runtimeType] matchedSubselections := by
  intro hobject hstack hlookupValid hnonempty hmerge hlookup hpossible
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailNonempty :
      selectionSetFilteredCompositeChildrenNonempty schema parentType
        typeConditions rest :=
    selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
  have hmatchedNonempty :
      selectionFilteredCompositeChildrenNonempty schema parentType
        typeConditions
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections) :=
    fieldSelectionsWithResponseNameInScope_field_filteredCompositeChildrenNonempty
      schema parentType responseName typeConditions hobject hstack
      rest htailNonempty matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
  have hsame :
      matchedFieldName = fieldName :=
    runtimeMergeSource_matching_same_field
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  have hstackFeasible :
      typeConditionStackFeasible schema typeConditions :=
    GroundTypeNormalization.typeConditionStackFeasible_of_objectSatisfies_forValidity
      hstack
  have hparts := hmatchedNonempty hstackFeasible
  cases matchedSubselections with
  | nil =>
      simp [selectionSetFilteredCompositeChildrenNonempty]
  | cons child children =>
      have hchildren := hparts.2
      rw [hlookup] at hchildren
      exact (hchildren.2 runtimeType hpossible).2

theorem selectionSetFilteredCompositeChildrenNonempty_fieldHead_merged_of_child_object
    (schema : Schema)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition) (typeConditions : List Name)
    : schema.objectType parentType
      -> GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
          parentType typeConditions
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> selectionSetFilteredCompositeChildrenNonempty schema runtimeType
          [runtimeType]
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType
                  responseName rest)) := by
  intro hobject hstack hlookupValid hnonempty hmerge hlookup hpossible
  apply selectionSetFilteredCompositeChildrenNonempty_append
  · have hhead :
        selectionFilteredCompositeChildrenNonempty schema parentType
          typeConditions
          (Selection.field responseName fieldName arguments []
            subselections) :=
      selectionSetFilteredCompositeChildrenNonempty_head hnonempty
    have hstackFeasible :
        typeConditionStackFeasible schema typeConditions :=
      GroundTypeNormalization.typeConditionStackFeasible_of_objectSatisfies_forValidity
        hstack
    have hparts := hhead hstackFeasible
    cases subselections with
    | nil =>
        simp [selectionSetFilteredCompositeChildrenNonempty]
    | cons child children =>
        have hchildren := hparts.2
        rw [hlookup] at hchildren
        exact (hchildren.2 runtimeType hpossible).2
  · apply
      selectionSetFilteredCompositeChildrenNonempty_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_filteredCompositeChildrenNonempty_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition typeConditions hobject hstack
        hlookupValid hnonempty hmerge hlookup hpossible matchedFieldName matchedArguments
        matchedDirectives matchedSubselections hmatched

theorem normalizedField_selectionValidInPossibleTypes_of_currentScope
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {sourceSubselections normalizedSubselections : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionValidInCurrentScope schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments [] sourceSubselections)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (schema.isCompositeType fieldDefinition.outputType.namedType
          -> normalizedSubselections ≠ [])
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (∀ objectType,
            objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
            -> Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType normalizedSubselections)
      -> (leafTypeNameBool schema fieldDefinition.outputType.namedType = true
          -> normalizedSubselections = [])
      -> Validation.selectionValidInPossibleTypes schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments []
            normalizedSubselections) := by
  intro hsourceCurrent hlookup hnormalizedValid hnormalizedNonempty
    hnormalizedImplementation hnormalizedPossible hnilIfLeaf
  have hsourceParts :
      Validation.selectionValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments []
            sourceSubselections)
        ∧ match schema.lookupField parentType fieldName with
          | none => False
          | some fieldDefinition =>
              ∀ objectType,
                objectType ∈
                    schema.getPossibleTypes fieldDefinition.outputType.namedType ->
                  selectionSetValidInCurrentScope schema
                    variableDefinitions objectType sourceSubselections := by
    simpa [selectionValidInCurrentScope] using hsourceCurrent
  rcases Validation.selectionValid_field_lookup hsourceParts.1 with
    ⟨sourceDefinition, hsourceLookup, harguments, hsourceChild⟩
  have hdefinitionEq : sourceDefinition = fieldDefinition := by
    rw [hlookup] at hsourceLookup
    cases hsourceLookup
    rfl
  subst sourceDefinition
  simp [Validation.selectionValidInPossibleTypes, hlookup]
  constructor
  · simp [Validation.selectionValid, Validation.directivesValid, hlookup]
    exact ⟨harguments,
      GroundTypeNormalization.fieldSelectionSetValid_normalized_of_source
        hsourceChild hnormalizedValid hnormalizedNonempty hnilIfLeaf⟩
  · exact hnormalizedPossible

theorem normalizedField_selectionValidInPossibleTypes_of_directedSource
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {sourceSubselections normalizedSubselections : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionValidInPossibleTypes schema variableDefinitions
        parentType
        (Selection.field responseName fieldName arguments directives sourceSubselections)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (schema.isCompositeType fieldDefinition.outputType.namedType
          -> normalizedSubselections ≠ [])
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (∀ objectType,
            objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
            -> Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType normalizedSubselections)
      -> (leafTypeNameBool schema fieldDefinition.outputType.namedType = true
          -> normalizedSubselections = [])
      -> Validation.selectionValidInPossibleTypes schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments []
            normalizedSubselections) := by
  intro hsource hlookup hnormalizedValid hnormalizedNonempty
    hnormalizedImplementation hnormalizedPossible hnilIfLeaf
  exact GroundTypeNormalization.normalizedField_selectionValidInPossibleTypes
    (selectionValidInPossibleTypes_field_clear_directives hsource)
    hlookup hnormalizedValid hnormalizedNonempty hnormalizedImplementation
    hnormalizedPossible hnilIfLeaf

theorem normalizedField_selectionValidInPossibleTypes_of_filteredCurrentSource
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {sourceSubselections normalizedSubselections : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionFilteredCurrentSourceValid schema variableDefinitions parentType
        (Selection.field responseName fieldName arguments [] sourceSubselections)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> Validation.selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (schema.isCompositeType fieldDefinition.outputType.namedType
          -> normalizedSubselections ≠ [])
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          fieldDefinition.outputType.namedType normalizedSubselections
      -> (∀ objectType,
            objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
            -> Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType normalizedSubselections)
      -> (leafTypeNameBool schema fieldDefinition.outputType.namedType = true
          -> normalizedSubselections = [])
      -> Validation.selectionValidInPossibleTypes schema variableDefinitions
          parentType
          (Selection.field responseName fieldName arguments []
            normalizedSubselections) := by
  intro hsource hlookup hnormalizedValid hnormalizedNonempty
    hnormalizedImplementation hnormalizedPossible hnilIfLeaf
  have hparts :
      ([] : List DirectiveApplication) = []
        ∧ ∃ sourceDirectives sourceSelectionSet sourceDefinition,
          schema.lookupField parentType fieldName = some sourceDefinition
            ∧ Validation.selectionValidInPossibleTypes schema
              variableDefinitions parentType
              (Selection.field responseName fieldName arguments
                sourceDirectives sourceSelectionSet)
            ∧ ∀ objectType,
              objectType ∈
                  schema.getPossibleTypes sourceDefinition.outputType.namedType ->
                selectionSetFilteredCurrentSourceValid schema variableDefinitions
                  objectType sourceSubselections := by
    simpa [selectionFilteredCurrentSourceValid] using hsource
  rcases hparts with
    ⟨_hdirectives, sourceDirectives, sourceSelectionSet, sourceDefinition,
      hsourceLookup, hsourceValid, _hchildren⟩
  have hdefinitionEq : sourceDefinition = fieldDefinition := by
    rw [hlookup] at hsourceLookup
    cases hsourceLookup
    rfl
  subst sourceDefinition
  exact normalizedField_selectionValidInPossibleTypes_of_directedSource
    hsourceValid hlookup hnormalizedValid hnormalizedNonempty
    hnormalizedImplementation hnormalizedPossible hnilIfLeaf

theorem fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetValidInCurrentScope schema variableDefinitions parentType selectionSet
        -> ∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                  selectionSet
            -> selectionValidInCurrentScope schema variableDefinitions parentType
                (Selection.field responseName fieldName arguments directives
                  subselections)
  | [], _hvalid, _fieldName, _arguments, _directives, _subselections,
    hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, hvalid, fieldName, arguments, directives,
    subselections, hfield => by
      have hhead :
          selectionValidInCurrentScope schema variableDefinitions parentType
            selection :=
        selectionSetValidInCurrentScope_head hvalid
      have htail :
          selectionSetValidInCurrentScope schema variableDefinitions parentType
            rest :=
        selectionSetValidInCurrentScope_tail hvalid
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hmatched | hrest
            · rcases hmatched with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              exact hhead
            · exact
                fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
                  schema variableDefinitions parentType responseName rest htail
                  fieldName arguments directives subselections hrest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
                schema variableDefinitions parentType responseName rest htail
                fieldName arguments directives subselections hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbody :
                  selectionSetValidInCurrentScope schema variableDefinitions
                    parentType selectionSet := by
                simpa [selectionValidInCurrentScope] using hhead
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbodyField | hrest
              · exact
                  fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
                    schema variableDefinitions parentType responseName
                    selectionSet hbody fieldName arguments directives
                    subselections hbodyField
              · exact
                  fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
                    schema variableDefinitions parentType responseName rest htail
                    fieldName arguments directives subselections hrest
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hbody :
                    selectionSetValidInCurrentScope schema variableDefinitions
                      parentType selectionSet := by
                  simpa [selectionValidInCurrentScope] using hhead hoverlap
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbodyField | hrest
                · exact
                    fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
                      schema variableDefinitions parentType responseName
                      selectionSet hbody fieldName arguments directives
                      subselections hbodyField
                · exact
                    fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
                      schema variableDefinitions parentType responseName rest htail
                      fieldName arguments directives subselections hrest
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
                    schema variableDefinitions parentType responseName rest htail
                    fieldName arguments directives subselections hfield

theorem selectionSetValidInCurrentScope_mergeSelectionSets_of_subselections
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetValidInCurrentScope schema variableDefinitions
              parentType selection.subselections)
        -> selectionSetValidInCurrentScope schema variableDefinitions
            parentType (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets, selectionSetValidInCurrentScope]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetValidInCurrentScope_append
      · exact hvalid selection (by simp)
      · exact
          selectionSetValidInCurrentScope_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate]))

theorem selectionSetValidInCurrentScope_mergeSelectionSets_of_field_subselections
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
            -> selectionSetValidInCurrentScope schema variableDefinitions parentType
                subselections)
      -> selectionSetValidInCurrentScope schema variableDefinitions parentType
          (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetValidInCurrentScope_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections]
    using hfields fieldName arguments directives subselections hselection

theorem
    selectionSetValidInCurrentScope_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName childType : Name} (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> selectionSetValidInCurrentScope schema variableDefinitions childType
            subselections)
      -> selectionSetValidInCurrentScope schema variableDefinitions childType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)) := by
  intro hfields
  apply selectionSetValidInCurrentScope_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
      responseName selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem
    fieldSelectionsWithResponseNameInScope_matching_subselections_validInCurrentScope_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name) (arguments : List Argument)
    (subselections rest : List Selection) (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetValidInCurrentScope schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetValidInCurrentScope schema variableDefinitions runtimeType
              matchedSubselections := by
  intro hobject hlookupValid hcurrent hmerge hlookup hpossible
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have htailCurrent :
      selectionSetValidInCurrentScope schema variableDefinitions parentType
        rest :=
    selectionSetValidInCurrentScope_tail hcurrent
  have hmatchedCurrent :
      selectionValidInCurrentScope schema variableDefinitions parentType
        (Selection.field responseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections) :=
    fieldSelectionsWithResponseNameInScope_field_validInCurrentScope
      schema variableDefinitions parentType responseName rest htailCurrent
      matchedFieldName matchedArguments matchedDirectives matchedSubselections
      hmatched
  have hsame :
      matchedFieldName = fieldName :=
    runtimeMergeSource_matching_same_field
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  have hparts :
      Validation.selectionValid schema variableDefinitions parentType
          (Selection.field responseName fieldName matchedArguments
            matchedDirectives matchedSubselections)
        ∧ ∀ objectType,
          objectType ∈
              schema.getPossibleTypes fieldDefinition.outputType.namedType ->
            selectionSetValidInCurrentScope schema variableDefinitions
              objectType matchedSubselections := by
    simpa [selectionValidInCurrentScope, hlookup] using hmatchedCurrent
  exact hparts.2 runtimeType hpossible

theorem selectionSetValidInCurrentScope_fieldHead_merged_of_child_object
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetValidInCurrentScope schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> selectionSetValidInCurrentScope schema variableDefinitions runtimeType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hobject hlookupValid hcurrent hmerge hlookup hpossible
  apply selectionSetValidInCurrentScope_append
  · have hheadCurrent :
        selectionValidInCurrentScope schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments [] subselections) :=
      selectionSetValidInCurrentScope_head hcurrent
    have hparts :
        Validation.selectionValid schema variableDefinitions parentType
            (Selection.field responseName fieldName arguments [] subselections)
          ∧ ∀ objectType,
            objectType ∈
                schema.getPossibleTypes fieldDefinition.outputType.namedType ->
              selectionSetValidInCurrentScope schema variableDefinitions
                objectType subselections := by
      simpa [selectionValidInCurrentScope, hlookup] using hheadCurrent
    exact hparts.2 runtimeType hpossible
  · apply
      selectionSetValidInCurrentScope_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_validInCurrentScope_of_child_object
        schema variableDefinitions parentType responseName fieldName
        runtimeType arguments subselections rest fieldDefinition hobject
        hlookupValid hcurrent hmerge hlookup hpossible matchedFieldName
        matchedArguments matchedDirectives matchedSubselections hmatched

mutual
  theorem filterSelectionSetBoolCase_selectionLookupValid
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType sourceSelection filteredSelection,
          filteredSelection ∈ filterSelectionSetBoolCase boolCase [sourceSelection]
          -> selectionLookupValid schema parentType sourceSelection
          -> selectionLookupValid schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionLookupValid] using hlookupValid
          | cons child children =>
              cases hchildFiltered :
                  filterSelectionSetBoolCase boolCase
                    (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  simpa [selectionLookupValid] using hlookupValid
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hsourceChildLookup :
                  selectionSetLookupValid schema parentType selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChildLookup :
                  selectionSetLookupValid schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetLookupValid schema
                    boolCase parentType selectionSet hsourceChildLookup
              simpa [selectionLookupValid] using hfilteredChildLookup
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hlookupValid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hsourceChildLookup :
                  selectionSetLookupValid schema typeCondition selectionSet := by
                simpa [selectionLookupValid] using hlookupValid
              have hfilteredChildLookup :
                  selectionSetLookupValid schema typeCondition
                    (filteredChild :: filteredChildren) := by
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetLookupValid schema
                    boolCase typeCondition selectionSet hsourceChildLookup
              simpa [selectionLookupValid] using hfilteredChildLookup
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem filterSelectionSetBoolCase_selectionSetLookupValid
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType selectionSet,
          selectionSetLookupValid schema parentType selectionSet
          -> selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hlookupValid => by
        simp [filterSelectionSetBoolCase, selectionSetLookupValid]
    | parentType, selection :: rest, hlookupValid => by
        have hhead :
            selectionLookupValid schema parentType selection :=
          selectionSetLookupValid_head hlookupValid
        have htail :
            selectionSetLookupValid schema parentType rest :=
          selectionSetLookupValid_tail hlookupValid
        have hheadFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetLookupValid
          intro candidate hcandidate
          exact filterSelectionSetBoolCase_selectionLookupValid schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetLookupValid schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          filterSelectionSetBoolCase_selectionSetLookupValid schema
            boolCase parentType rest htail
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetLookupValid_append hheadFiltered hrestFiltered
end

mutual
  theorem filterSelectionSetBoolCase_selectionSemanticsReady
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType sourceSelection filteredSelection,
          filteredSelection ∈ filterSelectionSetBoolCase boolCase [sourceSelection]
          -> selectionSemanticsReady schema parentType sourceSelection
          -> selectionSemanticsReady schema parentType filteredSelection
    | parentType,
      .field responseName fieldName arguments directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow] at hfiltered
              subst filteredSelection
              simpa [selectionSemanticsReady] using hready
          | cons child children =>
              cases hchildFiltered :
                  filterSelectionSetBoolCase boolCase
                    (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, _hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  exact ⟨fieldDefinition, hlookup, by
                    intro runtimeType _hincludes
                    exact selectionSetSemanticsReady_nil schema runtimeType⟩
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                    at hfiltered
                  subst filteredSelection
                  rcases (by
                    simpa [selectionSemanticsReady] using hready) with
                    ⟨fieldDefinition, hlookup, hchildrenReady⟩
                  simp [selectionSemanticsReady]
                  refine ⟨fieldDefinition, hlookup, ?_⟩
                  intro runtimeType hincludes
                  have hsourceChildReady :
                      selectionSetSemanticsReady schema runtimeType
                        (child :: children) :=
                    hchildrenReady runtimeType hincludes
                  simpa [hchildFiltered] using
                    filterSelectionSetBoolCase_selectionSetSemanticsReady
                      schema boolCase runtimeType (child :: children)
                      hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment none directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hsourceChildReady :
                  selectionSetSemanticsReady schema parentType selectionSet := by
                simpa [selectionSemanticsReady] using hready
              have hfilteredChildReady :
                  selectionSetSemanticsReady schema parentType
                    (filteredChild :: filteredChildren) := by
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetSemanticsReady
                    schema boolCase parentType selectionSet hsourceChildReady
              simpa [selectionSemanticsReady] using hfilteredChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered
    | parentType,
      .inlineFragment (some typeCondition) directives selectionSet,
      filteredSelection, hfiltered, hready => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchildFiltered :
            filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchildFiltered]
                at hfiltered
              subst filteredSelection
              have hreadyParts :
                  selectionSetLookupValid schema typeCondition selectionSet
                    ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                      selectionSetSemanticsReady schema parentType
                        selectionSet) := by
                simpa [selectionSemanticsReady] using hready
              simp [selectionSemanticsReady]
              constructor
              · simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetLookupValid schema
                    boolCase typeCondition selectionSet hreadyParts.1
              · intro hoverlap
                have hsourceChildReady :
                    selectionSetSemanticsReady schema parentType selectionSet :=
                  hreadyParts.2 hoverlap
                simpa [hchildFiltered] using
                  filterSelectionSetBoolCase_selectionSetSemanticsReady
                    schema boolCase parentType selectionSet hsourceChildReady
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse] at hfiltered

  theorem filterSelectionSetBoolCase_selectionSetSemanticsReady
      (schema : Schema) (boolCase : BoolCase)
      : ∀ parentType selectionSet,
          selectionSetSemanticsReady schema parentType selectionSet
          -> selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
    | parentType, [], _hready => by
        simpa [filterSelectionSetBoolCase] using
          selectionSetSemanticsReady_nil schema parentType
    | parentType, selection :: rest, hready => by
        have hhead :
            selectionSemanticsReady schema parentType selection := by
          unfold selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            selectionSetSemanticsReady schema parentType rest :=
          selectionSetSemanticsReady_tail hready
        have hheadFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase [selection]) := by
          unfold selectionSetSemanticsReady
          intro candidate hcandidate
          exact filterSelectionSetBoolCase_selectionSemanticsReady schema
            boolCase parentType selection candidate hcandidate hhead
        have hrestFiltered :
            selectionSetSemanticsReady schema parentType
              (filterSelectionSetBoolCase boolCase rest) :=
          filterSelectionSetBoolCase_selectionSetSemanticsReady schema
            boolCase parentType rest htailReady
        rw [filterSelectionSetBoolCase_cons]
        exact selectionSetSemanticsReady_append hheadFiltered hrestFiltered
end

mutual
  theorem selectionFilteredReturnLookupValid_filterSelectionSetBoolCase
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boolCase : BoolCase)
      : ∀ parentType,
          schema.objectType parentType
          -> ∀ selection,
              Validation.selectionValidInPossibleTypes schema
                variableDefinitions parentType selection
              -> selectionSetFilteredReturnLookupValid schema parentType
                  (filterSelectionSetBoolCase boolCase [selection])
    | parentType, hobject,
      .field responseName fieldName arguments directives selectionSet,
      hvalid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hsourceSelection :
              Validation.selectionValid schema variableDefinitions parentType
                (Selection.field responseName fieldName arguments directives
                  selectionSet) := by
            simpa [Validation.selectionValidInPossibleTypes] using hvalid.1
          rcases Validation.selectionValid_field_lookup hsourceSelection with
            ⟨fieldDefinition, hlookup, _harguments, hsourceChild⟩
          have hsourceChildLookup :
              selectionSetLookupValid schema
                fieldDefinition.outputType.namedType selectionSet :=
            selectionSetLookupValid_of_fieldSelectionSetValid_namedType
              hsourceChild
          have hfilteredChildLookup :
              selectionSetLookupValid schema
                fieldDefinition.outputType.namedType
                (filterSelectionSetBoolCase boolCase selectionSet) :=
            filterSelectionSetBoolCase_selectionSetLookupValid schema
              boolCase fieldDefinition.outputType.namedType selectionSet
              hsourceChildLookup
          have hchildren :
              ∀ objectType,
                objectType ∈
                    schema.getPossibleTypes
                      fieldDefinition.outputType.namedType ->
                  selectionSetFilteredReturnLookupValid schema objectType
                    (filterSelectionSetBoolCase boolCase selectionSet) := by
            intro objectType hpossible
            have hobjectType :
                schema.objectType objectType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema fieldDefinition.outputType.namedType objectType
                hpossible
            have hsourceChildImplementation :
                Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions objectType selectionSet := by
              have hchildren :
                  ∀ objectType,
                    objectType ∈
                        schema.getPossibleTypes
                          fieldDefinition.outputType.namedType ->
                      Validation.selectionSetValidInPossibleTypes schema
                        variableDefinitions objectType selectionSet := by
                simpa [Validation.selectionValidInPossibleTypes, hlookup]
                  using hvalid.2
              exact hchildren objectType hpossible
            exact
              selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
                schema variableDefinitions hschema boolCase objectType
                hobjectType selectionSet hsourceChildImplementation
          cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow,
                selectionSetFilteredReturnLookupValid,
                selectionFilteredReturnLookupValid]
              intro fieldDefinition' hlookup'
              have hdefinitionEq : fieldDefinition' = fieldDefinition := by
                rw [hlookup] at hlookup'
                cases hlookup'
                rfl
              subst fieldDefinition'
              simpa [filterSelectionSetBoolCase] using hfilteredChildLookup
          | cons child children =>
              cases hfiltered :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hfiltered,
                    selectionSetFilteredReturnLookupValid,
                    selectionFilteredReturnLookupValid]
                  intro fieldDefinition' hlookup'
                  have hdefinitionEq :
                      fieldDefinition' = fieldDefinition := by
                    rw [hlookup] at hlookup'
                    cases hlookup'
                    rfl
                  subst fieldDefinition'
                  simpa [hfiltered] using hfilteredChildLookup
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hfiltered,
                    selectionSetFilteredReturnLookupValid,
                    selectionFilteredReturnLookupValid]
                  intro fieldDefinition' hlookup'
                  have hdefinitionEq :
                      fieldDefinition' = fieldDefinition := by
                    rw [hlookup] at hlookup'
                    cases hlookup'
                    rfl
                  subst fieldDefinition'
                  exact ⟨by simpa [hfiltered] using hfilteredChildLookup,
                    by
                      intro objectType hpossible
                      simpa [hfiltered] using hchildren objectType hpossible⟩
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredReturnLookupValid]
    | parentType, hobject,
      .inlineFragment none directives selectionSet, hvalid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hsourceChildren :
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType selectionSet := by
            have hparentPossible :
                parentType ∈ schema.getPossibleTypes parentType :=
              List.contains_iff_mem.mp
                (object_typeIncludesObjectBool_self schema hobject)
            simpa [Validation.selectionValidInPossibleTypes] using
              hvalid parentType hparentPossible
          have hchildren :
              selectionSetFilteredReturnLookupValid schema parentType
                (filterSelectionSetBoolCase boolCase selectionSet) :=
            selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType hobject
              selectionSet hsourceChildren
          cases hfiltered :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hfiltered,
                selectionSetFilteredReturnLookupValid]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hfiltered,
                selectionSetFilteredReturnLookupValid,
                selectionFilteredReturnLookupValid]
              simpa [hfiltered] using hchildren
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredReturnLookupValid]
    | parentType, hobject,
      .inlineFragment (some typeCondition) directives selectionSet, hvalid => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hfiltered :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hfiltered,
                selectionSetFilteredReturnLookupValid]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hfiltered,
                selectionSetFilteredReturnLookupValid,
                selectionFilteredReturnLookupValid]
              intro hoverlap
              have hparentPossible :
                  parentType ∈ schema.getPossibleTypes typeCondition :=
                List.contains_iff_mem.mp
                  (typeIncludesObjectBool_of_object_typesOverlapBool schema
                    hobject hoverlap)
              have hsourceChildren :
                  Validation.selectionSetValidInPossibleTypes schema
                    variableDefinitions parentType selectionSet := by
                have hchildren :
                    ∀ objectType,
                      objectType ∈ schema.getPossibleTypes typeCondition ->
                        Validation.selectionSetValidInPossibleTypes schema
                          variableDefinitions objectType selectionSet := by
                  simpa [Validation.selectionValidInPossibleTypes, hoverlap]
                    using hvalid hoverlap
                exact hchildren parentType hparentPossible
              simpa [hfiltered] using
                selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
                  schema variableDefinitions hschema boolCase parentType
                  hobject selectionSet hsourceChildren
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredReturnLookupValid]

  theorem selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boolCase : BoolCase)
      : ∀ parentType,
          schema.objectType parentType
          -> ∀ selectionSet,
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType selectionSet
              -> selectionSetFilteredReturnLookupValid schema parentType
                  (filterSelectionSetBoolCase boolCase selectionSet)
    | _parentType, _hobject, [], _hvalid => by
        simp [filterSelectionSetBoolCase,
          selectionSetFilteredReturnLookupValid]
    | parentType, hobject, selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              parentType selection :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_head
            hvalid
        have htail :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions parentType rest :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_tail
            hvalid
        rw [filterSelectionSetBoolCase_cons]
        apply selectionSetFilteredReturnLookupValid_append
        · exact
            selectionFilteredReturnLookupValid_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType hobject
              selection hhead
        · exact
            selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType hobject
              rest htail
end

theorem filterSelectionSetBoolCase_singleton_nil_or_singleton
    (boolCase : BoolCase) (selection : Selection)
    : filterSelectionSetBoolCase boolCase [selection] = []
      ∨ ∃ filteredSelection,
          filterSelectionSetBoolCase boolCase [selection] = [filteredSelection] := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            exact Or.inr
              ⟨
                .field responseName fieldName arguments [] [],
                by simp [filterSelectionSetBoolCase, hallow]
              ⟩
        | cons child children =>
            cases hchild : filterSelectionSetBoolCase boolCase (child :: children) with
            | nil =>
                exact Or.inr
                  ⟨
                    .field responseName fieldName arguments [] [],
                    by
                      simp [filterSelectionSetBoolCase, hallow, hchild]
                  ⟩
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨
                    .field responseName fieldName arguments []
                      (filteredChild :: filteredChildren),
                    by
                      simp [filterSelectionSetBoolCase, hallow, hchild]
                  ⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        exact Or.inl (by simp [filterSelectionSetBoolCase, hfalse])
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases hchild : filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                exact Or.inl (by simp [filterSelectionSetBoolCase, hallow, hchild])
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨
                    .inlineFragment none [] (filteredChild :: filteredChildren),
                    by
                      simp [filterSelectionSetBoolCase, hallow, hchild]
                  ⟩
          · have hfalse :
                directivesAllowIn boolCase directives = false := by
              cases hmatch : directivesAllowIn boolCase directives
              · rfl
              · contradiction
            exact Or.inl (by simp [filterSelectionSetBoolCase, hfalse])
      | some typeCondition =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases hchild : filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                exact Or.inl (by simp [filterSelectionSetBoolCase, hallow, hchild])
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨
                    .inlineFragment (some typeCondition) []
                      (filteredChild :: filteredChildren),
                    by
                      simp [filterSelectionSetBoolCase, hallow, hchild]
                  ⟩
          · have hfalse :
                directivesAllowIn boolCase directives = false := by
              cases hmatch : directivesAllowIn boolCase directives
              · rfl
              · contradiction
            exact Or.inl (by simp [filterSelectionSetBoolCase, hfalse])

/-!
Case-local consequences used by the filtering proofs. The public feasibility
predicate packages these obligations without exposing existential/universal
modes.
-/

mutual
  def selectionBoolTypeConditionHasFieldInCase
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCase : BoolCase)
      : Selection -> Prop
    | .field _responseName _fieldName _arguments directives _selectionSet =>
        directivesAllowIn boolCase directives = true
        ∧ typeConditionStackFeasible schema typeConditions
    | .inlineFragment none directives selectionSet =>
        directivesAllowIn boolCase directives = true
        ∧ selectionSetBoolTypeConditionHasFieldInCase schema parentType
            typeConditions boolCase selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        directivesAllowIn boolCase directives = true
        ∧ selectionSetBoolTypeConditionHasFieldInCase schema parentType
            (typeCondition :: typeConditions) boolCase selectionSet

  def selectionSetBoolTypeConditionHasFieldInCase
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCase : BoolCase)
      : List Selection -> Prop
    | [] => False
    | selection :: rest =>
        selectionBoolTypeConditionHasFieldInCase schema parentType
          typeConditions boolCase selection
        ∨ selectionSetBoolTypeConditionHasFieldInCase schema parentType
            typeConditions boolCase rest

  def selectionBoolTypeConditionFeasibleInCase
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCase : BoolCase)
      : Selection -> Prop
    | .field _responseName fieldName _arguments directives selectionSet =>
        directivesAllowIn boolCase directives = true
        -> typeConditionStackFeasible schema typeConditions
            ∧ match selectionSet with
              | [] => True
              | _ :: _ =>
                  match schema.lookupField parentType fieldName with
                  | none => False
                  | some fieldDefinition =>
                      let possibleTypes :=
                        schema.getPossibleTypes fieldDefinition.outputType.namedType
                      possibleTypes ≠ []
                      ∧ ∀ objectType,
                          objectType ∈ possibleTypes
                          -> selectionSetBoolTypeConditionHasFieldInCase schema
                                objectType [objectType] boolCase selectionSet
                              ∧ selectionSetBoolTypeConditionFeasibleInCase schema
                                  objectType [objectType] boolCase selectionSet
    | .inlineFragment none directives selectionSet =>
        directivesAllowIn boolCase directives = true
        -> selectionSetBoolTypeConditionFeasibleInCase schema parentType
            typeConditions boolCase selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        directivesAllowIn boolCase directives = true
        -> selectionSetBoolTypeConditionFeasibleInCase schema parentType
            (typeCondition :: typeConditions) boolCase selectionSet

  def selectionSetBoolTypeConditionFeasibleInCase
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCase : BoolCase)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionBoolTypeConditionFeasibleInCase schema parentType typeConditions
          boolCase selection
        ∧ selectionSetBoolTypeConditionFeasibleInCase schema parentType
            typeConditions boolCase rest
end

theorem selectionSetBoolTypeConditionHasFieldInCase_of_mem
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {boolCase : BoolCase} {selection : Selection}
    : ∀ selectionSet,
        selection ∈ selectionSet
        -> selectionBoolTypeConditionHasFieldInCase schema parentType
            typeConditions boolCase selection
        -> selectionSetBoolTypeConditionHasFieldInCase schema parentType
            typeConditions boolCase selectionSet
  | [], hmem, _hselection => by
      cases hmem
  | head :: rest, hmem, hselection => by
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact Or.inl hselection
      · exact Or.inr
          (selectionSetBoolTypeConditionHasFieldInCase_of_mem rest hrest
            hselection)

private theorem selection_size_le_selectionSet_size_of_mem_for_boolFeasibility
    {selection : Selection} {selectionSet : List Selection}
    (hmem : selection ∈ selectionSet)
    : selection.size ≤ SelectionSet.size selectionSet := by
  induction selectionSet with
  | nil =>
      cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · simp [SelectionSet.size]
      · have := ih hrest
        simp [SelectionSet.size]
        omega

mutual
  theorem selectionBoolTypeConditionHasFieldInCase_of_feasible
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCases : List BoolCase)
      (boolCase : BoolCase)
      : ∀ selection,
          selectionBoolTypeConditionFeasible schema parentType typeConditions
            boolCases selection
          -> boolCase ∈ boolCases
          -> selectionAllowsIn boolCase selection = true
          -> selectionBoolTypeConditionHasFieldInCase schema parentType
              typeConditions boolCase selection
    | .field responseName fieldName arguments directives selectionSet,
      hfeasible, _hcase, hallow => by
        simp only [selectionBoolTypeConditionFeasible] at hfeasible
        exact ⟨by simpa [selectionAllowsIn] using hallow, hfeasible.2.1⟩
    | .inlineFragment none directives selectionSet,
      hfeasible, hcase, hallow => by
        simp only [selectionBoolTypeConditionFeasible] at hfeasible
        have hallowDirectives :
            directivesAllowIn boolCase directives = true := by
          simpa [selectionAllowsIn] using hallow
        have hallowedCase :
            boolCase
              ∈ boolCases.filter
                  (fun candidate =>
                    directivesAllowIn candidate directives) :=
          List.mem_filter.mpr ⟨hcase, hallowDirectives⟩
        exact ⟨hallowDirectives,
          selectionSetBoolTypeConditionHasFieldInCase_of_feasible
            schema parentType typeConditions
            (boolCases.filter
              (fun candidate => directivesAllowIn candidate directives))
            boolCase selectionSet hfeasible.2 hallowedCase⟩
    | .inlineFragment (some typeCondition) directives selectionSet,
      hfeasible, hcase, hallow => by
        simp only [selectionBoolTypeConditionFeasible] at hfeasible
        have hallowDirectives :
            directivesAllowIn boolCase directives = true := by
          simpa [selectionAllowsIn] using hallow
        have hallowedCase :
            boolCase
              ∈ boolCases.filter
                  (fun candidate =>
                    directivesAllowIn candidate directives) :=
          List.mem_filter.mpr ⟨hcase, hallowDirectives⟩
        exact ⟨hallowDirectives,
          selectionSetBoolTypeConditionHasFieldInCase_of_feasible
            schema parentType (typeCondition :: typeConditions)
            (boolCases.filter
              (fun candidate => directivesAllowIn candidate directives))
            boolCase selectionSet hfeasible.2 hallowedCase⟩
  termination_by selection => 2 * selection.size
  decreasing_by
    all_goals
      simp [Selection.size]
      omega

  theorem selectionSetBoolTypeConditionHasFieldInCase_of_feasible
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCases : List BoolCase)
      (boolCase : BoolCase)
      (selectionSet : List Selection)
      (hfeasible
        : selectionSetBoolTypeConditionFeasible schema parentType
            typeConditions boolCases selectionSet)
      (hcase : boolCase ∈ boolCases)
      : selectionSetBoolTypeConditionHasFieldInCase schema parentType
          typeConditions boolCase selectionSet := by
    simp only [selectionSetBoolTypeConditionFeasible] at hfeasible
    rcases hfeasible.2 boolCase hcase with
      ⟨selection, hselection, hallow⟩
    exact selectionSetBoolTypeConditionHasFieldInCase_of_mem
      selectionSet hselection
      (selectionBoolTypeConditionHasFieldInCase_of_feasible
        schema parentType typeConditions boolCases boolCase selection
        (hfeasible.1 selection hselection) hcase hallow)
  termination_by 2 * SelectionSet.size selectionSet + 1
  decreasing_by
    have hsize :=
      selection_size_le_selectionSet_size_of_mem_for_boolFeasibility
        (selection := selection) (selectionSet := selectionSet) hselection
    omega
end

theorem selectionSetBoolTypeConditionFeasible_selection
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {boolCases : List BoolCase} {selectionSet : List Selection}
    (hfeasible
      : selectionSetBoolTypeConditionFeasible schema parentType typeConditions
          boolCases selectionSet)
    {selection : Selection} (hselection : selection ∈ selectionSet)
    : selectionBoolTypeConditionFeasible schema parentType typeConditions
        boolCases selection := by
  simp only [selectionSetBoolTypeConditionFeasible] at hfeasible
  exact hfeasible.1 selection hselection

theorem selectionBoolTypeConditionFeasible_exists_allowed
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {boolCases : List BoolCase} {selection : Selection}
    (hfeasible
      : selectionBoolTypeConditionFeasible schema parentType typeConditions
          boolCases selection)
    : ∃ boolCase, boolCase ∈ boolCases ∧ selectionAllowsIn boolCase selection = true := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simp only [selectionBoolTypeConditionFeasible] at hfeasible
      rcases List.exists_mem_of_ne_nil _ hfeasible.1 with
        ⟨boolCase, hallowed⟩
      have hparts := List.mem_filter.mp hallowed
      exact ⟨boolCase, hparts.1, by simpa [selectionAllowsIn] using hparts.2⟩
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition <;>
        simp only [selectionBoolTypeConditionFeasible] at hfeasible
      all_goals
        rcases List.exists_mem_of_ne_nil _ hfeasible.1 with
          ⟨boolCase, hallowed⟩
        have hparts := List.mem_filter.mp hallowed
        exact ⟨boolCase, hparts.1,
          by simpa [selectionAllowsIn] using hparts.2⟩

mutual
  theorem selectionBoolTypeConditionFeasibleInCase_of_feasible
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCases : List BoolCase)
      (boolCase : BoolCase)
      : ∀ selection,
          selectionBoolTypeConditionFeasible schema parentType typeConditions
            boolCases selection
          -> boolCase ∈ boolCases
          -> selectionBoolTypeConditionFeasibleInCase schema parentType
              typeConditions boolCase selection
    | .field responseName fieldName arguments directives selectionSet,
      hfeasible, hcase => by
        simp only [selectionBoolTypeConditionFeasible] at hfeasible
        simp only [selectionBoolTypeConditionFeasibleInCase]
        intro hallow
        refine ⟨hfeasible.2.1, ?_⟩
        cases hselectionSet : selectionSet with
        | nil =>
            simp_all
        | cons child children =>
            subst selectionSet
            rcases hfeasible.2.2 with hnil | hchildren
            · cases hnil
            · cases hlookup :
                schema.lookupField parentType fieldName with
              | none =>
                  simp [hlookup] at hchildren
              | some fieldDefinition =>
                  simp only [hlookup] at hchildren ⊢
                  let allowedCases :=
                    boolCases.filter
                      (fun candidate =>
                        directivesAllowIn candidate directives)
                  have hallowedCase : boolCase ∈ allowedCases := by
                    exact List.mem_filter.mpr ⟨hcase, hallow⟩
                  refine ⟨hchildren.1, ?_⟩
                  intro objectType hobject
                  have himplementation := hchildren.2 objectType hobject
                  exact
                    ⟨selectionSetBoolTypeConditionHasFieldInCase_of_feasible
                        schema objectType [objectType] allowedCases boolCase
                        (child :: children) himplementation hallowedCase,
                      selectionSetBoolTypeConditionFeasibleInCase_of_all
                        schema objectType [objectType] allowedCases boolCase
                        (child :: children)
                        (fun candidate hcandidate =>
                          selectionSetBoolTypeConditionFeasible_selection
                            himplementation hcandidate)
                        hallowedCase⟩
    | .inlineFragment none directives selectionSet,
      hfeasible, hcase => by
        simp only [selectionBoolTypeConditionFeasible] at hfeasible
        simp only [selectionBoolTypeConditionFeasibleInCase]
        intro hallow
        let allowedCases :=
          boolCases.filter
            (fun candidate => directivesAllowIn candidate directives)
        have hallowedCase : boolCase ∈ allowedCases :=
          List.mem_filter.mpr ⟨hcase, hallow⟩
        exact selectionSetBoolTypeConditionFeasibleInCase_of_all schema
          parentType typeConditions allowedCases boolCase selectionSet
          (fun candidate hcandidate =>
            selectionSetBoolTypeConditionFeasible_selection
              hfeasible.2 hcandidate)
          hallowedCase
    | .inlineFragment (some typeCondition) directives selectionSet,
      hfeasible, hcase => by
        simp only [selectionBoolTypeConditionFeasible] at hfeasible
        simp only [selectionBoolTypeConditionFeasibleInCase]
        intro hallow
        let allowedCases :=
          boolCases.filter
            (fun candidate => directivesAllowIn candidate directives)
        have hallowedCase : boolCase ∈ allowedCases :=
          List.mem_filter.mpr ⟨hcase, hallow⟩
        exact selectionSetBoolTypeConditionFeasibleInCase_of_all schema
          parentType (typeCondition :: typeConditions) allowedCases boolCase
          selectionSet
          (fun candidate hcandidate =>
            selectionSetBoolTypeConditionFeasible_selection
              hfeasible.2 hcandidate)
          hallowedCase
  termination_by selection => 2 * selection.size
  decreasing_by
    all_goals
      simp_all [Selection.size, SelectionSet.size]
      omega

  theorem selectionSetBoolTypeConditionFeasibleInCase_of_all
      (schema : Schema) (parentType : Name)
      (typeConditions : List Name) (boolCases : List BoolCase)
      (boolCase : BoolCase)
      : ∀ selectionSet,
          (∀ selection,
            selection ∈ selectionSet
            -> selectionBoolTypeConditionFeasible schema parentType
                typeConditions boolCases selection)
          -> boolCase ∈ boolCases
          -> selectionSetBoolTypeConditionFeasibleInCase schema parentType
              typeConditions boolCase selectionSet
    | [], _hall, _hcase => by
        simp [selectionSetBoolTypeConditionFeasibleInCase]
    | selection :: rest, hall, hcase => by
        constructor
        · exact selectionBoolTypeConditionFeasibleInCase_of_feasible schema
            parentType typeConditions boolCases boolCase selection
            (hall selection (by simp)) hcase
        · exact selectionSetBoolTypeConditionFeasibleInCase_of_all schema
            parentType typeConditions boolCases boolCase rest
            (fun candidate hcandidate =>
              hall candidate (List.mem_cons_of_mem selection hcandidate))
            hcase
  termination_by selectionSet => 2 * SelectionSet.size selectionSet + 1
  decreasing_by
    all_goals
      have htail :=
        selectionSet_size_tail_lt_cons_for_currentScopeValidity selection rest
      simp [SelectionSet.size] at htail ⊢
      omega
end

mutual
  theorem typeConditionStackFeasible_of_selectionBoolTypeConditionFeasible_exists
      (schema : Schema) (boolCase : BoolCase)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selection,
          selectionBoolTypeConditionHasFieldInCase schema parentType typeConditions
            boolCase selection
          -> typeConditionStackFeasible schema typeConditions
    | .field _responseName _fieldName _arguments _directives _selectionSet,
      hfeasible => by
        exact hfeasible.2
    | .inlineFragment none _directives selectionSet, hfeasible => by
        exact
          typeConditionStackFeasible_of_selectionSetBoolTypeConditionFeasible_exists
            schema boolCase parentType typeConditions selectionSet
            hfeasible.2
    | .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible => by
        have hchild :
            typeConditionStackFeasible schema
              (typeCondition :: typeConditions) :=
          typeConditionStackFeasible_of_selectionSetBoolTypeConditionFeasible_exists
            schema boolCase parentType (typeCondition :: typeConditions)
            selectionSet hfeasible.2
        exact
          GroundTypeNormalization.typeConditionStackFeasible_of_subset_forValidity
            hchild
            (by
              intro candidate hcandidate
              exact List.mem_cons_of_mem typeCondition hcandidate)

  theorem typeConditionStackFeasible_of_selectionSetBoolTypeConditionFeasible_exists
      (schema : Schema) (boolCase : BoolCase)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selectionSet,
          selectionSetBoolTypeConditionHasFieldInCase schema parentType
            typeConditions boolCase selectionSet
          -> typeConditionStackFeasible schema typeConditions
    | [], hfeasible => by
        cases hfeasible
    | selection :: rest, hfeasible => by
        rcases hfeasible with hhead | htail
        · exact
            typeConditionStackFeasible_of_selectionBoolTypeConditionFeasible_exists
              schema boolCase parentType typeConditions selection hhead
        · exact
            typeConditionStackFeasible_of_selectionSetBoolTypeConditionFeasible_exists
              schema boolCase parentType typeConditions rest htail
end

mutual
  theorem selectionContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selection,
          selectionBoolTypeConditionHasFieldInCase schema parentType typeConditions
            boolCase selection
          -> selectionSetContainsTypeConditionFeasibleField schema typeConditions
              (filterSelectionSetBoolCase boolCase [selection])
    | .field responseName fieldName arguments directives selectionSet,
      hcontains => by
        rcases hcontains with ⟨hallow, hstack⟩
        cases selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow,
              selectionSetContainsTypeConditionFeasibleField,
              selectionContainsTypeConditionFeasibleField, hstack]
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase (child :: children)
            <;>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetContainsTypeConditionFeasibleField,
                selectionContainsTypeConditionFeasibleField, hstack]
    | .inlineFragment none directives selectionSet, hcontains => by
        rcases hcontains with ⟨hallow, hchildContainsBool⟩
        have hchildContains :
          selectionSetContainsTypeConditionFeasibleField schema
              typeConditions
              (filterSelectionSetBoolCase boolCase selectionSet) :=
          selectionSetContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
            schema boolCase parentType typeConditions selectionSet
            hchildContainsBool
        cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            have hfalse : False := by
              rw [hchild] at hchildContains
              exact hchildContains
            exact False.elim hfalse
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              selectionSetContainsTypeConditionFeasibleField,
              selectionContainsTypeConditionFeasibleField]
            simpa [hchild] using hchildContains
    | .inlineFragment (some typeCondition) directives selectionSet,
      hcontains => by
        rcases hcontains with ⟨hallow, hchildContainsBool⟩
        have hchildContains :
          selectionSetContainsTypeConditionFeasibleField schema
              (typeCondition :: typeConditions)
              (filterSelectionSetBoolCase boolCase selectionSet) :=
          selectionSetContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
            schema boolCase parentType (typeCondition :: typeConditions)
            selectionSet hchildContainsBool
        cases hchild :
            filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            have hfalse : False := by
              rw [hchild] at hchildContains
              exact hchildContains
            exact False.elim hfalse
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              selectionSetContainsTypeConditionFeasibleField,
              selectionContainsTypeConditionFeasibleField]
            simpa [hchild] using hchildContains

  theorem selectionSetContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selectionSet,
          selectionSetBoolTypeConditionHasFieldInCase schema parentType
            typeConditions boolCase selectionSet
          -> selectionSetContainsTypeConditionFeasibleField schema typeConditions
              (filterSelectionSetBoolCase boolCase selectionSet)
    | [], hcontains => by
        cases hcontains
    | selection :: rest, hcontains => by
        rw [filterSelectionSetBoolCase_cons]
        rcases hcontains with hhead | htail
        · exact GroundTypeNormalization.selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
            schema typeConditions
            (selectionContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
              schema boolCase parentType typeConditions selection hhead)
        · exact GroundTypeNormalization.selectionSetContainsTypeConditionFeasibleField_append_right_forValidity
            schema typeConditions
            (filterSelectionSetBoolCase boolCase [selection])
            (selectionSetContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
              schema boolCase parentType typeConditions rest htail)
end

theorem fieldFilteredCompositeChild_empty_of_boolTypeConditionFeasible_all
    (schema : Schema) (boolCase : BoolCase)
    (parentType : Name) (typeConditions : List Name)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (child : Selection) (children : List Selection)
    : selectionBoolTypeConditionFeasibleInCase schema parentType typeConditions
        boolCase
        (.field responseName fieldName arguments directives (child :: children))
      -> directivesAllowIn boolCase directives = true
      -> filterSelectionSetBoolCase boolCase (child :: children) = []
      -> ¬ typeConditionStackFeasible schema typeConditions := by
  intro hfeasible hallow hfiltered hstack
  have hsource := (hfeasible hallow).2
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      simp [hlookup] at hsource
  | some fieldDefinition =>
      have hparts :
          schema.getPossibleTypes fieldDefinition.outputType.namedType ≠ []
            ∧ ∀ objectType,
              objectType ∈
                  schema.getPossibleTypes
                    fieldDefinition.outputType.namedType ->
                selectionSetBoolTypeConditionHasFieldInCase schema
                    objectType [objectType] boolCase
                    (child :: children)
                  ∧ selectionSetBoolTypeConditionFeasibleInCase schema
                      objectType [objectType] boolCase
                      (child :: children) := by
        simpa [hlookup] using hsource
      rcases List.exists_mem_of_ne_nil _ hparts.1 with
        ⟨objectType, hobjectType⟩
      have hcontains :
          selectionSetContainsTypeConditionFeasibleField schema
            [objectType]
            (filterSelectionSetBoolCase boolCase (child :: children)) :=
        selectionSetContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
          schema boolCase objectType [objectType] (child :: children)
          (hparts.2 objectType hobjectType).1
      rw [hfiltered] at hcontains
      exact hcontains

mutual
  theorem selectionFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boolCase : BoolCase)
      : ∀ parentType typeConditions,
          schema.objectType parentType
          -> ∀ selection,
              Validation.selectionValidInPossibleTypes schema
                variableDefinitions parentType selection
              -> selectionBoolTypeConditionFeasibleInCase schema parentType typeConditions
                  boolCase selection
              -> selectionSetFilteredCompositeChildrenNonempty schema parentType
                  typeConditions (filterSelectionSetBoolCase boolCase [selection])
    | parentType, typeConditions, hobject,
      .field responseName fieldName arguments directives selectionSet,
      hvalid, hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hsourceSelection :
              Validation.selectionValid schema variableDefinitions parentType
                (Selection.field responseName fieldName arguments directives
                  selectionSet) := by
            simpa [Validation.selectionValidInPossibleTypes] using hvalid.1
          rcases Validation.selectionValid_field_lookup hsourceSelection with
            ⟨sourceDefinition, hsourceLookup, _harguments,
              hsourceChildren⟩
          cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow,
                selectionSetFilteredCompositeChildrenNonempty,
                selectionFilteredCompositeChildrenNonempty]
              intro _hstack
              intro fieldDefinition hlookup hcomposite
              have hdefinitionEq : sourceDefinition = fieldDefinition := by
                rw [hlookup] at hsourceLookup
                cases hsourceLookup
                rfl
              subst sourceDefinition
              have hsourceChildrenParts :
                  fieldDefinition.outputType.isOutputType schema
                    ∧ schema.isLeafType
                      fieldDefinition.outputType.namedType := by
                simpa [Validation.fieldSelectionSetValid] using
                  hsourceChildren
              have hleaf :
                  schema.isLeafType fieldDefinition.outputType.namedType :=
                hsourceChildrenParts.2
              exact
                GroundTypeNormalization.isLeafType_not_isCompositeType
                  hleaf hcomposite
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    selectionSetFilteredCompositeChildrenNonempty,
                    selectionFilteredCompositeChildrenNonempty]
                  intro hstack
                  intro _fieldDefinition _hlookup _hcomposite
                  exact False.elim
                    ((fieldFilteredCompositeChild_empty_of_boolTypeConditionFeasible_all
                      schema boolCase parentType typeConditions responseName
                      fieldName arguments directives child children
                      hfeasible hallow hchild) hstack)
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    selectionSetFilteredCompositeChildrenNonempty,
                    selectionFilteredCompositeChildrenNonempty]
                  intro hstack
                  have hsource := (hfeasible hallow).2
                  cases hlookup : schema.lookupField parentType fieldName with
                  | none =>
                      simp [hlookup] at hsource
                  | some fieldDefinition =>
                      have hparts :
                          schema.getPossibleTypes
                                fieldDefinition.outputType.namedType ≠ []
                            ∧ ∀ objectType,
                              objectType ∈
                                  schema.getPossibleTypes
                                    fieldDefinition.outputType.namedType ->
                                selectionSetBoolTypeConditionHasFieldInCase schema
                                    objectType [objectType] boolCase
                                    (child :: children)
                                  ∧ selectionSetBoolTypeConditionFeasibleInCase schema
                                      objectType [objectType] boolCase
                                      (child :: children) := by
                        simpa [hlookup] using hsource
                      constructor
                      · exact hparts.1
                      · intro objectType hpossible
                        constructor
                        · simpa [hchild] using
                            selectionSetContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
                              schema boolCase objectType [objectType]
                              (child :: children)
                              (hparts.2 objectType hpossible).1
                        have hobjectType :
                            schema.objectType objectType :=
                          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                            hschema fieldDefinition.outputType.namedType
                            objectType hpossible
                        have hchildImplementation :
                            Validation.selectionSetValidInPossibleTypes schema
                              variableDefinitions objectType
                              (child :: children) := by
                          have hchildren :
                              ∀ objectType,
                                objectType ∈
                                    schema.getPossibleTypes
                                      fieldDefinition.outputType.namedType ->
                                  Validation.selectionSetValidInPossibleTypes
                                    schema variableDefinitions objectType
                                    (child :: children) := by
                            simpa [Validation.selectionValidInPossibleTypes,
                              hlookup] using hvalid.2
                          exact hchildren objectType hpossible
                        exact
                          (by
                            simpa [hchild] using
                              selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
                                schema variableDefinitions hschema boolCase
                                objectType [objectType] hobjectType
                                (child :: children) hchildImplementation
                                (hparts.2 objectType hpossible).2)
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredCompositeChildrenNonempty]
    | parentType, typeConditions, hobject,
      .inlineFragment none directives selectionSet, hvalid, hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hsourceChildren :
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType selectionSet := by
            have hparentPossible :
                parentType ∈ schema.getPossibleTypes parentType :=
              List.contains_iff_mem.mp
                (object_typeIncludesObjectBool_self schema hobject)
            simpa [Validation.selectionValidInPossibleTypes] using
              hvalid parentType hparentPossible
          have hchildNonempty :
              selectionSetFilteredCompositeChildrenNonempty schema parentType
                typeConditions
                (filterSelectionSetBoolCase boolCase selectionSet) :=
            selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType
              typeConditions hobject selectionSet hsourceChildren
              (by
                simpa [selectionBoolTypeConditionFeasibleInCase]
                  using hfeasible hallow)
          cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCompositeChildrenNonempty]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCompositeChildrenNonempty,
                selectionFilteredCompositeChildrenNonempty]
              simpa [hchild] using hchildNonempty
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredCompositeChildrenNonempty]
    | parentType, typeConditions, hobject,
      .inlineFragment (some typeCondition) directives selectionSet, hvalid,
      hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCompositeChildrenNonempty]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetFilteredCompositeChildrenNonempty,
                selectionFilteredCompositeChildrenNonempty]
              intro hoverlap
              have hparentPossible :
                  parentType ∈ schema.getPossibleTypes typeCondition :=
                List.contains_iff_mem.mp
                  (typeIncludesObjectBool_of_object_typesOverlapBool schema
                    hobject hoverlap)
              have hsourceChildren :
                  Validation.selectionSetValidInPossibleTypes schema
                    variableDefinitions parentType selectionSet := by
                have hchildren :
                    ∀ objectType,
                      objectType ∈ schema.getPossibleTypes typeCondition ->
                        Validation.selectionSetValidInPossibleTypes schema
                          variableDefinitions objectType selectionSet := by
                  simpa [Validation.selectionValidInPossibleTypes, hoverlap]
                    using hvalid hoverlap
                exact hchildren parentType hparentPossible
              simpa [hchild] using
                selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
                  schema variableDefinitions hschema boolCase parentType
                  (typeCondition :: typeConditions) hobject selectionSet
                  hsourceChildren
                  (by
                    simpa [selectionBoolTypeConditionFeasibleInCase]
                      using hfeasible hallow)
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetFilteredCompositeChildrenNonempty]

  theorem selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (boolCase : BoolCase)
      : ∀ parentType typeConditions,
          schema.objectType parentType
          -> ∀ selectionSet,
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions parentType selectionSet
              -> selectionSetBoolTypeConditionFeasibleInCase schema parentType
                  typeConditions boolCase selectionSet
              -> selectionSetFilteredCompositeChildrenNonempty schema parentType
                  typeConditions (filterSelectionSetBoolCase boolCase selectionSet)
    | _parentType, _typeConditions, _hobject, [], _hvalid, _hfeasible => by
        simp [filterSelectionSetBoolCase,
          selectionSetFilteredCompositeChildrenNonempty]
    | parentType, typeConditions, hobject, selection :: rest, hvalid,
      hfeasible => by
        have hheadValid :
            Validation.selectionValidInPossibleTypes schema
              variableDefinitions parentType selection :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_head hvalid
        have htailValid :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions parentType rest :=
          GroundTypeNormalization.selectionSetValidInPossibleTypes_tail hvalid
        have hheadFeasible :
            selectionBoolTypeConditionFeasibleInCase schema parentType
              typeConditions boolCase selection := by
          simpa [selectionSetBoolTypeConditionFeasibleInCase] using hfeasible.1
        have htailFeasible :
            selectionSetBoolTypeConditionFeasibleInCase schema parentType
              typeConditions boolCase rest := by
          simpa [selectionSetBoolTypeConditionFeasibleInCase] using hfeasible.2
        rw [filterSelectionSetBoolCase_cons]
        apply selectionSetFilteredCompositeChildrenNonempty_append
        · exact
            selectionFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType
              typeConditions hobject selection hheadValid hheadFeasible
        · exact
            selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
              schema variableDefinitions hschema boolCase parentType
              typeConditions hobject rest htailValid htailFeasible
end

theorem selectionSetBoolTypeConditionFeasible_withoutFieldSelectionsWithResponseName
    (schema : Schema) (boolCase : BoolCase) (responseName : Name)
    (parentType : Name) (typeConditions : List Name)
    : ∀ selectionSet,
        selectionSetBoolTypeConditionFeasibleInCase schema parentType typeConditions
          boolCase selectionSet
        -> selectionSetBoolTypeConditionFeasibleInCase schema parentType typeConditions
            boolCase
            (withoutFieldSelectionsWithResponseName schema responseName
              selectionSet) := by
  have hmain :
      ∀ n selectionSet parentType typeConditions,
        SelectionSet.size selectionSet = n ->
        selectionSetBoolTypeConditionFeasibleInCase schema parentType
          typeConditions boolCase selectionSet ->
        selectionSetBoolTypeConditionFeasibleInCase schema parentType
          typeConditions boolCase
          (withoutFieldSelectionsWithResponseName schema responseName
            selectionSet) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro selectionSet parentType typeConditions hsize hfeasible
        cases selectionSet with
        | nil =>
            simp [withoutFieldSelectionsWithResponseName,
              selectionSetBoolTypeConditionFeasibleInCase]
        | cons selection rest =>
            have hhead :
                selectionBoolTypeConditionFeasibleInCase schema parentType
                  typeConditions boolCase selection := by
              simpa [selectionSetBoolTypeConditionFeasibleInCase] using hfeasible.1
            have htail :
                selectionSetBoolTypeConditionFeasibleInCase schema parentType
                  typeConditions boolCase rest := by
              simpa [selectionSetBoolTypeConditionFeasibleInCase] using hfeasible.2
            have hrestSize :
                SelectionSet.size rest < n := by
              rw [← hsize]
              exact
                selectionSet_size_tail_lt_cons_for_currentScopeValidity
                  selection rest
            cases selection with
            | field fieldResponseName fieldName arguments directives selectionSet =>
                by_cases hresponse : (fieldResponseName == responseName) = true
                · simp [withoutFieldSelectionsWithResponseName, hresponse]
                  exact ih (SelectionSet.size rest) hrestSize rest
                    parentType typeConditions rfl htail
                · have hfalse :
                      (fieldResponseName == responseName) = false := by
                    cases hmatch : fieldResponseName == responseName
                    · rfl
                    · contradiction
                  simp [withoutFieldSelectionsWithResponseName, hfalse,
                    selectionSetBoolTypeConditionFeasibleInCase]
                  exact ⟨hhead,
                    ih (SelectionSet.size rest) hrestSize rest parentType
                      typeConditions rfl htail⟩
            | inlineFragment typeCondition directives selectionSet =>
                have hchildSize :
                    SelectionSet.size selectionSet < n := by
                  rw [← hsize]
                  exact
                    selectionSet_size_child_lt_cons_inline_for_currentScopeValidity
                      typeCondition directives selectionSet rest
                cases typeCondition with
                | none =>
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetBoolTypeConditionFeasibleInCase,
                      selectionBoolTypeConditionFeasibleInCase]
                    constructor
                    · intro hallow
                      exact ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType typeConditions rfl
                        (by
                          simpa [selectionBoolTypeConditionFeasibleInCase]
                            using hhead hallow)
                    · exact ih (SelectionSet.size rest) hrestSize rest
                        parentType typeConditions rfl htail
                | some typeCondition =>
                    simp [withoutFieldSelectionsWithResponseName,
                      selectionSetBoolTypeConditionFeasibleInCase,
                      selectionBoolTypeConditionFeasibleInCase]
                    constructor
                    · intro hallow
                      exact ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType
                        (typeCondition :: typeConditions) rfl
                        (by
                          simpa [selectionBoolTypeConditionFeasibleInCase]
                            using hhead hallow)
                    · exact ih (SelectionSet.size rest) hrestSize rest
                        parentType typeConditions rfl htail
  intro selectionSet hfeasible
  exact hmain (SelectionSet.size selectionSet) selectionSet parentType
    typeConditions rfl hfeasible

theorem typesOverlapBool_false_of_infeasible_cons_stack
    (schema : Schema) {parentType typeCondition : Name}
    {typeConditions : List Name}
    : schema.objectType parentType
      -> GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
          parentType typeConditions
      -> ¬ typeConditionStackFeasible schema (typeCondition :: typeConditions)
      -> schema.typesOverlapBool parentType typeCondition = false := by
  intro hobject hstack hinfeasible
  cases hoverlap : schema.typesOverlapBool parentType typeCondition
  · rfl
  · have hstackCons :
        GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
          parentType (typeCondition :: typeConditions) :=
      GroundTypeNormalization.objectSatisfiesTypeConditionStack_cons_of_overlap_forValidity
        schema hobject hstack hoverlap
    exact False.elim
      (hinfeasible
        (GroundTypeNormalization.typeConditionStackFeasible_of_objectSatisfies_forValidity
          hstackCons))

mutual
  theorem selectionTypeConditionFeasible_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selection,
          selectionBoolTypeConditionFeasibleInCase schema parentType typeConditions
            boolCase selection
          -> selectionSetTypeConditionFeasible schema parentType typeConditions
              (filterSelectionSetBoolCase boolCase [selection])
    | .field responseName fieldName arguments directives selectionSet,
      hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · cases selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow,
                selectionSetTypeConditionFeasible,
                selectionTypeConditionFeasible]
              exact (hfeasible hallow).1
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase (child :: children) with
              | nil =>
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    selectionSetTypeConditionFeasible,
                    selectionTypeConditionFeasible]
                  exact (hfeasible hallow).1
              | cons filteredChild filteredChildren =>
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    selectionSetTypeConditionFeasible,
                    selectionTypeConditionFeasible]
                  have hsource := hfeasible hallow
                  constructor
                  · exact hsource.1
                  ·
                    cases hlookup : schema.lookupField parentType fieldName with
                    | none =>
                        simp [hlookup] at hsource
                    | some fieldDefinition =>
                        have hparts :
                          schema.getPossibleTypes
                                fieldDefinition.outputType.namedType ≠ []
                            ∧ ∀ objectType,
                              objectType ∈
                                  schema.getPossibleTypes
                                    fieldDefinition.outputType.namedType ->
                                selectionSetBoolTypeConditionHasFieldInCase schema
                                    objectType [objectType] boolCase
                                    (child :: children)
                                  ∧ selectionSetBoolTypeConditionFeasibleInCase schema
                                      objectType [objectType] boolCase
                                      (child :: children) := by
                          simpa [hlookup] using hsource.2
                        constructor
                        · exact hparts.1
                        · intro objectType hobjectType
                          have hobjectParts := hparts.2 objectType hobjectType
                          simpa [hchild] using
                            selectionSetTypeConditionFeasible_filterSelectionSetBoolCase
                              schema boolCase objectType [objectType]
                              (child :: children) hobjectParts.2
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetTypeConditionFeasible]
    | .inlineFragment none directives selectionSet, hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hchildFeasible := hfeasible hallow
          cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetTypeConditionFeasible]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetTypeConditionFeasible,
                selectionTypeConditionFeasible]
              simpa [hchild] using
                selectionSetTypeConditionFeasible_filterSelectionSetBoolCase
                  schema boolCase parentType typeConditions selectionSet
                  hchildFeasible
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetTypeConditionFeasible]
    | .inlineFragment (some typeCondition) directives selectionSet,
      hfeasible => by
        by_cases hallow : directivesAllowIn boolCase directives = true
        · have hchildFeasible := hfeasible hallow
          cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetTypeConditionFeasible]
          | cons filteredChild filteredChildren =>
              simp [filterSelectionSetBoolCase, hallow, hchild,
                selectionSetTypeConditionFeasible,
                selectionTypeConditionFeasible]
              simpa [hchild] using
                selectionSetTypeConditionFeasible_filterSelectionSetBoolCase
                  schema boolCase parentType (typeCondition :: typeConditions)
                  selectionSet hchildFeasible
        · have hfalse :
              directivesAllowIn boolCase directives = false := by
            cases hmatch : directivesAllowIn boolCase directives
            · rfl
            · contradiction
          simp [filterSelectionSetBoolCase, hfalse,
            selectionSetTypeConditionFeasible]

  theorem selectionSetTypeConditionFeasible_filterSelectionSetBoolCase
      (schema : Schema) (boolCase : BoolCase)
      (parentType : Name) (typeConditions : List Name)
      : ∀ selectionSet,
          selectionSetBoolTypeConditionFeasibleInCase schema parentType
            typeConditions boolCase selectionSet
          -> selectionSetTypeConditionFeasible schema parentType typeConditions
              (filterSelectionSetBoolCase boolCase selectionSet)
    | [], _hfeasible => by
        simp [filterSelectionSetBoolCase, selectionSetTypeConditionFeasible]
    | selection :: rest, hfeasible => by
        rw [filterSelectionSetBoolCase_cons]
        apply GroundTypeNormalization.selectionSetTypeConditionFeasible_append
        · exact selectionTypeConditionFeasible_filterSelectionSetBoolCase
            schema boolCase parentType typeConditions selection hfeasible.1
        · exact selectionSetTypeConditionFeasible_filterSelectionSetBoolCase
            schema boolCase parentType typeConditions rest hfeasible.2
end

theorem normalizeSelectionSet_normalizedValid_of_filteredCurrentSource
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
      ∀ typeConditions,
        schema.objectType parentType
        -> GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
            parentType typeConditions
        -> parentType ∈ typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType selectionSet
        -> selectionSetFilteredReturnLookupValid schema parentType selectionSet
        -> runtimeMergeSource schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions selectionSet
        -> GroundTypeNormalization.NormalizedSelectionSetValid schema
            variableDefinitions parentType
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _typeConditions _hobject _hstack _hparent _hready _hsource
        _hreturnLookup _hmerge _hfree _hfeasible _hnonempty
      simpa [normalizeSelectionSet]
        using GroundTypeNormalization.normalizedSelectionSetValid_nil schema
          variableDefinitions parentType
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro typeConditions hobject hstack hparent hready hsource hreturnLookup
        hmerge hfree hfeasible hnonempty
      have htailSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rest :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType rest :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          runtimeMergeSource schema parentType rest :=
        runtimeMergeSource_tail hmerge
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetFilteredCurrentSourceValid_withoutFieldSelectionsWithResponseName
          schema responseName parentType variableDefinitions rest htailSource
      have hfilteredReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetFilteredReturnLookupValid_withoutFieldSelectionsWithResponseName
          schema responseName parentType rest htailReturnLookup
      have hfilteredMerge :
          runtimeMergeSource schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        runtimeMergeSource_without schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest
          (selectionSetTypeConditionFeasible_tail hfeasible)
      have htailNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions rest :=
        selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
      have hfilteredNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetFilteredCompositeChildrenNonempty_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailNonempty
      simpa [normalizeSelectionSet, hlookup]
        using hrest typeConditions hobject hstack hparent hfilteredReady hfilteredSource
          hfilteredReturnLookup hfilteredMerge hfilteredFree hfilteredFeasible
          hfilteredNonempty
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro typeConditions hobject hstack hparent hready hsource hreturnLookup
        hmerge hfree hfeasible hnonempty
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hsubselectionsFree : selectionSetDirectiveFree subselections :=
        hselectionFree.2
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rest :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType rest :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have htailMerge :
          runtimeMergeSource schema parentType rest :=
        runtimeMergeSource_tail hmerge
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetFilteredCurrentSourceValid_withoutFieldSelectionsWithResponseName
          schema responseName parentType variableDefinitions rest htailSource
      have hfilteredReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetFilteredReturnLookupValid_withoutFieldSelectionsWithResponseName
          schema responseName parentType rest htailReturnLookup
      have hfilteredMerge :
          runtimeMergeSource schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        runtimeMergeSource_without schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailFeasible
      have htailNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions rest :=
        selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
      have hfilteredNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetFilteredCompositeChildrenNonempty_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailNonempty
      have hnormalizedRest :
          GroundTypeNormalization.NormalizedSelectionSetValid schema
            variableDefinitions parentType
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)) :=
        hrest typeConditions hobject hstack hparent hfilteredReady hfilteredSource
          hfilteredReturnLookup hfilteredMerge hfilteredFree hfilteredFeasible
          hfilteredNonempty
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments []
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments []
            subselections :: rest)
          hready
      have hmatchingFree :
          selectionSetDirectiveFree matching := by
        subst matching
        exact fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
          responseName rest hrestFree
      have hmergedFree :
          selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetDirectiveFree_append hsubselectionsFree
          (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hheadFeasible :
          selectionTypeConditionFeasible schema parentType typeConditions
            (Selection.field responseName fieldName arguments []
              subselections) := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have hmergedFeasible :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetTypeConditionFeasible schema objectType [objectType] mergedSubselections := by
        intro objectType hobjectType
        have hheadChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType] subselections :=
          selectionTypeConditionFeasible_field_child_branch_forObject
            schema hheadFeasible hstack hlookup
            (by simpa [returnType] using hobjectType)
        have hmatchingChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType] (mergeSelectionSets matching) := by
          subst matching
          apply
            selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
          intro matchedFieldName matchedArguments matchedDirectives
            matchedSubselections hmatched
          have hsame :
              matchedFieldName = fieldName :=
            runtimeMergeSource_matching_same_field
              schema parentType responseName fieldName arguments subselections
              rest hobject hlookupValid hmerge matchedFieldName
              matchedArguments matchedDirectives matchedSubselections hmatched
          subst matchedFieldName
          exact
            fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
              schema parentType responseName hobject hstack rest
              htailFeasible fieldName matchedArguments matchedDirectives
              matchedSubselections fieldDefinition objectType hmatched hlookup
              (by simpa [returnType] using hobjectType)
        subst mergedSubselections
        exact selectionSetTypeConditionFeasible_append hheadChildFeasible
          hmatchingChildFeasible
      have hchildSource :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetFilteredCurrentSourceValid schema variableDefinitions
                objectType mergedSubselections := by
        intro objectType hobjectType
        subst mergedSubselections
        exact
          selectionSetFilteredCurrentSourceValid_fieldHead_merged_of_child_object
            schema variableDefinitions parentType responseName fieldName
            objectType arguments subselections rest fieldDefinition hobject
            hlookupValid hsource hmerge hlookup
            (by simpa [returnType] using hobjectType)
      have hchildNonempty :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetFilteredCompositeChildrenNonempty schema objectType
                [objectType] mergedSubselections := by
        intro objectType hobjectType
        subst mergedSubselections
        exact
          selectionSetFilteredCompositeChildrenNonempty_fieldHead_merged_of_child_object
            schema parentType responseName fieldName objectType arguments
            subselections rest fieldDefinition typeConditions hobject hstack
            hlookupValid hnonempty hmerge hlookup
            (by simpa [returnType] using hobjectType)
      have hchildReturnLookup :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetFilteredReturnLookupValid schema objectType
                mergedSubselections := by
        intro objectType hobjectType
        subst mergedSubselections
        exact
          selectionSetFilteredReturnLookupValid_fieldHead_merged_of_child_object
            schema parentType responseName fieldName objectType arguments
            subselections rest fieldDefinition hobject hlookupValid
            hreturnLookup hmerge hlookup
            (by simpa [returnType] using hobjectType)
      have hnormalizedSubselectionsValid :
          GroundTypeNormalization.NormalizedSelectionSetValid schema
            variableDefinitions returnType normalizedSubselections := by
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType]
              using object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup (by simpa [returnType] using hinclude)
          simpa [hreturnObject]
            using hmerged [returnType] hreturnObjectType
              (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hreturnObjectType)
              (by simp) hchildReady
              (hchildSource returnType
                (by
                  simpa [returnType]
                    using (List.contains_iff_mem.mp
                            (object_typeIncludesObjectBool_self schema
                              hreturnObjectType))))
              (hchildReturnLookup returnType
                (by
                  simpa [returnType]
                    using (List.contains_iff_mem.mp
                            (object_typeIncludesObjectBool_self schema
                              hreturnObjectType))))
              (runtimeMergeSource_fieldHead_merged schema hschema hmerge hlookup hinclude)
              hmergedFree
              (hmergedFeasible returnType
                (by
                  simpa [returnType]
                    using (List.contains_iff_mem.mp
                            (object_typeIncludesObjectBool_self schema
                              hreturnObjectType))))
              (hchildNonempty returnType
                (by
                  simpa [returnType]
                    using (List.contains_iff_mem.mp
                            (object_typeIncludesObjectBool_self schema
                              hreturnObjectType))))
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          apply GroundTypeNormalization.possibleTypeNormalizations_normalizedValid
            schema variableDefinitions returnType
            (schema.getPossibleTypes returnType) mergedSubselections
          · intro objectType hobjectType
            exact
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType
          · intro objectType hobjectType
            exact hobjectType
          · intro objectType hobjectType
            have hobjectBranch :
                schema.objectType objectType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType
            have hinclude :
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType objectType = true :=
              List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType)
            have hchildReady :
                selectionSetSemanticsReady schema objectType
                  mergedSubselections :=
              runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup (by simpa [returnType] using hinclude)
            exact hpossible objectType [objectType] hobjectBranch
              (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hobjectBranch)
              (by simp)
              hchildReady
              (hchildSource objectType hobjectType)
              (hchildReturnLookup objectType hobjectType)
              (runtimeMergeSource_fieldHead_merged schema hschema hmerge hlookup hinclude)
              hmergedFree
              (hmergedFeasible objectType hobjectType)
              (hchildNonempty objectType hobjectType)
          · rcases hmerge with ⟨sources, hsources⟩
            apply GroundTypeNormalization.normalizedDistinctBranchesPairwiseMerge_of_runtimeSources
              (sources := fieldProjectionChildren schema
                (runtimeMergeParentSources schema parentType responseName sources))
              schema hschema
            · intro objectType hobjectType
              exact SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType objectType hobjectType
            · exact hmergedFree
            · intro objectType hobjectType
              exact runtimeMergeSource_fieldHead_semanticsReady schema ⟨sources, hsources⟩
                hready hlookup (List.contains_iff_mem.mpr hobjectType)
            · intro objectType hobjectType
              exact runtimeMergeSources_fieldHead_merged schema hschema hsources hlookup
                (List.contains_iff_mem.mpr hobjectType)
      have hnilIfLeaf :
          leafTypeNameBool schema fieldDefinition.outputType.namedType = true ->
            normalizedSubselections = [] := by
        intro hleaf
        subst normalizedSubselections
        have hobjectFalse :
            objectTypeNameBool schema returnType = false :=
          objectTypeNameBool_eq_false_of_isLeafType schema
            (by
              have hleafType :=
                leafTypeNameBool_eq_true_isLeafType schema
                  (by simpa [returnType] using hleaf)
              simpa [returnType] using hleafType)
        have hpossibleNil :
            schema.getPossibleTypes returnType = [] :=
          possibleTypes_eq_nil_of_leafTypeNameBool schema
            (by simpa [returnType] using hleaf)
        simp [hobjectFalse, hpossibleNil, possibleTypeNormalizations]
      have hnormalizedSubselectionsPossible :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes
                fieldDefinition.outputType.namedType ->
              Validation.selectionSetValidInPossibleTypes schema
                variableDefinitions objectType normalizedSubselections := by
        intro objectType hobjectType
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hobjectEq : objectType = returnType :=
            object_typeIncludesObjectBool_eq_self schema hreturnObjectType
              (List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType))
          subst objectType
          simpa [hreturnObject] using hnormalizedSubselectionsValid.validInPossibleTypes
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          apply GroundTypeNormalization.possibleTypeNormalizations_validInPossibleTypes
            (parentType := objectType)
          · intro branchType hbranchType
            exact
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType branchType hbranchType
          · intro branchType hbranchType
            have hbranchObject :
                schema.objectType branchType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType branchType hbranchType
            have hinclude :
                schema.typeIncludesObjectBool
                  fieldDefinition.outputType.namedType branchType = true :=
              List.contains_iff_mem.mpr
                (by simpa [returnType] using hbranchType)
            have hchildReady :
                selectionSetSemanticsReady schema branchType
                  mergedSubselections :=
              runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup
                (by simpa [returnType] using hinclude)
            have hchildMerge :
                runtimeMergeSource schema branchType
                  mergedSubselections :=
              runtimeMergeSource_fieldHead_merged schema hschema hmerge hlookup hinclude
            exact hpossible branchType [branchType] hbranchObject
              (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hbranchObject)
              (by simp)
              hchildReady
              (hchildSource branchType hbranchType)
              (hchildReturnLookup branchType hbranchType)
              hchildMerge hmergedFree
              (hmergedFeasible branchType hbranchType)
              (hchildNonempty branchType hbranchType)
      have hsubselectionsNonemptyOfComposite :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            subselections ≠ [] := by
        intro hcomposite
        have hheadNonempty :
            selectionFilteredCompositeChildrenNonempty schema parentType
              typeConditions
              (Selection.field responseName fieldName arguments []
                subselections) :=
          selectionSetFilteredCompositeChildrenNonempty_head hnonempty
        have hstackFeasible :
            typeConditionStackFeasible schema typeConditions :=
          GroundTypeNormalization.typeConditionStackFeasible_of_objectSatisfies_forValidity
            hstack
        exact (hheadNonempty hstackFeasible).1 fieldDefinition hlookup hcomposite
      have hmergedNonemptyOfComposite :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            mergedSubselections ≠ [] := by
        intro hcomposite hnil
        have hsubselectionsNonempty :
            subselections ≠ [] :=
          hsubselectionsNonemptyOfComposite hcomposite
        subst mergedSubselections
        cases subselections with
        | nil =>
            exact hsubselectionsNonempty rfl
        | cons selection rest =>
            simp at hnil
      have hnormalizedSubselectionsNonempty :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            normalizedSubselections ≠ [] := by
        intro hcomposite
        have hmergedNonempty :
            mergedSubselections ≠ [] :=
          hmergedNonemptyOfComposite hcomposite
        have hsubselectionsNonempty :
            subselections ≠ [] :=
          hsubselectionsNonemptyOfComposite hcomposite
        have hheadNonempty :
            selectionFilteredCompositeChildrenNonempty schema parentType
              typeConditions
              (Selection.field responseName fieldName arguments []
                subselections) :=
          selectionSetFilteredCompositeChildrenNonempty_head hnonempty
        have hstackFeasible :
            typeConditionStackFeasible schema typeConditions :=
          GroundTypeNormalization.typeConditionStackFeasible_of_objectSatisfies_forValidity
            hstack
        have hchildWitness :
            ∃ objectType,
              objectType ∈ schema.getPossibleTypes returnType
              ∧ selectionSetContainsTypeConditionFeasibleField schema
                  [objectType] subselections := by
          have hparts := hheadNonempty hstackFeasible
          cases subselections with
          | nil =>
              exact False.elim (hsubselectionsNonempty rfl)
          | cons child children =>
              have hchildren := hparts.2
              rw [hlookup] at hchildren
              rcases List.exists_mem_of_ne_nil _ hchildren.1 with
                ⟨objectType, hobjectType⟩
              exact ⟨
                objectType,
                by simpa [returnType] using hobjectType,
                (hchildren.2 objectType hobjectType).1
              ⟩
        rcases hchildWitness with
          ⟨childObjectType, hchildObjectType, hheadChildContains⟩
        have hmergedContains :
            selectionSetContainsTypeConditionFeasibleField schema
              [childObjectType]
              mergedSubselections := by
          subst mergedSubselections
          exact
            selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
              schema [childObjectType] hheadChildContains
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hchildObjectEq :
              childObjectType = returnType :=
            object_typeIncludesObjectBool_eq_self schema hreturnObjectType
              (List.contains_iff_mem.mpr hchildObjectType)
          subst childObjectType
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType]
              using object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup (by simpa [returnType] using hinclude)
          simpa [hreturnObject]
            using normalizeSelectionSet_ne_nil_of_contains schema
              returnType mergedSubselections hreturnObjectType hchildReady
              hmergedContains
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          have hbranchObject :
              schema.objectType childObjectType :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
              hschema returnType childObjectType hchildObjectType
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType childObjectType = true :=
            List.contains_iff_mem.mpr
              (by simpa [returnType] using hchildObjectType)
          have hchildReady :
              selectionSetSemanticsReady schema childObjectType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup (by simpa [returnType] using hinclude)
          exact
            possibleTypeNormalizations_ne_nil_of_branch_forValidity schema
              hchildObjectType
              (normalizeSelectionSet_ne_nil_of_contains schema
                childObjectType mergedSubselections hbranchObject hchildReady
                hmergedContains)
      have hconsNormalizedValid
          (hnonemptyField :
            schema.isCompositeType fieldDefinition.outputType.namedType ->
              normalizedSubselections ≠ []) :
          GroundTypeNormalization.NormalizedSelectionSetValid schema
            variableDefinitions parentType
            (Selection.field responseName fieldName arguments []
                normalizedSubselections ::
              normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest)) := by
        have hnormalizedFieldImplementation :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              parentType
              (Selection.field responseName fieldName arguments []
                normalizedSubselections) :=
          normalizedField_selectionValidInPossibleTypes_of_filteredCurrentSource
            (selectionSetFilteredCurrentSourceValid_head hsource)
            hlookup hnormalizedSubselectionsValid.selectionSetValid
            hnonemptyField
            hnormalizedSubselectionsValid.validInPossibleTypes
            hnormalizedSubselectionsPossible
            hnilIfLeaf
        have himplementation :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions parentType
              (Selection.field responseName fieldName arguments []
                  normalizedSubselections ::
                normalizeSelectionSet schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName
                    rest)) :=
          selectionSetValidInPossibleTypes_cons
            hnormalizedFieldImplementation
            hnormalizedRest.validInPossibleTypes
        have hselectionSetValid :
            Validation.selectionSetValid schema variableDefinitions parentType
              (Selection.field responseName fieldName arguments []
                  normalizedSubselections ::
                normalizeSelectionSet schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName
                    rest)) :=
          selectionSetValid_of_allFields_validInPossibleTypes schema
            variableDefinitions parentType
            (Selection.field responseName fieldName arguments []
                normalizedSubselections ::
              normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest))
            (by
              intro selection hselection
              simp at hselection
              rcases hselection with hhead | htail
              · subst selection
                simp [Selection.isField]
              · exact normalizeSelectionSet_allFields schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName
                    rest)
                  selection htail)
            himplementation
        have hrestFreeResponse :
            selectionSetResponseNameFree schema parentType responseName
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest)) :=
          normalizeSelectionSet_responseNameFree schema parentType responseName
            (withoutFieldSelectionsWithResponseName schema responseName rest)
            (withoutFieldSelectionsWithResponseName_responseNameFree schema
              parentType responseName rest)
        have hfieldMergePair :
            FieldMerge.fieldsInSetCanMerge schema parentType
                (Selection.field responseName fieldName arguments []
                    normalizedSubselections ::
                  normalizeSelectionSet schema parentType
                    (withoutFieldSelectionsWithResponseName schema responseName
                      rest))
              ∧ ∀ mergeParent,
                FieldMerge.fieldsInSetCanMerge schema mergeParent
                ((Selection.field responseName fieldName arguments []
                      normalizedSubselections ::
                    normalizeSelectionSet schema parentType
                      (withoutFieldSelectionsWithResponseName schema responseName
                        rest))
                  ++
                  (Selection.field responseName fieldName arguments []
                      normalizedSubselections ::
                    normalizeSelectionSet schema parentType
                      (withoutFieldSelectionsWithResponseName schema responseName
                        rest))) := by
          apply fieldsInSetCanMerge_field_cons_of_rest_responseNameFree
          · exact hschema
          · exact hlookup
          · exact SchemaWellFormedness.sameTypeShape_refl schema
              fieldDefinition.outputType
              (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
                hschema hlookup)
          · exact argumentsEquivalent_refl arguments
          · intro objectType
            exact hnormalizedSubselectionsValid.fieldsCanMergeSelf objectType
          · exact hnormalizedRest.fieldsCanMerge
          · exact hnormalizedRest.fieldsCanMergeSelf
          · exact normalizeSelectionSet_allFields schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)
          · exact hrestFreeResponse
        exact ⟨hselectionSetValid, himplementation, hfieldMergePair.1,
          fun mergeParent => hfieldMergePair.2 mergeParent⟩
      have hfinal :
          GroundTypeNormalization.NormalizedSelectionSetValid schema
            variableDefinitions parentType
            (normalizedFieldWithRest schema returnType responseName fieldName
              arguments [] normalizedSubselections
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName
                  rest))) := by
        simpa [normalizedFieldWithRest, normalizedField]
          using hconsNormalizedValid hnormalizedSubselectionsNonempty
      rw [normalizeSelectionSet.eq_2, hlookup]
      change GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions parentType
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments [] normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      exact hfinal
  | case4 parentType rest directives subselections happend =>
      intro typeConditions hobject hstack hparent hready hsource hreturnLookup
        hmerge hfree hfeasible hnonempty
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hhead :
            selectionSemanticsReady schema parentType
              (Selection.inlineFragment none [] subselections) := by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
        simpa [selectionSemanticsReady] using hhead
      have hheadSource :=
        selectionSetFilteredCurrentSourceValid_head hsource
      have hbodySource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType subselections := by
        simpa [selectionFilteredCurrentSourceValid] using hheadSource.2
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailSource :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType (subselections ++ rest) :=
        selectionSetFilteredCurrentSourceValid_append hbodySource htailSource
      have hheadReturnLookup :=
        selectionSetFilteredReturnLookupValid_head hreturnLookup
      have hbodyReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            subselections := by
        simpa [selectionFilteredReturnLookupValid] using hheadReturnLookup
      have hbodyTailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetFilteredReturnLookupValid_append hbodyReturnLookup
          htailReturnLookup
      have hbodyTailMerge :
          runtimeMergeSource schema parentType
            (subselections ++ rest) :=
        runtimeMergeSource_inlineFragment_flatten schema parentType none
          subselections rest (by simp) hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions subselections := by
        simpa [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible]
          using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasible htailFeasible
      have hheadNonempty :=
        selectionSetFilteredCompositeChildrenNonempty_head hnonempty
      have hbodyNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions subselections := by
        simpa [selectionFilteredCompositeChildrenNonempty] using hheadNonempty
      have htailNonempty :=
        selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
      have hbodyTailNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions (subselections ++ rest) :=
        selectionSetFilteredCompositeChildrenNonempty_append hbodyNonempty
          htailNonempty
      simpa [normalizeSelectionSet]
        using happend typeConditions hobject hstack hparent hbodyTailReady
          hbodyTailSource hbodyTailReturnLookup hbodyTailMerge
          hbodyTailFree hbodyTailFeasible hbodyTailNonempty
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro typeConditions hobject hstack hparent hready hsource hreturnLookup
        hmerge hfree hfeasible hnonempty
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) []
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hheadSource :=
        selectionSetFilteredCurrentSourceValid_head hsource
      have hbodySource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType subselections := by
        simpa [selectionFilteredCurrentSourceValid] using hheadSource.2 hoverlap
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailSource :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType (subselections ++ rest) :=
        selectionSetFilteredCurrentSourceValid_append hbodySource htailSource
      have hheadReturnLookup :=
        selectionSetFilteredReturnLookupValid_head hreturnLookup
      have hbodyReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            subselections := by
        simpa [selectionFilteredReturnLookupValid] using hheadReturnLookup hoverlap
      have hbodyTailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetFilteredReturnLookupValid_append hbodyReturnLookup
          htailReturnLookup
      have hlookupBodyType :
          selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hlookupBodyParent :
          selectionSetLookupValid schema parentType subselections :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hbodyReady
      have hlookupRest :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hbodyTailMerge :
          runtimeMergeSource schema parentType
            (subselections ++ rest) :=
        runtimeMergeSource_inlineFragment_flatten schema parentType (some typeCondition)
          subselections rest (by intro _ h; cases h; exact hoverlap) hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible]
          using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have htailFeasibleInBodyStack
          : selectionSetTypeConditionFeasible schema parentType
              (typeCondition :: typeConditions) rest := by
        have hcondition :
            parentType ∈ schema.getPossibleTypes typeCondition :=
          List.contains_iff_mem.mp
            (typeIncludesObjectBool_of_object_typesOverlapBool schema
              hobject hoverlap)
        simpa using
          selectionSetTypeConditionFeasible_insert_condition_for_object
            schema hobject hcondition hparent [] rest htailFeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions)
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasible
          htailFeasibleInBodyStack
      have hstackBody :
          GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
            parentType (typeCondition :: typeConditions) :=
        GroundTypeNormalization.objectSatisfiesTypeConditionStack_cons_of_overlap_forValidity
          schema hobject hstack hoverlap
      have hheadNonempty :=
        selectionSetFilteredCompositeChildrenNonempty_head hnonempty
      have hbodyNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionFilteredCompositeChildrenNonempty] using hheadNonempty hoverlap
      have htailNonempty :=
        selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
      have htailNonemptyInBodyStack :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            (typeCondition :: typeConditions) rest :=
        selectionSetFilteredCompositeChildrenNonempty_of_stack_subset
          schema parentType
          (fun candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)
          rest htailNonempty
      have hbodyTailNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            (typeCondition :: typeConditions) (subselections ++ rest) :=
        selectionSetFilteredCompositeChildrenNonempty_append hbodyNonempty
          htailNonemptyInBodyStack
      simpa [normalizeSelectionSet, hoverlap]
        using happend (typeCondition :: typeConditions) hobject hstackBody
          (List.mem_cons_of_mem typeCondition hparent)
          hbodyTailReady hbodyTailSource hbodyTailReturnLookup
          hbodyTailMerge hbodyTailFree hbodyTailFeasible hbodyTailNonempty
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro typeConditions hobject hstack hparent hready hsource hreturnLookup
        hmerge hfree hfeasible hnonempty
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailSource :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have htailMerge :
          runtimeMergeSource schema parentType rest :=
        runtimeMergeSource_tail hmerge
      have htailFree :=
        selectionSetDirectiveFree_tail hfree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have htailNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions rest :=
        selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse]
        using hrest typeConditions hobject hstack hparent htailReady htailSource
          htailReturnLookup htailMerge htailFree htailFeasible
          htailNonempty

/-
Source witness for a field collected from a normalized Boolean-filtered branch.

This is the filtered analogue of the ground-type normalized field source data:
it connects a normalized field back to the raw filtered group that produced it,
then carries exactly the proof-internal invariants needed for recursive branch
merge validity. Those invariants replace a raw validity requirement for the
filtered syntax, which would be too strong under infeasible type-condition
stacks.
-/
theorem normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name) (selectionSet : List Selection)
    (boolCase : BoolCase)
    : schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> selectionSetDeclaredLookupReady schema parentType selectionSet
      -> selectionSetBoolTypeConditionFeasibleInCase schema parentType [parentType]
          boolCase selectionSet
      -> GroundTypeNormalization.NormalizedSelectionSetValid schema
          variableDefinitions parentType
          (normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase boolCase selectionSet)) := by
  intro hobject hready himplementation hmerge hdeclared hboolFeasible
  have hfilteredReady :
      selectionSetSemanticsReady schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
      parentType selectionSet hready
  have hfilteredSource :
      selectionSetFilteredCurrentSourceValid schema variableDefinitions
        parentType (filterSelectionSetBoolCase boolCase selectionSet) :=
    selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
      schema variableDefinitions hschema boolCase parentType hobject
      selectionSet himplementation
  have hfilteredReturnLookup :
      selectionSetFilteredReturnLookupValid schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) :=
    selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
      schema variableDefinitions hschema boolCase parentType hobject
      selectionSet himplementation
  have hfilteredMerge :
      FieldMerge.fieldsInSetCanMerge schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase schema boolCase hmerge
  have hfilteredRuntime :
      runtimeMergeSource schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) :=
    runtimeMergeSource_of_declaredLookupReady schema hobject
      (object_typeIncludesObjectBool_self schema hobject)
      (selectionSetDeclaredLookupReady_filter schema boolCase parentType selectionSet hdeclared)
      hfilteredMerge
  have hfilteredFree :
      selectionSetDirectiveFree
        (filterSelectionSetBoolCase boolCase selectionSet) :=
    filterSelectionSetBoolCase_directiveFree schema boolCase selectionSet
  have hfilteredFeasible :
      selectionSetTypeConditionFeasible schema parentType [parentType] (filterSelectionSetBoolCase boolCase selectionSet) :=
    selectionSetTypeConditionFeasible_filterSelectionSetBoolCase schema
      boolCase parentType [parentType] selectionSet hboolFeasible
  have hfilteredNonempty :
      selectionSetFilteredCompositeChildrenNonempty schema parentType
        [parentType] (filterSelectionSetBoolCase boolCase selectionSet) :=
    selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
      schema variableDefinitions hschema boolCase parentType [parentType]
      hobject selectionSet himplementation hboolFeasible
  exact normalizeSelectionSet_normalizedValid_of_filteredCurrentSource schema
    variableDefinitions hschema parentType
    (filterSelectionSetBoolCase boolCase selectionSet) [parentType] hobject
    (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject)
    (by simp) hfilteredReady hfilteredSource hfilteredReturnLookup hfilteredRuntime
    hfilteredFree hfilteredFeasible hfilteredNonempty

theorem completeNormalizeBranches_selectionSetValid_of_normalizedBranches
    (schema : Schema) (operation : Operation)
    (hoperation : Validation.operationDefinitionValid schema operation)
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases -> boolCase ∈ allBoolCases (operationBoolVars operation))
        -> (∀ boolCase,
              boolCase ∈ cases
              -> GroundTypeNormalization.NormalizedSelectionSetValid schema
                  operation.variableDefinitions (operation.rootType schema)
                  (normalizeSelectionSet schema (operation.rootType schema)
                    (filterSelectionSetBoolCase boolCase operation.selectionSet)))
        -> Validation.selectionSetValid schema operation.variableDefinitions
            (operation.rootType schema)
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema (operation.rootType schema)
                          (filterSelectionSetBoolCase boolCase
                            operation.selectionSet) with
                  | [] => []
                  | selection :: rest =>
                      wrapWithBoolCase boolCase (selection :: rest))))
  | [], _hcases, _hbranches => by
      simp [Validation.selectionSetValid]
  | boolCase :: restCases, hcases, hbranches => by
      have hcase :
          boolCase ∈ allBoolCases (operationBoolVars operation) :=
        hcases boolCase (by simp)
      have hrest :
          Validation.selectionSetValid schema operation.variableDefinitions
            (operation.rootType schema)
            (List.flatten (restCases.map (fun boolCase =>
              match normalizeSelectionSet schema (operation.rootType schema)
                  (filterSelectionSetBoolCase boolCase
                    operation.selectionSet) with
              | [] => []
              | selection :: rest =>
                  wrapWithBoolCase boolCase (selection :: rest)))) :=
        completeNormalizeBranches_selectionSetValid_of_normalizedBranches
          schema operation hoperation restCases
          (by
            intro candidate hcandidate
            exact hcases candidate (by simp [hcandidate]))
          (by
            intro candidate hcandidate
            exact hbranches candidate (by simp [hcandidate]))
      cases hnormalized :
          normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase boolCase
              operation.selectionSet) with
      | nil =>
          simpa [hnormalized] using hrest
      | cons selection normalizedRest =>
          have hbranchValid :
              GroundTypeNormalization.NormalizedSelectionSetValid schema
                operation.variableDefinitions (operation.rootType schema)
                (selection :: normalizedRest) := by
            simpa [hnormalized] using hbranches boolCase (by simp)
          have hvars :
              ∀ varName, varName ∈ boolCase.map Prod.fst ->
                varName ∈ operationBoolVars operation := by
            have hfst := boolCase_map_fst_of_mem_allBoolCases hcase
            intro varName hvar
            simpa [hfst] using hvar
          have hwrapped :
              Validation.selectionSetValid schema operation.variableDefinitions
                (operation.rootType schema)
                (wrapWithBoolCase boolCase
                  (selection :: normalizedRest)) :=
            wrapWithBoolCase_selectionSetValid schema operation
              (operation.rootType schema) boolCase (selection :: normalizedRest)
              hoperation hvars (by simp) hbranchValid.selectionSetValid
          simpa [hnormalized] using
            Validation.selectionSetValid_append hwrapped hrest

theorem completeNormalizeBranches_selectionSetValid
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hrootObject : schema.objectType (operation.rootType schema))
    (hready
      : selectionSetSemanticsReady schema (operation.rootType schema)
          operation.selectionSet)
    (himplementation
      : Validation.selectionSetValidInPossibleTypes schema operation.variableDefinitions
          (operation.rootType schema) operation.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
          operation.selectionSet)
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases -> boolCase ∈ allBoolCases (operationBoolVars operation))
        -> (∀ boolCase,
              boolCase ∈ cases
              -> selectionSetBoolTypeConditionFeasibleInCase schema
                  (operation.rootType schema) [(operation.rootType schema)] boolCase
                  operation.selectionSet)
        -> Validation.selectionSetValid schema operation.variableDefinitions
            (operation.rootType schema)
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema (operation.rootType schema)
                          (filterSelectionSetBoolCase boolCase
                            operation.selectionSet) with
                  | [] => []
                  | selection :: rest =>
                      wrapWithBoolCase boolCase (selection :: rest))))
  | cases, hcases, hboolFeasibleCases =>
      completeNormalizeBranches_selectionSetValid_of_normalizedBranches
        schema operation hoperation cases hcases
        (by
          intro boolCase hcase
          exact normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
            schema operation.variableDefinitions hschema
            (operation.rootType schema) operation.selectionSet boolCase
            hrootObject hready
            himplementation hmerge
            (selectionSetDeclaredLookupReady_of_valid schema operation.variableDefinitions
              (operation.rootType schema) operation.selectionSet
              (Validation.operationDefinitionValid_selectionSetValid hoperation))
            (hboolFeasibleCases boolCase hcase))

theorem completeNormalizeBranches_validInPossibleTypes_of_normalizedBranches
    (schema : Schema) (operation : Operation)
    (hrootObject : schema.objectType (operation.rootType schema))
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases
          -> GroundTypeNormalization.NormalizedSelectionSetValid schema
              operation.variableDefinitions (operation.rootType schema)
              (normalizeSelectionSet schema (operation.rootType schema)
                (filterSelectionSetBoolCase boolCase operation.selectionSet)))
        -> Validation.selectionSetValidInPossibleTypes schema
            operation.variableDefinitions (operation.rootType schema)
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema (operation.rootType schema)
                          (filterSelectionSetBoolCase boolCase
                            operation.selectionSet) with
                  | [] => []
                  | selection :: rest =>
                      wrapWithBoolCase boolCase (selection :: rest))))
  | [], _hbranches => by
      simp [Validation.selectionSetValidInPossibleTypes]
  | boolCase :: restCases, hbranches => by
      have hrest :
          Validation.selectionSetValidInPossibleTypes schema
            operation.variableDefinitions (operation.rootType schema)
            (List.flatten (restCases.map (fun boolCase =>
              match normalizeSelectionSet schema (operation.rootType schema)
                  (filterSelectionSetBoolCase boolCase
                    operation.selectionSet) with
              | [] => []
              | selection :: rest =>
                  wrapWithBoolCase boolCase (selection :: rest)))) :=
        completeNormalizeBranches_validInPossibleTypes_of_normalizedBranches
          schema operation hrootObject restCases
          (by
            intro candidate hcandidate
            exact hbranches candidate (by simp [hcandidate]))
      cases hnormalized :
          normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase boolCase
              operation.selectionSet) with
      | nil =>
          simpa [hnormalized] using hrest
      | cons selection normalizedRest =>
          have hbranchValid :
              GroundTypeNormalization.NormalizedSelectionSetValid schema
                operation.variableDefinitions (operation.rootType schema)
                (selection :: normalizedRest) := by
            simpa [hnormalized] using hbranches boolCase (by simp)
          have hwrapped :
              Validation.selectionSetValidInPossibleTypes schema
                operation.variableDefinitions (operation.rootType schema)
                (wrapWithBoolCase boolCase
                  (selection :: normalizedRest)) :=
            wrapWithBoolCase_selectionSetValidInPossibleTypes schema
              operation.variableDefinitions (operation.rootType schema) hrootObject boolCase
              (selection :: normalizedRest) hbranchValid.validInPossibleTypes
          simpa [hnormalized] using
            GroundTypeNormalization.selectionSetValidInPossibleTypes_append
              hwrapped hrest

theorem completeNormalizeBranches_validInPossibleTypes
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrootObject : schema.objectType (operation.rootType schema))
    (hready
      : selectionSetSemanticsReady schema (operation.rootType schema)
          operation.selectionSet)
    (himplementation
      : Validation.selectionSetValidInPossibleTypes schema operation.variableDefinitions
          (operation.rootType schema) operation.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
          operation.selectionSet)
    (hdeclared
      : selectionSetDeclaredLookupReady schema (operation.rootType schema)
          operation.selectionSet)
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases
          -> selectionSetBoolTypeConditionFeasibleInCase schema
              (operation.rootType schema) [(operation.rootType schema)] boolCase
              operation.selectionSet)
        -> Validation.selectionSetValidInPossibleTypes schema
            operation.variableDefinitions (operation.rootType schema)
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema (operation.rootType schema)
                          (filterSelectionSetBoolCase boolCase
                            operation.selectionSet) with
                  | [] => []
                  | selection :: rest =>
                      wrapWithBoolCase boolCase (selection :: rest))))
  | cases, hboolFeasibleCases =>
      completeNormalizeBranches_validInPossibleTypes_of_normalizedBranches
        schema operation hrootObject cases
        (by
          intro boolCase hcase
          exact normalizeSelectionSet_filterSelectionSetBoolCase_normalizedValid
            schema operation.variableDefinitions hschema
            (operation.rootType schema) operation.selectionSet boolCase
            hrootObject hready
            himplementation hmerge hdeclared
            (hboolFeasibleCases boolCase hcase))

end CompleteNormalization

end NormalForm

end GraphQL
