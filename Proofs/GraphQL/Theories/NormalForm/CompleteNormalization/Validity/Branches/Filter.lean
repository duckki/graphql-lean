import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Sources

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
                      simpa [selectionValidInCurrentScope] using
                        ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType rfl hhead
                  | some typeCondition =>
                      simpa [selectionValidInCurrentScope] using
                        (fun hoverlap =>
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
  exact ⟨hcleared, by
    simpa [Validation.selectionValidInPossibleTypes, hlookup] using hvalid.2⟩

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
                    exact ⟨⟨hparts.1,
                      by
                        intro hoverlap
                        exact ih (SelectionSet.size selectionSet) hchildSize
                          selectionSet parentType rfl (hparts.2 hoverlap)⟩,
                      ih (SelectionSet.size rest) hrestSize rest parentType
                        rfl htail⟩
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
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
                    exact ⟨(by
                      intro hoverlap
                      exact ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType rfl (hhead hoverlap)),
                      ih (SelectionSet.size rest) hrestSize rest parentType
                        rfl htail⟩
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
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
      fieldSelectionsWithResponseNameInScope_matching_field_shape_of_canMerge_object_lookupValid
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
                    exact ⟨(by
                      intro hoverlap
                      exact ih (SelectionSet.size selectionSet) hchildSize
                        selectionSet parentType (typeCondition :: typeConditions)
                        rfl (hhead hoverlap)),
                      ih (SelectionSet.size rest) hrestSize rest parentType
                        typeConditions rfl htail⟩
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
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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
    fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
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
      -> FieldMerge.fieldsInSetCanMerge schema parentType
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

theorem collectFields_filterSelectionSetBoolCase_mem_source
    (schema : Schema) (boolCase : BoolCase)
    : ∀ parentType selectionSet filteredField,
        filteredField
          ∈ FieldMerge.collectFields schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
        -> ∃ sourceField,
            sourceField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ BoolFilteredScopedFieldSource schema boolCase sourceField filteredField
  | _parentType, [], _filteredField, hfield => by
      simp [filterSelectionSetBoolCase, FieldMerge.collectFields] at hfield
  | parentType,
    Selection.field responseName fieldName arguments directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow,
              FieldMerge.collectFields] at hfield
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [hlookup] at hfield
                rcases
                  collectFields_filterSelectionSetBoolCase_mem_source schema
                    boolCase parentType rest filteredField hfield with
                  ⟨sourceField, hsourceMem, hsource⟩
                exact ⟨sourceField, by
                  simp [FieldMerge.collectFields, hlookup, hsourceMem],
                  hsource⟩
            | some fieldDefinition =>
                simp [hlookup] at hfield
                rcases hfield with hhead | htail
                · subst filteredField
                  refine ⟨{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    outputType := fieldDefinition.outputType,
                    selectionSet := []
                  }, ?_, ?_⟩
                  · simp [FieldMerge.collectFields, hlookup]
                  · exact ⟨rfl, rfl, rfl, rfl, rfl, by
                      simp [filterSelectionSetBoolCase]⟩
                · rcases
                    collectFields_filterSelectionSetBoolCase_mem_source schema
                      boolCase parentType rest filteredField htail with
                    ⟨sourceField, hsourceMem, hsource⟩
                  exact ⟨sourceField, by
                    simp [FieldMerge.collectFields, hlookup, hsourceMem],
                    hsource⟩
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase
                  (child :: children) with
            | nil =>
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source schema
                        boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
            | cons filteredChild filteredChildren =>
                simp [filterSelectionSetBoolCase, hallow, hchild,
                  FieldMerge.collectFields] at hfield
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source
                        schema boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          cases hlookup : schema.lookupField parentType fieldName
          <;> simp [FieldMerge.collectFields, hlookup, hsourceMem],
          hsource⟩
  | parentType,
    Selection.inlineFragment none directives selectionSet :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source schema
                boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase parentType selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩
  | parentType,
    Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source schema
                boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase typeCondition selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source schema
                  boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩

theorem collectFields_normalize_filterSelectionSetBoolCase_mem_source
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (boolCase : BoolCase)
    : ∀ parentType selectionSet normalizedField,
        schema.objectType parentType
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> normalizedField
            ∈ FieldMerge.collectFields schema parentType
                (normalizeSelectionSet schema parentType
                  (filterSelectionSetBoolCase boolCase selectionSet))
        -> ∃ sourceField,
            sourceField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ GroundTypeNormalization.NormalizedFieldSource schema sourceField
                normalizedField := by
  intro parentType selectionSet normalizedField hobject hready hmem
  have hfilteredReady :
      selectionSetSemanticsReady schema parentType
        (filterSelectionSetBoolCase boolCase selectionSet) :=
    selectionSetSemanticsReady_filterSelectionSetBoolCase schema boolCase
      parentType selectionSet hready
  rcases
    GroundTypeNormalization.collectFields_normalizeSelectionSet_mem_source
      schema hschema parentType
      (filterSelectionSetBoolCase boolCase selectionSet) normalizedField
      hobject hfilteredReady hmem with
  ⟨filteredField, hfilteredMem, hnormalized⟩
  rcases
    collectFields_filterSelectionSetBoolCase_mem_source schema boolCase
      parentType selectionSet filteredField hfilteredMem with
  ⟨sourceField, hsourceMem, hfilteredSource⟩
  exact ⟨sourceField, hsourceMem,
    normalizedFieldSource_of_boolFiltered hfilteredSource hnormalized⟩

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase
    (schema : Schema) (boolCase : BoolCase)
    {parentType : Name} {selectionSet : List Selection}
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet) := by
  intro hmerge
  refine
    FieldMerge.FieldsInSetCanMerge.rec
      (motive_1 := fun parentType selectionSet _hmerge =>
        FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet))
      (motive_2 := fun sourceLeft sourceRight _hmerge =>
        ∀ left right,
          BoolFilteredScopedFieldSource schema boolCase sourceLeft left ->
          BoolFilteredScopedFieldSource schema boolCase sourceRight right ->
          left.responseName = right.responseName ->
            FieldMerge.fieldsForNameCanMerge schema left right)
      ?setCase ?fieldCase hmerge
  · intro parentType selectionSet hfields ihfields
    unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      (filterSelectionSetBoolCase boolCase selectionSet) ?_
    dsimp
    intro left hleft right hright hresponse
    rcases
      collectFields_filterSelectionSetBoolCase_mem_source schema
        boolCase parentType selectionSet left hleft with
      ⟨sourceLeft, hsourceLeft, hleftSource⟩
    rcases
      collectFields_filterSelectionSetBoolCase_mem_source schema
        boolCase parentType selectionSet right hright with
      ⟨sourceRight, hsourceRight, hrightSource⟩
    have hsourceResponse :
        sourceLeft.responseName = sourceRight.responseName :=
      hleftSource.responseName.symm.trans
        (hresponse.trans hrightSource.responseName)
    exact ihfields sourceLeft hsourceLeft sourceRight hsourceRight
      hsourceResponse left right hleftSource hrightSource hresponse
  · intro sourceLeft sourceRight hshape hidentity hsubfields ihsubfields
      left right hleftSource hrightSource _hresponse
    refine FieldMerge.FieldsForNameCanMerge.intro left right ?_ ?_ ?_
    · simpa [hleftSource.outputType, hrightSource.outputType] using
        hshape
    · intro hparents
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      rcases hidentity hsourceParents with ⟨hfieldName, harguments⟩
      exact ⟨hleftSource.fieldName.trans
          (hfieldName.trans hrightSource.fieldName.symm),
        by
          simpa [hleftSource.arguments, hrightSource.arguments]
            using harguments⟩
    · intro hparents objectType
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      have hfilteredSubfields :
          FieldMerge.fieldsInSetCanMerge schema objectType
            (filterSelectionSetBoolCase boolCase
              (sourceLeft.selectionSet ++ sourceRight.selectionSet)) :=
        ihsubfields hsourceParents objectType
      rw [filterSelectionSetBoolCase_append] at hfilteredSubfields
      simpa [FieldMerge.fieldsInSetCanMerge, hleftSource.selectionSet,
        hrightSource.selectionSet]
        using hfilteredSubfields

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase_pair
    (schema : Schema)
    {parentType : Name} {leftSet rightSet : List Selection}
    (leftCase rightCase : BoolCase)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase leftCase leftSet
            ++ filterSelectionSetBoolCase rightCase rightSet) := by
  intro hmerge
  refine
    FieldMerge.FieldsInSetCanMerge.rec
      (motive_1 := fun parentType selectionSet _hmerge =>
        ∀ leftSet rightSet,
          selectionSet = leftSet ++ rightSet ->
          ∀ leftCase rightCase,
            FieldMerge.fieldsInSetCanMerge schema parentType
              (filterSelectionSetBoolCase leftCase leftSet
                ++ filterSelectionSetBoolCase rightCase rightSet))
      (motive_2 := fun sourceLeft sourceRight _hmerge =>
        ∀ leftCase rightCase left right,
          BoolFilteredScopedFieldSource schema leftCase sourceLeft left ->
          BoolFilteredScopedFieldSource schema rightCase sourceRight right ->
          left.responseName = right.responseName ->
            FieldMerge.fieldsForNameCanMerge schema left right)
      ?setCase ?fieldCase hmerge leftSet rightSet rfl leftCase rightCase
  · intro parentType selectionSet hfields ihfields leftSet rightSet
      hsplit leftCase rightCase
    unfold FieldMerge.fieldsInSetCanMerge
    refine FieldMerge.FieldsInSetCanMerge.intro parentType
      (filterSelectionSetBoolCase leftCase leftSet
        ++ filterSelectionSetBoolCase rightCase rightSet) ?_
    dsimp
    intro left hleft right hright hresponse
    rw [FieldMerge.collectFields_append] at hleft hright
    rcases List.mem_append.mp hleft with hleftInLeft | hleftInRight
    · rcases
        collectFields_filterSelectionSetBoolCase_mem_source schema
          leftCase parentType leftSet left hleftInLeft with
        ⟨sourceLeft, hsourceLeftMem, hleftSource⟩
      have hsourceLeftAll :
          sourceLeft ∈ FieldMerge.collectFields schema parentType
            selectionSet := by
        rw [hsplit, FieldMerge.collectFields_append]
        exact List.mem_append_left
          (FieldMerge.collectFields schema parentType rightSet)
          hsourceLeftMem
      rcases List.mem_append.mp hright with hrightInLeft | hrightInRight
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            leftCase parentType leftSet right hrightInLeft with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_left
            (FieldMerge.collectFields schema parentType rightSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse leftCase leftCase left right
          hleftSource hrightSource hresponse
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            rightCase parentType rightSet right hrightInRight with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_right
            (FieldMerge.collectFields schema parentType leftSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse leftCase rightCase left right
          hleftSource hrightSource hresponse
    · rcases
        collectFields_filterSelectionSetBoolCase_mem_source schema
          rightCase parentType rightSet left hleftInRight with
        ⟨sourceLeft, hsourceLeftMem, hleftSource⟩
      have hsourceLeftAll :
          sourceLeft ∈ FieldMerge.collectFields schema parentType
            selectionSet := by
        rw [hsplit, FieldMerge.collectFields_append]
        exact List.mem_append_right
          (FieldMerge.collectFields schema parentType leftSet)
          hsourceLeftMem
      rcases List.mem_append.mp hright with hrightInLeft | hrightInRight
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            leftCase parentType leftSet right hrightInLeft with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_left
            (FieldMerge.collectFields schema parentType rightSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse rightCase leftCase left right
          hleftSource hrightSource hresponse
      · rcases
          collectFields_filterSelectionSetBoolCase_mem_source schema
            rightCase parentType rightSet right hrightInRight with
          ⟨sourceRight, hsourceRightMem, hrightSource⟩
        have hsourceRightAll :
            sourceRight ∈ FieldMerge.collectFields schema parentType
              selectionSet := by
          rw [hsplit, FieldMerge.collectFields_append]
          exact List.mem_append_right
            (FieldMerge.collectFields schema parentType leftSet)
            hsourceRightMem
        have hsourceResponse :
            sourceLeft.responseName = sourceRight.responseName :=
          hleftSource.responseName.symm.trans
            (hresponse.trans hrightSource.responseName)
        exact ihfields sourceLeft hsourceLeftAll sourceRight
          hsourceRightAll hsourceResponse rightCase rightCase left right
          hleftSource hrightSource hresponse
  · intro sourceLeft sourceRight hshape hidentity hsubfields ihsubfields
      leftCase rightCase left right hleftSource hrightSource _hresponse
    refine FieldMerge.FieldsForNameCanMerge.intro left right ?_ ?_ ?_
    · simpa [hleftSource.outputType, hrightSource.outputType] using
        hshape
    · intro hparents
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      rcases hidentity hsourceParents with ⟨hfieldName, harguments⟩
      exact ⟨hleftSource.fieldName.trans
          (hfieldName.trans hrightSource.fieldName.symm),
        by
          simpa [hleftSource.arguments, hrightSource.arguments]
            using harguments⟩
    · intro hparents objectType
      have hsourceParents :
          sourceLeft.parentType = sourceRight.parentType
            ∨ ¬ schema.objectType sourceLeft.parentType
            ∨ ¬ schema.objectType sourceRight.parentType := by
        rcases hparents with hparentEq | hnotObject
        · exact Or.inl
            (hleftSource.parentType.symm.trans
              (hparentEq.trans hrightSource.parentType))
        · rcases hnotObject with hleftNotObject | hrightNotObject
          · exact Or.inr (Or.inl (by
              intro hsourceObject
              exact hleftNotObject
                (by simpa [hleftSource.parentType] using hsourceObject)))
          · exact Or.inr (Or.inr (by
              intro hsourceObject
              exact hrightNotObject
                (by simpa [hrightSource.parentType] using hsourceObject)))
      have hfilteredSubfields :
          FieldMerge.fieldsInSetCanMerge schema objectType
            (filterSelectionSetBoolCase leftCase sourceLeft.selectionSet
              ++ filterSelectionSetBoolCase rightCase
                sourceRight.selectionSet) :=
        ihsubfields hsourceParents objectType sourceLeft.selectionSet
          sourceRight.selectionSet rfl leftCase rightCase
      simpa [FieldMerge.fieldsInSetCanMerge, hleftSource.selectionSet,
        hrightSource.selectionSet]
        using hfilteredSubfields

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
            exact Or.inr ⟨.field responseName fieldName arguments [] [],
              by simp [filterSelectionSetBoolCase, hallow]⟩
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase
                  (child :: children) with
            | nil =>
                exact Or.inr
                  ⟨.field responseName fieldName arguments [] [], by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨.field responseName fieldName arguments []
                    (filteredChild :: filteredChildren), by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
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
          · cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                exact Or.inl (by
                  simp [filterSelectionSetBoolCase, hallow, hchild])
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨.inlineFragment none []
                    (filteredChild :: filteredChildren), by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
          · have hfalse :
                directivesAllowIn boolCase directives = false := by
              cases hmatch : directivesAllowIn boolCase directives
              · rfl
              · contradiction
            exact Or.inl (by simp [filterSelectionSetBoolCase, hfalse])
      | some typeCondition =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                exact Or.inl (by
                  simp [filterSelectionSetBoolCase, hallow, hchild])
            | cons filteredChild filteredChildren =>
                exact Or.inr
                  ⟨.inlineFragment (some typeCondition) []
                    (filteredChild :: filteredChildren), by
                    simp [filterSelectionSetBoolCase, hallow, hchild]⟩
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
      exact ⟨boolCase, hparts.1,
        by simpa [selectionAllowsIn] using hparts.2⟩
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
              simpa [selectionSetBoolTypeConditionFeasibleInCase] using
                hfeasible.1
            have htail :
                selectionSetBoolTypeConditionFeasibleInCase schema parentType
                  typeConditions boolCase rest := by
              simpa [selectionSetBoolTypeConditionFeasibleInCase] using
                hfeasible.2
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
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
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
      simpa [normalizeSelectionSet] using
        GroundTypeNormalization.normalizedSelectionSetValid_nil schema
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
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest hmerge
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
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
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
      simpa [normalizeSelectionSet, hlookup] using
        hrest typeConditions hobject hstack hparent hfilteredReady hfilteredSource
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
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments []
            subselections)
          rest hmerge
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
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
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
            fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
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
            simpa [returnType] using
              object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
          simpa [hreturnObject] using
            hmerged [returnType] hreturnObjectType
              (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hreturnObjectType)
              (by simp)
              hchildReady
              (hchildSource returnType
                (by
                  simpa [returnType] using
                    (List.contains_iff_mem.mp
                      (object_typeIncludesObjectBool_self schema
                        hreturnObjectType))))
              (hchildReturnLookup returnType
                (by
                  simpa [returnType] using
                    (List.contains_iff_mem.mp
                      (object_typeIncludesObjectBool_self schema
                        hreturnObjectType))))
              (fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName returnType arguments
                subselections rest fieldDefinition hobject hlookupValid hmerge
                hlookup)
              hmergedFree
              (hmergedFeasible returnType
                (by
                  simpa [returnType] using
                    (List.contains_iff_mem.mp
                      (object_typeIncludesObjectBool_self schema
                        hreturnObjectType))))
              (hchildNonempty returnType
                (by
                  simpa [returnType] using
                    (List.contains_iff_mem.mp
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
              selectionSetSemanticsReady_fieldHead_merged_of_child_object
                schema parentType responseName fieldName objectType arguments
                subselections rest fieldDefinition hobject hready hlookupValid
                hmerge hlookup (by simpa [returnType] using hinclude)
            exact hpossible objectType [objectType] hobjectBranch
              (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hobjectBranch)
              (by simp)
              hchildReady
              (hchildSource objectType hobjectType)
              (hchildReturnLookup objectType hobjectType)
              (fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName objectType arguments
                subselections rest fieldDefinition hobject hlookupValid hmerge
                hlookup)
              hmergedFree
              (hmergedFeasible objectType hobjectType)
              (hchildNonempty objectType hobjectType)
          · have hreturnLookup :
                selectionSetLookupValid schema returnType
                  mergedSubselections := by
              subst mergedSubselections
              simpa [returnType] using
                selectionSetLookupValid_fieldHead_merged_of_filteredReturnLookup
                  schema parentType responseName fieldName returnType arguments
                  subselections rest fieldDefinition hobject hlookupValid
                  hreturnLookup hmerge hlookup rfl
            have hreadyBranches :
                ∀ objectType,
                  objectType ∈ schema.getPossibleTypes returnType ->
                    selectionSetSemanticsReady schema objectType
                      mergedSubselections := by
              intro objectType hobjectType
              have hinclude :
                  schema.typeIncludesObjectBool
                    fieldDefinition.outputType.namedType objectType = true :=
                List.contains_iff_mem.mpr
                  (by simpa [returnType] using hobjectType)
              exact
                selectionSetSemanticsReady_fieldHead_merged_of_child_object
                  schema parentType responseName fieldName objectType arguments
                  subselections rest fieldDefinition hobject hready
                  hlookupValid hmerge hlookup
                  (by simpa [returnType] using hinclude)
            have hmergeReturn :
                FieldMerge.fieldsInSetCanMerge schema returnType
                  mergedSubselections := by
              subst mergedSubselections
              exact
                fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                  schema parentType responseName fieldName returnType arguments
                  subselections rest fieldDefinition hobject hlookupValid hmerge
                  hlookup
            exact
              GroundTypeNormalization.normalizedDistinctBranchesPairwiseMerge_of_abstractMerge
                schema variableDefinitions hschema returnType
                (schema.getPossibleTypes returnType) mergedSubselections
                (by
                  intro objectType hobjectType
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hobjectType)
                (by
                  intro objectType hobjectType
                  exact hobjectType)
                hreturnLookup hreadyBranches hmergeReturn
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
          simpa [hreturnObject] using
            hnormalizedSubselectionsValid.validInPossibleTypes
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
              selectionSetSemanticsReady_fieldHead_merged_of_child_object
                schema parentType responseName fieldName branchType arguments
                subselections rest fieldDefinition hobject hready
                hlookupValid hmerge hlookup
                (by simpa [returnType] using hinclude)
            have hchildMerge :
                FieldMerge.fieldsInSetCanMerge schema branchType
                  mergedSubselections :=
              fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName branchType arguments
                subselections rest fieldDefinition hobject hlookupValid hmerge
                hlookup
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
        exact
          (hheadNonempty hstackFeasible).1 fieldDefinition hlookup hcomposite
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
              exact ⟨objectType, by simpa [returnType] using hobjectType,
                (hchildren.2 objectType hobjectType).1⟩
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
            simpa [returnType] using
              object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName returnType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
          simpa [hreturnObject] using
            normalizeSelectionSet_ne_nil_of_contains schema
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
            selectionSetSemanticsReady_fieldHead_merged_of_child_object
              schema parentType responseName fieldName childObjectType arguments
              subselections rest fieldDefinition hobject hready hlookupValid
              hmerge hlookup (by simpa [returnType] using hinclude)
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
          · exact FieldMerge.sameResponseShape_refl schema
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
        simpa [normalizedFieldWithRest, normalizedField] using
          hconsNormalizedValid hnormalizedSubselectionsNonempty
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
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType
          subselections rest hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
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
      simpa [normalizeSelectionSet] using
        happend typeConditions hobject hstack hparent hbodyTailReady
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
        simpa [selectionFilteredCurrentSourceValid] using
          hheadSource.2 hoverlap
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
        simpa [selectionFilteredReturnLookupValid] using
          hheadReturnLookup hoverlap
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
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
          schema parentType typeCondition subselections rest hschema hobject
          hoverlap hlookupBodyParent hlookupBodyType hlookupRest hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have htailFeasibleInBodyStack :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) rest :=
        by
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
        simpa [selectionFilteredCompositeChildrenNonempty] using
          hheadNonempty hoverlap
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
      simpa [normalizeSelectionSet, hoverlap] using
        happend (typeCondition :: typeConditions) hobject hstackBody
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
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) directives
            subselections)
          rest hmerge
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
      simpa [normalizeSelectionSet, hfalse] using
        hrest typeConditions hobject hstack hparent htailReady htailSource
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
structure FilteredNormalizedFieldGroupSource
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (normalized : FieldMerge.ScopedField) where
  source : FieldMerge.ScopedField
  sourceMem : source ∈ FieldMerge.collectFields schema parentType selectionSet
  sourceRel : GroundTypeNormalization.NormalizedFieldSource schema source normalized
  group : List Selection
  childSource : List Selection
  childSource_eq : childSource = mergeSelectionSets group
  childSource_size_lt : SelectionSet.size childSource < SelectionSet.size selectionSet
  childReady
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> selectionSetSemanticsReady schema runtimeType childSource
  childLookup : selectionSetLookupValid schema normalized.outputType.namedType childSource
  childCurrentSource
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            runtimeType childSource
  childReturnLookup
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> selectionSetFilteredReturnLookupValid schema runtimeType childSource
  childFeasible
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> selectionSetTypeConditionFeasible schema runtimeType [runtimeType] childSource
  childNonempty
    : ∀ runtimeType,
        runtimeType ∈ schema.getPossibleTypes normalized.outputType.namedType
        -> selectionSetFilteredCompositeChildrenNonempty schema runtimeType
            [runtimeType] childSource
  childDirectiveFree : selectionSetDirectiveFree childSource
  groupScoped
    : ∀ selection,
        selection ∈ group
        -> ∃ scopedField,
            scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ scopedField.responseName = normalized.responseName
            ∧ scopedField.selectionSet = selection.subselections
            ∧ (schema.objectType scopedField.parentType
                -> schema.typesOverlapBool parentType scopedField.parentType = true)
  normalizedSelectionSet
    : normalized.selectionSet
      = if objectTypeNameBool schema normalized.outputType.namedType then
          normalizeSelectionSet schema normalized.outputType.namedType childSource
        else
          GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes normalized.outputType.namedType)
            childSource

def filteredNormalizedFieldGroupSource_fieldHead
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema -> schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> selectionSetLookupValid schema parentType rest
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> selectionSetFilteredReturnLookupValid schema parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> selectionSetDirectiveFree
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> objectSatisfiesTypeConditionStack schema parentType typeConditions
      -> selectionSetTypeConditionFeasible schema parentType typeConditions
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          typeConditions
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
          {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := fieldDefinition.outputType,
            selectionSet :=
              if objectTypeNameBool schema fieldDefinition.outputType.namedType then
                normalizeSelectionSet schema fieldDefinition.outputType.namedType
                  (subselections
                    ++ mergeSelectionSets
                        (fieldSelectionsWithResponseNameInScope schema parentType
                          responseName rest))
              else
                GroundTypeNormalization.possibleTypeNormalizations schema
                  (schema.getPossibleTypes fieldDefinition.outputType.namedType)
                  (subselections
                    ++ mergeSelectionSets
                        (fieldSelectionsWithResponseNameInScope schema parentType
                          responseName rest))
          } := by
  intro hschema hobject hready htailLookup hlookupValid hsource
    hreturnLookup hmerge hfree hstack hfeasible hnonempty hlookup
  have hselectionFree := selectionSetDirectiveFree_head hfree
  have hdirectives : directives = [] := hselectionFree.1
  subst directives
  let headSelection : Selection :=
    Selection.field responseName fieldName arguments [] subselections
  let group : List Selection :=
    headSelection :: fieldSelectionsWithResponseNameInScope schema parentType
      responseName rest
  let childSource : List Selection := mergeSelectionSets group
  let sourceField : FieldMerge.ScopedField := {
    parentType := parentType,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := subselections
  }
  refine ⟨sourceField, ?_, ?_, group, childSource, rfl, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sourceField, FieldMerge.collectFields, hlookup]
  · refine ⟨rfl, rfl, rfl, ?_, Or.inl rfl⟩
    exact FieldMerge.sameResponseShape_refl schema
      fieldDefinition.outputType
      (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
        hschema hlookup)
  · have hmatchingSize :
        SelectionSet.size
            (mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest))
          ≤ SelectionSet.size rest :=
      size_mergeSelectionSets_fieldSelectionsWithResponseNameInScope_le_for_filterValidity
        schema parentType responseName rest
    simp [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections, selectionSet_size_append_for_filterValidity,
      SelectionSet.size, Selection.size]
    omega
  · intro runtimeType hpossible
    have hinclude :
        schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
          runtimeType = true :=
      List.contains_iff_mem.mpr hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetSemanticsReady_fieldHead_merged_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition hobject hready hlookupValid hmerge
        hlookup hinclude
  · simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetLookupValid_fieldHead_merged_of_filteredReturnLookup
        schema parentType responseName fieldName
        fieldDefinition.outputType.namedType arguments subselections rest
        fieldDefinition hobject hlookupValid hreturnLookup hmerge hlookup rfl
  · intro runtimeType hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetFilteredCurrentSourceValid_fieldHead_merged_of_child_object
        schema variableDefinitions parentType responseName fieldName
        runtimeType arguments subselections rest fieldDefinition hobject
        hlookupValid hsource hmerge hlookup hpossible
  · intro runtimeType hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetFilteredReturnLookupValid_fieldHead_merged_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition hobject hlookupValid hreturnLookup
        hmerge hlookup hpossible
  · intro runtimeType hpossible
    have hheadFeasible :
        selectionTypeConditionFeasible schema parentType typeConditions
          (Selection.field responseName fieldName arguments [] subselections) := by
      simpa [selectionSetTypeConditionFeasible] using hfeasible.1
    have htailFeasible :
        selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
      selectionSetTypeConditionFeasible_tail hfeasible
    have hheadChildFeasible :
        selectionSetTypeConditionFeasible schema runtimeType [runtimeType]
          subselections :=
      selectionTypeConditionFeasible_field_child_branch_forObject
        schema hheadFeasible hstack hlookup hpossible
    have hmatchingChildFeasible :
        selectionSetTypeConditionFeasible schema runtimeType [runtimeType]
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              rest)) := by
      apply
        selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
      intro matchedFieldName matchedArguments matchedDirectives
        matchedSubselections hmatched
      have hsame :
          matchedFieldName = fieldName :=
        fieldSelectionsWithResponseNameInScope_matching_same_field_of_canMerge_object_lookupValid
          schema parentType responseName fieldName arguments subselections
          rest hobject hlookupValid hmerge matchedFieldName
          matchedArguments matchedDirectives matchedSubselections hmatched
      subst matchedFieldName
      exact
        fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
          schema parentType responseName hobject hstack rest htailFeasible
          fieldName matchedArguments matchedDirectives matchedSubselections
          fieldDefinition runtimeType hmatched hlookup hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetTypeConditionFeasible_append hheadChildFeasible
        hmatchingChildFeasible
  · intro runtimeType hpossible
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetFilteredCompositeChildrenNonempty_fieldHead_merged_of_child_object
        schema parentType responseName fieldName runtimeType arguments
        subselections rest fieldDefinition typeConditions hobject hstack
        hlookupValid hnonempty hmerge hlookup hpossible
  · have htailFree := selectionSetDirectiveFree_tail hfree
    have hsubselectionsFree : selectionSetDirectiveFree subselections :=
      hselectionFree.2
    have hmatchingFree :
        selectionSetDirectiveFree
          (fieldSelectionsWithResponseNameInScope schema parentType responseName rest) :=
      fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
        responseName rest htailFree
    simpa [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections] using
      selectionSetDirectiveFree_append hsubselectionsFree
        (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
  · intro selection hselection
    rcases List.mem_cons.mp hselection with hhead | hmatched
    · subst selection
      refine ⟨sourceField, ?_, rfl, ?_, ?_⟩
      · simp [sourceField, FieldMerge.collectFields, hlookup]
      · simp [sourceField, headSelection, Selection.subselections]
      · intro _hscopedObject
        simp [sourceField]
        exact object_typesOverlapBool_self schema hobject
    · rcases
        fieldSelectionsWithResponseNameInScope_mem_field schema parentType
          responseName rest selection hmatched with
      ⟨matchedFieldName, matchedArguments, matchedDirectives,
        matchedSubselections, hselectionEq⟩
      subst selection
      have hoverlapSelf :
          schema.objectType parentType ->
            schema.typesOverlapBool parentType parentType = true := by
        intro hparentObject
        exact object_typesOverlapBool_self schema hparentObject
      rcases
        fieldSelectionsWithResponseNameInScope_field_mem_collectFields_scoped_lookupValid
          schema parentType parentType responseName rest matchedFieldName
          matchedArguments matchedDirectives matchedSubselections
          hoverlapSelf htailLookup hmatched with
      ⟨scopedField, hscopedRest, hresponse, _hfieldName, _harguments,
        hselectionSet, hoverlap⟩
      refine ⟨scopedField, ?_, hresponse, ?_, hoverlap⟩
      · exact fieldMerge_collectFields_tail_mem schema parentType
          headSelection rest scopedField hscopedRest
      · simpa [Selection.subselections] using hselectionSet
  · simp [childSource, group, headSelection, mergeSelectionSets,
      Selection.subselections]

def FilteredNormalizedFieldGroupSource.mapCollectFields
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name}
    {sourceSet targetSet : List Selection}
    {normalized : FieldMerge.ScopedField}
    (hgroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          sourceSet normalized)
    (hmap
      : ∀ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType sourceSet
          -> scopedField ∈ FieldMerge.collectFields schema parentType targetSet)
    (hsize : SelectionSet.size sourceSet ≤ SelectionSet.size targetSet)
    : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
        targetSet normalized := by
  refine ⟨hgroup.source, hmap hgroup.source hgroup.sourceMem,
    hgroup.sourceRel, hgroup.group, hgroup.childSource,
    hgroup.childSource_eq,
    Nat.lt_of_lt_of_le hgroup.childSource_size_lt hsize,
    hgroup.childReady, hgroup.childLookup, hgroup.childCurrentSource,
    hgroup.childReturnLookup, hgroup.childFeasible, hgroup.childNonempty,
    hgroup.childDirectiveFree, ?_, hgroup.normalizedSelectionSet⟩
  intro selection hselection
  rcases hgroup.groupScoped selection hselection with
    ⟨scopedField, hscopedMem, hresponse, hselectionSet, hoverlap⟩
  exact ⟨scopedField, hmap scopedField hscopedMem, hresponse,
    hselectionSet, hoverlap⟩

noncomputable def FilteredNormalizedFieldGroupSource.mapInlineSomeOverlap
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {selectionSet rest : List Selection}
    {normalized : FieldMerge.ScopedField}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hobject : schema.objectType parentType)
    (hpossible : parentType ∈ schema.getPossibleTypes typeCondition)
    (hbodyParentLookup : selectionSetLookupValid schema parentType selectionSet)
    (hbodyTypeLookup : selectionSetLookupValid schema typeCondition selectionSet)
    (hrestLookup : selectionSetLookupValid schema parentType rest)
    (hgroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          (selectionSet ++ rest) normalized)
    : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
        (Selection.inlineFragment (some typeCondition) directives selectionSet :: rest)
        normalized := by
  classical
  let targetSet : List Selection :=
    Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest
  have liftScoped :
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema parentType
          (selectionSet ++ rest) ->
        { targetField : FieldMerge.ScopedField //
          targetField ∈ FieldMerge.collectFields schema parentType targetSet
            ∧ scopedFieldSameSelection scopedField targetField
            ∧ FieldMerge.sameResponseShape schema scopedField.outputType
              targetField.outputType
            ∧ (targetField.parentType = scopedField.parentType
              ∨ ¬ schema.objectType targetField.parentType) } := by
    intro scopedField hscoped
    have hexists :
        ∃ targetField,
          targetField ∈ FieldMerge.collectFields schema parentType targetSet
            ∧ scopedFieldSameSelection scopedField targetField
            ∧ FieldMerge.sameResponseShape schema scopedField.outputType
              targetField.outputType
            ∧ (targetField.parentType = scopedField.parentType
              ∨ ¬ schema.objectType targetField.parentType) := by
      rw [FieldMerge.collectFields_append] at hscoped
      rcases List.mem_append.mp hscoped with hbody | htail
      · rcases
          fieldMerge_collectFields_objectParent_possibleParent schema
            parentType typeCondition selectionSet scopedField hschema hobject
            hpossible hbodyParentLookup hbodyTypeLookup hbody with
        ⟨targetField, htargetMem, hsame, hshape, hparent⟩
        refine ⟨targetField, ?_, hsame, hshape, hparent⟩
        simp [targetSet, FieldMerge.collectFields, htargetMem]
      · have hshape :
            FieldMerge.sameResponseShape schema scopedField.outputType
              scopedField.outputType :=
          FieldMerge.sameResponseShape_refl schema scopedField.outputType
            (fieldMerge_collectFields_mem_outputType schema parentType rest
              scopedField hschema hrestLookup htail)
        exact ⟨scopedField,
          fieldMerge_collectFields_tail_mem schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              selectionSet)
            rest scopedField htail,
          scopedFieldSameSelection_refl scopedField, hshape, Or.inl rfl⟩
    exact ⟨Classical.choose hexists, Classical.choose_spec hexists⟩
  let sourceLift := liftScoped hgroup.source hgroup.sourceMem
  let targetSource := sourceLift.1
  have htargetSourceMem :
      targetSource ∈ FieldMerge.collectFields schema parentType targetSet :=
    sourceLift.2.1
  have hsourceSame :
      scopedFieldSameSelection hgroup.source targetSource :=
    sourceLift.2.2.1
  have hsourceShape :
      FieldMerge.sameResponseShape schema hgroup.source.outputType
        targetSource.outputType :=
    sourceLift.2.2.2.1
  have hsourceParent :
      targetSource.parentType = hgroup.source.parentType
        ∨ ¬ schema.objectType targetSource.parentType :=
    sourceLift.2.2.2.2
  refine ⟨targetSource, htargetSourceMem, ?_, hgroup.group,
    hgroup.childSource, hgroup.childSource_eq, ?_,
    hgroup.childReady, hgroup.childLookup, hgroup.childCurrentSource,
    hgroup.childReturnLookup, hgroup.childFeasible, hgroup.childNonempty,
    hgroup.childDirectiveFree, ?_, hgroup.normalizedSelectionSet⟩
  · exact
      GroundTypeNormalization.normalizedFieldSource_of_scopedFieldSameSelection
        hsourceSame hsourceShape hsourceParent hgroup.sourceRel
  · have htargetSize :
        SelectionSet.size (selectionSet ++ rest)
          < SelectionSet.size
              (Selection.inlineFragment (some typeCondition) directives
                selectionSet :: rest) := by
      simp [selectionSet_size_append_for_filterValidity,
        SelectionSet.size, Selection.size]
    exact Nat.lt_trans hgroup.childSource_size_lt htargetSize
  · intro selection hselection
    rcases hgroup.groupScoped selection hselection with
      ⟨scopedField, hscopedMem, hresponse, hselectionSet, hoverlap⟩
    let scopedLift := liftScoped scopedField hscopedMem
    let targetField := scopedLift.1
    have htargetMem :
        targetField ∈ FieldMerge.collectFields schema parentType targetSet :=
      scopedLift.2.1
    have hsame :
        scopedFieldSameSelection scopedField targetField :=
      scopedLift.2.2.1
    have hparent :
        targetField.parentType = scopedField.parentType
          ∨ ¬ schema.objectType targetField.parentType :=
      scopedLift.2.2.2.2
    refine ⟨targetField, htargetMem, ?_, ?_, ?_⟩
    · rcases hsame with ⟨hresponseSame, _hfieldName, _harguments,
        _hselectionSame⟩
      exact hresponseSame.symm.trans hresponse
    · rcases hsame with ⟨_hresponseSame, _hfieldName, _harguments,
        hselectionSame⟩
      exact hselectionSame.symm.trans hselectionSet
    · intro htargetObject
      rcases hparent with hparentEq | htargetNotObject
      · have hscopedObject : schema.objectType scopedField.parentType := by
          simpa [hparentEq] using htargetObject
        simpa [hparentEq] using hoverlap hscopedObject
      · exact False.elim (htargetNotObject htargetObject)

theorem collectFields_normalizeSelectionSet_mem_filteredGroupSource_nonempty
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet normalizedField,
      ∀ typeConditions,
        schema.objectType parentType
        -> objectSatisfiesTypeConditionStack schema parentType typeConditions
        -> parentType ∈ typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> selectionSetLookupValid schema parentType selectionSet
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType selectionSet
        -> selectionSetFilteredReturnLookupValid schema parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions selectionSet
        -> normalizedField
            ∈ FieldMerge.collectFields schema parentType
                (normalizeSelectionSet schema parentType selectionSet)
        -> Nonempty
            (FilteredNormalizedFieldGroupSource schema variableDefinitions
              parentType selectionSet normalizedField) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro normalizedField _typeConditions _hobject _hstack _hparent _hready
        _hlookupValid _hsource _hreturnLookup _hmerge _hfree _hfeasible
        _hnonempty hfield
      simp [normalizeSelectionSet, FieldMerge.collectFields] at hfield
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro normalizedField typeConditions hobject hstack hparent hready
        hlookupValid hsource hreturnLookup hmerge hfree hfeasible hnonempty hfield
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have htailSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rest :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType rest :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest hmerge
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredLookup :
          selectionSetLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetLookupValid_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailLookup
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
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          htailFree
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
      rcases hrest normalizedField typeConditions hobject hstack
          hparent hfilteredReady hfilteredLookup hfilteredSource hfilteredReturnLookup
          hfilteredMerge hfilteredFree hfilteredFeasible hfilteredNonempty
          (by simpa [normalizeSelectionSet, hlookup] using hfield) with
        ⟨restGroup⟩
      exact ⟨FilteredNormalizedFieldGroupSource.mapCollectFields restGroup
        (by
          intro scopedField hscopedMem
          exact fieldMerge_collectFields_tail_mem schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections)
            rest scopedField
            (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
              schema responseName parentType rest scopedField hscopedMem))
        (by
          have hfilteredSize :=
            size_withoutFieldSelectionsWithResponseName_le_for_filterValidity
              schema responseName rest
          have htailSize :=
            selectionSet_size_tail_lt_cons_for_currentScopeValidity
              (Selection.field responseName fieldName arguments directives
                subselections)
              rest
          omega)⟩
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro candidate typeConditions hobject hstack hparent hready hlookupValid
        hsource hreturnLookup hmerge hfree hfeasible hnonempty hfieldMem
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      let normalizedHead : FieldMerge.ScopedField := {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        outputType := fieldDefinition.outputType,
        selectionSet := normalizedSubselections
      }
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have htailSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rest :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType rest :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments directives
            subselections)
          rest hmerge
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredLookup :
          selectionSetLookupValid schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetLookupValid_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailLookup
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
          FieldMerge.fieldsInSetCanMerge schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          htailFree
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
      have hfieldMem' :
          candidate = normalizedHead
            ∨ candidate ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName rest)) := by
        have hmem :
            candidate ∈ FieldMerge.collectFields schema parentType
              (normalizedField schema returnType responseName fieldName
                arguments directives normalizedSubselections ::
                normalizeSelectionSet schema parentType
                  (withoutFieldSelectionsWithResponseName schema responseName rest)) := by
          rw [normalizeSelectionSet.eq_2, hlookup] at hfieldMem
          change candidate ∈ FieldMerge.collectFields schema parentType
            (normalizedField schema returnType responseName fieldName
              arguments directives normalizedSubselections ::
              normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName rest))
            at hfieldMem
          exact hfieldMem
        cases hleaf :
            leafTypeNameBool schema returnType
        · cases hnormalizedSubselections : normalizedSubselections with
          | nil =>
              simpa [normalizedField, hleaf, hnormalizedSubselections,
                FieldMerge.collectFields, hlookup, normalizedHead,
                normalizedSubselections] using hmem
          | cons head tail =>
              simpa [normalizedField, hleaf, hnormalizedSubselections,
                FieldMerge.collectFields, hlookup, normalizedHead,
                normalizedSubselections] using hmem
        · simpa [normalizedField, hleaf, FieldMerge.collectFields, hlookup,
            normalizedHead,
            normalizedSubselections] using hmem
      by_cases hhead : candidate = normalizedHead
      · subst candidate
        exact ⟨by
          simpa [normalizedHead, normalizedSubselections,
            returnType, mergeSelectionSets, Selection.subselections] using
            filteredNormalizedFieldGroupSource_fieldHead schema variableDefinitions
              parentType
              responseName fieldName arguments directives subselections rest
              fieldDefinition hschema hobject hready htailLookup hlookupValid
              hsource hreturnLookup hmerge hfree hstack hfeasible hnonempty
              hlookup⟩
      · have htailMem :
            candidate ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType
                (withoutFieldSelectionsWithResponseName schema responseName rest)) := by
          rcases hfieldMem' with hcandidate | htail
          · exact False.elim (hhead hcandidate)
          · exact htail
        rcases hrest candidate typeConditions hobject hstack
            hparent hfilteredReady hfilteredLookup hfilteredSource
            hfilteredReturnLookup hfilteredMerge hfilteredFree
            hfilteredFeasible hfilteredNonempty htailMem with
          ⟨restGroup⟩
        exact ⟨FilteredNormalizedFieldGroupSource.mapCollectFields restGroup
          (by
            intro scopedField hscopedMem
            exact fieldMerge_collectFields_tail_mem schema parentType
              (Selection.field responseName fieldName arguments directives
                subselections)
              rest scopedField
              (fieldMerge_collectFields_withoutFieldSelectionsWithResponseName_mem
                schema responseName parentType rest scopedField hscopedMem))
          (by
            have hfilteredSize :=
              size_withoutFieldSelectionsWithResponseName_le_for_filterValidity
                schema responseName rest
            have htailSize :=
              selectionSet_size_tail_lt_cons_for_currentScopeValidity
                (Selection.field responseName fieldName arguments directives
                  subselections)
                rest
            omega)⟩
  | case4 parentType rest directives subselections happend =>
      intro normalizedField typeConditions hobject hstack hparent hready
        hlookupValid hsource hreturnLookup hmerge hfree hfeasible hnonempty
        hfieldMem
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment none [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hheadLookup :
          selectionLookupValid schema parentType
            (Selection.inlineFragment none [] subselections) :=
        selectionSetLookupValid_head hlookupValid
      have hbodyLookup :
          selectionSetLookupValid schema parentType subselections := by
        simpa [selectionLookupValid] using hheadLookup
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have hbodyTailLookup :
          selectionSetLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetLookupValid_append hbodyLookup htailLookup
      have hheadSource :=
        selectionSetFilteredCurrentSourceValid_head hsource
      have hbodySource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType subselections := by
        simpa [selectionFilteredCurrentSourceValid] using hheadSource.2
      have htailSource :=
        selectionSetFilteredCurrentSourceValid_tail hsource
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
      have htailReturnLookup :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have hbodyTailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetFilteredReturnLookupValid_append hbodyReturnLookup
          htailReturnLookup
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType
          subselections rest hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 htailFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions (subselections ++ rest) :=
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
      rcases happend normalizedField typeConditions hobject hstack
          hparent hbodyTailReady hbodyTailLookup hbodyTailSource
          hbodyTailReturnLookup hbodyTailMerge hbodyTailFree
          hbodyTailFeasible hbodyTailNonempty
          (by simpa [normalizeSelectionSet] using hfieldMem) with
        ⟨bodyTailGroup⟩
      exact ⟨FilteredNormalizedFieldGroupSource.mapCollectFields bodyTailGroup
        (by
          intro scopedField hscopedMem
          simpa [FieldMerge.collectFields, FieldMerge.collectFields_append]
            using hscopedMem)
        (by
          simp [selectionSet_size_append_for_filterValidity,
            SelectionSet.size, Selection.size])⟩
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro normalizedField typeConditions hobject hstack hparent hready
        hlookupValid hsource hreturnLookup hmerge hfree hfeasible hnonempty
        hfieldMem
      have hselectionFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
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
      have hbodyTypeLookup :
          selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hbodyParentLookup :
          selectionSetLookupValid schema parentType subselections :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hbodyReady
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailLookup :
          selectionSetLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetLookupValid_append hbodyParentLookup htailLookup
      have hheadSource :=
        selectionSetFilteredCurrentSourceValid_head hsource
      have hbodySource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType subselections := by
        simpa [selectionFilteredCurrentSourceValid] using
          hheadSource.2 hoverlap
      have htailSource :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have hbodyTailSource :
          selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType (subselections ++ rest) :=
        selectionSetFilteredCurrentSourceValid_append hbodySource htailSource
      have hheadReturnLookup :=
        selectionSetFilteredReturnLookupValid_head hreturnLookup
      have hbodyReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            subselections := by
        simpa [selectionFilteredReturnLookupValid] using
          hheadReturnLookup hoverlap
      have htailReturnLookup :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have hbodyTailReturnLookup :
          selectionSetFilteredReturnLookupValid schema parentType
            (subselections ++ rest) :=
        selectionSetFilteredReturnLookupValid_append hbodyReturnLookup
          htailReturnLookup
      have hbodyTailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType
            (subselections ++ rest) :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
          schema parentType typeCondition subselections rest hschema hobject
          hoverlap hbodyParentLookup hbodyTypeLookup htailLookup hmerge
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 htailFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionSetTypeConditionFeasible,
          selectionTypeConditionFeasible] using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have htailFeasibleInBodyStack :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions) rest :=
        by
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
          objectSatisfiesTypeConditionStack schema parentType
            (typeCondition :: typeConditions) :=
        objectSatisfiesTypeConditionStack_cons_of_overlap_forValidity
          schema hobject hstack hoverlap
      have hheadNonempty :=
        selectionSetFilteredCompositeChildrenNonempty_head hnonempty
      have hbodyNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            (typeCondition :: typeConditions) subselections := by
        simpa [selectionFilteredCompositeChildrenNonempty] using
          hheadNonempty hoverlap
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
      rcases happend normalizedField (typeCondition :: typeConditions)
          hobject hstackBody (List.mem_cons_of_mem typeCondition hparent)
          hbodyTailReady hbodyTailLookup
          hbodyTailSource hbodyTailReturnLookup hbodyTailMerge hbodyTailFree
          hbodyTailFeasible hbodyTailNonempty
          (by simpa [normalizeSelectionSet, hoverlap] using hfieldMem) with
        ⟨bodyTailGroup⟩
      exact ⟨FilteredNormalizedFieldGroupSource.mapInlineSomeOverlap
        hschema hobject
        (List.contains_iff_mem.mp
          (typeIncludesObjectBool_of_object_typesOverlapBool schema
            hobject hoverlap))
        hbodyParentLookup hbodyTypeLookup htailLookup bodyTailGroup⟩
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro normalizedField typeConditions hobject hstack hparent hready hlookupValid
        hsource hreturnLookup hmerge hfree hfeasible hnonempty hfieldMem
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailLookup :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_tail hlookupValid
      have htailSource :=
        selectionSetFilteredCurrentSourceValid_tail hsource
      have htailReturnLookup :=
        selectionSetFilteredReturnLookupValid_tail hreturnLookup
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.inlineFragment (some typeCondition) directives
            subselections)
          rest hmerge
      have htailFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have htailNonempty :
          selectionSetFilteredCompositeChildrenNonempty schema parentType
            typeConditions rest :=
        selectionSetFilteredCompositeChildrenNonempty_tail hnonempty
      rcases hrest normalizedField typeConditions hobject hstack hparent htailReady
          htailLookup htailSource htailReturnLookup htailMerge htailFree
          htailFeasible htailNonempty
          (by simpa [normalizeSelectionSet, hfalse] using hfieldMem) with
        ⟨restGroup⟩
      exact ⟨FilteredNormalizedFieldGroupSource.mapCollectFields restGroup
        (by
          intro scopedField hscopedMem
          exact fieldMerge_collectFields_tail_mem schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              subselections)
            rest scopedField hscopedMem)
        (by
          exact Nat.le_of_lt
            (selectionSet_size_tail_lt_cons_for_currentScopeValidity
              (Selection.inlineFragment (some typeCondition) directives
                subselections)
              rest))⟩

noncomputable def collectFields_normalizeSelectionSet_mem_filteredGroupSource
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType : Name) (selectionSet : List Selection)
    (normalizedField : FieldMerge.ScopedField)
    : schema.objectType parentType
      -> selectionSetSemanticsReady schema parentType selectionSet
      -> selectionSetLookupValid schema parentType selectionSet
      -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
          parentType selectionSet
      -> selectionSetFilteredReturnLookupValid schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetTypeConditionFeasible schema parentType [parentType] selectionSet
      -> selectionSetFilteredCompositeChildrenNonempty schema parentType
          [parentType] selectionSet
      -> normalizedField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType selectionSet)
      -> FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          selectionSet
          normalizedField := by
  intro hobject hready hlookupValid hsource hreturnLookup hmerge hfree
    hfeasible hnonempty hfield
  have hstack :
      objectSatisfiesTypeConditionStack schema parentType [parentType] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject
  exact Classical.choice
    (collectFields_normalizeSelectionSet_mem_filteredGroupSource_nonempty schema
      variableDefinitions hschema parentType selectionSet normalizedField
      [parentType] hobject hstack (by simp) hready hlookupValid hsource hreturnLookup
      hmerge hfree hfeasible hnonempty hfield)

theorem fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType objectType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : schema.objectType parentType
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> FieldMerge.fieldsInSetCanMerge schema objectType
          (hleftGroup.childSource ++ hrightGroup.childSource) := by
  intro hobject hsourcePair hresponse
  have hscopedOf :
      ∀ selection, selection ∈ hleftGroup.group ++ hrightGroup.group ->
        ∃ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType
            (leftSet ++ rightSet)
            ∧ scopedField.responseName = leftField.responseName
            ∧ scopedField.selectionSet = selection.subselections
            ∧ (schema.objectType scopedField.parentType ->
              schema.typesOverlapBool parentType scopedField.parentType =
                true) := by
    intro selection hselection
    rcases List.mem_append.mp hselection with hleftSelection | hrightSelection
    · rcases hleftGroup.groupScoped selection hleftSelection with
        ⟨scopedField, hscopedMem, hscopedResponse, hselectionSet,
          hoverlap⟩
      refine ⟨scopedField, ?_, hscopedResponse, hselectionSet, hoverlap⟩
      rw [FieldMerge.collectFields_append]
      exact List.mem_append_left
        (FieldMerge.collectFields schema parentType rightSet) hscopedMem
    · rcases hrightGroup.groupScoped selection hrightSelection with
        ⟨scopedField, hscopedMem, hscopedResponse, hselectionSet,
          hoverlap⟩
      refine ⟨scopedField, ?_, ?_, hselectionSet, hoverlap⟩
      · rw [FieldMerge.collectFields_append]
        exact List.mem_append_right
          (FieldMerge.collectFields schema parentType leftSet) hscopedMem
      · exact hscopedResponse.trans hresponse.symm
  have hraw :
      FieldMerge.fieldsInSetCanMerge schema objectType
        (mergeSelectionSets hleftGroup.group ++
          mergeSelectionSets hrightGroup.group) :=
    fieldsInSetCanMerge_mergeSelectionSets_pair_of_scoped schema
      parentType leftField.responseName objectType (leftSet ++ rightSet)
      hleftGroup.group hrightGroup.group hobject hsourcePair hscopedOf
  simpa [hleftGroup.childSource_eq, hrightGroup.childSource_eq] using hraw

theorem filteredFieldGroupSources_identity_of_sourcePair
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> (leftField.parentType = rightField.parentType
          ∨ ¬ schema.objectType leftField.parentType
          ∨ ¬ schema.objectType rightField.parentType)
      -> leftField.fieldName = rightField.fieldName
          ∧ Argument.argumentsEquivalent leftField.arguments rightField.arguments := by
  intro hsourcePair hresponse hparents
  have hsourceResponse :
      hleftGroup.source.responseName = hrightGroup.source.responseName :=
    hleftGroup.sourceRel.responseName.trans
      (hresponse.trans hrightGroup.sourceRel.responseName.symm)
  have hleftSourceMem :
      hleftGroup.source ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_left
      (FieldMerge.collectFields schema parentType rightSet)
      hleftGroup.sourceMem
  have hrightSourceMem :
      hrightGroup.source ∈ FieldMerge.collectFields schema parentType
        (leftSet ++ rightSet) := by
    rw [FieldMerge.collectFields_append]
    exact List.mem_append_right
      (FieldMerge.collectFields schema parentType leftSet)
      hrightGroup.sourceMem
  have hsourceMerge :
      FieldMerge.fieldsForNameCanMerge schema hleftGroup.source
        hrightGroup.source :=
    FieldMerge.fieldsInSetCanMerge_pair hsourcePair hleftSourceMem
      hrightSourceMem hsourceResponse
  have hsourceParents :
      hleftGroup.source.parentType = hrightGroup.source.parentType
        ∨ ¬ schema.objectType hleftGroup.source.parentType
        ∨ ¬ schema.objectType hrightGroup.source.parentType := by
    rcases hleftGroup.sourceRel.parentCondition with
      hleftParent | hleftNotObject
    · rcases hrightGroup.sourceRel.parentCondition with
        hrightParent | hrightNotObject
      · rcases hparents with hparentEq | hparentNotObject
        · exact Or.inl
            (hleftParent.trans (hparentEq.trans hrightParent.symm))
        · rcases hparentNotObject with hleftNormalizedNotObject
            | hrightNormalizedNotObject
          · exact Or.inr (Or.inl
              (by
                intro hsourceObject
                exact hleftNormalizedNotObject
                  (by simpa [hleftParent] using hsourceObject)))
          · exact Or.inr (Or.inr
              (by
                intro hsourceObject
                exact hrightNormalizedNotObject
                  (by simpa [hrightParent] using hsourceObject)))
      · exact Or.inr (Or.inr hrightNotObject)
    · exact Or.inr (Or.inl hleftNotObject)
  rcases
    FieldMerge.fieldsForNameCanMerge_identity hsourceMerge
      hsourceParents with
    ⟨hsourceField, hsourceArguments⟩
  exact ⟨
    hleftGroup.sourceRel.fieldName.symm.trans
      (hsourceField.trans hrightGroup.sourceRel.fieldName),
    by
      simpa [← hleftGroup.sourceRel.arguments,
        ← hrightGroup.sourceRel.arguments] using hsourceArguments⟩

theorem filteredFieldGroupSources_outputType_eq_of_sourcePair
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : leftField
        ∈ FieldMerge.collectFields schema parentType
            (normalizeSelectionSet schema parentType leftSet)
      -> rightField
          ∈ FieldMerge.collectFields schema parentType
              (normalizeSelectionSet schema parentType rightSet)
      -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> (leftField.parentType = rightField.parentType
          ∨ ¬ schema.objectType leftField.parentType
          ∨ ¬ schema.objectType rightField.parentType)
      -> leftField.outputType = rightField.outputType := by
  intro hleftMem hrightMem hsourcePair hresponse hparents
  have hidentity :=
    filteredFieldGroupSources_identity_of_sourcePair schema
      variableDefinitions parentType hleftGroup hrightGroup hsourcePair
      hresponse hparents
  have hleftParent :
      leftField.parentType = parentType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      parentType (normalizeSelectionSet schema parentType leftSet)
      leftField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType leftSet)
      hleftMem
  have hrightParent :
      rightField.parentType = parentType :=
    GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
      parentType (normalizeSelectionSet schema parentType rightSet)
      rightField
      (GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType rightSet)
      hrightMem
  exact
    fieldMerge_collectFields_outputType_eq_of_same_parent_field schema
      hleftMem hrightMem (hleftParent.trans hrightParent.symm)
      hidentity.1

theorem fieldsForNameCanMerge_of_filteredFieldGroupSources_childSources
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    {leftSet rightSet : List Selection}
    {leftField rightField : FieldMerge.ScopedField}
    (hleftGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          leftSet leftField)
    (hrightGroup
      : FilteredNormalizedFieldGroupSource schema variableDefinitions parentType
          rightSet rightField)
    : FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
      -> leftField.responseName = rightField.responseName
      -> ((leftField.parentType = rightField.parentType
            ∨ ¬ schema.objectType leftField.parentType
            ∨ ¬ schema.objectType rightField.parentType)
          -> ∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType
                ((if objectTypeNameBool schema leftField.outputType.namedType then
                    normalizeSelectionSet schema leftField.outputType.namedType
                      hleftGroup.childSource
                  else
                    GroundTypeNormalization.possibleTypeNormalizations schema
                      (schema.getPossibleTypes leftField.outputType.namedType)
                      hleftGroup.childSource)
                  ++ (if objectTypeNameBool schema rightField.outputType.namedType then
                        normalizeSelectionSet schema rightField.outputType.namedType
                          hrightGroup.childSource
                      else
                        GroundTypeNormalization.possibleTypeNormalizations schema
                          (schema.getPossibleTypes rightField.outputType.namedType)
                          hrightGroup.childSource)))
      -> FieldMerge.fieldsForNameCanMerge schema leftField rightField := by
  intro hsourcePair hresponse hchildPairs
  apply GroundTypeNormalization.fieldsForNameCanMerge_of_normalizedFieldSources
      hleftGroup.sourceRel hrightGroup.sourceRel hresponse
  · have hsourceResponse :
        hleftGroup.source.responseName = hrightGroup.source.responseName :=
      hleftGroup.sourceRel.responseName.trans
        (hresponse.trans hrightGroup.sourceRel.responseName.symm)
    have hleftSourceMem :
        hleftGroup.source ∈ FieldMerge.collectFields schema parentType
          (leftSet ++ rightSet) := by
      rw [FieldMerge.collectFields_append]
      exact List.mem_append_left
        (FieldMerge.collectFields schema parentType rightSet)
        hleftGroup.sourceMem
    have hrightSourceMem :
        hrightGroup.source ∈ FieldMerge.collectFields schema parentType
          (leftSet ++ rightSet) := by
      rw [FieldMerge.collectFields_append]
      exact List.mem_append_right
        (FieldMerge.collectFields schema parentType leftSet)
        hrightGroup.sourceMem
    exact FieldMerge.fieldsInSetCanMerge_pair hsourcePair hleftSourceMem
      hrightSourceMem hsourceResponse
  · intro hparents objectType
    have hchild := hchildPairs hparents objectType
    simpa [hleftGroup.normalizedSelectionSet,
      hrightGroup.normalizedSelectionSet] using hchild

/-
Main filtered branch-merge witness for complete-normalization validity. It
shows that two already Boolean-filtered branches remain merge-compatible after
ground normalization. The proof recurses through the filtered group-source
children and relies on the filtered source/return-lookup/nonempty invariants,
not on a public survival predicate or raw validity of the filtered syntax.
-/
theorem normalizeSelectionSets_fieldsInSetCanMerge_filteredCurrentSource_anyParent
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType leftSet rightSet,
        schema.objectType parentType
        -> selectionSetSemanticsReady schema parentType leftSet
        -> selectionSetSemanticsReady schema parentType rightSet
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType leftSet
        -> selectionSetFilteredCurrentSourceValid schema variableDefinitions
            parentType rightSet
        -> selectionSetFilteredReturnLookupValid schema parentType leftSet
        -> selectionSetFilteredReturnLookupValid schema parentType rightSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType leftSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType rightSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType (leftSet ++ rightSet)
        -> selectionSetDirectiveFree leftSet
        -> selectionSetDirectiveFree rightSet
        -> selectionSetTypeConditionFeasible schema parentType [parentType] leftSet
        -> selectionSetTypeConditionFeasible schema parentType [parentType] rightSet
        -> selectionSetFilteredCompositeChildrenNonempty schema parentType
            [parentType] leftSet
        -> selectionSetFilteredCompositeChildrenNonempty schema parentType
            [parentType] rightSet
        -> ∀ mergeParent,
            FieldMerge.fieldsInSetCanMerge schema mergeParent
              (normalizeSelectionSet schema parentType leftSet
                ++ normalizeSelectionSet schema parentType rightSet) := by
  intro parentType leftSet rightSet hobject hleftReady hrightReady
    hleftSource hrightSource hleftReturnLookup hrightReturnLookup
    hleftMerge hrightMerge hsourcePair hleftFree hrightFree
    hleftFeasible hrightFeasible hleftNonempty hrightNonempty
    mergeParent
  have hstack :
      GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
        parentType [parentType] :=
    GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject
  have hleftValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions parentType
        (normalizeSelectionSet schema parentType leftSet) :=
    normalizeSelectionSet_normalizedValid_of_filteredCurrentSource
      schema variableDefinitions hschema parentType leftSet [parentType]
      hobject hstack (by simp) hleftReady hleftSource hleftReturnLookup
      hleftMerge hleftFree hleftFeasible hleftNonempty
  have hrightValid :
      GroundTypeNormalization.NormalizedSelectionSetValid schema
        variableDefinitions parentType
        (normalizeSelectionSet schema parentType rightSet) :=
    normalizeSelectionSet_normalizedValid_of_filteredCurrentSource
      schema variableDefinitions hschema parentType rightSet [parentType]
      hobject hstack (by simp) hrightReady hrightSource hrightReturnLookup
      hrightMerge hrightFree hrightFeasible hrightNonempty
  apply fieldsInSetCanMerge_append_of_pairwise
      schema mergeParent
      (normalizeSelectionSet schema parentType leftSet)
      (normalizeSelectionSet schema parentType rightSet)
  · exact normalizedSelectionSetFieldsCanMerge_anyParent hleftValid
  · exact normalizedSelectionSetFieldsCanMerge_anyParent hrightValid
  · intro leftField hleftField rightField hrightField hresponse
    have hleftLookup :
        selectionSetLookupValid schema parentType leftSet :=
      selectionSetLookupValid_of_selectionSetSemanticsReady leftSet hleftReady
    have hrightLookup :
        selectionSetLookupValid schema parentType rightSet :=
      selectionSetLookupValid_of_selectionSetSemanticsReady rightSet hrightReady
    rcases
      fieldMerge_collectFields_allFields_lookupParent_sameSelection schema
        parentType mergeParent
        (normalizeSelectionSet schema parentType leftSet) leftField
        (GroundTypeNormalization.normalizeSelectionSet_allFields schema
          parentType leftSet)
        (selectionSetLookupValid_of_selectionSetValid
          (normalizeSelectionSet schema parentType leftSet)
          hleftValid.selectionSetValid)
        hleftField with
      ⟨leftParentField, hleftParentField, hleftSame⟩
    rcases
      fieldMerge_collectFields_allFields_lookupParent_sameSelection schema
        parentType mergeParent
        (normalizeSelectionSet schema parentType rightSet) rightField
        (GroundTypeNormalization.normalizeSelectionSet_allFields schema
          parentType rightSet)
        (selectionSetLookupValid_of_selectionSetValid
          (normalizeSelectionSet schema parentType rightSet)
          hrightValid.selectionSetValid)
        hrightField with
      ⟨rightParentField, hrightParentField, hrightSame⟩
    have hparentResponse :
        leftParentField.responseName = rightParentField.responseName :=
      hleftSame.1.symm.trans (hresponse.trans hrightSame.1)
    let leftGroup :=
      collectFields_normalizeSelectionSet_mem_filteredGroupSource schema
        variableDefinitions hschema parentType leftSet leftParentField
        hobject hleftReady hleftLookup hleftSource hleftReturnLookup
        hleftMerge hleftFree hleftFeasible hleftNonempty hleftParentField
    let rightGroup :=
      collectFields_normalizeSelectionSet_mem_filteredGroupSource schema
        variableDefinitions hschema parentType rightSet rightParentField
        hobject hrightReady hrightLookup hrightSource hrightReturnLookup
        hrightMerge hrightFree hrightFeasible hrightNonempty
        hrightParentField
    have hparentMerge :
        FieldMerge.fieldsForNameCanMerge schema leftParentField
          rightParentField := by
      apply fieldsForNameCanMerge_of_filteredFieldGroupSources_childSources
          schema variableDefinitions parentType leftGroup rightGroup
          hsourcePair hparentResponse
      intro hparents childMergeParent
      let returnType := leftParentField.outputType.namedType
      have houtputEq :
          leftParentField.outputType = rightParentField.outputType :=
        filteredFieldGroupSources_outputType_eq_of_sourcePair schema
          variableDefinitions parentType leftGroup rightGroup hleftParentField
          hrightParentField hsourcePair hparentResponse hparents
      have hrightReturn :
          rightParentField.outputType.namedType = returnType := by
        dsimp [returnType]
        exact (congrArg TypeRef.namedType houtputEq).symm
      by_cases hreturnObject : objectTypeNameBool schema returnType = true
      · have hreturnObjectProp : schema.objectType returnType :=
          objectType_of_objectTypeNameBool_eq_true schema hreturnObject
        have hreturnPossible :
            returnType ∈ schema.getPossibleTypes returnType :=
          List.contains_iff_mem.mp
            (object_typeIncludesObjectBool_self schema hreturnObjectProp)
        have hchildSourcePair :
            FieldMerge.fieldsInSetCanMerge schema returnType
              (leftGroup.childSource ++ rightGroup.childSource) :=
          fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
            schema variableDefinitions parentType returnType leftGroup
            rightGroup hobject hsourcePair hparentResponse
        have hleftChildMerge :
            FieldMerge.fieldsInSetCanMerge schema returnType
              leftGroup.childSource :=
          fieldsInSetCanMerge_append_left schema returnType
            leftGroup.childSource rightGroup.childSource hchildSourcePair
        have hrightChildMerge :
            FieldMerge.fieldsInSetCanMerge schema returnType
              rightGroup.childSource :=
          fieldsInSetCanMerge_append_right schema returnType
            leftGroup.childSource rightGroup.childSource hchildSourcePair
        have hrecursive :=
          normalizeSelectionSets_fieldsInSetCanMerge_filteredCurrentSource_anyParent
            schema variableDefinitions hschema returnType leftGroup.childSource
            rightGroup.childSource hreturnObjectProp
            (leftGroup.childReady returnType
              (by dsimp [returnType] at hreturnPossible; exact hreturnPossible))
            (rightGroup.childReady returnType
              (by simpa [← hrightReturn] using hreturnPossible))
            (leftGroup.childCurrentSource returnType
              (by dsimp [returnType] at hreturnPossible; exact hreturnPossible))
            (rightGroup.childCurrentSource returnType
              (by simpa [← hrightReturn] using hreturnPossible))
            (leftGroup.childReturnLookup returnType
              (by dsimp [returnType] at hreturnPossible; exact hreturnPossible))
            (rightGroup.childReturnLookup returnType
              (by simpa [← hrightReturn] using hreturnPossible))
            hleftChildMerge hrightChildMerge hchildSourcePair
            leftGroup.childDirectiveFree rightGroup.childDirectiveFree
            (leftGroup.childFeasible returnType
              (by dsimp [returnType] at hreturnPossible; exact hreturnPossible))
            (rightGroup.childFeasible returnType
              (by simpa [← hrightReturn] using hreturnPossible))
            (leftGroup.childNonempty returnType
              (by dsimp [returnType] at hreturnPossible; exact hreturnPossible))
            (rightGroup.childNonempty returnType
              (by simpa [← hrightReturn] using hreturnPossible))
            childMergeParent
        simpa [returnType, hreturnObject, hrightReturn] using hrecursive
      · have hreturnObjectFalse :
            objectTypeNameBool schema returnType = false := by
          cases hmatch : objectTypeNameBool schema returnType
          · rfl
          · exact False.elim (hreturnObject hmatch)
        have hsamePairs :
            ∀ objectType, objectType ∈ schema.getPossibleTypes returnType ->
              FieldMerge.fieldsInSetCanMerge schema objectType
                (normalizeSelectionSet schema objectType leftGroup.childSource
                  ++ normalizeSelectionSet schema objectType
                    rightGroup.childSource) := by
          intro objectType hpossible
          have hobjectType :
              schema.objectType objectType :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
              hschema returnType objectType hpossible
          have hchildSourcePair :
              FieldMerge.fieldsInSetCanMerge schema objectType
                (leftGroup.childSource ++ rightGroup.childSource) :=
            fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
              schema variableDefinitions parentType objectType leftGroup
              rightGroup hobject hsourcePair hparentResponse
          have hleftChildMerge :
              FieldMerge.fieldsInSetCanMerge schema objectType
                leftGroup.childSource :=
            fieldsInSetCanMerge_append_left schema objectType
              leftGroup.childSource rightGroup.childSource hchildSourcePair
          have hrightChildMerge :
              FieldMerge.fieldsInSetCanMerge schema objectType
                rightGroup.childSource :=
            fieldsInSetCanMerge_append_right schema objectType
              leftGroup.childSource rightGroup.childSource hchildSourcePair
          exact
            normalizeSelectionSets_fieldsInSetCanMerge_filteredCurrentSource_anyParent
              schema variableDefinitions hschema objectType
              leftGroup.childSource rightGroup.childSource hobjectType
              (leftGroup.childReady objectType
                (by dsimp [returnType] at hpossible; exact hpossible))
              (rightGroup.childReady objectType
                (by simpa [← hrightReturn] using hpossible))
              (leftGroup.childCurrentSource objectType
                (by dsimp [returnType] at hpossible; exact hpossible))
              (rightGroup.childCurrentSource objectType
                (by simpa [← hrightReturn] using hpossible))
              (leftGroup.childReturnLookup objectType
                (by dsimp [returnType] at hpossible; exact hpossible))
              (rightGroup.childReturnLookup objectType
                (by simpa [← hrightReturn] using hpossible))
              hleftChildMerge hrightChildMerge hchildSourcePair
              leftGroup.childDirectiveFree rightGroup.childDirectiveFree
              (leftGroup.childFeasible objectType
                (by dsimp [returnType] at hpossible; exact hpossible))
              (rightGroup.childFeasible objectType
                (by simpa [← hrightReturn] using hpossible))
              (leftGroup.childNonempty objectType
                (by dsimp [returnType] at hpossible; exact hpossible))
              (rightGroup.childNonempty objectType
                (by simpa [← hrightReturn] using hpossible))
              objectType
        have hleftSelfPairs :
            ∀ leftType, leftType ∈ schema.getPossibleTypes returnType ->
              ∀ rightType, rightType ∈ schema.getPossibleTypes returnType ->
                ∀ leftBranchField,
                  leftBranchField ∈ FieldMerge.collectFields schema leftType
                    (normalizeSelectionSet schema leftType
                      leftGroup.childSource) ->
                ∀ rightBranchField,
                  rightBranchField ∈ FieldMerge.collectFields schema rightType
                    (normalizeSelectionSet schema rightType
                      leftGroup.childSource) ->
                  leftBranchField.responseName = rightBranchField.responseName ->
                    FieldMerge.fieldsForNameCanMerge schema leftBranchField
                      rightBranchField := by
          intro leftType hleftType rightType hrightType leftBranchField
            hleftBranchField rightBranchField hrightBranchField hbranchResponse
          by_cases hsame : leftType = rightType
          · subst rightType
            have hleftObject :
                schema.objectType leftType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType leftType hleftType
            have hleftSelfPair :
                FieldMerge.fieldsInSetCanMerge schema leftType
                  (leftGroup.childSource ++ leftGroup.childSource) :=
              fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
                schema variableDefinitions parentType leftType leftGroup
                leftGroup hobject
                (GroundTypeNormalization.fieldsInSetCanMerge_self schema
                  parentType leftSet hleftMerge)
                rfl
            have hleftChildMerge :
                FieldMerge.fieldsInSetCanMerge schema leftType
                  leftGroup.childSource :=
              fieldsInSetCanMerge_append_left schema leftType
                leftGroup.childSource leftGroup.childSource hleftSelfPair
            have hstackLeft :
                objectSatisfiesTypeConditionStack schema leftType [leftType] :=
              objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hleftObject
            have hleftValidBranch :
                GroundTypeNormalization.NormalizedSelectionSetValid schema
                  variableDefinitions leftType
                  (normalizeSelectionSet schema leftType
                    leftGroup.childSource) :=
              normalizeSelectionSet_normalizedValid_of_filteredCurrentSource
                schema variableDefinitions hschema leftType leftGroup.childSource
                [leftType] hleftObject hstackLeft
                (by simp)
                (leftGroup.childReady leftType
                  (by dsimp [returnType] at hleftType; exact hleftType))
                (leftGroup.childCurrentSource leftType
                  (by dsimp [returnType] at hleftType; exact hleftType))
                (leftGroup.childReturnLookup leftType
                  (by dsimp [returnType] at hleftType; exact hleftType))
                hleftChildMerge leftGroup.childDirectiveFree
                (leftGroup.childFeasible leftType
                  (by dsimp [returnType] at hleftType; exact hleftType))
                (leftGroup.childNonempty leftType
                  (by dsimp [returnType] at hleftType; exact hleftType))
            exact
              GroundTypeNormalization.normalizedBranchFieldsCanMerge_of_normalizedValid
                hleftValidBranch hleftBranchField hrightBranchField
                hbranchResponse
          · exact
              normalizedDistinctBranchesPairwiseMerge_of_abstractMerge_pair
                schema variableDefinitions hschema returnType
                (schema.getPossibleTypes returnType)
                (schema.getPossibleTypes returnType)
                leftGroup.childSource leftGroup.childSource
                (by
                  intro objectType hpossible
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hpossible)
                (by intro objectType hpossible; exact hpossible)
                (by
                  intro objectType hpossible
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hpossible)
                (by intro objectType hpossible; exact hpossible)
                (by simpa [returnType] using leftGroup.childLookup)
                (by simpa [returnType] using leftGroup.childLookup)
                (by
                  intro objectType hpossible
                  exact leftGroup.childReady objectType
                    (by dsimp [returnType] at hpossible; exact hpossible))
                (by
                  intro objectType hpossible
                  exact leftGroup.childReady objectType
                    (by dsimp [returnType] at hpossible; exact hpossible))
                (fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
                  schema variableDefinitions parentType returnType leftGroup
                  leftGroup hobject
                  (GroundTypeNormalization.fieldsInSetCanMerge_self schema
                    parentType leftSet hleftMerge)
                  rfl)
                leftType hleftType rightType hrightType hsame
                leftBranchField hleftBranchField rightBranchField
                hrightBranchField hbranchResponse
        have hrightSelfPairs :
            ∀ leftType, leftType ∈ schema.getPossibleTypes returnType ->
              ∀ rightType, rightType ∈ schema.getPossibleTypes returnType ->
                ∀ leftBranchField,
                  leftBranchField ∈ FieldMerge.collectFields schema leftType
                    (normalizeSelectionSet schema leftType
                      rightGroup.childSource) ->
                ∀ rightBranchField,
                  rightBranchField ∈ FieldMerge.collectFields schema rightType
                    (normalizeSelectionSet schema rightType
                      rightGroup.childSource) ->
                  leftBranchField.responseName = rightBranchField.responseName ->
                    FieldMerge.fieldsForNameCanMerge schema leftBranchField
                      rightBranchField := by
          intro leftType hleftType rightType hrightType leftBranchField
            hleftBranchField rightBranchField hrightBranchField hbranchResponse
          by_cases hsame : leftType = rightType
          · subst rightType
            have hleftObject :
                schema.objectType leftType :=
              SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema returnType leftType hleftType
            have hrightSelfPair :
                FieldMerge.fieldsInSetCanMerge schema leftType
                  (rightGroup.childSource ++ rightGroup.childSource) :=
              fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
                schema variableDefinitions parentType leftType rightGroup
                rightGroup hobject
                (GroundTypeNormalization.fieldsInSetCanMerge_self schema
                  parentType rightSet hrightMerge)
                rfl
            have hrightChildMerge :
                FieldMerge.fieldsInSetCanMerge schema leftType
                  rightGroup.childSource :=
              fieldsInSetCanMerge_append_left schema leftType
                rightGroup.childSource rightGroup.childSource hrightSelfPair
            have hstackRight :
                objectSatisfiesTypeConditionStack schema leftType [leftType] :=
              objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hleftObject
            have hrightValidBranch :
                GroundTypeNormalization.NormalizedSelectionSetValid schema
                  variableDefinitions leftType
                  (normalizeSelectionSet schema leftType
                    rightGroup.childSource) :=
              normalizeSelectionSet_normalizedValid_of_filteredCurrentSource
                schema variableDefinitions hschema leftType rightGroup.childSource
                [leftType] hleftObject hstackRight
                (by simp)
                (rightGroup.childReady leftType
                  (by simpa [← hrightReturn] using hleftType))
                (rightGroup.childCurrentSource leftType
                  (by simpa [← hrightReturn] using hleftType))
                (rightGroup.childReturnLookup leftType
                  (by simpa [← hrightReturn] using hleftType))
                hrightChildMerge rightGroup.childDirectiveFree
                (rightGroup.childFeasible leftType
                  (by simpa [← hrightReturn] using hleftType))
                (rightGroup.childNonempty leftType
                  (by simpa [← hrightReturn] using hleftType))
            exact
              GroundTypeNormalization.normalizedBranchFieldsCanMerge_of_normalizedValid
                hrightValidBranch hleftBranchField hrightBranchField
                hbranchResponse
          · exact
              normalizedDistinctBranchesPairwiseMerge_of_abstractMerge_pair
                schema variableDefinitions hschema returnType
                (schema.getPossibleTypes returnType)
                (schema.getPossibleTypes returnType)
                rightGroup.childSource rightGroup.childSource
                (by
                  intro objectType hpossible
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hpossible)
                (by intro objectType hpossible; exact hpossible)
                (by
                  intro objectType hpossible
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hpossible)
                (by intro objectType hpossible; exact hpossible)
                (by simpa [returnType, hrightReturn] using rightGroup.childLookup)
                (by simpa [returnType, hrightReturn] using rightGroup.childLookup)
                (by
                  intro objectType hpossible
                  exact rightGroup.childReady objectType
                    (by simpa [← hrightReturn] using hpossible))
                (by
                  intro objectType hpossible
                  exact rightGroup.childReady objectType
                    (by simpa [← hrightReturn] using hpossible))
                (fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
                  schema variableDefinitions parentType returnType rightGroup
                  rightGroup hobject
                  (GroundTypeNormalization.fieldsInSetCanMerge_self schema
                    parentType rightSet hrightMerge)
                  rfl)
                leftType hleftType rightType hrightType hsame
                leftBranchField hleftBranchField rightBranchField
                hrightBranchField hbranchResponse
        have hcrossPairs :
            ∀ leftType, leftType ∈ schema.getPossibleTypes returnType ->
              ∀ rightType, rightType ∈ schema.getPossibleTypes returnType ->
                ∀ leftBranchField,
                  leftBranchField ∈ FieldMerge.collectFields schema leftType
                    (normalizeSelectionSet schema leftType
                      leftGroup.childSource) ->
                ∀ rightBranchField,
                  rightBranchField ∈ FieldMerge.collectFields schema rightType
                    (normalizeSelectionSet schema rightType
                      rightGroup.childSource) ->
                  leftBranchField.responseName = rightBranchField.responseName ->
                    FieldMerge.fieldsForNameCanMerge schema leftBranchField
                      rightBranchField := by
          intro leftType hleftType rightType hrightType leftBranchField
            hleftBranchField rightBranchField hrightBranchField hbranchResponse
          by_cases hsame : leftType = rightType
          · subst rightType
            exact FieldMerge.fieldsInSetCanMerge_pair
              (hsamePairs leftType hleftType)
              (by
                rw [FieldMerge.collectFields_append]
                exact List.mem_append_left
                  (FieldMerge.collectFields schema leftType
                    (normalizeSelectionSet schema leftType
                      rightGroup.childSource))
                  hleftBranchField)
              (by
                rw [FieldMerge.collectFields_append]
                exact List.mem_append_right
                  (FieldMerge.collectFields schema leftType
                    (normalizeSelectionSet schema leftType
                      leftGroup.childSource))
                  hrightBranchField)
              hbranchResponse
          · exact
              normalizedDistinctBranchesPairwiseMerge_of_abstractMerge_pair
                schema variableDefinitions hschema returnType
                (schema.getPossibleTypes returnType)
                (schema.getPossibleTypes returnType)
                leftGroup.childSource rightGroup.childSource
                (by
                  intro objectType hpossible
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hpossible)
                (by intro objectType hpossible; exact hpossible)
                (by
                  intro objectType hpossible
                  exact
                    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                      hschema returnType objectType hpossible)
                (by intro objectType hpossible; exact hpossible)
                (by simpa [returnType] using leftGroup.childLookup)
                (by simpa [returnType, hrightReturn] using rightGroup.childLookup)
                (by
                  intro objectType hpossible
                  exact leftGroup.childReady objectType
                    (by dsimp [returnType] at hpossible; exact hpossible))
                (by
                  intro objectType hpossible
                  exact rightGroup.childReady objectType
                    (by simpa [← hrightReturn] using hpossible))
                (fieldsInSetCanMerge_filteredGroupSources_rawChildSource_pair
                  schema variableDefinitions parentType returnType leftGroup
                  rightGroup hobject hsourcePair hparentResponse)
                leftType hleftType rightType hrightType hsame
                leftBranchField hleftBranchField rightBranchField
                hrightBranchField hbranchResponse
        have habstract :=
          possibleTypeNormalizations_fieldsInSetCanMerge_pair_any
            schema childMergeParent
            (schema.getPossibleTypes returnType)
            (schema.getPossibleTypes returnType)
            leftGroup.childSource rightGroup.childSource
            hleftSelfPairs hrightSelfPairs hcrossPairs
        simpa [returnType, hreturnObjectFalse, hrightReturn] using habstract
    have hleftTargetParent :
        leftField.parentType = mergeParent :=
      GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
        mergeParent (normalizeSelectionSet schema parentType leftSet)
        leftField
        (GroundTypeNormalization.normalizeSelectionSet_allFields schema
          parentType leftSet)
        hleftField
    have hrightTargetParent :
        rightField.parentType = mergeParent :=
      GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
        mergeParent (normalizeSelectionSet schema parentType rightSet)
        rightField
        (GroundTypeNormalization.normalizeSelectionSet_allFields schema
          parentType rightSet)
        hrightField
    have hleftParentEq :
        leftParentField.parentType = parentType :=
      GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
        parentType (normalizeSelectionSet schema parentType leftSet)
        leftParentField
        (GroundTypeNormalization.normalizeSelectionSet_allFields schema
          parentType leftSet)
        hleftParentField
    have hrightParentEq :
        rightParentField.parentType = parentType :=
      GroundTypeNormalization.collectFields_mem_parent_eq_of_allFields schema
        parentType (normalizeSelectionSet schema parentType rightSet)
        rightParentField
        (GroundTypeNormalization.normalizeSelectionSet_allFields schema
          parentType rightSet)
        hrightParentField
    have htargetParents :
        leftField.parentType = rightField.parentType :=
      hleftTargetParent.trans hrightTargetParent.symm
    have hsourceParents :
        leftParentField.parentType = rightParentField.parentType
          ∨ ¬ schema.objectType leftParentField.parentType
          ∨ ¬ schema.objectType rightParentField.parentType :=
      Or.inl (hleftParentEq.trans hrightParentEq.symm)
    have hsubfields :
        ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (leftField.selectionSet ++ rightField.selectionSet) := by
      intro objectType
      have hparentSubfields :=
        FieldMerge.fieldsForNameCanMerge_subfields hparentMerge
          hsourceParents objectType
      simpa [hleftSame.2.2.2, hrightSame.2.2.2] using
        hparentSubfields
    exact
      fieldsForNameCanMerge_of_sameParent_sameSelection_source schema hschema
        hleftField hrightField hleftSame hrightSame htargetParents
        hparentResponse hsourceParents hparentMerge hsubfields
termination_by _parentType leftSet rightSet =>
  SelectionSet.size leftSet + SelectionSet.size rightSet
decreasing_by
  all_goals
    simp_wf
    first
    | exact Nat.add_lt_add leftGroup.childSource_size_lt
        rightGroup.childSource_size_lt
    | omega

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
      -> selectionSetBoolTypeConditionFeasibleInCase schema parentType [parentType]
          boolCase selectionSet
      -> GroundTypeNormalization.NormalizedSelectionSetValid schema
          variableDefinitions parentType
          (normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase boolCase selectionSet)) := by
  intro hobject hready himplementation hmerge hboolFeasible
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
  exact
    normalizeSelectionSet_normalizedValid_of_filteredCurrentSource
      schema variableDefinitions hschema parentType
      (filterSelectionSetBoolCase boolCase selectionSet) [parentType]
    hobject
    (GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hobject)
    (by simp)
    hfilteredReady hfilteredSource hfilteredReturnLookup hfilteredMerge
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
                  operation.variableDefinitions operation.rootType
                  (normalizeSelectionSet schema operation.rootType
                    (filterSelectionSetBoolCase boolCase operation.selectionSet)))
        -> Validation.selectionSetValid schema operation.variableDefinitions
            operation.rootType
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema operation.rootType
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
            operation.rootType
            (List.flatten (restCases.map (fun boolCase =>
              match normalizeSelectionSet schema operation.rootType
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
          normalizeSelectionSet schema operation.rootType
            (filterSelectionSetBoolCase boolCase
              operation.selectionSet) with
      | nil =>
          simpa [hnormalized] using hrest
      | cons selection normalizedRest =>
          have hbranchValid :
              GroundTypeNormalization.NormalizedSelectionSetValid schema
                operation.variableDefinitions operation.rootType
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
                operation.rootType
                (wrapWithBoolCase boolCase
                  (selection :: normalizedRest)) :=
            wrapWithBoolCase_selectionSetValid schema operation
              operation.rootType boolCase (selection :: normalizedRest)
              hoperation hvars (by simp) hbranchValid.selectionSetValid
          simpa [hnormalized] using
            Validation.selectionSetValid_append hwrapped hrest

theorem completeNormalizeBranches_selectionSetValid
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hrootObject : schema.objectType operation.rootType)
    (hready : selectionSetSemanticsReady schema operation.rootType operation.selectionSet)
    (himplementation
      : Validation.selectionSetValidInPossibleTypes schema
          operation.variableDefinitions operation.rootType operation.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge schema operation.rootType operation.selectionSet)
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases -> boolCase ∈ allBoolCases (operationBoolVars operation))
        -> (∀ boolCase,
              boolCase ∈ cases
              -> selectionSetBoolTypeConditionFeasibleInCase schema operation.rootType
                  [operation.rootType] boolCase operation.selectionSet)
        -> Validation.selectionSetValid schema operation.variableDefinitions
            operation.rootType
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema operation.rootType
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
            operation.rootType operation.selectionSet boolCase
            hrootObject hready
            himplementation hmerge
            (hboolFeasibleCases boolCase hcase))

theorem completeNormalizeBranches_validInPossibleTypes_of_normalizedBranches
    (schema : Schema) (operation : Operation)
    (hrootObject : schema.objectType operation.rootType)
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases
          -> GroundTypeNormalization.NormalizedSelectionSetValid schema
              operation.variableDefinitions operation.rootType
              (normalizeSelectionSet schema operation.rootType
                (filterSelectionSetBoolCase boolCase operation.selectionSet)))
        -> Validation.selectionSetValidInPossibleTypes schema
            operation.variableDefinitions operation.rootType
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema operation.rootType
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
            operation.variableDefinitions operation.rootType
            (List.flatten (restCases.map (fun boolCase =>
              match normalizeSelectionSet schema operation.rootType
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
          normalizeSelectionSet schema operation.rootType
            (filterSelectionSetBoolCase boolCase
              operation.selectionSet) with
      | nil =>
          simpa [hnormalized] using hrest
      | cons selection normalizedRest =>
          have hbranchValid :
              GroundTypeNormalization.NormalizedSelectionSetValid schema
                operation.variableDefinitions operation.rootType
                (selection :: normalizedRest) := by
            simpa [hnormalized] using hbranches boolCase (by simp)
          have hwrapped :
              Validation.selectionSetValidInPossibleTypes schema
                operation.variableDefinitions operation.rootType
                (wrapWithBoolCase boolCase
                  (selection :: normalizedRest)) :=
            wrapWithBoolCase_selectionSetValidInPossibleTypes schema
              operation.variableDefinitions operation.rootType hrootObject boolCase
              (selection :: normalizedRest) hbranchValid.validInPossibleTypes
          simpa [hnormalized] using
            GroundTypeNormalization.selectionSetValidInPossibleTypes_append
              hwrapped hrest

theorem completeNormalizeBranches_validInPossibleTypes
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrootObject : schema.objectType operation.rootType)
    (hready : selectionSetSemanticsReady schema operation.rootType operation.selectionSet)
    (himplementation
      : Validation.selectionSetValidInPossibleTypes schema
          operation.variableDefinitions operation.rootType operation.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge schema operation.rootType operation.selectionSet)
    : ∀ cases : List BoolCase,
        (∀ boolCase,
          boolCase ∈ cases
          -> selectionSetBoolTypeConditionFeasibleInCase schema operation.rootType
              [operation.rootType] boolCase operation.selectionSet)
        -> Validation.selectionSetValidInPossibleTypes schema
            operation.variableDefinitions operation.rootType
            (List.flatten
              (cases.map
                (fun boolCase =>
                  match normalizeSelectionSet schema operation.rootType
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
            operation.rootType operation.selectionSet boolCase
            hrootObject hready
            himplementation hmerge
            (hboolFeasibleCases boolCase hcase))

end CompleteNormalization

end NormalForm

end GraphQL
