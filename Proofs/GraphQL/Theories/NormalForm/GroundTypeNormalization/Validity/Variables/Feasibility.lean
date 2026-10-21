import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeMergeSource

/-! Feasibility facts needed by variable-use preservation, independent of static validity. -/

namespace GraphQL.NormalForm.GroundTypeNormalization.VariableUse

mutual
  def selectionContainsTypeConditionFeasibleField (schema : Schema)
      (conditions : List Name)
      : Selection -> Prop
    | .field _ _ _ _ _ => typeConditionStackFeasible schema conditions
    | .inlineFragment none _ children =>
        selectionSetContainsTypeConditionFeasibleField schema conditions children
    | .inlineFragment (some condition) _ children =>
        selectionSetContainsTypeConditionFeasibleField schema (condition :: conditions)
          children

  def selectionSetContainsTypeConditionFeasibleField (schema : Schema)
      (conditions : List Name)
      : List Selection -> Prop
    | [] => False
    | selection :: rest =>
        selectionContainsTypeConditionFeasibleField schema conditions selection
        ∨ selectionSetContainsTypeConditionFeasibleField schema conditions rest
end

def objectSatisfiesTypeConditionStack
    (schema : Schema) (objectType : Name) (typeConditions : List Name)
    : Prop :=
  ∀ typeCondition,
    typeCondition ∈ typeConditions -> objectType ∈ schema.getPossibleTypes typeCondition

theorem objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
    (schema : Schema) {objectType : Name} (hobject : schema.objectType objectType)
    : objectSatisfiesTypeConditionStack schema objectType [objectType] := by
  intro condition hcondition
  have heq : condition = objectType := by simpa using hcondition
  subst condition
  exact List.contains_iff_mem.mp (object_typeIncludesObjectBool_self schema hobject)

theorem selectionSetTypeConditionFeasible_tail
    {schema : Schema} {parentType : Name} {conditions : List Name}
    {selection : Selection} {rest : List Selection}
    (hfeasible
      : selectionSetTypeConditionFeasible schema parentType conditions
          (selection :: rest))
    : selectionSetTypeConditionFeasible schema parentType conditions rest :=
  hfeasible.2

theorem selectionSetTypeConditionFeasible_append
    {schema : Schema} {parentType : Name} {conditions : List Name}
    {left right : List Selection}
    (hleft : selectionSetTypeConditionFeasible schema parentType conditions left)
    (hright : selectionSetTypeConditionFeasible schema parentType conditions right)
    : selectionSetTypeConditionFeasible schema parentType conditions (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons selection rest ih => exact ⟨hleft.1, ih hleft.2⟩

theorem selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName parentType : Name) (conditions : List Name)
    : ∀ selectionSet,
        selectionSetTypeConditionFeasible schema parentType conditions selectionSet
        -> selectionSetTypeConditionFeasible schema parentType conditions
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | [], _hfeasible => by
      simp [withoutFieldSelectionsWithResponseName, selectionSetTypeConditionFeasible]
  | selection :: rest, hfeasible => by
      have htail := selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
        schema responseName parentType conditions rest hfeasible.2
      cases selection with
      | field name fieldName arguments directives children =>
          simp only [withoutFieldSelectionsWithResponseName]
          split
          · exact htail
          · exact ⟨hfeasible.1, htail⟩
      | inlineFragment condition directives children =>
          cases condition with
          | none =>
              simp only [withoutFieldSelectionsWithResponseName,
                selectionSetTypeConditionFeasible, selectionTypeConditionFeasible]
              exact ⟨selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
                schema responseName parentType conditions children hfeasible.1, htail⟩
          | some condition =>
              simp only [withoutFieldSelectionsWithResponseName,
                selectionSetTypeConditionFeasible, selectionTypeConditionFeasible]
              exact ⟨selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
                schema responseName parentType (condition :: conditions) children hfeasible.1,
                htail⟩

theorem typeConditionStackFeasible_of_subset_forValidity
    {schema : Schema} {source target : List Name}
    (hfeasible : typeConditionStackFeasible schema source)
    (hsubset : ∀ condition, condition ∈ target -> condition ∈ source)
    : typeConditionStackFeasible schema target := by
  rcases hfeasible with ⟨objectType, hobject⟩
  exact ⟨objectType, fun condition hcondition => hobject condition (hsubset condition hcondition)⟩

mutual
  theorem selectionTypeConditionFeasible_of_stack_subset
      (schema : Schema) {parentType : Name} {source target : List Name}
      (hsubset : ∀ condition, condition ∈ target -> condition ∈ source)
      : ∀ selection,
          selectionTypeConditionFeasible schema parentType source selection
          -> selectionTypeConditionFeasible schema parentType target selection
    | .field _ _ _ _ _, hfeasible =>
        ⟨typeConditionStackFeasible_of_subset_forValidity hfeasible.1 hsubset, hfeasible.2⟩
    | .inlineFragment none _ children, hfeasible =>
        selectionSetTypeConditionFeasible_of_stack_subset schema hsubset children hfeasible
    | .inlineFragment (some condition) _ children, hfeasible => by
        apply selectionSetTypeConditionFeasible_of_stack_subset schema
          (source := condition :: source) (target := condition :: target) _ children hfeasible
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with rfl | htail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem condition (hsubset candidate htail)

  theorem selectionSetTypeConditionFeasible_of_stack_subset
      (schema : Schema) {parentType : Name} {source target : List Name}
      (hsubset : ∀ condition, condition ∈ target -> condition ∈ source)
      : ∀ selectionSet,
          selectionSetTypeConditionFeasible schema parentType source selectionSet
          -> selectionSetTypeConditionFeasible schema parentType target selectionSet
    | [], _hfeasible => trivial
    | selection :: rest, hfeasible =>
        ⟨
          selectionTypeConditionFeasible_of_stack_subset schema hsubset selection
            hfeasible.1,
          selectionSetTypeConditionFeasible_of_stack_subset schema hsubset rest
            hfeasible.2
        ⟩
end

-- Feasibility tracks the enclosing fragment stack; field children keep their own
-- return-type obligations even when runtime collection flattens those fragments.
theorem collectedField_feasible (schema : Schema) (parentType responseName : Name)
    : ∀ conditions selectionSet field,
        selectionSetTypeConditionFeasible schema parentType conditions selectionSet
        -> field
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet
        -> ∃ fieldConditions,
            selectionTypeConditionFeasible schema parentType fieldConditions field
  | _conditions, [], _field, _hfeasible, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | conditions, selection :: rest, field, hfeasible, hfield => by
      cases selection with
      | field name fieldName arguments directives children =>
          simp only [fieldSelectionsWithResponseNameInScope] at hfield
          split at hfield
          · rcases List.mem_cons.mp hfield with rfl | hrest
            · exact ⟨conditions, hfeasible.1⟩
            · exact collectedField_feasible schema parentType responseName
                conditions rest field hfeasible.2 hrest
          · exact collectedField_feasible schema parentType responseName
              conditions rest field hfeasible.2 hfield
      | inlineFragment condition directives children =>
          cases condition with
          | none =>
              simp only [fieldSelectionsWithResponseNameInScope, List.mem_append] at hfield
              exact hfield.elim
                (collectedField_feasible schema parentType responseName
                  conditions children field hfeasible.1)
                (collectedField_feasible schema parentType responseName
                  conditions rest field hfeasible.2)
          | some condition =>
              simp only [fieldSelectionsWithResponseNameInScope] at hfield
              split at hfield
              · exact (List.mem_append.mp hfield).elim
                  (collectedField_feasible schema parentType responseName
                    (condition :: conditions) children field hfeasible.1)
                  (collectedField_feasible schema parentType responseName
                    conditions rest field hfeasible.2)
              · exact collectedField_feasible schema parentType responseName
                  conditions rest field hfeasible.2 hfield

theorem selectionTypeConditionFeasible_field_child_branch_forObject
    (schema : Schema) {parentType responseName fieldName objectType : Name}
    {conditions : List Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {children : List Selection}
    {definition : FieldDefinition}
    (hfeasible
      : selectionTypeConditionFeasible schema parentType conditions
          (.field responseName fieldName arguments directives children))
    (_hstack : objectSatisfiesTypeConditionStack schema parentType conditions)
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hpossible : objectType ∈ schema.getPossibleTypes definition.outputType.namedType)
    : selectionSetTypeConditionFeasible schema objectType [objectType] children := by
  cases children with
  | nil => trivial
  | cons child children =>
      have hchildren := hfeasible.2
      rw [hlookup] at hchildren
      exact hchildren.2 objectType hpossible

theorem fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
    (schema : Schema) (parentType responseName : Name) {typeConditions : List Name}
    (_hobject : schema.objectType parentType)
    (_hstack : objectSatisfiesTypeConditionStack schema parentType typeConditions)
    (selectionSet : List Selection)
    (hfeasible
      : selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet)
    (fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (children : List Selection)
    (definition : FieldDefinition) (childType : Name)
    (hfield
      : Selection.field responseName fieldName arguments directives children
        ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
            selectionSet)
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hpossible : childType ∈ schema.getPossibleTypes definition.outputType.namedType)
    : selectionSetTypeConditionFeasible schema childType [childType] children := by
  rcases collectedField_feasible schema parentType responseName
    typeConditions selectionSet _ hfeasible hfield with ⟨conditions, hfield⟩
  cases children with
  | nil => trivial
  | cons child children =>
      have hchildren := hfield.2
      rw [hlookup] at hchildren
      exact hchildren.2 childType hpossible

theorem fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
    (schema : Schema) (parentType responseName : Name) {typeConditions : List Name}
    (selectionSet : List Selection)
    (hfeasible
      : selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet)
    (fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (children : List Selection)
    (definition : FieldDefinition)
    (hfield
      : Selection.field responseName fieldName arguments directives children
        ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
            selectionSet)
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hnonempty : children ≠ [])
    : schema.getPossibleTypes definition.outputType.namedType ≠ [] := by
  rcases collectedField_feasible schema parentType responseName
    typeConditions selectionSet _ hfeasible hfield with ⟨conditions, hfield⟩
  cases children with
  | nil => exact False.elim (hnonempty rfl)
  | cons child children =>
      have hchildren := hfield.2
      rw [hlookup] at hchildren
      exact hchildren.1

theorem selectionSetTypeConditionFeasible_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name} {conditions : List Name}
    (selections : List Selection)
    (hfeasible
      : ∀ selection,
          selection ∈ selections
          -> selectionSetTypeConditionFeasible schema parentType conditions
              selection.subselections)
    : selectionSetTypeConditionFeasible schema parentType conditions
        (mergeSelectionSets selections) := by
  induction selections with
  | nil => trivial
  | cons selection rest ih =>
      exact selectionSetTypeConditionFeasible_append (hfeasible selection (by simp))
        (ih (fun candidate hcandidate => hfeasible candidate (by simp [hcandidate])))

theorem
    selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {parentType responseName childType : Name}
    {typeConditions : List Name} (selectionSet : List Selection)
    (hfields
      : ∀ fieldName arguments directives children,
          Selection.field responseName fieldName arguments directives children
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet
          -> selectionSetTypeConditionFeasible schema childType typeConditions children)
    : selectionSetTypeConditionFeasible schema childType typeConditions
        (mergeSelectionSets
          (fieldSelectionsWithResponseNameInScope schema parentType responseName
            selectionSet)) := by
  apply selectionSetTypeConditionFeasible_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
    selectionSet selection hselection with ⟨fieldName, arguments, directives, children, rfl⟩
  exact hfields fieldName arguments directives children hselection

mutual
  theorem typeConditionStackFeasible_of_selectionContains_forValidity
      (schema : Schema) (conditions : List Name)
      : ∀ selection,
          selectionContainsTypeConditionFeasibleField schema conditions selection
          -> typeConditionStackFeasible schema conditions
    | .field _ _ _ _ _, hfeasible => hfeasible
    | .inlineFragment none _ children, hfeasible =>
        typeConditionStackFeasible_of_selectionSetContains_forValidity
          schema conditions children hfeasible
    | .inlineFragment (some condition) _ children, hfeasible =>
        typeConditionStackFeasible_of_subset_forValidity
          (typeConditionStackFeasible_of_selectionSetContains_forValidity
            schema (condition :: conditions) children hfeasible)
          (fun _ h => List.mem_cons_of_mem condition h)

  theorem typeConditionStackFeasible_of_selectionSetContains_forValidity
      (schema : Schema) (conditions : List Name)
      : ∀ selectionSet,
          selectionSetContainsTypeConditionFeasibleField schema conditions selectionSet
          -> typeConditionStackFeasible schema conditions
    | [], hfeasible => by cases hfeasible
    | selection :: rest, hfeasible =>
        hfeasible.elim
          (typeConditionStackFeasible_of_selectionContains_forValidity schema conditions selection)
          (typeConditionStackFeasible_of_selectionSetContains_forValidity schema conditions rest)
end

end GraphQL.NormalForm.GroundTypeNormalization.VariableUse
