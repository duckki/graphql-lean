import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.FieldHeads

/-!
Type-condition feasibility facts for ground-type normalization validity.
-/

namespace GraphQL

namespace NormalForm

-- Strong proof-facing form used by the existing preservation proofs: whenever the
-- normalizer is asked to process a nonempty selection set in a concrete scope, that
-- selection set contains a feasible field for that scope and recursively satisfies the
-- operation-level type-condition feasibility predicate in that scope.
def selectionSetsTypeConditionFeasibleInEveryNormalizerScope (schema : Schema) : Prop :=
  ∀ parentType selectionSet,
    selectionSet ≠ []
    -> GroundTypeNormalization.selectionSetContainsTypeConditionFeasibleField
          schema [parentType] selectionSet
        ∧ selectionSetTypeConditionFeasible schema parentType [parentType] selectionSet

namespace GroundTypeNormalization

theorem selectionSetTypeConditionFeasible_tail
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetTypeConditionFeasible schema parentType typeConditions
        (selection :: selectionSet)
      -> selectionSetTypeConditionFeasible schema parentType typeConditions
          selectionSet := by
  intro hfeasible
  simpa [selectionSetTypeConditionFeasible] using hfeasible.2

theorem selectionSetTypeConditionFeasible_append
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    {left right : List Selection}
    : selectionSetTypeConditionFeasible schema parentType typeConditions left
      -> selectionSetTypeConditionFeasible schema parentType typeConditions right
      -> selectionSetTypeConditionFeasible schema parentType typeConditions
          (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      have hhead :
          selectionTypeConditionFeasible schema parentType typeConditions
             selection := by
        simpa [selectionSetTypeConditionFeasible] using hleft.1
      have htail :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest := by
        simpa [selectionSetTypeConditionFeasible] using hleft.2
      simp [selectionSetTypeConditionFeasible]
      exact ⟨hhead, ih htail⟩

theorem selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName parentType : Name)
    (typeConditions : List Name)
    : ∀ selectionSet,
        selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions

            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | [], _hfeasible => by
      simp [withoutFieldSelectionsWithResponseName, selectionSetTypeConditionFeasible]
  | selection :: rest, hfeasible => by
      have hhead :
          selectionTypeConditionFeasible schema parentType typeConditions
             selection := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have htail :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.2
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hresponse : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hresponse]
            exact selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
              schema responseName parentType typeConditions rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse,
              selectionSetTypeConditionFeasible]
            exact ⟨hhead,
              selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
                schema responseName parentType typeConditions rest htail⟩
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              rw [withoutFieldSelectionsWithResponseName]
              simp [selectionSetTypeConditionFeasible,
                selectionTypeConditionFeasible]
              exact ⟨
                selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
                  schema responseName parentType typeConditions selectionSet
                  hhead,
                selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
                  schema responseName parentType typeConditions rest htail⟩
          | some typeCondition =>
              rw [withoutFieldSelectionsWithResponseName]
              simp [selectionSetTypeConditionFeasible,
                selectionTypeConditionFeasible]
              exact ⟨
                selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
                  schema responseName parentType
                  (typeCondition :: typeConditions) selectionSet hhead,
                selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
              schema responseName parentType typeConditions rest htail⟩

theorem possibleTypeNormalizations_ne_nil_of_branch_forValidity
    (schema : Schema) {possibleTypes : List Name}
    {selectionSet : List Selection} {objectType : Name}
    : objectType ∈ possibleTypes
      -> normalizeSelectionSet schema objectType selectionSet ≠ []
      -> possibleTypeNormalizations schema possibleTypes selectionSet ≠ [] := by
  intro hmem hnonempty
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst head
        cases hnormalized :
            normalizeSelectionSet schema objectType selectionSet with
        | nil =>
            exact False.elim (hnonempty hnormalized)
        | cons selection selections =>
            simp [possibleTypeNormalizations, hnormalized]
      · have hrestNonempty :
            possibleTypeNormalizations schema rest selectionSet ≠ [] :=
          ih hrest
        cases hnormalized :
            normalizeSelectionSet schema head selectionSet with
        | nil =>
            simpa [possibleTypeNormalizations, hnormalized] using
              hrestNonempty
        | cons selection selections =>
            simp [possibleTypeNormalizations, hnormalized]

def objectSatisfiesTypeConditionStack
    (schema : Schema) (objectType : Name) (typeConditions : List Name)
    : Prop :=
  ∀ typeCondition,
    typeCondition ∈ typeConditions -> objectType ∈ schema.getPossibleTypes typeCondition

theorem typeConditionStackFeasible_of_objectSatisfies_forValidity
    {schema : Schema} {objectType : Name} {typeConditions : List Name}
    : objectSatisfiesTypeConditionStack schema objectType typeConditions
      -> typeConditionStackFeasible schema typeConditions := by
  intro hobject
  exact ⟨objectType, hobject⟩

theorem objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
    (schema : Schema) {objectType : Name}
    : schema.objectType objectType
      -> objectSatisfiesTypeConditionStack schema objectType [objectType] := by
  intro hobject typeCondition hmem
  have heq : typeCondition = objectType := by simpa using hmem
  subst typeCondition
  exact object_typeIncludesObject_self schema hobject

theorem objectSatisfiesTypeConditionStack_cons_of_overlap_forValidity
    (schema : Schema) {objectType typeCondition : Name}
    {typeConditions : List Name}
    : schema.objectType objectType
      -> objectSatisfiesTypeConditionStack schema objectType typeConditions
      -> schema.typesOverlapBool objectType typeCondition = true
      -> objectSatisfiesTypeConditionStack schema objectType
          (typeCondition :: typeConditions) := by
  intro hobject hstack hoverlap candidate hcandidate
  rcases List.mem_cons.mp hcandidate with heq | htail
  · subst candidate
    exact List.contains_iff_mem.mp
      (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject
        hoverlap)
  · exact hstack candidate htail

theorem typeConditionStackFeasible_of_subset_forValidity
    {schema : Schema} {source target : List Name}
    : typeConditionStackFeasible schema source
      -> (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source)
      -> typeConditionStackFeasible schema target := by
  intro hfeasible hsubset
  rcases hfeasible with ⟨objectType, hobjectType⟩
  exact ⟨objectType, fun typeCondition hmem =>
    hobjectType typeCondition (hsubset typeCondition hmem)⟩

mutual
  theorem selectionContainsTypeConditionFeasibleField_of_feasible
      (schema : Schema) (parentType : Name) (typeConditions : List Name)
      : ∀ selection,
          selectionTypeConditionFeasible schema parentType typeConditions selection
          -> selectionInlineFragmentsNonempty selection
          -> selectionContainsTypeConditionFeasibleField schema typeConditions selection
    | .field _responseName _fieldName _arguments _directives _selectionSet,
      hfeasible, _hnonempty => by
        simpa [selectionTypeConditionFeasible,
          selectionContainsTypeConditionFeasibleField] using hfeasible.1
    | .inlineFragment none _directives selectionSet, hfeasible, hnonempty => by
        have hnonempty' :
            selectionSet ≠ [] ∧ selectionSetInlineFragmentsNonempty selectionSet := by
          simpa [selectionInlineFragmentsNonempty] using hnonempty
        exact
          selectionSetContainsTypeConditionFeasibleField_of_feasible
            schema parentType typeConditions selectionSet hfeasible
              hnonempty'.1 hnonempty'.2
    | .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible, hnonempty => by
        have hnonempty' :
            selectionSet ≠ [] ∧ selectionSetInlineFragmentsNonempty selectionSet := by
          simpa [selectionInlineFragmentsNonempty] using hnonempty
        exact
          selectionSetContainsTypeConditionFeasibleField_of_feasible
            schema parentType (typeCondition :: typeConditions)
              selectionSet hfeasible hnonempty'.1 hnonempty'.2

  theorem selectionSetContainsTypeConditionFeasibleField_of_feasible
      (schema : Schema) (parentType : Name) (typeConditions : List Name)
      : ∀ selectionSet,
          selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
          -> selectionSet ≠ []
          -> selectionSetInlineFragmentsNonempty selectionSet
          -> selectionSetContainsTypeConditionFeasibleField schema typeConditions
              selectionSet
    | [], _hfeasible, hnonempty, _hinline =>
        False.elim (hnonempty rfl)
    | selection :: rest, hfeasible, _hnonempty, hinline => by
        unfold selectionSetInlineFragmentsNonempty at hinline
        exact Or.inl
          (selectionContainsTypeConditionFeasibleField_of_feasible
            schema parentType typeConditions selection hfeasible.1
              (hinline selection (by simp)))
end

mutual
  theorem selectionTypeConditionFeasible_of_stack_subset
      (schema : Schema) {parentType : Name} {source target : List Name}
      : (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source)
        -> ∀ selection,
            selectionTypeConditionFeasible schema parentType source selection
            -> selectionTypeConditionFeasible schema parentType target selection
    | hsubset,
      .field responseName fieldName arguments directives selectionSet,
      hfeasible => by
        cases selectionSet with
        | nil =>
            exact ⟨
              typeConditionStackFeasible_of_subset_forValidity
                hfeasible.1 hsubset,
              by simp⟩
        | cons selection rest =>
            exact ⟨
              typeConditionStackFeasible_of_subset_forValidity
                hfeasible.1 hsubset,
              hfeasible.2⟩
    | hsubset, .inlineFragment none directives selectionSet, hfeasible => by
        exact
          selectionSetTypeConditionFeasible_of_stack_subset schema hsubset
            selectionSet hfeasible
    | hsubset, .inlineFragment (some typeCondition) directives selectionSet,
      hfeasible => by
        exact
          selectionSetTypeConditionFeasible_of_stack_subset schema
            (fun candidate hcandidate =>
              List.mem_cons.mp hcandidate |>.elim
                (fun heq => by subst candidate; simp)
                (fun hmem => List.mem_cons_of_mem typeCondition
                  (hsubset candidate hmem)))
            selectionSet hfeasible

  theorem selectionSetTypeConditionFeasible_of_stack_subset
      (schema : Schema) {parentType : Name} {source target : List Name}
      : (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source)
        -> ∀ selectionSet,
            selectionSetTypeConditionFeasible schema parentType source selectionSet
            -> selectionSetTypeConditionFeasible schema parentType target selectionSet
    | _hsubset, [], _hfeasible => by
        simp [selectionSetTypeConditionFeasible]
    | hsubset, selection :: rest, hfeasible => by
        have hhead :
            selectionTypeConditionFeasible schema parentType source
              selection := by
          simpa [selectionSetTypeConditionFeasible] using hfeasible.1
        have htail :
            selectionSetTypeConditionFeasible schema parentType source
               rest := by
          simpa [selectionSetTypeConditionFeasible] using hfeasible.2
        simp [selectionSetTypeConditionFeasible]
        exact ⟨
          selectionTypeConditionFeasible_of_stack_subset schema hsubset
            selection hhead,
          selectionSetTypeConditionFeasible_of_stack_subset schema hsubset
            rest htail⟩
end

mutual
  theorem selectionTypeConditionFeasible_insert_condition_for_object
      (schema : Schema) {parentType typeCondition : Name}
      (hobject : schema.objectType parentType)
      (hcondition : parentType ∈ schema.getPossibleTypes typeCondition)
      {baseConditions : List Name}
      (hparent : parentType ∈ baseConditions)
      : ∀ (leadingConditions : List Name) (selection : Selection),
          selectionTypeConditionFeasible schema parentType
            (leadingConditions ++ baseConditions) selection
          -> selectionTypeConditionFeasible schema parentType
              (leadingConditions ++ typeCondition :: baseConditions) selection
    | leadingConditions,
      .field responseName fieldName arguments directives selectionSet,
      hfeasible => by
        have hwitness := hfeasible.1
        rcases hwitness with ⟨witness, hwitness⟩
        have hwitnessParent :
            witness ∈ schema.getPossibleTypes parentType :=
          hwitness parentType
            (List.mem_append_right leadingConditions hparent)
        have hwitnessEq : witness = parentType :=
          object_typeIncludesObjectBool_eq_self schema hobject
            (List.contains_iff_mem.mpr hwitnessParent)
        subst witness
        constructor
        · refine ⟨parentType, ?_⟩
          intro candidate hcandidate
          rcases List.mem_append.mp hcandidate with hprefix | htail
          · exact hwitness candidate
              (List.mem_append_left baseConditions hprefix)
          · rcases List.mem_cons.mp htail with heq | hbase
            · subst candidate
              exact hcondition
            · exact hwitness candidate
                (List.mem_append_right leadingConditions hbase)
        · exact hfeasible.2
    | leadingConditions, .inlineFragment none directives selectionSet,
      hfeasible => by
        exact
          selectionSetTypeConditionFeasible_insert_condition_for_object
            schema hobject hcondition hparent leadingConditions selectionSet
              hfeasible
    | leadingConditions,
      .inlineFragment (some nestedCondition) directives selectionSet,
      hfeasible => by
        simpa [selectionTypeConditionFeasible, List.cons_append] using
          selectionSetTypeConditionFeasible_insert_condition_for_object
            schema hobject hcondition hparent
            (nestedCondition :: leadingConditions) selectionSet hfeasible

  theorem selectionSetTypeConditionFeasible_insert_condition_for_object
      (schema : Schema) {parentType typeCondition : Name}
      (hobject : schema.objectType parentType)
      (hcondition : parentType ∈ schema.getPossibleTypes typeCondition)
      {baseConditions : List Name}
      (hparent : parentType ∈ baseConditions)
      : ∀ (leadingConditions : List Name) (selectionSet : List Selection),
          selectionSetTypeConditionFeasible schema parentType
            (leadingConditions ++ baseConditions) selectionSet
          -> selectionSetTypeConditionFeasible schema parentType
              (leadingConditions ++ typeCondition :: baseConditions) selectionSet
    | _leadingConditions, [], _hfeasible => by
        simp [selectionSetTypeConditionFeasible]
    | leadingConditions, selection :: rest, hfeasible => by
        constructor
        · exact
            selectionTypeConditionFeasible_insert_condition_for_object
              schema hobject hcondition hparent leadingConditions selection
                hfeasible.1
        · exact
            selectionSetTypeConditionFeasible_insert_condition_for_object
              schema hobject hcondition hparent leadingConditions rest
                hfeasible.2
end

mutual
  theorem selectionContainsTypeConditionFeasibleField_of_subset_forValidity
      (schema : Schema) {source target : List Name}
      : (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source)
        -> ∀ selection,
            selectionContainsTypeConditionFeasibleField schema source selection
            -> selectionContainsTypeConditionFeasibleField schema target selection
    | hsubset,
      .field _responseName _fieldName _arguments _directives _selectionSet,
      hfeasible => by
        exact typeConditionStackFeasible_of_subset_forValidity hfeasible
          hsubset
    | hsubset,
      .inlineFragment none _directives selectionSet, hfeasible => by
        exact selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
          schema hsubset selectionSet hfeasible
    | hsubset,
      .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible => by
        exact selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
          schema
          (fun candidate hcandidate =>
            List.mem_cons.mp hcandidate |>.elim
              (fun heq => by subst candidate; simp)
              (fun hmem => List.mem_cons_of_mem typeCondition
                (hsubset candidate hmem)))
          selectionSet hfeasible

  theorem selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
      (schema : Schema) {source target : List Name}
      : (∀ typeCondition, typeCondition ∈ target -> typeCondition ∈ source)
        -> ∀ selectionSet,
            selectionSetContainsTypeConditionFeasibleField schema source selectionSet
            -> selectionSetContainsTypeConditionFeasibleField schema target selectionSet
    | _hsubset, [], hfeasible => by
        cases hfeasible
    | hsubset, selection :: rest, hfeasible => by
        rcases hfeasible with hhead | htail
        · exact Or.inl
            (selectionContainsTypeConditionFeasibleField_of_subset_forValidity
              schema hsubset selection hhead)
        · exact Or.inr
            (selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
              schema hsubset rest htail)
end

theorem selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
    (schema : Schema) (typeConditions : List Name)
    {left right : List Selection}
    : selectionSetContainsTypeConditionFeasibleField schema typeConditions left
      -> selectionSetContainsTypeConditionFeasibleField schema typeConditions
          (left ++ right) := by
  intro hleft
  induction left with
  | nil =>
      cases hleft
  | cons selection rest ih =>
      rcases hleft with hhead | htail
      · simp [selectionSetContainsTypeConditionFeasibleField, hhead]
      · simp [selectionSetContainsTypeConditionFeasibleField, ih htail]

theorem selectionSetContainsTypeConditionFeasibleField_append_right_forValidity
    (schema : Schema) (typeConditions : List Name)
    (left : List Selection) {right : List Selection}
    : selectionSetContainsTypeConditionFeasibleField schema typeConditions right
      -> selectionSetContainsTypeConditionFeasibleField schema typeConditions
          (left ++ right) := by
  intro hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      exact Or.inr ih

theorem selectionTypeConditionFeasible_field_child_contains_forPossibleType
    (schema : Schema) {parentType responseName fieldName : Name}
    {typeConditions : List Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet : List Selection} {fieldDefinition : FieldDefinition}
    : selectionTypeConditionFeasible schema parentType typeConditions

        (Selection.field responseName fieldName arguments directives selectionSet)
      -> objectSatisfiesTypeConditionStack schema parentType typeConditions
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSet ≠ []
      -> selectionSetInlineFragmentsNonempty selectionSet
      -> ∃ objectType,
          objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
          ∧ selectionSetContainsTypeConditionFeasibleField schema
              [objectType] selectionSet := by
  intro hfeasible _hstack hlookup hnonempty hinline
  cases selectionSet with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons selection rest =>
      have hchild := hfeasible.2
      rw [hlookup] at hchild
      rcases List.exists_mem_of_ne_nil _ hchild.1 with
        ⟨objectType, hobjectType⟩
      exact ⟨objectType, hobjectType,
        selectionSetContainsTypeConditionFeasibleField_of_feasible schema
          objectType [objectType] (selection :: rest)
          (hchild.2 objectType hobjectType) hnonempty hinline⟩

theorem selectionTypeConditionFeasible_field_child_branch_forObject
    (schema : Schema) {parentType responseName fieldName : Name}
    {typeConditions : List Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet : List Selection} {fieldDefinition : FieldDefinition}
    {objectType : Name}
    : selectionTypeConditionFeasible schema parentType typeConditions

        (Selection.field responseName fieldName arguments directives selectionSet)
      -> objectSatisfiesTypeConditionStack schema parentType typeConditions
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> selectionSetTypeConditionFeasible schema objectType [objectType]
          selectionSet := by
  intro hfeasible hstack hlookup hobjectType
  cases selectionSet with
  | nil =>
      simp [selectionSetTypeConditionFeasible]
  | cons selection rest =>
      have hchild := hfeasible.2
      rw [hlookup] at hchild
      exact hchild.2 objectType hobjectType

theorem selectionSetTypeConditionFeasible_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name} {typeConditions : List Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetTypeConditionFeasible schema parentType typeConditions
              selection.subselections)
        -> selectionSetTypeConditionFeasible schema parentType typeConditions
            (mergeSelectionSets selections)
  | [], _hfeasible => by
      simp [mergeSelectionSets, selectionSetTypeConditionFeasible]
  | selection :: rest, hfeasible => by
      simp [mergeSelectionSets]
      apply selectionSetTypeConditionFeasible_append
      · exact hfeasible selection (by simp)
      · exact
          selectionSetTypeConditionFeasible_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hfeasible candidate (by simp [hcandidate]))

theorem selectionSetTypeConditionFeasible_mergeSelectionSets_of_field_subselections
    {schema : Schema} {parentType responseName : Name}
    {typeConditions : List Name}
    (selections : List Selection)
    : (∀ selection,
        selection ∈ selections
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections)
      -> (∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ selections
            -> selectionSetTypeConditionFeasible schema parentType typeConditions
                subselections)
      -> selectionSetTypeConditionFeasible schema parentType typeConditions
          (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetTypeConditionFeasible_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections] using
    hfields fieldName arguments directives subselections hselection

theorem
    selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {parentType responseName childType : Name}
    {typeConditions : List Name} (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> selectionSetTypeConditionFeasible schema childType typeConditions
            subselections)
      -> selectionSetTypeConditionFeasible schema childType typeConditions
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)) := by
  intro hfields
  apply selectionSetTypeConditionFeasible_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType
      responseName selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
    (schema : Schema) (parentType responseName : Name)
    : schema.objectType parentType
      -> objectSatisfiesTypeConditionStack schema parentType typeConditions
      -> ∀ selectionSet,
          selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
          -> ∀ fieldName arguments directives subselections fieldDefinition childType,
              Selection.field responseName fieldName arguments directives subselections
                ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                    selectionSet
              -> schema.lookupField parentType fieldName = some fieldDefinition
              -> childType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
              -> selectionSetTypeConditionFeasible schema childType [childType]
                  subselections
  | hobject, hstack, [], hfeasible, fieldName, arguments, directives,
      subselections, fieldDefinition, childType, hfield, _hlookup,
      _hchildType => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | hobject, hstack, selection :: rest, hfeasible, fieldName, arguments,
      directives, subselections, fieldDefinition, childType, hfield,
      hlookup, hchildType => by
      have hhead :
          selectionTypeConditionFeasible schema parentType typeConditions
             selection := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have htail :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.2
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hfield | htailField
            · rcases hfield with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              exact
                selectionTypeConditionFeasible_field_child_branch_forObject
                  schema hhead hstack hlookup hchildType
            · exact
                fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
                  schema parentType responseName hobject hstack rest htail
                  fieldName arguments directives subselections fieldDefinition
                  childType htailField hlookup hchildType
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
                schema parentType responseName hobject hstack rest htail
                fieldName arguments directives subselections fieldDefinition
                childType hfield hlookup hchildType
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbody | htailField
              · exact
                  fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
                    schema parentType responseName hobject hstack selectionSet
                    hhead fieldName arguments directives subselections
                    fieldDefinition childType hbody hlookup hchildType
              · exact
                  fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
                    schema parentType responseName hobject hstack rest htail
                    fieldName arguments directives subselections
                    fieldDefinition childType htailField hlookup hchildType
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hstackBody :
                    objectSatisfiesTypeConditionStack schema parentType
                      (typeCondition :: typeConditions) :=
                  objectSatisfiesTypeConditionStack_cons_of_overlap_forValidity
                    schema hobject hstack hoverlap
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbody | htailField
                · exact
                    fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
                      schema parentType responseName hobject hstackBody
                      selectionSet hhead fieldName arguments directives
                      subselections fieldDefinition childType hbody hlookup
                      hchildType
                · exact
                    fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
                      schema parentType responseName hobject hstack rest htail
                      fieldName arguments directives subselections
                      fieldDefinition childType htailField hlookup hchildType
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
                    schema parentType responseName hobject hstack rest htail
                  fieldName arguments directives subselections fieldDefinition
                    childType hfield hlookup hchildType

theorem fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> ∀ fieldName arguments directives subselections fieldDefinition,
            Selection.field responseName fieldName arguments directives subselections
              ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                  selectionSet
            -> schema.lookupField parentType fieldName = some fieldDefinition
            -> subselections ≠ []
            -> schema.getPossibleTypes fieldDefinition.outputType.namedType ≠ []
  | [], _hfeasible, fieldName, arguments, directives, subselections,
      fieldDefinition, hfield, _hlookup, _hnonempty => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, hfeasible, fieldName, arguments, directives,
      subselections, fieldDefinition, hfield, hlookup, hnonempty => by
      have hhead :
          selectionTypeConditionFeasible schema parentType typeConditions
            selection := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have htail :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            rest := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.2
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hmatched | htailField
            · rcases hmatched with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              cases matchedSubselections with
              | nil =>
                  exact False.elim (hnonempty rfl)
              | cons child children =>
                  have hchildFeasible := hhead.2
                  rw [hlookup] at hchildFeasible
                  exact hchildFeasible.1
            · exact
                fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                  schema parentType responseName rest htail fieldName
                  arguments directives subselections fieldDefinition
                  htailField hlookup hnonempty
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                schema parentType responseName rest htail fieldName
                arguments directives subselections fieldDefinition
                hfield hlookup hnonempty
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbody | htailField
              · exact
                  fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                    schema parentType responseName selectionSet hhead fieldName
                    arguments directives subselections fieldDefinition
                    hbody hlookup hnonempty
              · exact
                  fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                    schema parentType responseName rest htail fieldName
                    arguments directives subselections fieldDefinition
                    htailField hlookup hnonempty
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbody | htailField
                · exact
                    fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                      schema parentType responseName selectionSet hhead fieldName
                      arguments directives subselections fieldDefinition
                      hbody hlookup hnonempty
                · exact
                    fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                      schema parentType responseName rest htail fieldName
                      arguments directives subselections fieldDefinition
                      htailField hlookup hnonempty
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition = false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_child_possibleTypes_nonempty
                    schema parentType responseName rest htail fieldName
                    arguments directives subselections fieldDefinition
                    hfield hlookup hnonempty

mutual
  theorem typeConditionStackFeasible_of_selectionContains_forValidity
      (schema : Schema) (typeConditions : List Name)
      : ∀ selection,
          selectionContainsTypeConditionFeasibleField schema typeConditions selection
          -> typeConditionStackFeasible schema typeConditions
    | .field _responseName _fieldName _arguments _directives _selectionSet,
      hfeasible => hfeasible
    | .inlineFragment none _directives selectionSet, hfeasible =>
        typeConditionStackFeasible_of_selectionSetContains_forValidity schema
          typeConditions selectionSet hfeasible
    | .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible =>
        typeConditionStackFeasible_of_subset_forValidity
          (typeConditionStackFeasible_of_selectionSetContains_forValidity
            schema (typeCondition :: typeConditions) selectionSet
            hfeasible)
          (fun _candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)

  theorem typeConditionStackFeasible_of_selectionSetContains_forValidity
      (schema : Schema) (typeConditions : List Name)
      : ∀ selectionSet,
          selectionSetContainsTypeConditionFeasibleField schema typeConditions
            selectionSet
          -> typeConditionStackFeasible schema typeConditions
    | [], hfeasible => by
        cases hfeasible
    | selection :: rest, hfeasible => by
        rcases hfeasible with hhead | htail
        · exact typeConditionStackFeasible_of_selectionContains_forValidity
            schema typeConditions selection hhead
        · exact typeConditionStackFeasible_of_selectionSetContains_forValidity
            schema typeConditions rest htail
end

mutual
  theorem selectionContainsTypeConditionFeasibleField_replace_base_with_object
      (schema : Schema)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (baseType : Name) (conditions : List Name)
      : ∀ selection,
          selectionContainsTypeConditionFeasibleField schema
            (conditions ++ [baseType]) selection
          -> ∃ objectType,
              objectType ∈ schema.getPossibleTypes baseType
              ∧ schema.objectType objectType
              ∧ selectionContainsTypeConditionFeasibleField schema
                  (conditions ++ [objectType]) selection
    | .field _responseName _fieldName _arguments _directives _selectionSet,
      hfeasible => by
        rcases hfeasible with ⟨objectType, hobjectType⟩
        have hbase :
            objectType ∈ schema.getPossibleTypes baseType :=
          hobjectType baseType (by simp)
        have hobject :
            schema.objectType objectType :=
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema baseType objectType hbase
        refine ⟨objectType, hbase, hobject, ?_⟩
        exact ⟨objectType, by
          intro typeCondition hmem
          rcases List.mem_append.mp hmem with hconditions | hlast
          · exact hobjectType typeCondition
              (List.mem_append_left [baseType] hconditions)
          · have heq : typeCondition = objectType := by simpa using hlast
            subst typeCondition
            exact object_typeIncludesObject_self schema hobject⟩
    | .inlineFragment none _directives selectionSet, hfeasible => by
        rcases
          selectionSetContainsTypeConditionFeasibleField_replace_base_with_object
            schema hschema baseType conditions selectionSet hfeasible with
          ⟨objectType, hbase, hobject, hbody⟩
        exact ⟨objectType, hbase, hobject, hbody⟩
    | .inlineFragment (some typeCondition) _directives selectionSet,
      hfeasible => by
        rcases
          selectionSetContainsTypeConditionFeasibleField_replace_base_with_object
            schema hschema baseType (typeCondition :: conditions) selectionSet
            (by
              simpa [selectionContainsTypeConditionFeasibleField] using
                hfeasible) with
          ⟨objectType, hbase, hobject, hbody⟩
        refine ⟨objectType, hbase, hobject, ?_⟩
        simpa [selectionContainsTypeConditionFeasibleField] using hbody

  theorem selectionSetContainsTypeConditionFeasibleField_replace_base_with_object
      (schema : Schema)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (baseType : Name) (conditions : List Name)
      : ∀ selectionSet,
          selectionSetContainsTypeConditionFeasibleField schema
            (conditions ++ [baseType]) selectionSet
          -> ∃ objectType,
              objectType ∈ schema.getPossibleTypes baseType
              ∧ schema.objectType objectType
              ∧ selectionSetContainsTypeConditionFeasibleField schema
                  (conditions ++ [objectType]) selectionSet
    | [], hfeasible => by
        cases hfeasible
    | selection :: rest, hfeasible => by
        rcases hfeasible with hhead | htail
        · rcases
            selectionContainsTypeConditionFeasibleField_replace_base_with_object
              schema hschema baseType conditions selection hhead with
            ⟨objectType, hbase, hobject, hselection⟩
          exact ⟨objectType, hbase, hobject, Or.inl hselection⟩
        · rcases
            selectionSetContainsTypeConditionFeasibleField_replace_base_with_object
              schema hschema baseType conditions rest htail with
            ⟨objectType, hbase, hobject, hrest⟩
          exact ⟨objectType, hbase, hobject, Or.inr hrest⟩
end

theorem typesOverlapBool_eq_true_of_object_stack_feasible_forValidity
    (schema : Schema) {parentType typeCondition : Name}
    {typeConditions : List Name}
    : schema.objectType parentType
      -> typeConditionStackFeasible schema (typeCondition :: parentType :: typeConditions)
      -> schema.typesOverlapBool parentType typeCondition = true := by
  intro hobject hfeasible
  rcases hfeasible with ⟨objectType, hobjectType⟩
  have hparentMem :
      objectType ∈ schema.getPossibleTypes parentType :=
    hobjectType parentType (by simp)
  have hobjectEq : objectType = parentType :=
    object_typeIncludesObjectBool_eq_self schema hobject
      (List.contains_iff_mem.mpr hparentMem)
  subst objectType
  exact typesOverlapBool_eq_true_of_typesOverlap schema
    ⟨parentType, object_typeIncludesObject_self schema hobject,
      hobjectType typeCondition (by simp)⟩

theorem normalizeSelectionSet_ne_nil_of_contains (schema : Schema)
    : ∀ parentType selectionSet,
        schema.objectType parentType
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> selectionSetContainsTypeConditionFeasibleField schema [parentType] selectionSet
        -> normalizeSelectionSet schema parentType selectionSet ≠ [] := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _hobject _hready hcontains
      cases hcontains
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup _hrest =>
      intro _hobject hready _hcontains
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments directives
            subselections :: rest)
          hready
      exact False.elim
        (selectionSetLookupValid_field_head_lookup_none_false hlookupValid
          hlookup)
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType _hrest _hmerged _hpossible =>
      intro _hobject _hready _hcontains
      simp [normalizeSelectionSet, hlookup]
  | case4 parentType rest directives subselections happend =>
      intro hobject hready hcontains
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment none directives subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hsubselectionsReady :
          selectionSetSemanticsReady schema parentType subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      have hrestReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have happendReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hsubselectionsReady hrestReady
      have happendContains :
          selectionSetContainsTypeConditionFeasibleField schema [parentType]
            (subselections ++ rest) := by
        rcases hcontains with hhead | htail
        · exact selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
            schema [parentType] hhead
        · exact selectionSetContainsTypeConditionFeasibleField_append_right_forValidity
            schema [parentType] subselections htail
      simpa [normalizeSelectionSet] using
        happend hobject happendReady happendContains
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro hobject hready hcontains
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) directives
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hsubselectionsReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have hrestReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have happendReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hsubselectionsReady hrestReady
      have happendContains :
          selectionSetContainsTypeConditionFeasibleField schema [parentType]
            (subselections ++ rest) := by
        rcases hcontains with hhead | htail
        · have hsubselectionsContains :
              selectionSetContainsTypeConditionFeasibleField schema [parentType]
                subselections :=
            selectionSetContainsTypeConditionFeasibleField_of_subset_forValidity
              schema
              (fun candidate hcandidate =>
                List.mem_cons_of_mem typeCondition hcandidate)
              subselections hhead
          exact selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
            schema [parentType] hsubselectionsContains
        · exact selectionSetContainsTypeConditionFeasibleField_append_right_forValidity
            schema [parentType] subselections htail
      simpa [normalizeSelectionSet, hoverlap] using
        happend hobject happendReady happendContains
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro hobject hready hcontains
      have hrestReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · exact False.elim (hoverlap hmatch)
      rcases hcontains with hhead | htail
      · have hstack :
            typeConditionStackFeasible schema [typeCondition, parentType] :=
          typeConditionStackFeasible_of_selectionSetContains_forValidity
            schema [typeCondition, parentType] subselections hhead
        have hoverlapTrue :
            schema.typesOverlapBool parentType typeCondition = true :=
          typesOverlapBool_eq_true_of_object_stack_feasible_forValidity
            schema hobject hstack
        simp [hfalse] at hoverlapTrue
      · simpa [normalizeSelectionSet, hfalse] using
          hrest hobject hrestReady htail

theorem normalizeSelectionSet_ne_nil_of_everyNormalizerScope
    (schema : Schema)
    (hfeasibleAll : selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema)
    : ∀ parentType selectionSet,
        schema.objectType parentType
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> selectionSet ≠ []
        -> normalizeSelectionSet schema parentType selectionSet ≠ [] := by
  intro parentType selectionSet hobject hready hnonempty
  exact normalizeSelectionSet_ne_nil_of_contains schema parentType selectionSet
    hobject hready (hfeasibleAll parentType selectionSet hnonempty).1

end GroundTypeNormalization

end NormalForm

end GraphQL
