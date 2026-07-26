import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.Feasibility

/-!
Feasibility helpers for ground-type normal-form uniqueness.

The syntactic diff theorem is intentionally independent of validity and
semantics.  Semantic separation needs one more ingredient: a selected normal
subtree must contain a field that can be reached through its enclosing
type-condition stack.  This module packages that proof-only obligation and
small projections from the existing feasibility predicates.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def selectionSetObservableInScope
    (schema : Schema) (parentType : Name)
    (selectionSet : List Selection)
    : Prop :=
  selectionSet ≠ []
  -> selectionSetContainsTypeConditionFeasibleField schema [parentType] selectionSet

def selectionSetFeasibleInScope
    (schema : Schema) (parentType : Name)
    (selectionSet : List Selection)
    : Prop :=
  selectionSetObservableInScope schema parentType selectionSet
  ∧ selectionSetTypeConditionFeasible schema parentType [parentType]
      .allFields selectionSet

theorem selectionSet_nonempty_of_containsTypeConditionFeasibleField
    {schema : Schema} {typeConditions : List Name}
    {selectionSet : List Selection}
    : selectionSetContainsTypeConditionFeasibleField schema typeConditions selectionSet
      -> selectionSet ≠ [] := by
  intro hcontains hempty
  subst selectionSet
  cases hcontains

theorem selectionSetContainsTypeConditionFeasibleField_of_feasible_nonempty
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetFeasibleInScope schema parentType selectionSet
      -> selectionSet ≠ []
      -> selectionSetContainsTypeConditionFeasibleField schema [parentType]
          selectionSet := by
  intro hfeasible hnonempty
  exact hfeasible.1 hnonempty

theorem selectionSetObservableInScope_of_contains
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetContainsTypeConditionFeasibleField schema [parentType] selectionSet
      -> selectionSetObservableInScope schema parentType selectionSet := by
  intro hcontains _hnonempty
  exact hcontains

theorem selectionSetObservableInScope_of_existsMode
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetTypeConditionFeasible schema parentType [parentType]
        .existsField selectionSet
      -> selectionSetObservableInScope schema parentType selectionSet := by
  intro hfeasible
  exact selectionSetObservableInScope_of_contains
    (selectionSetContainsTypeConditionFeasibleField_of_existsMode schema
      parentType [parentType] selectionSet hfeasible)

theorem selectionSetFeasibleInScope_of_everyNormalizerScope
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema
      -> selectionSetFeasibleInScope schema parentType selectionSet := by
  intro hfeasibleAll
  constructor
  · intro hnonempty
    exact (hfeasibleAll parentType selectionSet hnonempty).1
  · by_cases hnonempty : selectionSet ≠ []
    · exact (hfeasibleAll parentType selectionSet hnonempty).2
    · have hempty : selectionSet = [] := by
        exact Classical.not_not.mp hnonempty
      subst selectionSet
      simp [selectionSetTypeConditionFeasible]

theorem selectionSetFeasibleInScope_of_operationTypeConditionFeasible
    {schema : Schema} {operation : Operation}
    : operationTypeConditionFeasible schema operation
      -> selectionSetFeasibleInScope schema operation.rootType
          operation.selectionSet := by
  intro hfeasible
  exact
    ⟨selectionSetObservableInScope_of_existsMode hfeasible.1,
      hfeasible.2⟩

theorem selectionSetTypeConditionFeasible_allFields_of_mem
    {schema : Schema} {parentType : Name}
    {typeConditions : List Name} {selectionSet : List Selection}
    {selection : Selection}
    : selectionSetTypeConditionFeasible schema parentType typeConditions
        .allFields selectionSet
      -> selection ∈ selectionSet
      -> selectionTypeConditionFeasible schema parentType typeConditions
          .allFields selection := by
  intro hfeasible hmem
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst selection
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      · exact ih (by
          simpa [selectionSetTypeConditionFeasible] using hfeasible.2) htail

theorem selectionSetTypeConditionFeasible_field_child_existsMode_of_mem
    {schema : Schema} {parentType : Name}
    {typeConditions : List Name} {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetTypeConditionFeasible schema parentType typeConditions
        .allFields selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> typeConditionStackFeasible schema typeConditions
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> childSelectionSet ≠ []
      -> selectionSetTypeConditionFeasible schema
          fieldDefinition.outputType.namedType [fieldDefinition.outputType.namedType]
          .existsField childSelectionSet := by
  intro hfeasible hmem hstack hlookup hnonempty
  have hfield :
      selectionTypeConditionFeasible schema parentType typeConditions
        .allFields
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    selectionSetTypeConditionFeasible_allFields_of_mem hfeasible hmem
  cases childSelectionSet with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons child rest =>
      have hobligation :
          typeConditionStackFeasible schema typeConditions ->
            selectionSetTypeConditionFeasible schema
              fieldDefinition.outputType.namedType
              [fieldDefinition.outputType.namedType] .existsField
              (child :: rest)
              ∧ ∀ objectType,
                objectType ∈
                    schema.getPossibleTypes
                      fieldDefinition.outputType.namedType ->
                  selectionSetTypeConditionFeasible schema objectType
                    [objectType] .allFields (child :: rest) := by
        simpa [selectionTypeConditionFeasible, hlookup] using hfield
      exact (hobligation hstack).1

theorem selectionSetObservableInScope_field_child_of_mem
    {schema : Schema} {parentType : Name}
    {typeConditions : List Name} {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetTypeConditionFeasible schema parentType typeConditions
        .allFields selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> typeConditionStackFeasible schema typeConditions
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSetObservableInScope schema
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hfeasible hmem hstack hlookup hnonempty
  exact (selectionSetObservableInScope_of_existsMode
    (selectionSetTypeConditionFeasible_field_child_existsMode_of_mem
      hfeasible hmem hstack hlookup hnonempty)) hnonempty

theorem selectionSetObservableInScope_field_child_of_feasible_mem
    {schema : Schema} {parentType : Name}
    {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetFeasibleInScope schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema parentType = true
      -> selectionSetObservableInScope schema
          fieldDefinition.outputType.namedType childSelectionSet := by
  intro hfeasible hmem hlookup hparentObject
  exact
    selectionSetObservableInScope_field_child_of_mem hfeasible.2 hmem
      (by
        exact
          typeConditionStackFeasible_of_objectSatisfies_forValidity
            (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
              schema
              (objectType_of_objectTypeNameBool_eq_true
                (typeName := parentType) schema hparentObject)))
      hlookup

theorem selectionSetFeasibleInScope_object_field_child_of_mem
    {schema : Schema} {parentType : Name}
    {selectionSet : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetFeasibleInScope schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema parentType = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> selectionSetFeasibleInScope schema fieldDefinition.outputType.namedType
          childSelectionSet := by
  intro hfeasible hmem hlookup hparentObject hobject
  constructor
  · exact
      selectionSetObservableInScope_field_child_of_mem hfeasible.2 hmem
        (by
          exact
            typeConditionStackFeasible_of_objectSatisfies_forValidity
              (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema
                (objectType_of_objectTypeNameBool_eq_true
                  (typeName := parentType) schema hparentObject)))
        hlookup
  · have hfield :
        selectionTypeConditionFeasible schema parentType [parentType]
          .allFields
          (Selection.field responseName fieldName arguments directives
            childSelectionSet) :=
      selectionSetTypeConditionFeasible_allFields_of_mem hfeasible.2 hmem
    exact
      selectionTypeConditionFeasible_field_child_branch_forObject schema
        hfield
        (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
          schema
          (objectType_of_objectTypeNameBool_eq_true
            (typeName := parentType) schema hparentObject))
        hlookup
        (List.contains_iff_mem.mp
          (object_typeIncludesObjectBool_self schema
            (objectType_of_objectTypeNameBool_eq_true
              (typeName := fieldDefinition.outputType.namedType) schema
              hobject)))

theorem selectionSetTypeConditionFeasible_field_child_branch_of_feasible_mem
    {schema : Schema} {parentType : Name}
    {selectionSet : List Selection}
    {responseName fieldName runtimeType : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetFeasibleInScope schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema parentType = true
      -> runtimeType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> selectionSetTypeConditionFeasible schema runtimeType [runtimeType]
          .allFields childSelectionSet := by
  intro hfeasible hmem hlookup hparentObject hruntime
  have hfield :
      selectionTypeConditionFeasible schema parentType [parentType]
        .allFields
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    selectionSetTypeConditionFeasible_allFields_of_mem hfeasible.2 hmem
  exact
    selectionTypeConditionFeasible_field_child_branch_forObject schema
      hfield
      (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
        schema
        (objectType_of_objectTypeNameBool_eq_true
          (typeName := parentType) schema hparentObject))
      hlookup hruntime

theorem selectionSetTypeConditionFeasible_field_child_branch_of_feasible_mem_bool
    {schema : Schema} {parentType : Name}
    {selectionSet : List Selection}
    {responseName fieldName runtimeType : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : selectionSetFeasibleInScope schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema parentType = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> selectionSetTypeConditionFeasible schema runtimeType [runtimeType]
          .allFields childSelectionSet := by
  intro hfeasible hmem hlookup hparentObject hinclude
  exact
    selectionSetTypeConditionFeasible_field_child_branch_of_feasible_mem
      hfeasible hmem hlookup hparentObject
      (List.contains_iff_mem.mp hinclude)

end GroundTypeNormalization

end NormalForm

end GraphQL
