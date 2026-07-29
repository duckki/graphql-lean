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
  ∧ selectionSetTypeConditionFeasible schema parentType [parentType] selectionSet

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

theorem selectionSetTypeConditionFeasible_allFields_of_mem
    {schema : Schema} {parentType : Name}
    {typeConditions : List Name} {selectionSet : List Selection}
    {selection : Selection}
    : selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
      -> selection ∈ selectionSet
      -> selectionTypeConditionFeasible schema parentType typeConditions selection := by
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
          childSelectionSet := by
  intro hfeasible hmem hlookup hparentObject hruntime
  have hfield :
      selectionTypeConditionFeasible schema parentType [parentType]

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
          childSelectionSet := by
  intro hfeasible hmem hlookup hparentObject hinclude
  exact
    selectionSetTypeConditionFeasible_field_child_branch_of_feasible_mem
      hfeasible hmem hlookup hparentObject
      (List.contains_iff_mem.mp hinclude)

end GroundTypeNormalization

end NormalForm

end GraphQL
