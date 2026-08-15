import GraphQL.Execution
import GraphQL.SchemaWellFormedness
import GraphQL.Theories.ConditionTree.Termination
import GraphQL.Validation

/-! Condition-tree reduction back into GraphQL selection syntax.

Reduction extracts the current condition tree, traverses its field groups and branches,
and constructs another tree from every merged field-group child selection set. This is
the same tree-of-trees recursion shape used by condition-tree execution.
-/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution
open Termination

-----------------------------------------------------------------------------------------
-- Recursive reduction
-----------------------------------------------------------------------------------------

private theorem mergedFields_responseDepth_lt
    (responseName : Name) (first : Field) (rest : List Field)
    : selectionSetResponseDepth ((first :: rest).flatMap Field.selectionSet)
      < selectionSetResponseDepth
          ((first :: rest).map (Field.toSelection responseName)) := by
  induction rest generalizing first with
  | nil =>
      simp [selectionSetResponseDepth, selectionResponseDepth, Field.toSelection]
  | cons next tail ih =>
      rw [List.flatMap_cons, selectionSetResponseDepth_append]
      simp only [List.map_cons, selectionSetResponseDepth, selectionResponseDepth,
        Field.toSelection]
      apply Nat.max_lt.mpr
      constructor
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
          (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih next) (by
          simpa only [List.map_cons, selectionSetResponseDepth,
            selectionResponseDepth, Field.toSelection] using
            (Nat.le_max_right
              (selectionSetResponseDepth first.selectionSet + 1)
              (selectionSetResponseDepth
                ((next :: tail).map (Field.toSelection responseName)))))

private theorem FieldGroup.mergedSelectionSet_responseDepth_lt (group : FieldGroup)
    : selectionSetResponseDepth group.mergedSelectionSet
      < conditionFieldGroupResponseDepth group := by
  simpa [FieldGroup.mergedSelectionSet, conditionFieldGroupResponseDepth,
    FieldGroup.fields, FieldGroup.selections, SelectionSet.mergeSelectionSets,
    List.flatMap_map, Function.comp_def, Field.toSelection,
    Selection.subselections] using
    mergedFields_responseDepth_lt group.responseName group.first group.rest

mutual
  -- Mirrors `executeSelectionSet`: traverse one extracted tree, and call `reduceTree` again only
  -- after constructing the merged child tree of a field group.
  def reduceTree (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      : List Selection :=
    reduceTreeFieldGroups schema parentType inheritedBooleanCondition tree.condition
      tree.fields
    ++ reduceTreeBranches schema parentType inheritedBooleanCondition tree.branches
  termination_by (conditionTreeResponseDepth tree, 0, sizeOf tree)
  decreasing_by
    all_goals
      apply triple_lt_of_depth_le_of_tail_lt
      · simp only [conditionTreeResponseDepth]
        first
        | exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_refl _)
        | exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_refl _)
      · cases tree
        simp_wf
        omega

  def reduceTreeFieldGroups (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
      : List FieldGroup -> List Selection
    | [] => []
    | group :: rest =>
        reduceTreeFieldGroup schema parentType inheritedBooleanCondition condition group
        ++ reduceTreeFieldGroups schema parentType inheritedBooleanCondition condition
            rest
  termination_by groups => (conditionFieldGroupsResponseDepth groups, 0, sizeOf groups)
  decreasing_by
    all_goals
      apply triple_lt_of_depth_le_of_tail_lt
      · first
        | exact Nat.le_max_left _ _
        | exact Nat.le_max_right _ _
      · simp_wf
        omega

  def reduceTreeFieldGroup (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
      (group : FieldGroup)
      : List Selection :=
    let field := group.first
    let childSelectionSet := group.mergedSelectionSet
    match schema.lookupField parentType field.fieldName with
    | none => group.selections
    | some fieldDefinition =>
        let childInheritedBooleanCondition :=
          (canonicalBooleanCondition
            (inheritedBooleanCondition ++ condition.booleanCondition)).getD
            inheritedBooleanCondition
        let childTree :=
          ofSelectionSetInScope schema fieldDefinition.outputType.namedType
            childInheritedBooleanCondition childSelectionSet
        [.field group.responseName field.fieldName field.arguments []
          (reduceTree schema fieldDefinition.outputType.namedType
            childInheritedBooleanCondition childTree)]
  termination_by (conditionFieldGroupResponseDepth group, 0, sizeOf group)
  decreasing_by
    apply Prod.Lex.left
    exact Nat.lt_of_le_of_lt
      (conditionTreeResponseDepth_ofSelectionSetInScope schema
        fieldDefinition.outputType.namedType childInheritedBooleanCondition
        childSelectionSet)
      group.mergedSelectionSet_responseDepth_lt

  def reduceTreeBranches (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      : List (Branch Tree) -> List Selection
    | [] => []
    | branch :: rest =>
        let branchParentType := branch.condition.parentType parentType
        branch.condition.toSelection
          (reduceTree schema branchParentType inheritedBooleanCondition branch.body)
        :: reduceTreeBranches schema parentType inheritedBooleanCondition rest
  termination_by branches => (conditionBranchesResponseDepth branches, 0, sizeOf branches)
  decreasing_by
    all_goals
      apply triple_lt_of_depth_le_of_tail_lt
      · simp only [conditionBranchesResponseDepth]
        first
        | exact Nat.le_max_left _ _
        | exact Nat.le_max_right _ _
      · cases branch
        simp_wf
        omega
end

-- Entry point for reduction syntax. Extraction creates the first tree; `reduceTree`
-- creates and reduces further trees at merged response-field boundaries.
def reduceInScope (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : List Selection :=
  let tree :=
    ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet
  reduceTree schema parentType inheritedBooleanCondition tree

def reduce (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    : List Selection :=
  reduceInScope schema parentType [] selectionSet

def reduceOperation (schema : Schema) (operation : Operation) : Operation :=
  {
    operation with
      selectionSet :=
        reduce schema (operation.rootType schema) operation.selectionSet
  }

-----------------------------------------------------------------------------------------
-- Reduction soundness
-----------------------------------------------------------------------------------------

-- Selection-set semantic preservation for reduction at a concrete execution boundary.
-- Merge validity matters because an invalid alias collision can make source order choose
-- a different representative field after tree reduction. Extraction and validation use
-- `parentType`, while execution uses any concrete runtime object admitted by that static
-- scope. The theorem witness is `ConditionTree.reduction_sound` in
-- `Proofs.GraphQL.Theories.ConditionTree.Reduce`.
def ReductionSound (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  ∀ (variableDefinitions : List VariableDefinition),
    SchemaWellFormedness.schemaWellFormed schema
    -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
    -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
    -> ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
          (variableValues : VariableValues) (fuel : Nat)
          (runtimeType : Name) (ref : ObjectRef),
        schema.typeIncludesObjectBool parentType runtimeType = true
        -> Response.semanticEquivalent
            (selectionSetResultToResponse
              (executeSelectionSet schema resolvers variableValues fuel runtimeType
                (.object runtimeType ref) selectionSet))
            (selectionSetResultToResponse
              (executeSelectionSet schema resolvers variableValues fuel runtimeType
                (.object runtimeType ref) (reduce schema parentType selectionSet)))

-- Operation-level semantic preservation for `reduceOperation`, at the same schema and
-- operation-validity boundary as condition-tree execution equivalence. Both operations
-- are run with the same explicit fuel so the statement does not hide a fuel-bound
-- comparison. The theorem witness is `ConditionTree.reduceOperation_sound` in
-- `Proofs.GraphQL.Theories.ConditionTree.Reduce`.
def ReduceOperationSound (schema : Schema) (operation : Operation) : Prop :=
  ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef),
    SchemaWellFormedness.schemaWellFormed schema
    -> Validation.operationDefinitionValid schema operation
    -> Response.semanticEquivalent
        (executeQueryWithFuel schema resolvers variableValues operation fuel source)
        (executeQueryWithFuel schema resolvers variableValues
          (reduceOperation schema operation) fuel source)

end ConditionTree
end GraphQL
