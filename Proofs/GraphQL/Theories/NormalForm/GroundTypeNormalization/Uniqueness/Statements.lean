import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Semantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Feasibility
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity

/-!
Theorem-facing selection-set semantic predicates and assumption bundles for
ground-type normal-form uniqueness.
-/

namespace GraphQL

namespace NormalForm

def selectionSetsSemanticallyEquivalent (schema : Schema)
    (parentType : Name) (left right : List Selection)
    : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues fuel (source : Execution.ResolverValue ObjectRef),
    (∃ runtimeType ref,
      source = Execution.ResolverValue.object runtimeType ref
      ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    -> Execution.Response.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left)
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source right)

namespace GroundTypeNormalization

def normalSelectionSetsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (parentType : Name)
    (left right : List Selection)
    : Prop :=
  selectionSetDirectiveFree left
  -> selectionSetDirectiveFree right
  -> selectionSetNormal schema parentType left
  -> selectionSetNormal schema parentType right
  -> SelectionSetEqualUpToReordering left right
  -> selectionSetsSemanticallyEquivalent schema parentType left right

def selectionSetsDataEquivalent (schema : Schema)
    (parentType : Name) (left right : List Selection)
    : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues fuel (source : Execution.ResolverValue ObjectRef),
    (∃ runtimeType ref,
      source = Execution.ResolverValue.object runtimeType ref
      ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    -> Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left).data
        (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source right).data

theorem selectionSetsDataEquivalent_of_selectionSetsSemanticallyEquivalent
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetsSemanticallyEquivalent schema parentType left right
      -> selectionSetsDataEquivalent schema parentType left right := by
  intro hsem ObjectRef resolvers variableValues fuel source hsource
  exact (hsem resolvers variableValues fuel source hsource).1

def normalSelectionSetsSemanticallyEquivalentEqualUpToReordering
    (schema : Schema) (parentType : Name)
    (left right : List Selection)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> selectionSetDirectiveFree left
  -> selectionSetDirectiveFree right
  -> selectionSetNormal schema parentType left
  -> selectionSetNormal schema parentType right
  -> selectionSetsSemanticallyEquivalent schema parentType left right
  -> SelectionSetEqualUpToReordering left right

def feasibleNormalSelectionSetsSemanticallyEquivalentEqualUpToReordering
    (schema : Schema) (parentType : Name)
    (left right : List Selection)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> selectionSetDirectiveFree left
  -> selectionSetDirectiveFree right
  -> selectionSetNormal schema parentType left
  -> selectionSetNormal schema parentType right
  -> selectionSetFeasibleInScope schema parentType left
  -> selectionSetFeasibleInScope schema parentType right
  -> selectionSetsSemanticallyEquivalent schema parentType left right
  -> SelectionSetEqualUpToReordering left right

def validNormalSelectionSetsSemanticallyEquivalentEqualUpToReordering
    (schema : Schema)
    (leftVariableDefinitions rightVariableDefinitions : List VariableDefinition)
    (parentType : Name) (left right : List Selection)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
  -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
  -> selectionSetDirectiveFree left
  -> selectionSetDirectiveFree right
  -> selectionSetNormal schema parentType left
  -> selectionSetNormal schema parentType right
  -> selectionSetsSemanticallyEquivalent schema parentType left right
  -> SelectionSetEqualUpToReordering left right

def normalSelectionSetsDataEquivalentEqualUpToReordering
    (schema : Schema) (parentType : Name)
    (left right : List Selection)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> selectionSetDirectiveFree left
  -> selectionSetDirectiveFree right
  -> selectionSetNormal schema parentType left
  -> selectionSetNormal schema parentType right
  -> selectionSetsDataEquivalent schema parentType left right
  -> SelectionSetEqualUpToReordering left right

def validSelectionSetsDataEquivalentEqualUpToReordering
    (schema : Schema)
    (leftVariableDefinitions rightVariableDefinitions : List VariableDefinition)
    (parentType : Name) (left right : List Selection)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
  -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
  -> selectionSetDirectiveFree left
  -> selectionSetDirectiveFree right
  -> selectionSetNormal schema parentType left
  -> selectionSetNormal schema parentType right
  -> selectionSetsDataEquivalent schema parentType left right
  -> SelectionSetEqualUpToReordering left right

end GroundTypeNormalization

end NormalForm

end GraphQL
