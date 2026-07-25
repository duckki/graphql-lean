import GraphQL.NamedFragment.Execution
import GraphQL.NamedFragment.Validation
import GraphQL.SchemaWellFormedness

/-! Named-fragment inlining for the fragment-aware syntax. -/

namespace GraphQL
namespace NamedFragment
namespace Inline

mutual
  def inlineSelection : List FragmentDefinition -> Selection -> Selection
    | fragments, .field responseName fieldName arguments directives selectionSet =>
        .field responseName fieldName arguments directives
          (inlineSelectionSet fragments selectionSet)
    | fragments, .inlineFragment typeCondition directives selectionSet =>
        .inlineFragment typeCondition directives
          (inlineSelectionSet fragments selectionSet)
    | fragments, .fragmentSpread fragmentName directives =>
        match lookupFragmentAndRestLt? fragmentName fragments with
        | none => .inlineFragment none directives []
        | some (fragment, remainingFragments) =>
            .inlineFragment (some fragment.typeCondition) directives
              (inlineSelectionSet remainingFragments.val fragment.selectionSet)
  termination_by fragments selection => (fragments.length, sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst fragments
      simp_wf
      try
        first
        | apply Prod.Lex.left
          exact remainingFragments.property
        | apply Prod.Lex.right
          apply Prod.Lex.left
          omega
        | apply Prod.Lex.right
          apply Prod.Lex.right
          omega

  def inlineSelectionSet : List FragmentDefinition -> List Selection -> List Selection
    | _fragments, [] => []
    | fragments, selection :: rest =>
        inlineSelection fragments selection :: inlineSelectionSet fragments rest
  termination_by fragments selectionSet => (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      try subst fragments
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

def inlineOperation (operation : Operation) : Operation :=
  {
    operation with
      fragmentDefinitions := []
      selectionSet :=
        inlineSelectionSet operation.fragmentDefinitions operation.selectionSet
  }

end Inline

namespace Semantics

mutual
  def selectionInlined : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetInlined selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetInlined selectionSet
    | .fragmentSpread _fragmentName _directives => False

  def selectionSetInlined : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionInlined selection ∧ selectionSetInlined rest
end

def operationInlined (operation : Operation) : Prop :=
  operation.fragmentDefinitions = [] ∧ selectionSetInlined operation.selectionSet

-- Inlining always produces an operation with no fragment definitions or
-- fragment spreads.
-- Witness: `GraphQL.NamedFragment.Semantics.inlineOperation_inlined`.
def inlineOperationInlined (operation : Operation) : Prop :=
  operationInlined (Inline.inlineOperation operation)

-- Inlining preserves fragment-aware execution semantics.
-- Witness: `GraphQL.NamedFragment.Semantics.fragmentAwareExecutionEquivalentToInline_holds`.
def fragmentAwareExecutionEquivalentToInline (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation
  -> operationsEquivalent schema operation (Inline.inlineOperation operation)

-- Inlining preserves named-fragment operation validity.
-- Witness: `GraphQL.NamedFragment.Semantics.fragmentAwareValidityPreservedToInline_holds`.
def fragmentAwareValidityPreservedToInline (schema : Schema) (operation : Operation)
    : Prop :=
  GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation
  -> GraphQL.NamedFragment.Validation.operationDefinitionValid schema
      (Inline.inlineOperation operation)

end Semantics
end NamedFragment
end GraphQL
