import Proofs.GraphQL.NamedFragment.Inline.Basic

/-! Direct-execution proof witnesses for fragment-free named-fragment operations. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

mutual
  theorem inlineSelection_inlined
      : ∀ (fragments : List FragmentDefinition) (selection : Selection),
          selectionInlined (Inline.inlineSelection fragments selection)
    | fragments, .field responseName fieldName arguments directives selectionSet => by
        simp [Inline.inlineSelection, selectionInlined,
          inlineSelectionSet_inlined fragments selectionSet]
    | fragments, .inlineFragment typeCondition directives selectionSet => by
        simp [Inline.inlineSelection, selectionInlined,
          inlineSelectionSet_inlined fragments selectionSet]
    | fragments, .fragmentSpread fragmentName directives => by
        simp [Inline.inlineSelection]
        cases hlookup : lookupFragmentAndRestLt? fragmentName fragments with
        | none =>
            simp [selectionInlined, selectionSetInlined]
        | some pair =>
            cases pair with
            | mk fragment remainingFragments =>
                simp [selectionInlined,
                  inlineSelectionSet_inlined remainingFragments.val
                    fragment.selectionSet]
  termination_by fragments selection => (fragments.length, sizeOf selection, 0)
  decreasing_by
    all_goals
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

  theorem inlineSelectionSet_inlined
      : ∀ (fragments : List FragmentDefinition) (selectionSet : List Selection),
          selectionSetInlined (Inline.inlineSelectionSet fragments selectionSet)
    | fragments, [] => by
        simp [selectionSetInlined]
    | fragments, selection :: rest => by
        simp [Inline.inlineSelectionSet, selectionSetInlined,
          inlineSelection_inlined fragments selection,
          inlineSelectionSet_inlined fragments rest]
  termination_by fragments selectionSet => (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

mutual
  theorem inlineSelection_eq_of_inlined (fragments : List FragmentDefinition)
      : ∀ selection,
          selectionInlined selection
          -> Inline.inlineSelection fragments selection = selection
    | .field responseName fieldName arguments directives selectionSet, hinlined => by
        simp [selectionInlined] at hinlined
        simp [Inline.inlineSelection,
          inlineSelectionSet_eq_of_inlined fragments selectionSet hinlined]
    | .inlineFragment typeCondition directives selectionSet, hinlined => by
        simp [selectionInlined] at hinlined
        simp [Inline.inlineSelection,
          inlineSelectionSet_eq_of_inlined fragments selectionSet hinlined]
    | .fragmentSpread fragmentName directives, hinlined => by
        simp [selectionInlined] at hinlined

  theorem inlineSelectionSet_eq_of_inlined (fragments : List FragmentDefinition)
      : ∀ selectionSet,
          selectionSetInlined selectionSet
          -> Inline.inlineSelectionSet fragments selectionSet = selectionSet
    | [], _hinlined => by
        simp
    | selection :: rest, hinlined => by
        simp [selectionSetInlined] at hinlined
        rcases hinlined with ⟨hselection, hrest⟩
        simp [Inline.inlineSelectionSet,
          inlineSelection_eq_of_inlined fragments selection hselection,
          inlineSelectionSet_eq_of_inlined fragments rest hrest]
end

theorem inlineOperation_fragmentDefinitions (operation : Operation)
    : (Inline.inlineOperation operation).fragmentDefinitions = [] := by
  cases operation
  rfl

theorem inlineOperation_idem (operation : Operation)
    : Inline.inlineOperation (Inline.inlineOperation operation)
      = Inline.inlineOperation operation := by
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      simp [Inline.inlineOperation]
      exact inlineSelectionSet_eq_of_inlined []
        (Inline.inlineSelectionSet fragmentDefinitions selectionSet)
        (inlineSelectionSet_inlined fragmentDefinitions selectionSet)

theorem inlineOperation_eq_of_inlined
    (operation : Operation)
    (hinlined : operationInlined operation)
    : Inline.inlineOperation operation = operation := by
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      rcases hinlined with ⟨hfragments, hselectionSet⟩
      simp at hfragments hselectionSet
      subst fragmentDefinitions
      simp [Inline.inlineOperation]
      exact inlineSelectionSet_eq_of_inlined [] selectionSet hselectionSet

theorem inlineOperation_inlined (operation : Operation)
    : operationInlined (Inline.inlineOperation operation) := by
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      constructor
      · rfl
      · exact inlineSelectionSet_inlined fragmentDefinitions selectionSet

mutual
  theorem selectionVariables_inlineSelection
      : ∀ (fragments : List FragmentDefinition) (selection : Selection),
          GraphQL.NamedFragment.Validation.selectionVariables []
            (Inline.inlineSelection fragments selection)
          = GraphQL.NamedFragment.Validation.selectionVariables fragments selection
    | fragments,
        .field responseName fieldName arguments directives selectionSet => by
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionVariables,
          selectionSetVariables_inlineSelectionSet fragments selectionSet]
    | fragments, .inlineFragment typeCondition directives selectionSet => by
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionVariables,
          selectionSetVariables_inlineSelectionSet fragments selectionSet]
    | fragments, .fragmentSpread fragmentName directives => by
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionVariables]
        cases hlookup : lookupFragmentAndRestLt? fragmentName fragments with
        | none =>
            simp [GraphQL.NamedFragment.Validation.selectionVariables,
              GraphQL.NamedFragment.Validation.selectionSetVariables]
        | some pair =>
            cases pair with
            | mk fragment remainingFragments =>
                simp [GraphQL.NamedFragment.Validation.selectionVariables,
                  selectionSetVariables_inlineSelectionSet
                    remainingFragments.val fragment.selectionSet]
  termination_by fragments selection => (fragments.length, sizeOf selection, 0)
  decreasing_by
    all_goals
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

  theorem selectionSetVariables_inlineSelectionSet
      : ∀ (fragments : List FragmentDefinition) (selectionSet : List Selection),
          GraphQL.NamedFragment.Validation.selectionSetVariables []
            (Inline.inlineSelectionSet fragments selectionSet)
          = GraphQL.NamedFragment.Validation.selectionSetVariables fragments selectionSet
    | fragments, [] => by
        simp [GraphQL.NamedFragment.Validation.selectionSetVariables]
    | fragments, selection :: rest => by
        simp [Inline.inlineSelectionSet,
          GraphQL.NamedFragment.Validation.selectionSetVariables,
          selectionVariables_inlineSelection fragments selection,
          selectionSetVariables_inlineSelectionSet fragments rest]
  termination_by fragments selectionSet => (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

theorem inlineOperation_operationVariablesUsed
    {operation : Operation}
    (hused : GraphQL.NamedFragment.Validation.operationVariablesUsed operation)
    : GraphQL.NamedFragment.Validation.operationVariablesUsed
        (Inline.inlineOperation operation) := by
  intro variableDefinition hvariableDefinition
  have husedName := hused variableDefinition (by
    simpa [Inline.inlineOperation] using hvariableDefinition)
  simpa [Inline.inlineOperation,
    selectionSetVariables_inlineSelectionSet] using husedName

end Semantics
end NamedFragment
end GraphQL
