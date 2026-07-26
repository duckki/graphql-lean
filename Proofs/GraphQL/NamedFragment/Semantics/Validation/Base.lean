import Proofs.GraphQL.NamedFragment.Semantics.Inline

/-! Named-fragment validation preservation proofs. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

theorem inlineSelectionSet_nonempty
    {fragments : List FragmentDefinition} {selectionSet : List Selection}
    (hnonempty : selectionSet ≠ [])
    : Inline.inlineSelectionSet fragments selectionSet ≠ [] := by
  cases selectionSet with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons selection rest =>
      simp [Inline.inlineSelectionSet]

theorem inlineOperation_selectionSet_nonempty_of_valid
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    : (Inline.inlineOperation operation).selectionSet ≠ [] := by
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsValid, hselectionNonempty,
      _hselectionValid, _hmerge⟩
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      simp [Inline.inlineOperation]
      exact inlineSelectionSet_nonempty hselectionNonempty

end Semantics
end NamedFragment
end GraphQL
