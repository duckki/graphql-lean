import Proofs.GraphQL.NamedFragment.Semantics.Inline.Operation

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

end Semantics
end NamedFragment
end GraphQL
