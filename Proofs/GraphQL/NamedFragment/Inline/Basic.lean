import GraphQL.NamedFragment.Inline

/-! Basic facts about named-fragment inlining. -/

namespace GraphQL
namespace NamedFragment
namespace Inline

@[simp]
theorem inlineSelectionSet_empty (fragments : List FragmentDefinition)
    : inlineSelectionSet fragments [] = [] := by
  cases fragments <;> simp [inlineSelectionSet]

theorem inlineSelectionSet_nil (selectionSet : List Selection)
    : inlineSelectionSet [] selectionSet = selectionSet.map (inlineSelection []) := by
  induction selectionSet with
  | nil => simp
  | cons selection rest ih =>
      simp [inlineSelectionSet, ih]

theorem inlineSelection_nil (selection : Selection)
    : inlineSelection [] selection
      = match selection with
        | .field responseName fieldName arguments directives selectionSet =>
            .field responseName fieldName arguments directives
              (inlineSelectionSet [] selectionSet)
        | .inlineFragment typeCondition directives selectionSet =>
            .inlineFragment typeCondition directives (inlineSelectionSet [] selectionSet)
        | .fragmentSpread _fragmentName directives =>
            .inlineFragment none directives [] := by
  cases selection <;> simp [inlineSelection, lookupFragmentAndRestLt?]

end Inline
end NamedFragment
end GraphQL
