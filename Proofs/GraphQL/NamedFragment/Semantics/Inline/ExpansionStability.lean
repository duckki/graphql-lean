import Proofs.GraphQL.NamedFragment.Semantics.Validation.FragmentRemoval

/-!
For a valid acyclic fragment graph, removing fragments on the active ancestor path
does not change the static expansion of the fragment currently being entered. This is
the syntactic stability fact needed to compare two occurrences of one named fragment.
-/

namespace GraphQL
namespace NamedFragment
namespace Semantics

def selectionSpreadNamesWithin (selection : Selection) (selectionSet : List Selection)
    : Prop :=
  ∀ fragmentName,
    fragmentName ∈ GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames selection
    -> fragmentName
        ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames selectionSet

def selectionSetSpreadNamesWithin (nested selectionSet : List Selection) : Prop :=
  ∀ fragmentName,
    fragmentName ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames nested
    -> fragmentName
        ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames selectionSet

theorem fragmentSelectionSetValid_after_reachable_lookup_removal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {original current : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < current.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (hremovals : ReachableAncestorRemovals original fragmentName current current)
    (hlookupOriginal
      : GraphQL.NamedFragment.lookupFragment? original fragmentName = some fragment)
    (hlookup : lookupFragmentAndRestLt? fragmentName current = some (fragment, remaining))
    : GraphQL.NamedFragment.Validation.selectionSetValid schema variableDefinitions
        remaining.val fragment.typeCondition fragment.selectionSet := by
  have hfragmentMemCurrent : fragment ∈ current :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem hlookup
  have hfragmentMemOriginal : fragment ∈ original :=
    hremovals.mem_original hfragmentMemCurrent
  have hfragmentValidCurrent :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions current fragment :=
    fragmentDefinitionValid_after_reachable_ancestor_removals hacyclic hall
      hremovals hlookupOriginal hfragmentMemCurrent
  have hnoSelf :
      fragment.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          fragment.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_self_spread
      hunique hacyclic hfragmentMemOriginal
  have hfragmentName : fragment.name = fragmentName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name hlookup
  exact selectionSetValid_after_fragment_removal hlookup
    (by
      intro hspread
      exact hnoSelf (by simpa [hfragmentName] using hspread))
    hfragmentValidCurrent.2.2

theorem fragmentInlineSelectionSet_eq_of_reachable_contexts_aux
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {original : List FragmentDefinition}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    : ∀ (n : Nat)
        {leftCurrent rightCurrent : List FragmentDefinition}
        {fragmentName : Name} {fragment : FragmentDefinition}
        {leftRemaining
          : { remaining : List FragmentDefinition
              // remaining.length < leftCurrent.length }}
        {rightRemaining
          : { remaining : List FragmentDefinition
              // remaining.length < rightCurrent.length }},
        leftCurrent.length ≤ n
        -> rightCurrent.length ≤ n
        -> ReachableAncestorRemovals original fragmentName leftCurrent leftCurrent
        -> ReachableAncestorRemovals original fragmentName rightCurrent rightCurrent
        -> GraphQL.NamedFragment.lookupFragment? original fragmentName = some fragment
        -> lookupFragmentAndRestLt? fragmentName leftCurrent
            = some (fragment, leftRemaining)
        -> lookupFragmentAndRestLt? fragmentName rightCurrent
            = some (fragment, rightRemaining)
        -> Inline.inlineSelectionSet leftRemaining.val fragment.selectionSet
            = Inline.inlineSelectionSet rightRemaining.val fragment.selectionSet
  | 0, leftCurrent, _rightCurrent, _fragmentName, fragment, leftRemaining,
      _rightRemaining, hleftLength, _hrightLength, _hleftRemovals,
      _hrightRemovals, _hlookupOriginal, hlookupLeft, _hlookupRight => by
      have hmem : fragment ∈ leftCurrent :=
        GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
          hlookupLeft
      have hpositive : 0 < leftCurrent.length := List.length_pos_of_mem hmem
      omega
  | n + 1, leftCurrent, rightCurrent, fragmentName, fragment, leftRemaining,
      rightRemaining, hleftLength, hrightLength, hleftRemovals,
      hrightRemovals, hlookupOriginal, hlookupLeft, hlookupRight => by
      have hvalidLeft :=
        fragmentSelectionSetValid_after_reachable_lookup_removal
          hunique hacyclic hall hleftRemovals hlookupOriginal hlookupLeft
      have hvalidRight :=
        fragmentSelectionSetValid_after_reachable_lookup_removal
          hunique hacyclic hall hrightRemovals hlookupOriginal hlookupRight
      have hset : ∀ (k : Nat) {parentType : Name}
            {selectionSet : List Selection},
          sizeOf selectionSet ≤ k
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions leftRemaining.val parentType selectionSet
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions rightRemaining.val parentType selectionSet
          -> selectionSetSpreadNamesWithin selectionSet fragment.selectionSet
          -> Inline.inlineSelectionSet leftRemaining.val selectionSet
              = Inline.inlineSelectionSet rightRemaining.val selectionSet := by
        intro k
        induction k with
        | zero =>
            intro parentType selectionSet hsize _hleft _hright _hwithin
            cases selectionSet with
            | nil => simp
            | cons selection rest =>
                exfalso
                simp at hsize
        | succ k ihSize =>
            intro parentType selectionSet hsize hleft hright hwithin
            cases selectionSet with
            | nil => simp
            | cons selection rest =>
                have hleftPair := hleft
                have hrightPair := hright
                simp [GraphQL.NamedFragment.Validation.selectionSetValid]
                  at hleftPair hrightPair
                have hselectionWithin :
                    selectionSpreadNamesWithin selection fragment.selectionSet := by
                  intro candidate hcandidate
                  apply hwithin candidate
                  simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                    hcandidate]
                have hrestWithin :
                    selectionSetSpreadNamesWithin rest fragment.selectionSet := by
                  intro candidate hcandidate
                  apply hwithin candidate
                  simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                    hcandidate]
                have hhead :
                    Inline.inlineSelection leftRemaining.val selection
                      = Inline.inlineSelection rightRemaining.val selection := by
                  cases selection with
                  | field responseName fieldName arguments directives nested =>
                      simp [GraphQL.NamedFragment.Validation.selectionValid]
                        at hleftPair hrightPair
                      rcases hleftPair.1 with
                        ⟨_hdirectivesLeft, fieldDefinition, hfieldLookup,
                          _hargumentsLeft, hfieldLeft⟩
                      rcases hrightPair.1 with
                        ⟨_hdirectivesRight, rightFieldDefinition,
                          hrightFieldLookup, _hargumentsRight, hfieldRight⟩
                      have hfieldDefinition :
                          rightFieldDefinition = fieldDefinition := by
                        rw [hfieldLookup] at hrightFieldLookup
                        exact Option.some.inj hrightFieldLookup.symm
                      subst rightFieldDefinition
                      simp [GraphQL.NamedFragment.Validation.fieldSelectionSetValid]
                        at hfieldLeft hfieldRight
                      rcases hfieldLeft with ⟨_houtputLeft, hshapeLeft⟩
                      rcases hfieldRight with ⟨_houtputRight, hshapeRight⟩
                      cases hshapeLeft with
                      | inl hleafLeft =>
                          have hnil : nested = [] := hleafLeft.2
                          subst nested
                          simp [Inline.inlineSelection]
                      | inr hcompositeLeft =>
                          rcases hcompositeLeft with
                            ⟨_hcompositeLeft, hnonemptyLeft, hnestedLeft⟩
                          cases hshapeRight with
                          | inl hleafRight =>
                              exact False.elim (hnonemptyLeft hleafRight.2)
                          | inr hcompositeRight =>
                              rcases hcompositeRight with
                                ⟨_hcompositeRight, _hnonemptyRight, hnestedRight⟩
                              simp [Inline.inlineSelection]
                              apply ihSize
                              · simp at hsize
                                omega
                              · exact hnestedLeft
                              · exact hnestedRight
                              · intro candidate hcandidate
                                apply hselectionWithin candidate
                                simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames,
                                  hcandidate]
                  | inlineFragment typeCondition directives nested =>
                      cases typeCondition with
                      | none =>
                          simp [GraphQL.NamedFragment.Validation.selectionValid]
                            at hleftPair hrightPair
                          simp [Inline.inlineSelection]
                          apply ihSize
                          · simp at hsize
                            omega
                          · exact hleftPair.1.2.2
                          · exact hrightPair.1.2.2
                          · intro candidate hcandidate
                            apply hselectionWithin candidate
                            simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames,
                              hcandidate]
                      | some typeCondition =>
                          simp [GraphQL.NamedFragment.Validation.selectionValid]
                            at hleftPair hrightPair
                          simp [Inline.inlineSelection]
                          apply ihSize
                          · simp at hsize
                            omega
                          · exact hleftPair.1.2.2.2.2
                          · exact hrightPair.1.2.2.2.2
                          · intro candidate hcandidate
                            apply hselectionWithin candidate
                            simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames,
                              hcandidate]
                  | fragmentSpread childName directives =>
                      simp [GraphQL.NamedFragment.Validation.selectionValid]
                        at hleftPair hrightPair
                      rcases hleftPair.1 with
                        ⟨_hdirectivesLeft, child, hchildLookupLeft,
                          _hcompositeLeft, _hoverlapLeft⟩
                      rcases hrightPair.1 with
                        ⟨_hdirectivesRight, rightChild, hchildLookupRight,
                          _hcompositeRight, _hoverlapRight⟩
                      have hchildSpread :
                          childName ∈
                            GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                              fragment.selectionSet := by
                        apply hselectionWithin childName
                        simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                      have hfragmentMemOriginal : fragment ∈ original :=
                        GraphQL.NamedFragment.Validation.lookupFragment?_found_mem
                          hlookupOriginal
                      have hleftChildRemovals :
                          ReachableAncestorRemovals original childName
                            leftRemaining.val leftRemaining.val :=
                        hleftRemovals.child hfragmentMemOriginal hlookupOriginal
                          hlookupLeft hchildSpread
                      have hrightChildRemovals :
                          ReachableAncestorRemovals original childName
                            rightRemaining.val rightRemaining.val :=
                        hrightRemovals.child hfragmentMemOriginal hlookupOriginal
                          hlookupRight hchildSpread
                      have hchildOriginal :
                          GraphQL.NamedFragment.lookupFragment? original childName
                            = some child := by
                        have hchildMemLeft : child ∈ leftRemaining.val :=
                          GraphQL.NamedFragment.Validation.lookupFragment?_found_mem
                            hchildLookupLeft
                        have hchildMemOriginal : child ∈ original :=
                          hleftChildRemovals.mem_original hchildMemLeft
                        have hchildName : child.name = childName :=
                          GraphQL.NamedFragment.Validation.lookupFragment?_found_name
                            hchildLookupLeft
                        have hbyOwnName :=
                          GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
                            hunique hchildMemOriginal
                        simpa [hchildName] using hbyOwnName
                      have hrightChildOriginal :
                          GraphQL.NamedFragment.lookupFragment? original childName
                            = some rightChild := by
                        have hchildMemRight : rightChild ∈ rightRemaining.val :=
                          GraphQL.NamedFragment.Validation.lookupFragment?_found_mem
                            hchildLookupRight
                        have hchildMemOriginal : rightChild ∈ original :=
                          hrightChildRemovals.mem_original hchildMemRight
                        have hchildName : rightChild.name = childName :=
                          GraphQL.NamedFragment.Validation.lookupFragment?_found_name
                            hchildLookupRight
                        have hbyOwnName :=
                          GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
                            hunique hchildMemOriginal
                        simpa [hchildName] using hbyOwnName
                      have hchildren : rightChild = child := by
                        rw [hchildOriginal] at hrightChildOriginal
                        exact Option.some.inj hrightChildOriginal.symm
                      subst rightChild
                      rcases
                          GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_some_of_lookupFragment?
                            hchildLookupLeft with
                        ⟨leftChildRemaining, hleftChildLookup⟩
                      rcases
                          GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_some_of_lookupFragment?
                            hchildLookupRight with
                        ⟨rightChildRemaining, hrightChildLookup⟩
                      simp [Inline.inlineSelection, hleftChildLookup,
                        hrightChildLookup]
                      exact fragmentInlineSelectionSet_eq_of_reachable_contexts_aux
                        hunique hacyclic hall n (by omega) (by omega)
                        hleftChildRemovals hrightChildRemovals hchildOriginal
                        hleftChildLookup hrightChildLookup
                simp only [Inline.inlineSelectionSet]
                rw [hhead]
                congr 1
                apply ihSize
                · simp at hsize
                  omega
                · simpa [GraphQL.NamedFragment.Validation.selectionSetValid]
                    using hleftPair.2
                · simpa [GraphQL.NamedFragment.Validation.selectionSetValid]
                    using hrightPair.2
                · exact hrestWithin
      exact hset (sizeOf fragment.selectionSet) (Nat.le_refl _)
        hvalidLeft hvalidRight
        (by intro candidate hcandidate; exact hcandidate)
termination_by n _ _ _ _ _ _ _ _ _ _ _ _ _ => n

theorem fragmentInlineSelectionSet_eq_of_reachable_contexts
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {original leftCurrent rightCurrent : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {leftRemaining
      : { remaining : List FragmentDefinition // remaining.length < leftCurrent.length }}
    {rightRemaining
      : { remaining : List FragmentDefinition // remaining.length < rightCurrent.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (hleftRemovals
      : ReachableAncestorRemovals original fragmentName leftCurrent leftCurrent)
    (hrightRemovals
      : ReachableAncestorRemovals original fragmentName rightCurrent rightCurrent)
    (hlookupOriginal
      : GraphQL.NamedFragment.lookupFragment? original fragmentName = some fragment)
    (hlookupLeft
      : lookupFragmentAndRestLt? fragmentName leftCurrent
        = some (fragment, leftRemaining))
    (hlookupRight
      : lookupFragmentAndRestLt? fragmentName rightCurrent
        = some (fragment, rightRemaining))
    : Inline.inlineSelectionSet leftRemaining.val fragment.selectionSet
      = Inline.inlineSelectionSet rightRemaining.val fragment.selectionSet := by
  exact fragmentInlineSelectionSet_eq_of_reachable_contexts_aux
    hunique hacyclic hall (max leftCurrent.length rightCurrent.length)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    hleftRemovals hrightRemovals hlookupOriginal hlookupLeft hlookupRight

end Semantics
end NamedFragment
end GraphQL
