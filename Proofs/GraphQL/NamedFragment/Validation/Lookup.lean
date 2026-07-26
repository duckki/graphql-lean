import GraphQL.NamedFragment.Validation

/-! Lookup bookkeeping lemmas for fragment-definition lists. -/

namespace GraphQL
namespace NamedFragment
namespace Validation

theorem lookupFragmentAndRestLt?_found_mem
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
      -> fragment ∈ fragments := by
  induction fragments generalizing fragment with
  | nil =>
      intro hlookup
      simp [lookupFragmentAndRestLt?] at hlookup
  | cons head rest ih =>
      intro hlookup
      by_cases hname : head.name == fragmentName
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        rcases hlookup with ⟨hfragment, _hremaining⟩
        subst fragment
        simp
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        cases hrest : lookupFragmentAndRestLt? fragmentName rest with
        | none =>
            simp [hrest] at hlookup
        | some pair =>
            cases pair with
            | mk found remaining' =>
                simp [hrest] at hlookup
                rcases hlookup with ⟨hfragment, _hremaining⟩
                subst fragment
                have hfound : found ∈ rest := ih hrest
                simp [hfound]

theorem lookupFragmentAndRestLt?_remaining_mem
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
      -> ∀ candidate, candidate ∈ remaining.val -> candidate ∈ fragments := by
  induction fragments generalizing fragment with
  | nil =>
      intro hlookup
      simp [lookupFragmentAndRestLt?] at hlookup
  | cons head rest ih =>
      intro hlookup candidate hcandidate
      by_cases hname : head.name == fragmentName
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        rcases hlookup with ⟨_hfragment, hremaining⟩
        subst remaining
        simp [hcandidate]
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        cases hrest : lookupFragmentAndRestLt? fragmentName rest with
        | none =>
            simp [hrest] at hlookup
        | some pair =>
            cases pair with
            | mk found remaining' =>
                simp [hrest] at hlookup
                rcases hlookup with ⟨_hfragment, hremaining⟩
                subst remaining
                simp at hcandidate
                rcases hcandidate with hhead | htail
                · subst candidate
                  simp
                · have hcandidateRest :
                      candidate ∈ rest :=
                    ih hrest candidate htail
                  simp [hcandidateRest]

theorem lookupFragmentAndRestLt?_found_name
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
      -> fragment.name = fragmentName := by
  induction fragments generalizing fragment with
  | nil =>
      intro hlookup
      simp [lookupFragmentAndRestLt?] at hlookup
  | cons head rest ih =>
      intro hlookup
      by_cases hname : head.name == fragmentName
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        rcases hlookup with ⟨hfragment, _hremaining⟩
        subst fragment
        simpa using hname
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        cases hrest : lookupFragmentAndRestLt? fragmentName rest with
        | none =>
            simp [hrest] at hlookup
        | some pair =>
            cases pair with
            | mk found remaining' =>
                simp [hrest] at hlookup
                rcases hlookup with ⟨hfragment, _hremaining⟩
                subst fragment
                exact ih hrest

theorem lookupFragment?_found_mem
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    : lookupFragment? fragments fragmentName = some fragment -> fragment ∈ fragments := by
  induction fragments generalizing fragment with
  | nil =>
      intro hlookup
      change
        List.find? (fun candidate : FragmentDefinition =>
          candidate.name == fragmentName) [] = some fragment at hlookup
      simp at hlookup
  | cons head rest ih =>
      intro hlookup
      change
        List.find? (fun candidate : FragmentDefinition =>
          candidate.name == fragmentName) (head :: rest) = some fragment
        at hlookup
      rw [List.find?_cons] at hlookup
      by_cases hname : head.name == fragmentName
      · simp [hname] at hlookup
        subst fragment
        simp
      · simp [hname] at hlookup
        have hrest :
            lookupFragment? rest fragmentName = some fragment := by
          simpa [GraphQL.NamedFragment.lookupFragment?] using hlookup
        have hmem : fragment ∈ rest := ih hrest
        simp [hmem]

theorem lookupFragment?_found_name
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    : lookupFragment? fragments fragmentName = some fragment
      -> fragment.name = fragmentName := by
  induction fragments generalizing fragment with
  | nil =>
      intro hlookup
      change
        List.find? (fun candidate : FragmentDefinition =>
          candidate.name == fragmentName) [] = some fragment at hlookup
      simp at hlookup
  | cons head rest ih =>
      intro hlookup
      change
        List.find? (fun candidate : FragmentDefinition =>
          candidate.name == fragmentName) (head :: rest) = some fragment
        at hlookup
      rw [List.find?_cons] at hlookup
      by_cases hname : head.name == fragmentName
      · simp [hname] at hlookup
        subst fragment
        simpa using hname
      · simp [hname] at hlookup
        have hrest :
            lookupFragment? rest fragmentName = some fragment := by
          simpa [GraphQL.NamedFragment.lookupFragment?] using hlookup
        exact ih hrest

theorem lookupFragment?_of_lookupFragmentAndRestLt?
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
      -> lookupFragment? fragments fragmentName = some fragment := by
  induction fragments generalizing fragment with
  | nil =>
      intro hlookup
      simp [lookupFragmentAndRestLt?] at hlookup
  | cons head rest ih =>
      intro hlookup
      by_cases hname : head.name == fragmentName
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        rcases hlookup with ⟨hfragment, _hremaining⟩
        subst fragment
        change
          List.find? (fun candidate : FragmentDefinition =>
            candidate.name == fragmentName) (head :: rest) = some head
        rw [List.find?_cons]
        simp [hname]
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        cases hrest : lookupFragmentAndRestLt? fragmentName rest with
        | none =>
            simp [hrest] at hlookup
        | some pair =>
            cases pair with
            | mk found remaining' =>
                simp [hrest] at hlookup
                rcases hlookup with ⟨hfound, _hremaining⟩
                subst fragment
                change
                  List.find? (fun candidate : FragmentDefinition =>
                    candidate.name == fragmentName) (head :: rest) =
                    some found
                rw [List.find?_cons]
                simp [hname]
                exact ih hrest

theorem fragmentNamesUnique_of_lookupFragmentAndRestLt?_remaining
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hunique : fragmentNamesUnique fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    : fragmentNamesUnique remaining.val := by
  induction fragments generalizing fragment with
  | nil =>
      simp [lookupFragmentAndRestLt?] at hlookup
  | cons head rest ih =>
      by_cases hname : head.name == fragmentName
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        rcases hlookup with ⟨_hfragment, hremaining⟩
        subst remaining
        simp [fragmentNamesUnique] at hunique
        exact hunique.2
      · simp [lookupFragmentAndRestLt?, hname] at hlookup
        cases hrest : lookupFragmentAndRestLt? fragmentName rest with
        | none =>
            simp [hrest] at hlookup
        | some pair =>
            cases pair with
            | mk found remaining' =>
                simp [hrest] at hlookup
                rcases hlookup with ⟨hfound, hremaining⟩
                subst fragment
                subst remaining
                simp [fragmentNamesUnique] at hunique ⊢
                refine ⟨?headNotMem, ih hunique.2 hrest⟩
                intro candidate hcandidate hcandidateName
                exact hunique.1 candidate
                  (lookupFragmentAndRestLt?_remaining_mem hrest candidate
                    hcandidate)
                  hcandidateName

theorem lookupFragmentAndRestLt?_some_of_lookupFragment?
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    : lookupFragment? fragments fragmentName = some fragment
      -> ∃ remaining
            : { remaining : List FragmentDefinition
                // remaining.length < fragments.length },
          lookupFragmentAndRestLt? fragmentName fragments
          = some (fragment, remaining) := by
  induction fragments generalizing fragment with
  | nil =>
      intro hlookup
      change
        List.find? (fun fragment : FragmentDefinition =>
          fragment.name == fragmentName) [] = some fragment at hlookup
      simp at hlookup
  | cons head rest ih =>
      intro hlookup
      change
        List.find? (fun fragment : FragmentDefinition =>
          fragment.name == fragmentName) (head :: rest) = some fragment
        at hlookup
      rw [List.find?_cons] at hlookup
      by_cases hname : head.name == fragmentName
      · simp [hname] at hlookup
        cases hlookup
        exact ⟨⟨rest, by simp⟩, by
          simp [lookupFragmentAndRestLt?, hname]⟩
      · simp [hname] at hlookup
        have hlookupRest :
            lookupFragment? rest fragmentName = some fragment := by
          simpa [GraphQL.NamedFragment.lookupFragment?] using hlookup
        rcases ih hlookupRest with ⟨remaining, hremaining⟩
        exact ⟨⟨head :: remaining.val, by
          have hlt := remaining.property
          simp at hlt ⊢
          omega⟩, by
          simp [lookupFragmentAndRestLt?, hname, hremaining]⟩

theorem lookupFragment?_remaining_of_ne
    {removedName otherName : Name} {fragments : List FragmentDefinition}
    {removed other : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hremove : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
    (hlookup : lookupFragment? fragments otherName = some other)
    (hne : removedName ≠ otherName)
    : lookupFragment? remaining.val otherName = some other := by
  induction fragments generalizing removed other with
  | nil =>
      simp [lookupFragmentAndRestLt?] at hremove
  | cons head rest ih =>
      by_cases hremovedHead : head.name == removedName
      · simp [lookupFragmentAndRestLt?, hremovedHead] at hremove
        rcases hremove with ⟨_hremoved, hremaining⟩
        subst remaining
        change
          List.find? (fun fragment : FragmentDefinition =>
            fragment.name == otherName) rest = some other
        change
          List.find? (fun fragment : FragmentDefinition =>
            fragment.name == otherName) (head :: rest) = some other
          at hlookup
        rw [List.find?_cons] at hlookup
        have hheadNeOther : (head.name == otherName) = false := by
          cases hother : head.name == otherName
          · rfl
          · have hheadRemoved : head.name = removedName := by
              simpa using hremovedHead
            have hheadOther : head.name = otherName := by
              simpa using hother
            exact False.elim (hne (hheadRemoved.symm.trans hheadOther))
        simpa [hheadNeOther] using hlookup
      · simp [lookupFragmentAndRestLt?, hremovedHead] at hremove
        cases hrest : lookupFragmentAndRestLt? removedName rest with
        | none =>
            simp [hrest] at hremove
        | some pair =>
            cases pair with
            | mk found remaining' =>
                simp [hrest] at hremove
                rcases hremove with ⟨hfound, hremaining⟩
                subst removed
                subst remaining
                change
                  List.find? (fun fragment : FragmentDefinition =>
                    fragment.name == otherName) (head :: remaining'.val) =
                    some other
                change
                  List.find? (fun fragment : FragmentDefinition =>
                    fragment.name == otherName) (head :: rest) = some other
                  at hlookup
                rw [List.find?_cons] at hlookup ⊢
                cases hotherHead : head.name == otherName
                · simp [hotherHead] at hlookup ⊢
                  exact ih hrest hlookup
                · simp [hotherHead] at hlookup ⊢
                  exact hlookup

theorem lookupFragment?_eq_some_of_mem_unique
    {fragments : List FragmentDefinition} {fragment : FragmentDefinition}
    (hunique : fragmentNamesUnique fragments)
    (hmem : fragment ∈ fragments)
    : lookupFragment? fragments fragment.name = some fragment := by
  induction fragments with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      simp [fragmentNamesUnique] at hunique
      rcases hunique with ⟨hheadNotMem, hrestUnique⟩
      cases hmem with
      | head =>
        change
          List.find? (fun candidate : FragmentDefinition =>
            candidate.name == fragment.name) (fragment :: rest) = some fragment
        rw [List.find?_cons]
        simp
      | tail _ htail =>
        change
          List.find? (fun candidate : FragmentDefinition =>
            candidate.name == fragment.name) (head :: rest) =
            some fragment
        rw [List.find?_cons]
        have hheadNe : (head.name == fragment.name) = false := by
          cases hname : head.name == fragment.name
          · rfl
          · have hnameEq : head.name = fragment.name := by
              simpa using hname
            exact False.elim (hheadNotMem fragment htail hnameEq.symm)
        simp [hheadNe]
        exact ih hrestUnique htail

theorem lookupFragment?_of_lookupFragmentAndRestLt?_remaining_original
    {removedName targetName : Name}
    {fragments : List FragmentDefinition}
    {removed target : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {targetRemaining
      : { targetRemaining : List FragmentDefinition
          // targetRemaining.length < remaining.val.length }}
    (hunique : fragmentNamesUnique fragments)
    (hremove : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
    (htarget
      : lookupFragmentAndRestLt? targetName remaining.val
        = some (target, targetRemaining))
    : lookupFragment? fragments targetName = some target := by
  have htargetMemRemaining : target ∈ remaining.val :=
    lookupFragmentAndRestLt?_found_mem htarget
  have htargetMem : target ∈ fragments :=
    lookupFragmentAndRestLt?_remaining_mem hremove target
      htargetMemRemaining
  have htargetName : target.name = targetName :=
    lookupFragmentAndRestLt?_found_name htarget
  have hlookupByOwnName :
      lookupFragment? fragments target.name = some target :=
    lookupFragment?_eq_some_of_mem_unique hunique htargetMem
  simpa [htargetName] using hlookupByOwnName

theorem lookupFragmentAndRestLt?_remaining_lift
    {removedName targetName : Name}
    {fragments : List FragmentDefinition}
    {removed target : FragmentDefinition}
    {remaining : { xs : List FragmentDefinition // xs.length < fragments.length }}
    {targetRemaining
      : { xs : List FragmentDefinition // xs.length < remaining.val.length }}
    (hne : removedName ≠ targetName)
    (hremove : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
    (htarget
      : lookupFragmentAndRestLt? targetName remaining.val
        = some (target, targetRemaining))
    : ∃ sourceRemaining
          : { xs : List FragmentDefinition // xs.length < fragments.length },
        lookupFragmentAndRestLt? targetName fragments = some (target, sourceRemaining)
        ∧ ∃ liftedRemaining
              : { xs : List FragmentDefinition
                  // xs.length < sourceRemaining.val.length },
            liftedRemaining.val = targetRemaining.val
            ∧ lookupFragmentAndRestLt? removedName sourceRemaining.val
              = some (removed, liftedRemaining) := by
  induction fragments generalizing removed target with
  | nil =>
      simp [lookupFragmentAndRestLt?] at hremove
  | cons head rest ih =>
      by_cases hremovedHead : head.name == removedName
      · simp [lookupFragmentAndRestLt?, hremovedHead] at hremove
        rcases hremove with ⟨hremoved, hremaining⟩
        subst removed
        subst remaining
        refine ⟨⟨head :: targetRemaining.val, by
          have hlt := targetRemaining.property
          simp at hlt ⊢
          omega⟩, ?_, ?_⟩
        · have htargetHeadFalse : (head.name == targetName) = false := by
            cases htargetHead : head.name == targetName
            · rfl
            · have hheadRemoved : head.name = removedName := by
                simpa using hremovedHead
              have hheadTarget : head.name = targetName := by
                simpa using htargetHead
              exact False.elim
                (hne (hheadRemoved.symm.trans hheadTarget))
          simp [lookupFragmentAndRestLt?, htargetHeadFalse, htarget]
        · refine ⟨⟨targetRemaining.val, by simp⟩, rfl, ?_⟩
          simp [lookupFragmentAndRestLt?, hremovedHead]
      · simp [lookupFragmentAndRestLt?, hremovedHead] at hremove
        cases hremoveRest : lookupFragmentAndRestLt? removedName rest with
        | none =>
            simp [hremoveRest] at hremove
        | some removePair =>
            cases removePair with
            | mk removedRest remainingRest =>
                simp [hremoveRest] at hremove
                rcases hremove with ⟨hremovedEq, hremainingEq⟩
                subst removed
                subst remaining
                by_cases htargetHead : head.name == targetName
                · simp [lookupFragmentAndRestLt?, htargetHead] at htarget
                  rcases htarget with ⟨htargetEq, htargetRemainingEq⟩
                  subst target
                  refine ⟨⟨rest, by simp⟩, ?_, ?_⟩
                  · simp [lookupFragmentAndRestLt?, htargetHead]
                  · refine
                      ⟨⟨remainingRest.val, remainingRest.property⟩, ?_, ?_⟩
                    · simpa using congrArg Subtype.val htargetRemainingEq
                    · simpa using hremoveRest
                · simp [lookupFragmentAndRestLt?, htargetHead] at htarget
                  cases htargetRest :
                      lookupFragmentAndRestLt? targetName remainingRest.val with
                  | none =>
                      simp [htargetRest] at htarget
                  | some targetPair =>
                      cases targetPair with
                      | mk targetRest targetRemainingRest =>
                          simp [htargetRest] at htarget
                          rcases htarget with
                            ⟨htargetEq, htargetRemainingEq⟩
                          subst target
                          rcases ih hremoveRest htargetRest with
                            ⟨sourceRemainingRest, hsourceLookupRest,
                              liftedRemaining, hliftVal, hliftLookup⟩
                          refine ⟨⟨head :: sourceRemainingRest.val, by
                            have hlt := sourceRemainingRest.property
                            simp at hlt ⊢
                            omega⟩, ?_, ?_⟩
                          · simp [lookupFragmentAndRestLt?, htargetHead,
                              hsourceLookupRest]
                          · refine ⟨⟨head :: liftedRemaining.val, by
                              have hlt := liftedRemaining.property
                              simp at hlt ⊢
                              omega⟩, ?_, ?_⟩
                            · have hval :=
                                congrArg Subtype.val htargetRemainingEq
                              simpa [hliftVal] using hval
                            · simp [lookupFragmentAndRestLt?, hremovedHead,
                                hliftLookup]

theorem allFragmentDefinitionsValid_of_remaining_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {candidate : FragmentDefinition}
    (hall : allFragmentDefinitionsValid schema variableDefinitions fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    (hcandidate : candidate ∈ remaining.val)
    : fragmentDefinitionValid schema variableDefinitions fragments candidate := by
  exact hall candidate
    (lookupFragmentAndRestLt?_remaining_mem hlookup candidate hcandidate)

theorem allFragmentDefinitionsValid_of_lookupFragmentAndRestLt?
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hall : allFragmentDefinitionsValid schema variableDefinitions fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    : fragmentDefinitionValid schema variableDefinitions fragments fragment := by
  exact hall fragment (lookupFragmentAndRestLt?_found_mem hlookup)

theorem selectionValid_fragmentSpread_lookupFragmentAndRestLt?
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition} {parentType fragmentName : Name}
    {directives : List DirectiveApplication}
    (hvalid
      : selectionValid schema variableDefinitions fragments parentType
          (.fragmentSpread fragmentName directives))
    : GraphQL.Validation.directivesValid schema variableDefinitions directives
      ∧ ∃ fragment,
        ∃ remaining
            : { remaining : List FragmentDefinition
                // remaining.length < fragments.length },
          lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
          ∧ schema.isCompositeType fragment.typeCondition
          ∧ schema.typesOverlap parentType fragment.typeCondition := by
  simp [selectionValid] at hvalid
  rcases hvalid with
    ⟨hdirectives, fragment, hlookup, hcomposite, hoverlap⟩
  rcases lookupFragmentAndRestLt?_some_of_lookupFragment? hlookup with
    ⟨remaining, hremaining⟩
  exact ⟨hdirectives, fragment, remaining, hremaining, hcomposite, hoverlap⟩

end Validation
end NamedFragment
end GraphQL
