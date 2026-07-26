import Proofs.GraphQL.NamedFragment.Validation.Lookup

/-! Basic consequences of named-fragment acyclicness. -/

namespace GraphQL
namespace NamedFragment
namespace Validation

theorem fragmentReachableBool_direct
    {fragments : List FragmentDefinition} {source target : Name}
    {fragment : FragmentDefinition}
    (hlookup : lookupFragment? fragments source = some fragment)
    (hspread : target ∈ selectionSetFragmentSpreadNames fragment.selectionSet)
    (fuel : Nat)
    : fragmentReachableBool fragments (fuel + 1) source target = true := by
  have hany :
      (selectionSetFragmentSpreadNames fragment.selectionSet).any
      (fun next => next == target) = true :=
    List.any_eq_true.mpr ⟨target, hspread, by simp⟩
  simp [fragmentReachableBool, hlookup, hany]

theorem fragmentReachableBool_direct_of_lookupFragmentAndRestLt?
    {fragments : List FragmentDefinition} {source target : Name}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hlookup : lookupFragmentAndRestLt? source fragments = some (fragment, remaining))
    (hspread : target ∈ selectionSetFragmentSpreadNames fragment.selectionSet)
    (fuel : Nat)
    : fragmentReachableBool fragments (fuel + 1) source target = true := by
  exact fragmentReachableBool_direct
    (lookupFragment?_of_lookupFragmentAndRestLt? hlookup) hspread fuel

theorem fragmentReachableBool_two_step
    {fragments : List FragmentDefinition}
    {source intermediate target : Name}
    {sourceFragment intermediateFragment : FragmentDefinition}
    (hsource : lookupFragment? fragments source = some sourceFragment)
    (hsourceSpread
      : intermediate ∈ selectionSetFragmentSpreadNames sourceFragment.selectionSet)
    (hintermediate : lookupFragment? fragments intermediate = some intermediateFragment)
    (hintermediateSpread
      : target ∈ selectionSetFragmentSpreadNames intermediateFragment.selectionSet)
    (fuel : Nat)
    : fragmentReachableBool fragments (fuel + 2) source target = true := by
  have hnext :
      fragmentReachableBool fragments (fuel + 1) intermediate target = true :=
    fragmentReachableBool_direct hintermediate hintermediateSpread fuel
  simp [fragmentReachableBool, hsource]
  exact Or.inr ⟨intermediate, hsourceSpread, hnext⟩

theorem fragmentReachableBool_append_direct
    {fragments : List FragmentDefinition}
    {source target final : Name}
    {targetFragment : FragmentDefinition}
    (hreachable : fragmentReachableBool fragments fuel source target = true)
    (htarget : lookupFragment? fragments target = some targetFragment)
    (htargetSpread : final ∈ selectionSetFragmentSpreadNames targetFragment.selectionSet)
    : fragmentReachableBool fragments (fuel + 1) source final = true := by
  induction fuel generalizing source with
  | zero =>
      simp [fragmentReachableBool] at hreachable
  | succ fuel ih =>
      cases hsource : lookupFragment? fragments source with
      | none =>
          simp [fragmentReachableBool, hsource] at hreachable
      | some sourceFragment =>
          simp [fragmentReachableBool, hsource] at hreachable ⊢
          rcases hreachable with hdirect | htail
          · have hnext :
                fragmentReachableBool fragments (fuel + 1) target final =
                  true :=
              fragmentReachableBool_direct htarget htargetSpread fuel
            exact Or.inr ⟨target, hdirect, hnext⟩
          · rcases htail with ⟨next, hnextSpread, hnextReachable⟩
            exact Or.inr
              ⟨next, hnextSpread,
                ih hnextReachable⟩

theorem fragmentReachableBool_mono_fuel
    {fragments : List FragmentDefinition} {source target : Name}
    {fuel fuel' : Nat}
    (hle : fuel ≤ fuel')
    (hreachable : fragmentReachableBool fragments fuel source target = true)
    : fragmentReachableBool fragments fuel' source target = true := by
  induction fuel generalizing source fuel' with
  | zero =>
      simp [fragmentReachableBool] at hreachable
  | succ fuel ih =>
      cases fuel' with
      | zero =>
          omega
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.succ_le_succ_iff.mp hle
          cases hsource : lookupFragment? fragments source with
          | none =>
              simp [fragmentReachableBool, hsource] at hreachable
          | some sourceFragment =>
              simp [fragmentReachableBool, hsource] at hreachable ⊢
              rcases hreachable with hdirect | htail
              · exact Or.inl hdirect
              · rcases htail with ⟨next, hnextSpread, hnextReachable⟩
                exact Or.inr
                  ⟨next, hnextSpread, ih hle' hnextReachable⟩

theorem fragmentsAcyclic_not_reachable_self
    {fragments : List FragmentDefinition} {fragment : FragmentDefinition}
    (hacyclic : fragmentsAcyclic fragments)
    (hmem : fragment ∈ fragments)
    : fragmentReachableBool fragments fragments.length fragment.name fragment.name
      = false := by
  simp [fragmentsAcyclic, fragmentsAcyclicBool] at hacyclic
  have hnotReachable := hacyclic fragment hmem
  cases hreachable :
      fragmentReachableBool fragments fragments.length fragment.name
        fragment.name <;>
    simp [hreachable] at hnotReachable ⊢

theorem fragmentsAcyclic_no_direct_self_spread
    {fragments : List FragmentDefinition} {fragment : FragmentDefinition}
    (hunique : fragmentNamesUnique fragments)
    (hacyclic : fragmentsAcyclic fragments)
    (hmem : fragment ∈ fragments)
    : fragment.name ∉ selectionSetFragmentSpreadNames fragment.selectionSet := by
  intro hspread
  cases fragments with
  | nil =>
      simp at hmem
  | cons head rest =>
      have hreachableFalse :
          fragmentReachableBool (head :: rest) (head :: rest).length
              fragment.name fragment.name = false :=
        fragmentsAcyclic_not_reachable_self hacyclic hmem
      have hlookup :
          lookupFragment? (head :: rest) fragment.name = some fragment :=
        lookupFragment?_eq_some_of_mem_unique hunique hmem
      have hany :
          (selectionSetFragmentSpreadNames fragment.selectionSet).any
              (fun next => next == fragment.name) = true :=
        List.any_eq_true.mpr ⟨fragment.name, hspread, by simp⟩
      simp [fragmentReachableBool, hlookup, hany] at hreachableFalse

theorem fragmentsAcyclic_no_direct_spread_to_reachable_source
    {fragments : List FragmentDefinition}
    {source target : FragmentDefinition} {targetName : Name}
    {fuel : Nat}
    (hacyclic : fragmentsAcyclic fragments)
    (hsourceMem : source ∈ fragments)
    (hreachable : fragmentReachableBool fragments fuel source.name targetName = true)
    (hle : fuel + 1 ≤ fragments.length)
    (htargetLookup : lookupFragment? fragments targetName = some target)
    : source.name ∉ selectionSetFragmentSpreadNames target.selectionSet := by
  intro htargetSpread
  have hcycleSmall :
      fragmentReachableBool fragments (fuel + 1) source.name source.name =
        true :=
    fragmentReachableBool_append_direct hreachable htargetLookup htargetSpread
  have hcycleFull :
      fragmentReachableBool fragments fragments.length source.name source.name =
        true :=
    fragmentReachableBool_mono_fuel hle hcycleSmall
  have hreachableFalse :
      fragmentReachableBool fragments fragments.length source.name source.name =
        false :=
    fragmentsAcyclic_not_reachable_self hacyclic hsourceMem
  rw [hreachableFalse] at hcycleFull
  contradiction

theorem fragmentsAcyclic_no_direct_back_spread
    {fragments : List FragmentDefinition}
    {source target : FragmentDefinition} {targetName : Name}
    (hunique : fragmentNamesUnique fragments)
    (hacyclic : fragmentsAcyclic fragments)
    (hsourceMem : source ∈ fragments)
    (hsourceSpread : targetName ∈ selectionSetFragmentSpreadNames source.selectionSet)
    (htargetLookup : lookupFragment? fragments targetName = some target)
    : source.name ∉ selectionSetFragmentSpreadNames target.selectionSet := by
  intro htargetSpread
  by_cases hsame : targetName = source.name
  · have hsourceLookup :
        lookupFragment? fragments source.name = some source :=
      lookupFragment?_eq_some_of_mem_unique hunique hsourceMem
    rw [hsame] at htargetLookup
    rw [hsourceLookup] at htargetLookup
    injection htargetLookup with htarget
    subst target
    exact (fragmentsAcyclic_no_direct_self_spread hunique hacyclic
      hsourceMem) htargetSpread
  · have htargetMem : target ∈ fragments :=
      lookupFragment?_found_mem htargetLookup
    have htargetName : target.name = targetName :=
      lookupFragment?_found_name htargetLookup
    have hsourceLookup :
        lookupFragment? fragments source.name = some source :=
      lookupFragment?_eq_some_of_mem_unique hunique hsourceMem
    have hreachableFalse :
        fragmentReachableBool fragments fragments.length source.name
          source.name = false :=
      fragmentsAcyclic_not_reachable_self hacyclic hsourceMem
    cases fragments with
    | nil =>
        simp at hsourceMem
    | cons head rest =>
        cases rest with
        | nil =>
            simp at hsourceMem htargetMem
            subst source
            subst target
            exact hsame htargetName.symm
        | cons second tail =>
            have hreachableTrue :
                fragmentReachableBool (head :: second :: tail)
                    (head :: second :: tail).length source.name source.name =
                  true := by
              simpa using
                (fragmentReachableBool_two_step
                  (fragments := head :: second :: tail)
                  (source := source.name)
                  (intermediate := targetName)
                  (target := source.name)
                  hsourceLookup hsourceSpread htargetLookup
                  (by simpa [htargetName] using htargetSpread)
                  tail.length)
            rw [hreachableFalse] at hreachableTrue
            contradiction

theorem lookupFragment?_remaining_to_original
    {removedName sourceName : Name}
    {fragments : List FragmentDefinition}
    {removed source : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hunique : fragmentNamesUnique fragments)
    (hremove : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
    (hlookup : lookupFragment? remaining.val sourceName = some source)
    : lookupFragment? fragments sourceName = some source := by
  have hsourceMemRemaining : source ∈ remaining.val :=
    lookupFragment?_found_mem hlookup
  have hsourceMem : source ∈ fragments :=
    lookupFragmentAndRestLt?_remaining_mem hremove source
      hsourceMemRemaining
  have hsourceName : source.name = sourceName :=
    lookupFragment?_found_name hlookup
  have hlookupByOwnName :
      lookupFragment? fragments source.name = some source :=
    lookupFragment?_eq_some_of_mem_unique hunique hsourceMem
  simpa [hsourceName] using hlookupByOwnName

theorem fragmentReachableBool_remaining_to_original
    {removedName : Name}
    {fragments : List FragmentDefinition}
    {removed : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {fuel : Nat} {source target : Name}
    (hunique : fragmentNamesUnique fragments)
    (hremove : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
    (hreachable : fragmentReachableBool remaining.val fuel source target = true)
    : fragmentReachableBool fragments fuel source target = true := by
  induction fuel generalizing source with
  | zero =>
      simp [fragmentReachableBool] at hreachable
  | succ fuel ih =>
      cases hsource :
          lookupFragment? remaining.val source with
      | none =>
          simp [fragmentReachableBool, hsource] at hreachable
      | some sourceFragment =>
          have hsourceOriginal :
              lookupFragment? fragments source = some sourceFragment :=
            lookupFragment?_remaining_to_original hunique hremove hsource
          simp [fragmentReachableBool, hsource] at hreachable
          simp [fragmentReachableBool, hsourceOriginal]
          rcases hreachable with hdirect | htail
          · exact Or.inl hdirect
          · rcases htail with ⟨next, hnextSpread, hnextReachable⟩
            exact Or.inr ⟨next, hnextSpread, ih hnextReachable⟩

theorem fragmentsAcyclic_of_lookupFragmentAndRestLt?_remaining
    {fragmentName : Name}
    {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hunique : fragmentNamesUnique fragments)
    (hacyclic : fragmentsAcyclic fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    : fragmentsAcyclic remaining.val := by
  simp [fragmentsAcyclic, fragmentsAcyclicBool]
  intro candidate hcandidate
  have hcandidateOriginal : candidate ∈ fragments :=
    lookupFragmentAndRestLt?_remaining_mem hlookup candidate hcandidate
  have hnotReachableOriginal :
      fragmentReachableBool fragments fragments.length candidate.name
        candidate.name = false :=
    fragmentsAcyclic_not_reachable_self hacyclic hcandidateOriginal
  cases hreachable :
      fragmentReachableBool remaining.val remaining.val.length candidate.name
        candidate.name
  · rfl
  · have hreachableOriginalSmall :
        fragmentReachableBool fragments remaining.val.length candidate.name
          candidate.name = true :=
      fragmentReachableBool_remaining_to_original hunique hlookup hreachable
    have hreachableOriginal :
        fragmentReachableBool fragments fragments.length candidate.name
          candidate.name = true :=
      fragmentReachableBool_mono_fuel
        (Nat.le_of_lt remaining.property) hreachableOriginalSmall
    rw [hnotReachableOriginal] at hreachableOriginal
    contradiction

end Validation
end NamedFragment
end GraphQL
