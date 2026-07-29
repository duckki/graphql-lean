import Proofs.GraphQL.NamedFragment.Semantics.Validation.Selection
import Proofs.GraphQL.NamedFragment.Validation.Acyclic

/-! Named-fragment validation preservation proofs. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

mutual
  theorem selectionValid_after_fragment_removal
      {removedName : Name} {fragments : List FragmentDefinition}
      {removed : FragmentDefinition}
      {remaining
        : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
      (hremove
        : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
            {parentType : Name} {selection : Selection},
          removedName
            ∉ GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames selection
          -> GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions fragments parentType selection
          -> GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions remaining.val parentType selection
    | schema, variableDefinitions, parentType,
        .field responseName fieldName arguments directives selectionSet,
        hnoSpread, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, fieldDefinition, hlookup, harguments, hfield⟩
        simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames] at hnoSpread
        simp [GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, fieldDefinition, hlookup, harguments,
          fieldSelectionSetValid_after_fragment_removal hremove hnoSpread
            hfield⟩
    | schema, variableDefinitions, parentType,
        .inlineFragment none directives selectionSet, hnoSpread, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with ⟨hdirectives, hnonempty, hselectionSet⟩
        simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames] at hnoSpread
        simp [GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hnonempty,
          selectionSetValid_after_fragment_removal hremove hnoSpread
            hselectionSet⟩
    | schema, variableDefinitions, parentType,
        .inlineFragment (some typeCondition) directives selectionSet,
        hnoSpread, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, hcomposite, hoverlap, hnonempty, hselectionSet⟩
        simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames] at hnoSpread
        simp [GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hcomposite, hoverlap, hnonempty,
          selectionSetValid_after_fragment_removal hremove hnoSpread
            hselectionSet⟩
    | schema, variableDefinitions, parentType,
        .fragmentSpread fragmentName directives, hnoSpread, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames] at hnoSpread
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid ⊢
        rcases hvalid with
          ⟨hdirectives, fragment, hlookup, hcomposite, hoverlap⟩
        exact ⟨hdirectives, fragment,
          GraphQL.NamedFragment.Validation.lookupFragment?_remaining_of_ne
            hremove hlookup hnoSpread,
          hcomposite, hoverlap⟩

  theorem selectionSetValid_after_fragment_removal
      {removedName : Name} {fragments : List FragmentDefinition}
      {removed : FragmentDefinition}
      {remaining
        : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
      (hremove
        : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
            {parentType : Name} {selectionSet : List Selection},
          removedName
            ∉ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                selectionSet
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions fragments parentType selectionSet
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions remaining.val parentType selectionSet
    | _schema, _variableDefinitions, _parentType, [], _hnoSpread,
        _hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionSetValid]
    | schema, variableDefinitions, parentType, selection :: rest,
        hnoSpread, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames]
          at hnoSpread
        have hselectionNoSpread :
            removedName ∉
              GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames
                selection := by
          intro hmem
          exact hnoSpread.1 hmem
        have hrestNoSpread :
            removedName ∉
              GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                rest := by
          intro hmem
          exact hnoSpread.2 hmem
        have hvalidPair := hvalid
        simp [GraphQL.NamedFragment.Validation.selectionSetValid] at hvalidPair
        have hselectionValid :
            GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions fragments parentType selection :=
          hvalidPair.1
        have hrestValid :
            GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions fragments parentType rest := by
          simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
            hvalidPair.2
        simp [GraphQL.NamedFragment.Validation.selectionSetValid]
        exact ⟨selectionValid_after_fragment_removal hremove
            hselectionNoSpread hselectionValid,
          by
            simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
              selectionSetValid_after_fragment_removal hremove hrestNoSpread
                hrestValid⟩

  theorem fieldSelectionSetValid_after_fragment_removal
      {removedName : Name} {fragments : List FragmentDefinition}
      {removed : FragmentDefinition}
      {remaining
        : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
      (hremove
        : lookupFragmentAndRestLt? removedName fragments = some (removed, remaining))
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
            {fieldDefinition : FieldDefinition} {selectionSet : List Selection},
          removedName
            ∉ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                selectionSet
          -> GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
              variableDefinitions fragments fieldDefinition selectionSet
          -> GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
              variableDefinitions remaining.val fieldDefinition selectionSet
    | schema, variableDefinitions, fieldDefinition, selectionSet,
        hnoSpread, hvalid => by
        simp [GraphQL.NamedFragment.Validation.fieldSelectionSetValid] at hvalid ⊢
        rcases hvalid with ⟨houtput, hshape⟩
        refine ⟨houtput, ?_⟩
        cases hshape with
        | inl hleaf =>
            exact Or.inl hleaf
        | inr hcomposite =>
            rcases hcomposite with
              ⟨hcompositeType, hnonempty, hselectionSetValid⟩
            exact Or.inr ⟨hcompositeType, hnonempty,
              selectionSetValid_after_fragment_removal hremove hnoSpread
                hselectionSetValid⟩
end

theorem fragmentSelectionSetValid_after_lookup_removal_of_no_spread
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hfragmentValid
      : GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
          variableDefinitions fragments fragment)
    (hnoRemoved
      : fragmentName
        ∉ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
            fragment.selectionSet)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions remaining.val fragment.typeCondition
        fragment.selectionSet := by
  rcases hfragmentValid with
    ⟨_hcomposite, _hnonempty, hselectionSetValid⟩
  exact selectionSetValid_after_fragment_removal hlookup hnoRemoved
    hselectionSetValid

theorem allFragmentDefinitionsValid_after_lookup_removal_of_no_spread
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hnoRemoved
      : ∀ candidate,
          candidate ∈ remaining.val
          -> fragmentName
              ∉ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                  candidate.selectionSet)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
        variableDefinitions remaining.val := by
  intro candidate hcandidate
  have hcandidateValid :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments candidate :=
    hall candidate
      (GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
        hlookup candidate hcandidate)
  rcases hcandidateValid with
    ⟨hcomposite, hnonempty, hselectionSetValid⟩
  exact ⟨hcomposite, hnonempty,
    selectionSetValid_after_fragment_removal hlookup
      (hnoRemoved candidate hcandidate) hselectionSetValid⟩

theorem lookupFragmentAndRestLt?_remaining_length_lt
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
      -> remaining.val.length < fragments.length := by
  intro _hlookup
  exact remaining.property

inductive ReachableAncestorRemovals
    (original : List FragmentDefinition) (targetName : Name)
    (final : List FragmentDefinition)
    : List FragmentDefinition -> Prop where
  | root : ReachableAncestorRemovals original targetName final original
  | remove
    {current : List FragmentDefinition}
    {ancestorName : Name} {ancestor : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < current.length }}
    {fuel : Nat}
    (hprevious : ReachableAncestorRemovals original targetName final current)
    (hancestorMem : ancestor ∈ original)
    (hlookup : lookupFragmentAndRestLt? ancestorName current = some (ancestor, remaining))
    (hreachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool original fuel
          ancestor.name targetName
        = true)
    (hfuel : fuel + final.length ≤ original.length)
    : ReachableAncestorRemovals original targetName final remaining.val

theorem ReachableAncestorRemovals.length_le_original
    {original final current : List FragmentDefinition}
    {targetName : Name}
    (hremovals : ReachableAncestorRemovals original targetName final current)
    : current.length ≤ original.length := by
  induction hremovals with
  | root =>
      exact Nat.le_refl original.length
  | remove hprevious _hancestorMem _hlookup _hreachable _hfuel ih =>
      exact Nat.le_trans
        (Nat.le_of_lt
          (lookupFragmentAndRestLt?_remaining_length_lt _hlookup))
        ih

theorem ReachableAncestorRemovals.mem_original
    {original final current : List FragmentDefinition}
    {targetName : Name}
    (hremovals : ReachableAncestorRemovals original targetName final current)
    {fragment : FragmentDefinition}
    (hmem : fragment ∈ current)
    : fragment ∈ original := by
  induction hremovals with
  | root =>
      exact hmem
  | remove hprevious _hancestorMem hlookup _hreachable _hfuel ih =>
      exact ih
        (GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
          hlookup fragment hmem)

theorem ReachableAncestorRemovals.retarget_direct
    {original parentFinal childFinal current : List FragmentDefinition}
    {parentName childName : Name} {parent : FragmentDefinition}
    (hremovals : ReachableAncestorRemovals original parentName parentFinal current)
    (hparentLookup
      : GraphQL.NamedFragment.lookupFragment? original parentName = some parent)
    (hparentSpread
      : childName
        ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
            parent.selectionSet)
    (hfinalLength : childFinal.length + 1 ≤ parentFinal.length)
    : ReachableAncestorRemovals original childName childFinal current := by
  induction hremovals with
  | root =>
      exact ReachableAncestorRemovals.root
  | remove hprevious hancestorMem hlookup hreachable hfuel ih =>
      exact ReachableAncestorRemovals.remove ih hancestorMem hlookup
        (GraphQL.NamedFragment.Validation.fragmentReachableBool_append_direct
          hreachable hparentLookup hparentSpread)
        (by omega)

theorem ReachableAncestorRemovals.child
    {original current : List FragmentDefinition}
    {parentName childName : Name}
    {parent : FragmentDefinition}
    {parentRemaining
      : { parentRemaining : List FragmentDefinition
          // parentRemaining.length < current.length }}
    (hremovals : ReachableAncestorRemovals original parentName current current)
    (hparentMem : parent ∈ original)
    (hparentLookupOriginal
      : GraphQL.NamedFragment.lookupFragment? original parentName = some parent)
    (hparentLookupCurrent
      : lookupFragmentAndRestLt? parentName current = some (parent, parentRemaining))
    (hparentSpread
      : childName
        ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
            parent.selectionSet)
    : ReachableAncestorRemovals original childName parentRemaining.val
        parentRemaining.val := by
  have hretarget :
      ReachableAncestorRemovals original childName parentRemaining.val
        current :=
    ReachableAncestorRemovals.retarget_direct hremovals
      hparentLookupOriginal hparentSpread
      (Nat.succ_le_of_lt parentRemaining.property)
  have hparentName : parent.name = parentName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      hparentLookupCurrent
  have hparentLookupByOwnName :
      GraphQL.NamedFragment.lookupFragment? original parent.name =
        some parent := by
    simpa [hparentName] using hparentLookupOriginal
  have hreachable :
      GraphQL.NamedFragment.Validation.fragmentReachableBool original 1
        parent.name childName = true := by
    simpa using
      (GraphQL.NamedFragment.Validation.fragmentReachableBool_direct
        hparentLookupByOwnName hparentSpread 0)
  have hcurrentLength :
      current.length ≤ original.length :=
    ReachableAncestorRemovals.length_le_original hremovals
  exact ReachableAncestorRemovals.remove hretarget hparentMem
    hparentLookupCurrent hreachable (by omega)

theorem selectionSetValid_after_reachable_ancestor_removals
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {original final current : List FragmentDefinition}
    {targetName : Name} {target : FragmentDefinition}
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (hremovals : ReachableAncestorRemovals original targetName final current)
    (htargetLookup
      : GraphQL.NamedFragment.lookupFragment? original targetName = some target)
    (htargetFinal : target ∈ final)
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions current target.typeCondition target.selectionSet := by
  induction hremovals with
  | root =>
      exact (hall target
        (GraphQL.NamedFragment.Validation.lookupFragment?_found_mem
          htargetLookup)).2.2
  | remove hprevious hancestorMem hlookup hreachable hfuel ih =>
      have hnoAncestor :=
        GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_spread_to_reachable_source
          hacyclic hancestorMem hreachable
          (by
            have hfinalNonempty :=
              List.length_pos_of_mem htargetFinal
            omega)
          htargetLookup
      have hancestorName :=
        GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
          hlookup
      exact selectionSetValid_after_fragment_removal hlookup
        (by
          intro hspread
          exact hnoAncestor (by simpa [hancestorName] using hspread))
        ih

theorem fragmentDefinitionValid_after_reachable_ancestor_removals
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {original final current : List FragmentDefinition}
    {targetName : Name} {target : FragmentDefinition}
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (hremovals : ReachableAncestorRemovals original targetName final current)
    (htargetLookup
      : GraphQL.NamedFragment.lookupFragment? original targetName = some target)
    (htargetFinal : target ∈ final)
    : GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions current target := by
  have htargetValidOriginal :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions original target :=
    hall target
      (GraphQL.NamedFragment.Validation.lookupFragment?_found_mem
        htargetLookup)
  rcases htargetValidOriginal with
    ⟨hcomposite, hnonempty, _hselectionValid⟩
  exact ⟨hcomposite, hnonempty,
    selectionSetValid_after_reachable_ancestor_removals hacyclic hall
      hremovals htargetLookup htargetFinal⟩

theorem descendantSelectionSetValid_after_ancestor_lookup_removal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {ancestorName targetName : Name}
    {ancestor target : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {fuel : Nat}
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hancestorLookup
      : lookupFragmentAndRestLt? ancestorName fragments = some (ancestor, remaining))
    (hreachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments fuel
          ancestor.name targetName
        = true)
    (hle : fuel + 1 ≤ fragments.length)
    (htargetLookup
      : GraphQL.NamedFragment.lookupFragment? fragments targetName = some target)
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions remaining.val target.typeCondition
        target.selectionSet := by
  have hancestorMem : ancestor ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      hancestorLookup
  have htargetValid :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments target :=
    hall target
      (GraphQL.NamedFragment.Validation.lookupFragment?_found_mem
        htargetLookup)
  rcases htargetValid with
    ⟨_htargetComposite, _htargetNonempty, htargetSelectionValid⟩
  have hnoAncestor :
      ancestor.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_spread_to_reachable_source
      hacyclic hancestorMem hreachable hle htargetLookup
  have hancestorName : ancestor.name = ancestorName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      hancestorLookup
  have hnoAncestorName :
      ancestorName ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet := by
    intro hspread
    exact hnoAncestor (by simpa [hancestorName] using hspread)
  exact selectionSetValid_after_fragment_removal hancestorLookup
    hnoAncestorName htargetSelectionValid

theorem descendantFragmentDefinitionValid_after_ancestor_lookup_removal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {ancestorName targetName : Name}
    {ancestor target : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {targetRemaining
      : { targetRemaining : List FragmentDefinition
          // targetRemaining.length < remaining.val.length }}
    {fuel : Nat}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hancestorLookup
      : lookupFragmentAndRestLt? ancestorName fragments = some (ancestor, remaining))
    (hreachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments fuel
          ancestor.name targetName
        = true)
    (hle : fuel + 1 ≤ fragments.length)
    (htargetLookup
      : lookupFragmentAndRestLt? targetName remaining.val
        = some (target, targetRemaining))
    : GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions remaining.val target := by
  have htargetLookupOriginal :
      GraphQL.NamedFragment.lookupFragment? fragments targetName =
        some target :=
    GraphQL.NamedFragment.Validation.lookupFragment?_of_lookupFragmentAndRestLt?_remaining_original
      hunique hancestorLookup htargetLookup
  have htargetValidOriginal :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments target :=
    hall target
      (GraphQL.NamedFragment.Validation.lookupFragment?_found_mem
        htargetLookupOriginal)
  rcases htargetValidOriginal with
    ⟨htargetComposite, htargetNonempty, _htargetSelectionValid⟩
  exact ⟨htargetComposite, htargetNonempty,
    descendantSelectionSetValid_after_ancestor_lookup_removal hacyclic hall
      hancestorLookup hreachable hle htargetLookupOriginal⟩

theorem childFragmentDefinitionValid_after_ancestor_lookup_removal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {ancestorName targetName : Name}
    {ancestor target : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {targetRemaining
      : { targetRemaining : List FragmentDefinition
          // targetRemaining.length < remaining.val.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hancestorLookup
      : lookupFragmentAndRestLt? ancestorName fragments = some (ancestor, remaining))
    (hancestorSpread
      : targetName
        ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
            ancestor.selectionSet)
    (htargetLookup
      : lookupFragmentAndRestLt? targetName remaining.val
        = some (target, targetRemaining))
    : GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions remaining.val target := by
  have hancestorName : ancestor.name = ancestorName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      hancestorLookup
  have hreachable :
      GraphQL.NamedFragment.Validation.fragmentReachableBool fragments 1
        ancestor.name targetName = true := by
    have hdirect :
        GraphQL.NamedFragment.Validation.fragmentReachableBool fragments
          (0 + 1) ancestorName targetName = true :=
      GraphQL.NamedFragment.Validation.fragmentReachableBool_direct_of_lookupFragmentAndRestLt?
        hancestorLookup hancestorSpread 0
    simpa [hancestorName] using hdirect
  have htargetMemRemaining : target ∈ remaining.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      htargetLookup
  have hremainingNonempty : 0 < remaining.val.length := by
    exact List.length_pos_of_mem htargetMemRemaining
  exact descendantFragmentDefinitionValid_after_ancestor_lookup_removal
    hunique hacyclic hall hancestorLookup hreachable
    (by omega) htargetLookup

theorem descendantSelectionSetValid_after_two_ancestor_lookup_removals
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {firstName secondName targetName : Name}
    {first second target : FragmentDefinition}
    {afterFirst
      : { afterFirst : List FragmentDefinition // afterFirst.length < fragments.length }}
    {afterSecond
      : { afterSecond : List FragmentDefinition
          // afterSecond.length < afterFirst.val.length }}
    {firstFuel secondFuel : Nat}
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hfirstLookup
      : lookupFragmentAndRestLt? firstName fragments = some (first, afterFirst))
    (hsecondLookup
      : lookupFragmentAndRestLt? secondName afterFirst.val = some (second, afterSecond))
    (hfirstReachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments
          firstFuel first.name targetName
        = true)
    (hfirstFuel : firstFuel + 1 ≤ fragments.length)
    (hsecondReachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments
          secondFuel second.name targetName
        = true)
    (hsecondFuel : secondFuel + 1 ≤ fragments.length)
    (htargetLookup
      : GraphQL.NamedFragment.lookupFragment? fragments targetName = some target)
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions afterSecond.val target.typeCondition
        target.selectionSet := by
  have htargetSelectionAfterFirst :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions afterFirst.val target.typeCondition
        target.selectionSet :=
    descendantSelectionSetValid_after_ancestor_lookup_removal hacyclic hall
      hfirstLookup hfirstReachable hfirstFuel htargetLookup
  have hsecondMemAfterFirst : second ∈ afterFirst.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      hsecondLookup
  have hsecondMem : second ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
      hfirstLookup second hsecondMemAfterFirst
  have hnoSecond :
      second.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_spread_to_reachable_source
      hacyclic hsecondMem hsecondReachable hsecondFuel htargetLookup
  have hsecondName : second.name = secondName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      hsecondLookup
  have hnoSecondName :
      secondName ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet := by
    intro hspread
    exact hnoSecond (by simpa [hsecondName] using hspread)
  exact selectionSetValid_after_fragment_removal hsecondLookup
    hnoSecondName htargetSelectionAfterFirst

theorem descendantFragmentDefinitionValid_after_two_ancestor_lookup_removals
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {firstName secondName targetName : Name}
    {first second target : FragmentDefinition}
    {afterFirst
      : { afterFirst : List FragmentDefinition // afterFirst.length < fragments.length }}
    {afterSecond
      : { afterSecond : List FragmentDefinition
          // afterSecond.length < afterFirst.val.length }}
    {targetRemaining
      : { targetRemaining : List FragmentDefinition
          // targetRemaining.length < afterSecond.val.length }}
    {firstFuel secondFuel : Nat}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hfirstLookup
      : lookupFragmentAndRestLt? firstName fragments = some (first, afterFirst))
    (hsecondLookup
      : lookupFragmentAndRestLt? secondName afterFirst.val = some (second, afterSecond))
    (hfirstReachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments
          firstFuel first.name targetName
        = true)
    (hfirstFuel : firstFuel + 1 ≤ fragments.length)
    (hsecondReachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments
          secondFuel second.name targetName
        = true)
    (hsecondFuel : secondFuel + 1 ≤ fragments.length)
    (htargetLookup
      : lookupFragmentAndRestLt? targetName afterSecond.val
        = some (target, targetRemaining))
    : GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions afterSecond.val target := by
  have htargetMemAfterSecond : target ∈ afterSecond.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      htargetLookup
  have htargetMemAfterFirst : target ∈ afterFirst.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
      hsecondLookup target htargetMemAfterSecond
  have htargetMem : target ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
      hfirstLookup target htargetMemAfterFirst
  have htargetName : target.name = targetName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      htargetLookup
  have htargetLookupOriginal :
      GraphQL.NamedFragment.lookupFragment? fragments targetName =
        some target := by
    have hlookupByOwnName :
        GraphQL.NamedFragment.lookupFragment? fragments target.name =
          some target :=
      GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
        hunique htargetMem
    simpa [htargetName] using hlookupByOwnName
  have htargetValidOriginal :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments target :=
    hall target htargetMem
  rcases htargetValidOriginal with
    ⟨htargetComposite, htargetNonempty, _htargetSelectionValid⟩
  exact ⟨htargetComposite, htargetNonempty,
    descendantSelectionSetValid_after_two_ancestor_lookup_removals hacyclic
      hall hfirstLookup hsecondLookup hfirstReachable hfirstFuel
      hsecondReachable hsecondFuel htargetLookupOriginal⟩

theorem fragmentSelectionSetValid_after_lookup_removal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions remaining.val fragment.typeCondition
        fragment.selectionSet := by
  have hfragmentValid :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments fragment :=
    GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid_of_lookupFragmentAndRestLt?
      hall hlookup
  rcases hfragmentValid with
    ⟨_hcomposite, _hnonempty, hselectionSetValid⟩
  have hmem : fragment ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      hlookup
  have hnoSelf :
      fragment.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          fragment.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_self_spread
      hunique hacyclic hmem
  have hname : fragment.name = fragmentName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      hlookup
  have hnoRemoved :
      fragmentName ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          fragment.selectionSet := by
    intro hspread
    exact hnoSelf (by simpa [hname] using hspread)
  exact fragmentSelectionSetValid_after_lookup_removal_of_no_spread
    ⟨_hcomposite, _hnonempty, hselectionSetValid⟩ hnoRemoved hlookup

theorem fragmentInlineSelectionSetValid_after_reachable_removals_aux
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {original : List FragmentDefinition}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    : ∀ n {current : List FragmentDefinition}
          {fragmentName : Name} {fragment : FragmentDefinition}
          {remaining
            : { remaining : List FragmentDefinition
                // remaining.length < current.length }},
        current.length ≤ n
        -> ReachableAncestorRemovals original fragmentName current current
        -> GraphQL.NamedFragment.lookupFragment? original fragmentName = some fragment
        -> lookupFragmentAndRestLt? fragmentName current = some (fragment, remaining)
        -> fragment.selectionSet ≠ []
            ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                variableDefinitions [] fragment.typeCondition
                (Inline.inlineSelectionSet remaining.val fragment.selectionSet) := by
  intro n
  induction n with
  | zero =>
      intro current _fragmentName _fragment remaining hlength _hremovals
        _hlookupOriginal hlookup
      have hfragmentMemCurrent :
          _fragment ∈ current :=
        GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
          hlookup
      have hcurrentPositive : 0 < current.length :=
        List.length_pos_of_mem hfragmentMemCurrent
      omega
  | succ n ih =>
      intro current fragmentName fragment remaining hlength hremovals
        hlookupOriginal hlookup
      have hfragmentMemCurrent : fragment ∈ current :=
        GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
          hlookup
      have hfragmentMemOriginal : fragment ∈ original :=
        ReachableAncestorRemovals.mem_original hremovals hfragmentMemCurrent
      have hfragmentValidCurrent :
          GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
            variableDefinitions current fragment :=
        fragmentDefinitionValid_after_reachable_ancestor_removals hacyclic
          hall hremovals hlookupOriginal hfragmentMemCurrent
      rcases hfragmentValidCurrent with
        ⟨_hcomposite, hnonempty, hselectionSetValidCurrent⟩
      have hnoSelf :
          fragment.name ∉
            GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
              fragment.selectionSet :=
        GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_self_spread
          hunique hacyclic hfragmentMemOriginal
      have hfragmentName : fragment.name = fragmentName :=
        GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
          hlookup
      have hnoFragmentName :
          fragmentName ∉
            GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
              fragment.selectionSet := by
        intro hspread
        exact hnoSelf (by simpa [hfragmentName] using hspread)
      have hselectionSetValidRemaining :
          GraphQL.NamedFragment.Validation.selectionSetValid schema
            variableDefinitions remaining.val fragment.typeCondition
            fragment.selectionSet :=
        selectionSetValid_after_fragment_removal hlookup hnoFragmentName
          hselectionSetValidCurrent
      exact ⟨hnonempty,
        selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
          (fun {childName} {childFragment} {childRemaining} hchildSpread
              hchildLookup => by
            have hchildMemRemaining : childFragment ∈ remaining.val :=
              GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
                hchildLookup
            have hchildMemCurrent : childFragment ∈ current :=
              GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
                hlookup childFragment hchildMemRemaining
            have hchildMemOriginal : childFragment ∈ original :=
              ReachableAncestorRemovals.mem_original hremovals hchildMemCurrent
            have hchildName : childFragment.name = childName :=
              GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
                hchildLookup
            have hchildLookupOriginal :
                GraphQL.NamedFragment.lookupFragment? original
                    childName =
                  some childFragment := by
              have hlookupByOwnName :
                  GraphQL.NamedFragment.lookupFragment? original
                      childFragment.name =
                    some childFragment :=
                GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
                  hunique hchildMemOriginal
              simpa [hchildName] using hlookupByOwnName
            have hchildRemovals :
                ReachableAncestorRemovals original childName remaining.val
                  remaining.val :=
              ReachableAncestorRemovals.child hremovals
                hfragmentMemOriginal hlookupOriginal hlookup hchildSpread
            have hremainingLength : remaining.val.length ≤ n := by
              have hremainingLt :
                  remaining.val.length < current.length :=
                lookupFragmentAndRestLt?_remaining_length_lt hlookup
              omega
            exact ih hremainingLength hchildRemovals
              hchildLookupOriginal hchildLookup)
          hselectionSetValidRemaining⟩

theorem fragmentInlineSelectionSetValid_after_reachable_removals
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
    : fragment.selectionSet ≠ []
      ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions [] fragment.typeCondition
          (Inline.inlineSelectionSet remaining.val fragment.selectionSet) := by
  exact fragmentInlineSelectionSetValid_after_reachable_removals_aux
    hunique hacyclic hall current.length (Nat.le_refl current.length)
    hremovals hlookupOriginal hlookup

theorem fragmentInlineSelectionSetValid_after_lookup_removal_of_fragmentBodiesValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    (hremainingBodies
      : ∀ {nextName : Name} {nextFragment : FragmentDefinition}
            {nextRemaining
              : { nextRemaining : List FragmentDefinition
                  // nextRemaining.length < remaining.val.length }},
          lookupFragmentAndRestLt? nextName remaining.val
            = some (nextFragment, nextRemaining)
          -> nextFragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  variableDefinitions [] nextFragment.typeCondition
                  (Inline.inlineSelectionSet nextRemaining.val nextFragment.selectionSet))
    : fragment.selectionSet ≠ []
      ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions [] fragment.typeCondition
          (Inline.inlineSelectionSet remaining.val fragment.selectionSet) := by
  have hfragmentValid :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments fragment :=
    GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid_of_lookupFragmentAndRestLt?
      hall hlookup
  rcases hfragmentValid with ⟨_hcomposite, hnonempty, _hselectionSetValid⟩
  have hselectionSetValid :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions remaining.val fragment.typeCondition
        fragment.selectionSet :=
    fragmentSelectionSetValid_after_lookup_removal hunique hacyclic hall hlookup
  exact ⟨hnonempty,
    selectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
      hremainingBodies hselectionSetValid⟩

theorem fragmentInlineSelectionSetValid_after_lookup_removal_of_localFragmentBodiesValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition}
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    (hremainingBodies
      : ∀ {nextName : Name} {nextFragment : FragmentDefinition}
            {nextRemaining
              : { nextRemaining : List FragmentDefinition
                  // nextRemaining.length < remaining.val.length }},
          nextName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                fragment.selectionSet
          -> lookupFragmentAndRestLt? nextName remaining.val
              = some (nextFragment, nextRemaining)
          -> nextFragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  variableDefinitions [] nextFragment.typeCondition
                  (Inline.inlineSelectionSet nextRemaining.val nextFragment.selectionSet))
    : fragment.selectionSet ≠ []
      ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions [] fragment.typeCondition
          (Inline.inlineSelectionSet remaining.val fragment.selectionSet) := by
  have hfragmentValid :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments fragment :=
    GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid_of_lookupFragmentAndRestLt?
      hall hlookup
  rcases hfragmentValid with ⟨_hcomposite, hnonempty, _hselectionSetValid⟩
  have hselectionSetValid :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions remaining.val fragment.typeCondition
        fragment.selectionSet :=
    fragmentSelectionSetValid_after_lookup_removal hunique hacyclic hall hlookup
  exact ⟨hnonempty,
    selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
      hremainingBodies hselectionSetValid⟩

theorem operationFragmentInlineSelectionSetValid_after_lookup_removal
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    {fragmentName : Name} {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition
          // remaining.length < operation.fragmentDefinitions.length }}
    (hlookup
      : lookupFragmentAndRestLt? fragmentName operation.fragmentDefinitions
        = some (fragment, remaining))
    (hremainingBodies
      : ∀ {nextName : Name} {nextFragment : FragmentDefinition}
            {nextRemaining
              : { nextRemaining : List FragmentDefinition
                  // nextRemaining.length < remaining.val.length }},
          nextName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                fragment.selectionSet
          -> lookupFragmentAndRestLt? nextName remaining.val
              = some (nextFragment, nextRemaining)
          -> nextFragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  operation.variableDefinitions [] nextFragment.typeCondition
                  (Inline.inlineSelectionSet nextRemaining.val nextFragment.selectionSet))
    : fragment.selectionSet ≠ []
      ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
          operation.variableDefinitions [] fragment.typeCondition
          (Inline.inlineSelectionSet remaining.val fragment.selectionSet) := by
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, huniqueFragments,
      hfragmentsAcyclic, hfragmentDefinitionsValid, _hselectionNonempty,
      _hselectionValid, _hmerge, _hvariablesUsed⟩
  exact fragmentInlineSelectionSetValid_after_lookup_removal_of_localFragmentBodiesValid
    huniqueFragments hfragmentsAcyclic hfragmentDefinitionsValid
    hlookup hremainingBodies

theorem childFragmentInlineSelectionSetValid_after_lookup_removals_of_localFragmentBodiesValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition} {sourceName childName : Name}
    {source child : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {childRemaining
      : { childRemaining : List FragmentDefinition
          // childRemaining.length < remaining.val.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hsourceLookup
      : lookupFragmentAndRestLt? sourceName fragments = some (source, remaining))
    (hsourceSpread
      : childName
        ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
            source.selectionSet)
    (hchildLookup
      : lookupFragmentAndRestLt? childName remaining.val = some (child, childRemaining))
    (hchildBodies
      : ∀ {nextName : Name} {nextFragment : FragmentDefinition}
            {nextRemaining
              : { nextRemaining : List FragmentDefinition
                  // nextRemaining.length < childRemaining.val.length }},
          nextName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                child.selectionSet
          -> lookupFragmentAndRestLt? nextName childRemaining.val
              = some (nextFragment, nextRemaining)
          -> nextFragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  variableDefinitions [] nextFragment.typeCondition
                  (Inline.inlineSelectionSet nextRemaining.val nextFragment.selectionSet))
    : child.selectionSet ≠ []
      ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions [] child.typeCondition
          (Inline.inlineSelectionSet childRemaining.val child.selectionSet) := by
  have hsourceMem : source ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      hsourceLookup
  have hchildMemRemaining : child ∈ remaining.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      hchildLookup
  have hchildMem : child ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
      hsourceLookup child hchildMemRemaining
  have hchildValidOriginal :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments child :=
    hall child hchildMem
  rcases hchildValidOriginal with
    ⟨hchildComposite, hchildNonempty, hchildSelectionValidOriginal⟩
  have hchildName : child.name = childName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      hchildLookup
  have hchildLookupOriginal :
      GraphQL.NamedFragment.lookupFragment? fragments childName =
        some child := by
    have hlookupByOwnName :
        GraphQL.NamedFragment.lookupFragment? fragments child.name =
          some child :=
      GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
        hunique hchildMem
    simpa [hchildName] using hlookupByOwnName
  have hnoBack :
      source.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          child.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_back_spread
      hunique hacyclic hsourceMem hsourceSpread hchildLookupOriginal
  have hsourceName : source.name = sourceName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      hsourceLookup
  have hnoSourceName :
      sourceName ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          child.selectionSet := by
    intro hspread
    exact hnoBack (by simpa [hsourceName] using hspread)
  have hchildSelectionValidRemaining :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions remaining.val child.typeCondition
        child.selectionSet :=
    selectionSetValid_after_fragment_removal hsourceLookup hnoSourceName
      hchildSelectionValidOriginal
  have hnoChildSelf :
      child.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          child.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_self_spread
      hunique hacyclic hchildMem
  have hnoChildName :
      childName ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          child.selectionSet := by
    intro hspread
    exact hnoChildSelf (by simpa [hchildName] using hspread)
  have hchildSelectionValidAfterChildRemoval :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions childRemaining.val child.typeCondition
        child.selectionSet :=
    selectionSetValid_after_fragment_removal hchildLookup hnoChildName
      hchildSelectionValidRemaining
  exact ⟨hchildNonempty,
    selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
      hchildBodies hchildSelectionValidAfterChildRemoval⟩

theorem descendantFragmentInlineSelectionSetValid_after_lookup_removals_of_localFragmentBodiesValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition} {ancestorName targetName : Name}
    {ancestor target : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    {targetRemaining
      : { targetRemaining : List FragmentDefinition
          // targetRemaining.length < remaining.val.length }}
    {fuel : Nat}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hancestorLookup
      : lookupFragmentAndRestLt? ancestorName fragments = some (ancestor, remaining))
    (hreachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments fuel
          ancestor.name targetName
        = true)
    (hle : fuel + 1 ≤ fragments.length)
    (htargetLookup
      : lookupFragmentAndRestLt? targetName remaining.val
        = some (target, targetRemaining))
    (htargetBodies
      : ∀ {nextName : Name} {nextFragment : FragmentDefinition}
            {nextRemaining
              : { nextRemaining : List FragmentDefinition
                  // nextRemaining.length < targetRemaining.val.length }},
          nextName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                target.selectionSet
          -> lookupFragmentAndRestLt? nextName targetRemaining.val
              = some (nextFragment, nextRemaining)
          -> nextFragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  variableDefinitions [] nextFragment.typeCondition
                  (Inline.inlineSelectionSet nextRemaining.val nextFragment.selectionSet))
    : target.selectionSet ≠ []
      ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions [] target.typeCondition
          (Inline.inlineSelectionSet targetRemaining.val target.selectionSet) := by
  have htargetMemRemaining : target ∈ remaining.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      htargetLookup
  have htargetMem : target ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
      hancestorLookup target htargetMemRemaining
  have htargetName : target.name = targetName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      htargetLookup
  have htargetLookupOriginal :
      GraphQL.NamedFragment.lookupFragment? fragments targetName =
        some target := by
    have hlookupByOwnName :
        GraphQL.NamedFragment.lookupFragment? fragments target.name =
          some target :=
      GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
        hunique htargetMem
    simpa [htargetName] using hlookupByOwnName
  have htargetValidOriginal :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments target :=
    hall target htargetMem
  rcases htargetValidOriginal with
    ⟨_htargetComposite, htargetNonempty, _htargetSelectionValidOriginal⟩
  have htargetSelectionValidRemaining :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions remaining.val target.typeCondition
        target.selectionSet :=
    descendantSelectionSetValid_after_ancestor_lookup_removal hacyclic hall
      hancestorLookup hreachable hle htargetLookupOriginal
  have hnoTargetSelf :
      target.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_self_spread
      hunique hacyclic htargetMem
  have hnoTargetName :
      targetName ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet := by
    intro hspread
    exact hnoTargetSelf (by simpa [htargetName] using hspread)
  have htargetSelectionValidAfterTargetRemoval :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions targetRemaining.val target.typeCondition
        target.selectionSet :=
    selectionSetValid_after_fragment_removal htargetLookup hnoTargetName
      htargetSelectionValidRemaining
  exact ⟨htargetNonempty,
    selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
      htargetBodies htargetSelectionValidAfterTargetRemoval⟩

theorem descendantFragmentInlineSelectionSetValid_after_two_ancestor_lookup_removals_of_localFragmentBodiesValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition} {firstName secondName targetName : Name}
    {first second target : FragmentDefinition}
    {afterFirst
      : { afterFirst : List FragmentDefinition // afterFirst.length < fragments.length }}
    {afterSecond
      : { afterSecond : List FragmentDefinition
          // afterSecond.length < afterFirst.val.length }}
    {targetRemaining
      : { targetRemaining : List FragmentDefinition
          // targetRemaining.length < afterSecond.val.length }}
    {firstFuel secondFuel : Nat}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hfirstLookup
      : lookupFragmentAndRestLt? firstName fragments = some (first, afterFirst))
    (hsecondLookup
      : lookupFragmentAndRestLt? secondName afterFirst.val = some (second, afterSecond))
    (hfirstReachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments
          firstFuel first.name targetName
        = true)
    (hfirstFuel : firstFuel + 1 ≤ fragments.length)
    (hsecondReachable
      : GraphQL.NamedFragment.Validation.fragmentReachableBool fragments
          secondFuel second.name targetName
        = true)
    (hsecondFuel : secondFuel + 1 ≤ fragments.length)
    (htargetLookup
      : lookupFragmentAndRestLt? targetName afterSecond.val
        = some (target, targetRemaining))
    (htargetBodies
      : ∀ {nextName : Name} {nextFragment : FragmentDefinition}
            {nextRemaining
              : { nextRemaining : List FragmentDefinition
                  // nextRemaining.length < targetRemaining.val.length }},
          nextName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                target.selectionSet
          -> lookupFragmentAndRestLt? nextName targetRemaining.val
              = some (nextFragment, nextRemaining)
          -> nextFragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  variableDefinitions [] nextFragment.typeCondition
                  (Inline.inlineSelectionSet nextRemaining.val nextFragment.selectionSet))
    : target.selectionSet ≠ []
      ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions [] target.typeCondition
          (Inline.inlineSelectionSet targetRemaining.val target.selectionSet) := by
  have htargetMemAfterSecond : target ∈ afterSecond.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem
      htargetLookup
  have htargetMemAfterFirst : target ∈ afterFirst.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
      hsecondLookup target htargetMemAfterSecond
  have htargetMem : target ∈ fragments :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_remaining_mem
      hfirstLookup target htargetMemAfterFirst
  have htargetName : target.name = targetName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name
      htargetLookup
  have htargetLookupOriginal :
      GraphQL.NamedFragment.lookupFragment? fragments targetName =
        some target := by
    have hlookupByOwnName :
        GraphQL.NamedFragment.lookupFragment? fragments target.name =
          some target :=
      GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
        hunique htargetMem
    simpa [htargetName] using hlookupByOwnName
  have htargetValidOriginal :
      GraphQL.NamedFragment.Validation.fragmentDefinitionValid schema
        variableDefinitions fragments target :=
    hall target htargetMem
  rcases htargetValidOriginal with
    ⟨_htargetComposite, htargetNonempty, _htargetSelectionValidOriginal⟩
  have htargetSelectionValidAfterAncestors :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions afterSecond.val target.typeCondition
        target.selectionSet :=
    descendantSelectionSetValid_after_two_ancestor_lookup_removals hacyclic
      hall hfirstLookup hsecondLookup hfirstReachable hfirstFuel
      hsecondReachable hsecondFuel htargetLookupOriginal
  have hnoTargetSelf :
      target.name ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet :=
    GraphQL.NamedFragment.Validation.fragmentsAcyclic_no_direct_self_spread
      hunique hacyclic htargetMem
  have hnoTargetName :
      targetName ∉
        GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
          target.selectionSet := by
    intro hspread
    exact hnoTargetSelf (by simpa [htargetName] using hspread)
  have htargetSelectionValidAfterTargetRemoval :
      GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions targetRemaining.val target.typeCondition
        target.selectionSet :=
    selectionSetValid_after_fragment_removal htargetLookup hnoTargetName
      htargetSelectionValidAfterAncestors
  exact ⟨htargetNonempty,
    selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
      htargetBodies htargetSelectionValidAfterTargetRemoval⟩

end Semantics
end NamedFragment
end GraphQL
