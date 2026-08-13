import Proofs.GraphQL.Execution.DuplicateFields
import Proofs.GraphQL.NamedFragment.Semantics.Inline.ExpansionStability
import Proofs.GraphQL.NamedFragment.Semantics.Inline.Translate

/-! Collection correspondence for spec `visitedFragments`. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

namespace VisitedFragments

open GraphQL.Execution.DuplicateFields

set_option maxHeartbeats 1000000

variable {ObjectRef : Type}

def expandedExecutableFieldToSpec (field : Execution.ExecutableField)
    : GraphQL.Execution.ExecutableField :=
  {
    parentType := field.parentType
    responseName := field.responseName
    fieldName := field.fieldName
    arguments := field.arguments
    selectionSet :=
      Translate.reduceSelectionSet
        (Inline.inlineSelectionSet field.availableFragments field.selectionSet)
  }

def expandedExecutableGroupToSpec (group : Name × List Execution.ExecutableField)
    : Name × List GraphQL.Execution.ExecutableField :=
  (group.fst, group.snd.map expandedExecutableFieldToSpec)

def expandedExecutableGroupsToSpec (groups : List (Name × List Execution.ExecutableField))
    : List (Name × List GraphQL.Execution.ExecutableField) :=
  groups.map expandedExecutableGroupToSpec

def selectionToSpecAfterInline
    (fragments : List FragmentDefinition) (selection : Selection)
    : GraphQL.Selection :=
  inlinedSelectionToSpec (Inline.inlineSelection fragments selection)

theorem reduce_inlineSelection
    (fragments : List FragmentDefinition) (selection : Selection)
    : Translate.reduceSelection (Inline.inlineSelection fragments selection)
      = [selectionToSpecAfterInline fragments selection] := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simp [selectionToSpecAfterInline, inlinedSelectionToSpec,
        Inline.inlineSelection, Translate.reduceSelection]
  | inlineFragment typeCondition directives selectionSet =>
      simp [selectionToSpecAfterInline, inlinedSelectionToSpec,
        Inline.inlineSelection, Translate.reduceSelection]
  | fragmentSpread fragmentName directives =>
      simp [selectionToSpecAfterInline, inlinedSelectionToSpec,
        Inline.inlineSelection]
      cases hlookup : lookupFragmentAndRestLt? fragmentName fragments with
      | none => simp [Translate.reduceSelection]
      | some pair =>
          rcases pair with ⟨fragment, remaining⟩
          simp [Translate.reduceSelection]

theorem reduce_inlineSelectionSet
    (fragments : List FragmentDefinition) (selectionSet : List Selection)
    : Translate.reduceSelectionSet (Inline.inlineSelectionSet fragments selectionSet)
      = selectionSet.map (selectionToSpecAfterInline fragments) := by
  induction selectionSet with
  | nil => simp [Translate.reduceSelectionSet]
  | cons selection rest ih =>
      simp [Inline.inlineSelectionSet, Translate.reduceSelectionSet,
        reduce_inlineSelection fragments selection, ih,
        selectionToSpecAfterInline]

theorem expanded_addExecutableGroup
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : expandedExecutableGroupsToSpec (Execution.addExecutableGroup group groups)
      = GraphQL.Execution.addExecutableGroup
          (expandedExecutableGroupToSpec group)
          (expandedExecutableGroupsToSpec groups) := by
  induction groups with
  | nil =>
      simp [expandedExecutableGroupsToSpec, expandedExecutableGroupToSpec,
        Execution.addExecutableGroup, GraphQL.Execution.addExecutableGroup]
  | cons head rest ih =>
      rcases group with ⟨groupName, groupFields⟩
      rcases head with ⟨responseName, fields⟩
      by_cases hname : responseName == groupName
      · simp [expandedExecutableGroupsToSpec, expandedExecutableGroupToSpec,
          Execution.addExecutableGroup, GraphQL.Execution.addExecutableGroup,
          hname, List.map_append]
      · simp [expandedExecutableGroupsToSpec, expandedExecutableGroupToSpec,
          Execution.addExecutableGroup, GraphQL.Execution.addExecutableGroup,
          hname]
        simpa [expandedExecutableGroupsToSpec, expandedExecutableGroupToSpec]
          using ih

theorem expanded_mergeExecutableGroups
    (left right : List (Name × List Execution.ExecutableField))
    : expandedExecutableGroupsToSpec (Execution.mergeExecutableGroups left right)
      = GraphQL.Execution.mergeExecutableGroups
          (expandedExecutableGroupsToSpec left)
          (expandedExecutableGroupsToSpec right) := by
  induction right generalizing left with
  | nil =>
      simp [expandedExecutableGroupsToSpec, Execution.mergeExecutableGroups,
        GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change
        expandedExecutableGroupsToSpec
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup group left) rest)
          =
        GraphQL.Execution.mergeExecutableGroups
          (GraphQL.Execution.addExecutableGroup
            (expandedExecutableGroupToSpec group)
            (expandedExecutableGroupsToSpec left))
          (expandedExecutableGroupsToSpec rest)
      rw [ih, expanded_addExecutableGroup]

mutual
  theorem expanded_collectSelection_namesNodup
      (schema : Schema) (variableValues : Execution.VariableValues)
      : ∀ (fragments : List FragmentDefinition) (visited : List Name)
          (parentType : Name) (source : Execution.ResolverValue ObjectRef)
          (selection : Selection),
          GraphQL.NormalForm.executableGroupNamesNodup
            (expandedExecutableGroupsToSpec
              (Execution.collectSelection schema variableValues fragments visited
                parentType source selection).groupedFields)
    | fragments, visited, parentType, source,
        .field responseName fieldName arguments directives selectionSet => by
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · simp [Execution.collectSelection, hallows, expandedExecutableGroupsToSpec,
            expandedExecutableGroupToSpec,
            GraphQL.NormalForm.executableGroupNamesNodup]
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            expandedExecutableGroupsToSpec,
            GraphQL.NormalForm.executableGroupNamesNodup]
    | fragments, visited, parentType, source,
        .inlineFragment none directives selectionSet => by
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · simpa [Execution.collectSelection, hallows] using
            expanded_collectFields_namesNodup schema variableValues fragments visited
              parentType source selectionSet
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            expandedExecutableGroupsToSpec,
            GraphQL.NormalForm.executableGroupNamesNodup]
    | fragments, visited, parentType, source,
        .inlineFragment (some condition) directives selectionSet => by
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · by_cases happly :
              GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                condition = true
          · simpa [Execution.collectSelection, hallows, happly] using
              expanded_collectFields_namesNodup schema variableValues fragments visited
                parentType source selectionSet
          · have happlyFalse :
                GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                  condition = false := by
                cases h : GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                    source condition
                · rfl
                · contradiction
            simp [Execution.collectSelection, hallows, happlyFalse,
              expandedExecutableGroupsToSpec,
              GraphQL.NormalForm.executableGroupNamesNodup]
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            expandedExecutableGroupsToSpec,
            GraphQL.NormalForm.executableGroupNamesNodup]
    | fragments, visited, parentType, source,
        .fragmentSpread fragmentName directives => by
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · by_cases hseen : fragmentName ∈ visited
          · simp [Execution.collectSelection, hallows, hseen,
              expandedExecutableGroupsToSpec,
              GraphQL.NormalForm.executableGroupNamesNodup]
          · cases hlookup : lookupFragmentAndRestLt? fragmentName fragments with
            | none =>
                simp [Execution.collectSelection, hallows, hseen, hlookup,
                  expandedExecutableGroupsToSpec,
                  GraphQL.NormalForm.executableGroupNamesNodup]
            | some pair =>
                rcases pair with ⟨fragment, remaining⟩
                by_cases happly :
                    GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                      fragment.typeCondition = true
                · simpa [Execution.collectSelection, hallows, hseen, hlookup,
                    happly] using
                    expanded_collectFields_namesNodup schema variableValues remaining.val
                      (fragmentName :: visited) parentType source fragment.selectionSet
                · have happlyFalse :
                      GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                        fragment.typeCondition = false := by
                      cases h : GraphQL.Execution.doesFragmentTypeApplyBool schema
                          parentType source fragment.typeCondition
                      · rfl
                      · contradiction
                  simp [Execution.collectSelection, hallows, hseen, hlookup,
                    happlyFalse, expandedExecutableGroupsToSpec,
                    GraphQL.NormalForm.executableGroupNamesNodup]
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            expandedExecutableGroupsToSpec,
            GraphQL.NormalForm.executableGroupNamesNodup]
  termination_by fragments _visited _parentType _source selection =>
    (fragments.length, sizeOf selection, 0)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem expanded_collectFields_namesNodup
      (schema : Schema) (variableValues : Execution.VariableValues)
      : ∀ (fragments : List FragmentDefinition) (visited : List Name)
          (parentType : Name) (source : Execution.ResolverValue ObjectRef)
          (selectionSet : List Selection),
          GraphQL.NormalForm.executableGroupNamesNodup
            (expandedExecutableGroupsToSpec
              (Execution.collectFields schema variableValues fragments visited parentType
                source selectionSet).groupedFields)
    | fragments, visited, parentType, source, [] => by
        simp [Execution.collectFields, expandedExecutableGroupsToSpec,
          GraphQL.NormalForm.executableGroupNamesNodup]
    | fragments, visited, parentType, source, selection :: rest => by
        simp only [Execution.collectFields, expanded_mergeExecutableGroups]
        exact GraphQL.NormalForm.mergeExecutableGroups_namesNodup _ _
          (expanded_collectSelection_namesNodup schema variableValues fragments visited
            parentType source selection)
  termination_by fragments _visited _parentType _source selectionSet =>
    (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

def canonicalFragmentGroups
    (schema : Schema) (variableValues : Execution.VariableValues)
    (original : List FragmentDefinition) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (fragmentName : Name)
    : List (Name × List GraphQL.Execution.ExecutableField) :=
  match lookupFragmentAndRestLt? fragmentName original with
  | none => []
  | some (fragment, remaining) =>
      if GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
          fragment.typeCondition then
        GraphQL.Execution.collectFields schema variableValues parentType source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
      else
        []

def fragmentGroupsAt
    (schema : Schema) (variableValues : Execution.VariableValues)
    (fragments : List FragmentDefinition) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (fragmentName : Name)
    : List (Name × List GraphQL.Execution.ExecutableField) :=
  match lookupFragmentAndRestLt? fragmentName fragments with
  | none => []
  | some (fragment, remaining) =>
      if GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
          fragment.typeCondition then
        GraphQL.Execution.collectFields schema variableValues parentType source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
      else
        []

def VisitedContained
    (schema : Schema) (variableValues : Execution.VariableValues)
    (original current : List FragmentDefinition) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (groups : List (Name × List GraphQL.Execution.ExecutableField))
    (visited : List Name)
    : Prop :=
  ∀ fragmentName,
    fragmentName ∈ visited
    -> lookupFragment? current fragmentName ≠ none
    -> GroupsContained groups
        (canonicalFragmentGroups schema variableValues original parentType source
          fragmentName)

def SpreadContext
    (original current : List FragmentDefinition)
    (selectionSet : List Selection)
    : Prop :=
  ∀ fragmentName,
    fragmentName
      ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames selectionSet
    -> ∀ {fragment : FragmentDefinition}
          {remaining
            : { remaining : List FragmentDefinition
                // remaining.length < current.length }},
        lookupFragmentAndRestLt? fragmentName current = some (fragment, remaining)
        -> ReachableAncestorRemovals original fragmentName current current
            ∧ ∃ originalRemaining
                  : { remaining : List FragmentDefinition
                      // remaining.length < original.length },
                lookupFragmentAndRestLt? fragmentName original
                = some (fragment, originalRemaining)

theorem SpreadContext.subset
    (hcontext : SpreadContext original current selectionSet)
    (hsubset
      : ∀ fragmentName,
          fragmentName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames nested
          -> fragmentName
              ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                  selectionSet)
    : SpreadContext original current nested := by
  intro fragmentName hname fragment remaining hlookup
  exact hcontext fragmentName (hsubset fragmentName hname) hlookup

theorem SpreadContext.root (fragments : List FragmentDefinition)
    (selectionSet : List Selection)
    : SpreadContext fragments fragments selectionSet := by
  intro fragmentName _hname fragment remaining hlookup
  exact ⟨ReachableAncestorRemovals.root, remaining, hlookup⟩

theorem fragmentGroupsAt_eq_canonical
    {schema : Schema} {variableValues : Execution.VariableValues}
    {original current : List FragmentDefinition} {parentType fragmentName : Name}
    {source : Execution.ResolverValue ObjectRef}
    {selectionSet : List Selection}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (hcontext : SpreadContext original current selectionSet)
    (hname
      : fragmentName
        ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames selectionSet)
    {fragment : FragmentDefinition}
    {currentRemaining
      : { remaining : List FragmentDefinition // remaining.length < current.length }}
    (hcurrent
      : lookupFragmentAndRestLt? fragmentName current = some (fragment, currentRemaining))
    : fragmentGroupsAt schema variableValues current parentType source fragmentName
      = canonicalFragmentGroups schema variableValues original parentType source
          fragmentName := by
  rcases hcontext fragmentName hname hcurrent with
    ⟨hremovals, originalRemaining, horiginal⟩
  have hlookupOriginal : lookupFragment? original fragmentName = some fragment :=
    GraphQL.NamedFragment.Validation.lookupFragment?_of_lookupFragmentAndRestLt?
      horiginal
  have hstable :=
    fragmentInlineSelectionSet_eq_of_reachable_contexts
      hunique hacyclic hall hremovals ReachableAncestorRemovals.root
      hlookupOriginal hcurrent horiginal
  simp [fragmentGroupsAt, canonicalFragmentGroups, hcurrent, horiginal]
  rw [hstable]

theorem lookupFragment?_removed_none
    {fragmentName : Name} {fragments : List FragmentDefinition}
    {fragment : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < fragments.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hlookup
      : lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining))
    : lookupFragment? remaining.val fragmentName = none := by
  induction fragments generalizing fragment with
  | nil => simp [lookupFragmentAndRestLt?] at hlookup
  | cons head rest ih =>
      simp [GraphQL.NamedFragment.Validation.fragmentNamesUnique] at hunique
      by_cases hhead : head.name == fragmentName
      · simp [lookupFragmentAndRestLt?, hhead] at hlookup
        rcases hlookup with ⟨hfragment, hremaining⟩
        subst fragment
        subst remaining
        cases hrest : lookupFragment? rest fragmentName with
        | none => rfl
        | some candidate =>
            have hcandidateMem : candidate ∈ rest :=
              GraphQL.NamedFragment.Validation.lookupFragment?_found_mem hrest
            have hcandidateName : candidate.name = fragmentName :=
              GraphQL.NamedFragment.Validation.lookupFragment?_found_name hrest
            have hheadName : head.name = fragmentName := by simpa using hhead
            exact False.elim
              (hunique.1 candidate hcandidateMem
                (by simp [hheadName, hcandidateName]))
      · simp [lookupFragmentAndRestLt?, hhead] at hlookup
        cases hrest : lookupFragmentAndRestLt? fragmentName rest with
        | none => simp [hrest] at hlookup
        | some pair =>
            rcases pair with ⟨found, tailRemaining⟩
            simp [hrest] at hlookup
            rcases hlookup with ⟨hfragment, hremaining⟩
            subst fragment
            subst remaining
            change lookupFragment? (head :: tailRemaining.val) fragmentName = none
            change
              List.find?
                  (fun candidate : FragmentDefinition =>
                    candidate.name == fragmentName)
                  (head :: tailRemaining.val)
                = none
            rw [List.find?_cons]
            simp [hhead]
            simpa [GraphQL.NamedFragment.lookupFragment?] using
              (ih hunique.2 hrest)

theorem VisitedContained.merge_left
    (hvisited
      : VisitedContained schema variableValues original current
          parentType source groups visited)
    (incoming : List (Name × List GraphQL.Execution.ExecutableField))
    : VisitedContained schema variableValues original current parentType source
        (GraphQL.Execution.mergeExecutableGroups groups incoming) visited := by
  intro fragmentName hname hlookup
  exact groupsContained_merge_left groups incoming _
    (hvisited fragmentName hname hlookup)

theorem SpreadContext.fragmentBody
    {original current : List FragmentDefinition}
    {ownerName : Name} {owner : FragmentDefinition}
    {remaining
      : { remaining : List FragmentDefinition // remaining.length < current.length }}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hremovals : ReachableAncestorRemovals original ownerName current current)
    (hlookupOriginal : lookupFragment? original ownerName = some owner)
    (hlookup : lookupFragmentAndRestLt? ownerName current = some (owner, remaining))
    : SpreadContext original remaining.val owner.selectionSet := by
  intro childName hchildName child childRemaining hchildLookup
  have hownerMemOriginal : owner ∈ original :=
    GraphQL.NamedFragment.Validation.lookupFragment?_found_mem hlookupOriginal
  have hchildRemovals :
      ReachableAncestorRemovals original childName remaining.val remaining.val :=
    hremovals.child hownerMemOriginal hlookupOriginal hlookup hchildName
  have hchildMem : child ∈ remaining.val :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_mem hchildLookup
  have hchildMemOriginal : child ∈ original :=
    hchildRemovals.mem_original hchildMem
  have hchildNameEq : child.name = childName :=
    GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_found_name hchildLookup
  have hchildLookupOriginal : lookupFragment? original childName = some child := by
    have hbyOwnName :=
      GraphQL.NamedFragment.Validation.lookupFragment?_eq_some_of_mem_unique
        hunique hchildMemOriginal
    simpa [hchildNameEq] using hbyOwnName
  rcases
      GraphQL.NamedFragment.Validation.lookupFragmentAndRestLt?_some_of_lookupFragment?
        hchildLookupOriginal with
    ⟨originalRemaining, horiginal⟩
  exact ⟨hchildRemovals, originalRemaining, horiginal⟩

theorem collectFields_firstOccurrences_aux
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    (variableValues : Execution.VariableValues)
    {original : List FragmentDefinition}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    : ∀ (current : List FragmentDefinition) (visited : List Name)
        (validationParentType parentType : Name)
        (source : Execution.ResolverValue ObjectRef)
        (selectionSet : List Selection)
        (leftPrefix rightPrefix : List (Name × List GraphQL.Execution.ExecutableField)),
        GraphQL.NamedFragment.Validation.fragmentNamesUnique current
        -> GraphQL.NamedFragment.Validation.selectionSetValid schema
            variableDefinitions current validationParentType selectionSet
        -> SpreadContext original current selectionSet
        -> GroupFirstOccurrences leftPrefix rightPrefix
        -> GraphQL.NormalForm.executableGroupNamesNodup leftPrefix
        -> VisitedContained schema variableValues original current parentType source
            leftPrefix visited
        ->  let collected :=
              Execution.collectFields schema variableValues current visited parentType
                source selectionSet
            GroupFirstOccurrences
              (GraphQL.Execution.mergeExecutableGroups leftPrefix
                (expandedExecutableGroupsToSpec collected.groupedFields))
              (GraphQL.Execution.mergeExecutableGroups rightPrefix
                (GraphQL.Execution.collectFields schema variableValues parentType source
                  (Translate.reduceSelectionSet
                    (Inline.inlineSelectionSet current selectionSet))))
            ∧ VisitedContained schema variableValues original current parentType source
                (GraphQL.Execution.mergeExecutableGroups leftPrefix
                  (expandedExecutableGroupsToSpec collected.groupedFields))
                collected.visitedFragments
  | current, visited, validationParentType, parentType, source, [], leftPrefix,
      rightPrefix,
      _hcurrentUnique, _hvalid, _hcontext, hprefixes, _hleftNodup,
      hvisited => by
      simp [Execution.collectFields, GraphQL.Execution.collectFields,
        Translate.reduceSelectionSet, expandedExecutableGroupsToSpec]
      exact ⟨hprefixes, hvisited⟩
  | current, visited, validationParentType, parentType, source,
      selection :: rest,
      leftPrefix, rightPrefix, hcurrentUnique, hvalid, hcontext,
      hprefixes, hleftNodup, hvisited => by
      have hvalidPair := hvalid
      simp [GraphQL.NamedFragment.Validation.selectionSetValid]
        at hvalidPair
      have hselectionContext :
          SpreadContext original current [selection] :=
        hcontext.subset (by
          intro fragmentName hname
          simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames]
            at hname ⊢
          exact Or.inl hname)
      let selected :=
        Execution.collectSelection schema variableValues current visited parentType
          source selection
      let staticSelected :=
        GraphQL.Execution.collectSelection schema variableValues parentType source
          (selectionToSpecAfterInline current selection)
      have hselected :
          GroupFirstOccurrences
              (GraphQL.Execution.mergeExecutableGroups leftPrefix
                (expandedExecutableGroupsToSpec selected.groupedFields))
              (GraphQL.Execution.mergeExecutableGroups rightPrefix staticSelected)
          ∧ VisitedContained schema variableValues original current parentType source
              (GraphQL.Execution.mergeExecutableGroups leftPrefix
                (expandedExecutableGroupsToSpec selected.groupedFields))
              selected.visitedFragments := by
        cases selection with
        | field responseName fieldName arguments directives nested =>
            by_cases hallows :
                GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives = true
            · simp [selected, staticSelected, Execution.collectSelection,
                GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                inlinedSelectionToSpec, Inline.inlineSelection,
                expandedExecutableGroupsToSpec, expandedExecutableGroupToSpec,
                expandedExecutableFieldToSpec, hallows]
              constructor
              · exact hprefixes.mergeSame
                  [(responseName,
                    [{
                      parentType := parentType
                      responseName := responseName
                      fieldName := fieldName
                      arguments := arguments
                      selectionSet := Translate.reduceSelectionSet
                        (Inline.inlineSelectionSet current nested)
                    }])]
              · exact hvisited.merge_left _
            · have hallowsFalse :
                  GraphQL.Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                  cases h : GraphQL.Execution.selectionDirectivesAllowBool
                      variableValues directives
                  · rfl
                  · contradiction
              simp [selected, staticSelected, Execution.collectSelection,
                GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                inlinedSelectionToSpec, Inline.inlineSelection,
                expandedExecutableGroupsToSpec, hallowsFalse,
                GraphQL.Execution.mergeExecutableGroups]
              exact ⟨hprefixes, hvisited⟩
        | inlineFragment typeCondition directives nested =>
            by_cases hallows :
                GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives = true
            · cases typeCondition with
              | none =>
                  have hnestedValid := hvalidPair.1
                  simp [GraphQL.NamedFragment.Validation.selectionValid]
                    at hnestedValid
                  have hnestedContext : SpreadContext original current nested :=
                    hselectionContext.subset (by
                      intro fragmentName hname
                      simpa [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                        GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                        using hname)
                  simpa [selected, staticSelected, Execution.collectSelection,
                    GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                    inlinedSelectionToSpec, Inline.inlineSelection, hallows] using
                    collectFields_firstOccurrences_aux variableValues hunique hacyclic
                      hall current visited validationParentType parentType source nested
                      leftPrefix rightPrefix hcurrentUnique
                      hnestedValid.2.2
                      hnestedContext hprefixes hleftNodup hvisited
              | some condition =>
                  have hnestedValid := hvalidPair.1
                  simp [GraphQL.NamedFragment.Validation.selectionValid]
                    at hnestedValid
                  by_cases happly :
                      GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                        source condition = true
                  · have hnestedContext : SpreadContext original current nested :=
                      hselectionContext.subset (by
                        intro fragmentName hname
                        simpa [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                          GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                          using hname)
                    simpa [selected, staticSelected, Execution.collectSelection,
                      GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                      inlinedSelectionToSpec, Inline.inlineSelection, hallows,
                      happly] using
                      collectFields_firstOccurrences_aux variableValues hunique hacyclic
                        hall current visited condition parentType source nested leftPrefix
                        rightPrefix hcurrentUnique
                        hnestedValid.2.2.2.2 hnestedContext hprefixes hleftNodup
                        hvisited
                  · have happlyFalse :
                        GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                          source condition = false := by
                        cases h : GraphQL.Execution.doesFragmentTypeApplyBool schema
                            parentType source condition
                        · rfl
                        · contradiction
                    simp [selected, staticSelected, Execution.collectSelection,
                      GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                      inlinedSelectionToSpec, Inline.inlineSelection, hallows,
                      happlyFalse, expandedExecutableGroupsToSpec,
                      GraphQL.Execution.mergeExecutableGroups]
                    exact ⟨hprefixes, hvisited⟩
            · have hallowsFalse :
                  GraphQL.Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                  cases h : GraphQL.Execution.selectionDirectivesAllowBool
                      variableValues directives
                  · rfl
                  · contradiction
              cases typeCondition with
              | none =>
                  simp [selected, staticSelected, Execution.collectSelection,
                    GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                    inlinedSelectionToSpec, Inline.inlineSelection, hallowsFalse,
                    expandedExecutableGroupsToSpec,
                    GraphQL.Execution.mergeExecutableGroups]
                  exact ⟨hprefixes, hvisited⟩
              | some condition =>
                  simp [selected, staticSelected, Execution.collectSelection,
                    GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                    inlinedSelectionToSpec, Inline.inlineSelection, hallowsFalse,
                    expandedExecutableGroupsToSpec,
                    GraphQL.Execution.mergeExecutableGroups]
                  exact ⟨hprefixes, hvisited⟩
        | fragmentSpread fragmentName directives =>
            have hspreadName :
                fragmentName ∈
                  GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                    [Selection.fragmentSpread fragmentName directives] := by
              simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
            rcases
                GraphQL.NamedFragment.Validation.selectionValid_fragmentSpread_lookupFragmentAndRestLt?
                  hvalidPair.1 with
              ⟨_hdirectivesValid, fragment, remaining, hlookup,
                _hcomposite, _hoverlap⟩
            rcases hselectionContext fragmentName hspreadName hlookup with
              ⟨hremovals, originalRemaining, hlookupOriginal⟩
            have hlookupOriginalFind :
                lookupFragment? original fragmentName = some fragment :=
              GraphQL.NamedFragment.Validation.lookupFragment?_of_lookupFragmentAndRestLt?
                hlookupOriginal
            have hcurrentGroupsCanonical :
                fragmentGroupsAt schema variableValues current parentType source
                    fragmentName
                  = canonicalFragmentGroups schema variableValues original parentType
                      source fragmentName :=
              fragmentGroupsAt_eq_canonical hunique hacyclic hall hselectionContext
                hspreadName hlookup
            by_cases hallows :
                GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives = true
            · by_cases hseen : fragmentName ∈ visited
              · by_cases happly :
                    GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                      source fragment.typeCondition = true
                · have hlookupCurrent : lookupFragment? current fragmentName ≠ none := by
                      rw [GraphQL.NamedFragment.Validation.lookupFragment?_of_lookupFragmentAndRestLt?
                        hlookup]
                      simp
                  have hcontained := hvisited fragmentName hseen hlookupCurrent
                  have hrightNodup := hprefixes.right_namesNodup hleftNodup
                  have hcurrentGroups :
                      fragmentGroupsAt schema variableValues current parentType source
                          fragmentName
                        = GraphQL.Execution.collectFields schema variableValues
                            parentType source
                            (Translate.reduceSelectionSet
                              (Inline.inlineSelectionSet remaining.val
                                fragment.selectionSet)) := by
                    simp [fragmentGroupsAt, hlookup, happly]
                  have hcanonical :
                      canonicalFragmentGroups schema variableValues original parentType
                          source fragmentName
                        = GraphQL.Execution.collectFields schema variableValues
                            parentType source
                            (Translate.reduceSelectionSet
                              (Inline.inlineSelectionSet remaining.val
                                fragment.selectionSet)) := by
                    rw [← hcurrentGroupsCanonical, hcurrentGroups]
                  constructor
                  · simpa [selected, staticSelected, Execution.collectSelection,
                      GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                      inlinedSelectionToSpec, Inline.inlineSelection, hallows,
                      hseen, hlookup, happly, expandedExecutableGroupsToSpec,
                      GraphQL.Execution.mergeExecutableGroups, hcanonical] using
                      hprefixes.mergeDuplicatesRight
                        (canonicalFragmentGroups schema variableValues original
                          parentType source fragmentName)
                        hleftNodup hcontained
                  · simpa [selected, Execution.collectSelection, hallows, hseen,
                      expandedExecutableGroupsToSpec,
                      GraphQL.Execution.mergeExecutableGroups] using hvisited
                · have happlyFalse :
                      GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                        source fragment.typeCondition = false := by
                      cases h : GraphQL.Execution.doesFragmentTypeApplyBool schema
                          parentType source fragment.typeCondition
                      · rfl
                      · contradiction
                  simp [selected, staticSelected, Execution.collectSelection,
                    GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                    inlinedSelectionToSpec, Inline.inlineSelection, hallows, hseen,
                    hlookup, happlyFalse, expandedExecutableGroupsToSpec,
                    GraphQL.Execution.mergeExecutableGroups]
                  exact ⟨hprefixes, hvisited⟩
              · by_cases happly :
                    GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                      source fragment.typeCondition = true
                · have hremainingUnique :=
                      GraphQL.NamedFragment.Validation.fragmentNamesUnique_of_lookupFragmentAndRestLt?_remaining
                        hcurrentUnique hlookup
                  have hbodyValid :=
                    fragmentSelectionSetValid_after_reachable_lookup_removal
                      hunique hacyclic hall hremovals hlookupOriginalFind hlookup
                  have hbodyContext :
                      SpreadContext original remaining.val fragment.selectionSet :=
                    SpreadContext.fragmentBody hunique hremovals hlookupOriginalFind
                      hlookup
                  have hstartVisited :
                      VisitedContained schema variableValues original remaining.val
                        parentType source leftPrefix (fragmentName :: visited) := by
                    intro candidate hcandidate hcandidateLookup
                    simp only [List.mem_cons] at hcandidate
                    cases hcandidate with
                    | inl hcandidate =>
                        subst candidate
                        exact False.elim
                          (hcandidateLookup
                            (lookupFragment?_removed_none hcurrentUnique hlookup))
                    | inr hcandidate =>
                        cases hremainingLookup : lookupFragment? remaining.val candidate with
                        | none => contradiction
                        | some candidateFragment =>
                            have hcurrentLookup :
                                lookupFragment? current candidate = some candidateFragment :=
                              GraphQL.NamedFragment.Validation.lookupFragment?_remaining_to_original
                                hcurrentUnique hlookup hremainingLookup
                            exact hvisited candidate hcandidate (by simp [hcurrentLookup])
                  have hbody :=
                    collectFields_firstOccurrences_aux variableValues hunique hacyclic
                      hall remaining.val (fragmentName :: visited)
                      fragment.typeCondition parentType source fragment.selectionSet
                      leftPrefix rightPrefix hremainingUnique hbodyValid hbodyContext
                      hprefixes hleftNodup hstartVisited
                  let bodyCollected :=
                    Execution.collectFields schema variableValues remaining.val
                      (fragmentName :: visited) parentType source fragment.selectionSet
                  let bodyStatic :=
                    GraphQL.Execution.collectFields schema variableValues parentType
                      source
                      (Translate.reduceSelectionSet
                        (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
                  have hbodyRelation :
                      GroupFirstOccurrences
                        (GraphQL.Execution.mergeExecutableGroups leftPrefix
                          (expandedExecutableGroupsToSpec bodyCollected.groupedFields))
                        (GraphQL.Execution.mergeExecutableGroups rightPrefix bodyStatic) :=
                    hbody.1
                  have hbodyInvariant := hbody.2
                  have hbodyRightContains :
                      GroupsContained
                        (GraphQL.Execution.mergeExecutableGroups rightPrefix bodyStatic)
                        bodyStatic :=
                    groupsContained_merge_right rightPrefix bodyStatic
                  have hbodyLeftContains :
                      GroupsContained
                        (GraphQL.Execution.mergeExecutableGroups leftPrefix
                          (expandedExecutableGroupsToSpec bodyCollected.groupedFields))
                        bodyStatic :=
                    groupsContained_trans hbodyRelation.rightContainedInLeft
                      hbodyRightContains
                  have hcanonicalBody :
                      canonicalFragmentGroups schema variableValues original parentType
                          source fragmentName = bodyStatic := by
                    rw [← hcurrentGroupsCanonical]
                    simp [fragmentGroupsAt, hlookup, happly, bodyStatic]
                  have hreturnedInvariant :
                      VisitedContained schema variableValues original current parentType
                        source
                        (GraphQL.Execution.mergeExecutableGroups leftPrefix
                          (expandedExecutableGroupsToSpec bodyCollected.groupedFields))
                        bodyCollected.visitedFragments := by
                    intro candidate hcandidate hcandidateCurrent
                    by_cases hcand : candidate = fragmentName
                    · subst candidate
                      rw [hcanonicalBody]
                      exact hbodyLeftContains
                    · have hcandidateFind : lookupFragment? current candidate ≠ none :=
                        hcandidateCurrent
                      cases hcurrentCandidate : lookupFragment? current candidate with
                      | none => contradiction
                      | some candidateFragment =>
                          have hremainingCandidate :
                              lookupFragment? remaining.val candidate
                                = some candidateFragment :=
                            GraphQL.NamedFragment.Validation.lookupFragment?_remaining_of_ne
                              hlookup hcurrentCandidate (Ne.symm hcand)
                          exact hbodyInvariant candidate hcandidate
                            (by simp [hremainingCandidate])
                  simpa [selected, staticSelected, Execution.collectSelection,
                    GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                    inlinedSelectionToSpec, Inline.inlineSelection, hallows, hseen,
                    hlookup, happly, bodyCollected, bodyStatic] using
                    And.intro hbodyRelation hreturnedInvariant
                · have happlyFalse :
                      GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                        source fragment.typeCondition = false := by
                      cases h : GraphQL.Execution.doesFragmentTypeApplyBool schema
                          parentType source fragment.typeCondition
                      · rfl
                      · contradiction
                  have hnewVisited :
                      VisitedContained schema variableValues original current parentType
                        source leftPrefix (fragmentName :: visited) := by
                    intro candidate hcandidate hlookupCandidate
                    simp only [List.mem_cons] at hcandidate
                    cases hcandidate with
                    | inl hcandidate =>
                        subst candidate
                        have hcanonicalEmpty :
                            canonicalFragmentGroups schema variableValues original
                              parentType source fragmentName = [] := by
                          rw [← hcurrentGroupsCanonical]
                          simp [fragmentGroupsAt, hlookup, happlyFalse]
                        intro group hgroup
                        simp [hcanonicalEmpty] at hgroup
                    | inr hcandidate =>
                        exact hvisited candidate hcandidate hlookupCandidate
                  simp [selected, staticSelected, Execution.collectSelection,
                    GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                    inlinedSelectionToSpec, Inline.inlineSelection, hallows, hseen,
                    hlookup, happlyFalse, expandedExecutableGroupsToSpec,
                    GraphQL.Execution.mergeExecutableGroups]
                  exact ⟨hprefixes, hnewVisited⟩
            · have hallowsFalse :
                  GraphQL.Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                  cases h : GraphQL.Execution.selectionDirectivesAllowBool
                      variableValues directives
                  · rfl
                  · contradiction
              simp [selected, staticSelected, Execution.collectSelection,
                GraphQL.Execution.collectSelection, selectionToSpecAfterInline,
                inlinedSelectionToSpec, Inline.inlineSelection, hallowsFalse,
                hlookup,
                expandedExecutableGroupsToSpec,
                GraphQL.Execution.mergeExecutableGroups]
              exact ⟨hprefixes, hvisited⟩
      have hselectedLeftNodup :
          GraphQL.NormalForm.executableGroupNamesNodup
            (GraphQL.Execution.mergeExecutableGroups leftPrefix
              (expandedExecutableGroupsToSpec selected.groupedFields)) := by
        have hrightPrefixNodup := hprefixes.right_namesNodup hleftNodup
        have hstaticNodup :=
          GraphQL.NormalForm.collectSelection_namesNodup schema variableValues
            parentType source (selectionToSpecAfterInline current selection)
        exact hselected.1.left_namesNodup
          (GraphQL.NormalForm.mergeExecutableGroups_namesNodup _ _
            hrightPrefixNodup)
      have hrestContext : SpreadContext original current rest :=
        hcontext.subset (by
          intro fragmentName hname
          simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
            hname])
      have hrest :=
        collectFields_firstOccurrences_aux variableValues hunique hacyclic hall current
          selected.visitedFragments validationParentType parentType source rest
          (GraphQL.Execution.mergeExecutableGroups leftPrefix
            (expandedExecutableGroupsToSpec selected.groupedFields))
          (GraphQL.Execution.mergeExecutableGroups rightPrefix staticSelected)
          hcurrentUnique
          (by
            simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
              hvalidPair.2)
          hrestContext hselected.1 hselectedLeftNodup hselected.2
      let remaining :=
        Execution.collectFields schema variableValues current
          selected.visitedFragments parentType source rest
      let staticRemaining :=
        GraphQL.Execution.collectFields schema variableValues parentType source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet current rest))
      have hselectedNodup :=
        expanded_collectSelection_namesNodup schema variableValues current visited
          parentType source selection
      have hremainingNodup :=
        expanded_collectFields_namesNodup schema variableValues current
          selected.visitedFragments parentType source rest
      have hstaticSelectedNodup :=
        GraphQL.NormalForm.collectSelection_namesNodup schema variableValues
          parentType source (selectionToSpecAfterInline current selection)
      have hstaticRemainingNodup :=
        GraphQL.NormalForm.collectFields_namesNodup schema variableValues parentType
          source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet current rest))
      constructor
      · have hrelation := hrest.1
        rw [GraphQL.NormalForm.mergeExecutableGroups_assoc_of_namesNodup
          leftPrefix (expandedExecutableGroupsToSpec selected.groupedFields)
          (expandedExecutableGroupsToSpec remaining.groupedFields)
          hselectedNodup hremainingNodup] at hrelation
        rw [GraphQL.NormalForm.mergeExecutableGroups_assoc_of_namesNodup
          rightPrefix staticSelected staticRemaining hstaticSelectedNodup
          hstaticRemainingNodup] at hrelation
        simpa [Execution.collectFields, selected, remaining,
          expanded_mergeExecutableGroups, reduce_inlineSelectionSet,
          GraphQL.Execution.collectFields, staticSelected, staticRemaining] using
          hrelation
      · have hinvariant := hrest.2
        rw [GraphQL.NormalForm.mergeExecutableGroups_assoc_of_namesNodup
          leftPrefix (expandedExecutableGroupsToSpec selected.groupedFields)
          (expandedExecutableGroupsToSpec remaining.groupedFields)
          hselectedNodup hremainingNodup] at hinvariant
        simpa [Execution.collectFields, selected, remaining,
          expanded_mergeExecutableGroups] using hinvariant
termination_by current _visited _validationParentType _parentType _source
    selectionSet _leftPrefix _rightPrefix _hcurrentUnique _hvalid _hcontext
    _hprefixes _hleftNodup _hvisited =>
  (current.length, sizeOf selectionSet)
decreasing_by
  all_goals
    simp_all
    repeat first
      | apply Prod.Lex.left; omega
      | apply Prod.Lex.right
    try omega

theorem collectFields_firstOccurrences
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    (variableValues : Execution.VariableValues)
    {fragments : List FragmentDefinition}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (hvalid
      : GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions fragments parentType selectionSet)
    : let collected :=
        Execution.collectFields schema variableValues fragments [] parentType source
          selectionSet
      GroupFirstOccurrences
        (expandedExecutableGroupsToSpec collected.groupedFields)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet fragments selectionSet))) := by
  have hresult :=
    collectFields_firstOccurrences_aux variableValues hunique hacyclic hall fragments []
      parentType parentType source selectionSet [] [] hunique hvalid
      (SpreadContext.root fragments selectionSet) .nil
      (by simp [GraphQL.NormalForm.executableGroupNamesNodup])
      (by
        intro fragmentName hname _hlookup
        simp at hname)
  let collected :=
    Execution.collectFields schema variableValues fragments [] parentType source
      selectionSet
  have hleftNodup :=
    expanded_collectFields_namesNodup schema variableValues fragments [] parentType
      source selectionSet
  have hrightNodup :=
    GraphQL.NormalForm.collectFields_namesNodup schema variableValues parentType source
      (Translate.reduceSelectionSet
        (Inline.inlineSelectionSet fragments selectionSet))
  simpa [collected,
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup _ hleftNodup,
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup _ hrightNodup]
    using hresult.1

def ExecutableFieldValidContext
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (original : List FragmentDefinition) (field : Execution.ExecutableField)
    : Prop :=
  GraphQL.NamedFragment.Validation.fragmentNamesUnique field.availableFragments
  ∧ SpreadContext original field.availableFragments field.selectionSet
  ∧ ∃ validationParentType,
      GraphQL.NamedFragment.Validation.selectionSetValid schema variableDefinitions
        field.availableFragments validationParentType field.selectionSet

def ExecutableFieldsValidContext
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (original : List FragmentDefinition)
    (fields : List Execution.ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields
    -> ExecutableFieldValidContext schema variableDefinitions original field

def ExecutableGroupsValidContext
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (original : List FragmentDefinition)
    (groups : List (Name × List Execution.ExecutableField))
    : Prop :=
  ∀ group,
    group ∈ groups
    -> ExecutableFieldsValidContext schema variableDefinitions original group.snd

theorem ExecutableGroupsValidContext.add
    (hgroup : ExecutableFieldsValidContext schema variableDefinitions original group.snd)
    (hgroups : ExecutableGroupsValidContext schema variableDefinitions original groups)
    : ExecutableGroupsValidContext schema variableDefinitions original
        (Execution.addExecutableGroup group groups) := by
  induction groups with
  | nil =>
      intro candidate hcandidate
      simp [Execution.addExecutableGroup] at hcandidate
      subst candidate
      exact hgroup
  | cons head rest ih =>
      rcases group with ⟨groupName, groupFields⟩
      rcases head with ⟨responseName, fields⟩
      have hfields := hgroups (responseName, fields) (by simp)
      have hrest : ExecutableGroupsValidContext schema variableDefinitions original
          rest := by
        intro candidate hcandidate
        exact hgroups candidate (by simp [hcandidate])
      by_cases hname : responseName == groupName
      · intro candidate hcandidate
        simp [Execution.addExecutableGroup, hname] at hcandidate
        cases hcandidate with
        | inl hcandidate =>
            subst candidate
            intro field hfield
            simp only [List.mem_append] at hfield
            exact hfield.elim (hfields field) (hgroup field)
        | inr hcandidate => exact hrest candidate hcandidate
      · intro candidate hcandidate
        simp [Execution.addExecutableGroup, hname] at hcandidate
        cases hcandidate with
        | inl hcandidate =>
            subst candidate
            exact hfields
        | inr hcandidate => exact ih hrest candidate hcandidate

theorem ExecutableGroupsValidContext.merge
    (hleft : ExecutableGroupsValidContext schema variableDefinitions original left)
    (hright : ExecutableGroupsValidContext schema variableDefinitions original right)
    : ExecutableGroupsValidContext schema variableDefinitions original
        (Execution.mergeExecutableGroups left right) := by
  induction right generalizing left with
  | nil => simpa [Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      simp only [Execution.mergeExecutableGroups, List.foldl_cons]
      apply ih
      · exact hleft.add (hright group (by simp))
      · intro candidate hcandidate
        exact hright candidate (by simp [hcandidate])

mutual
  theorem collectSelection_validContext
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {original : List FragmentDefinition}
      (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
      (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
      (hall
        : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
            variableDefinitions original)
      (variableValues : Execution.VariableValues)
      : ∀ (current : List FragmentDefinition) (visited : List Name)
          (validationParentType parentType : Name)
          (source : Execution.ResolverValue ObjectRef) (selection : Selection),
          GraphQL.NamedFragment.Validation.fragmentNamesUnique current
          -> GraphQL.NamedFragment.Validation.selectionValid schema variableDefinitions
              current validationParentType selection
          -> SpreadContext original current [selection]
          -> ExecutableGroupsValidContext schema variableDefinitions original
              (Execution.collectSelection schema variableValues current visited parentType
                source selection).groupedFields
    | current, visited, validationParentType, parentType, source,
        .field responseName fieldName arguments directives selectionSet,
        hcurrentUnique, hvalid, hcontext => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨_hdirectives, fieldDefinition, hlookup, _harguments, hfieldValid⟩
        have hselectionSetValid :
            ∃ validationParentType,
              GraphQL.NamedFragment.Validation.selectionSetValid schema
                variableDefinitions current validationParentType selectionSet := by
          simp [GraphQL.NamedFragment.Validation.fieldSelectionSetValid] at hfieldValid
          rcases hfieldValid with ⟨_houtput, hshape⟩
          cases hshape with
          | inl hleaf =>
              exact ⟨fieldDefinition.outputType.namedType, by
                rw [hleaf.2]
                simp [GraphQL.NamedFragment.Validation.selectionSetValid]⟩
          | inr hcomposite =>
              exact ⟨fieldDefinition.outputType.namedType, hcomposite.2.2⟩
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · simp [Execution.collectSelection, hallows,
            ExecutableGroupsValidContext, ExecutableFieldsValidContext,
            ExecutableFieldValidContext]
          exact ⟨hcurrentUnique,
            hcontext.subset (by
              intro fragmentName hname
              simpa [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                using hname),
            hselectionSetValid⟩
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            ExecutableGroupsValidContext]
    | current, visited, validationParentType, parentType, source,
        .inlineFragment none directives selectionSet,
        hcurrentUnique, hvalid, hcontext => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · simpa [Execution.collectSelection, hallows] using
            collectFields_validContext hunique hacyclic hall variableValues current
              visited validationParentType parentType source selectionSet
              hcurrentUnique hvalid.2.2
              (hcontext.subset (by
                intro fragmentName hname
                simpa [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                  GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                  using hname))
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            ExecutableGroupsValidContext]
    | current, visited, validationParentType, parentType, source,
        .inlineFragment (some condition) directives selectionSet,
        hcurrentUnique, hvalid, hcontext => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · by_cases happly :
              GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                condition = true
          · simpa [Execution.collectSelection, hallows, happly] using
              collectFields_validContext hunique hacyclic hall variableValues current
                visited condition parentType source selectionSet hcurrentUnique
                hvalid.2.2.2.2
                (hcontext.subset (by
                  intro fragmentName hname
                  simpa [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                    GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                    using hname))
          · have happlyFalse :
                GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                  condition = false := by
                cases h : GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                    source condition
                · rfl
                · contradiction
            simp [Execution.collectSelection, hallows, happlyFalse,
              ExecutableGroupsValidContext]
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            ExecutableGroupsValidContext]
    | current, visited, validationParentType, parentType, source,
        .fragmentSpread fragmentName directives,
        hcurrentUnique, hvalid, hcontext => by
        rcases
            GraphQL.NamedFragment.Validation.selectionValid_fragmentSpread_lookupFragmentAndRestLt?
              hvalid with
          ⟨_hdirectives, fragment, remaining, hlookup, _hcomposite, _hoverlap⟩
        have hspreadName :
            fragmentName ∈
              GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                [Selection.fragmentSpread fragmentName directives] := by
          simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
            GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
        rcases hcontext fragmentName hspreadName hlookup with
          ⟨hremovals, originalRemaining, hlookupOriginal⟩
        have hlookupOriginalFind : lookupFragment? original fragmentName = some fragment :=
          GraphQL.NamedFragment.Validation.lookupFragment?_of_lookupFragmentAndRestLt?
            hlookupOriginal
        by_cases hallows :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
              = true
        · by_cases hseen : fragmentName ∈ visited
          · simp [Execution.collectSelection, hallows, hseen,
              ExecutableGroupsValidContext]
          · by_cases happly :
                GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                  fragment.typeCondition = true
            · have hremainingUnique :=
                  GraphQL.NamedFragment.Validation.fragmentNamesUnique_of_lookupFragmentAndRestLt?_remaining
                    hcurrentUnique hlookup
              have hbodyValid :=
                fragmentSelectionSetValid_after_reachable_lookup_removal
                  hunique hacyclic hall hremovals hlookupOriginalFind hlookup
              have hbodyContext :=
                SpreadContext.fragmentBody hunique hremovals hlookupOriginalFind hlookup
              simpa [Execution.collectSelection, hallows, hseen, hlookup, happly] using
                collectFields_validContext hunique hacyclic hall variableValues
                  remaining.val (fragmentName :: visited) fragment.typeCondition
                  parentType source fragment.selectionSet hremainingUnique hbodyValid
                  hbodyContext
            · have happlyFalse :
                  GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                    fragment.typeCondition = false := by
                  cases h : GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                      source fragment.typeCondition
                  · rfl
                  · contradiction
              simp [Execution.collectSelection, hallows, hseen, hlookup, happlyFalse,
                ExecutableGroupsValidContext]
        · have hallowsFalse :
              GraphQL.Execution.selectionDirectivesAllowBool variableValues directives
                = false := by
              cases h : GraphQL.Execution.selectionDirectivesAllowBool variableValues
                  directives
              · rfl
              · contradiction
          simp [Execution.collectSelection, hallowsFalse,
            ExecutableGroupsValidContext]
  termination_by current _visited _validationParentType _parentType _source selection
      _hcurrentUnique _hvalid _hcontext =>
    (current.length, sizeOf selection, 0)
  decreasing_by
    all_goals
      simp_all
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem collectFields_validContext
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {original : List FragmentDefinition}
      (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
      (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
      (hall
        : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
            variableDefinitions original)
      (variableValues : Execution.VariableValues)
      : ∀ (current : List FragmentDefinition) (visited : List Name)
          (validationParentType parentType : Name)
          (source : Execution.ResolverValue ObjectRef) (selectionSet : List Selection),
          GraphQL.NamedFragment.Validation.fragmentNamesUnique current
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema variableDefinitions
              current validationParentType selectionSet
          -> SpreadContext original current selectionSet
          -> ExecutableGroupsValidContext schema variableDefinitions original
              (Execution.collectFields schema variableValues current visited parentType
                source selectionSet).groupedFields
    | current, visited, validationParentType, parentType, source, [],
        _hcurrentUnique, _hvalid, _hcontext => by
        simp [Execution.collectFields, ExecutableGroupsValidContext]
    | current, visited, validationParentType, parentType, source,
        selection :: rest, hcurrentUnique, hvalid, hcontext => by
        have hvalidPair := hvalid
        simp [GraphQL.NamedFragment.Validation.selectionSetValid] at hvalidPair
        simp only [Execution.collectFields]
        apply ExecutableGroupsValidContext.merge
        · exact collectSelection_validContext hunique hacyclic hall variableValues
            current visited validationParentType parentType source selection
            hcurrentUnique hvalidPair.1
            (hcontext.subset (by
              intro fragmentName hname
              simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames]
                at hname ⊢
              exact Or.inl hname))
        · exact collectFields_validContext hunique hacyclic hall variableValues current
            (Execution.collectSelection schema variableValues current visited parentType
              source selection).visitedFragments
            validationParentType parentType source rest hcurrentUnique
            (by
              simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
                hvalidPair.2)
            (hcontext.subset (by
              intro fragmentName hname
              simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                hname]))
  termination_by current _visited _validationParentType _parentType _source selectionSet
      _hcurrentUnique _hvalid _hcontext =>
    (current.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_all
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

theorem ExecutableFieldValidContext.selectionSetValid
    (hfield : ExecutableFieldValidContext schema variableDefinitions original field)
    : ∃ validationParentType,
        GraphQL.NamedFragment.Validation.selectionSetValid schema variableDefinitions
          field.availableFragments validationParentType field.selectionSet := by
  exact hfield.2.2

theorem collectFields_firstOccurrences_withRuntimeParent
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    (variableValues : Execution.VariableValues)
    {original current : List FragmentDefinition}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (hcurrentUnique : GraphQL.NamedFragment.Validation.fragmentNamesUnique current)
    (validationParentType parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (hvalid
      : GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions current validationParentType selectionSet)
    (hcontext : SpreadContext original current selectionSet)
    : let collected :=
        Execution.collectFields schema variableValues current [] parentType source
          selectionSet
      GroupFirstOccurrences
        (expandedExecutableGroupsToSpec collected.groupedFields)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet current selectionSet))) := by
  have hresult :=
    collectFields_firstOccurrences_aux variableValues hunique hacyclic hall current []
      validationParentType parentType source selectionSet [] [] hcurrentUnique hvalid
      hcontext .nil
      (by simp [GraphQL.NormalForm.executableGroupNamesNodup])
      (by
        intro fragmentName hname _hlookup
        simp at hname)
  let collected :=
    Execution.collectFields schema variableValues current [] parentType source
      selectionSet
  have hleftNodup :=
    expanded_collectFields_namesNodup schema variableValues current [] parentType
      source selectionSet
  have hrightNodup :=
    GraphQL.NormalForm.collectFields_namesNodup schema variableValues parentType source
      (Translate.reduceSelectionSet
        (Inline.inlineSelectionSet current selectionSet))
  simpa [collected,
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup _ hleftNodup,
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup _ hrightNodup]
    using hresult.1

theorem collectSubfields_firstOccurrences
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    (variableValues : Execution.VariableValues)
    {original : List FragmentDefinition}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    : ∀ fields,
        ExecutableFieldsValidContext schema variableDefinitions original fields
        -> GroupFirstOccurrences
            (expandedExecutableGroupsToSpec
              (Execution.collectSubfields schema variableValues objectType objectValue
                fields))
            (GraphQL.Execution.collectSubfields schema variableValues objectType
              objectValue (fields.map expandedExecutableFieldToSpec))
  | [], _hfields => by
      exact .nil
  | field :: rest, hfields => by
      have hfield := hfields field (by simp)
      have hrest :
          ExecutableFieldsValidContext schema variableDefinitions original rest := by
        intro candidate hcandidate
        exact hfields candidate (by simp [hcandidate])
      rcases hfield with
        ⟨hcurrentUnique, hcontext, validationParentType, hvalid⟩
      have hhead :=
        collectFields_firstOccurrences_withRuntimeParent variableValues hunique hacyclic
          hall hcurrentUnique validationParentType objectType objectValue
          field.selectionSet hvalid hcontext
      have htail :=
        collectSubfields_firstOccurrences variableValues hunique hacyclic hall objectType
          objectValue rest hrest
      simpa only [Execution.collectSubfields, GraphQL.Execution.collectSubfields,
        expanded_mergeExecutableGroups, expandedExecutableFieldToSpec,
        List.map_cons] using htail.mergeRelated hhead

theorem collectSubfields_validContext
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {original : List FragmentDefinition}
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique original)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic original)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions original)
    (variableValues : Execution.VariableValues)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    : ∀ fields,
        ExecutableFieldsValidContext schema variableDefinitions original fields
        -> ExecutableGroupsValidContext schema variableDefinitions original
            (Execution.collectSubfields schema variableValues objectType objectValue
              fields)
  | [], _hfields => by
      simp [Execution.collectSubfields, ExecutableGroupsValidContext]
  | field :: rest, hfields => by
      have hfield := hfields field (by simp)
      have hrest :
          ExecutableFieldsValidContext schema variableDefinitions original rest := by
        intro candidate hcandidate
        exact hfields candidate (by simp [hcandidate])
      rcases hfield with
        ⟨hcurrentUnique, hcontext, validationParentType, hvalid⟩
      simp only [Execution.collectSubfields]
      apply ExecutableGroupsValidContext.merge
      · exact collectFields_validContext hunique hacyclic hall variableValues
          field.availableFragments [] validationParentType objectType objectValue
          field.selectionSet hcurrentUnique hvalid hcontext
      · exact collectSubfields_validContext hunique hacyclic hall variableValues
          objectType objectValue rest hrest

end VisitedFragments

end Semantics
end NamedFragment
end GraphQL
