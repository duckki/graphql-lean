import Proofs.GraphQL.NamedFragment.Inline.Basic
import GraphQL.NamedFragment.Translate

/-! Direct-execution proof witnesses for fragment-free named-fragment operations. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

variable {ObjectRef : Type}

def executableFieldToSpec (field : Execution.ExecutableField)
    : GraphQL.Execution.ExecutableField :=
  {
    parentType := field.parentType
    responseName := field.responseName
    fieldName := field.fieldName
    arguments := field.arguments
    selectionSet := Translate.reduceSelectionSet field.selectionSet
  }

def executableGroupToSpec (group : Name × List Execution.ExecutableField)
    : Name × List GraphQL.Execution.ExecutableField :=
  (group.fst, group.snd.map executableFieldToSpec)

def executableGroupsToSpec (groups : List (Name × List Execution.ExecutableField))
    : List (Name × List GraphQL.Execution.ExecutableField) :=
  groups.map executableGroupToSpec

def executableFieldsInlined (fields : List Execution.ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> selectionSetInlined field.selectionSet

def executableGroupsInlined (groups : List (Name × List Execution.ExecutableField))
    : Prop :=
  ∀ group, group ∈ groups -> executableFieldsInlined group.snd

def inlinedSelectionToSpec : Selection -> GraphQL.Selection
  | .field responseName fieldName arguments directives selectionSet =>
      .field responseName fieldName arguments directives
        (Translate.reduceSelectionSet selectionSet)
  | .inlineFragment typeCondition directives selectionSet =>
      .inlineFragment typeCondition directives (Translate.reduceSelectionSet selectionSet)
  | .fragmentSpread _fragmentName directives =>
      .inlineFragment none directives []

theorem reduceSelection_eq_singleton_inlinedSelectionToSpec
    (selection : Selection)
    (hinlined : selectionInlined selection)
    : Translate.reduceSelection selection = [inlinedSelectionToSpec selection] := by
  cases selection <;>
    simp [selectionInlined, inlinedSelectionToSpec, Translate.reduceSelection]
      at hinlined ⊢

theorem addExecutableGroup_toSpec
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : executableGroupsToSpec (Execution.addExecutableGroup group groups)
      = GraphQL.Execution.addExecutableGroup (executableGroupToSpec group)
          (executableGroupsToSpec groups) := by
  induction groups with
  | nil =>
      simp [executableGroupsToSpec, executableGroupToSpec,
        Execution.addExecutableGroup, GraphQL.Execution.addExecutableGroup]
  | cons head rest ih =>
      cases group with
      | mk groupResponseName groupFields =>
          cases head with
          | mk responseName fields =>
              by_cases hresponse : responseName == groupResponseName
              · simp [executableGroupsToSpec, executableGroupToSpec,
                  Execution.addExecutableGroup,
                  GraphQL.Execution.addExecutableGroup, hresponse,
                  List.map_append]
              · simp [executableGroupsToSpec, executableGroupToSpec,
                  Execution.addExecutableGroup,
                  GraphQL.Execution.addExecutableGroup, hresponse]
                simpa [executableGroupsToSpec, executableGroupToSpec] using ih

theorem mergeExecutableGroups_toSpec
    (left right : List (Name × List Execution.ExecutableField))
    : executableGroupsToSpec (Execution.mergeExecutableGroups left right)
      = GraphQL.Execution.mergeExecutableGroups (executableGroupsToSpec left)
          (executableGroupsToSpec right) := by
  induction right generalizing left with
  | nil =>
      simp [executableGroupsToSpec, Execution.mergeExecutableGroups,
        GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change
        executableGroupsToSpec
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup group left) rest)
          =
        GraphQL.Execution.mergeExecutableGroups
          (GraphQL.Execution.addExecutableGroup
            (executableGroupToSpec group) (executableGroupsToSpec left))
          (executableGroupsToSpec rest)
      rw [ih (Execution.addExecutableGroup group left)]
      rw [addExecutableGroup_toSpec]

theorem addExecutableGroup_inlined
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    (hgroup : executableFieldsInlined group.snd)
    (hgroups : executableGroupsInlined groups)
    : executableGroupsInlined (Execution.addExecutableGroup group groups) := by
  induction groups with
  | nil =>
      intro candidate hcandidate
      simp [Execution.addExecutableGroup] at hcandidate
      subst candidate
      exact hgroup
  | cons head rest ih =>
      cases group with
      | mk groupResponseName groupFields =>
          cases head with
          | mk responseName fields =>
              have hfields : executableFieldsInlined fields :=
                hgroups (responseName, fields) (by simp)
              have hrest : executableGroupsInlined rest := by
                intro candidate hcandidate
                exact hgroups candidate (by simp [hcandidate])
              by_cases hresponse : responseName == groupResponseName
              · intro candidate hcandidate
                simp [Execution.addExecutableGroup, hresponse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  intro field hfield
                  simp at hfield
                  rcases hfield with hfield | hfield
                  · exact hfields field hfield
                  · exact hgroup field hfield
                · exact hrest candidate hcandidate
              · intro candidate hcandidate
                simp [Execution.addExecutableGroup, hresponse] at hcandidate
                rcases hcandidate with hcandidate | hcandidate
                · subst candidate
                  exact hfields
                · exact ih hrest candidate hcandidate

theorem mergeExecutableGroups_inlined
    (left right : List (Name × List Execution.ExecutableField))
    (hleft : executableGroupsInlined left)
    (hright : executableGroupsInlined right)
    : executableGroupsInlined (Execution.mergeExecutableGroups left right) := by
  induction right generalizing left with
  | nil => simpa [Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      have hgroup : executableFieldsInlined group.snd :=
        hright group (by simp)
      have hrest : executableGroupsInlined rest := by
        intro candidate hcandidate
        exact hright candidate (by simp [hcandidate])
      apply ih (Execution.addExecutableGroup group left)
      · exact addExecutableGroup_inlined group left hgroup hleft
      · exact hrest

mutual
  theorem collectSelection_toSpec_of_inlined
      : ∀ (schema : Schema) (variableValues : Execution.VariableValues)
          (fragments : List FragmentDefinition) (visitedFragments : List Name)
          (parentType : Name) (source : Execution.ResolverValue ObjectRef)
          (selection : Selection),
          selectionInlined selection
          ->  let collected :=
                Execution.collectSelection schema variableValues fragments
                  visitedFragments parentType source selection
              executableGroupsToSpec collected.groupedFields
                = GraphQL.Execution.collectSelection schema variableValues parentType
                    source (inlinedSelectionToSpec selection)
              ∧ collected.visitedFragments = visitedFragments
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        .field responseName fieldName arguments directives selectionSet => by
        intro hinlined
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            inlinedSelectionToSpec, executableGroupsToSpec,
            executableGroupToSpec, executableFieldToSpec, hdirectives]
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            inlinedSelectionToSpec, executableGroupsToSpec, hdirectives]
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        .inlineFragment none directives selectionSet => by
        intro hinlined
        simp [selectionInlined] at hinlined
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            inlinedSelectionToSpec, hdirectives]
          exact collectFields_toSpec_of_inlined schema variableValues fragments
            visitedFragments parentType source selectionSet hinlined
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            inlinedSelectionToSpec, hdirectives, executableGroupsToSpec]
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        .inlineFragment (some typeCondition) directives selectionSet => by
        intro hinlined
        simp [selectionInlined] at hinlined
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · by_cases happly :
              GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                source typeCondition = true
          · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
              inlinedSelectionToSpec, hdirectives, happly]
            exact collectFields_toSpec_of_inlined schema variableValues fragments
              visitedFragments parentType source selectionSet hinlined
          · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
              inlinedSelectionToSpec, hdirectives, happly, executableGroupsToSpec]
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            inlinedSelectionToSpec, hdirectives, executableGroupsToSpec]
    | _schema, _variableValues, _fragments, _visitedFragments, _parentType, _source,
        .fragmentSpread _fragmentName _directives => by
        simp [selectionInlined]

  theorem collectFields_toSpec_of_inlined
      : ∀ (schema : Schema) (variableValues : Execution.VariableValues)
          (fragments : List FragmentDefinition) (visitedFragments : List Name)
          (parentType : Name) (source : Execution.ResolverValue ObjectRef)
          (selectionSet : List Selection),
          selectionSetInlined selectionSet
          ->  let collected :=
                Execution.collectFields schema variableValues fragments
                  visitedFragments parentType source selectionSet
              executableGroupsToSpec collected.groupedFields
                = GraphQL.Execution.collectFields schema variableValues parentType source
                    (Translate.reduceSelectionSet selectionSet)
              ∧ collected.visitedFragments = visitedFragments
    | schema, variableValues, fragments, visitedFragments, parentType, source, [] => by
        intro _hinlined
        simp [Execution.collectFields, GraphQL.Execution.collectFields,
          executableGroupsToSpec, Translate.reduceSelectionSet]
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        selection :: rest => by
        intro hinlined
        simp [selectionSetInlined] at hinlined
        rcases hinlined with ⟨hselection, hrest⟩
        have hselected :=
          collectSelection_toSpec_of_inlined schema variableValues fragments
            visitedFragments parentType source selection hselection
        have hremaining :=
          collectFields_toSpec_of_inlined schema variableValues fragments
            visitedFragments parentType source rest hrest
        simp only [Execution.collectFields]
        rw [hselected.2]
        constructor
        · rw [mergeExecutableGroups_toSpec, hselected.1, hremaining.1]
          rw [Translate.reduceSelectionSet]
          rw [reduceSelection_eq_singleton_inlinedSelectionToSpec selection hselection]
          simp [GraphQL.Execution.collectFields]
        · exact hremaining.2
end

mutual
  theorem collectSelection_inlined
      : ∀ (schema : Schema) (variableValues : Execution.VariableValues)
          (fragments : List FragmentDefinition) (visitedFragments : List Name)
          (parentType : Name) (source : Execution.ResolverValue ObjectRef)
          (selection : Selection),
          selectionInlined selection
          -> executableGroupsInlined
              (Execution.collectSelection schema variableValues fragments
                visitedFragments parentType source selection).groupedFields
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        .field responseName fieldName arguments directives selectionSet => by
        intro hinlined
        simp [selectionInlined] at hinlined
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · simp [Execution.collectSelection, hdirectives, executableGroupsInlined,
            executableFieldsInlined, hinlined]
        · simp [Execution.collectSelection, hdirectives, executableGroupsInlined]
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        .inlineFragment none directives selectionSet => by
        intro hinlined
        simp [selectionInlined] at hinlined
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · simp [Execution.collectSelection, hdirectives]
          exact collectFields_inlined schema variableValues fragments
            visitedFragments parentType source selectionSet hinlined
        · simp [Execution.collectSelection, hdirectives, executableGroupsInlined]
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        .inlineFragment (some typeCondition) directives selectionSet => by
        intro hinlined
        simp [selectionInlined] at hinlined
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · by_cases happly :
              GraphQL.Execution.doesFragmentTypeApplyBool schema parentType source
                typeCondition = true
          · simp [Execution.collectSelection, hdirectives, happly]
            exact collectFields_inlined schema variableValues fragments
              visitedFragments parentType source selectionSet hinlined
          · simp [Execution.collectSelection, hdirectives, happly,
              executableGroupsInlined]
        · simp [Execution.collectSelection, hdirectives, executableGroupsInlined]
    | _schema, _variableValues, _fragments, _visitedFragments, _parentType, _source,
        .fragmentSpread _fragmentName _directives => by
        simp [selectionInlined]

  theorem collectFields_inlined
      : ∀ (schema : Schema) (variableValues : Execution.VariableValues)
          (fragments : List FragmentDefinition) (visitedFragments : List Name)
          (parentType : Name) (source : Execution.ResolverValue ObjectRef)
          (selectionSet : List Selection),
          selectionSetInlined selectionSet
          -> executableGroupsInlined
              (Execution.collectFields schema variableValues fragments
                visitedFragments parentType source selectionSet).groupedFields
    | _schema, _variableValues, _fragments, _visitedFragments, _parentType, _source,
        [] => by
        intro _hinlined
        simp [Execution.collectFields, executableGroupsInlined]
    | schema, variableValues, fragments, visitedFragments, parentType, source,
        selection :: rest => by
        intro hinlined
        simp [selectionSetInlined] at hinlined
        rcases hinlined with ⟨hselection, hrest⟩
        simp only [Execution.collectFields]
        apply mergeExecutableGroups_inlined
        · exact collectSelection_inlined schema variableValues fragments
            visitedFragments parentType source selection hselection
        · exact collectFields_inlined schema variableValues fragments
            (Execution.collectSelection schema variableValues fragments
              visitedFragments parentType source selection).visitedFragments
            parentType source rest hrest
end

theorem collectSubfields_inlined
    (schema : Schema) (variableValues : Execution.VariableValues)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    : ∀ (fields : List Execution.ExecutableField),
        executableFieldsInlined fields
        -> executableGroupsInlined
            (Execution.collectSubfields schema variableValues objectType objectValue
              fields)
  | [], _hinlined => by
      simp [Execution.collectSubfields, executableGroupsInlined]
  | field :: rest, hinlined => by
      have hfield : selectionSetInlined field.selectionSet :=
        hinlined field (by simp)
      have hrest : executableFieldsInlined rest := by
        intro candidate hcandidate
        exact hinlined candidate (by simp [hcandidate])
      simp only [Execution.collectSubfields]
      apply mergeExecutableGroups_inlined
      · exact collectFields_inlined schema variableValues field.availableFragments []
          objectType objectValue field.selectionSet hfield
      · exact collectSubfields_inlined schema variableValues objectType objectValue
          rest hrest

theorem collectSubfields_toSpec
    (schema : Schema) (variableValues : Execution.VariableValues)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    : ∀ (fields : List Execution.ExecutableField),
        (∀ field, field ∈ fields -> selectionSetInlined field.selectionSet)
        -> executableGroupsToSpec
              (Execution.collectSubfields schema variableValues objectType objectValue
                fields)
            = GraphQL.Execution.collectSubfields schema variableValues objectType
                objectValue (fields.map executableFieldToSpec)
  | [], _hinlined => by
      simp [Execution.collectSubfields, GraphQL.Execution.collectSubfields,
        executableGroupsToSpec]
  | field :: rest, hinlined => by
      have hfield : selectionSetInlined field.selectionSet :=
        hinlined field (by simp)
      have hrest : ∀ candidate, candidate ∈ rest
          -> selectionSetInlined candidate.selectionSet := by
        intro candidate hcandidate
        exact hinlined candidate (by simp [hcandidate])
      simp [Execution.collectSubfields, GraphQL.Execution.collectSubfields,
        mergeExecutableGroups_toSpec, executableFieldToSpec,
        collectSubfields_toSpec schema variableValues objectType objectValue rest hrest]
      rw [(collectFields_toSpec_of_inlined schema variableValues
        field.availableFragments [] objectType objectValue field.selectionSet
        hfield).1]

end Semantics
end NamedFragment
end GraphQL
