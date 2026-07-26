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
    selectionSet :=
      Translate.reduceSelectionSet
        (Inline.inlineSelectionSet field.availableFragments field.selectionSet)
  }

def executableGroupToSpec (group : Name × List Execution.ExecutableField)
    : Name × List GraphQL.Execution.ExecutableField :=
  (group.fst, group.snd.map executableFieldToSpec)

def executableGroupsToSpec (groups : List (Name × List Execution.ExecutableField))
    : List (Name × List GraphQL.Execution.ExecutableField) :=
  groups.map executableGroupToSpec

def inlinedSelectionToSpec : Selection -> GraphQL.Selection
  | .field responseName fieldName arguments directives selectionSet =>
      .field responseName fieldName arguments directives
        (Translate.reduceSelectionSet selectionSet)
  | .inlineFragment typeCondition directives selectionSet =>
      .inlineFragment typeCondition directives (Translate.reduceSelectionSet selectionSet)
  | .fragmentSpread _fragmentName directives =>
      .inlineFragment none directives []

def selectionToSpecAfterInline
    (fragments : List FragmentDefinition) (selection : Selection)
    : GraphQL.Selection :=
  inlinedSelectionToSpec (Inline.inlineSelection fragments selection)

theorem translate_inlineSelection_singleton
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
      | none =>
          simp [Translate.reduceSelection]
      | some pair =>
          cases pair with
          | mk fragment remainingFragments =>
              simp [Translate.reduceSelection]

theorem translate_inlineSelectionSet_map
    (fragments : List FragmentDefinition)
    (selectionSet : List Selection)
    : Translate.reduceSelectionSet (Inline.inlineSelectionSet fragments selectionSet)
      = selectionSet.map (selectionToSpecAfterInline fragments) := by
  induction selectionSet with
  | nil =>
      simp [Translate.reduceSelectionSet]
  | cons selection rest ih =>
      simp [Inline.inlineSelectionSet, Translate.reduceSelectionSet,
        translate_inlineSelection_singleton fragments selection, ih,
        selectionToSpecAfterInline]

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

mutual
  theorem collectSelection_toSpec
      : ∀ (schema : Schema) (variableValues : Execution.VariableValues)
            (fragments : List FragmentDefinition) (parentType : Name)
            (source : Execution.ResolverValue ObjectRef) (selection : Selection),
          executableGroupsToSpec
            (Execution.collectSelection schema variableValues fragments
              parentType source selection)
          = GraphQL.Execution.collectSelection schema variableValues parentType
              source (selectionToSpecAfterInline fragments selection)
    | schema, variableValues, fragments, parentType, source,
        .field responseName fieldName arguments directives selectionSet => by
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            selectionToSpecAfterInline, inlinedSelectionToSpec,
            Inline.inlineSelection, executableGroupsToSpec,
            executableGroupToSpec, executableFieldToSpec, hdirectives]
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            selectionToSpecAfterInline, inlinedSelectionToSpec,
            Inline.inlineSelection, executableGroupsToSpec, hdirectives]
    | schema, variableValues, fragments, parentType, source,
        .inlineFragment none directives selectionSet => by
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            selectionToSpecAfterInline, inlinedSelectionToSpec,
            Inline.inlineSelection, hdirectives]
          exact collectFields_toSpec schema variableValues fragments parentType
            source selectionSet
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            selectionToSpecAfterInline, inlinedSelectionToSpec,
            Inline.inlineSelection, hdirectives, executableGroupsToSpec]
    | schema, variableValues, fragments, parentType, source,
        .inlineFragment (some typeCondition) directives selectionSet => by
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · by_cases happly :
              GraphQL.Execution.doesFragmentTypeApplyBool schema parentType
                source typeCondition = true
          · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
              selectionToSpecAfterInline, inlinedSelectionToSpec,
              Inline.inlineSelection, hdirectives, happly]
            exact collectFields_toSpec schema variableValues fragments parentType
              source selectionSet
          · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
              selectionToSpecAfterInline, inlinedSelectionToSpec,
              Inline.inlineSelection, hdirectives, happly, executableGroupsToSpec]
        · simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
            selectionToSpecAfterInline, inlinedSelectionToSpec,
            Inline.inlineSelection, hdirectives, executableGroupsToSpec]
    | schema, variableValues, fragments, parentType, source,
        .fragmentSpread fragmentName directives => by
        by_cases hdirectives :
            GraphQL.Execution.selectionDirectivesAllowBool variableValues
              directives = true
        · generalize hlookup :
              lookupFragmentAndRestLt? fragmentName fragments = lookupResult
          cases lookupResult with
          | none =>
              simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
                selectionToSpecAfterInline, inlinedSelectionToSpec,
                Inline.inlineSelection, hdirectives,
                hlookup, GraphQL.Execution.collectFields,
                Translate.reduceSelectionSet, executableGroupsToSpec]
          | some pair =>
              cases pair with
              | mk fragment remainingFragments =>
                  by_cases happly :
                      GraphQL.Execution.doesFragmentTypeApplyBool schema
                        parentType source fragment.typeCondition = true
                  · simp [Execution.collectSelection,
                      GraphQL.Execution.collectSelection,
                      selectionToSpecAfterInline, inlinedSelectionToSpec,
                      Inline.inlineSelection, hdirectives, hlookup, happly]
                    exact collectFields_toSpec schema variableValues
                      remainingFragments.val parentType source
                      fragment.selectionSet
                  · simp [Execution.collectSelection,
                      GraphQL.Execution.collectSelection,
                      selectionToSpecAfterInline, inlinedSelectionToSpec,
                      Inline.inlineSelection, hdirectives, hlookup, happly,
                      executableGroupsToSpec]
        · generalize hlookup :
              lookupFragmentAndRestLt? fragmentName fragments = lookupResult
          cases lookupResult with
          | none =>
              simp [Execution.collectSelection, GraphQL.Execution.collectSelection,
                selectionToSpecAfterInline, inlinedSelectionToSpec,
                Inline.inlineSelection, hdirectives, hlookup,
                executableGroupsToSpec]
          | some pair =>
              cases pair with
              | mk fragment remainingFragments =>
                  simp [Execution.collectSelection,
                    GraphQL.Execution.collectSelection,
                    selectionToSpecAfterInline, inlinedSelectionToSpec,
                    Inline.inlineSelection, hdirectives, hlookup,
                    executableGroupsToSpec]
  termination_by _schema _variableValues fragments _parentType _source selection =>
    (fragments.length, sizeOf selection, 0)
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

  theorem collectFields_toSpec
      : ∀ (schema : Schema) (variableValues : Execution.VariableValues)
            (fragments : List FragmentDefinition) (parentType : Name)
            (source : Execution.ResolverValue ObjectRef)
            (selectionSet : List Selection),
          executableGroupsToSpec
            (Execution.collectFields schema variableValues fragments parentType
              source selectionSet)
          = GraphQL.Execution.collectFields schema variableValues parentType source
              (Translate.reduceSelectionSet
                (Inline.inlineSelectionSet fragments selectionSet))
    | schema, variableValues, fragments, parentType, source, [] => by
        simp [Execution.collectFields, GraphQL.Execution.collectFields,
          executableGroupsToSpec, Translate.reduceSelectionSet]
    | schema, variableValues, fragments, parentType, source,
        selection :: rest => by
        rw [translate_inlineSelectionSet_map]
        simp [Execution.collectFields, GraphQL.Execution.collectFields,
          mergeExecutableGroups_toSpec,
          collectSelection_toSpec schema variableValues fragments parentType
            source selection,
          collectFields_toSpec schema variableValues fragments parentType source
            rest,
          translate_inlineSelectionSet_map fragments rest]
  termination_by _schema _variableValues fragments _parentType _source selectionSet =>
    (fragments.length, sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

theorem collectSubfields_toSpec
    (schema : Schema) (variableValues : Execution.VariableValues)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    (fields : List Execution.ExecutableField)
    : executableGroupsToSpec
        (Execution.collectSubfields schema variableValues objectType objectValue fields)
      = GraphQL.Execution.collectSubfields schema variableValues objectType
          objectValue (fields.map executableFieldToSpec) := by
  induction fields with
  | nil =>
      simp [Execution.collectSubfields, GraphQL.Execution.collectSubfields,
        executableGroupsToSpec]
  | cons field rest ih =>
      simp [Execution.collectSubfields, GraphQL.Execution.collectSubfields,
        mergeExecutableGroups_toSpec, ih, executableFieldToSpec]
      rw [collectFields_toSpec schema variableValues field.availableFragments
        objectType objectValue field.selectionSet
      ]

end Semantics
end NamedFragment
end GraphQL
