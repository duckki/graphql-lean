import GraphQL.NamedFragment.Execution
import GraphQL.NamedFragment.Operation
import GraphQL.NamedFragment.Translate
import GraphQL.NamedFragment.Validation
import Tests.GraphQL.Execution

namespace GraphQL
namespace Tests
namespace NamedFragment

def characterNameFragment : GraphQL.NamedFragment.FragmentDefinition :=
  {
    name := "CharacterName"
    typeCondition := "Character"
    selectionSet :=
      [.field "name" "name" [] [] []]
  }

def heroWithNamedFragment : GraphQL.NamedFragment.Operation :=
  {
    name := some "HeroWithNamedFragment"
    fragmentDefinitions := [characterNameFragment]
    selectionSet :=
      [.field "mainHero" "hero" [] [] [.fragmentSpread "CharacterName" []]]
  }

theorem namedFragmentNamesUniqueSmoke
    : GraphQL.NamedFragment.Validation.fragmentNamesUnique
        heroWithNamedFragment.fragmentDefinitions := by
  simp [GraphQL.NamedFragment.Validation.fragmentNamesUnique,
    heroWithNamedFragment, characterNameFragment]

theorem namedFragmentAcyclicSmoke
    : GraphQL.NamedFragment.Validation.fragmentsAcyclicBool
        heroWithNamedFragment.fragmentDefinitions
      = true := by
  native_decide

theorem executeNamedFragmentQuerySmoke
    : Execution.responseEqBool
        (GraphQL.NamedFragment.Execution.executeQuery
          Execution.sampleSchema Execution.sampleResolvers []
          heroWithNamedFragment
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("mainHero", .object [("name", .scalar "Leia")])])
      = true := by
  native_decide

def variableDefaultQuery : GraphQL.NamedFragment.Operation :=
  {
    name := some "VariableDefault"
    variableDefinitions :=
      [{
        name := "includeName"
        typeRef := .named "Boolean"
        defaultValue := some (.boolean true)
      }]
    selectionSet :=
      [.field "name" "name" [] [.include (.variable "includeName")] []]
  }

theorem executeQueryUsesVariableDefaultSmoke
    : Execution.responseEqBool
        (GraphQL.NamedFragment.Execution.executeQuery Execution.sampleSchema
          Execution.rootNameResolvers [] variableDefaultQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("name", .scalar "Query")])
      = true := by
  native_decide

def variableUsingFragment : GraphQL.NamedFragment.FragmentDefinition :=
  {
    name := "VariableUsing"
    typeCondition := "Query"
    selectionSet :=
      [.field "name" "name" [] [.include (.variable "included")] []]
  }

def transitiveVariableFragment : GraphQL.NamedFragment.FragmentDefinition :=
  {
    name := "Transitive"
    typeCondition := "Query"
    selectionSet := [.fragmentSpread "VariableUsing" []]
  }

def transitivelyUsedVariableOperation : GraphQL.NamedFragment.Operation :=
  {
    name := some "TransitivelyUsedVariable"
    variableDefinitions :=
      [{ name := "included", typeRef := .nonNull (.named "Boolean") }]
    fragmentDefinitions := [transitiveVariableFragment, variableUsingFragment]
    selectionSet := [.fragmentSpread "Transitive" []]
  }

theorem transitivelyReferencedFragmentVariableCountsAsUsed
    : GraphQL.NamedFragment.Validation.operationVariablesUsed
        transitivelyUsedVariableOperation := by
  simp [GraphQL.NamedFragment.Validation.operationVariablesUsed,
    transitivelyUsedVariableOperation, transitiveVariableFragment,
    variableUsingFragment,
    GraphQL.NamedFragment.Validation.selectionSetVariables,
    GraphQL.NamedFragment.Validation.selectionVariables,
    GraphQL.NamedFragment.lookupFragmentAndRestLt?,
    GraphQL.Validation.directivesVariables,
    GraphQL.Validation.directiveVariables,
    GraphQL.Validation.inputValueVariables]

def variableOnlyInUnusedFragmentOperation : GraphQL.NamedFragment.Operation :=
  {
    name := some "VariableOnlyInUnusedFragment"
    variableDefinitions :=
      [{ name := "included", typeRef := .nonNull (.named "Boolean") }]
    fragmentDefinitions := [variableUsingFragment]
    selectionSet := [.field "name" "name" [] [] []]
  }

theorem variableUseInUnreferencedFragmentDoesNotCount
    : ¬ GraphQL.NamedFragment.Validation.operationVariablesUsed
          variableOnlyInUnusedFragmentOperation := by
  simp [GraphQL.NamedFragment.Validation.operationVariablesUsed,
    variableOnlyInUnusedFragmentOperation,
    GraphQL.NamedFragment.Validation.selectionSetVariables,
    GraphQL.NamedFragment.Validation.selectionVariables,
    GraphQL.Validation.argumentsVariables,
    GraphQL.Validation.directivesVariables]

theorem variableOnlyInUnusedFragmentOperationRejected
    : ¬ GraphQL.NamedFragment.Validation.operationDefinitionValid
          Execution.sampleSchema variableOnlyInUnusedFragmentOperation := by
  intro hvalid
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsUsed,
      _hfragmentDefinitionsValid, _hselectionNonempty, _hselectionValid,
      _hmerge, hvariablesUsed⟩
  exact variableUseInUnreferencedFragmentDoesNotCount hvariablesUsed

def cyclicFragments : List GraphQL.NamedFragment.FragmentDefinition :=
  [
    {
      name := "A"
      typeCondition := "Character"
      selectionSet := [.fragmentSpread "B" []]
    },
    {
      name := "B"
      typeCondition := "Character"
      selectionSet := [.fragmentSpread "A" []]
    }
  ]

theorem cyclicFragmentsRejectedSmoke
    : GraphQL.NamedFragment.Validation.fragmentsAcyclicBool cyclicFragments = false := by
  native_decide

def undefinedFragmentOperation : GraphQL.NamedFragment.Operation :=
  {
    name := some "UndefinedFragment"
    fragmentDefinitions := []
    selectionSet :=
      [.field "mainHero" "hero" [] [] [.fragmentSpread "MissingFragment" []]]
  }

theorem undefinedFragmentOperationRejectedSmoke
    : ¬ GraphQL.NamedFragment.Validation.operationDefinitionValid
          Execution.sampleSchema undefinedFragmentOperation := by
  intro hvalid
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsUsed,
      _hfragmentDefinitionsValid, _hselectionNonempty, hselectionValid, _hmerge,
      _hvariablesUsed⟩
  have hrootFieldValid :
      GraphQL.NamedFragment.Validation.selectionValid Execution.sampleSchema
        undefinedFragmentOperation.variableDefinitions
        undefinedFragmentOperation.fragmentDefinitions
        (undefinedFragmentOperation.rootType Execution.sampleSchema)
        (.field "mainHero" "hero" [] [] [.fragmentSpread "MissingFragment" []]) :=
    by
      unfold GraphQL.NamedFragment.Validation.selectionSetValid at hselectionValid
      exact hselectionValid
        (.field "mainHero" "hero" [] [] [.fragmentSpread "MissingFragment" []])
        (by simp [undefinedFragmentOperation])
  simp [undefinedFragmentOperation,
    GraphQL.NamedFragment.Validation.selectionValid,
    GraphQL.NamedFragment.Validation.fieldSelectionSetValid,
    GraphQL.NamedFragment.Validation.selectionSetValid,
    GraphQL.NamedFragment.lookupFragment?] at hrootFieldValid

def fragmentAwareInlineStatementSmoke : Prop :=
  GraphQL.NamedFragment.Semantics.fragmentAwareExecutionEquivalentToInline
    Execution.sampleSchema heroWithNamedFragment

def translatedInlinedOperationSmoke : GraphQL.Operation :=
  GraphQL.NamedFragment.Translate.reduceOperation
    (GraphQL.NamedFragment.Inline.inlineOperation heroWithNamedFragment)

def fragmentAwareToSpecStatementSmoke : Prop :=
  GraphQL.NamedFragment.Semantics.fragmentAwareInlinedExecutionEquivalentToSpecExecution
    Execution.sampleSchema
    (GraphQL.NamedFragment.Inline.inlineOperation heroWithNamedFragment)

def pairFragment : GraphQL.NamedFragment.FragmentDefinition :=
  {
    name := "Pair"
    typeCondition := "Query"
    selectionSet :=
      [.field "name" "name" [] [] [], .field "age" "age" [] [] []]
  }

def pairFragmentGroups (selectionSet : List GraphQL.NamedFragment.Selection)
    : List (Name × Nat) :=
  let collected :=
    GraphQL.NamedFragment.Execution.collectFields Execution.sampleSchema []
      [pairFragment] [] "Query"
      (GraphQL.Execution.ResolverValue.object "Query" ()) selectionSet
  collected.groupedFields.map fun group => (group.fst, group.snd.length)

theorem repeatedSiblingSpreadVisitedOnce
    : let collected :=
        GraphQL.NamedFragment.Execution.collectFields Execution.sampleSchema []
          [pairFragment] [] "Query"
          (GraphQL.Execution.ResolverValue.object "Query" ())
          [.fragmentSpread "Pair" [], .fragmentSpread "Pair" []]
      collected.visitedFragments = ["Pair"]
      ∧ pairFragmentGroups [.fragmentSpread "Pair" [], .fragmentSpread "Pair" []]
        = [("name", 1), ("age", 1)] := by
  native_decide

def repeatedPairSpreadOperation : GraphQL.NamedFragment.Operation :=
  {
    name := some "RepeatedPair"
    fragmentDefinitions := [pairFragment]
    selectionSet := [.fragmentSpread "Pair" [], .fragmentSpread "Pair" []]
  }

def pairResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "name" => some (.scalar "Query")
        | "Query", "age" => some (.scalar "42")
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

theorem repeatedSpreadExecutionMatchesStaticInlining
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let direct :=
        GraphQL.NamedFragment.Execution.executeQueryWithFuel Execution.sampleSchema
          pairResolvers [] repeatedPairSpreadOperation 20 source
      let inlined :=
        GraphQL.NamedFragment.Execution.executeQueryWithFuel Execution.sampleSchema
          pairResolvers []
          (GraphQL.NamedFragment.Inline.inlineOperation repeatedPairSpreadOperation)
          20 source
      direct.errors = inlined.errors
      ∧ Execution.responseEqBool direct.data inlined.data = true := by
  native_decide

def repeatedNestedSpreadOperation : GraphQL.NamedFragment.Operation :=
  {
    name := some "RepeatedNestedSpread"
    fragmentDefinitions := [characterNameFragment]
    selectionSet :=
      [.field "mainHero" "hero" [] []
        [.fragmentSpread "CharacterName" [], .fragmentSpread "CharacterName" []]]
  }

theorem repeatedNestedSpreadExecutionMatchesStaticInlining
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let direct :=
        GraphQL.NamedFragment.Execution.executeQueryWithFuel Execution.sampleSchema
          Execution.sampleResolvers [] repeatedNestedSpreadOperation 20 source
      let inlined :=
        GraphQL.NamedFragment.Execution.executeQueryWithFuel Execution.sampleSchema
          Execution.sampleResolvers []
          (GraphQL.NamedFragment.Inline.inlineOperation repeatedNestedSpreadOperation)
          20 source
      direct.errors = inlined.errors
      ∧ Execution.responseEqBool direct.data inlined.data = true := by
  native_decide

theorem skippedSpreadDoesNotVisitFragment
    : let selectionSet : List GraphQL.NamedFragment.Selection :=
        [.fragmentSpread "Pair" [.skip (.boolean true)], .fragmentSpread "Pair" []]
      let collected :=
        GraphQL.NamedFragment.Execution.collectFields Execution.sampleSchema []
          [pairFragment] [] "Query"
          (GraphQL.Execution.ResolverValue.object "Query" ()) selectionSet
      collected.visitedFragments = ["Pair"]
      ∧ pairFragmentGroups selectionSet = [("name", 1), ("age", 1)] := by
  native_decide

def nonApplicableFragment : GraphQL.NamedFragment.FragmentDefinition :=
  {
    name := "CharacterDetails"
    typeCondition := "Character"
    selectionSet := [.field "name" "name" [] [] []]
  }

theorem nonApplicableSpreadStillVisitsFragment
    : let collected :=
        GraphQL.NamedFragment.Execution.collectFields Execution.sampleSchema []
          [nonApplicableFragment] [] "Query"
          (GraphQL.Execution.ResolverValue.object "Query" ())
          [.fragmentSpread "CharacterDetails" [], .fragmentSpread "CharacterDetails" []]
      collected.visitedFragments = ["CharacterDetails"]
      ∧ collected.groupedFields.isEmpty := by
  native_decide

theorem inlineFragmentPropagatesVisitedFragments
    : let selectionSet : List GraphQL.NamedFragment.Selection :=
        [.inlineFragment none [] [.fragmentSpread "Pair" []], .fragmentSpread "Pair" []]
      let collected :=
        GraphQL.NamedFragment.Execution.collectFields Execution.sampleSchema []
          [pairFragment] [] "Query"
          (GraphQL.Execution.ResolverValue.object "Query" ()) selectionSet
      collected.visitedFragments = ["Pair"]
      ∧ pairFragmentGroups selectionSet = [("name", 1), ("age", 1)] := by
  native_decide

def pairSpreadExecutableField : GraphQL.NamedFragment.Execution.ExecutableField :=
  {
    parentType := "Query"
    responseName := "parent"
    fieldName := "parent"
    arguments := []
    selectionSet := [.fragmentSpread "Pair" []]
    availableFragments := [pairFragment]
  }

theorem collectSubfieldsUsesFreshVisitedFragments
    : let groups :=
        GraphQL.NamedFragment.Execution.collectSubfields Execution.sampleSchema []
          "Query" (GraphQL.Execution.ResolverValue.object "Query" ())
          [pairSpreadExecutableField, pairSpreadExecutableField]
      groups.map (fun group => (group.fst, group.snd.length))
      = [("name", 2), ("age", 2)] := by
  native_decide

end NamedFragment
end Tests
end GraphQL
