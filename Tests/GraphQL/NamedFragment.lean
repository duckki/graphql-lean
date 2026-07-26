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
    rootType := "Query"
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
    rootType := "Query"
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
      _hfragmentsAcyclic, _hfragmentDefinitionsValid, _hselectionNonempty,
      hselectionValid, _hmerge⟩
  have hrootFieldValid :
      GraphQL.NamedFragment.Validation.selectionValid Execution.sampleSchema
        undefinedFragmentOperation.variableDefinitions
        undefinedFragmentOperation.fragmentDefinitions
        undefinedFragmentOperation.rootType
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

end NamedFragment
end Tests
end GraphQL
