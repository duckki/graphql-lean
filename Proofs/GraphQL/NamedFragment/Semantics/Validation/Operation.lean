import Proofs.GraphQL.NamedFragment.Semantics.Validation.FragmentRemoval
import Proofs.GraphQL.NamedFragment.Semantics.Inline.Execution
import Proofs.GraphQL.NamedFragment.Validation.Translate

/-! Named-fragment validation preservation proofs. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

theorem inlineOperation_selectionSetValid_of_fragmentBodiesValid
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hfragmentBodies
      : ∀ {fragmentName : Name} {fragment : FragmentDefinition}
            {remaining
              : { remaining : List FragmentDefinition
                  // remaining.length < operation.fragmentDefinitions.length }},
          lookupFragmentAndRestLt? fragmentName operation.fragmentDefinitions
            = some (fragment, remaining)
          -> fragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  operation.variableDefinitions [] fragment.typeCondition
                  (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        (Inline.inlineOperation operation).variableDefinitions
        (Inline.inlineOperation operation).fragmentDefinitions
        (Inline.inlineOperation operation).rootType
        (Inline.inlineOperation operation).selectionSet := by
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsValid, _hselectionNonempty,
      hselectionValid, _hmerge, _hvariablesUsed⟩
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      simp [Inline.inlineOperation]
      exact selectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
        (fun {fragmentName} {fragment} {remaining} hlookup =>
          hfragmentBodies hlookup)
        hselectionValid

theorem inlineOperation_valid_of_fragmentBodiesValid
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hfragmentBodies
      : ∀ {fragmentName : Name} {fragment : FragmentDefinition}
            {remaining
              : { remaining : List FragmentDefinition
                  // remaining.length < operation.fragmentDefinitions.length }},
          lookupFragmentAndRestLt? fragmentName operation.fragmentDefinitions
            = some (fragment, remaining)
          -> fragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  operation.variableDefinitions [] fragment.typeCondition
                  (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
    : GraphQL.NamedFragment.Validation.operationDefinitionValid schema
        (Inline.inlineOperation operation) := by
  exact inlineOperation_valid_of_selectionSetValid hvalid
    (inlineOperation_selectionSetValid_of_fragmentBodiesValid hvalid
      hfragmentBodies)

theorem inlineOperation_selectionSetValid_of_localFragmentBodiesValid
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hfragmentBodies
      : ∀ {fragmentName : Name} {fragment : FragmentDefinition}
            {remaining
              : { remaining : List FragmentDefinition
                  // remaining.length < operation.fragmentDefinitions.length }},
          fragmentName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                operation.selectionSet
          -> lookupFragmentAndRestLt? fragmentName operation.fragmentDefinitions
              = some (fragment, remaining)
          -> fragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  operation.variableDefinitions [] fragment.typeCondition
                  (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        (Inline.inlineOperation operation).variableDefinitions
        (Inline.inlineOperation operation).fragmentDefinitions
        (Inline.inlineOperation operation).rootType
        (Inline.inlineOperation operation).selectionSet := by
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, _huniqueFragments,
      _hfragmentsAcyclic, _hfragmentDefinitionsValid, _hselectionNonempty,
      hselectionValid, _hmerge, _hvariablesUsed⟩
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      simp [Inline.inlineOperation]
      exact selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
        (fun hmem hlookup => hfragmentBodies hmem hlookup)
        hselectionValid

theorem inlineOperation_valid_of_localFragmentBodiesValid
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hfragmentBodies
      : ∀ {fragmentName : Name} {fragment : FragmentDefinition}
            {remaining
              : { remaining : List FragmentDefinition
                  // remaining.length < operation.fragmentDefinitions.length }},
          fragmentName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                operation.selectionSet
          -> lookupFragmentAndRestLt? fragmentName operation.fragmentDefinitions
              = some (fragment, remaining)
          -> fragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  operation.variableDefinitions [] fragment.typeCondition
                  (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
    : GraphQL.NamedFragment.Validation.operationDefinitionValid schema
        (Inline.inlineOperation operation) := by
  exact inlineOperation_valid_of_selectionSetValid hvalid
    (inlineOperation_selectionSetValid_of_localFragmentBodiesValid hvalid
      hfragmentBodies)

theorem inlineOperation_valid_of_reachable_removals
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    : GraphQL.NamedFragment.Validation.operationDefinitionValid schema
        (Inline.inlineOperation operation) := by
  have hvalidOriginal := hvalid
  rcases hvalid with
    ⟨_hroot, _hrootComposite, _hvariables, huniqueFragments,
      hfragmentsAcyclic, hfragmentDefinitionsValid, _hselectionNonempty,
      _hselectionValid, _hmerge, _hvariablesUsed⟩
  exact inlineOperation_valid_of_localFragmentBodiesValid hvalidOriginal
    (fun {_fragmentName} {_fragment} {_remaining} _hrootSpread hlookup =>
      fragmentInlineSelectionSetValid_after_reachable_removals
        huniqueFragments hfragmentsAcyclic hfragmentDefinitionsValid
        ReachableAncestorRemovals.root
        (GraphQL.NamedFragment.Validation.lookupFragment?_of_lookupFragmentAndRestLt?
          hlookup)
        hlookup)

-- Witness for the already-inlined spec-validity bridge used by the public
-- execution/spec theorem. It proves translation validity once the named-fragment
-- operation is valid and contains no fragment spreads.
theorem inlinedOperation_translatesToSpecValid
    (schema : Schema) (operation : Operation)
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hinlined : operationInlined operation)
    : GraphQL.Validation.operationDefinitionValid schema
        (Translate.reduceOperation operation) :=
  _root_.GraphQL.NamedFragment.Validation.TranslateValidation.operationDefinitionValid_toSpec_of_inlined
    hvalid hinlined

theorem fragmentAwareInlinedValidityPreservedToSpec_holds
    (schema : Schema) (operation : Operation)
    : fragmentAwareInlinedValidityPreservedToSpec schema operation := by
  intro hvalid hinlined
  exact inlinedOperation_translatesToSpecValid schema operation hvalid hinlined

theorem inlinedOperation_specValidAndExecutionEquivalent
    (schema : Schema) (operation : Operation)
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hinlined : operationInlined operation)
    : GraphQL.Validation.operationDefinitionValid schema
        (Translate.reduceOperation operation)
      ∧ ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues fuel (source : Execution.ResolverValue ObjectRef),
          Execution.executeQueryWithFuel schema resolvers variableValues
            operation fuel source
          = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
              (Translate.reduceOperation operation) fuel source := by
  exact ⟨inlinedOperation_translatesToSpecValid schema operation hvalid hinlined,
    by
      intro ObjectRef resolvers variableValues fuel source
      exact executeQueryWithFuel_eq_spec_of_inlined schema resolvers
        variableValues operation fuel source hinlined⟩

theorem fragmentAwareValidityPreservedToInline_of_inlineSelectionSetValid
    {schema : Schema} {operation : Operation}
    (hselectionValid
      : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation
        -> GraphQL.NamedFragment.Validation.selectionSetValid schema
            (Inline.inlineOperation operation).variableDefinitions
            (Inline.inlineOperation operation).fragmentDefinitions
            (Inline.inlineOperation operation).rootType
            (Inline.inlineOperation operation).selectionSet)
    : fragmentAwareValidityPreservedToInline schema operation := by
  intro hvalid
  exact inlineOperation_valid_of_selectionSetValid hvalid
    (hselectionValid hvalid)

theorem fragmentAwareInlineValidityPreservedToSpec_of_inlineValidityPreserved
    {schema : Schema} {operation : Operation}
    (hpreserved : fragmentAwareValidityPreservedToInline schema operation)
    : fragmentAwareInlineValidityPreservedToSpec schema operation := by
  intro hvalid
  exact inlinedOperation_translatesToSpecValid schema
    (Inline.inlineOperation operation)
    (hpreserved hvalid)
    (inlineOperation_inlined operation)

theorem fragmentAwareValidityPreservedToInline_holds
    (schema : Schema) (operation : Operation)
    : fragmentAwareValidityPreservedToInline schema operation := by
  intro hvalid
  exact inlineOperation_valid_of_reachable_removals hvalid

theorem fragmentAwareInlineValidityPreservedToSpec_holds
    (schema : Schema) (operation : Operation)
    : fragmentAwareInlineValidityPreservedToSpec schema operation := by
  exact fragmentAwareInlineValidityPreservedToSpec_of_inlineValidityPreserved
    (fragmentAwareValidityPreservedToInline_holds schema operation)

theorem inlineOperation_specValidAndExecutionEquivalent_of_selectionSetValid
    (schema : Schema) (operation : Operation)
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hselectionValid
      : GraphQL.NamedFragment.Validation.selectionSetValid schema
          (Inline.inlineOperation operation).variableDefinitions
          (Inline.inlineOperation operation).fragmentDefinitions
          (Inline.inlineOperation operation).rootType
          (Inline.inlineOperation operation).selectionSet)
    : GraphQL.Validation.operationDefinitionValid schema
        (Translate.reduceOperation (Inline.inlineOperation operation))
      ∧ ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues fuel (source : Execution.ResolverValue ObjectRef),
          Execution.executeQueryWithFuel schema resolvers variableValues
            (Inline.inlineOperation operation) fuel source
          = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
              (Translate.reduceOperation (Inline.inlineOperation operation))
              fuel source := by
  exact inlinedOperation_specValidAndExecutionEquivalent schema
    (Inline.inlineOperation operation)
    (inlineOperation_valid_of_selectionSetValid hvalid hselectionValid)
    (inlineOperation_inlined operation)

theorem inlineOperation_specValidAndExecutionEquivalent_of_fragmentBodiesValid
    (schema : Schema) (operation : Operation)
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hfragmentBodies
      : ∀ {fragmentName : Name} {fragment : FragmentDefinition}
            {remaining
              : { remaining : List FragmentDefinition
                  // remaining.length < operation.fragmentDefinitions.length }},
          lookupFragmentAndRestLt? fragmentName operation.fragmentDefinitions
            = some (fragment, remaining)
          -> fragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  operation.variableDefinitions [] fragment.typeCondition
                  (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
    : GraphQL.Validation.operationDefinitionValid schema
        (Translate.reduceOperation (Inline.inlineOperation operation))
      ∧ ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues fuel (source : Execution.ResolverValue ObjectRef),
          Execution.executeQueryWithFuel schema resolvers variableValues
            (Inline.inlineOperation operation) fuel source
          = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
              (Translate.reduceOperation (Inline.inlineOperation operation))
              fuel source := by
  exact inlineOperation_specValidAndExecutionEquivalent_of_selectionSetValid
    schema operation hvalid
    (inlineOperation_selectionSetValid_of_fragmentBodiesValid hvalid
      hfragmentBodies)

theorem inlineOperation_specValidAndExecutionEquivalent_of_localFragmentBodiesValid
    (schema : Schema) (operation : Operation)
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hfragmentBodies
      : ∀ {fragmentName : Name} {fragment : FragmentDefinition}
            {remaining
              : { remaining : List FragmentDefinition
                  // remaining.length < operation.fragmentDefinitions.length }},
          fragmentName
            ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                operation.selectionSet
          -> lookupFragmentAndRestLt? fragmentName operation.fragmentDefinitions
              = some (fragment, remaining)
          -> fragment.selectionSet ≠ []
              ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                  operation.variableDefinitions [] fragment.typeCondition
                  (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
    : GraphQL.Validation.operationDefinitionValid schema
        (Translate.reduceOperation (Inline.inlineOperation operation))
      ∧ ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues fuel (source : Execution.ResolverValue ObjectRef),
          Execution.executeQueryWithFuel schema resolvers variableValues
            (Inline.inlineOperation operation) fuel source
          = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
              (Translate.reduceOperation (Inline.inlineOperation operation))
              fuel source := by
  exact inlineOperation_specValidAndExecutionEquivalent_of_selectionSetValid
    schema operation hvalid
    (inlineOperation_selectionSetValid_of_localFragmentBodiesValid hvalid
      hfragmentBodies)

end Semantics
end NamedFragment
end GraphQL
