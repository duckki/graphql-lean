import Proofs.GraphQL.NamedFragment.Semantics.Validation.FieldMerge
import Proofs.GraphQL.NamedFragment.Validation.Lookup

/-! Named-fragment validation preservation proofs. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

mutual
  theorem selectionValid_changeFragments_of_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition} {parentType : Name}
          {selection : Selection},
          GraphQL.NamedFragment.Validation.selectionValid schema
            variableDefinitions fragments parentType selection
          -> selectionInlined selection
          -> GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions [] parentType selection
    | schema, variableDefinitions, fragments, parentType,
        .field responseName fieldName arguments directives selectionSet,
        hvalid, hinlined => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, fieldDefinition, hlookup, harguments, hfield⟩
        simp [selectionInlined] at hinlined
        simp [GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, fieldDefinition, hlookup, harguments,
          fieldSelectionSetValid_changeFragments_of_inlined hfield hinlined⟩
    | schema, variableDefinitions, fragments, parentType,
        .inlineFragment none directives selectionSet, hvalid, hinlined => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with ⟨hdirectives, hnonempty, hselectionSet⟩
        simp [selectionInlined] at hinlined
        simp [GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hnonempty,
          selectionSetValid_changeFragments_of_inlined hselectionSet hinlined⟩
    | schema, variableDefinitions, fragments, parentType,
        .inlineFragment (some typeCondition) directives selectionSet,
        hvalid, hinlined => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, hcomposite, hoverlap, hnonempty, hselectionSet⟩
        simp [selectionInlined] at hinlined
        simp [GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hcomposite, hoverlap, hnonempty,
          selectionSetValid_changeFragments_of_inlined hselectionSet hinlined⟩
    | _schema, _variableDefinitions, _fragments, _parentType,
        .fragmentSpread _fragmentName _directives, _hvalid, hinlined => by
        simp [selectionInlined] at hinlined

  theorem selectionSetValid_changeFragments_of_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition} {parentType : Name}
          {selectionSet : List Selection},
          GraphQL.NamedFragment.Validation.selectionSetValid schema
            variableDefinitions fragments parentType selectionSet
          -> selectionSetInlined selectionSet
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions [] parentType selectionSet
    | _schema, _variableDefinitions, _fragments, _parentType, [],
        _hvalid, _hinlined => by
        simp [GraphQL.NamedFragment.Validation.selectionSetValid]
    | schema, variableDefinitions, fragments, parentType, selection :: rest,
        hvalid, hinlined => by
        simp [selectionSetInlined] at hinlined
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
        exact ⟨selectionValid_changeFragments_of_inlined hselectionValid
            hinlined.1,
          by
            simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
              selectionSetValid_changeFragments_of_inlined hrestValid
                hinlined.2⟩

  theorem fieldSelectionSetValid_changeFragments_of_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition}
          {fieldDefinition : FieldDefinition} {selectionSet : List Selection},
          GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
            variableDefinitions fragments fieldDefinition selectionSet
          -> selectionSetInlined selectionSet
          -> GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
              variableDefinitions [] fieldDefinition selectionSet
    | schema, variableDefinitions, fragments, fieldDefinition, selectionSet,
        hvalid, hinlined => by
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
              selectionSetValid_changeFragments_of_inlined hselectionSetValid
                hinlined⟩
end

theorem inlineSelectionSet_valid_changeFragments
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {fragments : List FragmentDefinition} {parentType : Name}
    {selectionSet : List Selection}
    (hvalid
      : GraphQL.NamedFragment.Validation.selectionSetValid schema
          variableDefinitions fragments parentType
          (Inline.inlineSelectionSet fragments selectionSet))
    : GraphQL.NamedFragment.Validation.selectionSetValid schema
        variableDefinitions [] parentType
        (Inline.inlineSelectionSet fragments selectionSet) :=
  selectionSetValid_changeFragments_of_inlined hvalid
    (inlineSelectionSet_inlined fragments selectionSet)

theorem inlineOperation_valid_of_inlinedSelectionSetValidWithFragments
    {schema : Schema} {operation : Operation}
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    (hselectionValid
      : GraphQL.NamedFragment.Validation.selectionSetValid schema
          (Inline.inlineOperation operation).variableDefinitions
          operation.fragmentDefinitions
          ((Inline.inlineOperation operation).rootType schema)
          (Inline.inlineOperation operation).selectionSet)
    : GraphQL.NamedFragment.Validation.operationDefinitionValid schema
        (Inline.inlineOperation operation) := by
  apply inlineOperation_valid_of_selectionSetValid hvalid
  cases operation with
  | mk name rootType variableDefinitions fragmentDefinitions selectionSet =>
      simpa [Inline.inlineOperation] using
        inlineSelectionSet_valid_changeFragments hselectionValid

mutual
  theorem selectionValid_inlineSelection_of_localFragmentBodiesValid
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition} {parentType : Name}
          {selection : Selection},
          (∀ {fragmentName : Name} {fragment : FragmentDefinition}
              {remaining
                : { remaining : List FragmentDefinition
                    // remaining.length < fragments.length }},
            fragmentName
              ∈ GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames selection
            -> lookupFragmentAndRestLt? fragmentName fragments
                = some (fragment, remaining)
            -> fragment.selectionSet ≠ []
                ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                    variableDefinitions [] fragment.typeCondition
                    (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
          -> GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions fragments parentType selection
          -> GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions [] parentType
              (Inline.inlineSelection fragments selection)
    | schema, variableDefinitions, fragments, parentType,
        .field responseName fieldName arguments directives selectionSet,
        hfragmentBodies, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, fieldDefinition, hlookup, harguments, hfield⟩
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, fieldDefinition, hlookup, harguments,
          fieldSelectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
            (fun hmem hlookup =>
              hfragmentBodies
                (by
                  simpa [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                    using hmem)
                hlookup)
            hfield⟩
    | schema, variableDefinitions, fragments, parentType,
        .inlineFragment none directives selectionSet, hfragmentBodies,
        hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with ⟨hdirectives, hnonempty, hselectionSet⟩
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, inlineSelectionSet_nonempty hnonempty,
          selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
            (fun hmem hlookup =>
              hfragmentBodies
                (by
                  simpa [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                    using hmem)
                hlookup)
            hselectionSet⟩
    | schema, variableDefinitions, fragments, parentType,
        .inlineFragment (some typeCondition) directives selectionSet,
        hfragmentBodies, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, hcomposite, hoverlap, hnonempty, hselectionSet⟩
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hcomposite, hoverlap,
          inlineSelectionSet_nonempty hnonempty,
          selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
            (fun hmem hlookup =>
              hfragmentBodies
                (by
                  simpa [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames]
                    using hmem)
                hlookup)
            hselectionSet⟩
    | schema, variableDefinitions, fragments, parentType,
        .fragmentSpread fragmentName directives, hfragmentBodies,
        hvalid => by
        rcases GraphQL.NamedFragment.Validation.selectionValid_fragmentSpread_lookupFragmentAndRestLt?
            hvalid with
          ⟨hdirectives, fragment, remaining, hlookup, hcomposite, hoverlap⟩
        rcases hfragmentBodies
            (by
              simp [GraphQL.NamedFragment.Validation.selectionFragmentSpreadNames])
            hlookup with
          ⟨hnonempty, hselectionSet⟩
        simp [Inline.inlineSelection, hlookup,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hcomposite, hoverlap,
          inlineSelectionSet_nonempty hnonempty, hselectionSet⟩

  theorem selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition} {parentType : Name}
          {selectionSet : List Selection},
          (∀ {fragmentName : Name} {fragment : FragmentDefinition}
              {remaining
                : { remaining : List FragmentDefinition
                    // remaining.length < fragments.length }},
            fragmentName
              ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                  selectionSet
            -> lookupFragmentAndRestLt? fragmentName fragments
                = some (fragment, remaining)
            -> fragment.selectionSet ≠ []
                ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                    variableDefinitions [] fragment.typeCondition
                    (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions fragments parentType selectionSet
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions [] parentType
              (Inline.inlineSelectionSet fragments selectionSet)
    | _schema, _variableDefinitions, _fragments, _parentType, [],
        _hfragmentBodies, _hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionSetValid]
    | schema, variableDefinitions, fragments, parentType, selection :: rest,
        hfragmentBodies, hvalid => by
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
        simp [Inline.inlineSelectionSet,
          GraphQL.NamedFragment.Validation.selectionSetValid]
        exact ⟨selectionValid_inlineSelection_of_localFragmentBodiesValid
            (fun hmem hlookup =>
              hfragmentBodies
                (by
                  simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                    hmem])
                hlookup)
            hselectionValid,
          by
            simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
              selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
                (fun hmem hlookup =>
                  hfragmentBodies
                    (by
                      simp [GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames,
                        hmem])
                    hlookup)
                hrestValid⟩

  theorem fieldSelectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition}
          {fieldDefinition : FieldDefinition} {selectionSet : List Selection},
          (∀ {fragmentName : Name} {fragment : FragmentDefinition}
              {remaining
                : { remaining : List FragmentDefinition
                    // remaining.length < fragments.length }},
            fragmentName
              ∈ GraphQL.NamedFragment.Validation.selectionSetFragmentSpreadNames
                  selectionSet
            -> lookupFragmentAndRestLt? fragmentName fragments
                = some (fragment, remaining)
            -> fragment.selectionSet ≠ []
                ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                    variableDefinitions [] fragment.typeCondition
                    (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
          -> GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
              variableDefinitions fragments fieldDefinition selectionSet
          -> GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
              variableDefinitions [] fieldDefinition
              (Inline.inlineSelectionSet fragments selectionSet)
    | schema, variableDefinitions, fragments, fieldDefinition, selectionSet,
        hfragmentBodies, hvalid => by
        simp [GraphQL.NamedFragment.Validation.fieldSelectionSetValid] at hvalid ⊢
        rcases hvalid with ⟨houtput, hshape⟩
        refine ⟨houtput, ?_⟩
        cases hshape with
        | inl hleaf =>
            rcases hleaf with ⟨hleaf, hselectionSetEmpty⟩
            exact Or.inl ⟨hleaf, by
              simp [hselectionSetEmpty]⟩
        | inr hcomposite =>
            rcases hcomposite with
              ⟨hcompositeType, hnonempty, hselectionSetValid⟩
            exact Or.inr ⟨hcompositeType,
              inlineSelectionSet_nonempty hnonempty,
              selectionSetValid_inlineSelectionSet_of_localFragmentBodiesValid
                hfragmentBodies hselectionSetValid⟩
end

mutual
  theorem selectionValid_inlineSelection_of_fragmentBodiesValid
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition} {parentType : Name}
          {selection : Selection},
          (∀ {fragmentName : Name} {fragment : FragmentDefinition}
              {remaining
                : { remaining : List FragmentDefinition
                    // remaining.length < fragments.length }},
            lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
            -> fragment.selectionSet ≠ []
                ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                    variableDefinitions [] fragment.typeCondition
                    (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
          -> GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions fragments parentType selection
          -> GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions [] parentType
              (Inline.inlineSelection fragments selection)
    | schema, variableDefinitions, fragments, parentType,
        .field responseName fieldName arguments directives selectionSet,
        hfragmentBodies, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, fieldDefinition, hlookup, harguments, hfield⟩
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, fieldDefinition, hlookup, harguments,
          fieldSelectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
            hfragmentBodies hfield⟩
    | schema, variableDefinitions, fragments, parentType,
        .inlineFragment none directives selectionSet, hfragmentBodies,
        hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with ⟨hdirectives, hnonempty, hselectionSet⟩
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, inlineSelectionSet_nonempty hnonempty,
          selectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
            hfragmentBodies hselectionSet⟩
    | schema, variableDefinitions, fragments, parentType,
        .inlineFragment (some typeCondition) directives selectionSet,
        hfragmentBodies, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨hdirectives, hcomposite, hoverlap, hnonempty, hselectionSet⟩
        simp [Inline.inlineSelection,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hcomposite, hoverlap,
          inlineSelectionSet_nonempty hnonempty,
          selectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
            hfragmentBodies hselectionSet⟩
    | schema, variableDefinitions, fragments, parentType,
        .fragmentSpread fragmentName directives, hfragmentBodies,
        hvalid => by
        rcases GraphQL.NamedFragment.Validation.selectionValid_fragmentSpread_lookupFragmentAndRestLt?
            hvalid with
          ⟨hdirectives, fragment, remaining, hlookup, hcomposite, hoverlap⟩
        rcases hfragmentBodies hlookup with ⟨hnonempty, hselectionSet⟩
        simp [Inline.inlineSelection, hlookup,
          GraphQL.NamedFragment.Validation.selectionValid]
        exact ⟨hdirectives, hcomposite, hoverlap,
          inlineSelectionSet_nonempty hnonempty, hselectionSet⟩

  theorem selectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition} {parentType : Name}
          {selectionSet : List Selection},
          (∀ {fragmentName : Name} {fragment : FragmentDefinition}
              {remaining
                : { remaining : List FragmentDefinition
                    // remaining.length < fragments.length }},
            lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
            -> fragment.selectionSet ≠ []
                ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                    variableDefinitions [] fragment.typeCondition
                    (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions fragments parentType selectionSet
          -> GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions [] parentType
              (Inline.inlineSelectionSet fragments selectionSet)
    | _schema, _variableDefinitions, _fragments, _parentType, [],
        _hfragmentBodies, _hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionSetValid]
    | schema, variableDefinitions, fragments, parentType, selection :: rest,
        hfragmentBodies, hvalid => by
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
        simp [Inline.inlineSelectionSet,
          GraphQL.NamedFragment.Validation.selectionSetValid]
        exact ⟨selectionValid_inlineSelection_of_fragmentBodiesValid
            hfragmentBodies hselectionValid,
          by
            simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
              selectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
                hfragmentBodies hrestValid⟩

  theorem fieldSelectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fragments : List FragmentDefinition}
          {fieldDefinition : FieldDefinition} {selectionSet : List Selection},
          (∀ {fragmentName : Name} {fragment : FragmentDefinition}
              {remaining
                : { remaining : List FragmentDefinition
                    // remaining.length < fragments.length }},
            lookupFragmentAndRestLt? fragmentName fragments = some (fragment, remaining)
            -> fragment.selectionSet ≠ []
                ∧ GraphQL.NamedFragment.Validation.selectionSetValid schema
                    variableDefinitions [] fragment.typeCondition
                    (Inline.inlineSelectionSet remaining.val fragment.selectionSet))
          -> GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
              variableDefinitions fragments fieldDefinition selectionSet
          -> GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
              variableDefinitions [] fieldDefinition
              (Inline.inlineSelectionSet fragments selectionSet)
    | schema, variableDefinitions, fragments, fieldDefinition, selectionSet,
        hfragmentBodies, hvalid => by
        simp [GraphQL.NamedFragment.Validation.fieldSelectionSetValid] at hvalid ⊢
        rcases hvalid with ⟨houtput, hshape⟩
        refine ⟨houtput, ?_⟩
        cases hshape with
        | inl hleaf =>
            rcases hleaf with ⟨hleaf, hselectionSetEmpty⟩
            exact Or.inl ⟨hleaf, by
              simp [hselectionSetEmpty]⟩
        | inr hcomposite =>
            rcases hcomposite with
              ⟨hcompositeType, hnonempty, hselectionSetValid⟩
            exact Or.inr ⟨hcompositeType,
              inlineSelectionSet_nonempty hnonempty,
              selectionSetValid_inlineSelectionSet_of_fragmentBodiesValid
                hfragmentBodies hselectionSetValid⟩
end

mutual
  theorem selectionValid_emptyFragments_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {parentType : Name} {selection : Selection},
          GraphQL.NamedFragment.Validation.selectionValid schema
            variableDefinitions [] parentType selection
          -> selectionInlined selection
    | schema, variableDefinitions, parentType,
        .field responseName fieldName arguments directives selectionSet,
        hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨_hdirectives, _fieldDefinition, _hlookup, _harguments, hfield⟩
        simp [selectionInlined]
        exact fieldSelectionSetValid_emptyFragments_inlined hfield
    | schema, variableDefinitions, parentType,
        .inlineFragment none directives selectionSet, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with ⟨_hdirectives, _hnonempty, hselectionSet⟩
        simp [selectionInlined]
        exact selectionSetValid_emptyFragments_inlined hselectionSet
    | schema, variableDefinitions, parentType,
        .inlineFragment (some typeCondition) directives selectionSet,
        hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid] at hvalid
        rcases hvalid with
          ⟨_hdirectives, _hcomposite, _hoverlap, _hnonempty,
            hselectionSet⟩
        simp [selectionInlined]
        exact selectionSetValid_emptyFragments_inlined hselectionSet
    | _schema, _variableDefinitions, _parentType,
        .fragmentSpread fragmentName directives, hvalid => by
        simp [GraphQL.NamedFragment.Validation.selectionValid,
          GraphQL.NamedFragment.lookupFragment?,
          GraphQL.NamedFragment.lookupFragment?] at hvalid

  theorem selectionSetValid_emptyFragments_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {parentType : Name} {selectionSet : List Selection},
          GraphQL.NamedFragment.Validation.selectionSetValid schema
            variableDefinitions [] parentType selectionSet
          -> selectionSetInlined selectionSet
    | _schema, _variableDefinitions, _parentType, [], _hvalid => by
        simp [selectionSetInlined]
    | schema, variableDefinitions, parentType, selection :: rest, hvalid => by
        have hvalidPair := hvalid
        simp [GraphQL.NamedFragment.Validation.selectionSetValid] at hvalidPair
        have hselectionValid :
            GraphQL.NamedFragment.Validation.selectionValid schema
              variableDefinitions [] parentType selection :=
          hvalidPair.1
        have hrestValid :
            GraphQL.NamedFragment.Validation.selectionSetValid schema
              variableDefinitions [] parentType rest := by
          simpa [GraphQL.NamedFragment.Validation.selectionSetValid] using
            hvalidPair.2
        simp [selectionSetInlined,
          selectionValid_emptyFragments_inlined hselectionValid,
          selectionSetValid_emptyFragments_inlined hrestValid]

  theorem fieldSelectionSetValid_emptyFragments_inlined
      : ∀ {schema : Schema} {variableDefinitions : List VariableDefinition}
          {fieldDefinition : FieldDefinition} {selectionSet : List Selection},
          GraphQL.NamedFragment.Validation.fieldSelectionSetValid schema
            variableDefinitions [] fieldDefinition selectionSet
          -> selectionSetInlined selectionSet
    | schema, variableDefinitions, fieldDefinition, selectionSet, hvalid => by
        simp [GraphQL.NamedFragment.Validation.fieldSelectionSetValid] at hvalid
        rcases hvalid with ⟨_houtput, hshape⟩
        cases hshape with
        | inl hleaf =>
            rcases hleaf with ⟨_hleaf, hselectionSetEmpty⟩
            simp [hselectionSetEmpty, selectionSetInlined]
        | inr hcomposite =>
            rcases hcomposite with
              ⟨_hcomposite, _hnonempty, hselectionSetValid⟩
            exact selectionSetValid_emptyFragments_inlined hselectionSetValid
end

end Semantics
end NamedFragment
end GraphQL
