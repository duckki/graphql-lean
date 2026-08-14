import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup.CollectedState

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

def ExecutedSingleGroupSelectionState.of_collected_two_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet := by
  let state : ExecutionEquivalenceState ObjectIdentity :=
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := parentType
        source := source
        selectionSet := selectionSet }
      initial := .object [] }
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
        hinvariant hcollect
  have hgroupResponses :
      ExecutableFieldsResponseName responseName [first, later] :=
    hresponses responseName [first, later] hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType [first, later] :=
    hparents responseName [first, later] hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible [first, later] :=
    hcompatible responseName [first, later] hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable schema resolvers variableValues source [first, later] :=
    hstable responseName [first, later] hgroup
  have hfirstResponse : first.responseName = responseName :=
    hgroupResponses first (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later (by simp)
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later (by simp)
  have hsameResponse : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  have hfieldName : later.fieldName = first.fieldName :=
    (hgroupCompatible first later (by simp) (by simp) hsameResponse).1.symm
  have hresolveLater :
      resolveFieldValueByName schema resolvers variableValues later.parentType later.fieldName later.arguments source =
      resolveFieldValueByName schema resolvers variableValues first.parentType first.fieldName first.arguments source :=
    (hgroupStable first later (by simp) (by simp) hsameResponse).symm
  apply ExecutedSingleGroupSelectionState.of_collected_appendPlan schema
    resolvers variableValues depth parentType source selectionSet groups
    responseName first [later] hcollect hgroup hexact hdirect
    hfieldLookup
    (by
      intro childDepth runtimeType identity hlt _hincludes
      exact hfirstChildren childDepth runtimeType identity hlt)
  exact
    ExecutedFieldAppendPlan_two_of_visit_absorbs schema resolvers
      variableValues depth parentType source responseName first later
      (resolveFieldValueByName schema resolvers variableValues first.parentType first.fieldName first.arguments source)
      hlaterParent hlaterResponse hfieldName hresolveLater hfirstChildren
      hobjects herrors hchildren

theorem stateEquivalent_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth + 1
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } := by
  have hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (first :: []) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hfirstChildren childDepth runtimeType identity hlt
  have hobjectsMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
                (.object []))) := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hobjects childDepth runtimeType identity hlt
  have herrorsMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object [])) := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet,
      VisitSubfieldsErrorNeutral] using
      herrors childDepth runtimeType identity hlt
  have hchildrenMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((first :: []) ++ [later]) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildren childDepth runtimeType identity hlt
  exact
    stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName first [later] hcollect hgroup hexact hdirect hinvariant
      hcompatible hfieldLookup
      (ExecutedFieldAppendPlanState.singleton
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hprefixChildren childDepth runtimeType identity hlt)
        (by simp)
        hobjectsMerged
        herrorsMerged
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hchildrenMerged childDepth runtimeType identity hlt))

theorem stateEquivalent_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjectSteps
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth + 1
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } := by
  have hprefixChildren :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet (first :: []) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hfirstChildren childDepth runtimeType identity hlt
  have hstepsMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity)
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object []))
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object [])) := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hobjectSteps childDepth runtimeType identity hlt
  have herrorsMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (first :: []))
              (.object [])) := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet,
      VisitSubfieldsErrorNeutral] using
      herrors childDepth runtimeType identity hlt
  have hchildrenMerged :
      ∀ childDepth runtimeType identity,
        childDepth < depth ->
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := childDepth
                parentType := runtimeType
                source := .object runtimeType identity
                selectionSet :=
                  GraphQL.Execution.mergedFieldSelectionSet
                    ((first :: []) ++ [later]) }
              initial := .object [] } := by
    intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildren childDepth runtimeType identity hlt
  exact
    stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName first [later] hcollect hgroup hexact hdirect hinvariant
      hcompatible hfieldLookup
      (ExecutedFieldAppendPlanState.singleton_of_visit_absorbs
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hprefixChildren childDepth runtimeType identity hlt)
        (by simp) hstepsMerged herrorsMerged
        (by
          intro childDepth runtimeType identity hlt _hincludes
          exact hchildrenMerged childDepth runtimeType identity hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjectSteps
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    {
      schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet := selectionSet
    }
    (stateEquivalent_of_collected_two_field_group_invariant_steps schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName first later hcollect hgroup hexact hdirect hinvariant
      hcompatible hfieldLookup hfirstChildren hobjectSteps herrors hchildren)

theorem executeQueryWithFuel_eq_spec_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) first.fieldName
          = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjectSteps
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsAbsorbsFrom schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_two_field_group_invariant_steps schema
      resolvers (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet groups responseName first later hcollect hgroup
      hexact hdirect hinvariant hcompatible hfieldLookup hfirstChildren hobjectSteps
      herrors hchildren

theorem executeQuery_eq_spec_of_collected_two_field_group_invariant_steps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) first.fieldName
          = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjectSteps
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsAbsorbsFrom schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_collected_two_field_group_invariant_steps
      schema resolvers variableValues operation depth source groups
      responseName first later hroot hcollect hgroup hexact hdirect hinvariant
      hcompatible hfieldLookup hfirstChildren hobjectSteps herrors hchildren

theorem executeRootSelectionSet_eq_spec_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    {
      schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth + 1
      parentType := parentType
      source := source
      selectionSet := selectionSet
    }
    (stateEquivalent_of_collected_two_field_group_invariant schema resolvers
      variableValues depth parentType source selectionSet groups responseName
      first later hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hfirstChildren hobjects herrors hchildren)

theorem executeQueryWithFuel_eq_spec_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) first.fieldName
          = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_two_field_group_invariant schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues) depth
      (operation.rootType schema) source operation.selectionSet
      groups responseName first later hcollect hgroup hexact hdirect hinvariant
      hcompatible hfieldLookup hfirstChildren hobjects herrors hchildren

theorem executeQuery_eq_spec_of_collected_two_field_group_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hinvariant
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) first.fieldName
          = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_collected_two_field_group_invariant schema
      resolvers variableValues operation depth source groups responseName first
      later hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hfirstChildren hobjects herrors hchildren

def ExecutedFieldGroup.two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveFirst
      : resolveFieldValueByName schema resolvers variableValues first.parentType
          first.fieldName first.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hresolveLater
      : resolveFieldValueByName schema resolvers variableValues later.parentType
          later.fieldName later.arguments source
        = resolved)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName first [later] :=
  ExecutedFieldGroup.of_appendPlan schema resolvers variableValues depth
    parentType source responseName first [later] resolved
    (by
      intro candidate hmem
      simp at hmem
      rcases hmem with rfl | hmem
      · exact hfirstResponse
      · rcases hmem with rfl | hfalse
        · exact hlaterResponse)
    (by
      intro candidate hmem
      simp at hmem
      rcases hmem with rfl | hmem
      · exact hfirstParent
      · rcases hmem with rfl | hfalse
        · exact hlaterParent)
    hresolveFirst hfieldLookup
    (by
      intro childDepth runtimeType identity hlt _hincludes
      exact hfirstChildren childDepth runtimeType identity hlt)
    (ExecutedFieldAppendPlan_two_of_visit_absorbs schema resolvers
      variableValues depth parentType source responseName first later resolved
      hlaterParent hlaterResponse hfieldName hresolveLater hfirstChildren
      hobjects herrors hchildren)

def ExecutedFieldGroup.collected_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName first [later] := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName [first, later] :=
    hresponses responseName [first, later] hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType [first, later] :=
    hparents responseName [first, later] hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible [first, later] :=
    hcompatible responseName [first, later] hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable schema resolvers variableValues source [first, later] :=
    hstable responseName [first, later] hgroup
  have hfirstResponse : first.responseName = responseName :=
    hgroupResponses first (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later (by simp)
  have hfirstParent : first.parentType = parentType :=
    hgroupParents first (by simp)
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later (by simp)
  have hsameResponse : first.responseName = later.responseName := by
    rw [hfirstResponse, hlaterResponse]
  have hfieldName : later.fieldName = first.fieldName :=
    (hgroupCompatible first later (by simp) (by simp) hsameResponse).1.symm
  have hresolveLater :
      resolveFieldValueByName schema resolvers variableValues later.parentType later.fieldName later.arguments source =
      resolveFieldValueByName schema resolvers variableValues first.parentType first.fieldName first.arguments source :=
    (hgroupStable first later (by simp) (by simp) hsameResponse).symm
  exact
    ExecutedFieldGroup.two_of_visit_absorbs schema resolvers variableValues
      depth parentType source responseName first later
      (resolveFieldValueByName schema resolvers variableValues first.parentType first.fieldName first.arguments source)
      hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName rfl
      hfieldLookup hresolveLater hfirstChildren hobjects herrors hchildren

theorem executeRootSelectionSet_eq_spec_of_exact_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (first later : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hfirstParent : first.parentType = parentType)
    (hlaterParent : later.parentType = parentType)
    (hfirstResponse : first.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
    (hresolveLater
      : resolveFieldValueByName schema resolvers variableValues later.parentType
          later.fieldName later.arguments source
        = resolveFieldValueByName schema resolvers variableValues first.parentType
            first.fieldName first.arguments source)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName first
      [later] hcollect hdirect
      (ExecutedFieldGroup.two_of_visit_absorbs schema resolvers variableValues
        depth parentType source responseName first later
        (resolveFieldValueByName schema resolvers variableValues first.parentType first.fieldName first.arguments source)
        hfirstParent hlaterParent hfirstResponse hlaterResponse hfieldName rfl
        hfieldLookup hresolveLater hfirstChildren hobjects herrors hchildren)

theorem executeRootSelectionSet_eq_spec_of_collected_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType first.fieldName = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName first
      [later] hcollect hdirect
      (ExecutedFieldGroup.collected_two_of_visit_absorbs schema resolvers
        variableValues depth parentType source [(responseName, [first, later])]
        responseName first later hgroup hresponses hparents hcompatible hstable
        hfieldLookup hfirstChildren hobjects herrors hchildren)

theorem executeQueryWithFuel_eq_spec_of_collected_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable
      : CollectedGroupsResolveStable schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) source
          groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) first.fieldName
          = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_collected_two_field_group_appendPlan
      schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues) depth
      (operation.rootType schema) source
      operation.selectionSet groups responseName first later hcollect hgroup
      hexact hdirect hresponses hparents hcompatible hstable hfieldLookup
      hfirstChildren hobjects herrors hchildren

theorem executeQuery_eq_spec_of_collected_two_field_group_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (first later : ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, [first, later]) ∈ groups)
    (hexact : groups = [(responseName, [first, later])])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable
      : CollectedGroupsResolveStable schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) source
          groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField (operation.rootType schema) first.fieldName
          = some fieldDefinition)
    (hfirstChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object []))
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth
                  runtimeType (.object runtimeType identity) first.selectionSet
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers
                (GraphQL.Execution.coerceVariableValues operation variableValues)
                childDepth
                runtimeType (.object runtimeType identity) first.selectionSet
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues :=
                      GraphQL.Execution.coerceVariableValues operation variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := first.selectionSet ++ later.selectionSet
                  }
                initial := .object []
              })
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_collected_two_field_group_appendPlan schema
      resolvers variableValues operation depth source groups responseName first
      later hroot hcollect hgroup hexact hdirect hresponses hparents
      hcompatible hstable hfieldLookup hfirstChildren hobjects herrors
      hchildren

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
