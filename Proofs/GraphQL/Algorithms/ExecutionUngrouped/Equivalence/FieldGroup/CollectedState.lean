import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup.AppendSteps.Query

/-!
Collected single-group state constructors for field-group equivalence.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance fieldGroupCollectedStateResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

structure ExecutedSingleGroupSelectionState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) where
  groups : List (Name × List ExecutableField)
  responseName : Name
  field : ExecutableField
  fields : List ExecutableField
  collect_eq
    : GraphQL.Execution.collectFields schema variableValues parentType source selectionSet
      = groups
  group_mem : (responseName, field :: fields) ∈ groups
  exact_groups : groups = [(responseName, field :: fields)]
  direct
    : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
        parentType source selectionSet (.object [])
  responses : CollectedGroupsResponseName groups
  parents : CollectedGroupsParent parentType groups
  headLookup
    : ∃ fieldDefinition,
        schema.lookupField parentType field.fieldName = some fieldDefinition
  headChildren
    : ∀ childDepth runtimeType identity,
        childDepth < depth
        -> schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              runtimeType
            = true
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
                  selectionSet := field.selectionSet
                }
              initial := .object []
            }
  appendPlan
    : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolveFieldValueByName schema resolvers variableValues field.parentType
          field.fieldName field.arguments source)
        [] fields

namespace ExecutedSingleGroupSelectionState

def of_collected_appendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    (plan
      : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field
          (resolveFieldValueByName schema resolvers variableValues field.parentType
            field.fieldName field.arguments source)
          [] fields)
    : ExecutedSingleGroupSelectionState schema resolvers variableValues depth
        parentType source selectionSet where
  groups := groups
  responseName := responseName
  field := field
  fields := fields
  collect_eq := hcollect
  group_mem := hgroup
  exact_groups := hexact
  direct := hdirect
  responses :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq
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
      }
      groups hcollect
  parents :=
    ExecutionCollectedFieldInvariant.parent_of_collect_eq
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
      }
      groups hcollect
  headLookup := hfieldLookup
  headChildren := hfieldChildren
  appendPlan := plan

def toExecutedFieldGroup
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedSingleGroupSelectionState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        state.responseName state.field state.fields :=
  ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
    depth parentType source state.groups state.responseName state.field
    state.fields state.group_mem state.responses state.parents
    state.headLookup state.headChildren state.appendPlan

theorem flatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedSingleGroupSelectionState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source (state.field :: state.fields) :=
  state.toExecutedFieldGroup.flatSpecEquivalent

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedSingleGroupSelectionState schema resolvers variableValues depth
          parentType source selectionSet)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source
        [(state.responseName, state.field :: state.fields)] :=
  state.toExecutedFieldGroup.groupFlatSpecEquivalent

theorem executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedSingleGroupSelectionState schema resolvers variableValues depth
          parentType source selectionSet)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_appendPlan schema resolvers
    variableValues depth parentType source selectionSet state.groups
    state.responseName state.field state.fields state.collect_eq
    state.group_mem state.direct state.responses state.parents
    state.headLookup state.headChildren state.appendPlan state.exact_groups

theorem stateEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (state
      : ExecutedSingleGroupSelectionState schema resolvers variableValues depth
          parentType source selectionSet)
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
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source selectionSet
      state.executeRootSelectionSet_eq_spec

theorem executeQueryWithFuel_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (state
      : ExecutedSingleGroupSelectionState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact state.executeRootSelectionSet_eq_spec

theorem executeQuery_eq_spec
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (state
      : ExecutedSingleGroupSelectionState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact state.executeQueryWithFuel_eq_spec hroot

end ExecutedSingleGroupSelectionState

theorem ExecutedFieldAppendStep_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hlaterParent : later.parentType = parentType)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
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
    : ExecutedFieldAppendStep schema resolvers variableValues depth parentType
        source responseName first resolved [] later := by
  refine {
    responseName_eq := hlaterResponse
    parent_eq := hlaterParent
    fieldName_eq := hfieldName
    resolved_eq := hresolveLater
    prefixChildren := ?prefixChildren
    absorbs := ?absorbs
    errorNeutral := ?errorNeutral
    extendedChildren := ?extendedChildren
  }
  · intro childDepth runtimeType identity hlt _hincludes
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hfirstChildren childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hobjects childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt
    simpa [GraphQL.Execution.mergedFieldSelectionSet,
      VisitSubfieldsErrorNeutral] using
      herrors childDepth runtimeType identity hlt
  · intro childDepth runtimeType identity hlt _hincludes
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildren childDepth runtimeType identity hlt

theorem ExecutedFieldAppendPlan_two_of_visit_absorbs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hlaterParent : later.parentType = parentType)
    (hlaterResponse : later.responseName = responseName)
    (hfieldName : later.fieldName = first.fieldName)
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
    : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName first resolved [] [later] :=
  ExecutedFieldAppendPlan.singleton
    (ExecutedFieldAppendStep_two_of_visit_absorbs schema resolvers
      variableValues depth parentType source responseName first later resolved
      hlaterParent hlaterResponse hfieldName hresolveLater hfirstChildren
      hobjects herrors hchildren)

theorem ExecutedFieldAppendStep.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField) (later : ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hlater : later ∈ field :: fields)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (hprefixChildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                (.object []))
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                  (.object []))))
    (herrors
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                (.object [])))
    (hchildren
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet
                        ((field :: prefixTail) ++ [later])
                  }
                initial := .object []
              })
    : ExecutedFieldAppendStep schema resolvers variableValues depth parentType
        source responseName field
        (resolveFieldValueByName schema resolvers variableValues field.parentType
          field.fieldName field.arguments source)
        prefixTail later := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  have hgroupCompatible :
      ExecutableFieldsFieldValidationMergeCompatible (field :: fields) :=
    hcompatible responseName (field :: fields) hgroup
  have hgroupStable :
      ExecutableFieldsResolveStable schema resolvers variableValues source (field :: fields) :=
    hstable responseName (field :: fields) hgroup
  have hfieldResponse : field.responseName = responseName :=
    hgroupResponses field (by simp)
  have hlaterResponse : later.responseName = responseName :=
    hgroupResponses later hlater
  have hlaterParent : later.parentType = parentType :=
    hgroupParents later hlater
  have hsameResponse : field.responseName = later.responseName := by
    rw [hfieldResponse, hlaterResponse]
  have hfieldName : later.fieldName = field.fieldName :=
    (hgroupCompatible field later (by simp) hlater hsameResponse).1.symm
  have hresolveLater :
      resolveFieldValueByName schema resolvers variableValues later.parentType later.fieldName later.arguments source =
      resolveFieldValueByName schema resolvers variableValues field.parentType
        field.fieldName field.arguments source :=
    (hgroupStable field later (by simp) hlater hsameResponse).symm
  refine {
    responseName_eq := hlaterResponse
    parent_eq := hlaterParent
    fieldName_eq := hfieldName
    resolved_eq := hresolveLater
    prefixChildren := hprefixChildren
    absorbs := hobjects
    errorNeutral := herrors
    extendedChildren := hchildren
  }

theorem ExecutedFieldAppendPlan.of_collected_group_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    : ∀ prefixTail remaining,
        ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields prefixTail remaining
        -> ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
            source responseName field
            (resolveFieldValueByName schema resolvers variableValues field.parentType
              field.fieldName field.arguments source)
            prefixTail remaining
  | _prefixTail, [], _hstate => by
      exact ExecutedFieldAppendPlan.nil
  | prefixTail, later :: rest, hstate => by
      rcases hstate with
        ⟨hprefixChildren, hlater, hobjects, herrors, hchildren, hrest⟩
      apply ExecutedFieldAppendPlan.cons
      · exact
          ExecutedFieldAppendStep.of_collected_group schema resolvers
            variableValues depth parentType source groups responseName field
            fields prefixTail later hgroup hlater hresponses hparents
            hcompatible hstable hprefixChildren hobjects herrors hchildren
      · exact
          ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
            variableValues depth parentType source groups responseName field
            fields hgroup hresponses hparents hcompatible hstable
            (prefixTail ++ [later]) rest hrest

theorem ExecutedFieldAppendPlan.of_collected_group_from_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                      (.object []))))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : ∀ prefixTail remaining,
        (∀ later, later ∈ remaining -> later ∈ fields)
        -> ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
            source responseName field
            (resolveFieldValueByName schema resolvers variableValues field.parentType
              field.fieldName field.arguments source)
            prefixTail remaining
  | prefixTail, remaining, hremaining => by
      exact
        ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
          variableValues depth parentType source groups responseName field fields
          hgroup hresponses hparents hcompatible hstable prefixTail remaining
          (ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
            (by
              intro prefixTail childDepth runtimeType identity hlt _hincludes
              exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
            hobjects
            herrors
            (by
              intro prefixTail later hlater childDepth runtimeType identity hlt
                _hincludes
              exact hchildren prefixTail later hlater childDepth runtimeType
                identity hlt)
            prefixTail remaining hremaining)

theorem ExecutedFieldAppendPlan.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                      (.object []))))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field
        (resolveFieldValueByName schema resolvers variableValues field.parentType
          field.fieldName field.arguments source)
        [] fields := by
  apply ExecutedFieldAppendPlan.of_collected_group_from_prefix schema resolvers
    variableValues depth parentType source groups responseName field fields
    hgroup hresponses hparents hcompatible hstable hprefixChildren hobjects
    herrors hchildren
  intro later hlater
  exact hlater

def ExecutedFieldGroup.of_collected_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                      (.object []))))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields := by
  let hstate :
      ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields :=
    ExecutedFieldAppendPlanState.of_all_prefixes
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hobjects
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt)
  exact
    ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
      depth parentType source groups responseName field fields hgroup hresponses
      hparents hfieldLookup
      (by
        intro childDepth runtimeType identity hlt
        simpa [GraphQL.Execution.mergedFieldSelectionSet] using
          ExecutedFieldAppendPlanState.prefixChildren hstate childDepth
            runtimeType identity hlt)
      (ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
        variableValues depth parentType source groups responseName field fields
        hgroup hresponses hparents hcompatible hstable [] fields hstate)

def ExecutedFieldGroup.of_collected_group_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable schema resolvers variableValues source groups)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hstate
      : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields [] fields)
    : ExecutedFieldGroup schema resolvers variableValues depth parentType source
        responseName field fields :=
  ExecutedFieldGroup.of_collected_appendPlan schema resolvers variableValues
    depth parentType source groups responseName field fields hgroup hresponses
    hparents hfieldLookup
    (by
      intro childDepth runtimeType identity hlt
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        ExecutedFieldAppendPlanState.prefixChildren hstate childDepth
          runtimeType identity hlt)
    (ExecutedFieldAppendPlan.of_collected_group_state schema resolvers
      variableValues depth parentType source groups responseName field fields
      hgroup hresponses hparents hcompatible hstable [] fields hstate)

theorem stateEquivalent_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                      (.object []))))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
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
  apply stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_group schema resolvers variableValues
        depth parentType source [(responseName, field :: fields)] responseName
      field fields hgroup hresponses hparents hcompatible hstable
      hfieldLookup hprefixChildren hobjects herrors hchildren)

theorem stateEquivalent_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hplanState
      : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields [] fields)
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
  apply stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues (depth + 1) parentType source selectionSet
  rw [hexact] at hcollect hgroup hresponses hparents hcompatible hstable
  exact
    executeRootSelectionSet_eq_spec_of_executedFieldGroup schema resolvers
      variableValues depth parentType source selectionSet responseName field
      fields hcollect hdirect
      (ExecutedFieldGroup.of_collected_group_state schema resolvers
        variableValues depth parentType source [(responseName, field :: fields)]
        responseName field fields hgroup hresponses hparents hcompatible
        hstable hfieldLookup hplanState)

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hplanState
      : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields [] fields)
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
    (stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers variableValues depth parentType source selectionSet groups
      responseName field fields hcollect hgroup hexact hdirect hinvariant
      hcompatible hfieldLookup hplanState)

theorem executeQueryWithFuel_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hplanState
      : ExecutedFieldAppendPlanState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth field fields [] fields)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_field_group_state_of_invariant schema
      resolvers (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet groups responseName field fields hcollect hgroup
      hexact hdirect hinvariant hcompatible hfieldLookup hplanState

theorem executeQuery_eq_spec_of_collected_field_group_state_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hplanState
      : ExecutedFieldAppendPlanState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth field fields [] fields)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_collected_field_group_state_of_invariant
      schema resolvers variableValues operation depth source groups responseName
      field fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hplanState

theorem stateEquivalent_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hsteps
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
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
        } :=
  stateEquivalent_of_collected_field_group_state_of_invariant schema
    resolvers variableValues depth parentType source selectionSet groups
    responseName field fields hcollect hgroup hexact hdirect hinvariant
    hcompatible hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hsteps
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_collected_field_group_state_of_invariant
    schema resolvers variableValues depth parentType source selectionSet groups
    responseName field fields hcollect hgroup hexact hdirect hinvariant
    hcompatible hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeQueryWithFuel_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hsteps
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsAbsorbsFrom schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source :=
  executeQueryWithFuel_eq_spec_of_collected_field_group_state_of_invariant
    schema resolvers variableValues operation depth source groups responseName
    field fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
    hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeQuery_eq_spec_of_collected_field_group_steps_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hsteps
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsAbsorbsFrom schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation source :=
  executeQuery_eq_spec_of_collected_field_group_state_of_invariant schema
    resolvers variableValues operation depth source groups responseName field
    fields hdepth hroot hcollect hgroup hexact hdirect hinvariant hcompatible
    hfieldLookup
    (ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
      (by
        intro prefixTail childDepth runtimeType identity hlt _hincludes
        exact hprefixChildren prefixTail childDepth runtimeType identity hlt)
      hsteps
      herrors
      (by
        intro prefixTail later hlater childDepth runtimeType identity hlt
          _hincludes
        exact hchildren prefixTail later hlater childDepth runtimeType identity
          hlt))

theorem executeRootSelectionSet_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers variableValues childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                      (.object []))))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
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
    (stateEquivalent_of_collected_field_group_of_invariant schema resolvers
      variableValues depth parentType source selectionSet groups responseName
      field fields hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hprefixChildren hobjects herrors hchildren)

theorem executeQueryWithFuel_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers
                      (GraphQL.Execution.coerceVariableValues operation variableValues)
                      childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                      (.object []))))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    stateEquivalent_of_collected_field_group_of_invariant schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues) depth
      (operation.rootType schema) source operation.selectionSet
      groups responseName field fields hcollect hgroup hexact hdirect
      hinvariant hcompatible hfieldLookup hprefixChildren hobjects herrors
      hchildren

theorem executeQuery_eq_spec_of_collected_field_group_of_invariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hdepth : GraphQL.Execution.executeQueryFuelBound schema operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hexact : groups = [(responseName, field :: fields)])
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
          schema.lookupField (operation.rootType schema) field.fieldName
          = some fieldDefinition)
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
                    selectionSet :=
                      GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)
                  }
                initial := .object []
              })
    (hobjects
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ResponseAbsorbs
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object []))
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity) later.selectionSet
                    (visitSubfields schema resolvers
                      (GraphQL.Execution.coerceVariableValues operation variableValues)
                      childDepth
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                      (.object []))))
    (herrors
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers
                    (GraphQL.Execution.coerceVariableValues operation variableValues)
                    childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    (hchildren
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
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
                        selectionSet :=
                          GraphQL.Execution.mergedFieldSelectionSet
                            ((field :: prefixTail) ++ [later])
                      }
                    initial := .object []
                  })
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_collected_field_group_of_invariant schema
      resolvers variableValues operation depth source groups responseName field
      fields hroot hcollect hgroup hexact hdirect hinvariant hcompatible
      hfieldLookup hprefixChildren hobjects herrors hchildren

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
