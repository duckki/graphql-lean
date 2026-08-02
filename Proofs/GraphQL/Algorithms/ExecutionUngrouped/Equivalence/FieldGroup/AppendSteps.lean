import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.FieldGroup.PrefixAppend

/-!
Append-step and append-plan machinery for field-group equivalence.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance fieldGroupAppendStepsResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

def ExecutableFieldsMergedCompleteAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    : List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      later.responseName = responseName
      ∧ later.parentType = parentType
      ∧ later.fieldName = field.fieldName
      ∧ resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved
      ∧ (∀ childDepth runtimeType identity,
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
      ∧ (∀ childDepth runtimeType identity,
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
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                (.object [])))
      ∧ (∀ childDepth runtimeType identity,
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
      ∧ ExecutableFieldsMergedCompleteAppendSteps schema resolvers
          variableValues depth parentType source responseName field resolved
          (prefixTail ++ [later]) rest

def ExecutableFieldsMergedCompleteContainedAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    : List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      later.responseName = responseName
      ∧ later.parentType = parentType
      ∧ later.fieldName = field.fieldName
      ∧ resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
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
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
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
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                (.object [])))
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
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
      ∧ ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
          variableValues depth parentType source responseName field resolved
          (prefixTail ++ [later]) rest

def ExecutableFieldsMergedAlignedAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    : List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      later.responseName = responseName
      ∧ later.parentType = parentType
      ∧ later.fieldName = field.fieldName
      ∧ resolvers.resolve later.parentType later.fieldName later.arguments source
        = resolved
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))))
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> ResponseAbsorbs
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                (.object [])).fst
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                  (.object [])).fst).fst)
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: prefixTail) ++ [later])))
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet
                  ((field :: prefixTail) ++ [later]))))
      ∧ ExecutableFieldsMergedAlignedAppendSteps schema resolvers variableValues
          depth parentType source responseName field resolved
          (prefixTail ++ [later]) rest

theorem ExecutableFieldsMergedVisitAligned_of_alignedAppendSteps_from_prefix_positive
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hfieldResponse : field.responseName = responseName)
    (hfieldParent : field.parentType = parentType)
    (hresolveFirst
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    : ∀ prefixTail remaining,
        GroupedFieldVisitAlignedEquivalent responseName
          (visitSubfields schema resolvers variableValues (completionDepth + 2)
            parentType source (executableFieldSelections (field :: prefixTail))
            (.object []))
          (GraphQL.Execution.executeField schema resolvers variableValues
            (completionDepth + 2) source responseName (field :: prefixTail))
        -> ExecutableFieldsMergedAlignedAppendSteps schema resolvers variableValues
            (completionDepth + 1) parentType source responseName field resolved
            prefixTail remaining
        -> (∀ candidate,
              candidate ∈ field :: prefixTail -> candidate.responseName = responseName)
        -> (∀ candidate,
              candidate ∈ prefixTail
              -> ∃ fieldDefinition,
                  schema.lookupField parentType candidate.fieldName
                  = some fieldDefinition)
        -> GroupedFieldVisitAlignedEquivalent responseName
            (visitSubfields schema resolvers variableValues (completionDepth + 2)
              parentType source
              (executableFieldSelections (field :: (prefixTail ++ remaining)))
              (.object []))
            (GraphQL.Execution.executeField schema resolvers variableValues
              (completionDepth + 2) source responseName
              (field :: (prefixTail ++ remaining)))
  | prefixTail, [], hprefixAligned, _hsteps, _hresponses, _hlookups => by
      simpa using hprefixAligned
  | prefixTail, later :: rest, hprefixAligned, hsteps, hresponses,
      hlookups => by
      simp [ExecutableFieldsMergedAlignedAppendSteps] at hsteps
      rcases hsteps with
        ⟨hlaterResponse, hlaterParent, hfieldName, hresolveLater,
          hprefixChildren, hobjects, hchildren, hrest⟩
      have htailLookups :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            ∃ fieldDefinition, schema.lookupField parentType
              candidate.fieldName = some fieldDefinition := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hprefixMem | hlater
        · exact hlookups candidate hprefixMem
        · subst candidate
          rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
          exact ⟨fieldDefinition, by simpa [hfieldName] using hlookup⟩
      have hnextResponses :
          ∀ candidate, candidate ∈ field :: (prefixTail ++ [later]) ->
            candidate.responseName = responseName := by
        intro candidate hmem
        simp at hmem
        rcases hmem with hhead | htail
        · subst candidate
          exact hfieldResponse
        · rcases htail with hprefixTail | hlater
          · exact hresponses candidate (by simp [hprefixTail])
          · subst candidate
            exact hlaterResponse
      have hnextAligned :
          GroupedFieldVisitAlignedEquivalent responseName
            (visitSubfields schema resolvers variableValues
              (completionDepth + 2) parentType source
              (executableFieldSelections
                (field :: (prefixTail ++ [later])))
              (.object []))
            (GraphQL.Execution.executeField schema resolvers variableValues
              (completionDepth + 2) source responseName
              (field :: (prefixTail ++ [later]))) :=
        ExecutableFieldsMergedVisit_append_one_visit_aligned_of_prefix_contained_positive_of_aligned_children
          schema resolvers variableValues completionDepth parentType source
          responseName field prefixTail later resolved hprefixAligned hresponses
          hfieldResponse hlaterResponse hfieldParent hlaterParent hfieldName
          htailLookups hresolveFirst hresolveLater hprefixChildren hobjects
          hchildren
      have htail :=
        ExecutableFieldsMergedVisitAligned_of_alignedAppendSteps_from_prefix_positive
          schema resolvers variableValues completionDepth parentType source
          responseName field resolved hfieldResponse hfieldParent hresolveFirst
          hfieldLookup (prefixTail ++ [later]) rest hnextAligned hrest
          hnextResponses htailLookups
      simpa [List.append_assoc] using htail

theorem
    ExecutableFieldsFlatSpecAlignedEquivalent_nonempty_group_of_alignedAppendSteps_positive
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ childDepth runtimeType identity,
          childDepth < completionDepth + 1
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) field.selectionSet)
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                field.selectionSet))
    (hsteps
      : ExecutableFieldsMergedAlignedAppendSteps schema resolvers variableValues
          (completionDepth + 1) parentType source responseName field resolved []
          fields)
    : ExecutableFieldsFlatSpecAlignedEquivalent schema resolvers variableValues
        (completionDepth + 2) parentType source (field :: fields) := by
  have hfieldResponse : field.responseName = responseName :=
    hresponse field (by simp)
  have hfieldParent : field.parentType = parentType :=
    hparent field (by simp)
  have hbase :
      GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source (executableFieldSelections [field]) (.object []))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (completionDepth + 2) source responseName [field]) :=
    visitSubfields_executableFieldSelections_single_aligned_of_contained_child_states
      schema resolvers variableValues (completionDepth + 1) parentType source
      responseName field resolved hfieldResponse hfieldParent hresolve
      hfieldChildren
  have hgroup :
      GroupedFieldVisitAlignedEquivalent responseName
        (visitSubfields schema resolvers variableValues (completionDepth + 2)
          parentType source
          (executableFieldSelections (field :: ([] ++ fields)))
          (.object []))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (completionDepth + 2) source responseName
          (field :: ([] ++ fields))) :=
    ExecutableFieldsMergedVisitAligned_of_alignedAppendSteps_from_prefix_positive
      schema resolvers variableValues completionDepth parentType source
      responseName field resolved hfieldResponse hfieldParent hresolve
      hfieldLookup [] fields hbase hsteps
      (by
        intro candidate hmem
        simp at hmem
        subst candidate
        exact hfieldResponse)
      (by
        intro candidate hmem
        simp at hmem)
  have hrootAligned :
      RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections (field :: fields)))
        (GraphQL.Execution.executeField schema resolvers variableValues
          (completionDepth + 2) source responseName (field :: fields)) := by
    unfold executeRootSelectionSet
    exact GroupedFieldVisitAlignedEquivalent.to_rootSelectionResult responseName
      (by simpa using hgroup)
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 2) parentType source
          (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (completionDepth + 2) source [(responseName, field :: fields)] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (completionDepth + 2) parentType source
      responseName field fields hresponse hparent
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (completionDepth + 2) source [(responseName, field :: fields)] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (completionDepth + 2) source responseName (field :: fields) := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (completionDepth + 2) source responseName (field :: fields) <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  unfold ExecutableFieldsFlatSpecAlignedEquivalent
  exact
    RootSelectionResultAlignedEquivalent.trans hrootAligned
      (RootSelectionResultAlignedEquivalent.of_eq
        (hspecRoot.trans hspecField).symm)

structure ExecutedFieldAppendStep
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (prefixTail : List ExecutableField) (later : ExecutableField) where
  responseName_eq : later.responseName = responseName
  parent_eq : later.parentType = parentType
  fieldName_eq : later.fieldName = field.fieldName
  resolved_eq
    : resolvers.resolve later.parentType later.fieldName later.arguments source = resolved
  prefixChildren
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
            }
  absorbs
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
                (.object [])))
  errorNeutral
    : ∀ childDepth runtimeType identity,
        childDepth < depth
        -> VisitSubfieldsErrorNeutral schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
              (.object []))
  extendedChildren
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
            }

def ExecutedFieldAppendPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    : List ExecutableField -> List ExecutableField -> Prop
  | _prefixTail, [] => True
  | prefixTail, later :: rest =>
      ExecutedFieldAppendStep schema resolvers variableValues depth
        parentType source responseName field resolved prefixTail later
      ∧ ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field resolved (prefixTail ++ [later]) rest

def ExecutedFieldAppendPlanState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (field : ExecutableField) (fields : List ExecutableField)
    : List ExecutableField -> List ExecutableField -> Prop
  | prefixTail, [] =>
      ∀ childDepth runtimeType identity,
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
            }
  | prefixTail, later :: rest =>
      (∀ childDepth runtimeType identity,
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
      ∧ later ∈ field :: fields
      ∧ (∀ childDepth runtimeType identity,
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
      ∧ (∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                (.object [])))
      ∧ (∀ childDepth runtimeType identity,
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
      ∧ ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields (prefixTail ++ [later]) rest

theorem ExecutedFieldAppendPlanState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields prefixTail : List ExecutableField}
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
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail [] :=
  hprefixChildren

theorem ExecutedFieldAppendPlanState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail rest : List ExecutableField}
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
    (hlater : later ∈ field :: fields)
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
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
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
    (hrest
      : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields (prefixTail ++ [later]) rest)
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail (later :: rest) :=
  ⟨hprefixChildren, hlater, hobjects, herrors, hchildren, hrest⟩

theorem ExecutedFieldAppendPlanState.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail : List ExecutableField}
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
    (hlater : later ∈ field :: fields)
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
          -> VisitSubfieldsErrorNeutral schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet
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
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail [later] := by
  refine ⟨hprefixChildren, hlater, hobjects, herrors, hchildren, ?_⟩
  intro childDepth runtimeType identity hlt hincludes
  simpa using hchildren childDepth runtimeType identity hlt hincludes

theorem ExecutedFieldAppendPlanState.cons_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail rest : List ExecutableField}
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
    (hlater : later ∈ field :: fields)
    (hsteps
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
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
    (hrest
      : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
          fields (prefixTail ++ [later]) rest)
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail (later :: rest) := by
  apply ExecutedFieldAppendPlanState.cons hprefixChildren hlater
  · intro childDepth runtimeType identity hlt
    exact visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity)
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object []))
      later.selectionSet
      (visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object []))
      (hsteps childDepth runtimeType identity hlt)
  · exact herrors
  · exact hchildren
  · exact hrest

theorem ExecutedFieldAppendPlanState.singleton_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field later : ExecutableField}
    {fields prefixTail : List ExecutableField}
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
    (hlater : later ∈ field :: fields)
    (hsteps
      : ∀ childDepth runtimeType identity,
          childDepth < depth
          -> VisitSubfieldsAbsorbsFrom schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
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
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail [later] := by
  apply ExecutedFieldAppendPlanState.cons_of_visit_absorbs hprefixChildren
    hlater hsteps herrors hchildren
  intro childDepth runtimeType identity hlt hincludes
  simpa using hchildren childDepth runtimeType identity hlt hincludes

theorem ExecutedFieldAppendPlanState.prefixChildren
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField}
    {fields prefixTail remaining : List ExecutableField}
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail remaining
      -> ∀ childDepth runtimeType identity,
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
              } := by
  cases remaining with
  | nil =>
      intro hstate
      exact hstate
  | cons later rest =>
      intro hstate
      exact hstate.1

theorem ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
    : ∀ prefixTail remaining,
        (∀ later, later ∈ remaining -> later ∈ fields)
        -> ExecutedFieldAppendPlanState schema resolvers variableValues depth field
            fields prefixTail remaining
  | prefixTail, [], _hremaining => by
      exact ExecutedFieldAppendPlanState.nil (hprefixChildren prefixTail)
  | prefixTail, later :: rest, hremaining => by
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons (hprefixChildren prefixTail)
      · exact List.mem_cons_of_mem field hlaterFields
      · exact hobjects prefixTail later hlaterFields
      · exact herrors prefixTail later hlaterFields
      · exact hchildren prefixTail later hlaterFields
      · apply ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
          hprefixChildren hobjects herrors hchildren
          (prefixTail ++ [later]) rest
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])

theorem ExecutedFieldAppendPlanState.of_all_prefixes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields := by
  apply ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix
    hprefixChildren hobjects herrors hchildren
  intro later hlater
  exact hlater

theorem ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
    : ∀ prefixTail remaining,
        (∀ later, later ∈ remaining -> later ∈ fields)
        -> ExecutedFieldAppendPlanState schema resolvers variableValues depth field
            fields prefixTail remaining
  | prefixTail, [], _hremaining => by
      exact ExecutedFieldAppendPlanState.nil (hprefixChildren prefixTail)
  | prefixTail, later :: rest, hremaining => by
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons_of_visit_absorbs
        (hprefixChildren prefixTail)
      · exact List.mem_cons_of_mem field hlaterFields
      · exact hsteps prefixTail later hlaterFields
      · exact herrors prefixTail later hlaterFields
      · exact hchildren prefixTail later hlaterFields
      · apply
          ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
            hprefixChildren hsteps herrors hchildren
            (prefixTail ++ [later]) rest
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])

theorem ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields := by
  apply
    ExecutedFieldAppendPlanState.of_all_prefixes_from_prefix_of_visit_absorbs
      hprefixChildren hsteps herrors hchildren
  intro later hlater
  exact hlater

theorem ExecutedFieldAppendPlanState.of_all_prefixes_of_local_absorbs
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {field : ExecutableField} {fields : List ExecutableField}
    (hprefixChildren
      : ∀ prefixTail childDepth runtimeType identity,
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
    (hlocal
      : ∀ prefixTail later,
          later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
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
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields := by
  apply ExecutedFieldAppendPlanState.of_all_prefixes_of_visit_absorbs
    hprefixChildren
  · intro prefixTail later hlater childDepth runtimeType identity hlt
    let base :=
      visitSubfields schema resolvers variableValues childDepth runtimeType
        (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        (.object [])
    have hbaseReady : ResponseMergeReady base := by
      exact visitSubfields_response_ready schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity)
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) []
        ResponseMergeReady_empty_object
    have hbaseAbsorbs : ResponseAbsorbs base base :=
      ResponseAbsorbs_refl_of_ready base hbaseReady
    exact
      visitSubfields_absorbs_from_local_steps schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) base
        later.selectionSet base hbaseReady hbaseAbsorbs
        (hlocal prefixTail later hlater childDepth runtimeType identity hlt)
  · exact herrors
  · exact hchildren

theorem ExecutedFieldAppendPlan.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Option (ResolverValue ObjectIdentity)}
    {prefixTail : List ExecutableField} {later : ExecutableField}
    (step
      : ExecutedFieldAppendStep schema resolvers variableValues depth parentType
          source responseName field resolved prefixTail later)
    : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail [later] := by
  exact ⟨step, by simp [ExecutedFieldAppendPlan]⟩

theorem ExecutedFieldAppendPlan.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Option (ResolverValue ObjectIdentity)}
    {prefixTail : List ExecutableField}
    : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail [] := by
  simp [ExecutedFieldAppendPlan]

theorem ExecutedFieldAppendPlan.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {resolved : Option (ResolverValue ObjectIdentity)}
    {prefixTail : List ExecutableField} {later : ExecutableField}
    {rest : List ExecutableField}
    (step
      : ExecutedFieldAppendStep schema resolvers variableValues depth parentType
          source responseName field resolved prefixTail later)
    (restPlan
      : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field resolved (prefixTail ++ [later]) rest)
    : ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
        source responseName field resolved prefixTail (later :: rest) :=
  ⟨step, restPlan⟩

theorem ExecutedFieldAppendPlan.toAppendSteps
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    : ∀ prefixTail rest,
        ExecutedFieldAppendPlan schema resolvers variableValues depth parentType
          source responseName field resolved prefixTail rest
        -> ExecutableFieldsMergedCompleteAppendSteps schema resolvers variableValues
            depth parentType source responseName field resolved prefixTail rest
  | _prefixTail, [], _plan => by
      simp [ExecutableFieldsMergedCompleteAppendSteps]
  | prefixTail, later :: rest, plan => by
      rcases plan with ⟨step, restPlan⟩
      simp [ExecutableFieldsMergedCompleteAppendSteps]
      exact
        ⟨step.responseName_eq, step.parent_eq, step.fieldName_eq,
          step.resolved_eq, step.prefixChildren, step.absorbs,
          step.errorNeutral, step.extendedChildren,
          ExecutedFieldAppendPlan.toAppendSteps schema resolvers
            variableValues depth parentType source responseName field resolved
            (prefixTail ++ [later]) rest restPlan⟩

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
