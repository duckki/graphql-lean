import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList

/-!
Append-invariant and aligned group-list assembly helpers.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance groupListAppendInvariantResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem CollectedGroupsFieldValidationMergeCompatible_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    : CollectedGroupsFieldValidationMergeCompatible (group :: groups)
      -> CollectedGroupsFieldValidationMergeCompatible groups := by
  intro hcompatible responseName fields hmem
  exact hcompatible responseName fields (by simp [hmem])

structure FieldGroupAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    : Prop where
  childEquivalent
    : ∀ selectionSet childDepth runtimeType identity,
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
                  selectionSet := selectionSet
                }
              initial := .object []
            }
  absorbs
    : ∀ (prefixFields : List ExecutableField) (later : ExecutableField)
          childDepth runtimeType identity,
        childDepth < depth
        -> ResponseAbsorbs
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) later.selectionSet
              (visitSubfields schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity)
                (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
                (.object [])))
  errorNeutral
    : ∀ (prefixFields : List ExecutableField) (later : ExecutableField)
          childDepth runtimeType identity,
        childDepth < depth
        -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
            runtimeType (.object runtimeType identity) later.selectionSet
            (visitSubfields schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity)
              (GraphQL.Execution.mergedFieldSelectionSet prefixFields)
              (.object []))

theorem FieldGroupAppendInvariant.depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    : FieldGroupAppendInvariant schema resolvers variableValues 0 :=
  { childEquivalent := by
      intro _selectionSet childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    absorbs := by
      intro _prefixFields _later childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    errorNeutral := by
      intro _prefixFields _later childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt) }

theorem ExecutedFieldAppendPlanState.of_appendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    (hinvariant : FieldGroupAppendInvariant schema resolvers variableValues depth)
    (field : ExecutableField) (fields : List ExecutableField)
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields :=
  ExecutedFieldAppendPlanState.of_all_prefixes (by
      intro prefixTail childDepth runtimeType identity hlt _hincludes
      exact hinvariant.childEquivalent
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
        childDepth runtimeType identity hlt) (by
      intro prefixTail later _hlater childDepth runtimeType identity hlt
      exact hinvariant.absorbs (field :: prefixTail) later childDepth
        runtimeType identity hlt) (by
      intro prefixTail later _hlater childDepth runtimeType identity hlt
      exact hinvariant.errorNeutral (field :: prefixTail) later childDepth
        runtimeType identity hlt) (by
      intro prefixTail later _hlater childDepth runtimeType identity hlt
        _hincludes
      exact hinvariant.childEquivalent
        (GraphQL.Execution.mergedFieldSelectionSet
          ((field :: prefixTail) ++ [later]))
        childDepth runtimeType identity hlt)

structure CollectedFieldGroupAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (groups : List (Name × List ExecutableField))
    : Prop where
  prefixChildren
    : ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
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
                }
  absorbs
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
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
                    (.object [])))
  errorNeutral
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                  (.object []))
  extendedChildren
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
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
                }

theorem CollectedFieldGroupAppendInvariant.depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (groups : List (Name × List ExecutableField))
    : CollectedFieldGroupAppendInvariant schema resolvers variableValues 0 groups :=
  { prefixChildren := by
      intro _responseName _field _fields _prefixTail _hgroup _hprefix
        childDepth _runtimeType _identity hlt _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    absorbs := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    errorNeutral := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    extendedChildren := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt
      exact False.elim (Nat.not_lt_zero childDepth hlt) }

structure CollectedFieldGroupContainedAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : Prop where
  prefixChildren
    : ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> ValueContainsObject
                (resolvers.resolve field.parentType field.fieldName field.arguments
                  source)
                runtimeType identity
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
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> ValueContainsObject
                (resolvers.resolve field.parentType field.fieldName field.arguments
                  source)
                runtimeType identity
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
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> ValueContainsObject
                (resolvers.resolve field.parentType field.fieldName field.arguments
                  source)
                runtimeType identity
            -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                  (.object []))
  extendedChildren
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> ValueContainsObject
                (resolvers.resolve field.parentType field.fieldName field.arguments
                  source)
                runtimeType identity
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

theorem CollectedFieldGroupContainedAppendInvariant.depth_zero
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
        0 source groups :=
  { prefixChildren := by
      intro _responseName _field _fields _prefixTail _hgroup _hprefix
        childDepth _runtimeType _identity hlt _hcontains _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    absorbs := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt _hcontains
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    errorNeutral := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt _hcontains
      exact False.elim (Nat.not_lt_zero childDepth hlt)
    extendedChildren := by
      intro _responseName _field _fields _prefixTail _later _hgroup _hprefix
        _hlater childDepth _runtimeType _identity hlt _hcontains _hincludes
      exact False.elim (Nat.not_lt_zero childDepth hlt) }

theorem CollectedFieldGroupContainedAppendInvariant.of_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (source : ResolverValue ObjectIdentity)
    (hinvariant
      : CollectedFieldGroupAppendInvariant schema resolvers variableValues depth groups)
    : CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
        depth source groups :=
  { prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt _hcontains hincludes
      exact hinvariant.prefixChildren responseName field fields prefixTail
        hgroup hprefix childDepth runtimeType identity hlt hincludes
    absorbs := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains
      exact hinvariant.absorbs responseName field fields prefixTail later
        hgroup hprefix hlater childDepth runtimeType identity hlt
    errorNeutral := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains
      exact hinvariant.errorNeutral responseName field fields prefixTail later
        hgroup hprefix hlater childDepth runtimeType identity hlt
    extendedChildren := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains hincludes
      exact hinvariant.extendedChildren responseName field fields prefixTail
        later hgroup hprefix hlater childDepth runtimeType identity hlt }

theorem visitSubfields_absorbs_from_empty_object_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (childDepth : Nat) (runtimeType : Name) (identity : ObjectIdentity)
    (prefixSelectionSet laterSelectionSet : List Selection)
    : ResponseAbsorbs
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) prefixSelectionSet (.object []))
        (visitSubfields schema resolvers variableValues childDepth runtimeType
          (.object runtimeType identity) laterSelectionSet
          (visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity) prefixSelectionSet (.object []))) := by
  let base :=
    visitSubfields schema resolvers variableValues childDepth runtimeType
      (.object runtimeType identity) prefixSelectionSet (.object [])
  have hbaseReady : ResponseMergeReady base := by
    exact visitSubfields_response_ready schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity) prefixSelectionSet
      [] ResponseMergeReady_empty_object
  have hbaseAbsorbs : ResponseAbsorbs base base :=
    ResponseAbsorbs_refl_of_ready base hbaseReady
  obtain ⟨baseFields, hbaseObject⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues childDepth
      runtimeType (.object runtimeType identity) prefixSelectionSet []
  have hbaseFieldsReady : ResponseMergeReady (.object baseFields) := by
    rw [← hbaseObject]
    exact hbaseReady
  have hlocal :
      VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) laterSelectionSet
        base := by
    dsimp [base]
    rw [hbaseObject]
    exact
      visitSubfields_local_absorbs_from_ready schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity)
        laterSelectionSet baseFields hbaseFieldsReady
  exact
    visitSubfields_absorbs_from_steps schema resolvers variableValues
      childDepth runtimeType (.object runtimeType identity) base
      laterSelectionSet base
      (visitSubfields_absorbs_from_local_steps schema resolvers variableValues
        childDepth runtimeType (.object runtimeType identity) base
        laterSelectionSet base hbaseReady hbaseAbsorbs hlocal)

theorem CollectedFieldGroupContainedAppendInvariant.of_prefixChildren
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hchildren
      : ∀ responseName field fields prefixTail,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject
                  (resolvers.resolve field.parentType field.fieldName
                    field.arguments source)
                  runtimeType identity
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
    (herrors
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> ValueContainsObject
                  (resolvers.resolve field.parentType field.fieldName
                    field.arguments source)
                  runtimeType identity
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    : CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
        depth source groups :=
  { prefixChildren := hchildren
    absorbs := by
      intro _responseName field _fields prefixTail later _hgroup _hprefix
        _hlater childDepth runtimeType identity _hlt _hcontains
      exact
        visitSubfields_absorbs_from_empty_object_prefix schema resolvers
          variableValues childDepth runtimeType identity
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
          later.selectionSet
    errorNeutral := herrors
    extendedChildren := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt hcontains hincludes
      exact
        hchildren responseName field fields (prefixTail ++ [later]) hgroup
          (by
            intro candidate hcandidate
            rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
            · exact hprefix candidate hprefixMem
            · rcases List.mem_singleton.mp hlaterMem
              exact hlater)
          childDepth runtimeType identity hlt hcontains hincludes }

theorem
    ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant_from_prefix
    {ObjectIdentity : Type} {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity} {groups : List (Name × List ExecutableField)}
    (hinvariant
      : CollectedFieldGroupContainedAppendInvariant schema resolvers
          variableValues depth source groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups) (responseName : Name)
    (field : ExecutableField) (fields prefixTail remaining : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
    (hremaining : ∀ later, later ∈ remaining -> later ∈ fields)
    : ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments source)
        prefixTail remaining := by
  cases remaining with
  | nil =>
      simp [ExecutableFieldsMergedCompleteContainedAppendSteps]
  | cons later rest =>
      have hlaterFields : later ∈ fields := hremaining later (by simp)
      have hlater : later ∈ field :: fields :=
        List.mem_cons_of_mem field hlaterFields
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
          ExecutableFieldsResolveStable resolvers source (field :: fields) :=
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
          resolvers.resolve later.parentType later.fieldName later.arguments
              source =
          resolvers.resolve field.parentType field.fieldName field.arguments
              source :=
        (hgroupStable field later (by simp) hlater hsameResponse).symm
      have hprefixNext :
          ∀ candidate, candidate ∈ prefixTail ++ [later] ->
            candidate ∈ fields := by
        intro candidate hcandidate
        rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
        · exact hprefix candidate hprefixMem
        · rcases List.mem_singleton.mp hlaterMem
          exact hlaterFields
      have hremainingRest :
          ∀ candidate, candidate ∈ rest -> candidate ∈ fields := by
        intro candidate hcandidate
        exact hremaining candidate (by simp [hcandidate])
      simp [ExecutableFieldsMergedCompleteContainedAppendSteps]
      exact
        ⟨hlaterResponse, hlaterParent, hfieldName, hresolveLater,
          hinvariant.prefixChildren responseName field fields prefixTail hgroup
            hprefix,
          hinvariant.absorbs responseName field fields prefixTail later hgroup
            hprefix hlaterFields,
          hinvariant.errorNeutral responseName field fields prefixTail later
            hgroup hprefix hlaterFields,
          hinvariant.extendedChildren responseName field fields prefixTail
            later hgroup hprefix hlaterFields,
          ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant_from_prefix
            hinvariant hresponses hparents hcompatible hstable responseName
            field fields (prefixTail ++ [later]) rest hgroup hprefixNext
            hremainingRest⟩

theorem ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hinvariant
      : CollectedFieldGroupContainedAppendInvariant schema resolvers
          variableValues depth source groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    : ExecutableFieldsMergedCompleteContainedAppendSteps schema resolvers
        variableValues depth parentType source responseName field
        (resolvers.resolve field.parentType field.fieldName field.arguments source)
        [] fields :=
  ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant_from_prefix
    hinvariant hresponses hparents hcompatible hstable responseName field
    fields [] fields hgroup
    (by intro candidate hmem; simp at hmem)
    (by intro later hlater; exact hlater)

structure CollectedFieldGroupLocalAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (groups : List (Name × List ExecutableField))
    : Prop where
  prefixChildren
    : ∀ responseName field fields prefixTail,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
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
                }
  errorNeutral
    : ∀ responseName field fields prefixTail later,
        (responseName, field :: fields) ∈ groups
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> later ∈ fields
        -> ∀ childDepth runtimeType identity,
            childDepth < depth
            -> VisitSubfieldsErrorNeutral schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) later.selectionSet
                (visitSubfields schema resolvers variableValues childDepth
                  runtimeType (.object runtimeType identity)
                  (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                  (.object []))

theorem CollectedFieldGroupLocalAppendInvariant.of_child_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hchildren
      : ∀ childDepth runtimeType identity selectionSet,
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
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    (herrors
      : ∀ responseName field fields prefixTail later,
          (responseName, field :: fields) ∈ groups
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> later ∈ fields
          -> ∀ childDepth runtimeType identity,
              childDepth < depth
              -> VisitSubfieldsErrorNeutral schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType identity)
                  later.selectionSet
                  (visitSubfields schema resolvers variableValues childDepth
                    runtimeType (.object runtimeType identity)
                    (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
                    (.object [])))
    : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues depth
        groups :=
  { prefixChildren := by
      intro _responseName field _fields prefixTail _hgroup _hprefix childDepth
        runtimeType identity hlt _hincludes
      exact hchildren childDepth runtimeType identity
        (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) hlt
    errorNeutral := herrors }

theorem CollectedFieldGroupContainedAppendInvariant.of_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (source : ResolverValue ObjectIdentity)
    (hinvariant
      : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth groups)
    : CollectedFieldGroupContainedAppendInvariant schema resolvers variableValues
        depth source groups :=
  { prefixChildren := by
      intro responseName field fields prefixTail hgroup hprefix childDepth
        runtimeType identity hlt _hcontains hincludes
      exact hinvariant.prefixChildren responseName field fields prefixTail
        hgroup hprefix childDepth runtimeType identity hlt hincludes
    absorbs := by
      intro _responseName field _fields prefixTail later _hgroup _hprefix
        _hlater childDepth runtimeType identity _hlt _hcontains
      exact
        visitSubfields_absorbs_from_empty_object_prefix schema resolvers
          variableValues childDepth runtimeType identity
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
          later.selectionSet
    errorNeutral := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains
      exact hinvariant.errorNeutral responseName field fields prefixTail later
        hgroup hprefix hlater childDepth runtimeType identity hlt
    extendedChildren := by
      intro responseName field fields prefixTail later hgroup hprefix hlater
        childDepth runtimeType identity hlt _hcontains hincludes
      simpa [List.cons_append] using
        hinvariant.prefixChildren responseName field fields
          (prefixTail ++ [later]) hgroup
          (by
            intro candidate hcandidate
            rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
            · exact hprefix candidate hprefixMem
            · rcases List.mem_singleton.mp hlaterMem
              exact hlater)
          childDepth runtimeType identity hlt hincludes }

theorem ExecutedFieldAppendPlanState.of_collectedAppendInvariant_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant
      : CollectedFieldGroupAppendInvariant schema resolvers variableValues depth groups)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail remaining : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
    (hremaining : ∀ later, later ∈ remaining -> later ∈ fields)
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail remaining := by
  cases remaining with
  | nil =>
      exact
        ExecutedFieldAppendPlanState.nil
          (by
            intro childDepth runtimeType identity hlt _hincludes
            exact hinvariant.prefixChildren responseName field fields
              prefixTail hgroup hprefix childDepth runtimeType identity hlt
              _hincludes)
  | cons later rest =>
      have hlater : later ∈ fields := hremaining later (by simp)
      apply ExecutedFieldAppendPlanState.cons
      · intro childDepth runtimeType identity hlt _hincludes
        exact hinvariant.prefixChildren responseName field fields prefixTail
          hgroup hprefix childDepth runtimeType identity hlt _hincludes
      · exact List.mem_cons_of_mem field hlater
      · exact hinvariant.absorbs responseName field fields prefixTail later
          hgroup hprefix hlater
      · exact hinvariant.errorNeutral responseName field fields prefixTail
          later hgroup hprefix hlater
      · intro childDepth runtimeType identity hlt _hincludes
        simpa [List.cons_append] using
          hinvariant.prefixChildren responseName field fields
            (prefixTail ++ [later]) hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            childDepth runtimeType identity hlt _hincludes
      · exact
          ExecutedFieldAppendPlanState.of_collectedAppendInvariant_from_prefix
            hinvariant responseName field fields (prefixTail ++ [later]) rest
            hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            (by
              intro candidate hcandidate
              exact hremaining candidate (by simp [hcandidate]))

theorem ExecutedFieldAppendPlanState.of_collectedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant
      : CollectedFieldGroupAppendInvariant schema resolvers variableValues depth groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields :=
  ExecutedFieldAppendPlanState.of_collectedAppendInvariant_from_prefix
    hinvariant responseName field fields [] fields hgroup
    (by intro candidate hmem; simp at hmem)
    (by intro later hlater; exact hlater)

theorem ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant_from_prefix
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant
      : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth groups)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail remaining : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
    (hremaining : ∀ later, later ∈ remaining -> later ∈ fields)
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields prefixTail remaining := by
  cases remaining with
  | nil =>
      exact
        ExecutedFieldAppendPlanState.nil
          (by
            intro childDepth runtimeType identity hlt _hincludes
            exact hinvariant.prefixChildren responseName field fields
              prefixTail hgroup hprefix childDepth runtimeType identity hlt
              _hincludes)
  | cons later rest =>
      have hlater : later ∈ fields := hremaining later (by simp)
      let base :=
        fun childDepth runtimeType identity =>
          visitSubfields schema resolvers variableValues childDepth runtimeType
            (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
            (.object [])
      apply ExecutedFieldAppendPlanState.cons
      · intro childDepth runtimeType identity hlt _hincludes
        exact hinvariant.prefixChildren responseName field fields prefixTail
          hgroup hprefix childDepth runtimeType identity hlt _hincludes
      · exact List.mem_cons_of_mem field hlater
      · intro childDepth runtimeType identity hlt
        have hbaseReady :
            ResponseMergeReady (base childDepth runtimeType identity) := by
          exact visitSubfields_response_ready schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
            [] ResponseMergeReady_empty_object
        have hbaseAbsorbs :
            ResponseAbsorbs (base childDepth runtimeType identity)
              (base childDepth runtimeType identity) :=
          ResponseAbsorbs_refl_of_ready
            (base childDepth runtimeType identity) hbaseReady
        obtain ⟨baseFields, hbaseObject⟩ :=
          visitSubfields_preserves_object schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
            []
        have hbaseFieldsReady :
            ResponseMergeReady (.object baseFields) := by
          rw [← hbaseObject]
          exact hbaseReady
        have hlocal :
            VisitSubfieldsLocalAbsorbsFrom schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity)
              later.selectionSet (base childDepth runtimeType identity) := by
          dsimp [base]
          rw [hbaseObject]
          exact
            visitSubfields_local_absorbs_from_ready schema resolvers
              variableValues childDepth runtimeType (.object runtimeType identity)
              later.selectionSet baseFields hbaseFieldsReady
        exact
          visitSubfields_absorbs_from_steps schema resolvers variableValues
            childDepth runtimeType (.object runtimeType identity)
            (base childDepth runtimeType identity) later.selectionSet
            (base childDepth runtimeType identity)
            (visitSubfields_absorbs_from_local_steps schema resolvers
              variableValues childDepth runtimeType (.object runtimeType identity)
              (base childDepth runtimeType identity)
              later.selectionSet (base childDepth runtimeType identity)
              hbaseReady hbaseAbsorbs hlocal)
      · exact hinvariant.errorNeutral responseName field fields prefixTail
          later hgroup hprefix hlater
      · intro childDepth runtimeType identity hlt _hincludes
        simpa [List.cons_append] using
          hinvariant.prefixChildren responseName field fields
            (prefixTail ++ [later]) hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            childDepth runtimeType identity hlt _hincludes
      · exact
          ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant_from_prefix
            hinvariant responseName field fields (prefixTail ++ [later]) rest
            hgroup
            (by
              intro candidate hcandidate
              rcases List.mem_append.mp hcandidate with hprefixMem | hlaterMem
              · exact hprefix candidate hprefixMem
              · rcases List.mem_singleton.mp hlaterMem
                exact hlater)
            (by
              intro candidate hcandidate
              exact hremaining candidate (by simp [hcandidate]))

theorem ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {groups : List (Name × List ExecutableField)}
    (hinvariant
      : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    : ExecutedFieldAppendPlanState schema resolvers variableValues depth field
        fields [] fields :=
  ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant_from_prefix
    hinvariant responseName field fields [] fields hgroup
    (by intro candidate hmem; simp at hmem)
    (by intro later hlater; exact hlater)

theorem combineVisitStatus_object_append_result
    (leftFields rightFields : List (Name × ResponseValue))
    (leftStatus rightStatus : VisitStatus)
    : (match combineVisitStatus leftStatus rightStatus with
        | .error errors => .error errors
        | .ok (_unit, errors) => .ok (leftFields ++ rightFields, errors))
      = Result.combine List.append
          (match leftStatus with
            | .error errors => .error errors
            | .ok (_unit, errors) => .ok (leftFields, errors))
          (match rightStatus with
            | .error errors => .error errors
            | .ok (_unit, errors) => .ok (rightFields, errors)) := by
  cases leftStatus <;> cases rightStatus <;>
    simp [combineVisitStatus, GraphQL.Execution.Result.combine]

theorem executeRootSelectionSet_executableFieldSelections_append_fresh_eq_combine
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List ExecutableField)
    (hfresh
      : ∀ leftFields,
          (visitSubfields schema resolvers variableValues depth parentType source
              (executableFieldSelections left) (.object [])).fst
            = .object leftFields
          -> ∀ field, field ∈ right -> field.responseName ∉ leftFields.map Prod.fst)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source (executableFieldSelections (left ++ right))
      = Result.combine List.append
          (executeRootSelectionSet schema resolvers variableValues depth parentType
            source (executableFieldSelections left))
          (executeRootSelectionSet schema resolvers variableValues depth parentType
            source (executableFieldSelections right)) := by
  unfold executeRootSelectionSet
  rw [show executableFieldSelections (left ++ right) =
      executableFieldSelections left ++ executableFieldSelections right by
    simp [executableFieldSelections, List.map_append]]
  rw [visitSubfields_append_equivalence]
  obtain ⟨leftFields, hleftFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source (executableFieldSelections left) []
  let leftStatus :=
    (visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections left) (.object [])).snd
  have hleft :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections left) (.object []) =
      (.object leftFields, leftStatus) :=
    Prod.ext hleftFields rfl
  obtain ⟨rightFields, hrightFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source (executableFieldSelections right) []
  let rightStatus :=
    (visitSubfields schema resolvers variableValues depth parentType source
      (executableFieldSelections right) (.object [])).snd
  have hright :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections right) (.object []) =
      (.object rightFields, rightStatus) :=
    Prod.ext hrightFields rfl
  have hrightPrefix :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections right) (.object (leftFields ++ [])) =
      (.object (leftFields ++ rightFields), rightStatus) :=
    visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
      variableValues depth parentType source right leftFields [] rightFields
      rightStatus (hfresh leftFields hleftFields) hright
  have hrightPrefix' :
      visitSubfields schema resolvers variableValues depth parentType source
        (executableFieldSelections right) (.object leftFields) =
      (.object (leftFields ++ rightFields), rightStatus) := by
    simpa using hrightPrefix
  rw [hleft]
  rw [hright]
  dsimp
  rw [hrightPrefix']
  exact combineVisitStatus_object_append_result leftFields rightFields
    leftStatus rightStatus

namespace ExecutedFieldGroups

theorem fieldsNonempty
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ∀ {groups : List (Name × List ExecutableField)},
        ExecutedFieldGroups schema resolvers variableValues depth parentType source groups
        -> CollectedGroupsFieldsNonempty groups
  | [], _hgroups => CollectedGroupsFieldsNonempty_nil
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (ExecutedFieldGroups.no_empty_head hgroups)
  | (groupResponseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        subst candidateFields
        simp
      · exact fieldsNonempty hgroups.2 candidateResponseName candidateFields
          htail

theorem responseName
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ∀ {groups : List (Name × List ExecutableField)},
        ExecutedFieldGroups schema resolvers variableValues depth parentType source groups
        -> CollectedGroupsResponseName groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (ExecutedFieldGroups.no_empty_head hgroups)
  | (groupResponseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem candidate hcandidate
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponseName, hfields⟩
        subst candidateResponseName
        subst candidateFields
        exact hgroups.1.responseName_eq candidate hcandidate
      · exact responseName hgroups.2 candidateResponseName candidateFields
          htail candidate hcandidate

theorem parent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ∀ {groups : List (Name × List ExecutableField)},
        ExecutedFieldGroups schema resolvers variableValues depth parentType source groups
        -> CollectedGroupsParent parentType groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (responseName, []) :: rest, hgroups =>
      False.elim (ExecutedFieldGroups.no_empty_head hgroups)
  | (responseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem candidate hcandidate
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        subst candidateFields
        exact hgroups.1.parent_eq candidate hcandidate
      · exact parent hgroups.2 candidateResponseName candidateFields htail
          candidate hcandidate

def of_collected_groups_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ (groups : List (Name × List ExecutableField)),
        CollectedGroupsFieldsNonempty groups
        -> CollectedGroupsResponseName groups
        -> CollectedGroupsParent parentType groups
        -> (∀ responseName field fields,
              (responseName, field :: fields) ∈ groups
              -> ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName = some fieldDefinition)
        -> CollectedGroupsFieldValidationMergeCompatible groups
        -> CollectedGroupsResolveStable resolvers source groups
        -> (∀ responseName field fields,
              (responseName, field :: fields) ∈ groups
              -> ExecutedFieldAppendPlanState schema resolvers variableValues depth
                  field fields [] fields)
        -> ExecutedFieldGroups schema resolvers variableValues depth parentType
            source groups
  | [], _hnonempty, _hresponses, _hparents, _hlookups, _hcompatible, _hstable,
      _hplanStates =>
      ExecutedFieldGroups.nil
  | (responseName, []) :: rest, hnonempty, _hresponses, _hparents,
      _hlookups, _hcompatible, _hstable, _hplanStates => by
      have hhead : ([] : List ExecutableField) ≠ [] :=
        hnonempty responseName [] (by simp)
      exact False.elim (hhead rfl)
  | (responseName, field :: fields) :: rest, hnonempty, hresponses, hparents,
      hlookups, hcompatible, hstable, hplanStates => by
      exact
        ExecutedFieldGroups.cons
          (ExecutedFieldGroup.of_collected_group_state schema resolvers
            variableValues depth parentType source
            ((responseName, field :: fields) :: rest) responseName field
            fields (by simp) hresponses hparents hcompatible hstable
            (hlookups responseName field fields (by simp))
            (hplanStates responseName field fields (by simp)))
          (of_collected_groups_state schema resolvers variableValues depth
            parentType source rest
            (CollectedGroupsFieldsNonempty_tail hnonempty)
            (CollectedGroupsResponseName_tail hresponses)
            (CollectedGroupsParent_tail hparents)
            (by
              intro tailResponseName tailField tailFields hmem
              exact hlookups tailResponseName tailField tailFields
                (by simp [hmem]))
            (CollectedGroupsFieldValidationMergeCompatible_tail hcompatible)
            (CollectedGroupsResolveStable.tail resolvers source
              (responseName, field :: fields) rest hstable)
            (by
              intro tailResponseName tailField tailFields hmem
              exact hplanStates tailResponseName tailField tailFields
                (by simp [hmem])))

def of_collected_groups_appendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hlookups
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant : FieldGroupAppendInvariant schema resolvers variableValues depth)
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        groups :=
  of_collected_groups_state schema resolvers variableValues depth parentType
    source groups hnonempty hresponses hparents hlookups hcompatible hstable
    (by
      intro _responseName field fields _hmem
      exact ExecutedFieldAppendPlanState.of_appendInvariant hinvariant field
        fields)

def of_collected_groups_collectedAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hlookups
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant
      : CollectedFieldGroupAppendInvariant schema resolvers variableValues depth groups)
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        groups :=
  of_collected_groups_state schema resolvers variableValues depth parentType
    source groups hnonempty hresponses hparents hlookups hcompatible hstable
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedAppendInvariant hinvariant
          responseName field fields hgroup)

def of_collected_groups_collectedLocalAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hlookups
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant
      : CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth groups)
    : ExecutedFieldGroups schema resolvers variableValues depth parentType source
        groups :=
  of_collected_groups_state schema resolvers variableValues depth parentType
    source groups hnonempty hresponses hparents hlookups hcompatible hstable
    (by
      intro responseName field fields hgroup
      exact
        ExecutedFieldAppendPlanState.of_collectedLocalAppendInvariant hinvariant
          responseName field fields hgroup)

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hgroups
      : ExecutedFieldGroups schema resolvers variableValues depth parentType
          source groups)
    (hnodup : PairKeysNodup groups)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source groups := by
  unfold ExecutableGroupsFlatSpecEquivalent
  unfold ExecutableFieldsFlatSpecEquivalent
  induction groups with
  | nil =>
      simp [collectedExecutableFields, executableFieldSelections,
        executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields,
        GraphQL.Execution.executeCollectedFields, visitSubfields, visitOk]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      cases fields with
      | nil =>
          exact False.elim (ExecutedFieldGroups.no_empty_head hgroups)
      | cons field fieldsTail =>
          have hhead :
              ExecutedFieldGroup schema resolvers variableValues depth
                parentType source responseName field fieldsTail :=
            hgroups.1
          have htail :
              ExecutedFieldGroups schema resolvers variableValues depth
                parentType source rest :=
            hgroups.2
          have htailNodup : PairKeysNodup rest :=
            PairKeysNodup.tail hnodup
          have htailEq := ih htail htailNodup
          unfold ExecutableFieldsFlatSpecEquivalent at htailEq
          have hnonempty :
              CollectedGroupsFieldsNonempty
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroups.fieldsNonempty hgroups
          have hresponses :
              CollectedGroupsResponseName
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroups.responseName hgroups
          have hparents :
              CollectedGroupsParent parentType
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroups.parent hgroups
          have hspec :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues (depth + 1) parentType source
                  (executableFieldSelections
                    (collectedExecutableFields
                      ((responseName, field :: fieldsTail) :: rest))) =
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues (depth + 1) source
                  ((responseName, field :: fieldsTail) :: rest) :=
            specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
              schema resolvers variableValues (depth + 1) parentType source
              ((responseName, field :: fieldsTail) :: rest) hnodup hnonempty
              hresponses hparents
          have htailSpec :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues (depth + 1) parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) =
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues (depth + 1) source rest :=
            specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
              schema resolvers variableValues (depth + 1) parentType source
              rest htailNodup
              (ExecutedFieldGroups.fieldsNonempty htail)
              (ExecutedFieldGroups.responseName htail)
              (ExecutedFieldGroups.parent htail)
          have hheadEq :
              executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
                GraphQL.Execution.executeField schema resolvers variableValues
                  (depth + 1) source responseName (field :: fieldsTail) :=
            hhead.mergedComplete
          have happend :
              executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections
                    ((field :: fieldsTail) ++
                      collectedExecutableFields rest)) =
                Result.combine List.append
                  (executeRootSelectionSet schema resolvers variableValues
                    (depth + 1) parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (executeRootSelectionSet schema resolvers variableValues
                    (depth + 1) parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
            apply
              executeRootSelectionSet_executableFieldSelections_append_fresh_eq_combine
                schema resolvers variableValues (depth + 1) parentType source
                (field :: fieldsTail) (collectedExecutableFields rest)
            intro leftFields hleftFields tailField htailField hmemLeft
            have hleftKey :
                tailField.responseName =
                  responseName := by
              have hcollectKey :
                  tailField.responseName ∈
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source
                      (executableFieldSelections (field :: fieldsTail))).map
                      Prod.fst :=
                visitSubfields_object_empty_key_mem_collectFields schema
                  resolvers variableValues (depth + 1) parentType source
                  (executableFieldSelections (field :: fieldsTail))
                  leftFields tailField.responseName hleftFields hmemLeft
              have hfieldKey :
                  tailField.responseName ∈
                    (field :: fieldsTail).map
                      (fun field => field.responseName) :=
                (collectFields_executableFieldSelections_key_mem_global schema
                  variableValues parentType source (field :: fieldsTail)
                  tailField.responseName).mp hcollectKey
              rcases List.mem_map.mp hfieldKey with
                ⟨headField, hheadField, hkey⟩
              rw [← hkey]
              exact hhead.responseName_eq headField hheadField
            have htailGroupKey :
                tailField.responseName ∈ rest.map Prod.fst := by
              exact
                collectedExecutableFields_responseName_mem rest
                  (ExecutedFieldGroups.responseName htail) tailField
                  htailField
            have hheadNotTail : responseName ∉ rest.map Prod.fst :=
              PairKeysNodup.head_not_mem_tail hnodup
            exact hheadNotTail (by simpa [hleftKey] using htailGroupKey)
          calc
            executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source
                (executableFieldSelections
                  (collectedExecutableFields
                    ((responseName, field :: fieldsTail) :: rest)))
                =
              executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source
                (executableFieldSelections
                  ((field :: fieldsTail) ++ collectedExecutableFields rest)) := by
                simp [collectedExecutableFields]
            _ =
                Result.combine List.append
                (executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections (field :: fieldsTail)))
                (executeRootSelectionSet schema resolvers variableValues
                  (depth + 1) parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest))) :=
                happend
            _ =
              Result.combine List.append
                (GraphQL.Execution.executeField schema resolvers
                  variableValues (depth + 1) source responseName
                  (field :: fieldsTail))
                (GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues (depth + 1) source rest) := by
                rw [hheadEq, htailEq, htailSpec]
            _ =
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues (depth + 1) source
                ((responseName, field :: fieldsTail) :: rest) := by
                simp [GraphQL.Execution.executeCollectedFields]
            _ =
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues (depth + 1) parentType source
                (executableFieldSelections
                  (collectedExecutableFields
                    ((responseName, field :: fieldsTail) :: rest))) :=
                hspec.symm

theorem groupFlatSpecAlignedEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hgroups
      : ExecutedFieldGroups schema resolvers variableValues depth parentType
          source groups)
    (hnodup : PairKeysNodup groups)
    : ExecutableGroupsFlatSpecAlignedEquivalent schema resolvers variableValues
        (depth + 1) parentType source groups :=
  ExecutableGroupsFlatSpecAlignedEquivalent.of_exact
    (ExecutedFieldGroups.groupFlatSpecEquivalent hgroups hnodup)

end ExecutedFieldGroups

theorem ExecutableGroupsFlatSpecAlignedEquivalent_of_group_aligned
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hnodup : PairKeysNodup groups)
    (hgroupAligned
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ExecutableFieldsFlatSpecAlignedEquivalent schema resolvers
              variableValues depth parentType source (field :: fields))
    : ExecutableGroupsFlatSpecAlignedEquivalent schema resolvers variableValues
        depth parentType source groups := by
  unfold ExecutableGroupsFlatSpecAlignedEquivalent
  unfold ExecutableFieldsFlatSpecAlignedEquivalent
  induction groups with
  | nil =>
      simp [collectedExecutableFields, executableFieldSelections,
        executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
        GraphQL.Execution.collectFields,
        GraphQL.Execution.executeCollectedFields, visitSubfields, visitOk,
        RootSelectionResultAlignedEquivalent]
      exact ErrorPresenceEquivalent.refl 0
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      cases fields with
      | nil =>
          have hhead : ([] : List ExecutableField) ≠ [] :=
            hnonempty responseName [] (by simp)
          exact False.elim (hhead rfl)
      | cons field fieldsTail =>
          have htailNodup : PairKeysNodup rest :=
            PairKeysNodup.tail hnodup
          have htailAligned :
              ExecutableFieldsFlatSpecAlignedEquivalent schema resolvers
                variableValues depth parentType source
                (collectedExecutableFields rest) := by
            exact ih
              (CollectedGroupsFieldsNonempty_tail hnonempty)
              (CollectedGroupsResponseName_tail hresponses)
              (CollectedGroupsParent_tail hparents)
              htailNodup
              (by
                intro tailResponseName tailField tailFields hmem
                exact hgroupAligned tailResponseName tailField tailFields
                  (by simp [hmem]))
          unfold ExecutableFieldsFlatSpecAlignedEquivalent at htailAligned
          have hheadAligned :
              RootSelectionResultAlignedEquivalent
                (executeRootSelectionSet schema resolvers variableValues depth
                  parentType source
                  (executableFieldSelections (field :: fieldsTail)))
                (GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues depth parentType source
                  (executableFieldSelections (field :: fieldsTail))) := by
            simpa [ExecutableFieldsFlatSpecAlignedEquivalent] using
              hgroupAligned responseName field fieldsTail (by simp)
          have hnonemptyAll :
              CollectedGroupsFieldsNonempty
                ((responseName, field :: fieldsTail) :: rest) :=
            hnonempty
          have hresponsesAll :
              CollectedGroupsResponseName
                ((responseName, field :: fieldsTail) :: rest) :=
            hresponses
          have hparentsAll :
              CollectedGroupsParent parentType
                ((responseName, field :: fieldsTail) :: rest) :=
            hparents
          have hspec :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues depth parentType source
                  (executableFieldSelections
                    (collectedExecutableFields
                      ((responseName, field :: fieldsTail) :: rest))) =
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues depth source
                  ((responseName, field :: fieldsTail) :: rest) :=
            specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
              schema resolvers variableValues depth parentType source
              ((responseName, field :: fieldsTail) :: rest) hnodup hnonemptyAll
              hresponsesAll hparentsAll
          have htailSpec :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues depth parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) =
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues depth source rest :=
            specExecuteRootSelectionSet_executableFieldSelections_collectedExecutableFields
              schema resolvers variableValues depth parentType source rest
              htailNodup (CollectedGroupsFieldsNonempty_tail hnonempty)
              (CollectedGroupsResponseName_tail hresponses)
              (CollectedGroupsParent_tail hparents)
          have hheadSpecRoot :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues depth parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source [(responseName, field :: fieldsTail)] :=
            specExecuteRootSelectionSet_executableFieldSelections_same_group
              schema resolvers variableValues depth parentType source responseName
              field fieldsTail
              (hresponses responseName (field :: fieldsTail) (by simp))
              (hparents responseName (field :: fieldsTail) (by simp))
          have hheadSpec :
              GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues depth parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
              GraphQL.Execution.executeField schema resolvers variableValues depth
                source responseName (field :: fieldsTail) := by
            rw [hheadSpecRoot]
            cases hfield :
                GraphQL.Execution.executeField schema resolvers variableValues
                  depth source responseName (field :: fieldsTail) <;>
              simp [GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine, hfield]
          have happend :
              executeRootSelectionSet schema resolvers variableValues depth
                  parentType source
                  (executableFieldSelections
                    ((field :: fieldsTail) ++
                      collectedExecutableFields rest)) =
                Result.combine List.append
                  (executeRootSelectionSet schema resolvers variableValues depth
                    parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (executeRootSelectionSet schema resolvers variableValues depth
                    parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
            apply
              executeRootSelectionSet_executableFieldSelections_append_fresh_eq_combine
                schema resolvers variableValues depth parentType source
                (field :: fieldsTail) (collectedExecutableFields rest)
            intro leftFields hleftFields tailField htailField hmemLeft
            have hleftKey :
                tailField.responseName = responseName := by
              have hcollectKey :
                  tailField.responseName ∈
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source
                      (executableFieldSelections (field :: fieldsTail))).map
                      Prod.fst :=
                visitSubfields_object_empty_key_mem_collectFields schema
                  resolvers variableValues depth parentType source
                  (executableFieldSelections (field :: fieldsTail))
                  leftFields tailField.responseName hleftFields hmemLeft
              have hfieldKey :
                  tailField.responseName ∈
                    (field :: fieldsTail).map (fun field => field.responseName) :=
                (collectFields_executableFieldSelections_key_mem_global schema
                  variableValues parentType source (field :: fieldsTail)
                  tailField.responseName).mp hcollectKey
              rcases List.mem_map.mp hfieldKey with
                ⟨headField, hheadField, hkey⟩
              rw [← hkey]
              exact
                hresponses responseName (field :: fieldsTail) (by simp)
                  headField hheadField
            have htailGroupKey :
                tailField.responseName ∈ rest.map Prod.fst := by
              exact
                collectedExecutableFields_responseName_mem rest
                  (CollectedGroupsResponseName_tail hresponses) tailField
                  htailField
            have hheadNotTail : responseName ∉ rest.map Prod.fst :=
              PairKeysNodup.head_not_mem_tail hnodup
            exact hheadNotTail (by simpa [hleftKey] using htailGroupKey)
          have hcombined :
              RootSelectionResultAlignedEquivalent
                (Result.combine List.append
                  (executeRootSelectionSet schema resolvers variableValues depth
                    parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (executeRootSelectionSet schema resolvers variableValues depth
                    parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))))
                (Result.combine List.append
                  (GraphQL.Execution.executeRootSelectionSet schema resolvers
                    variableValues depth parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (GraphQL.Execution.executeRootSelectionSet schema resolvers
                    variableValues depth parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest)))) :=
            RootSelectionResultAlignedEquivalent.combine_append hheadAligned
              htailAligned
          have hleftEq :
              executeRootSelectionSet schema resolvers variableValues depth
                  parentType source
                  (executableFieldSelections
                    (collectedExecutableFields
                      ((responseName, field :: fieldsTail) :: rest))) =
                Result.combine List.append
                  (executeRootSelectionSet schema resolvers variableValues depth
                    parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (executeRootSelectionSet schema resolvers variableValues depth
                    parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
            simpa [collectedExecutableFields] using happend
          have hspecCombine :
              Result.combine List.append
                  (GraphQL.Execution.executeRootSelectionSet schema resolvers
                    variableValues depth parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (GraphQL.Execution.executeRootSelectionSet schema resolvers
                    variableValues depth parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) =
                GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues depth parentType source
                  (executableFieldSelections
                    (collectedExecutableFields
                      ((responseName, field :: fieldsTail) :: rest))) := by
            calc
              Result.combine List.append
                  (GraphQL.Execution.executeRootSelectionSet schema resolvers
                    variableValues depth parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (GraphQL.Execution.executeRootSelectionSet schema resolvers
                    variableValues depth parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest)))
                  =
                Result.combine List.append
                  (GraphQL.Execution.executeField schema resolvers variableValues
                    depth source responseName (field :: fieldsTail))
                  (GraphQL.Execution.executeCollectedFields schema resolvers
                    variableValues depth source rest) := by
                    rw [hheadSpec, htailSpec]
              _ =
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues depth source
                  ((responseName, field :: fieldsTail) :: rest) := by
                    simp [GraphQL.Execution.executeCollectedFields]
              _ =
                GraphQL.Execution.executeRootSelectionSet schema resolvers
                  variableValues depth parentType source
                  (executableFieldSelections
                    (collectedExecutableFields
                      ((responseName, field :: fieldsTail) :: rest))) :=
                    hspec.symm
          exact
            RootSelectionResultAlignedEquivalent.trans
              (RootSelectionResultAlignedEquivalent.of_eq hleftEq)
              (RootSelectionResultAlignedEquivalent.trans hcombined
                (RootSelectionResultAlignedEquivalent.of_eq hspecCombine))

theorem ExecutableGroupsFlatSpecAlignedEquivalent_of_alignedAppendSteps_positive
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hlookups
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfieldChildren
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ∀ childDepth runtimeType identity,
              childDepth < completionDepth + 1
              -> ValueContainsObject
                  (resolvers.resolve field.parentType field.fieldName field.arguments
                    source)
                  runtimeType identity
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
      : ∀ responseName field fields,
          (responseName, field :: fields) ∈ groups
          -> ExecutableFieldsMergedAlignedAppendSteps schema resolvers variableValues
              (completionDepth + 1) parentType source responseName field
              (resolvers.resolve field.parentType field.fieldName field.arguments source)
              [] fields)
    (hnodup : PairKeysNodup groups)
    : ExecutableGroupsFlatSpecAlignedEquivalent schema resolvers variableValues
        (completionDepth + 2) parentType source groups := by
  exact
    ExecutableGroupsFlatSpecAlignedEquivalent_of_group_aligned
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (depth := completionDepth + 2)
      (parentType := parentType) (source := source) (groups := groups)
      hnonempty hresponses hparents hnodup
      (by
        intro responseName field fields hgroup
        exact
          ExecutableFieldsFlatSpecAlignedEquivalent_nonempty_group_of_alignedAppendSteps_positive
            schema resolvers variableValues completionDepth parentType source
            responseName field fields
            (resolvers.resolve field.parentType field.fieldName field.arguments
              source)
            (hresponses responseName (field :: fields) hgroup)
            (hparents responseName (field :: fields) hgroup)
            rfl
            (hlookups responseName field fields hgroup)
            (hfieldChildren responseName field fields hgroup)
            (hsteps responseName field fields hgroup))

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
