import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.AppendInvariant

/-!
Group-list proof helpers that carry final merged-complete evidence per group.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped
namespace Eager

open GraphQL.Execution

structure ExecutedFieldGroupComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) where
  resolved : Option (ResolverValue ObjectIdentity)
  responseName_eq
    : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName
  parent_eq
    : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType
  resolved_eq
    : resolvers.resolve field.parentType field.fieldName field.arguments source = resolved
  mergedComplete
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields resolved

namespace ExecutedFieldGroupComplete

theorem mergedComplete_resolved
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {field : ExecutableField}
    {fields : List ExecutableField}
    (group
      : ExecutedFieldGroupComplete schema resolvers variableValues depth
          parentType source responseName field fields)
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field fields
        (resolvers.resolve field.parentType field.fieldName field.arguments source) := by
  rw [group.resolved_eq]
  exact group.mergedComplete

def of_containedAppendInvariant
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
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    : ExecutedFieldGroupComplete schema resolvers variableValues depth parentType
        source responseName field fields where
  resolved :=
    resolvers.resolve field.parentType field.fieldName field.arguments source
  responseName_eq := hresponses responseName (field :: fields) hgroup
  parent_eq := hparents responseName (field :: fields) hgroup
  resolved_eq := rfl
  mergedComplete := by
    have hfieldResponse :
        field.responseName = responseName :=
      hresponses responseName (field :: fields) hgroup field (by simp)
    have hfieldParent :
        field.parentType = parentType :=
      hparents responseName (field :: fields) hgroup field (by simp)
    apply ExecutableFieldsMergedComplete_of_contained_appendSteps schema
      resolvers variableValues depth parentType source responseName field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hfieldResponse hfieldParent rfl
      (hlookups responseName field fields hgroup)
    · intro childDepth runtimeType identity hlt hcontains hincludes
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        hinvariant.prefixChildren responseName field fields [] hgroup
          (by intro candidate hmem; simp at hmem)
          childDepth runtimeType identity hlt hcontains hincludes
    · exact
        ExecutableFieldsMergedCompleteContainedAppendSteps.of_collectedInvariant
          hinvariant hresponses hparents hcompatible hstable responseName field
          fields hgroup

end ExecutedFieldGroupComplete

def ExecutedFieldGroupsComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List (Name × List ExecutableField) -> Type
  | [] => Unit
  | (_responseName, []) :: _rest => Empty
  | (responseName, field :: fields) :: rest =>
      ExecutedFieldGroupComplete schema resolvers variableValues depth
        parentType source responseName field fields
      × ExecutedFieldGroupsComplete schema resolvers variableValues depth
          parentType source rest

namespace ExecutedFieldGroupsComplete

theorem no_empty_head
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {responseName : Name} {rest : List (Name × List ExecutableField)}
    : ExecutedFieldGroupsComplete schema resolvers variableValues depth
        parentType source ((responseName, []) :: rest)
      -> False := by
  intro hgroups
  exact nomatch hgroups

theorem fieldsNonempty
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ∀ {groups : List (Name × List ExecutableField)},
        ExecutedFieldGroupsComplete schema resolvers variableValues depth
          parentType source groups
        -> CollectedGroupsFieldsNonempty groups
  | [], _hgroups => CollectedGroupsFieldsNonempty_nil
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (no_empty_head hgroups)
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
        ExecutedFieldGroupsComplete schema resolvers variableValues depth
          parentType source groups
        -> CollectedGroupsResponseName groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (groupResponseName, []) :: rest, hgroups =>
      False.elim (no_empty_head hgroups)
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
        ExecutedFieldGroupsComplete schema resolvers variableValues depth
          parentType source groups
        -> CollectedGroupsParent parentType groups
  | [], _hgroups => by
      intro _responseName _fields hmem
      simp at hmem
  | (responseName, []) :: rest, hgroups =>
      False.elim (no_empty_head hgroups)
  | (responseName, field :: fields) :: rest, hgroups => by
      intro candidateResponseName candidateFields hmem candidate hcandidate
      simp at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        subst candidateFields
        exact hgroups.1.parent_eq candidate hcandidate
      · exact parent hgroups.2 candidateResponseName candidateFields htail
          candidate hcandidate

def of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hnonempty : CollectedGroupsFieldsNonempty groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hstable : CollectedGroupsResolveStable resolvers source groups)
    (hinvariant
      : CollectedFieldGroupContainedAppendInvariant schema resolvers
          variableValues depth source groups)
    : ExecutedFieldGroupsComplete schema resolvers variableValues depth parentType
        source groups :=
  match groups with
  | [] => ()
  | (responseName, []) :: _rest =>
      False.elim (hnonempty responseName [] (by simp) rfl)
  | (responseName, field :: fields) :: rest =>
      let tailInvariant : CollectedFieldGroupContainedAppendInvariant schema resolvers
                            variableValues depth source rest :=
        { prefixChildren := by
            intro tailResponseName tailField tailFields prefixTail hgroup
              hprefix childDepth runtimeType identity hlt hcontains hincludes
            exact hinvariant.prefixChildren tailResponseName tailField
              tailFields prefixTail (by simp [hgroup]) hprefix childDepth
              runtimeType identity hlt hcontains hincludes
          absorbs := by
            intro tailResponseName tailField tailFields prefixTail later hgroup
              hprefix hlater childDepth runtimeType identity hlt hcontains
            exact hinvariant.absorbs tailResponseName tailField tailFields
              prefixTail later (by simp [hgroup]) hprefix hlater childDepth
              runtimeType identity hlt hcontains
          errorNeutral := by
            intro tailResponseName tailField tailFields prefixTail later hgroup
              hprefix hlater childDepth runtimeType identity hlt hcontains
            exact hinvariant.errorNeutral tailResponseName tailField
              tailFields prefixTail later (by simp [hgroup]) hprefix hlater
              childDepth runtimeType identity hlt hcontains
          extendedChildren := by
            intro tailResponseName tailField tailFields prefixTail later hgroup
              hprefix hlater childDepth runtimeType identity hlt hcontains
              hincludes
            exact hinvariant.extendedChildren tailResponseName tailField
              tailFields prefixTail later (by simp [hgroup]) hprefix hlater
              childDepth runtimeType identity hlt hcontains hincludes }
      let tailLookups : CollectedGroupsFieldLookupValid schema parentType rest := by
        intro tailResponseName tailField tailFields hgroup
        exact hlookups tailResponseName tailField tailFields (by simp [hgroup])
      ⟨ExecutedFieldGroupComplete.of_containedAppendInvariant hinvariant
          hresponses hparents hcompatible hlookups hstable responseName field fields
          (by simp),
        of_collected_groups_containedAppendInvariant schema resolvers
          variableValues depth parentType source rest
          (CollectedGroupsFieldsNonempty_tail hnonempty)
          (CollectedGroupsResponseName_tail hresponses)
          (CollectedGroupsParent_tail hparents)
          (CollectedGroupsFieldValidationMergeCompatible_tail hcompatible)
          tailLookups
          (CollectedGroupsResolveStable.tail resolvers source
            (responseName, field :: fields) rest hstable)
          tailInvariant⟩

theorem groupFlatSpecEquivalent
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hgroups
      : ExecutedFieldGroupsComplete schema resolvers variableValues depth
          parentType source groups)
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
          exact False.elim (no_empty_head hgroups)
      | cons field fieldsTail =>
          have hhead :
              ExecutedFieldGroupComplete schema resolvers variableValues depth
                parentType source responseName field fieldsTail :=
            hgroups.1
          have htail :
              ExecutedFieldGroupsComplete schema resolvers variableValues depth
                parentType source rest :=
            hgroups.2
          have htailNodup : PairKeysNodup rest :=
            PairKeysNodup.tail hnodup
          have htailEq := ih htail htailNodup
          unfold ExecutableFieldsFlatSpecEquivalent at htailEq
          have hnonempty :
              CollectedGroupsFieldsNonempty
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroupsComplete.fieldsNonempty hgroups
          have hresponses :
              CollectedGroupsResponseName
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroupsComplete.responseName hgroups
          have hparents :
              CollectedGroupsParent parentType
                ((responseName, field :: fieldsTail) :: rest) :=
            ExecutedFieldGroupsComplete.parent hgroups
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
              (ExecutedFieldGroupsComplete.fieldsNonempty htail)
              (ExecutedFieldGroupsComplete.responseName htail)
              (ExecutedFieldGroupsComplete.parent htail)
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
                  (ExecutedFieldGroupsComplete.responseName htail) tailField
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

end ExecutedFieldGroupsComplete

theorem executeRootSelectionSet_eq_spec_of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    {groups : List (Name × List ExecutableField)}
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers variableValues (depth + 1)
          parentType source selectionSet (.object []))
    (hcollected
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
    (hlookups : CollectedGroupsFieldLookupValid schema parentType groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupContainedAppendInvariant schema resolvers
          variableValues depth source groups)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source selectionSet := by
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
  have hnonempty : CollectedGroupsFieldsNonempty groups := by
    rw [← hcollect]
    exact collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  have hresponses : CollectedGroupsResponseName groups :=
    ExecutionCollectedFieldInvariant.responseName_of_collect_eq state groups
      hcollect
  have hparents : CollectedGroupsParent parentType groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.parent_of_collect_eq state groups
        hcollect
  have hstable : CollectedGroupsResolveStable resolvers source groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq state groups
        hcollected hcollect
  have hnodup : PairKeysNodup groups := by
    simpa [state] using
      ExecutionCollectedFieldInvariant.pairKeysNodup_of_collect_eq state
        groups hcollected hcollect
  apply executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
    schema resolvers variableValues (depth + 1) parentType source selectionSet
    hflat
  rw [hcollect]
  exact
    ExecutedFieldGroupsComplete.groupFlatSpecEquivalent
      (ExecutedFieldGroupsComplete.of_collected_groups_containedAppendInvariant
        schema resolvers variableValues depth parentType source groups
        hnonempty hresponses hparents hcompatible hlookups hstable happend)
      hnodup

theorem executeQueryWithFuel_eq_spec_of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
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
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupContainedAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth source groups)
    : executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          operation (depth + 1) source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation (depth + 1) source hroot
  exact
    executeRootSelectionSet_eq_spec_of_collected_groups_containedAppendInvariant
      hcollect hflat hcollected hlookups hcompatible happend

theorem executeQuery_eq_spec_of_collected_groups_containedAppendInvariant
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {operation : Operation}
    {depth : Nat} {source : ResolverValue ObjectIdentity}
    {groups : List (Name × List ExecutableField)}
    (hdepth : GraphQL.Execution.executeQueryFuelBound operation = depth + 1)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (depth + 1) (operation.rootType schema) source operation.selectionSet
          (.object []))
    (hcollected
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
    (hlookups : CollectedGroupsFieldLookupValid schema (operation.rootType schema) groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (happend
      : CollectedFieldGroupContainedAppendInvariant schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          depth source groups)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  rw [hdepth]
  exact
    executeQueryWithFuel_eq_spec_of_collected_groups_containedAppendInvariant
      hroot hcollect hflat hcollected hlookups hcompatible happend

end Eager
end ExecutionUngrouped
end Algorithms

end GraphQL
