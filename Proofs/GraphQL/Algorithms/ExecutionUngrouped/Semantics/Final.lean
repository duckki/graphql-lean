import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Semantics.AlignedReady
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.CancelingEager
import Proofs.GraphQL.Algorithms.ExecutionCancelingSiblings.Semantics

/-!
Final semantic-preservation theorems for ungrouped execution.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

variable {ObjectRef : Type}

theorem collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_responseNamesNodup
    (schema : Schema) (variableValues : Execution.VariableValues) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> CollectedSelectionSetGroupsSingleton schema variableValues parentType
          source selectionSet := by
  intro hall hfree hnodup responseName fields hgroup
  have hnonempty :=
    collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  cases fields with
  | nil =>
      exact False.elim (hnonempty responseName [] hgroup rfl)
  | cons field fieldsTail =>
      have htail : fieldsTail = [] :=
        (FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
            schema variableValues parentType source selectionSet hall hfree hnodup
            hgroup
            (prefixTail := ([] : List Execution.ExecutableField))
            (by
              intro candidate hmem
              simp at hmem)).1
      subst fieldsTail
      simp

theorem collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_normal
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.selectionSetNormal schema parentType selectionSet
      -> CollectedSelectionSetGroupsSingleton schema variableValues parentType
          source selectionSet := by
  intro hall hfree hnormal
  have hnonRedundant : NormalForm.selectionSetNonRedundant selectionSet :=
    hnormal.2
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant
  rcases hnonRedundant with ⟨hnodup, _hfragmentNodup, _hchildren⟩
  exact
    collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_responseNamesNodup
      schema variableValues parentType source selectionSet hall hfree
      hnodup

theorem collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> CollectedSelectionSetGroupsSingleton schema variableValues childRuntime
          (Execution.ResolverValue.object childRuntime ref) childSelectionSet := by
  intro hschema hinclude hgenerated responseName fields hgroup
  have hnonempty :=
    collectFields_fieldsNonempty schema variableValues childRuntime
      (Execution.ResolverValue.object childRuntime ref) childSelectionSet
  cases fields with
  | nil =>
      exact False.elim (hnonempty responseName [] hgroup rfl)
  | cons field fieldsTail =>
      have htail : fieldsTail = [] :=
        (collectFields_generatedNormalizedFieldChild_prefix_empty schema
          variableValues childType childRuntime ref childSelectionSet hschema
          hinclude hgenerated hgroup
          (prefixTail := ([] : List Execution.ExecutableField))
            (by
              intro candidate hmem
              simp at hmem)).1
      subst fieldsTail
      simp

theorem executionSelectionSetLookupValid_normalizeSelectionSet (schema : Schema)
    : ∀ parentType selectionSet,
        executionSelectionSetLookupValid schema parentType
          (NormalForm.normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet
    using NormalForm.normalizeSelectionSet.induct schema with
  | case1 parentType =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      simp [NormalForm.normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have hrestLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType
                  (NormalForm.withoutFieldSelectionsWithResponseName schema responseName rest) ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using hrest
      exact
        hrestLookup selection
          (by simpa [NormalForm.normalizeSelectionSet, hlookup] using hmem)
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      simp [NormalForm.normalizeSelectionSet, hlookup,
        NormalForm.normalizedField] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponse, hfield, harguments, hdirectives,
          hchild⟩
        unfold executionSelectionLookupValid
        exact ⟨fieldDefinition, hlookup⟩
      · have hrestLookup :
            ∀ selection,
              selection ∈
                  NormalForm.normalizeSelectionSet schema parentType
                    (NormalForm.withoutFieldSelectionsWithResponseName schema responseName rest) ->
                executionSelectionLookupValid schema parentType selection := by
          simpa [executionSelectionSetLookupValid] using hrest
        exact hrestLookup selection htail
  | case4 parentType rest directives selectionSet happend =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have happendLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType
                  (selectionSet ++ rest) ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using happend
      exact
        happendLookup selection
          (by simpa [NormalForm.normalizeSelectionSet] using hmem)
  | case5 parentType rest typeCondition directives selectionSet hoverlap hrest
      happend =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have happendLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType
                  (selectionSet ++ rest) ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using happend
      exact
        happendLookup selection
          (by simpa [NormalForm.normalizeSelectionSet, hoverlap] using hmem)
  | case6 parentType rest typeCondition directives selectionSet hoverlap hrest =>
      unfold executionSelectionSetLookupValid
      intro selection hmem
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · exact False.elim (hoverlap hmatch)
      have hrestLookup :
          ∀ selection,
            selection ∈
                NormalForm.normalizeSelectionSet schema parentType rest ->
              executionSelectionLookupValid schema parentType selection := by
        simpa [executionSelectionSetLookupValid] using hrest
      exact
        hrestLookup selection
          (by simpa [NormalForm.normalizeSelectionSet, hfalse] using hmem)

theorem collectedGroupsFieldLookupValid_of_generatedNormalizedFieldChild
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> CollectedGroupsFieldLookupValid schema childRuntime
          (GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref)
            childSelectionSet) := by
  intro hschema hinclude hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, _hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType
            sourceSelectionSet := by
      simpa [hobject] using hchild
    simpa [hchildEq] using
      collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
        schema variableValues childType (Execution.ResolverValue.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (executionSelectionSetLookupValid_normalizeSelectionSet schema
          childType sourceSelectionSet)
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    have hpossibleMem : childRuntime ∈ schema.getPossibleTypes childType :=
      List.contains_iff_mem.mp hinclude
    have hobjects :
        ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
          NormalForm.objectTypeNameBool schema objectType = true := by
      intro objectType hobjectType
      exact
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
          schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema childType objectType hobjectType)
    have hpossibleNodup :
        (schema.getPossibleTypes childType).Nodup :=
      SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType
    have hcollect :
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    rw [hchildEq, hcollect]
    exact
      collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
        schema variableValues childRuntime
        (Execution.ResolverValue.object childRuntime ref)
        (NormalForm.normalizeSelectionSet schema childRuntime sourceSelectionSet)
        (executionSelectionSetLookupValid_normalizeSelectionSet schema
          childRuntime sourceSelectionSet)

theorem executeRootSelectionSet_eq_spec_of_allFieldsNormal
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (childReady : Name -> List Selection -> Prop)
    (hchild
      : ∀ childDepth childType runtimeType (ref : ObjectRef) childSelectionSet,
          childDepth < depth
          -> schema.typeIncludesObjectBool childType runtimeType = true
          -> childReady childType childSelectionSet
          -> NormalForm.selectionSetNormal schema childType childSelectionSet
          -> NormalForm.selectionSetDirectiveFree childSelectionSet
          -> executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (Execution.ResolverValue.object runtimeType ref)
                childSelectionSet
              = Execution.executeRootSelectionSet schema resolvers variableValues
                  childDepth runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  childSelectionSet)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.selectionSetNormal schema parentType selectionSet
      -> executionSelectionSetLookupValid schema parentType selectionSet
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> childReady
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                childSelectionSet)
      -> executeRootSelectionSet schema resolvers variableValues depth
            parentType source selectionSet
          = Execution.executeRootSelectionSet schema resolvers variableValues depth
              parentType source selectionSet := by
  intro hall hfree hnormal hlookup hchildren
  cases depth with
  | zero =>
      exact
        (ExecutedGroupedSelectionSetState.depth_zero schema resolvers
          variableValues parentType source selectionSet
          (collectedSelectionSetGroupsSingleton_of_allFields_directiveFree_normal
            schema variableValues parentType source selectionSet hall hfree
            hnormal)).executeRootSelectionSet_eq_spec
  | succ completionDepth =>
      apply executeRootSelectionSet_eq_spec_of_collected_groups_collectedLocalAppendInvariant
        (hcollect := rfl)
        (hflat :=
          (VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_normal
            schema resolvers variableValues completionDepth parentType source
            selectionSet hall hfree hnormal).empty)
        (hcollected :=
          executionCollectedFieldInvariant_of_allFieldsNormal schema resolvers
            variableValues completionDepth parentType source selectionSet hall
            hfree hnormal)
          (hcompatible :=
            collectedGroupsFieldValidationMergeCompatible_of_allFieldsNormal
              schema variableValues parentType source selectionSet hall hfree
              hnormal)
          (hlookups :=
            collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
              schema variableValues parentType source selectionSet hlookup)
          (happend :=
          collectedFieldGroupLocalAppendInvariant_of_allFieldsNormal schema
            resolvers variableValues completionDepth parentType source
            selectionSet childReady
            (by
              intro childDepth childType runtimeType ref childSelectionSet hlt
                hinclude hready hchildNormal hchildFree
              exact hchild childDepth childType runtimeType ref
                childSelectionSet
                (by simpa [Nat.succ_eq_add_one] using hlt)
                hinclude hready hchildNormal hchildFree)
            hall hfree hnormal hchildren)

theorem executeQueryWithFuel_eq_spec_of_allFieldsNormal
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (childReady : Name -> List Selection -> Prop)
    (hchild
      : ∀ childDepth childType runtimeType (ref : ObjectRef) childSelectionSet,
          childDepth < depth
          -> schema.typeIncludesObjectBool childType runtimeType = true
          -> childReady childType childSelectionSet
          -> NormalForm.selectionSetNormal schema childType childSelectionSet
          -> NormalForm.selectionSetDirectiveFree childSelectionSet
          -> executeRootSelectionSet schema resolvers
                (Execution.coerceVariableValues operation variableValues) childDepth
                runtimeType (Execution.ResolverValue.object runtimeType ref)
                childSelectionSet
              = Execution.executeRootSelectionSet schema resolvers
                  (Execution.coerceVariableValues operation variableValues)
                  childDepth runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  childSelectionSet)
    : NormalForm.selectionsAllFields operation.selectionSet
      -> NormalForm.operationDirectiveFree operation
      -> NormalForm.operationNormal schema operation
      -> executionSelectionSetLookupValid schema (operation.rootType schema)
          operation.selectionSet
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ operation.selectionSet
            -> childReady
                ((schema.fieldReturnType? (operation.rootType schema) fieldName).getD
                  fieldName)
                childSelectionSet)
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              depth source := by
  intro hall hfree hnormal hlookup hchildren
  unfold executeQueryWithFuel Execution.executeQueryWithFuel
  by_cases hsource :
      Execution.rootSourceAppliesBool schema operation source = true
  · simp [hsource]
    rw [
      executeRootSelectionSet_eq_spec_of_allFieldsNormal schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet
          childReady hchild hall hfree hnormal hlookup hchildren]
  · simp [hsource]

theorem collectedGroupsFieldValidationMergeCompatible_of_generatedNormalizedFieldChild
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref) childSelectionSet) := by
  intro hschema hinclude hgenerated responseName fields hgroup
  have hnonempty :
      CollectedGroupsFieldsNonempty
        (GraphQL.Execution.collectFields schema variableValues childRuntime
          (Execution.ResolverValue.object childRuntime ref) childSelectionSet) :=
    collectFields_fieldsNonempty schema variableValues childRuntime
      (Execution.ResolverValue.object childRuntime ref) childSelectionSet
  cases fields with
  | nil =>
      exact False.elim (hnonempty responseName [] hgroup rfl)
  | cons field fieldsTail =>
      have htail : fieldsTail = [] :=
        (collectFields_generatedNormalizedFieldChild_prefix_empty schema
          variableValues childType childRuntime ref childSelectionSet hschema
          hinclude hgenerated hgroup
          (prefixTail := ([] : List Execution.ExecutableField))
          (show ∀ candidate : Execution.ExecutableField,
              candidate ∈ ([] : List Execution.ExecutableField) ->
                candidate ∈ fieldsTail from
            by
              intro candidate hmem
              simp at hmem)).1
      subst fieldsTail
      exact executableFieldsFieldValidationMergeCompatible_singleton field

theorem executionCollectedFieldInvariant_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := childRuntime
                source := Execution.ResolverValue.object childRuntime ref
                selectionSet := childSelectionSet
              }
            initial := .object []
          } := by
  intro hschema hinclude hgenerated
  constructor
  · exact PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues childRuntime
        (Execution.ResolverValue.object childRuntime ref) childSelectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        childRuntime (Execution.ResolverValue.object childRuntime ref)
        childSelectionSet)
  · intro responseName fields hgroup
    have hnonempty :
        CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectFields schema variableValues childRuntime
            (Execution.ResolverValue.object childRuntime ref)
            childSelectionSet) :=
      collectFields_fieldsNonempty schema variableValues childRuntime
        (Execution.ResolverValue.object childRuntime ref) childSelectionSet
    cases fields with
    | nil =>
        exact False.elim (hnonempty responseName [] hgroup rfl)
    | cons field fieldsTail =>
        have htail : fieldsTail = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime ref childSelectionSet hschema
            hinclude hgenerated hgroup
            (prefixTail := ([] : List Execution.ExecutableField))
            (show ∀ candidate : Execution.ExecutableField,
                candidate ∈ ([] : List Execution.ExecutableField) ->
                  candidate ∈ fieldsTail from
              by
                intro candidate hmem
                simp at hmem)).1
        subst fieldsTail
        exact executableFieldsResolveStable_singleton resolvers
          (Execution.ResolverValue.object childRuntime ref) field

def selectionSetLocalFreshPrefixInvariants_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> SelectionSetLocalFreshPrefixInvariants schema resolvers variableValues
          depth childRuntime (Execution.ResolverValue.object childRuntime ref)
          childSelectionSet := by
  intro hschema hinclude hgenerated
  exact
    SelectionSetLocalFreshPrefixInvariants.of_freshPrefixDerivation
      (freshPrefixSelectionDerivation_generatedNormalizedFieldChild_runtime
        schema variableValues childType childRuntime ref childSelectionSet
        hschema hinclude hgenerated)
      (executionCollectedFieldInvariant_of_generatedNormalizedFieldChild
        schema resolvers variableValues depth childType childRuntime ref
        childSelectionSet hschema hinclude hgenerated)
      (collectedGroupsFieldValidationMergeCompatible_of_generatedNormalizedFieldChild
        schema variableValues childType childRuntime ref childSelectionSet hschema
        hinclude hgenerated)
      (collectedGroupsFieldLookupValid_of_generatedNormalizedFieldChild
        schema variableValues childType childRuntime ref childSelectionSet
        hschema hinclude hgenerated)
      (by
        intro responseName field fields prefixTail later hgroup hprefix hlater
          childDepth grandchildRuntime grandchildRef hlt
        have hprefixTail : prefixTail = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime ref childSelectionSet hschema
            hinclude hgenerated hgroup hprefix).2
        subst prefixTail
        have hfields : fields = [] :=
          (collectFields_generatedNormalizedFieldChild_prefix_empty schema
            variableValues childType childRuntime ref childSelectionSet hschema
            hinclude hgenerated hgroup
            (prefixTail := ([] : List Execution.ExecutableField))
            (by
              intro candidate hmem
              simp at hmem)).1
        subst fields
        simp at hlater)

def recursiveGroupedSelectionSetState_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> RecursiveGroupedSelectionSetState schema resolvers variableValues depth
          childRuntime (Execution.ResolverValue.object childRuntime ref)
          childSelectionSet := by
  intro hschema hinclude hgenerated
  apply RecursiveGroupedSelectionSetState.of_localFreshPrefixInvariants
    (selectionSetLocalFreshPrefixInvariants_of_generatedNormalizedFieldChild
      schema resolvers variableValues depth childType childRuntime ref
      childSelectionSet hschema hinclude hgenerated)
  intro responseName field fields prefixTail hgroup hprefix childDepth
    grandchildRuntime grandchildRef hlt hgrandchildInclude
  have hgrandchildGenerated :
      generatedNormalizedFieldChild schema
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        field.selectionSet :=
    generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
      schema variableValues childType childRuntime ref childSelectionSet hschema
      hinclude hgenerated hgroup hprefix
  have hprefixTail : prefixTail = [] :=
    (collectFields_generatedNormalizedFieldChild_prefix_empty schema
      variableValues childType childRuntime ref childSelectionSet hschema
      hinclude hgenerated hgroup hprefix).2
  subst prefixTail
  simpa [GraphQL.Execution.mergedFieldSelectionSet] using
    recursiveGroupedSelectionSetState_of_generatedNormalizedFieldChild schema
      resolvers variableValues childDepth
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName)
      grandchildRuntime grandchildRef field.selectionSet hschema
      hgrandchildInclude hgrandchildGenerated
  · intro responseName field fields prefixTail hgroup hprefix
      grandchildRuntime grandchildRef _hlt hgrandchildInclude
    have hgrandchildGenerated :
        generatedNormalizedFieldChild schema
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName)
          field.selectionSet :=
      generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
        schema variableValues childType childRuntime ref childSelectionSet hschema
        hinclude hgenerated hgroup hprefix
    have hprefixTail : prefixTail = [] :=
      (collectFields_generatedNormalizedFieldChild_prefix_empty schema
        variableValues childType childRuntime ref childSelectionSet hschema
        hinclude hgenerated hgroup hprefix).2
    subst prefixTail
    simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
        schema variableValues
        ((schema.fieldReturnType? field.parentType field.fieldName).getD
          field.fieldName)
        grandchildRuntime grandchildRef field.selectionSet hschema
        hgrandchildInclude hgrandchildGenerated
termination_by depth
decreasing_by exact Nat.lt_of_succ_lt hlt

theorem executeRootSelectionSet_eq_spec_of_generatedNormalizedFieldChild
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (childType childRuntime : Name)
    (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> executeRootSelectionSet schema resolvers variableValues depth childRuntime
            (Execution.ResolverValue.object childRuntime ref) childSelectionSet
          = Execution.executeRootSelectionSet schema resolvers variableValues depth
              childRuntime (Execution.ResolverValue.object childRuntime ref)
              childSelectionSet := by
  intro hschema hinclude hgenerated
  cases depth with
  | zero =>
      exact
        (ExecutedGroupedSelectionSetState.depth_zero schema resolvers
          variableValues childRuntime
          (Execution.ResolverValue.object childRuntime ref)
          childSelectionSet
          (collectedSelectionSetGroupsSingleton_of_generatedNormalizedFieldChild
            schema variableValues childType childRuntime ref childSelectionSet
            hschema hinclude hgenerated)).executeRootSelectionSet_eq_spec
  | succ completionDepth =>
      exact
        (recursiveGroupedSelectionSetState_of_generatedNormalizedFieldChild
          schema resolvers variableValues completionDepth childType childRuntime
          ref childSelectionSet hschema hinclude
          hgenerated).executeRootSelectionSet_eq_spec

theorem executeRootSelectionSet_eq_spec_of_normalizeSelectionSet
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> NormalForm.objectTypeNameBool schema parentType = true
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> executeRootSelectionSet schema resolvers variableValues depth parentType
            source (NormalForm.normalizeSelectionSet schema parentType selectionSet)
          = Execution.executeRootSelectionSet schema resolvers variableValues depth
              parentType source
              (NormalForm.normalizeSelectionSet schema parentType selectionSet) := by
  intro hschema hobject hfree
  apply executeRootSelectionSet_eq_spec_of_allFieldsNormal schema resolvers
    variableValues depth parentType source
    (NormalForm.normalizeSelectionSet schema parentType selectionSet)
    (generatedNormalizedFieldChild schema)
  · intro childDepth childType runtimeType ref childSelectionSet _hlt hinclude
      hgenerated _hchildNormal _hchildFree
    exact
      executeRootSelectionSet_eq_spec_of_generatedNormalizedFieldChild schema
        resolvers variableValues childDepth childType runtimeType ref
        childSelectionSet hschema hinclude hgenerated
  · exact
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields schema
        parentType selectionSet
  · exact
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
        schema parentType selectionSet hfree
  · exact
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal schema
        hschema parentType selectionSet hobject
  · exact
      executionSelectionSetLookupValid_normalizeSelectionSet schema parentType
        selectionSet
  · intro responseName fieldName arguments directives childSelectionSet hmem
    exact
      normalizeSelectionSet_field_child_generated schema parentType selectionSet
        responseName fieldName arguments directives childSelectionSet hfree hmem

theorem executeQueryWithFuel_completeNormalizeOperation_eq_of_filter_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> NormalForm.objectTypeNameBool schema (operation.rootType schema) = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType
              = true)
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> NormalForm.selectionSetDirectiveFree
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> executeRootSelectionSet schema resolvers
                  (Execution.coerceVariableValues operation variableValues) depth
                  (operation.rootType schema) source
                  (NormalForm.filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet)
                = Execution.executeRootSelectionSet schema resolvers
                    (Execution.coerceVariableValues operation variableValues)
                    depth (operation.rootType schema) source
                    (NormalForm.filterSelectionSetBoolCase runtimeCase
                      operation.selectionSet))
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hschema hcomplete hobject hsource hfree hready hmerge hsourceSpec
  rcases hsource with ⟨runtimeType, ref, hsourceEq, hinclude⟩
  have hsourceObject :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType =
            true :=
    ⟨runtimeType, ref, hsourceEq, hinclude⟩
  have hroot :
      Execution.rootSourceAppliesBool schema operation source = true := by
    simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
      hsourceEq, hinclude]
  have hrootComplete :
      Execution.rootSourceAppliesBool schema
          (NormalForm.completeNormalizeOperation schema operation) source =
        true := by
    simpa [NormalForm.CompleteNormalization.completeNormalizeOperation_rootSourceAppliesBool]
      using hroot
  rcases
      NormalForm.CompleteNormalization.operationBoolVarsComplete_caseForVariableValues
        (Execution.coerceVariableValues operation variableValues) operation
        hcomplete with
    ⟨runtimeCase, hruntime, hagrees⟩
  let filtered :=
    NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet
  let normalized :=
    NormalForm.normalizeSelectionSet schema (operation.rootType schema) filtered
  have hfilteredRoot :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source filtered
        =
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet := by
    simpa [filtered] using
      executeRootSelectionSet_filterSelectionSetBoolCase_eq schema resolvers
        (Execution.coerceVariableValues operation variableValues) operation
        runtimeCase hagrees depth (operation.rootType schema)
        source operation.selectionSet
        (by
          intro varName hmem
          exact hmem)
  have hfilteredSpec :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source filtered
        =
      Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source filtered := by
    simpa [filtered] using hsourceSpec runtimeCase hruntime hagrees
  have hgroundSpec :
      Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized
        =
      Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source filtered := by
    simpa [Execution.executeSelectionSet, filtered, normalized] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_executeSelectionSet
        schema resolvers (Execution.coerceVariableValues operation variableValues)
        hschema depth (operation.rootType schema) source
        filtered hobject hsourceObject
        (hfree runtimeCase hruntime hagrees)
        (hready runtimeCase hruntime hagrees)
        (hmerge runtimeCase hruntime hagrees)
  have hnormalizedSpec :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized
        =
      Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized := by
    simpa [filtered, normalized] using
      executeRootSelectionSet_eq_spec_of_normalizeSelectionSet schema
        resolvers (Execution.coerceVariableValues operation variableValues)
        depth (operation.rootType schema) source filtered
        hschema hobject (hfree runtimeCase hruntime hagrees)
  have hcompleteRoot :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized := by
    simpa [NormalForm.completeNormalizeOperation, filtered, normalized] using
      executeRootSelectionSet_completeNormalizeRootSelectionSet_runtime schema
        resolvers (Execution.coerceVariableValues operation variableValues)
        operation depth (operation.rootType schema) source
        runtimeCase operation.selectionSet hruntime hagrees
  have hrootResult :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet
        =
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet :=
    hfilteredRoot.symm.trans
      (hfilteredSpec.trans
        (hgroundSpec.symm.trans
          (hnormalizedSpec.symm.trans hcompleteRoot.symm)))
  unfold executeQueryWithFuel
  simp only [hroot, hrootComplete, ↓reduceIte]
  rw [hrootResult]
  simp [Execution.coerceVariableValues, NormalForm.completeNormalizeOperation,
    Operation.rootType, OperationType.rootType]

theorem
    executeQueryWithFuel_completeNormalizeOperation_eq_of_filter_recursiveGroupedStates
    (schema : Schema) (operation : Operation) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> NormalForm.objectTypeNameBool schema (operation.rootType schema) = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType
              = true)
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> NormalForm.selectionSetDirectiveFree
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues) runtimeCase
                (NormalForm.operationBoolVars operation)
            -> RecursiveGroupedSelectionSetState schema resolvers
                (Execution.coerceVariableValues operation variableValues) depth
                (operation.rootType schema) source
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
              source := by
  intro hschema hcomplete hobject hsource hfree hready hmerge hstates
  apply executeQueryWithFuel_completeNormalizeOperation_eq_of_filter_source_eq_spec
    schema operation resolvers variableValues (depth + 1) source hschema
    hcomplete hobject hsource hfree hready hmerge
  intro runtimeCase hruntime hagrees
  exact (hstates runtimeCase hruntime hagrees).executeRootSelectionSet_eq_spec

theorem executeQueryWithFuel_eq_spec_of_generatedNormalOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> NormalForm.selectionsAllFields operation.selectionSet
      -> NormalForm.operationDirectiveFree operation
      -> NormalForm.operationNormal schema operation
      -> executionSelectionSetLookupValid schema (operation.rootType schema)
          operation.selectionSet
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ operation.selectionSet
            -> generatedNormalizedFieldChild schema
                ((schema.fieldReturnType? (operation.rootType schema) fieldName).getD
                  fieldName)
                childSelectionSet)
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              depth source := by
  intro hschema hall hfree hnormal hlookup hchildren
  apply executeQueryWithFuel_eq_spec_of_allFieldsNormal schema operation resolvers
    variableValues depth source (generatedNormalizedFieldChild schema)
  · intro childDepth childType runtimeType ref childSelectionSet _hlt
      hinclude hgenerated _hchildNormal _hchildFree
    exact
      executeRootSelectionSet_eq_spec_of_generatedNormalizedFieldChild schema
        resolvers (Execution.coerceVariableValues operation variableValues)
        childDepth childType runtimeType ref childSelectionSet hschema hinclude
        hgenerated
  · exact hall
  · exact hfree
  · exact hnormal
  · exact hlookup
  · exact hchildren

theorem executeQueryWithFuel_normalizeOperation_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationDirectiveFree operation
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.normalizeOperation schema operation) depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues
              (NormalForm.normalizeOperation schema operation) depth source := by
  intro hschema hvalid hfree
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  apply executeQueryWithFuel_eq_spec_of_generatedNormalOperation schema
    (NormalForm.normalizeOperation schema operation) resolvers variableValues
    depth source hschema
  · simpa [NormalForm.normalizeOperation] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
        schema (operation.rootType schema) operation.selectionSet
  · exact hnormalizedFree
  · exact
      NormalForm.GroundTypeNormalization.normalizeOperation_normal schema
        operation hschema hvalid
  · simpa [NormalForm.normalizeOperation, Operation.rootType,
      OperationType.rootType] using
      executionSelectionSetLookupValid_normalizeSelectionSet schema
        (operation.rootType schema) operation.selectionSet
  · intro responseName fieldName arguments directives childSelectionSet hmem
    exact
      (by
        simpa [NormalForm.normalizeOperation, Operation.rootType,
          OperationType.rootType] using
          normalizeSelectionSet_field_child_generated schema
            (operation.rootType schema) operation.selectionSet responseName fieldName
            arguments directives childSelectionSet hfree
            (by simpa [NormalForm.normalizeOperation] using hmem))

theorem executeQueryWithFuel_eq_spec_of_executeRootSelectionSet_eq
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet
        = Execution.executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) source operation.selectionSet
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              depth source := by
  intro hroot
  unfold executeQueryWithFuel Execution.executeQueryWithFuel
  by_cases hsource :
      Execution.rootSourceAppliesBool schema operation source = true
  · simp [hsource]
    rw [hroot]
  · simp [hsource]

theorem executeQueryWithFuel_eq_spec_depth_zero
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef)
    : CollectedSelectionSetGroupsSingleton schema
        (Execution.coerceVariableValues operation variableValues)
        (operation.rootType schema) source operation.selectionSet
      -> executeQueryWithFuel schema resolvers variableValues operation 0 source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              0 source := by
  intro hsingletons
  by_cases hsource :
      Execution.rootSourceAppliesBool schema operation source = true
  · exact
      ({ root := hsource
         selectionSet :=
          ExecutedGroupedSelectionSetState.depth_zero schema resolvers
            (Execution.coerceVariableValues operation variableValues)
            (operation.rootType schema) source operation.selectionSet
            hsingletons } :
        ExecutedGroupedOperationState schema resolvers
          (Execution.coerceVariableValues operation variableValues) operation 0
          source).executeQueryWithFuel_eq_spec
  · unfold executeQueryWithFuel Execution.executeQueryWithFuel
    simp [hsource]

theorem executeQueryWithFuel_eq_spec_depth_zero_general
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef)
    : executeQueryWithFuel schema resolvers variableValues operation 0 source
      = Execution.executeQueryWithFuel schema resolvers variableValues operation
          0 source := by
  by_cases hsource :
      Execution.rootSourceAppliesBool schema operation source = true
  · exact
      ({ root := hsource
         selectionSet :=
          ExecutedGroupedSelectionSetState.depth_zero_general schema resolvers
            (Execution.coerceVariableValues operation variableValues)
            (operation.rootType schema) source operation.selectionSet } :
        ExecutedGroupedOperationState schema resolvers
          (Execution.coerceVariableValues operation variableValues) operation 0
          source).executeQueryWithFuel_eq_spec
  · unfold executeQueryWithFuel Execution.executeQueryWithFuel
    simp [hsource]

theorem executeRootSelectionSet_completeNormalizeOperation_eq_spec_of_runtime_body
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> executeRootSelectionSet schema resolvers variableValues depth
            (operation.rootType schema) source
            (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
              (NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet))
          = Execution.executeRootSelectionSet schema resolvers variableValues depth
              (operation.rootType schema) source
              (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> executeRootSelectionSet schema resolvers variableValues depth
            (operation.rootType schema) source
            (NormalForm.completeNormalizeOperation schema operation).selectionSet
          = Execution.executeRootSelectionSet schema resolvers variableValues depth
              (operation.rootType schema) source
              (NormalForm.completeNormalizeOperation schema operation).selectionSet := by
  intro hruntime hagrees hbody
  have hungrouped :
      executeRootSelectionSet schema resolvers variableValues depth
          (operation.rootType schema) source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      executeRootSelectionSet schema resolvers variableValues depth
          (operation.rootType schema) source
          (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)) := by
    have hvisit :=
      visitSubfields_completeNormalizeRootSelectionSet_runtime schema
        resolvers variableValues operation depth (operation.rootType schema) source
        runtimeCase operation.selectionSet (Execution.ResponseValue.object [])
        hruntime hagrees
    let toRootResult :
        Execution.ResponseValue × VisitStatus ->
          Execution.Result (List (Name × Execution.ResponseValue)) :=
      fun visited =>
        match visited.snd with
        | Except.error errors => Except.error errors
        | Except.ok (_unit, errors) =>
            match visited.fst with
            | .object fields => Except.ok (fields, errors)
            | _ => Except.error (errors + 1)
    unfold executeRootSelectionSet
    exact congrArg toRootResult hvisit
  have hspec :
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          (operation.rootType schema) source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      Execution.executeRootSelectionSet schema resolvers variableValues depth
          (operation.rootType schema) source
          (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)) := by
    simpa [Execution.executeSelectionSet,
      NormalForm.completeNormalizeOperation] using
      NormalForm.CompleteNormalization.executeSelectionSet_completeNormalizeRootSelectionSet_runtime
        schema resolvers variableValues operation depth (operation.rootType schema)
        source runtimeCase operation.selectionSet hruntime hagrees
  exact hungrouped.trans (hbody.trans hspec.symm)

theorem executeQueryWithFuel_completeNormalizeOperation_eq_spec_of_runtime_body
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          (Execution.coerceVariableValues operation variableValues) runtimeCase
          (NormalForm.operationBoolVars operation)
      -> executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) source
            (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
              (NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet))
          = Execution.executeRootSelectionSet schema resolvers
              (Execution.coerceVariableValues operation variableValues) depth
              (operation.rootType schema) source
              (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hruntime hagrees hbody
  apply executeQueryWithFuel_eq_spec_of_executeRootSelectionSet_eq
  simpa [Execution.coerceVariableValues,
    NormalForm.completeNormalizeOperation, Operation.rootType,
    OperationType.rootType] using
    executeRootSelectionSet_completeNormalizeOperation_eq_spec_of_runtime_body
      schema operation resolvers
      (Execution.coerceVariableValues operation variableValues) depth source runtimeCase
      hruntime hagrees hbody

theorem executeQueryWithFuel_completeNormalizeOperation_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> NormalForm.objectTypeNameBool schema (operation.rootType schema) = true
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hschema hcomplete hobject
  rcases
      NormalForm.CompleteNormalization.operationBoolVarsComplete_caseForVariableValues
        (Execution.coerceVariableValues operation variableValues) operation
        hcomplete with
    ⟨runtimeCase, hruntime, hagrees⟩
  apply executeQueryWithFuel_completeNormalizeOperation_eq_spec_of_runtime_body
    schema operation resolvers variableValues depth source runtimeCase hruntime
    hagrees
  apply executeRootSelectionSet_eq_spec_of_normalizeSelectionSet schema resolvers
    (Execution.coerceVariableValues operation variableValues) depth
    (operation.rootType schema) source
    (NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet)
    hschema hobject
  exact NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
    schema runtimeCase operation.selectionSet

theorem specExecution_eq_ungroupedExecution_of_completeNormalizeOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> NormalForm.objectTypeNameBool schema (operation.rootType schema) = true
      -> Execution.executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hschema hcomplete hobject
  exact (executeQueryWithFuel_completeNormalizeOperation_eq_spec schema
    operation resolvers variableValues depth source hschema hcomplete hobject).symm

theorem executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              depth source := by
  intro hschema hvalid hcomplete
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hrootObjectBool :
      NormalForm.objectTypeNameBool schema (operation.rootType schema) = true :=
    NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
      schema hrootObject
  have hcompleteUngrouped :
      executeQueryWithFuel schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source :=
    executeQueryWithFuel_completeNormalizeOperation_eq_spec schema operation
      resolvers variableValues depth source hschema hcomplete hrootObjectBool
  have hcompleteSpec :
      Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) depth source :=
    by
      exact
        NormalForm.CompleteNormalization.completeNormalizationEffectiveSemanticsPreserved
          schema operation hschema hvalid resolvers variableValues depth source
          hcomplete
  exact hcompleteUngrouped.trans hcompleteSpec.symm

theorem completeNormalizationPreservesUngroupedExecutionSemantics
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues depth (source : Execution.ResolverValue ObjectRef),
          NormalForm.operationBoolVarsComplete operation
            (Execution.coerceVariableValues operation variableValues)
          -> executeQueryWithFuel schema resolvers variableValues
                (NormalForm.completeNormalizeOperation schema operation) depth source
              = Execution.executeQueryWithFuel schema resolvers variableValues operation
                  depth source := by
  intro hschema hvalid ObjectRef resolvers variableValues depth source hcomplete
  exact executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete

theorem executeQueryWithFuel_responseEquivalent_of_rootSelectionResult
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : Execution.rootSourceAppliesBool schema operation source = true
      -> RootSelectionResultDataAndErrorPresenceEquivalent
          (executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) source operation.selectionSet)
          (Execution.executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) source operation.selectionSet)
      -> responseDataAndErrorPresenceEquivalent
          (executeQueryWithFuel schema resolvers variableValues operation depth source)
          (Execution.executeQueryWithFuel schema resolvers variableValues
            operation depth source) := by
  intro hroot hrootResult
  unfold RootSelectionResultDataAndErrorPresenceEquivalent at hrootResult
  unfold ErrorPresenceEquivalent at hrootResult
  rcases hrootResult with ⟨hdata, hzero, hpositive⟩
  unfold executeQueryWithFuel Execution.executeQueryWithFuel
  cases hleft :
      executeRootSelectionSet schema resolvers
        (Execution.coerceVariableValues operation variableValues) depth
        (operation.rootType schema) source operation.selectionSet <;>
    cases hright :
      Execution.executeRootSelectionSet schema resolvers
        (Execution.coerceVariableValues operation variableValues) depth
        (operation.rootType schema) source operation.selectionSet <;>
    simp [hroot, hleft, hright, responseDataAndErrorPresenceEquivalent,
      Execution.selectionSetResultToResponse, rootSelectionResultData,
      resultErrorCount] at hdata hzero hpositive ⊢
  · exact ⟨hzero, hpositive⟩
  · exact ⟨hdata, hzero, hpositive⟩

theorem executeQueryWithFuel_responseEquivalent_of_ungroupedRootSelectionResult
    (schema : Schema) (leftOperation rightOperation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : Execution.rootSourceAppliesBool schema leftOperation source = true
      -> Execution.rootSourceAppliesBool schema rightOperation source = true
      -> RootSelectionResultDataAndErrorPresenceEquivalent
          (executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues leftOperation variableValues) depth
            (leftOperation.rootType schema) source leftOperation.selectionSet)
          (executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues rightOperation variableValues) depth
            (rightOperation.rootType schema) source rightOperation.selectionSet)
      -> responseDataAndErrorPresenceEquivalent
          (executeQueryWithFuel schema resolvers variableValues leftOperation
            depth source)
          (executeQueryWithFuel schema resolvers variableValues rightOperation
            depth source) := by
  intro hleftRoot hrightRoot hrootResult
  unfold RootSelectionResultDataAndErrorPresenceEquivalent at hrootResult
  unfold ErrorPresenceEquivalent at hrootResult
  rcases hrootResult with ⟨hdata, hzero, hpositive⟩
  unfold executeQueryWithFuel
  cases hleft :
      executeRootSelectionSet schema resolvers
        (Execution.coerceVariableValues leftOperation variableValues) depth
        (leftOperation.rootType schema) source leftOperation.selectionSet <;>
    cases hright :
      executeRootSelectionSet schema resolvers
        (Execution.coerceVariableValues rightOperation variableValues) depth
        (rightOperation.rootType schema) source rightOperation.selectionSet <;>
    simp [hleftRoot, hrightRoot, hleft, hright,
      responseDataAndErrorPresenceEquivalent,
      Execution.selectionSetResultToResponse, rootSelectionResultData,
      resultErrorCount] at hdata hzero hpositive ⊢
  · exact ⟨hzero, hpositive⟩
  · exact ⟨hdata, hzero, hpositive⟩

theorem
    executeQueryWithFuel_completeNormalizeOperation_responseEquivalent_of_filter_source_rootEquivalent
    (schema : Schema) (operation : Operation) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> NormalForm.objectTypeNameBool schema (operation.rootType schema) = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType
              = true)
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues)
                runtimeCase
                (NormalForm.operationBoolVars operation)
            -> NormalForm.selectionSetDirectiveFree
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues)
                runtimeCase
                (NormalForm.operationBoolVars operation)
            -> NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues)
                runtimeCase
                (NormalForm.operationBoolVars operation)
            -> FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
                (NormalForm.filterSelectionSetBoolCase runtimeCase
                  operation.selectionSet))
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues)
                runtimeCase
                (NormalForm.operationBoolVars operation)
            -> RootSelectionResultDataAndErrorPresenceEquivalent
                (executeRootSelectionSet schema resolvers
                  (Execution.coerceVariableValues operation variableValues) depth
                  (operation.rootType schema) source
                  (NormalForm.filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet))
                (Execution.executeRootSelectionSet schema resolvers
                  (Execution.coerceVariableValues operation variableValues) depth
                  (operation.rootType schema) source
                  (NormalForm.filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet)))
      -> responseDataAndErrorPresenceEquivalent
          (executeQueryWithFuel schema resolvers variableValues operation depth source)
          (executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth
            source) := by
  intro hschema hcomplete hobject hsource hfree hready hmerge hsourceRoot
  rcases hsource with ⟨runtimeType, ref, hsourceEq, hinclude⟩
  have hsourceObject :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType =
            true :=
    ⟨runtimeType, ref, hsourceEq, hinclude⟩
  have hroot :
      Execution.rootSourceAppliesBool schema operation source = true := by
    simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
      hsourceEq, hinclude]
  have hrootComplete :
      Execution.rootSourceAppliesBool schema
          (NormalForm.completeNormalizeOperation schema operation) source =
        true := by
    simpa [NormalForm.CompleteNormalization.completeNormalizeOperation_rootSourceAppliesBool]
      using hroot
  rcases
      NormalForm.CompleteNormalization.operationBoolVarsComplete_caseForVariableValues
        (Execution.coerceVariableValues operation variableValues) operation
        hcomplete with
    ⟨runtimeCase, hruntime, hagrees⟩
  let filtered :=
    NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet
  let normalized :=
    NormalForm.normalizeSelectionSet schema (operation.rootType schema) filtered
  have hfilteredRoot :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source filtered
        =
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet := by
    simpa [filtered] using
      executeRootSelectionSet_filterSelectionSetBoolCase_eq schema resolvers
        (Execution.coerceVariableValues operation variableValues) operation
        runtimeCase hagrees depth (operation.rootType schema)
        source operation.selectionSet
        (by
          intro varName hmem
          exact hmem)
  have hfilteredSpec :
      RootSelectionResultDataAndErrorPresenceEquivalent
        (executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) source filtered)
        (Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source filtered) := by
    simpa [filtered] using hsourceRoot runtimeCase hruntime hagrees
  have hgroundSpec :
      Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized
        =
      Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source filtered := by
    simpa [Execution.executeSelectionSet, filtered, normalized] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_executeSelectionSet
        schema resolvers
        (Execution.coerceVariableValues operation variableValues) hschema depth
        (operation.rootType schema) source filtered hobject hsourceObject
        (hfree runtimeCase hruntime hagrees)
        (hready runtimeCase hruntime hagrees)
        (hmerge runtimeCase hruntime hagrees)
  have hnormalizedSpec :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized
        =
      Execution.executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized := by
    simpa [filtered, normalized] using
      executeRootSelectionSet_eq_spec_of_normalizeSelectionSet schema
        resolvers (Execution.coerceVariableValues operation variableValues)
        depth (operation.rootType schema) source filtered
        hschema hobject (hfree runtimeCase hruntime hagrees)
  have hcompleteRoot :
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source
          (NormalForm.completeNormalizeOperation schema operation).selectionSet
        =
      executeRootSelectionSet schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source normalized := by
    simpa [NormalForm.completeNormalizeOperation, filtered, normalized] using
      executeRootSelectionSet_completeNormalizeRootSelectionSet_runtime schema
        resolvers (Execution.coerceVariableValues operation variableValues)
        operation depth (operation.rootType schema) source runtimeCase
        operation.selectionSet hruntime hagrees
  have hrootResult :
      RootSelectionResultDataAndErrorPresenceEquivalent
        (executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) source operation.selectionSet)
        (executeRootSelectionSet schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) source
            (NormalForm.completeNormalizeOperation schema operation).selectionSet) :=
    RootSelectionResultDataAndErrorPresenceEquivalent.trans
      (RootSelectionResultDataAndErrorPresenceEquivalent.of_eq
        hfilteredRoot.symm)
      (RootSelectionResultDataAndErrorPresenceEquivalent.trans hfilteredSpec
        (RootSelectionResultDataAndErrorPresenceEquivalent.trans
          (RootSelectionResultDataAndErrorPresenceEquivalent.of_eq
            hgroundSpec.symm)
          (RootSelectionResultDataAndErrorPresenceEquivalent.trans
            (RootSelectionResultDataAndErrorPresenceEquivalent.of_eq
              hnormalizedSpec.symm)
            (RootSelectionResultDataAndErrorPresenceEquivalent.of_eq
              hcompleteRoot.symm))))
  apply
    executeQueryWithFuel_responseEquivalent_of_ungroupedRootSelectionResult
      schema operation (NormalForm.completeNormalizeOperation schema operation)
      resolvers variableValues depth source hroot hrootComplete
  simpa [Execution.coerceVariableValues,
    NormalForm.completeNormalizeOperation, Operation.rootType,
    OperationType.rootType] using hrootResult

theorem ungroupedExecutionPreservesSpecExecution_proof
    (schema : Schema) (operation : Operation)
    : ungroupedExecutionPreservesSpecExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues depth source
    hcomplete
  by_cases hroot :
      Execution.rootSourceAppliesBool schema operation source = true
  · have hrootObject : schema.objectType (operation.rootType schema) :=
      by
        have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
        rw [hrootEq]
        exact hschema.2.1
    have hoperationReady :
        NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
          operation.selectionSet :=
      NormalForm.selectionSetSemanticsReady_of_selectionSetValid_object schema
        operation.variableDefinitions (operation.rootType schema) hschema hrootObject
        operation.selectionSet
        (Validation.operationDefinitionValid_selectionSetValid hvalid)
    have hobjectBool :
        NormalForm.objectTypeNameBool schema (operation.rootType schema) = true :=
      NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
        schema hrootObject
    have hsourceObject :
        ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
            ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType =
              true :=
      NormalForm.GroundTypeNormalization.rootSourceAppliesBool_true_object
        schema operation source hroot
    have hbridge :
        responseDataAndErrorPresenceEquivalent
          (executeQueryWithFuel schema resolvers variableValues operation depth
            source)
          (executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth
            source) := by
      apply
        executeQueryWithFuel_completeNormalizeOperation_responseEquivalent_of_filter_source_rootEquivalent
          schema operation resolvers variableValues depth source hschema
          hcomplete hobjectBool hsourceObject
      · intro runtimeCase _hruntime _hagrees
        exact
          NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
            schema runtimeCase operation.selectionSet
      · intro runtimeCase _hruntime _hagrees
        exact
          NormalForm.CompleteNormalization.selectionSetSemanticsReady_filterSelectionSetBoolCase
            schema runtimeCase (operation.rootType schema) operation.selectionSet
            hoperationReady
      · intro runtimeCase _hruntime _hagrees
        exact
          NormalForm.CompleteNormalization.fieldsInSetCanMerge_filterSelectionSetBoolCase_forSemantics
            schema runtimeCase
            (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
      · intro runtimeCase _hruntime _hagrees
        rcases hsourceObject with ⟨runtimeType, ref, hsourceEq, hinclude⟩
        have hparentRuntime :
            ScopedParentRuntimeApplies schema runtimeType (operation.rootType schema) :=
          ScopedParentRuntimeApplies.of_typeIncludesObjectBool schema runtimeType
            (operation.rootType schema) hinclude
        have hfilteredReady :
            NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
              (NormalForm.filterSelectionSetBoolCase runtimeCase
                operation.selectionSet) :=
          NormalForm.CompleteNormalization.selectionSetSemanticsReady_filterSelectionSetBoolCase
            schema runtimeCase (operation.rootType schema) operation.selectionSet
            hoperationReady
        have hfilteredMerge :
            FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
              (NormalForm.filterSelectionSetBoolCase runtimeCase
                operation.selectionSet) :=
          NormalForm.CompleteNormalization.fieldsInSetCanMerge_filterSelectionSetBoolCase_forSemantics
            schema runtimeCase
            (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
        have hstate :=
          executedGroupedSelectionSetAlignedState_of_selectionSetSemanticsReady_object
            schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema) runtimeType ref
            (NormalForm.filterSelectionSetBoolCase runtimeCase
              operation.selectionSet)
            hschema hrootObject hparentRuntime hfilteredReady hfilteredMerge
        simpa [hsourceEq] using hstate.executeRootSelectionSet_responseEquivalent
    have hnormalized :
        executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth source =
          Execution.executeQueryWithFuel schema resolvers variableValues operation
            depth source :=
      executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved
        schema operation resolvers variableValues depth source hschema hvalid
        hcomplete
    exact
      responseDataAndErrorPresenceEquivalent_trans hbridge
        (responseDataAndErrorPresenceEquivalent_of_eq hnormalized)
  · apply responseDataAndErrorPresenceEquivalent_of_eq
    unfold executeQueryWithFuel Execution.executeQueryWithFuel
    simp [hroot]

theorem completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              depth source
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hschema hvalid hcomplete hsource
  have hnormalized :
      executeQueryWithFuel schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues operation
        depth source :=
    executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved
      schema operation resolvers variableValues depth source hschema hvalid
      hcomplete
  exact hsource.trans hnormalized.symm

theorem completeNormalizationPreservesUngroupedExecution_of_executedGroupedOperationState
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (state
      : ExecutedGroupedOperationState schema resolvers
          (Execution.coerceVariableValues operation variableValues) operation
          depth source)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hschema hvalid hcomplete
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete
  exact state.executeQueryWithFuel_eq_spec

theorem
    completeNormalizationPreservesUngroupedExecution_of_collected_groups_recursiveAppendState
    (schema : Schema) (operation : Operation) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    {groups : List (Name × List Execution.ExecutableField)}
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (hcollect
      : Execution.collectFields schema
          (Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema) source operation.selectionSet
        = groups)
    (hflat
      : VisitSubfieldsFlatCollects schema resolvers
          (Execution.coerceVariableValues operation variableValues) (depth + 1)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hcollected
      : ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  Execution.coerceVariableValues operation variableValues
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
      : CollectedFieldGroupRecursiveAppendState schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth groups)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
              source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_executedGroupedOperationState
        schema operation resolvers variableValues (depth + 1) source
        (ExecutedGroupedOperationState.of_collected_groups_recursiveAppendState
          hroot hcollect hflat hcollected hlookups hcompatible happend)
        hschema hvalid hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (state
      : RecursiveGroupedOperationState schema resolvers
          (Execution.coerceVariableValues operation variableValues) operation
          depth source)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
              source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_executedGroupedOperationState
      schema operation resolvers variableValues (depth + 1) source
      state.toExecutedGroupedOperationState hschema hvalid hcomplete

theorem
    executeQueryWithFuel_semanticsPreserved_via_completeNormalization_of_recursiveGroupedOperationState
    (schema : Schema) (operation : Operation) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (state
      : RecursiveGroupedOperationState schema resolvers
          (Execution.coerceVariableValues operation variableValues) operation
          depth source)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              (depth + 1) source := by
  intro hschema hvalid hcomplete
  have hpreserved :
      executeQueryWithFuel schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryWithFuel schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source :=
    completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
      schema operation resolvers variableValues depth source state hschema
      hvalid hcomplete
  have hnormalized :
      executeQueryWithFuel schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
          source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues operation
        (depth + 1) source :=
    executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved schema
      operation resolvers variableValues (depth + 1) source hschema hvalid
      hcomplete
  exact hpreserved.trans hnormalized

theorem completeNormalizationPreservesUngroupedExecution_of_globalInvariants
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (invariants
      : RecursiveSelectionSetGlobalInvariants schema resolvers
          (Execution.coerceVariableValues operation variableValues))
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
              source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_recursiveGroupedOperationState
      schema operation resolvers variableValues depth source
      (RecursiveGroupedOperationState.of_globalInvariants hroot invariants)
      hschema hvalid hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_globalFreshPrefixInvariants
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (invariants
      : RecursiveSelectionSetGlobalFreshPrefixInvariants schema resolvers
          (Execution.coerceVariableValues operation variableValues))
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
              source := by
  intro hschema hvalid hcomplete
  exact
    completeNormalizationPreservesUngroupedExecution_of_globalInvariants
      schema operation resolvers variableValues depth source hroot
      invariants.toGlobalInvariants hschema hvalid hcomplete

theorem executeQueryWithFuel_semanticsPreserved_of_globalFreshPrefixInvariants
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (invariants
      : RecursiveSelectionSetGlobalFreshPrefixInvariants schema resolvers
          (Execution.coerceVariableValues operation variableValues))
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              (depth + 1) source := by
  intro hschema hvalid hcomplete
  have hpreserved :
      executeQueryWithFuel schema resolvers variableValues operation (depth + 1)
          source
        =
      executeQueryWithFuel schema resolvers variableValues
        (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
        source :=
    completeNormalizationPreservesUngroupedExecution_of_globalFreshPrefixInvariants
      schema operation resolvers variableValues depth source hroot invariants
      hschema hvalid hcomplete
  have hnormalized :
      executeQueryWithFuel schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
          source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues operation
        (depth + 1) source :=
    executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved schema
      operation resolvers variableValues (depth + 1) source hschema hvalid
      hcomplete
  exact hpreserved.trans hnormalized

theorem completeNormalizationPreservesUngroupedExecution_iff_source_eq_spec
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcomplete
      : NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues))
    : (executeQueryWithFuel schema resolvers variableValues operation depth source
        = executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema operation) depth source)
      ↔ executeQueryWithFuel schema resolvers variableValues operation depth source
        = Execution.executeQueryWithFuel schema resolvers variableValues operation
            depth source := by
  have hnormalized :
      executeQueryWithFuel schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema operation) depth source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues operation
        depth source :=
    executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved
      schema operation resolvers variableValues depth source hschema hvalid
      hcomplete
  constructor
  · intro hpreserved
    exact hpreserved.trans hnormalized
  · intro hsource
    exact hsource.trans hnormalized.symm

theorem completeNormalizationPreservesUngroupedExecution_iff_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    : (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
          variableValues depth (source : Execution.ResolverValue ObjectRef),
        NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
        -> executeQueryWithFuel schema resolvers variableValues operation depth source
            = executeQueryWithFuel schema resolvers variableValues
                (NormalForm.completeNormalizeOperation schema operation) depth
                source)
      ↔ (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues depth (source : Execution.ResolverValue ObjectRef),
          NormalForm.operationBoolVarsComplete operation
            (Execution.coerceVariableValues operation variableValues)
          -> executeQueryWithFuel schema resolvers variableValues operation depth source
              = Execution.executeQueryWithFuel schema resolvers variableValues
                  operation depth source) := by
  constructor
  · intro hpreserved ObjectRef resolvers variableValues depth source hcomplete
    exact
      (completeNormalizationPreservesUngroupedExecution_iff_source_eq_spec
        schema operation resolvers variableValues depth source hschema hvalid
        hcomplete).mp
        (hpreserved resolvers variableValues depth source hcomplete)
  · intro hsemantics ObjectRef resolvers variableValues depth source hcomplete
    exact
      (completeNormalizationPreservesUngroupedExecution_iff_source_eq_spec
        schema operation resolvers variableValues depth source hschema hvalid
        hcomplete).mpr
        (hsemantics resolvers variableValues depth source hcomplete)

theorem completeNormalizationPreservesUngroupedExecution_of_source_semanticsPreserved
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues depth (source : Execution.ResolverValue ObjectRef),
            NormalForm.operationBoolVarsComplete operation
              (Execution.coerceVariableValues operation variableValues)
            -> executeQueryWithFuel schema resolvers variableValues operation depth source
                = Execution.executeQueryWithFuel schema resolvers variableValues
                    operation depth source)
      -> ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
            variableValues depth (source : Execution.ResolverValue ObjectRef),
          NormalForm.operationBoolVarsComplete operation
            (Execution.coerceVariableValues operation variableValues)
          -> executeQueryWithFuel schema resolvers variableValues operation depth source
              = executeQueryWithFuel schema resolvers variableValues
                  (NormalForm.completeNormalizeOperation schema operation) depth
                  source := by
  intro hschema hvalid hsourceSemantics ObjectRef resolvers variableValues
    depth source hcomplete
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete
  exact hsourceSemantics resolvers variableValues depth source hcomplete

theorem completeNormalizationPreservesUngroupedExecution_of_generatedNormalOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationBoolVarsComplete operation
          (Execution.coerceVariableValues operation variableValues)
      -> NormalForm.selectionsAllFields operation.selectionSet
      -> NormalForm.operationDirectiveFree operation
      -> NormalForm.operationNormal schema operation
      -> executionSelectionSetLookupValid schema (operation.rootType schema)
          operation.selectionSet
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ operation.selectionSet
            -> generatedNormalizedFieldChild schema
                ((schema.fieldReturnType? (operation.rootType schema) fieldName).getD
                  fieldName)
                childSelectionSet)
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hschema hvalid hcomplete hall hfree hnormal hlookup hchildren
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema operation resolvers variableValues depth source hschema hvalid
    hcomplete
  exact executeQueryWithFuel_eq_spec_of_generatedNormalOperation schema
    operation resolvers variableValues depth source hschema hall hfree hnormal
    hlookup hchildren

theorem completeNormalizationPreservesUngroupedExecution_of_normalizeOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationFieldsValidInPossibleTypes schema operation
      -> NormalForm.operationDirectiveFree operation
      -> NormalForm.selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema
      -> Validation.operationVariablesUsed
          (NormalForm.normalizeOperation schema operation)
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.normalizeOperation schema operation) depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema
                (NormalForm.normalizeOperation schema operation)) depth source := by
  intro hschema hvalid hfields hfree hfeasibleAll hvariablesUsed
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hready :
      NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    NormalForm.selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  have hnormalizedNonempty :
      NormalForm.normalizeSelectionSet schema (operation.rootType schema)
        operation.selectionSet ≠ [] :=
    NormalForm.GroundTypeNormalization.normalizeSelectionSet_ne_nil_of_everyNormalizerScope
      schema hfeasibleAll (operation.rootType schema) operation.selectionSet hrootObject
      hready (Validation.operationDefinitionValid_selectionSet_nonempty hvalid)
  have hnormalizedValid :
      Validation.operationDefinitionValid schema
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_valid_of_operationFieldsValid schema
      operation hschema hvalid hfields hfree hfeasibleAll hnormalizedNonempty
      hvariablesUsed
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema (NormalForm.normalizeOperation schema operation) resolvers
    variableValues depth source hschema hnormalizedValid
    (NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
      (NormalForm.normalizeOperation schema operation)
      (Execution.coerceVariableValues
        (NormalForm.normalizeOperation schema operation) variableValues)
      hnormalizedFree)
  exact executeQueryWithFuel_normalizeOperation_eq_spec schema operation
    resolvers variableValues depth source hschema hvalid hfree

theorem normalizeThenCompleteUngroupedExecution_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationFieldsValidInPossibleTypes schema operation
      -> NormalForm.operationDirectiveFree operation
      -> NormalForm.selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema
      -> Validation.operationVariablesUsed
          (NormalForm.normalizeOperation schema operation)
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema
              (NormalForm.normalizeOperation schema operation)) depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              depth source := by
  intro hschema hvalid hfields hfree hfeasibleAll hvariablesUsed
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hready :
      NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    NormalForm.selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  have hnormalizedNonempty :
      NormalForm.normalizeSelectionSet schema (operation.rootType schema)
        operation.selectionSet ≠ [] :=
    NormalForm.GroundTypeNormalization.normalizeSelectionSet_ne_nil_of_everyNormalizerScope
      schema hfeasibleAll (operation.rootType schema) operation.selectionSet hrootObject
      hready (Validation.operationDefinitionValid_selectionSet_nonempty hvalid)
  have hnormalizedValid :
      Validation.operationDefinitionValid schema
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_valid_of_operationFieldsValid schema
      operation hschema hvalid hfields hfree hfeasibleAll hnormalizedNonempty
      hvariablesUsed
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  have hcomplete :
      NormalForm.operationBoolVarsComplete
        (NormalForm.normalizeOperation schema operation)
        (Execution.coerceVariableValues
          (NormalForm.normalizeOperation schema operation) variableValues) :=
    NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
      (NormalForm.normalizeOperation schema operation)
      (Execution.coerceVariableValues
        (NormalForm.normalizeOperation schema operation) variableValues)
      hnormalizedFree
  have hcompleteUngrouped :
      executeQueryWithFuel schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema
            (NormalForm.normalizeOperation schema operation)) depth source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues
        (NormalForm.normalizeOperation schema operation) depth source :=
    executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved schema
      (NormalForm.normalizeOperation schema operation) resolvers
      variableValues depth source hschema hnormalizedValid hcomplete
  have hgroundSpec :
      Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues
        (NormalForm.normalizeOperation schema operation) depth source :=
    by
      exact
        NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation
          schema operation hschema hvalid hfree resolvers variableValues depth
          source
  exact hcompleteUngrouped.trans hgroundSpec.symm

end Eager

theorem ungroupedExecutionPreservesSpecExecution_proof
    (schema : Schema) (operation : Operation)
    : ungroupedExecutionPreservesSpecExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues fuel source hcomplete
  exact
    Eager.responseDataAndErrorPresenceEquivalent_trans
      (executeQueryWithFuel_canceling_eager_responseEquivalent schema resolvers
        variableValues operation fuel source)
      (Eager.ungroupedExecutionPreservesSpecExecution_proof schema operation
        hschema hvalid resolvers variableValues fuel source hcomplete)

theorem ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof
    (schema : Schema) (operation : Operation)
    : ungroupedExecutionEquivalentToCancelingSiblingsExecution schema operation := by
  intro hschema hvalid ObjectRef resolvers variableValues fuel source hcomplete
  have hungroupedSpec :=
    ungroupedExecutionPreservesSpecExecution_proof schema operation
      hschema hvalid resolvers variableValues fuel source hcomplete
  have hcancelingSpec :=
    ExecutionCancelingSiblings.siblingCancelingExecutionPreservesSpecExecution_proof
      schema operation resolvers variableValues fuel source
  unfold responseDataAndErrorPresenceEquivalent at hungroupedSpec ⊢
  unfold ExecutionCancelingSiblings.responseDataAndErrorPresenceEquivalent at hcancelingSpec
  rcases hungroupedSpec with
    ⟨hungroupedData, hungroupedZero, hungroupedPositive⟩
  rcases hcancelingSpec with
    ⟨hcancelingData, hcancelingZero, hcancelingPositive⟩
  constructor
  · exact hungroupedData.trans hcancelingData.symm
  constructor
  · intro hcancelingErrorsZero
    rcases Nat.eq_zero_or_pos
        (Execution.executeQueryWithFuel schema resolvers variableValues operation
          fuel source).errors with hspecErrorsZero | hspecErrorsPositive
    · exact hungroupedZero hspecErrorsZero
    · exfalso
      exact
        (Nat.ne_of_gt (hcancelingPositive hspecErrorsPositive))
          hcancelingErrorsZero
  · intro hcancelingErrorsPositive
    rcases Nat.eq_zero_or_pos
        (Execution.executeQueryWithFuel schema resolvers variableValues operation
          fuel source).errors with hspecErrorsZero | hspecErrorsPositive
    · exfalso
      exact
        (Nat.ne_of_gt hcancelingErrorsPositive)
          (hcancelingZero hspecErrorsZero)
    · exact hungroupedPositive hspecErrorsPositive

end ExecutionUngroupedUncached
end Algorithms

end GraphQL
