import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.FreshPrefixPlan

/-!
Fresh-plan normalization witnesses for group-list selection sets.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance groupListFreshPlanNormalizesResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

structure SelectionSetFreshPlanNormalizes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (raw normalized : List Selection)
    : Prop where
  collect_eq
    : GraphQL.Execution.collectFields schema variableValues parentType source raw
      = GraphQL.Execution.collectFields schema variableValues parentType source normalized
  rawFreshFlat
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source raw
  normalizedPlan
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source normalized

namespace SelectionSetFreshPlanNormalizes

open FreshPrefixSelectionDerivation

private def keyedExecutableFieldsOfGroups
    : List (Name × List ExecutableField) -> List KeyedExecutableField
  | [] => []
  | (responseName, fields) :: rest =>
      fields.map
        (fun field =>
          { toExecutableField := field, responseName := responseName })
      ++ keyedExecutableFieldsOfGroups rest

private theorem keyedExecutableFieldSelections_keyedExecutableFieldsOfGroups
    : ∀ groups,
        keyedExecutableFieldSelections (keyedExecutableFieldsOfGroups groups)
        = collectedExecutableSelections groups
  | [] => rfl
  | (responseName, fields) :: rest => by
      simp only [keyedExecutableFieldsOfGroups,
        keyedExecutableFieldSelections, List.map_append,
        collectedExecutableSelections]
      rw [show List.map keyedExecutableFieldSelection
            (keyedExecutableFieldsOfGroups rest) =
          keyedExecutableFieldSelections (keyedExecutableFieldsOfGroups rest) from rfl]
      rw [keyedExecutableFieldSelections_keyedExecutableFieldsOfGroups rest]
      simp [keyedExecutableFieldSelection, executableFieldSelections,
        Function.comp_def]

private theorem map_toExecutableField_keyedExecutableFieldsOfGroups
    : ∀ groups,
        (keyedExecutableFieldsOfGroups groups).map KeyedExecutableField.toExecutableField
        = collectedExecutableFields groups
  | [] => rfl
  | (responseName, fields) :: rest => by
      simp [keyedExecutableFieldsOfGroups, collectedExecutableFields,
        map_toExecutableField_keyedExecutableFieldsOfGroups rest,
        List.map_append, Function.comp_def]

private theorem length_keyedExecutableFieldsOfGroups
    : ∀ groups,
        (keyedExecutableFieldsOfGroups groups).length
        = (collectedExecutableFields groups).length
  | [] => rfl
  | (responseName, fields) :: rest => by
      simp [keyedExecutableFieldsOfGroups, collectedExecutableFields,
        length_keyedExecutableFieldsOfGroups rest]

private theorem
    collectedExecutableFields_collectFields_keyedExecutableFieldSelections_length
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ fields : List KeyedExecutableField,
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (keyedExecutableFieldSelections fields))).length
        = fields.length
  | [] => by
      simp [keyedExecutableFieldSelections, GraphQL.Execution.collectFields,
        collectedExecutableFields]
  | field :: rest => by
      simp only [keyedExecutableFieldSelections, List.map_cons,
        GraphQL.Execution.collectFields]
      rw [show keyedExecutableFieldSelection field =
          executableFieldSelection field.responseName field.toExecutableField by rfl]
      rw [collectSelection_executableFieldSelection schema variableValues
        parentType source field.responseName field.toExecutableField]
      rw [collectedExecutableFields_mergeExecutableGroups_length]
      rw [show List.map keyedExecutableFieldSelection rest =
          keyedExecutableFieldSelections rest by rfl]
      rw [collectedExecutableFields_collectFields_keyedExecutableFieldSelections_length
        schema variableValues parentType source rest]
      simp [collectedExecutableFields, Nat.add_comm]

private theorem keyedExecutableFieldSelections_lookupValid
    (schema : Schema) (parentType : Name)
    (fields : List KeyedExecutableField)
    (hlookups
      : ∀ field,
          field ∈ fields
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    : executionSelectionSetLookupValid schema parentType
        (keyedExecutableFieldSelections fields) := by
  unfold executionSelectionSetLookupValid
  intro selection hselection
  rcases List.mem_map.mp hselection with ⟨field, hfield, rfl⟩
  simpa [keyedExecutableFieldSelection, executableFieldSelection,
    executionSelectionLookupValid] using hlookups field hfield

theorem nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source [] [] :=
  let plan :=
    FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
  {
    collect_eq := rfl
    rawFreshFlat := FreshPrefixSelectionPlan.freshFlat plan
    normalizedPlan := plan
  }

theorem of_plan
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (plan
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source selectionSet)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet :=
  {
    collect_eq := rfl
    rawFreshFlat := FreshPrefixSelectionPlan.freshFlat plan
    normalizedPlan := plan
  }

theorem of_derivation
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (derivation
      : FreshPrefixSelectionDerivation schema variableValues parentType source
          selectionSet)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet :=
  of_plan
    (FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
      completionDepth parentType source derivation)

theorem of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (htree
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet :=
  of_plan
    (FreshPrefixSelectionPlan.of_headDisjointTree schema resolvers
      variableValues completionDepth parentType source selectionSet htree)

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet))
        (collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet)) :=
  of_plan
    (FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
      variableValues completionDepth parentType source selectionSet)

theorem of_rawFreshFlat_collectedCollectFields
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw : List Selection}
    (hrawFreshFlat
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source raw)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source raw
        (collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
            source raw)) :=
  {
    collect_eq :=
      (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source raw).symm
    rawFreshFlat := hrawFreshFlat
    normalizedPlan :=
      FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
        variableValues completionDepth parentType source raw
  }

theorem of_derivation_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (derivation
      : FreshPrefixSelectionDerivation schema variableValues parentType source
          selectionSet)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source selectionSet
        (collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet)) :=
  of_rawFreshFlat_collectedCollectFields
    (FreshPrefixSelectionPlan.freshFlat
      (FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
        completionDepth parentType source derivation))

theorem of_normalizeSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionSetDirectiveFree selectionSet
      -> SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (NormalForm.normalizeSelectionSet schema parentType selectionSet)
          (NormalForm.normalizeSelectionSet schema parentType selectionSet) :=
  fun hfree =>
    of_plan
      (FreshPrefixSelectionPlan.of_normalizeSelectionSet schema resolvers
        variableValues completionDepth parentType source selectionSet hfree)

theorem trans
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw middle normalized : List Selection}
    (left
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source raw middle)
    (right
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source middle normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source raw normalized :=
  {
    collect_eq := by
      rw [left.collect_eq, right.collect_eq]
    rawFreshFlat := left.rawFreshFlat
    normalizedPlan := right.normalizedPlan
  }

theorem appendDisjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {rawLeft rawRight normalizedLeft normalizedRight : List Selection}
    (left
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rawLeft normalizedLeft)
    (right
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rawRight normalizedRight)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            rawLeft)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            rawRight))
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source (rawLeft ++ rawRight)
        (normalizedLeft ++ normalizedRight) := by
  have hnormalizedDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedLeft)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedRight) := by
    intro responseName hleft hright
    exact hdisjoint responseName
      (by rwa [left.collect_eq])
      (by rwa [right.collect_eq])
  exact {
    collect_eq := by
      rw [GraphQL.NormalForm.collectFields_append]
      rw [GraphQL.NormalForm.collectFields_append]
      rw [left.collect_eq, right.collect_eq]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint schema
        resolvers variableValues (completionDepth + 1) parentType source
        rawLeft rawRight hdisjoint left.rawFreshFlat right.rawFreshFlat
    normalizedPlan :=
      FreshPrefixSelectionPlan.appendDisjoint normalizedLeft normalizedRight
        left.normalizedPlan right.normalizedPlan hnormalizedDisjoint
  }

theorem consDisjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selection : Selection} {rest normalizedSelection normalizedRest : List Selection}
    (head
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source [selection] normalizedSelection)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rest normalizedRest)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [selection])
          (GraphQL.Execution.collectFields schema variableValues parentType source rest))
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source (selection :: rest)
        (normalizedSelection ++ normalizedRest) := by
  simpa using
    appendDisjoint (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      (rawLeft := [selection]) (rawRight := rest)
      (normalizedLeft := normalizedSelection)
      (normalizedRight := normalizedRest) head tail hdisjoint

theorem field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet]
        [.field responseName fieldName arguments directives selectionSet] :=
  of_headDisjointTree schema resolvers variableValues completionDepth
    parentType source
    (by
      have htree :
          SelectionSetCollectFieldsHeadDisjoint schema variableValues
              parentType source
              [.field responseName fieldName arguments directives selectionSet]
            ∧
            (∀ selection,
              selection ∈
                  [.field responseName fieldName arguments directives
                    selectionSet] ->
                SelectionCollectFieldsHeadDisjointTree schema variableValues
                  parentType source selection) := by
        constructor
        · constructor
          · intro _candidate _hleft hright
            simp [GraphQL.Execution.collectFields] at hright
          · simp [SelectionSetCollectFieldsHeadDisjoint]
        · intro selection hselection
          simp at hselection
          subst selection
          simp [SelectionCollectFieldsHeadDisjointTree]
      simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree)

theorem of_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List FreshPrefixSelectionDerivation.KeyedExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections fields)
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections fields) :=
  of_plan
    (FreshPrefixSelectionPlan.of_executableFieldSelections_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source fields
      hnodup)

theorem fieldAllowedDropDirectives
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet]
        [.field responseName fieldName arguments [] selectionSet] :=
  {
    collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hallows,
        selectionDirectivesAllowBool_empty]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_field_single schema resolvers
        variableValues (completionDepth + 1) parentType source responseName
        fieldName arguments directives selectionSet
    normalizedPlan :=
      (SelectionSetFreshPlanNormalizes.field schema resolvers variableValues
        completionDepth parentType source responseName fieldName arguments []
        selectionSet).normalizedPlan
  }

theorem fieldSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet] [] :=
  {
    collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hskip]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_field_single schema resolvers
        variableValues (completionDepth + 1) parentType source responseName
        fieldName arguments directives selectionSet
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
  }

theorem executablePrefixFieldConsAllowed {ObjectIdentity : Type} {schema : Schema}
    {resolvers : Resolvers ObjectIdentity} {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixSelections : List Selection) (responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest normalized : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (prefixSelections
            ++ executableFieldSelections responseName
                [executableField fieldName arguments selectionSet]
            ++ rest)
          normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (prefixSelections
          ++ Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
        normalized :=
  {
    collect_eq := by
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hallows,
        executableFieldSelections, executableFieldSelection, executableField,
        selectionDirectivesAllowBool_empty, GraphQL.NormalForm.collectFields_append,
        List.append_assoc]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_allowed
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixSelections responseName fieldName arguments directives selectionSet
        rest hallows tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem executablePrefixFieldConsSkipped {ObjectIdentity : Type} {schema : Schema}
    {resolvers : Resolvers ObjectIdentity} {variableValues : VariableValues}
    {completionDepth : Nat} {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixSelections : List Selection) (responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest normalized : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (prefixSelections ++ rest)
          normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (prefixSelections
          ++ Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
        normalized :=
  {
    collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hskip, hmergeNil, GraphQL.NormalForm.collectFields_append,
        List.append_assoc] using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixSelections responseName fieldName arguments directives selectionSet
        rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem inlineFragmentNone
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (child
      : selectionDirectivesAllowBool variableValues directives = true
        -> SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source rawChild normalizedChild)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment none directives rawChild]
        [.inlineFragment none directives normalizedChild] := by
  refine {
    collect_eq := ?_
    rawFreshFlat := ?_
    normalizedPlan := ?_
  }
  · by_cases hallows :
        selectionDirectivesAllowBool variableValues directives = true
    · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows, (child hallows).collect_eq]
    · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows]
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild
        (fun hallows => (child hallows).rawFreshFlat)
  · exact
      FreshPrefixSelectionPlan.consDisjoint
        (.inlineFragment none directives normalizedChild) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          directives normalizedChild
          (fun hallows => (child hallows).normalizedPlan.freshFlat))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)

theorem inlineFragmentNoneFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (child
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rawChild normalizedChild)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment none directives rawChild] normalizedChild :=
  {
    collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows, child.collect_eq,
        GraphQL.Execution.mergeExecutableGroups]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild (fun _hallows => child.rawFreshFlat)
    normalizedPlan := child.normalizedPlan
  }

theorem inlineFragmentNoneConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source (rawChild ++ rest) normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment none directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hallows]
        using (by simpa [GraphQL.NormalForm.collectFields_append] using tail.collect_eq)
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_allowed
        schema resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild rest hallows tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem inlineFragmentNoneConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rest normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment none directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hskip,
        hmergeNil]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        directives rawChild rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem inlineFragmentNoneCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication)
    (rawChild rest : List Selection)
    (normalizeAllowed
      : selectionDirectivesAllowBool variableValues directives = true
        -> ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source (rawChild ++ rest)
              normalized)
    (normalizeSkipped
      : selectionDirectivesAllowBool variableValues directives = false
        -> ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source rest normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (Selection.inlineFragment none directives rawChild :: rest)
          normalized := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · rcases normalizeAllowed hallows with ⟨normalized, hnormalized⟩
    exact ⟨normalized, inlineFragmentNoneConsFlatten directives hallows hnormalized⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rcases normalizeSkipped hskip with ⟨normalized, hnormalized⟩
    exact ⟨
      normalized,
      inlineFragmentNoneConsSkipped directives rawChild hskip hnormalized
    ⟩

theorem normalizeSelectionSet_inlineFragmentNoneCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (rawChild rest : List Selection)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source (rawChild ++ rest)
          (GraphQL.NormalForm.normalizeSelectionSet schema parentType (rawChild ++ rest)))
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment none [] rawChild :: rest)
        (GraphQL.NormalForm.normalizeSelectionSet schema parentType
          (Selection.inlineFragment none [] rawChild :: rest)) := by
  simpa [GraphQL.NormalForm.normalizeSelectionSet]
    using inlineFragmentNoneConsFlatten (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source) [] rfl
      (rawChild := rawChild) (rest := rest) tail

theorem inlineFragmentNoneSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment none directives selectionSet] [] :=
  {
    collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hskip]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        directives selectionSet
        (by
          intro hallows
          rw [hskip] at hallows
          contradiction)
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
  }

theorem inlineFragmentSome
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (child
      : selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source rawChild normalizedChild)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives rawChild]
        [.inlineFragment (some typeCondition) directives normalizedChild] := by
  refine {
    collect_eq := ?_
    rawFreshFlat := ?_
    normalizedPlan := ?_
  }
  · by_cases hallows :
        selectionDirectivesAllowBool variableValues directives = true
    · by_cases happly :
          doesFragmentTypeApplyBool schema parentType source typeCondition = true
      · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
          hallows, happly, (child hallows happly).collect_eq]
      · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
          hallows, happly]
    · simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows]
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild
        (fun hallows happly => (child hallows happly).rawFreshFlat)
  · exact
      FreshPrefixSelectionPlan.consDisjoint
        (.inlineFragment (some typeCondition) directives normalizedChild) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          typeCondition directives normalizedChild
          (fun hallows happly =>
            (child hallows happly).normalizedPlan.freshFlat))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)

theorem inlineFragmentSomeFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    (child
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rawChild normalizedChild)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives rawChild]
        normalizedChild :=
  {
    collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        hallows, happly, child.collect_eq,
        GraphQL.Execution.mergeExecutableGroups]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild
        (fun _hallows _happly => child.rawFreshFlat)
    normalizedPlan := child.normalizedPlan
  }

theorem inlineFragmentSomeConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source (rawChild ++ rest) normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment (some typeCondition) directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hallows,
        happly]
        using (by simpa [GraphQL.NormalForm.collectFields_append] using tail.collect_eq)
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_allowed_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild rest hallows happly tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem inlineFragmentSomeConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rest normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment (some typeCondition) directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hskip,
        hmergeNil]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem inlineFragmentSomeConsDoesNotApply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rest normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment (some typeCondition) directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hallows,
        hnotApply, hmergeNil]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_not_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives rawChild rest hallows hnotApply
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem inlineFragmentSomeCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild rest : List Selection)
    (normalizeApplies
      : selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source (rawChild ++ rest)
              normalized)
    (normalizeSkipped
      : selectionDirectivesAllowBool variableValues directives = false
        -> ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source rest normalized)
    (normalizeDoesNotApply
      : selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = false
        -> ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source rest normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (Selection.inlineFragment (some typeCondition) directives rawChild :: rest)
          normalized := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · rcases normalizeApplies hallows happly with
        ⟨normalized, hnormalized⟩
      exact ⟨
        normalized,
        inlineFragmentSomeConsFlatten typeCondition directives hallows happly hnormalized
      ⟩
    · have hnotApply :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases h :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      rcases normalizeDoesNotApply hallows hnotApply with
        ⟨normalized, hnormalized⟩
      exact ⟨
        normalized,
        inlineFragmentSomeConsDoesNotApply typeCondition directives
          rawChild hallows hnotApply hnormalized
      ⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    rcases normalizeSkipped hskip with ⟨normalized, hnormalized⟩
    exact ⟨
      normalized,
      inlineFragmentSomeConsSkipped typeCondition directives rawChild hskip hnormalized
    ⟩

theorem normalizeSelectionSet_inlineFragmentSomeCons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (rawChild rest : List Selection)
    (hfragment
      : doesFragmentTypeApplyBool schema parentType source typeCondition
        = schema.typesOverlapBool parentType typeCondition)
    (normalizeApplies
      : schema.typesOverlapBool parentType typeCondition = true
        -> SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source (rawChild ++ rest)
            (GraphQL.NormalForm.normalizeSelectionSet schema parentType
              (rawChild ++ rest)))
    (normalizeDoesNotApply
      : schema.typesOverlapBool parentType typeCondition = false
        -> SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source rest
            (GraphQL.NormalForm.normalizeSelectionSet schema parentType rest))
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (Selection.inlineFragment (some typeCondition) [] rawChild :: rest)
        (GraphQL.NormalForm.normalizeSelectionSet schema parentType
          (Selection.inlineFragment (some typeCondition) [] rawChild :: rest)) := by
  by_cases hoverlap :
      schema.typesOverlapBool parentType typeCondition = true
  · have happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          true := by
      rw [hfragment, hoverlap]
    simpa [GraphQL.NormalForm.normalizeSelectionSet, hoverlap]
      using inlineFragmentSomeConsFlatten (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues) (completionDepth := completionDepth)
        (parentType := parentType) (source := source) typeCondition []
        rfl happly (rawChild := rawChild) (rest := rest)
        (normalizeApplies hoverlap)
  · have hoverlapFalse :
        schema.typesOverlapBool parentType typeCondition = false := by
      cases h :
          schema.typesOverlapBool parentType typeCondition
      · rfl
      · contradiction
    have hnotApply :
        doesFragmentTypeApplyBool schema parentType source typeCondition =
          false := by
      rw [hfragment, hoverlapFalse]
    simpa [GraphQL.NormalForm.normalizeSelectionSet, hoverlapFalse]
      using inlineFragmentSomeConsDoesNotApply (schema := schema)
        (resolvers := resolvers) (variableValues := variableValues)
        (completionDepth := completionDepth) (parentType := parentType)
        (source := source) typeCondition [] rawChild rfl hnotApply
        (normalizeDoesNotApply hoverlapFalse)

theorem executablePrefixInlineFragmentNoneConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixSelections : List Selection)
    (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (prefixSelections ++ rawChild ++ rest)
          normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (prefixSelections ++ Selection.inlineFragment none directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hallows,
        GraphQL.NormalForm.collectFields_append, List.append_assoc]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_allowed
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixSelections directives rawChild rest hallows tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem executablePrefixInlineFragmentNoneConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixSelections : List Selection)
    (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (prefixSelections ++ rest) normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (prefixSelections ++ Selection.inlineFragment none directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hskip,
        hmergeNil, GraphQL.NormalForm.collectFields_append, List.append_assoc]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixSelections directives rawChild rest hskip tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem executablePrefixInlineFragmentSomeConsFlatten
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixSelections : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    {rawChild rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (prefixSelections ++ rawChild ++ rest)
          normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (prefixSelections
          ++ Selection.inlineFragment (some typeCondition) directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hallows,
        happly, GraphQL.NormalForm.collectFields_append, List.append_assoc]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_allowed_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixSelections typeCondition directives rawChild rest hallows happly
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem executablePrefixInlineFragmentSomeConsSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixSelections : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (prefixSelections ++ rest) normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (prefixSelections
          ++ Selection.inlineFragment (some typeCondition) directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hskip,
        hmergeNil, GraphQL.NormalForm.collectFields_append, List.append_assoc]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_skipped
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixSelections typeCondition directives rawChild rest hskip
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem executablePrefixInlineFragmentSomeConsDoesNotApply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixSelections : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (rawChild : List Selection) {rest normalized : List Selection}
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    (tail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (prefixSelections ++ rest) normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (prefixSelections
          ++ Selection.inlineFragment (some typeCondition) directives rawChild :: rest)
        normalized :=
  {
    collect_eq := by
      have hmergeNil :
          GraphQL.Execution.mergeExecutableGroups []
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
            =
          GraphQL.Execution.collectFields schema variableValues parentType
            source rest :=
        GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source rest)
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection, hallows,
        hnotApply, hmergeNil, GraphQL.NormalForm.collectFields_append, List.append_assoc]
        using tail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_not_apply
        schema resolvers variableValues (completionDepth + 1) parentType source
        prefixSelections typeCondition directives rawChild rest hallows hnotApply
        tail.rawFreshFlat
    normalizedPlan := tail.normalizedPlan
  }

theorem inlineFragmentSomeSkipped
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (hskip : selectionDirectivesAllowBool variableValues directives = false)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives selectionSet] [] :=
  {
    collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hskip]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives selectionSet
        (by
          intro hallows _happly
          rw [hskip] at hallows
          contradiction)
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
  }

theorem inlineFragmentSomeDoesNotApply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        [.inlineFragment (some typeCondition) directives selectionSet] [] :=
  {
    collect_eq := by
      simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups, hallows, hnotApply]
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
        resolvers variableValues (completionDepth + 1) parentType source
        typeCondition directives selectionSet
        (by
          intro _hallows happly
          rw [hnotApply] at happly
          contradiction)
    normalizedPlan :=
      FreshPrefixSelectionPlan.nil (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
  }

theorem executableFieldConsFresh
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (field : FreshPrefixSelectionDerivation.KeyedExecutableField)
    (rest normalizedRest : List Selection)
    (hfresh
      : field.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType source
            rest).map
            Prod.fst)
    (hrest
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source rest normalizedRest)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelection field :: rest)
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections [field]
          ++ normalizedRest) := by
  apply consDisjoint
  · simpa [FreshPrefixSelectionDerivation.keyedExecutableFieldSelections,
      FreshPrefixSelectionDerivation.keyedExecutableFieldSelection,
      executableFieldSelections, executableFieldSelection]
      using SelectionSetFreshPlanNormalizes.field schema resolvers variableValues
        completionDepth parentType source field.responseName field.fieldName
        field.arguments [] field.selectionSet
  · exact hrest
  · intro responseName hhead htail
    have hheadEq : responseName = field.responseName := by
      simpa [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
        GraphQL.Execution.mergeExecutableGroups,
        FreshPrefixSelectionDerivation.keyedExecutableFieldSelection,
        executableFieldSelection, selectionDirectivesAllowBool_empty]
        using hhead
    exact hfresh (by simpa [hheadEq] using htail)

theorem executableFieldConsFreshNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (field : FreshPrefixSelectionDerivation.KeyedExecutableField)
    (restFields : List FreshPrefixSelectionDerivation.KeyedExecutableField)
    (normalizedRest : List Selection)
    (hfresh : field.responseName ∉ restFields.map (fun field => field.responseName))
    (hrest
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections restFields)
          normalizedRest)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections
          (field :: restFields))
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections [field]
          ++ normalizedRest) := by
  have hfreshCollect :
      field.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections
            restFields)).map Prod.fst := by
    intro hmem
    exact hfresh
      ((FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source restFields
        field.responseName).mp hmem)
  simpa [FreshPrefixSelectionDerivation.keyedExecutableFieldSelections]
    using executableFieldConsFresh (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues) (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      field
      (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections restFields)
      normalizedRest
      hfreshCollect hrest

theorem executableFieldSinglePrefixDuplicateFreshMiddle
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : FreshPrefixSelectionDerivation.KeyedExecutableField)
    (middle : List FreshPrefixSelectionDerivation.KeyedExecutableField)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hmiddleNodup : (middle.map (fun field => field.responseName)).Nodup)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections
          ([first] ++ (middle ++ [later])))
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections
          ([first] ++ [later] ++ middle)) := by
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections middle)).map
            Prod.fst := by
    intro hmem
    have hfieldMem :
        first.responseName ∈ middle.map (fun field => field.responseName) :=
      (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middle first.responseName).mp
        hmem
    exact hnotMiddle (by simpa [hsameResponse] using hfieldMem)
  have hmiddlePlan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections middle) :=
    FreshPrefixSelectionPlan.of_executableFieldSelections_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source middle
      hmiddleNodup
  have hpairCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections first.responseName
            [first.toExecutableField, later.toExecutableField]) =
        [(first.responseName, [first.toExecutableField, later.toExecutableField])] :=
    collectFields_executableFieldSelections_same_group schema variableValues
      parentType source first.responseName
      [first.toExecutableField, later.toExecutableField]
  have hpairMiddleDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections first.responseName
            [first.toExecutableField, later.toExecutableField]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections middle)) := by
    intro responseName hleft hright
    rw [hpairCollect] at hleft
    simp at hleft
    have hmiddleMem :
        responseName ∈ middle.map (fun field => field.responseName) :=
      (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middle responseName).mp
        hright
    exact hnotMiddle (by simpa [hsameResponse, hleft] using hmiddleMem)
  refine {
    collect_eq := ?_
    rawFreshFlat := ?_
    normalizedPlan := ?_
  }
  · exact
      collectFields_executableFieldSelections_single_prefix_duplicate_fresh_middle
        schema variableValues parentType source first later middle
        hsameResponse hmiddleNodup hnotMiddle
  · have hraw :
        VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections first.responseName [first.toExecutableField] ++
            FreshPrefixSelectionDerivation.keyedExecutableFieldSelections middle ++
            executableFieldSelections first.responseName [later.toExecutableField]) :=
      VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
        resolvers variableValues completionDepth parentType source
        first.responseName first.toExecutableField later.toExecutableField
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections middle)
        hlaterLookup
        hnotMiddleCollect hmiddlePlan.freshFlat
    simpa [FreshPrefixSelectionDerivation.keyedExecutableFieldSelections,
      FreshPrefixSelectionDerivation.keyedExecutableFieldSelection,
      executableFieldSelections, hsameResponse, List.map_append, List.append_assoc]
      using hraw
  · have hnormalizedPlan :
        FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          (executableFieldSelections first.responseName
              [first.toExecutableField, later.toExecutableField] ++
            FreshPrefixSelectionDerivation.keyedExecutableFieldSelections middle) :=
      FreshPrefixSelectionPlan.appendDisjoint
        (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
        (executableFieldSelections first.responseName
          [first.toExecutableField, later.toExecutableField])
        (FreshPrefixSelectionDerivation.keyedExecutableFieldSelections middle)
        (.sameGroup first.responseName
          [first.toExecutableField, later.toExecutableField])
        hmiddlePlan
        hpairMiddleDisjoint
    simpa [FreshPrefixSelectionDerivation.keyedExecutableFieldSelections,
      FreshPrefixSelectionDerivation.keyedExecutableFieldSelection,
      executableFieldSelections, hsameResponse, List.append_assoc]
      using hnormalizedPlan

theorem executableFieldPrefixDuplicateFreshMiddle
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections responseName prefixFields
          ++ middle
          ++ executableFieldSelections responseName [later])
        (executableFieldSelections responseName (prefixFields ++ [later])
          ++ collectedExecutableSelections
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle)) := by
  let collectedMiddle :=
    collectedExecutableSelections
      (GraphQL.Execution.collectFields schema variableValues parentType
        source middle)
  have hprefixCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections responseName (prefixFields ++ [later])) =
        [(responseName, prefixFields ++ [later])] := by
    cases prefixFields with
    | nil =>
        contradiction
    | cons firstPrefix restPrefix =>
        simpa using
          collectFields_executableFieldSelections_same_group schema
            variableValues parentType source responseName
            ((firstPrefix :: restPrefix) ++ [later])
  have hmiddleCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle =
        GraphQL.Execution.collectFields schema variableValues parentType source
          middle := by
    dsimp [collectedMiddle]
    exact
      collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source middle
  have hprefixMiddleDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections responseName (prefixFields ++ [later])))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle) := by
    intro candidate hleft hright
    rw [hprefixCollect] at hleft
    rw [hmiddleCollect] at hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  refine {
    collect_eq := ?_
    rawFreshFlat := ?_
    normalizedPlan := ?_
  }
  · simpa [collectedMiddle]
      using collectFields_group_duplicate_field_middle_append_eq_collected_middle
        schema variableValues parentType source responseName prefixFields later
        middle [] hprefixNonempty hnotMiddle
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
        schema resolvers variableValues completionDepth parentType source
        responseName prefixFields later middle hprefixNonempty
        hlaterLookup hnotMiddle hmiddle
  · have hnormalizedPlan :
        FreshPrefixSelectionPlan schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections responseName (prefixFields ++ [later]) ++
            collectedMiddle) :=
      FreshPrefixSelectionPlan.appendDisjoint
        (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth)
        (parentType := parentType) (source := source)
        (executableFieldSelections responseName (prefixFields ++ [later]))
        collectedMiddle
        (.sameGroup responseName (prefixFields ++ [later]))
        (FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
          variableValues completionDepth parentType source middle)
        hprefixMiddleDisjoint
    simpa [collectedMiddle] using hnormalizedPlan

theorem duplicateFieldPrefixBlockNormalizeTrans_of_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField)
    (middle suffix normalizedMiddle normalizedTail : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source middle normalizedMiddle)
    (htail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections responseName (prefixFields ++ [later])
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix)
          normalizedTail)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections responseName prefixFields
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        normalizedTail :=
  {
    collect_eq := by
      calc
        GraphQL.Execution.collectFields schema variableValues parentType source
              ((executableFieldSelections responseName prefixFields
                  ++ middle
                  ++ executableFieldSelections responseName [later])
                ++ suffix)
            = GraphQL.Execution.collectFields schema variableValues parentType source
                ((executableFieldSelections responseName (prefixFields ++ [later])
                    ++ collectedExecutableSelections
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source middle))
                  ++ suffix) :=
          collectFields_group_duplicate_field_middle_append_eq_collected_middle
            schema variableValues parentType source responseName prefixFields
            later middle suffix hprefixNonempty
            hnotMiddle
        _ = GraphQL.Execution.collectFields schema variableValues parentType source
              normalizedTail :=
          htail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_group_duplicate_field_middle_append_of_normalized
        schema resolvers variableValues completionDepth parentType source responseName
        prefixFields later middle suffix hprefixNonempty hlaterLookup hnotMiddle
        hmiddle.rawFreshFlat htail.rawFreshFlat
    normalizedPlan := htail.normalizedPlan
  }

theorem duplicateFieldBlockNormalize
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (middle suffix : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source middle)
    (hnormalized
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix))
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        ((executableFieldSelections responseName [first, later]
            ++ collectedExecutableSelections
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source middle))
          ++ suffix) :=
  {
    collect_eq :=
      collectFields_duplicate_field_middle_append_eq_collected_middle schema
        variableValues parentType source responseName first later middle suffix
        hnotMiddle
    rawFreshFlat :=
      (FreshPrefixSelectionPlan.duplicateFieldBlockNormalize responseName first later
        middle suffix hlaterLookup hnotMiddle hmiddle hnormalized).freshFlat
    normalizedPlan := hnormalized
  }

theorem duplicateFieldBlockNormalizeTrans
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (first later : ExecutableField)
    (middle suffix normalizedTail : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source middle)
    (hnormalized
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix))
    (htail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix)
          normalizedTail)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        normalizedTail :=
  trans
    (duplicateFieldBlockNormalize schema resolvers variableValues
      completionDepth parentType source responseName first later middle suffix
      hlaterLookup hnotMiddle hmiddle hnormalized)
    htail

theorem duplicateFieldBlockNormalizeTrans_of_middleNormalizes {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat} {parentType : Name}
    {source : ResolverValue ObjectIdentity} (responseName : Name)
    (first later : ExecutableField)
    (middle suffix normalizedMiddle normalizedTail : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source middle normalizedMiddle)
    (htail
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix)
          normalizedTail)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        normalizedTail :=
  {
    collect_eq := by
      calc
        GraphQL.Execution.collectFields schema variableValues parentType source
              ((executableFieldSelections responseName [first]
                  ++ middle
                  ++ executableFieldSelections responseName [later])
                ++ suffix)
            = GraphQL.Execution.collectFields schema variableValues parentType source
                ((executableFieldSelections responseName [first, later]
                    ++ collectedExecutableSelections
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source middle))
                  ++ suffix) :=
          collectFields_duplicate_field_middle_append_eq_collected_middle
            schema variableValues parentType source responseName first later middle suffix
            hnotMiddle
        _ = GraphQL.Execution.collectFields schema variableValues parentType source
              normalizedTail :=
          htail.collect_eq
    rawFreshFlat :=
      VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_normalized
        schema resolvers variableValues completionDepth parentType source responseName
        first later middle suffix hlaterLookup hnotMiddle
        hmiddle.rawFreshFlat htail.rawFreshFlat
    normalizedPlan := htail.normalizedPlan
  }

theorem executableFieldDuplicateBlockNormalizeTrans
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : KeyedExecutableField)
    (middleFields suffixFields : List KeyedExecutableField)
    (normalized : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle : first.responseName ∉ middleFields.map (fun field => field.responseName))
    (hmiddle
      : FreshPrefixSelectionDerivation schema variableValues parentType source
          (keyedExecutableFieldSelections middleFields))
    (hintermediatePlan
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          ((executableFieldSelections first.responseName
                [first.toExecutableField, later.toExecutableField]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (keyedExecutableFieldSelections middleFields)))
            ++ keyedExecutableFieldSelections suffixFields))
    (hnormalized
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections first.responseName
                [first.toExecutableField, later.toExecutableField]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (keyedExecutableFieldSelections middleFields)))
            ++ keyedExecutableFieldSelections suffixFields)
          normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (keyedExecutableFieldSelections
          (first :: (middleFields ++ later :: suffixFields)))
        normalized := by
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (keyedExecutableFieldSelections middleFields)).map Prod.fst := by
    intro hmem
    exact hnotMiddle
      ((FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middleFields
        first.responseName).mp hmem)
  have hmiddlePlan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source (keyedExecutableFieldSelections middleFields) :=
    FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
      completionDepth parentType source hmiddle
  simpa [keyedExecutableFieldSelections, keyedExecutableFieldSelection,
    executableFieldSelections, hsameResponse, List.map_append, List.append_assoc]
    using duplicateFieldBlockNormalizeTrans (schema := schema)
      (resolvers := resolvers) (variableValues := variableValues)
      (completionDepth := completionDepth) (parentType := parentType)
      (source := source) first.responseName first.toExecutableField
      later.toExecutableField (keyedExecutableFieldSelections middleFields)
      (keyedExecutableFieldSelections suffixFields) normalized
      hlaterLookup hnotMiddleCollect hmiddlePlan hintermediatePlan hnormalized

theorem executableFieldDuplicateBlockNormalizeTrans_of_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first later : KeyedExecutableField)
    (middleFields suffixFields : List KeyedExecutableField)
    (normalizedMiddle normalized : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle : first.responseName ∉ middleFields.map (fun field => field.responseName))
    (hmiddle
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (keyedExecutableFieldSelections middleFields) normalizedMiddle)
    (hnormalized
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections first.responseName
                [first.toExecutableField, later.toExecutableField]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (keyedExecutableFieldSelections middleFields)))
            ++ keyedExecutableFieldSelections suffixFields)
          normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (keyedExecutableFieldSelections
          (first :: (middleFields ++ later :: suffixFields)))
        normalized := by
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (keyedExecutableFieldSelections middleFields)).map Prod.fst := by
    intro hmem
    exact hnotMiddle
      ((FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middleFields
        first.responseName).mp hmem)
  simpa [keyedExecutableFieldSelections, keyedExecutableFieldSelection,
    executableFieldSelections, hsameResponse, List.map_append, List.append_assoc]
    using duplicateFieldBlockNormalizeTrans_of_middleNormalizes (schema := schema)
      (resolvers := resolvers) (variableValues := variableValues)
      (completionDepth := completionDepth) (parentType := parentType)
      (source := source) first.responseName first.toExecutableField
      later.toExecutableField (keyedExecutableFieldSelections middleFields)
      (keyedExecutableFieldSelections suffixFields) normalizedMiddle normalized
      hlaterLookup hnotMiddleCollect hmiddle hnormalized

theorem executableFieldPrefixDuplicateBlockNormalizeTrans_of_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : KeyedExecutableField)
    (middleFields suffixFields : List KeyedExecutableField)
    (normalizedMiddle normalized : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hlaterResponse : later.responseName = responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle : responseName ∉ middleFields.map (fun field => field.responseName))
    (hmiddle
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (keyedExecutableFieldSelections middleFields) normalizedMiddle)
    (hnormalized
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections responseName
                (prefixFields ++ [later.toExecutableField])
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (keyedExecutableFieldSelections middleFields)))
            ++ keyedExecutableFieldSelections suffixFields)
          normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections responseName prefixFields
          ++ keyedExecutableFieldSelections (middleFields ++ later :: suffixFields))
        normalized := by
  have hnotMiddleCollect :
      responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (keyedExecutableFieldSelections middleFields)).map Prod.fst := by
    intro hmem
    exact hnotMiddle
      ((FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middleFields responseName).mp
        hmem)
  simpa [keyedExecutableFieldSelections, keyedExecutableFieldSelection,
    executableFieldSelections, hlaterResponse, List.map_append, List.append_assoc]
    using duplicateFieldPrefixBlockNormalizeTrans_of_middleNormalizes
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues)
      (completionDepth := completionDepth) (parentType := parentType)
      (source := source) responseName prefixFields later.toExecutableField
      (keyedExecutableFieldSelections middleFields)
      (keyedExecutableFieldSelections suffixFields) normalizedMiddle normalized
      hprefixNonempty hlaterLookup
      hnotMiddleCollect hmiddle hnormalized

theorem executableFieldPrefixNormalizesOfCases_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (rest : List KeyedExecutableField)
    (hprefixNonempty : prefixFields ≠ [])
    (hrestLookups
      : ∀ field,
          field ∈ rest
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfresh
      : responseName ∉ rest.map (fun field => field.responseName)
        -> ∃ normalizedRest,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (keyedExecutableFieldSelections rest) normalizedRest)
    (hmiddle
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = responseName
          -> responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalizedMiddle,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (keyedExecutableFieldSelections middle) normalizedMiddle)
    (hduplicate
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = responseName
          -> responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalized,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                ((executableFieldSelections responseName
                      (prefixFields ++ [later.toExecutableField])
                    ++ collectedExecutableSelections
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source
                          (keyedExecutableFieldSelections middle)))
                  ++ keyedExecutableFieldSelections suffix)
                normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections responseName prefixFields
            ++ keyedExecutableFieldSelections rest) normalized := by
  by_cases hmem :
      responseName ∈ rest.map (fun field => field.responseName)
  · rcases
      FreshPrefixSelectionDerivation.executableFields_first_responseName_split
        responseName rest hmem with
      ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
    have hlaterLookup :
        ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
          some fieldDefinition := by
      exact hrestLookups later (by
        rw [hsplit]
        simp)
    rcases hmiddle middle later suffix hsplit hlater hnotMiddle with
      ⟨normalizedMiddle, hmiddleStep⟩
    rcases hduplicate middle later suffix hsplit hlater hnotMiddle with
      ⟨normalized, hnormalizedStep⟩
    refine ⟨normalized, ?_⟩
    rw [hsplit]
    simpa [List.append_assoc]
      using executableFieldPrefixDuplicateBlockNormalizeTrans_of_middleNormalizes
        responseName prefixFields later middle suffix normalizedMiddle
        normalized hprefixNonempty hlater hlaterLookup
        hnotMiddle hmiddleStep hnormalizedStep
  · rcases hfresh hmem with ⟨normalizedRest, hrest⟩
    have hprefix :
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections responseName prefixFields)
          (executableFieldSelections responseName prefixFields) :=
      SelectionSetFreshPlanNormalizes.of_plan
        (.sameGroup responseName prefixFields)
    have hprefixCollect :
        GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections responseName prefixFields) =
          [(responseName, prefixFields)] := by
      cases prefixFields with
      | nil =>
          contradiction
      | cons firstPrefix restPrefix =>
          simpa using
            collectFields_executableFieldSelections_same_group schema
              variableValues parentType source responseName
              (firstPrefix :: restPrefix)
    have hdisjoint :
        GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (executableFieldSelections responseName prefixFields))
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (keyedExecutableFieldSelections rest)) := by
      intro candidate hleft hright
      rw [hprefixCollect] at hleft
      simp at hleft
      have hrightName :
          candidate ∈ rest.map (fun field => field.responseName) :=
        (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
          schema variableValues parentType source rest candidate).mp hright
      exact hmem (by simpa [hleft] using hrightName)
    exact ⟨
      executableFieldSelections responseName prefixFields ++ normalizedRest,
      by
        simpa [keyedExecutableFieldSelections, executableFieldSelections, List.map_append]
          using SelectionSetFreshPlanNormalizes.appendDisjoint hprefix hrest hdisjoint
    ⟩

theorem executableFieldPrefixNormalizes_of_smaller
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName : Name) (prefixFields : List ExecutableField)
    (rest : List KeyedExecutableField)
    (hprefixNonempty : prefixFields ≠ [])
    (hwholeLookups
      : ∀ field,
          field ∈ prefixFields ++ rest.map KeyedExecutableField.toExecutableField
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (normalizeSmaller
      : ∀ fields,
          fields.length < prefixFields.length + rest.length
          -> (∀ field,
                field ∈ fields
                -> ∃ fieldDefinition,
                    schema.lookupField parentType field.fieldName = some fieldDefinition)
          -> ∃ normalized,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (keyedExecutableFieldSelections fields) normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections responseName prefixFields
            ++ keyedExecutableFieldSelections rest) normalized := by
  let total := prefixFields.length + rest.length
  have aux :
      ∀ m (prefixFields : List ExecutableField)
          (rest : List KeyedExecutableField),
        rest.length = m ->
        prefixFields ≠ [] ->
        prefixFields.length + rest.length = total ->
        (∀ field, field ∈ prefixFields ++
            rest.map KeyedExecutableField.toExecutableField ->
          ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
            some fieldDefinition) ->
          ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (executableFieldSelections responseName prefixFields ++
                keyedExecutableFieldSelections rest) normalized := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro prefixFields rest hrestLen hprefixNonempty htotal hlookups
        by_cases hmem :
            responseName ∈ rest.map (fun field => field.responseName)
        · rcases
            FreshPrefixSelectionDerivation.executableFields_first_responseName_split
              responseName rest hmem with
            ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
          let collectedMiddle : List KeyedExecutableField :=
            keyedExecutableFieldsOfGroups
              (GraphQL.Execution.collectFields schema variableValues
                parentType source (keyedExecutableFieldSelections middle))
          let transformedRest : List KeyedExecutableField :=
            collectedMiddle ++ suffix
          have hmiddleLookups :
              ∀ field, field ∈ middle ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            exact hlookups field.toExecutableField
              (List.mem_append.mpr (.inr (List.mem_map_of_mem (f :=
                KeyedExecutableField.toExecutableField) (by
                rw [hsplit]
                simp [hfield]))))
          have hlaterLookup :
              ∃ fieldDefinition,
                schema.lookupField parentType later.fieldName =
                  some fieldDefinition := by
            exact hlookups later.toExecutableField
              (List.mem_append.mpr (.inr (List.mem_map_of_mem (f :=
                KeyedExecutableField.toExecutableField) (by
                rw [hsplit]
                simp))))
          have hmiddleLt :
              middle.length < total := by
            rw [← htotal, hsplit]
            simp [List.length_append]
            omega
          rcases normalizeSmaller middle hmiddleLt hmiddleLookups with
            ⟨normalizedMiddle, hmiddleStep⟩
          have hcollectedMiddleLookups :
              ∀ field,
                field ∈ collectedMiddle.map
                    KeyedExecutableField.toExecutableField ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            dsimp [collectedMiddle] at hfield
            rw [map_toExecutableField_keyedExecutableFieldsOfGroups] at hfield
            exact collectedExecutableFields_collectFields_lookupValid schema
              variableValues parentType source
              (keyedExecutableFieldSelections middle)
              (keyedExecutableFieldSelections_lookupValid schema parentType
                middle hmiddleLookups)
              field hfield
          have hsuffixLookups :
              ∀ field,
                field ∈ suffix.map KeyedExecutableField.toExecutableField ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            apply hlookups field
            apply List.mem_append.mpr
            right
            rw [hsplit, List.map_append, List.map_cons]
            exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ hfield))
          have htransformedLookups :
              ∀ field,
                field ∈ transformedRest.map
                    KeyedExecutableField.toExecutableField ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            dsimp [transformedRest] at hfield
            rw [List.map_append] at hfield
            rcases List.mem_append.mp hfield with hcollected | hsuffix
            · exact hcollectedMiddleLookups field hcollected
            · exact hsuffixLookups field hsuffix
          have hcollectedLen :
              collectedMiddle.length = middle.length := by
            dsimp [collectedMiddle]
            rw [length_keyedExecutableFieldsOfGroups]
            exact
              collectedExecutableFields_collectFields_keyedExecutableFieldSelections_length
                schema variableValues parentType source middle
          have htransformedLt :
              transformedRest.length < m := by
            dsimp [transformedRest]
            rw [List.length_append, hcollectedLen]
            rw [← hrestLen, hsplit]
            simp [List.length_append]
          have hnewTotal :
              (prefixFields ++ [later.toExecutableField]).length +
                  transformedRest.length = total := by
            dsimp [transformedRest]
            simp only [List.length_append]
            rw [hcollectedLen, ← htotal, hsplit]
            simp [List.length_append]
            omega
          have hnewPrefixNonempty :
              prefixFields ++ [later.toExecutableField] ≠ [] := by
            simp
          have hnewWholeLookups :
              ∀ field,
                field ∈ (prefixFields ++ [later.toExecutableField]) ++
                    transformedRest.map KeyedExecutableField.toExecutableField ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            rcases List.mem_append.mp hfield with hprefixLater | htail
            · rcases List.mem_append.mp hprefixLater with hprefix | hlaterMem
              · exact hlookups field (by
                  rw [hsplit]
                  simp [hprefix])
              · rcases List.mem_singleton.mp hlaterMem
                exact hlaterLookup
            · exact htransformedLookups field htail
          rcases
              ih transformedRest.length htransformedLt
                (prefixFields ++ [later.toExecutableField]) transformedRest rfl
                hnewPrefixNonempty hnewTotal hnewWholeLookups with
            ⟨normalizedTail, htailStep⟩
          have htailStep' :
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                ((executableFieldSelections responseName
                      (prefixFields ++ [later.toExecutableField]) ++
                    collectedExecutableSelections
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source
                        (keyedExecutableFieldSelections middle))) ++
                  keyedExecutableFieldSelections suffix)
                normalizedTail := by
            rw [←
              keyedExecutableFieldSelections_keyedExecutableFieldsOfGroups]
            simpa [transformedRest, collectedMiddle,
              keyedExecutableFieldSelections,
              List.map_append, List.append_assoc] using htailStep
          refine ⟨normalizedTail, ?_⟩
          rw [hsplit]
          simpa [transformedRest, collectedMiddle, keyedExecutableFieldSelections,
            keyedExecutableFieldSelections_keyedExecutableFieldsOfGroups, List.map_append,
            List.append_assoc]
            using executableFieldPrefixDuplicateBlockNormalizeTrans_of_middleNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth)
              (parentType := parentType) (source := source)
              responseName prefixFields later middle suffix normalizedMiddle
              normalizedTail hprefixNonempty hlater
              hlaterLookup hnotMiddle hmiddleStep htailStep'
        · have hprefix :
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (executableFieldSelections responseName prefixFields)
                (executableFieldSelections responseName prefixFields) :=
            SelectionSetFreshPlanNormalizes.of_plan
              (.sameGroup responseName prefixFields)
          have hrestLookups :
              ∀ field, field ∈ rest ->
                ∃ fieldDefinition,
                  schema.lookupField parentType field.fieldName =
                    some fieldDefinition := by
            intro field hfield
            exact hlookups field.toExecutableField
              (List.mem_append.mpr (.inr (List.mem_map_of_mem (f :=
                KeyedExecutableField.toExecutableField) hfield)))
          have hrestLt :
              rest.length < total := by
            rw [← htotal]
            cases prefixFields with
            | nil =>
                contradiction
            | cons firstPrefix restPrefix =>
                simp
          rcases normalizeSmaller rest hrestLt hrestLookups with
            ⟨normalizedRest, hrestStep⟩
          have hprefixCollect :
              GraphQL.Execution.collectFields schema variableValues parentType
                  source (executableFieldSelections responseName prefixFields) =
                [(responseName, prefixFields)] := by
            cases prefixFields with
            | nil =>
                contradiction
            | cons firstPrefix restPrefix =>
                simpa using
                  collectFields_executableFieldSelections_same_group schema
                    variableValues parentType source responseName
                    (firstPrefix :: restPrefix)
          have hdisjoint :
              GraphQL.NormalForm.executableGroupNamesDisjoint
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source (executableFieldSelections responseName prefixFields))
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source (keyedExecutableFieldSelections rest)) := by
            intro candidate hleft hright
            rw [hprefixCollect] at hleft
            simp at hleft
            have hrightName :
                candidate ∈ rest.map (fun field => field.responseName) :=
              (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
                schema variableValues parentType source rest candidate).mp
                hright
            exact hmem (by simpa [hleft] using hrightName)
          exact ⟨
            executableFieldSelections responseName prefixFields ++ normalizedRest,
            by
              simpa [keyedExecutableFieldSelections, executableFieldSelections,
                List.map_append]
                using SelectionSetFreshPlanNormalizes.appendDisjoint hprefix
                  hrestStep hdisjoint
          ⟩
  exact aux rest.length prefixFields rest rfl hprefixNonempty
    rfl hwholeLookups

theorem executableFieldsNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (fields : List KeyedExecutableField)
    (hlookups
      : ∀ field,
          field ∈ fields
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (keyedExecutableFieldSelections fields) normalized := by
  have aux :
      ∀ n (fields : List KeyedExecutableField),
          fields.length = n ->
          (∀ field, field ∈ fields ->
            ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName =
                some fieldDefinition) ->
            ∃ normalized,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (keyedExecutableFieldSelections fields) normalized := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro fields hlen hlookups
        cases fields with
        | nil =>
            exact ⟨
              [],
              SelectionSetFreshPlanNormalizes.nil schema resolvers
                variableValues completionDepth parentType source
            ⟩
        | cons first rest =>
            have hwholeLookups :
                ∀ field,
                  field ∈ [first.toExecutableField] ++
                    rest.map KeyedExecutableField.toExecutableField ->
                  ∃ fieldDefinition,
                    schema.lookupField parentType field.fieldName =
                      some fieldDefinition := by
              intro field hfield
              rcases List.mem_append.mp hfield with hfirst | hrest
              · rw [List.mem_singleton] at hfirst
                subst field
                exact hlookups first (by simp)
              · rcases List.mem_map.mp hrest with
                  ⟨keyedField, hkeyedField, rfl⟩
                exact hlookups keyedField (by simp [hkeyedField])
            rcases
                executableFieldPrefixNormalizes_of_smaller
                  (schema := schema) (resolvers := resolvers)
                  (variableValues := variableValues)
                  (completionDepth := completionDepth)
                  (parentType := parentType) (source := source)
                  first.responseName [first.toExecutableField] rest
                  (by simp)
                  hwholeLookups
                  (by
                    intro smaller hlt hsmallerLookups
                    exact
                      ih smaller.length
                        (by
                          rw [← hlen]
                          simpa [List.length_append, Nat.add_comm] using hlt)
                        smaller rfl hsmallerLookups) with
            ⟨normalized, hnormalized⟩
            exact ⟨
              normalized,
              by
                simpa [keyedExecutableFieldSelections, keyedExecutableFieldSelection,
                  executableFieldSelections]
                  using hnormalized
            ⟩
  exact aux fields.length fields rfl hlookups

private theorem selectionSet_size_append (left right : List Selection)
    : SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

theorem executablePrefixRawNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (prefixFields : List KeyedExecutableField)
    (hprefixLookups
      : ∀ field,
          field ∈ prefixFields
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    : (selectionSet : List Selection)
      -> executionSelectionSetLookupValid schema parentType selectionSet
          -> ∃ normalized,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (keyedExecutableFieldSelections prefixFields ++ selectionSet) normalized
  | [], _hlookupValid => by
      rcases
          executableFieldsNormalizes (schema := schema) (resolvers := resolvers)
            (variableValues := variableValues)
            (completionDepth := completionDepth) (parentType := parentType)
            (source := source) prefixFields hprefixLookups with
        ⟨normalized, hnormalized⟩
      exact ⟨normalized, by simpa using hnormalized⟩
  | .field responseName fieldName arguments directives selectionSet :: rest,
      hlookupValid => by
      unfold executionSelectionSetLookupValid at hlookupValid
      have hfieldLookup :
          ∃ fieldDefinition, schema.lookupField parentType fieldName =
            some fieldDefinition := by
        simpa [executionSelectionLookupValid] using
          hlookupValid
            (.field responseName fieldName arguments directives selectionSet)
            (by simp)
      have hrestLookup :
          executionSelectionSetLookupValid schema parentType rest := by
        unfold executionSelectionSetLookupValid
        intro selection hselection
        exact hlookupValid selection (by simp [hselection])
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · let field : KeyedExecutableField :=
          { toExecutableField := executableField fieldName arguments selectionSet
            responseName := responseName }
        have hlookups' :
            ∀ candidate, candidate ∈ prefixFields ++ [field] ->
              ∃ fieldDefinition,
                schema.lookupField parentType candidate.fieldName =
                  some fieldDefinition := by
          intro candidate hcandidate
          rcases List.mem_append.mp hcandidate with hprefix | hfield
          · exact hprefixLookups candidate hprefix
          · rcases List.mem_singleton.mp hfield with rfl
            simpa [field, executableField] using hfieldLookup
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) (prefixFields ++ [field]) hlookups' rest
              hrestLookup with
          ⟨normalized, tail⟩
        have tail' :
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (keyedExecutableFieldSelections prefixFields ++
                keyedExecutableFieldSelections [field] ++
                rest)
              normalized := by
          simpa [field, keyedExecutableFieldSelections,
            keyedExecutableFieldSelection, executableFieldSelection,
            List.map_append, List.append_assoc] using tail
        exact
          ⟨normalized,
            executablePrefixFieldConsAllowed
              (keyedExecutableFieldSelections prefixFields) responseName
              fieldName arguments directives selectionSet rest normalized
              hallows tail'⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hprefixLookups rest
              hrestLookup with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            executablePrefixFieldConsSkipped
              (keyedExecutableFieldSelections prefixFields) responseName
              fieldName arguments directives selectionSet rest normalized
              hskip tail⟩
  | .inlineFragment none directives rawChild :: rest, hlookupValid => by
      unfold executionSelectionSetLookupValid at hlookupValid
      have hchildLookup :
          executionSelectionSetLookupValid schema parentType rawChild := by
        simpa [executionSelectionLookupValid] using
          hlookupValid (.inlineFragment none directives rawChild) (by simp)
      have hrestLookup :
          executionSelectionSetLookupValid schema parentType rest := by
        unfold executionSelectionSetLookupValid
        intro selection hselection
        exact hlookupValid selection (by simp [hselection])
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · have happendLookup :
            executionSelectionSetLookupValid schema parentType
              (rawChild ++ rest) := by
          unfold executionSelectionSetLookupValid at hchildLookup hrestLookup
          unfold executionSelectionSetLookupValid
          intro selection hselection
          rcases List.mem_append.mp hselection with hchild | hrest
          · exact hchildLookup selection hchild
          · exact hrestLookup selection hrest
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hprefixLookups
              (rawChild ++ rest) happendLookup with
          ⟨normalized, tail⟩
        have tail' :
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (keyedExecutableFieldSelections prefixFields ++ rawChild ++ rest)
              normalized := by
          simpa [List.append_assoc] using tail
        exact
          ⟨normalized,
            executablePrefixInlineFragmentNoneConsFlatten
              (keyedExecutableFieldSelections prefixFields)
              directives hallows tail'⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hprefixLookups rest
              hrestLookup with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            executablePrefixInlineFragmentNoneConsSkipped
              (keyedExecutableFieldSelections prefixFields)
              directives rawChild hskip tail⟩
  | .inlineFragment (some typeCondition) directives rawChild :: rest,
      hlookupValid => by
      unfold executionSelectionSetLookupValid at hlookupValid
      have hchildLookup :
          executionSelectionSetLookupValid schema parentType rawChild := by
        simpa [executionSelectionLookupValid] using
          hlookupValid (.inlineFragment (some typeCondition) directives rawChild)
            (by simp)
      have hrestLookup :
          executionSelectionSetLookupValid schema parentType rest := by
        unfold executionSelectionSetLookupValid
        intro selection hselection
        exact hlookupValid selection (by simp [hselection])
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · by_cases happly :
            doesFragmentTypeApplyBool schema parentType source typeCondition =
              true
        · have happendLookup :
              executionSelectionSetLookupValid schema parentType
                (rawChild ++ rest) := by
            unfold executionSelectionSetLookupValid at hchildLookup hrestLookup
            unfold executionSelectionSetLookupValid
            intro selection hselection
            rcases List.mem_append.mp hselection with hchild | hrest
            · exact hchildLookup selection hchild
            · exact hrestLookup selection hrest
          rcases
              executablePrefixRawNormalizes
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth) (parentType := parentType)
                (source := source) prefixFields hprefixLookups
                (rawChild ++ rest) happendLookup with
            ⟨normalized, tail⟩
          have tail' :
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (keyedExecutableFieldSelections prefixFields ++ rawChild ++ rest)
                normalized := by
            simpa [List.append_assoc] using tail
          exact
            ⟨normalized,
              executablePrefixInlineFragmentSomeConsFlatten
                (keyedExecutableFieldSelections prefixFields)
                typeCondition directives hallows happly tail'⟩
        · have hnotApply :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                false := by
            cases h :
                doesFragmentTypeApplyBool schema parentType source typeCondition
            · rfl
            · exact False.elim (happly h)
          rcases
              executablePrefixRawNormalizes
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth) (parentType := parentType)
                (source := source) prefixFields hprefixLookups rest
                hrestLookup with
            ⟨normalized, tail⟩
          exact
            ⟨normalized,
              executablePrefixInlineFragmentSomeConsDoesNotApply
                (keyedExecutableFieldSelections prefixFields)
                typeCondition directives rawChild hallows hnotApply tail⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (source := source) prefixFields hprefixLookups rest
              hrestLookup with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            executablePrefixInlineFragmentSomeConsSkipped
              (keyedExecutableFieldSelections prefixFields)
              typeCondition directives rawChild hskip tail⟩
termination_by selectionSet _ => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [selectionSet_size_append, SelectionSet.size, Selection.size]
    try omega

theorem exists_allFields_directiveFree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> executionSelectionSetLookupValid schema parentType selectionSet
      -> ∃ normalizedSelectionSet,
          SelectionSetFreshPlanNormalizes schema resolvers variableValues
            completionDepth parentType source selectionSet
            normalizedSelectionSet := by
  intro hall hfree hlookupValid
  let fields :=
    selectionSet.map
      FreshPrefixSelectionDerivation.executableFieldOfSelection
  have hselectionEq : keyedExecutableFieldSelections fields = selectionSet := by
    dsimp [fields]
    exact
      FreshPrefixSelectionDerivation.executableFieldSelections_map_executableFieldOfSelection
        selectionSet hall hfree
  have hlookups :
      ∀ field, field ∈ fields ->
        ∃ fieldDefinition, schema.lookupField parentType field.fieldName =
          some fieldDefinition := by
    intro field hfield
    dsimp [fields] at hfield
    rcases List.mem_map.mp hfield with ⟨selection, hselection, hfieldEq⟩
    have hselectionField : Selection.isField selection :=
      hall selection hselection
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        rcases hfieldEq
        have hselectionLookup :
            executionSelectionLookupValid schema parentType
              (.field responseName fieldName arguments directives
                childSelectionSet) := by
          unfold executionSelectionSetLookupValid at hlookupValid
          exact hlookupValid
            (.field responseName fieldName arguments directives
              childSelectionSet)
            hselection
        simpa [FreshPrefixSelectionDerivation.executableFieldOfSelection, executableField,
          executionSelectionLookupValid]
          using hselectionLookup
    | inlineFragment typeCondition directives childSelectionSet =>
        simp [Selection.isField] at hselectionField
  rcases
      executableFieldsNormalizes (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth) (parentType := parentType)
        (source := source) fields hlookups with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact ⟨normalizedSelectionSet, by simpa [hselectionEq] using hnormalization⟩

theorem executableFieldHeadDuplicateNormalizesOfMem
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : KeyedExecutableField) (rest : List KeyedExecutableField)
    (hmem : first.responseName ∈ rest.map (fun field => field.responseName))
    (hrestLookups
      : ∀ field,
          field ∈ rest
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hmiddle
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> FreshPrefixSelectionDerivation schema variableValues parentType source
              (keyedExecutableFieldSelections middle))
    (hnormalized
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalized,
              FreshPrefixSelectionPlan schema resolvers variableValues
                completionDepth parentType source
                ((executableFieldSelections first.responseName
                      [first.toExecutableField, later.toExecutableField]
                    ++ collectedExecutableSelections
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source
                          (keyedExecutableFieldSelections middle)))
                  ++ keyedExecutableFieldSelections suffix)
              ∧ SelectionSetFreshPlanNormalizes schema resolvers variableValues
                  completionDepth parentType source
                  ((executableFieldSelections first.responseName
                        [first.toExecutableField, later.toExecutableField]
                      ++ collectedExecutableSelections
                          (GraphQL.Execution.collectFields schema variableValues
                            parentType source
                            (keyedExecutableFieldSelections middle)))
                    ++ keyedExecutableFieldSelections suffix)
                  normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (keyedExecutableFieldSelections (first :: rest)) normalized := by
  rcases
      FreshPrefixSelectionDerivation.executableFields_first_responseName_split
        first.responseName rest hmem with
      ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
  have hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition := by
    exact hrestLookups later (by rw [hsplit]; simp)
  rcases hnormalized middle later suffix hsplit hlater hnotMiddle with
    ⟨normalized, hintermediatePlan, hnormalizedStep⟩
  refine ⟨normalized, ?_⟩
  rw [hsplit]
  exact executableFieldDuplicateBlockNormalizeTrans first later middle suffix
    normalized hlater hlaterLookup hnotMiddle
    (hmiddle middle later suffix hsplit hlater hnotMiddle)
    hintermediatePlan hnormalizedStep

theorem executableFieldHeadDuplicateNormalizesOfMem_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : KeyedExecutableField) (rest : List KeyedExecutableField)
    (hmem : first.responseName ∈ rest.map (fun field => field.responseName))
    (hrestLookups
      : ∀ field,
          field ∈ rest
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hmiddle
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalizedMiddle,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (keyedExecutableFieldSelections middle) normalizedMiddle)
    (hnormalized
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalized,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                ((executableFieldSelections first.responseName
                      [first.toExecutableField, later.toExecutableField]
                    ++ collectedExecutableSelections
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source
                          (keyedExecutableFieldSelections middle)))
                  ++ keyedExecutableFieldSelections suffix)
                normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (keyedExecutableFieldSelections (first :: rest)) normalized := by
  rcases
      FreshPrefixSelectionDerivation.executableFields_first_responseName_split
        first.responseName rest hmem with
      ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
  have hlaterLookup :
      ∃ fieldDefinition, schema.lookupField parentType later.fieldName =
        some fieldDefinition := by
    exact hrestLookups later (by rw [hsplit]; simp)
  rcases hmiddle middle later suffix hsplit hlater hnotMiddle with
    ⟨normalizedMiddle, hmiddleStep⟩
  rcases hnormalized middle later suffix hsplit hlater hnotMiddle with
    ⟨normalized, hnormalizedStep⟩
  refine ⟨normalized, ?_⟩
  rw [hsplit]
  exact
    executableFieldDuplicateBlockNormalizeTrans_of_middleNormalizes first
      later middle suffix normalizedMiddle normalized hlater hlaterLookup
      hnotMiddle hmiddleStep hnormalizedStep

theorem executableFieldHeadNormalizesOfCases
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : KeyedExecutableField) (rest : List KeyedExecutableField)
    (hrestLookups
      : ∀ field,
          field ∈ rest
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfresh
      : first.responseName ∉ rest.map (fun field => field.responseName)
        -> ∃ normalizedRest,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (keyedExecutableFieldSelections rest) normalizedRest)
    (hmiddle
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> FreshPrefixSelectionDerivation schema variableValues parentType source
              (keyedExecutableFieldSelections middle))
    (hduplicate
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalized,
              FreshPrefixSelectionPlan schema resolvers variableValues
                completionDepth parentType source
                ((executableFieldSelections first.responseName
                      [first.toExecutableField, later.toExecutableField]
                    ++ collectedExecutableSelections
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source
                          (keyedExecutableFieldSelections middle)))
                  ++ keyedExecutableFieldSelections suffix)
              ∧ SelectionSetFreshPlanNormalizes schema resolvers variableValues
                  completionDepth parentType source
                  ((executableFieldSelections first.responseName
                        [first.toExecutableField, later.toExecutableField]
                      ++ collectedExecutableSelections
                          (GraphQL.Execution.collectFields schema variableValues
                            parentType source
                            (keyedExecutableFieldSelections middle)))
                    ++ keyedExecutableFieldSelections suffix)
                  normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (keyedExecutableFieldSelections (first :: rest)) normalized := by
  by_cases hmem :
      first.responseName ∈ rest.map (fun field => field.responseName)
  · exact executableFieldHeadDuplicateNormalizesOfMem first rest hmem
      hrestLookups hmiddle hduplicate
  · rcases hfresh hmem with ⟨normalizedRest, hrest⟩
    exact ⟨
      keyedExecutableFieldSelections [first] ++ normalizedRest,
      executableFieldConsFreshNormalizes first rest normalizedRest hmem hrest
    ⟩

theorem executableFieldHeadNormalizesOfCases_middleNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (first : KeyedExecutableField) (rest : List KeyedExecutableField)
    (hrestLookups
      : ∀ field,
          field ∈ rest
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hfresh
      : first.responseName ∉ rest.map (fun field => field.responseName)
        -> ∃ normalizedRest,
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType source
              (keyedExecutableFieldSelections rest) normalizedRest)
    (hmiddle
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalizedMiddle,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                (keyedExecutableFieldSelections middle) normalizedMiddle)
    (hduplicate
      : ∀ middle later suffix,
          rest = middle ++ later :: suffix
          -> later.responseName = first.responseName
          -> first.responseName ∉ middle.map (fun field => field.responseName)
          -> ∃ normalized,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType source
                ((executableFieldSelections first.responseName
                      [first.toExecutableField, later.toExecutableField]
                    ++ collectedExecutableSelections
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source
                          (keyedExecutableFieldSelections middle)))
                  ++ keyedExecutableFieldSelections suffix)
                normalized)
    : ∃ normalized,
        SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source
          (keyedExecutableFieldSelections (first :: rest)) normalized := by
  by_cases hmem :
      first.responseName ∈ rest.map (fun field => field.responseName)
  · exact executableFieldHeadDuplicateNormalizesOfMem_middleNormalizes first
      rest hmem hrestLookups hmiddle hduplicate
  · rcases hfresh hmem with ⟨normalizedRest, hrest⟩
    exact ⟨
      keyedExecutableFieldSelections [first] ++ normalizedRest,
      executableFieldConsFreshNormalizes first rest normalizedRest hmem hrest
    ⟩

theorem duplicateFieldBlockNormalizeHeadDisjointMiddle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (middle suffix : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source middle)
    (hnormalized
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix))
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        ((executableFieldSelections responseName [first, later]
            ++ collectedExecutableSelections
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source middle))
          ++ suffix) :=
  duplicateFieldBlockNormalize schema resolvers variableValues completionDepth
    parentType source responseName first later middle suffix hlaterLookup
    hnotMiddle
    (FreshPrefixSelectionPlan.of_headDisjointTree schema resolvers
      variableValues completionDepth parentType source middle hmiddle)
    hnormalized

theorem duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField)
    (middle suffix : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections responseName [first]
              ++ middle
              ++ executableFieldSelections responseName [later]))
          (GraphQL.Execution.collectFields schema variableValues parentType source
            suffix))
    (hmiddle
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source middle)
    (hsuffix
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source suffix)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        ((executableFieldSelections responseName [first, later]
            ++ collectedExecutableSelections
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source middle))
          ++ suffix) :=
  duplicateFieldBlockNormalizeHeadDisjointMiddle schema resolvers variableValues
    completionDepth parentType source responseName first later middle suffix
    hlaterLookup hnotMiddle hmiddle
    (FreshPrefixSelectionPlan.duplicateFieldBlockNormalizePlan_of_headDisjointSuffix
      schema resolvers variableValues completionDepth parentType source
      responseName first later middle suffix hnotMiddle hdisjoint hsuffix)

end SelectionSetFreshPlanNormalizes

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
