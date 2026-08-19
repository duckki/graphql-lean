import GraphQL.Execution
import GraphQL.SchemaWellFormedness
import GraphQL.Validation
import GraphQL.Theories.ConditionTree.Termination

/-! Execution of condition-minimized selection trees.

Runtime condition traversal: local node fields first, followed by condition children in
tree order. Active fields are then folded into one response-name map, so a name first seen
at a parent is merged with matching fields from taken descendants and executed only once.

The public coverage and soundness predicates live beside these semantics: extraction
coverage is stated against specification field collection, and operation execution is
stated equivalent to the specification-facing query executor.
-/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution
open Termination
open scoped SemanticEquivalence

-----------------------------------------------------------------------------------------
-- Runtime field collection and grouping
-----------------------------------------------------------------------------------------

-- Ungrouped runtime field collection for one syntax boundary.
mutual
  def collectFlatFields (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : List Selection -> List ExecutableField
    | [] => []
    | selection :: rest =>
        collectFlatSelection schema variableValues executionParentType source selection
        ++ collectFlatFields schema variableValues executionParentType source rest

  def collectFlatSelection (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : Selection -> List ExecutableField
    | .field responseName fieldName arguments directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          [{
            parentType := executionParentType
            responseName
            fieldName
            arguments
            selectionSet
          }]
        else
          []
    | .inlineFragment none directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          collectFlatFields schema variableValues executionParentType source selectionSet
        else
          []
    | .inlineFragment (some typeCondition) directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives
            && doesFragmentTypeApplyBool schema executionParentType source
                typeCondition then
          collectFlatFields schema variableValues executionParentType source selectionSet
        else
          []
end

-- For coverage and exactness statements, forget response-name grouping while retaining
-- every executable field occurrence.
def flattenCollectedFields (groups : List (Name × List ExecutableField))
    : List ExecutableField :=
  groups.flatMap Prod.snd

-- Groups a flat field stream by response name. The first occurrence fixes group order;
-- later occurrences append their selections to that group.
def groupExecutableFields (fields : List ExecutableField)
    : List (Name × List ExecutableField) :=
  fields.foldl
    (fun groups field => addExecutableGroup (field.responseName, [field]) groups) []

def RuntimeFieldGroupsExact (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  (groups.map Prod.fst).Nodup ∧ (flattenCollectedFields groups).Perm fields

-- All local fields in analyzer preorder, annotated with their cumulative node
-- condition. A child contributes only its own fields; parent entries are not copied.
mutual
  def Tree.storedFieldEntries (tree : Tree) : List (Condition × NamedField) :=
    tree.fields.flatMap
      (fun group =>
        group.fields.map
          fun field =>
            (tree.condition, { responseName := group.responseName, field }))
    ++ branchStoredFieldEntries tree.branches
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def branchStoredFieldEntries : List (Branch Tree) -> List (Condition × NamedField)
    | [] => []
    | branch :: rest =>
        branch.body.storedFieldEntries ++ branchStoredFieldEntries rest
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

-- Canonical runtime interpretation of typed condition-tree entries. All runtime gating
-- is decided by the node condition; stored `Field` values contain no directive payload.
def runtimeFieldsForEntries
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (entries : List (Condition × NamedField))
    : List ExecutableField :=
  entries.flatMap
    fun entry =>
      if entry.1.allows variableValues runtimeType then
        [{
          parentType := executionParentType
          responseName := entry.2.responseName
          fieldName := entry.2.field.fieldName
          arguments := entry.2.field.arguments
          selectionSet := entry.2.field.selectionSet
        }]
      else
        []

def Tree.collectRuntimeFields
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (tree : Tree)
    : List ExecutableField :=
  runtimeFieldsForEntries variableValues executionParentType runtimeType
    tree.storedFieldEntries

-- Runtime-active field groups in condition-tree/analyzer traversal order.
-- `storedFieldEntries` emits only a node's local fields before descending, so parent
-- fields are not copied into child nodes. Global grouping merges repeated response
-- names before execution.
def Tree.collectRuntimeFieldGroups
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (tree : Tree)
    : List (Name × List ExecutableField) :=
  groupExecutableFields
    (tree.collectRuntimeFields variableValues executionParentType runtimeType)

-----------------------------------------------------------------------------------------
-- Tree execution termination measure
-----------------------------------------------------------------------------------------

private def executableFieldResponseDepth (field : ExecutableField) : Nat :=
  selectionSetResponseDepth field.selectionSet + 1

private def executableFieldsResponseDepth : List ExecutableField -> Nat
  | [] => 0
  | field :: rest =>
      max (executableFieldResponseDepth field) (executableFieldsResponseDepth rest)

private def executableGroupsResponseDepth : List (Name × List ExecutableField) -> Nat
  | [] => 0
  | group :: rest =>
      max (executableFieldsResponseDepth group.2) (executableGroupsResponseDepth rest)

private theorem executableFieldsResponseDepth_append (left right : List ExecutableField)
    : executableFieldsResponseDepth (left ++ right)
      = max (executableFieldsResponseDepth left)
          (executableFieldsResponseDepth right) := by
  induction left with
  | nil => simp [executableFieldsResponseDepth]
  | cons field rest ih =>
      simp [executableFieldsResponseDepth, ih, Nat.max_assoc]

private theorem executableFieldsResponseDepth_singleton (field : ExecutableField)
    : executableFieldsResponseDepth [field] = executableFieldResponseDepth field := by
  simp [executableFieldsResponseDepth]

private theorem collectFlatFields_responseDepth_le
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : executableFieldsResponseDepth
        (collectFlatFields schema variableValues executionParentType source selectionSet)
      ≤ selectionSetResponseDepth selectionSet := by
  cases selectionSet with
  | nil => simp [collectFlatFields, executableFieldsResponseDepth,
      selectionSetResponseDepth]
  | cons selection rest =>
      rw [collectFlatFields, executableFieldsResponseDepth_append,
        selectionSetResponseDepth]
      apply Nat.max_le.mpr
      constructor
      · cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simpa [collectFlatSelection, hallows, executableFieldsResponseDepth,
                executableFieldResponseDepth, selectionResponseDepth] using
                (Nat.le_max_left
                  (selectionSetResponseDepth childSelectionSet + 1)
                  (selectionSetResponseDepth rest))
            · simp [collectFlatSelection, hallows, executableFieldsResponseDepth]
        | inlineFragment typeCondition directives childSelectionSet =>
            cases typeCondition with
            | none =>
                by_cases hallows :
                    selectionDirectivesAllowBool variableValues directives = true
                · simpa [collectFlatSelection, hallows, selectionResponseDepth] using
                    Nat.le_trans
                    (collectFlatFields_responseDepth_le schema variableValues
                      executionParentType source childSelectionSet)
                    (Nat.le_max_left _ _)
                · simp [collectFlatSelection, hallows, executableFieldsResponseDepth]
            | some typeName =>
                by_cases hallows :
                    (selectionDirectivesAllowBool variableValues directives
                      && doesFragmentTypeApplyBool schema executionParentType source
                        typeName) = true
                · simpa [collectFlatSelection, hallows, selectionResponseDepth] using
                    Nat.le_trans
                    (collectFlatFields_responseDepth_le schema variableValues
                      executionParentType source childSelectionSet)
                    (Nat.le_max_left _ _)
                · simp [collectFlatSelection, hallows, executableFieldsResponseDepth]
      · exact Nat.le_trans
          (collectFlatFields_responseDepth_le schema variableValues
            executionParentType source rest)
          (Nat.le_max_right _ _)
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    first
    | exact Nat.lt_add_right _ (Nat.lt_add_of_pos_left (by omega))
    | cases selection <;> simp [Selection.size] <;> omega

def conditionEntriesResponseDepth : List (Condition × NamedField) -> Nat
  | [] => 0
  | entry :: rest =>
      max (selectionResponseDepth entry.2.toSelection)
        (conditionEntriesResponseDepth rest)

private theorem conditionEntriesResponseDepth_append
    (left right : List (Condition × NamedField))
    : conditionEntriesResponseDepth (left ++ right)
      = max (conditionEntriesResponseDepth left)
          (conditionEntriesResponseDepth right) := by
  induction left with
  | nil => simp [conditionEntriesResponseDepth]
  | cons entry rest ih =>
      simp [conditionEntriesResponseDepth, ih, Nat.max_assoc]

private theorem conditionEntriesResponseDepth_annotatedFields
    (condition : Condition) (responseName : Name) (fields : List Field)
    : conditionEntriesResponseDepth
        (fields.map
          fun field =>
            (condition, { responseName, field }))
      = selectionSetResponseDepth (fields.map (Field.toSelection responseName)) := by
  induction fields with
  | nil => simp [conditionEntriesResponseDepth, selectionSetResponseDepth]
  | cons field rest ih =>
      simp [conditionEntriesResponseDepth, selectionSetResponseDepth, ih,
        NamedField.toSelection]

private theorem conditionEntriesResponseDepth_annotatedGroup
    (condition : Condition) (group : FieldGroup)
    : conditionEntriesResponseDepth
        (group.fields.map
          fun field =>
            (condition, { responseName := group.responseName, field }))
      = selectionSetResponseDepth group.selections := by
  exact conditionEntriesResponseDepth_annotatedFields condition group.responseName
    group.fields

private theorem conditionEntriesResponseDepth_localGroups
    (condition : Condition) (groups : List FieldGroup)
    : conditionEntriesResponseDepth
        (groups.flatMap
          fun group =>
            group.fields.map
              fun field =>
                (condition, { responseName := group.responseName, field }))
      = conditionFieldGroupsResponseDepth groups := by
  induction groups with
  | nil => simp [conditionEntriesResponseDepth, conditionFieldGroupsResponseDepth]
  | cons group rest ih =>
      rw [List.flatMap_cons, conditionEntriesResponseDepth_append,
        conditionEntriesResponseDepth_annotatedGroup, ih]
      rfl

mutual
  theorem Tree.storedFieldEntries_responseDepth_le (tree : Tree)
      : conditionEntriesResponseDepth tree.storedFieldEntries
        ≤ conditionTreeResponseDepth tree := by
    rw [Tree.storedFieldEntries, conditionEntriesResponseDepth_append,
      conditionEntriesResponseDepth_localGroups, conditionTreeResponseDepth]
    exact Nat.max_le.mpr
      ⟨Nat.le_max_left _ _,
        Nat.le_trans (branchStoredFieldEntries_responseDepth_le tree.branches)
          (Nat.le_max_right _ _)⟩
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  private theorem branchStoredFieldEntries_responseDepth_le
      (branches : List (Branch Tree))
      : conditionEntriesResponseDepth (branchStoredFieldEntries branches)
        ≤ conditionBranchesResponseDepth branches := by
    cases branches with
    | nil => simp [branchStoredFieldEntries, conditionEntriesResponseDepth,
        conditionBranchesResponseDepth]
    | cons branch rest =>
        rw [branchStoredFieldEntries, conditionEntriesResponseDepth_append,
          conditionBranchesResponseDepth]
        exact Nat.max_le.mpr
          ⟨Nat.le_trans branch.body.storedFieldEntries_responseDepth_le
              (Nat.le_max_left _ _),
            Nat.le_trans (branchStoredFieldEntries_responseDepth_le rest)
              (Nat.le_max_right _ _)⟩
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

private theorem runtimeFieldsForEntries_responseDepth_le
    (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (entries : List (Condition × NamedField))
    : executableFieldsResponseDepth
        (runtimeFieldsForEntries variableValues executionParentType runtimeType entries)
      ≤ conditionEntriesResponseDepth entries := by
  induction entries with
  | nil => simp [runtimeFieldsForEntries, executableFieldsResponseDepth,
      conditionEntriesResponseDepth]
  | cons entry rest ih =>
      rw [runtimeFieldsForEntries, List.flatMap_cons,
        executableFieldsResponseDepth_append, conditionEntriesResponseDepth]
      apply Nat.max_le.mpr
      constructor
      · split
        · apply Nat.le_trans _ (Nat.le_max_left _ _)
          rcases entry.2 with ⟨responseName, field⟩
          cases field
          simp [executableFieldsResponseDepth, executableFieldResponseDepth,
            NamedField.toSelection, Field.toSelection, selectionResponseDepth]
        · simp [executableFieldsResponseDepth]
      · exact Nat.le_trans ih (Nat.le_max_right _ _)

private theorem Tree.collectRuntimeFields_responseDepth_le
    (tree : Tree) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    : executableFieldsResponseDepth
        (tree.collectRuntimeFields variableValues executionParentType runtimeType)
      ≤ conditionTreeResponseDepth tree := by
  change executableFieldsResponseDepth
      (runtimeFieldsForEntries variableValues executionParentType runtimeType
        tree.storedFieldEntries) ≤ conditionTreeResponseDepth tree
  exact Nat.le_trans
    (runtimeFieldsForEntries_responseDepth_le variableValues executionParentType
      runtimeType tree.storedFieldEntries)
    tree.storedFieldEntries_responseDepth_le

private theorem executableGroupsResponseDepth_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : executableGroupsResponseDepth (addExecutableGroup group groups)
      ≤ max (executableGroupsResponseDepth groups)
          (executableFieldsResponseDepth group.2) := by
  induction groups with
  | nil =>
      simp [addExecutableGroup, executableGroupsResponseDepth]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      rcases group with ⟨groupName, groupFields⟩
      simp only [addExecutableGroup]
      split
      · simp only [executableGroupsResponseDepth,
          executableFieldsResponseDepth_append]
        exact Nat.le_of_eq (by ac_rfl)
      · simp only [executableGroupsResponseDepth]
        apply Nat.max_le.mpr
        constructor
        · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        · exact Nat.le_trans ih <| Nat.max_le.mpr
            ⟨Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _),
              Nat.le_max_right _ _⟩

private theorem executableGroupsResponseDepth_foldFields
    (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : executableGroupsResponseDepth
        (fields.foldl
          (fun result field =>
            addExecutableGroup (field.responseName, [field]) result)
          groups)
      ≤ max (executableGroupsResponseDepth groups)
          (executableFieldsResponseDepth fields) := by
  induction fields generalizing groups with
  | nil => simp [executableFieldsResponseDepth]
  | cons field rest ih =>
      simp only [List.foldl_cons, executableFieldsResponseDepth]
      have hadded :=
        executableGroupsResponseDepth_addExecutableGroup
          (field.responseName, [field]) groups
      have hadded' :
          executableGroupsResponseDepth
              (addExecutableGroup (field.responseName, [field]) groups)
            ≤ max (executableGroupsResponseDepth groups)
                (executableFieldResponseDepth field) := by
        simpa [executableFieldsResponseDepth_singleton] using hadded
      have hrest := ih (addExecutableGroup (field.responseName, [field]) groups)
      exact Nat.le_trans hrest <| calc
        max
              (executableGroupsResponseDepth
                (addExecutableGroup (field.responseName, [field]) groups))
              (executableFieldsResponseDepth rest)
            ≤ max
                (max (executableGroupsResponseDepth groups)
                  (executableFieldResponseDepth field))
                (executableFieldsResponseDepth rest) :=
          Nat.max_le.mpr
            ⟨Nat.le_trans hadded' (Nat.le_max_left _ _),
              Nat.le_max_right _ _⟩
        _ = max (executableGroupsResponseDepth groups)
              (max (executableFieldResponseDepth field)
                (executableFieldsResponseDepth rest)) := by
          ac_rfl

private theorem groupExecutableFields_responseDepth_le (fields : List ExecutableField)
    : executableGroupsResponseDepth (groupExecutableFields fields)
      ≤ executableFieldsResponseDepth fields := by
  unfold groupExecutableFields
  simpa [executableGroupsResponseDepth] using
    executableGroupsResponseDepth_foldFields fields []

private theorem Tree.collectRuntimeFieldGroups_responseDepth_le
    (tree : Tree) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    : executableGroupsResponseDepth
        (tree.collectRuntimeFieldGroups variableValues executionParentType runtimeType)
      ≤ conditionTreeResponseDepth tree := by
  exact Nat.le_trans
    (groupExecutableFields_responseDepth_le
      (tree.collectRuntimeFields variableValues executionParentType runtimeType))
    (tree.collectRuntimeFields_responseDepth_le variableValues
      executionParentType runtimeType)

def mergedExecutableSelectionSet (fields : List ExecutableField) : List Selection :=
  fields.flatMap ExecutableField.selectionSet

private theorem mergedExecutableSelectionSet_cons
    (field : ExecutableField) (rest : List ExecutableField)
    : mergedExecutableSelectionSet (field :: rest)
      = field.selectionSet ++ mergedExecutableSelectionSet rest := by
  rfl

private theorem mergedExecutableSelectionSet_responseDepth_lt
    (field : ExecutableField) (rest : List ExecutableField)
    : selectionSetResponseDepth (mergedExecutableSelectionSet (field :: rest))
      < executableFieldsResponseDepth (field :: rest) := by
  cases rest with
  | nil =>
      rw [mergedExecutableSelectionSet_cons, executableFieldsResponseDepth,
        selectionSetResponseDepth_append]
      simp [mergedExecutableSelectionSet, executableFieldResponseDepth,
        executableFieldsResponseDepth, selectionSetResponseDepth]
  | cons next tail =>
      rw [mergedExecutableSelectionSet_cons, selectionSetResponseDepth_append,
        executableFieldsResponseDepth]
      have hrest := mergedExecutableSelectionSet_responseDepth_lt next tail
      simp only [executableFieldsResponseDepth] at hrest
      exact (Nat.max_lt).2
        ⟨
        (Nat.lt_of_lt_of_le
          (Nat.lt_succ_self (selectionSetResponseDepth field.selectionSet))
          (Nat.le_max_left _ _)),
        (Nat.lt_of_lt_of_le hrest (Nat.le_max_right _ _))⟩
termination_by rest.length
decreasing_by simp_wf

private theorem executionMeasure_lt_of_le_of_control_lt
    {leftDepth rightDepth leftControl rightControl leftTail rightTail : Nat}
    (hdepth : leftDepth ≤ rightDepth)
    (hcontrol : leftControl < rightControl)
    : Prod.Lex (fun left right : Nat => left < right)
        (Prod.Lex (fun left right : Nat => left < right)
          (fun left right : Nat => left < right))
        (leftDepth, leftControl, leftTail)
        (rightDepth, rightControl, rightTail) := by
  rcases Nat.lt_or_eq_of_le hdepth with hstrict | hequal
  · exact Prod.Lex.left _ _ hstrict
  · subst rightDepth
    exact Prod.Lex.right leftDepth (Prod.Lex.left _ _ hcontrol)

-----------------------------------------------------------------------------------------
-- Tree execution
-----------------------------------------------------------------------------------------

-- Fuel-free condition-tree execution of a selection set. Each response boundary
-- extracts its tree internally, collects the active field groups, and recursively calls
-- `executeSelectionSet` with the merged child selection set during object completion. Termination
-- is lexicographic: nested response selection depth strictly decreases; traversal
-- phases and structural list/type size handle work within one boundary.
mutual
  def executeSelectionSet
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (parentType executionParentType runtimeType : Name)
      (source : ResolverValue ObjectRef) (selectionSet : List Selection)
      : Result (List (Name × ResponseValue)) :=
    let tree := ofSelectionSet schema parentType selectionSet
    executeCollectedFields schema resolvers variableValues source
      (tree.collectRuntimeFieldGroups variableValues executionParentType runtimeType)
  termination_by (selectionSetResponseDepth selectionSet, 5, 0)
  decreasing_by
    apply executionMeasure_lt_of_le_of_control_lt
    · exact Nat.le_trans
        (tree.collectRuntimeFieldGroups_responseDepth_le variableValues
          executionParentType runtimeType)
        (conditionTreeResponseDepth_ofSelectionSetInScope schema parentType []
          selectionSet)
    · omega

  def executeCollectedFields
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (source : ResolverValue ObjectRef)
      : List (Name × List ExecutableField) -> Result (List (Name × ResponseValue))
    | [] => .ok ([], 0)
    | (responseName, fields) :: rest =>
        let head :=
          executeField schema resolvers variableValues source responseName fields
        let tail := executeCollectedFields schema resolvers variableValues source rest
        Result.combine List.append head tail
  termination_by groups => (executableGroupsResponseDepth groups, 4, sizeOf groups)
  decreasing_by
    · apply executionMeasure_lt_of_le_of_control_lt
      · exact Nat.le_max_left _ _
      · omega
    · apply triple_lt_of_depth_le_of_tail_lt
      · exact Nat.le_max_right _ _
      · simp_wf
        omega

  def executeField
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (source : ResolverValue ObjectRef)
      (responseName : Name)
      : List ExecutableField -> Result (List (Name × ResponseValue))
    | [] => .error 1
    | field :: rest =>
        match schema.lookupField field.parentType field.fieldName with
        | none => .error 1
        | some fieldDefinition =>
            match coerceArgumentValues schema variableValues fieldDefinition.arguments
                    field.arguments with
            | .error =>
                singleFieldResult responseName
                  (handleFieldError fieldDefinition.outputType)
            | .success coercedArguments =>
                match resolveFieldValue resolvers field.parentType field.fieldName
                        coercedArguments source with
                | none =>
                    singleFieldResult responseName
                      (handleFieldError fieldDefinition.outputType)
                | some resolved =>
                    singleFieldResult responseName
                      (completeValue schema resolvers variableValues
                        fieldDefinition.outputType (field :: rest) resolved)
  termination_by fields => (executableFieldsResponseDepth fields, 3, 0)
  decreasing_by
    apply executionMeasure_lt_of_le_of_control_lt
    · exact Nat.le_refl _
    · omega

  def completeValue
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : TypeRef -> List ExecutableField -> ResolverValue ObjectRef -> Result ResponseValue
    | .nonNull inner, fields, value =>
        nonNullCompletion
          (completeValue schema resolvers variableValues inner fields value)
    | _fieldType, _fields, .null =>
        .ok (.null, 0)
    | .named typeName, _fields, .scalar value =>
        if (TypeRef.named typeName).isCompositeBool schema then
          .error 1
        else
          .ok (.scalar value, 0)
    | .named _parentType, [], .object _runtimeType _ref =>
        .error 1
    | .named parentType,
      field :: rest,
      source@(.object runtimeType _ref) =>
        if schema.typeIncludesObjectBool parentType runtimeType then
          let childSelectionSet := mergedExecutableSelectionSet (field :: rest)
          let completed :=
            executeSelectionSet schema resolvers variableValues parentType runtimeType
              runtimeType source childSelectionSet
          catchBubbleAsNull ResponseValue.object completed
        else
          .error 1
    | .list inner, fields, .list values =>
        let completed :=
          completeValueList schema resolvers variableValues inner fields values
        catchBubbleAsNull ResponseValue.list completed
    | .named _typeName, _fields, .list _values =>
        .error 1
    | .list _inner, _fields, _value =>
        .error 1
  termination_by fieldType fields value =>
    (executableFieldsResponseDepth fields, 2, sizeOf fieldType + sizeOf value)
  decreasing_by
    · apply triple_lt_of_depth_le_of_tail_lt
      · exact Nat.le_refl _
      · simp_wf
    · apply Prod.Lex.left
      exact mergedExecutableSelectionSet_responseDepth_lt field rest
    · apply triple_lt_of_depth_le_of_tail_lt
      · exact Nat.le_refl _
      · simp_wf
        omega

  def completeValueList
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (itemType : TypeRef) (fields : List ExecutableField)
      : List (ResolverValue ObjectRef) -> Result (List ResponseValue)
    | [] => .ok ([], 0)
    | value :: values =>
        let head := completeValue schema resolvers variableValues itemType fields value
        let tail :=
          completeValueList schema resolvers variableValues itemType fields values
        Result.combine List.cons head tail
  termination_by values =>
    (executableFieldsResponseDepth fields, 2, sizeOf itemType + sizeOf values)
  decreasing_by
    · apply triple_lt_of_depth_le_of_tail_lt
      · exact Nat.le_refl _
      · simp_wf
        omega
    · apply triple_lt_of_depth_le_of_tail_lt
      · exact Nat.le_refl _
      · simp_wf
        omega
end

-- Total operation entry point. Variable coercion and invalid-root behavior match the
-- specification-facing executor, while all nested object completion stays in the
-- condition-tree evaluator.
def executeQuery
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Response :=
  let coercedVariableValues := coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    match source with
    | .object runtimeType _ref =>
        selectionSetResultToResponse
          (executeSelectionSet schema resolvers coercedVariableValues
            (operation.rootType schema) (operation.rootType schema) runtimeType source
            operation.selectionSet)
    | .null | .scalar _ | .list _ =>
        { data := .null, errors := 1 }
  else
    { data := .null, errors := 1 }

-----------------------------------------------------------------------------------------
-- Public execution coverage and soundness
-----------------------------------------------------------------------------------------

-- Runtime field-group equivalence ignores response-name order and duplicate field
-- occurrences. This is the public extensional coverage relation; the recursive
-- execution proof strengthens it internally to a permutation of all executable field
-- occurrences. Executable fields carry their response name, so preserving both keys
-- and flattened membership also preserves membership in each generated response-name
-- group.
def RuntimeFieldGroupsEquivalent (left right : List (Name × List ExecutableField))
    : Prop :=
  (∀ responseName, responseName ∈ left.map Prod.fst ↔ responseName ∈ right.map Prod.fst)
  ∧ ∀ field, field ∈ flattenCollectedFields left ↔ field ∈ flattenCollectedFields right

-- Extracted runtime groups preserve the source selection set's executable response
-- names and fields. Its theorem witness is `ConditionTree.extraction_groups_equivalent`
-- in `Proofs.GraphQL.Theories.ConditionTree.Soundness`.
def ExtractionGroupsEquivalent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Prop :=
  ∀ {ObjectRef : Type}
    (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef),
    booleanConditionAllows variableValues inheritedBooleanCondition = true
    -> (schema.getPossibleTypes parentType).contains runtimeType = true
    -> RuntimeFieldGroupsEquivalent
        ((ofSelectionSetInScope schema parentType inheritedBooleanCondition
            selectionSet).collectRuntimeFieldGroups
          variableValues executionParentType runtimeType)
        (Execution.collectFields schema variableValues executionParentType
          (.object runtimeType ref) selectionSet)

-- The analysis-independent condition-tree soundness statement. Its theorem witness is
-- `ConditionTree.extraction_sound` in
-- `Proofs.GraphQL.Theories.ConditionTree.Soundness`.
def ExtractionSound (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Prop :=
  ∀ {ObjectRef : Type}
    (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef),
    booleanConditionAllows variableValues inheritedBooleanCondition = true
    -> (schema.getPossibleTypes parentType).contains runtimeType = true
    -> ∀ field,
        field
          ∈ (ofSelectionSetInScope schema parentType inheritedBooleanCondition
              selectionSet).collectRuntimeFields
              variableValues executionParentType runtimeType
        ↔ field
          ∈ flattenCollectedFields
              (Execution.collectFields schema variableValues executionParentType
                (.object runtimeType ref) selectionSet)

-- Operation-level preservation statement for the total tree executor. Its theorem
-- witness is `ConditionTree.ExecutionEquivalence.execution_equivalent` in
-- `Proofs.GraphQL.Theories.ConditionTree.ExecutionEquivalence`.
def ExecutionEquivalent (schema : Schema) (operation : Operation) : Prop :=
  ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef),
    SchemaWellFormedness.schemaWellFormed schema
    -> Validation.operationDefinitionValid schema operation
    -> executeQuery schema resolvers variableValues operation source
        ≈ Execution.executeQuery schema resolvers variableValues operation source

-- Explicit-fuel form of operation-level tree/spec preservation. For every fuel at
-- least the proved execution bound, its witness is
-- `ConditionTree.ExecutionEquivalence.execution_equivalent_of_sufficient_fuel` in
-- `Proofs.GraphQL.Theories.ConditionTree.ExecutionEquivalence`.
def ExecutionEquivalentAtFuel (schema : Schema) (operation : Operation) (fuel : Nat)
    : Prop :=
  ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef),
    SchemaWellFormedness.schemaWellFormed schema
    -> Validation.operationDefinitionValid schema operation
    -> executeQuery schema resolvers variableValues operation source
        ≈ Execution.executeQueryWithFuel schema resolvers variableValues operation
            fuel source

end ConditionTree
end GraphQL
