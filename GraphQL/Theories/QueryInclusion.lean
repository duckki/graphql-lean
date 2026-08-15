import GraphQL.Theories.AnnotatedExecution
import GraphQL.Algorithms.Common
import GraphQL.Theories.ExecutionReadiness
import GraphQL.Theories.SelectionConditions
import GraphQL.Theories.ResponseDepth
import GraphQL.SchemaWellFormedness

/-! GraphQL query inclusion over concrete annotated execution. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open AnnotatedExecution
open scoped SyntacticEquivalence

-----------------------------------------------------------------------------------------
-- Shared variable definitions and comparison condition variables
-----------------------------------------------------------------------------------------

-- The definitions on the left whose names are also declared on the right. Query-inclusion
-- correctness uses this projection together with operation validity, which rejects
-- duplicate variable names.
def variableDefinitionsSharedWith (left right : List VariableDefinition)
    : List VariableDefinition :=
  left.filter
    fun definition =>
      right.any fun candidate => candidate.name == definition.name

-- Only names declared by both operations are constrained. Their raw types and defaults
-- must agree; definition order and definitions occurring on only one side remain free.
def sharedVariableDefinitionsSyntacticallyCompatible
    (left right : List VariableDefinition)
    : Prop :=
  variableDefinitionsSyntacticallyEquivalent
    (variableDefinitionsSharedWith left right)
    (variableDefinitionsSharedWith right left)

instance sharedVariableDefinitionsSyntacticallyCompatibleDecidable
    : DecidableRel sharedVariableDefinitionsSyntacticallyCompatible :=
  fun _left _right => by
    unfold sharedVariableDefinitionsSyntacticallyCompatible
    infer_instance

def sharedVariableDefinitionsSyntacticallyCompatibleBool
    (left right : List VariableDefinition)
    : Bool :=
  decide (sharedVariableDefinitionsSyntacticallyCompatible left right)

-- The complete Boolean environment for comparing two selection sets is their union.
-- Occurrence order and duplicate uses do not affect conditional execution.
def comparisonConditionVariables (left right : List Selection) : List Name :=
  (SelectionConditions.selectionSetBooleanVariables left
    ++ SelectionConditions.selectionSetBooleanVariables right).eraseDups

-----------------------------------------------------------------------------------------
-- ResolvedFieldProvenance equality
-----------------------------------------------------------------------------------------

-- The annotated executor records the representative field call for every response-name
-- group. Provenance uses the nominal arguments from the selected field;
-- `ResolvedFieldProvenance.coercedArguments` separately records whether argument coercion
-- succeeded and, when it did, the coerced arguments. GraphQL argument order is
-- immaterial, so compare nominal arguments by the syntactic equivalence relation.
def sameFieldProvenance (left right : ResolvedFieldProvenance) : Prop :=
  left.parentType = right.parentType
  ∧ left.fieldName = right.fieldName
  ∧ left.originalArguments ≡ right.originalArguments

instance sameFieldProvenanceDecidable : DecidableRel sameFieldProvenance :=
  fun left right => by
    unfold sameFieldProvenance
    infer_instance

-----------------------------------------------------------------------------------------
-- Query inclusion statement
-----------------------------------------------------------------------------------------

-- `left.includes right` recursively preserves every response field of `right` in
-- `left`. Object fields are matched by response name and concrete resolver-call
-- provenance. List elements are matched recursively at their response positions.
-- Leaves have no nested response fields, so they add no inclusion obligation.
def responseValueIncludes : AnnotatedResponseValue -> AnnotatedResponseValue -> Prop
  | .object _ leftFields, .object _ rightFields =>
      ∀ rightName rightCall rightValue,
        (hmember : .resolved rightName rightCall rightValue ∈ rightFields)
        -> ∃ leftName leftCall leftValue,
            .resolved leftName leftCall leftValue ∈ leftFields
            ∧ leftName = rightName
            ∧ sameFieldProvenance leftCall rightCall
            ∧ responseValueIncludes leftValue rightValue
  | .list leftValues, .list rightValues =>
      ∀ (index : Nat) rightValue,
        (hmember : rightValues[index]? = some rightValue)
        -> ∃ leftValue,
            leftValues[index]? = some leftValue
            ∧ responseValueIncludes leftValue rightValue
  | _, .object _ _ => False
  | _, .list _ => False
  | _, .null => True
  | _, .scalar _ => True
termination_by _left right => right.structuralSize
decreasing_by
  all_goals
    first
    | exact AnnotatedResponseValue.structuralSize_lt_of_object_field_mem hmember
    | exact AnnotatedResponseValue.structuralSize_lt_of_list_get? hmember

-- Query `left` includes query `right` when shared variable definitions have the same
-- types and equivalent defaults and every pair of error-free concrete executions
-- recursively preserves right response fields. One-sided definitions are unrestricted; each
-- operation's condition variables must be complete after its own defaults are
-- materialized. Resolver failures and null bubbling can erase otherwise present response
-- structure, so executions with errors are deliberately outside this relation.
def includes (schema : Schema) (left right : Operation) : Prop :=
  sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
    right.variableDefinitions
  ∧ ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (source : ResolverValue ObjectRef),
      let leftValues := coerceVariableValues left variableValues
      let rightValues := coerceVariableValues right variableValues
      let leftResponse :=
        executeQueryAnnotated schema resolvers variableValues left source
      let rightResponse :=
        executeQueryAnnotated schema resolvers variableValues right source
      boolVarsComplete
        (SelectionConditions.selectionSetBooleanVariables left.selectionSet) leftValues
      -> boolVarsComplete
          (SelectionConditions.selectionSetBooleanVariables right.selectionSet)
          rightValues
      -> leftResponse.errors = 0
      -> rightResponse.errors = 0
      -> responseValueIncludes leftResponse.data rightResponse.data

-----------------------------------------------------------------------------------------
-- Common implementation utilities
-----------------------------------------------------------------------------------------

def executableFieldsMergedSelectionSet (fields : List ExecutableField) : List Selection :=
  fields.flatMap ExecutableField.selectionSet

-- Every total Boolean assignment over the variables that can affect modeled directives.
-- Because each variable is explicitly present, operation defaults cannot affect field
-- collection in these cases.
def booleanVariableAssignments : List Name -> List VariableValues
  | [] => [[]]
  | variableName :: rest =>
      let tailCases : List VariableValues := booleanVariableAssignments rest
      let falseCases : List VariableValues :=
        tailCases.map
          fun values => (variableName, ConstInputValue.boolean false) :: values
      let trueCases : List VariableValues :=
        tailCases.map fun values => (variableName, ConstInputValue.boolean true) :: values
      falseCases ++ trueCases

-----------------------------------------------------------------------------------------
-- Exhaustive query-inclusion decision procedure (reference implementation)
-----------------------------------------------------------------------------------------

-- Field collection observes an object source only through its runtime type. A unit ref
-- therefore gives the checker a canonical source for each possible runtime object.
def collectRuntimeFieldGroups (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (selectionSet : List Selection)
    : List (Name × List ExecutableField) :=
  Execution.collectFields schema variableValues parentType
    (.object runtimeType PUnit.unit) selectionSet

def executableGroupIncludedBool (schema : Schema)
    (childIncludes : TypeRef -> List Selection -> List Selection -> Bool)
    (leftGroups : List (Name × List ExecutableField))
    (rightGroup : Name × List ExecutableField)
    : Bool :=
  leftGroups.any
    fun leftGroup =>
      leftGroup.1 == rightGroup.1
      && match leftGroup.2, rightGroup.2 with
          | leftField :: _leftRest, rightField :: _rightRest =>
              leftField.parentType == rightField.parentType
              && leftField.fieldName == rightField.fieldName
              && Argument.argumentsSyntacticallyEquivalentBool leftField.arguments
                  rightField.arguments
              && match schema.lookupField rightField.parentType rightField.fieldName with
                  | none => false
                  | some definition =>
                      if definition.outputType.isCompositeBool schema then
                        childIncludes definition.outputType
                          (executableFieldsMergedSelectionSet leftGroup.2)
                          (executableFieldsMergedSelectionSet rightGroup.2)
                      else
                        true
          | _, _ => false

def executableGroupsIncludeBool (schema : Schema)
    (childIncludes : TypeRef -> List Selection -> List Selection -> Bool)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    : Bool :=
  rightGroups.all
    fun rightGroup =>
      executableGroupIncludedBool schema childIncludes leftGroups rightGroup

mutual
  -- Compares one concrete runtime-object case.
  def selectionSetIncludesAtRuntimeBoolWithFuel (schema : Schema) (fuel : Nat)
      (parentType runtimeType : Name)
      (variableValues : VariableValues)
      (leftSelectionSet rightSelectionSet : List Selection)
      : Bool :=
    match fuel with
    | 0 =>
        (collectRuntimeFieldGroups schema variableValues parentType runtimeType
          rightSelectionSet).isEmpty
    | fuel + 1 =>
        let leftGroups :=
          collectRuntimeFieldGroups schema variableValues parentType runtimeType
            leftSelectionSet
        let rightGroups :=
          collectRuntimeFieldGroups schema variableValues parentType runtimeType
            rightSelectionSet
        executableGroupsIncludeBool schema
          (fun outputType leftSelectionSet rightSelectionSet =>
            (schema.getPossibleTypes outputType.namedType).all
              fun childRuntimeType =>
                selectionSetIncludesBoolWithFuel schema fuel childRuntimeType
                  variableValues leftSelectionSet rightSelectionSet)
          leftGroups rightGroups

  -- Compares the field groups active for every possible runtime type under one
  -- Boolean assignment, then recursively compares composite children. `fuel` bounds
  -- nested response-field descent.
  def selectionSetIncludesBoolWithFuel (schema : Schema) (fuel : Nat) (parentType : Name)
      (variableValues : VariableValues)
      (leftSelectionSet rightSelectionSet : List Selection)
      : Bool :=
    (schema.getPossibleTypes parentType).all
      fun runtimeType =>
        selectionSetIncludesAtRuntimeBoolWithFuel schema fuel parentType runtimeType
          variableValues leftSelectionSet rightSelectionSet
end

-- Complete enumeration used as the proof-facing reference checker.
def includesBoolReference (schema : Schema) (left right : Operation) : Bool :=
  if left.rootType schema == right.rootType schema
      && sharedVariableDefinitionsSyntacticallyCompatibleBool left.variableDefinitions
          right.variableDefinitions then
    let parentType := right.rootType schema
    let variables := comparisonConditionVariables left.selectionSet right.selectionSet
    let fuel := right.size + 1
    booleanVariableAssignments variables
    |>.all
        fun variableValues =>
          selectionSetIncludesBoolWithFuel schema fuel parentType
            variableValues left.selectionSet right.selectionSet
  else
    false

-----------------------------------------------------------------------------------------
-- Syntactic inclusion shortcut
-----------------------------------------------------------------------------------------

mutual
  -- A conservative syntax-only inclusion witness. A right selection must occur in the
  -- left scope with the same response name, resolver call, directives, and recursively
  -- included child selections. Inline-fragment conditions are compared exactly.
  def selectionSyntacticallyIncludesBool : Selection -> Selection -> Bool
    | .field leftResponseName leftFieldName leftArguments leftDirectives leftSelectionSet,
      .field rightResponseName rightFieldName rightArguments rightDirectives
        rightSelectionSet =>
        leftResponseName == rightResponseName
        && leftFieldName == rightFieldName
        && Argument.argumentsSyntacticallyEquivalentBool leftArguments rightArguments
        && Algorithms.directiveListEqBool leftDirectives rightDirectives
        && selectionSetSyntacticallyIncludesBool leftSelectionSet rightSelectionSet
    | .inlineFragment leftTypeCondition leftDirectives leftSelectionSet,
      .inlineFragment rightTypeCondition rightDirectives rightSelectionSet =>
        leftTypeCondition == rightTypeCondition
        && Algorithms.directiveListEqBool leftDirectives rightDirectives
        && selectionSetSyntacticallyIncludesBool leftSelectionSet rightSelectionSet
    | _, _ => false

  -- Selection order and additional left selections do not affect inclusion. This check
  -- deliberately stays syntax-only; condition normalization, field merging, and all
  -- non-matching cases remain the responsibility of the general checker.
  def selectionSetSyntacticallyIncludesBool (left : List Selection)
      : List Selection -> Bool
    | [] => true
    | right :: rest =>
        left.any (fun candidate => selectionSyntacticallyIncludesBool candidate right)
        && selectionSetSyntacticallyIncludesBool left rest
end

-- The semantic reference checker consumes one fuel unit at every nested response
-- boundary. The depth guard ensures that a successful syntax shortcut never bypasses
-- the reference check's explicit exhaustion behavior.
def selectionSetSyntacticInclusionShortcutBool (responseFuel : Nat)
    (left right : List Selection)
    : Bool :=
  decide (selectionSetResponseDepth right ≤ responseFuel)
  && selectionSetSyntacticallyIncludesBool left right

-----------------------------------------------------------------------------------------
-- Condition-region search infrastructure
-----------------------------------------------------------------------------------------

def splitPossibleTypeRegion (region allowed : List Name) : List (List Name) :=
  let included := region.filter allowed.contains
  let excluded := region.filter fun typeName => !allowed.contains typeName
  (if included.isEmpty then [] else [included])
  ++ (if excluded.isEmpty then [] else [excluded])

def refinePossibleTypeRegions (regions : List (List Name))
    (condition : SelectionConditions.Condition)
    : List (List Name) :=
  regions.flatMap
    fun region =>
      splitPossibleTypeRegion region condition.possibleTypes

-- One recursive obligation produced after shallow response-name and resolver-call
-- comparison. `possibleTypes` is the exact inclusive child region contributed by every
-- concrete field definition with these merged child selection sets. It avoids widening
-- a covariant concrete return to every implementation of its interface.
structure InclusionChildTask where
  possibleTypes : List Name
  leftSelectionSet : List Selection
  rightSelectionSet : List Selection
deriving Repr

-- A matching scalar field closes the obligation at this scope; a composite field
-- contributes one recursive child task. `none` from the matcher remains reserved for
-- the absence of a provenance-compatible left field group.
inductive InclusionChildMatch where
  | leaf
  | composite (task : InclusionChildTask)
deriving Repr

def matchInclusionChildTask? (schema : Schema) (rightGroup : Name × List ExecutableField)
    : List (Name × List ExecutableField) -> Option InclusionChildMatch
  | [] => none
  | leftGroup :: rest =>
      if leftGroup.1 == rightGroup.1 then
        match leftGroup.2, rightGroup.2 with
        | leftField :: _leftRest, rightField :: _rightRest =>
            if leftField.parentType == rightField.parentType
                && leftField.fieldName == rightField.fieldName
                && Argument.argumentsSyntacticallyEquivalentBool leftField.arguments
                    rightField.arguments then
              match schema.lookupField rightField.parentType rightField.fieldName with
              | none => none
              | some definition =>
                  if definition.outputType.isCompositeBool schema then
                    some
                      (.composite
                        {
                          possibleTypes :=
                            schema.getPossibleTypes definition.outputType.namedType
                          leftSelectionSet :=
                            executableFieldsMergedSelectionSet leftGroup.2
                          rightSelectionSet :=
                            executableFieldsMergedSelectionSet rightGroup.2
                        })
                  else
                    some .leaf
            else
              matchInclusionChildTask? schema rightGroup rest
        | _, _ => matchInclusionChildTask? schema rightGroup rest
      else
        matchInclusionChildTask? schema rightGroup rest

def inclusionChildTasks? (schema : Schema)
    (leftGroups : List (Name × List ExecutableField))
    : List (Name × List ExecutableField) -> Option (List InclusionChildTask)
  | [] => some []
  | rightGroup :: rest => do
      let childMatch ← matchInclusionChildTask? schema rightGroup leftGroups
      let tasks ← inclusionChildTasks? schema leftGroups rest
      match childMatch with
      | .leaf => pure tasks
      | .composite task => pure (task :: tasks)

def executableFieldWithParentType (parentType : Name) (field : ExecutableField)
    : ExecutableField :=
  { field with parentType }

def executableGroupWithParentType (parentType : Name)
    (group : Name × List ExecutableField)
    : Name × List ExecutableField :=
  (group.1, group.2.map (executableFieldWithParentType parentType))

def executableGroupsWithParentType (parentType : Name)
    (groups : List (Name × List ExecutableField))
    : List (Name × List ExecutableField) :=
  groups.map (executableGroupWithParentType parentType)

def inclusionChildTaskEqBool (left right : InclusionChildTask) : Bool :=
  left.possibleTypes == right.possibleTypes
  && Algorithms.selectionSetEqBool left.leftSelectionSet right.leftSelectionSet
  && Algorithms.selectionSetEqBool left.rightSelectionSet right.rightSelectionSet

def insertInclusionChildTask (task : InclusionChildTask)
    : List InclusionChildTask -> List InclusionChildTask
  | [] => [task]
  | candidate :: rest =>
      if inclusionChildTaskEqBool task candidate then
        candidate :: rest
      else
        candidate :: insertInclusionChildTask task rest

def deduplicateInclusionChildTasks : List InclusionChildTask -> List InclusionChildTask
  | [] => []
  | task :: rest =>
      insertInclusionChildTask task (deduplicateInclusionChildTasks rest)

-- Computes child obligations for every concrete parent type while reusing the already
-- collected field groups. Duplicate obligations are removed, while covariant returns
-- with different possible-type sets remain separate.
def inclusionChildTasksForParentTypes? (schema : Schema)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    : List Name -> Option (List InclusionChildTask)
  | [] => some []
  | parentType :: rest => do
      let tasks ←
        inclusionChildTasks? schema
          (executableGroupsWithParentType parentType leftGroups)
          (executableGroupsWithParentType parentType rightGroups)
      let restTasks ←
        inclusionChildTasksForParentTypes? schema leftGroups rightGroups rest
      pure <| deduplicateInclusionChildTasks (tasks ++ restTasks)

-----------------------------------------------------------------------------------------
-- Guarded field-group checker
-----------------------------------------------------------------------------------------

-- Grouping conditioned field occurrences by response name lets inclusion split only
-- the conditions that can change that field group.
structure GuardedFieldGroup where
  responseName : Name
  entries : List SelectionConditions.ConditionedField
deriving Repr

-- Adds one occurrence to its response-name group while preserving the first occurrence
-- order of groups and the source order of entries within each group.
def addGuardedFieldEntry (entry : SelectionConditions.ConditionedField)
    : List GuardedFieldGroup -> List GuardedFieldGroup
  | [] => [{ responseName := entry.field.responseName, entries := [entry] }]
  | group :: rest =>
      if entry.field.responseName == group.responseName then
        { group with entries := group.entries ++ [entry] } :: rest
      else
        group :: addGuardedFieldEntry entry rest

-- Compiles a flat conditioned-field boundary into response-name-local guarded groups in
-- one pass. Cumulative conditions contain everything needed to decide whether an
-- occurrence is active; no condition-tree shape is required.
def guardedFieldGroups (entries : List SelectionConditions.ConditionedField)
    : List GuardedFieldGroup :=
  entries.foldl (fun groups entry => addGuardedFieldEntry entry groups) []

def findGuardedFieldGroup? (responseName : Name)
    : List GuardedFieldGroup -> Option GuardedFieldGroup
  | [] => none
  | group :: rest =>
      if responseName == group.responseName then
        some group
      else
        findGuardedFieldGroup? responseName rest

def guardedFieldGroupConditions (group : GuardedFieldGroup)
    : List SelectionConditions.Condition :=
  group.entries.map SelectionConditions.ConditionedField.condition

def guardedFieldGroupTypeRegions (parentRegion : List Name)
    (left right : GuardedFieldGroup)
    : List (List Name) :=
  let conditions := guardedFieldGroupConditions left ++ guardedFieldGroupConditions right
  conditions.foldl refinePossibleTypeRegions
    (if parentRegion.isEmpty then [] else [parentRegion])

def guardedFieldGroupBooleanVariables (left right : GuardedFieldGroup) : List Name :=
  ((left.entries ++ right.entries).flatMap
    fun entry =>
      entry.condition.booleanCondition.map
        SelectionConditions.BooleanLiteral.variableName).eraseDups

def guardedFieldExecutableFields (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (responseName : Name)
    (entries : List SelectionConditions.ConditionedField)
    : List ExecutableField :=
  entries.flatMap
    fun entry =>
      if entry.condition.allows variableValues runtimeType then
        [{
          parentType := executionParentType
          responseName
          fieldName := entry.field.fieldName
          arguments := entry.field.arguments
          selectionSet := entry.field.selectionSet
        }]
      else
        []

def executableFieldsAsGroup (responseName : Name) (fields : List ExecutableField)
    : List (Name × List ExecutableField) :=
  match fields with
  | [] => []
  | field :: rest => [(responseName, field :: rest)]

def conditionedFieldResolverCallEqBool (left right : SelectionConditions.ConditionedField)
    : Bool :=
  left.field.fieldName == right.field.fieldName
  && Argument.argumentsSyntacticallyEquivalentBool left.field.arguments
      right.field.arguments

def guardedFieldEntriesAtRuntimeType (runtimeType : Name)
    (entries : List SelectionConditions.ConditionedField)
    : List SelectionConditions.ConditionedField :=
  entries.filter fun entry => entry.condition.possibleTypes.contains runtimeType

-- Symbolically decides a scalar field group without enumerating its Boolean
-- assignments. Type conditions have already been flattened into `possibleTypes`.
-- Requiring one resolver call throughout the runtime-type slice matches the field
-- merge invariant directly, while clause subtraction handles unions such as
-- `@include(if: $x)` together with `@skip(if: $x)`.
def guardedScalarFieldIncludesAtRuntimeTypeBool (schema : Schema)
    (fixedExecutionParentType : Option Name) (runtimeType : Name)
    (left right : GuardedFieldGroup)
    : Bool :=
  let leftEntries := guardedFieldEntriesAtRuntimeType runtimeType left.entries
  let rightEntries := guardedFieldEntriesAtRuntimeType runtimeType right.entries
  left.responseName == right.responseName
  && match rightEntries with
      | [] => true
      | rightHead :: _rightRest =>
          let executionParentType := fixedExecutionParentType.getD runtimeType
          match schema.lookupField executionParentType rightHead.field.fieldName with
          | none => false
          | some definition =>
              !definition.outputType.isCompositeBool schema
              && (leftEntries.all
                    fun leftEntry =>
                      conditionedFieldResolverCallEqBool leftEntry rightHead)
              && (rightEntries.all
                    fun rightEntry =>
                      conditionedFieldResolverCallEqBool rightEntry rightHead)
              && (rightEntries.all
                    fun rightEntry =>
                      SelectionConditions.booleanConditionCoveredByBool
                        rightEntry.condition.booleanCondition
                        (leftEntries.map
                          fun leftEntry =>
                            leftEntry.condition.booleanCondition))

def guardedScalarFieldIncludesBool (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name) (left right : GuardedFieldGroup)
    (regions : List (List Name))
    : Bool :=
  match responseFuel with
  | 0 => false
  | _responseFuel + 1 =>
      regions.all
        fun region =>
          region.all
            fun runtimeType =>
              guardedScalarFieldIncludesAtRuntimeTypeBool schema
                fixedExecutionParentType runtimeType left right

-- The composite counterpart of the local shortcut. It deliberately handles the
-- one-to-one field case: field merging stays with the complete checker, while a
-- broader type/directive guard can still bypass recursive analysis when the child
-- selections have the verified syntax witness.
def guardedCompositeFieldIncludesAtRuntimeTypeBool (schema : Schema)
    (childFuel : Nat) (fixedExecutionParentType : Option Name) (runtimeType : Name)
    (left right : GuardedFieldGroup)
    : Bool :=
  let leftEntries := guardedFieldEntriesAtRuntimeType runtimeType left.entries
  let rightEntries := guardedFieldEntriesAtRuntimeType runtimeType right.entries
  left.responseName == right.responseName
  && match rightEntries with
      | [] => true
      | [rightEntry] =>
          match leftEntries with
          | [leftEntry] =>
              let executionParentType := fixedExecutionParentType.getD runtimeType
              conditionedFieldResolverCallEqBool leftEntry rightEntry
              && SelectionConditions.booleanConditionCoveredByBool
                  rightEntry.condition.booleanCondition
                  [leftEntry.condition.booleanCondition]
              && match schema.lookupField executionParentType
                        rightEntry.field.fieldName with
                  | none => false
                  | some definition =>
                      definition.outputType.isCompositeBool schema
                      && selectionSetSyntacticInclusionShortcutBool childFuel
                          leftEntry.field.selectionSet rightEntry.field.selectionSet
          | _ => false
      | _ => false

def guardedCompositeFieldIncludesBool (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name) (left right : GuardedFieldGroup)
    (regions : List (List Name))
    : Bool :=
  match responseFuel with
  | 0 => false
  | childFuel + 1 =>
      regions.all
        fun region =>
          region.all
            fun runtimeType =>
              guardedCompositeFieldIncludesAtRuntimeTypeBool schema childFuel
                fixedExecutionParentType runtimeType left right

def guardedFieldGroupLocallyIncludesBool (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name) (left right : GuardedFieldGroup)
    (regions : List (List Name))
    : Bool :=
  guardedScalarFieldIncludesBool schema responseFuel fixedExecutionParentType
    left right regions
  || guardedCompositeFieldIncludesBool schema responseFuel fixedExecutionParentType
      left right regions

mutual
  -- Checks one response name for a fixed Boolean assignment over every relevant type
  -- region. Conditions belonging exclusively to other response names never enter this
  -- search space.
  def guardedFieldGroupIncludesForRegionsWithFuel (schema : Schema)
      (responseFuel : Nat) (fixedExecutionParentType : Option Name)
      (variableValues : VariableValues) (left right : GuardedFieldGroup)
      (regions : List (List Name))
      : Bool :=
    regions.all
      fun region =>
        match region with
        | [] => true
        | runtimeType :: _rest =>
            let executionParentType := fixedExecutionParentType.getD runtimeType
            let leftFields :=
              guardedFieldExecutableFields variableValues executionParentType
                runtimeType left.responseName left.entries
            let rightFields :=
              guardedFieldExecutableFields variableValues executionParentType
                runtimeType right.responseName right.entries
            match responseFuel with
            | 0 => rightFields.isEmpty
            | responseFuel + 1 =>
                let parentTypes :=
                  match fixedExecutionParentType with
                  | some parentType => [parentType]
                  | none => region
                let leftGroups := executableFieldsAsGroup left.responseName leftFields
                let rightGroups := executableFieldsAsGroup right.responseName rightFields
                match inclusionChildTasksForParentTypes? schema leftGroups rightGroups
                        parentTypes with
                | none => false
                | some tasks =>
                    tasks.all
                      fun task =>
                        selectionSetSyntacticInclusionShortcutBool responseFuel
                          task.leftSelectionSet task.rightSelectionSet
                        ||  let leftChildEntries :=
                              SelectionConditions.ofTypeRegion schema task.possibleTypes
                                task.leftSelectionSet
                            let rightChildEntries :=
                              SelectionConditions.ofTypeRegion schema task.possibleTypes
                                task.rightSelectionSet
                            guardedFieldGroupsIncludeWithFuel schema responseFuel none
                              variableValues (guardedFieldGroups leftChildEntries)
                              (guardedFieldGroups rightChildEntries)
  termination_by (responseFuel, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.right <;> omega

  -- Enumerates the Boolean assignments that can change one field group, then checks
  -- the type regions under each complete assignment.
  def guardedFieldGroupIncludesWithFuel (schema : Schema)
      (responseFuel : Nat) (fixedExecutionParentType : Option Name)
      (variableValues : VariableValues) (remainingBooleanVariables : List Name)
      (left right : GuardedFieldGroup) (regions : List (List Name))
      : Bool :=
    match remainingBooleanVariables with
    | variableName :: rest =>
        match inputValueBoolean? variableValues (.variable variableName) with
        | some _value =>
            guardedFieldGroupIncludesWithFuel schema responseFuel
              fixedExecutionParentType variableValues rest left right regions
        | none =>
            guardedFieldGroupIncludesWithFuel schema responseFuel
              fixedExecutionParentType
              ((variableName, .boolean false) :: variableValues) rest left right regions
            && guardedFieldGroupIncludesWithFuel schema responseFuel
                fixedExecutionParentType
                ((variableName, .boolean true) :: variableValues) rest left right regions
    | [] =>
        guardedFieldGroupIncludesForRegionsWithFuel schema responseFuel
          fixedExecutionParentType variableValues left right regions
  termination_by (responseFuel, 1, remainingBooleanVariables.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.right <;> omega

  -- Universal inclusion is the conjunction of the obligations for response names that
  -- can occur on the included (right) side. A missing left group is represented by an
  -- empty guarded group and therefore fails exactly when the right group is feasible.
  def guardedFieldGroupsIncludeWithFuel (schema : Schema)
      (responseFuel : Nat) (fixedExecutionParentType : Option Name)
      (variableValues : VariableValues) (leftGroups : List GuardedFieldGroup)
      : List GuardedFieldGroup -> Bool
    | [] => true
    | right :: rest =>
        let left :=
          (findGuardedFieldGroup? right.responseName leftGroups).getD
            { responseName := right.responseName, entries := [] }
        let parentRegion :=
          match fixedExecutionParentType with
          | some parentType => schema.getPossibleTypes parentType
          | none =>
              (guardedFieldGroupConditions left ++ guardedFieldGroupConditions right)
              |>.flatMap SelectionConditions.Condition.possibleTypes
              |>.eraseDups
        let regions := guardedFieldGroupTypeRegions parentRegion left right
        (guardedFieldGroupLocallyIncludesBool schema responseFuel fixedExecutionParentType
            left right regions
          || guardedFieldGroupIncludesWithFuel schema responseFuel
              fixedExecutionParentType variableValues
              (guardedFieldGroupBooleanVariables left right) left right
              regions)
        && guardedFieldGroupsIncludeWithFuel schema responseFuel
            fixedExecutionParentType variableValues leftGroups rest
  termination_by rightGroups => (responseFuel, 2, rightGroups.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.left <;> omega
      | apply Prod.Lex.right; apply Prod.Lex.right <;> omega
end

-- Checks a selection-set scope starting from a partial Boolean assignment. Any
-- relevant unassigned variables are split by the guarded field-group search.
def selectionSetIncludesBoolWithPartialAssignment (schema : Schema)
    (responseFuel : Nat) (parentType : Name) (variableValues : VariableValues)
    (leftSelectionSet rightSelectionSet : List Selection)
    : Bool :=
  let leftEntries := SelectionConditions.ofSelectionSet schema parentType leftSelectionSet
  let rightEntries :=
    SelectionConditions.ofSelectionSet schema parentType rightSelectionSet
  guardedFieldGroupsIncludeWithFuel schema responseFuel (some parentType)
    variableValues (guardedFieldGroups leftEntries)
    (guardedFieldGroups rightEntries)

def selectionSetIncludesBool (schema : Schema) (responseFuel : Nat)
    (parentType : Name) (leftSelectionSet rightSelectionSet : List Selection)
    : Bool :=
  selectionSetIncludesBoolWithPartialAssignment schema responseFuel parentType []
    leftSelectionSet rightSelectionSet

-- The executable inclusion checker. Each response name is analyzed independently:
-- it refines only the type conditions and Boolean variables that can affect that
-- field group, then recursively analyzes merged composite children. Both
-- operations are explored under the same assignments, and field arguments are
-- compared symbolically. The function is total on raw syntax; callers should establish
-- schema well-formedness, operation validity, and composite-return inhabitance before
-- using it as a semantic decision procedure, then establish the run-specific premises
-- of `includes` before applying an accepted result.
def includesBool (schema : Schema) (left right : Operation) : Bool :=
  if left.rootType schema == right.rootType schema
      && sharedVariableDefinitionsSyntacticallyCompatibleBool left.variableDefinitions
          right.variableDefinitions then
    selectionSetIncludesBool schema (right.size + 1)
      (right.rootType schema) left.selectionSet right.selectionSet
  else
    false

-----------------------------------------------------------------------------------------
-- `includesBool` soundness and completeness statements
-----------------------------------------------------------------------------------------

-- Public soundness statement for the executable checker: whenever it accepts two valid
-- operations under a well-formed schema, semantic query inclusion follows. Its theorem
-- witness is `QueryInclusion.includesBool_sound` in the corresponding proof module.
def IncludesBoolSound (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> includesBool schema left right = true
  -> includes schema left right

-- An operation-local inhabitance condition for composite field returns. It requires
-- possible object types only for fields that can occur in the operation. Runtime-type
-- and directive conditions are not themselves required to be feasible: an impossible
-- inline-fragment scope contributes no field-execution obligation.
mutual
  def selectionCompositeFieldTypesInhabited (schema : Schema) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∀ definition,
          schema.lookupField parentType fieldName = some definition
          -> definition.outputType.isCompositeBool schema = true
          -> schema.getPossibleTypes definition.outputType.namedType ≠ []
              ∧ ∀ runtimeType,
                  schema.typeIncludesObjectBool definition.outputType.namedType
                      runtimeType
                    = true
                  -> selectionSetCompositeFieldTypesInhabited schema runtimeType
                      selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetCompositeFieldTypesInhabited schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typeIncludesObjectBool typeCondition parentType = true
        -> selectionSetCompositeFieldTypesInhabited schema parentType selectionSet

  def selectionSetCompositeFieldTypesInhabited (schema : Schema)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> selectionCompositeFieldTypesInhabited schema parentType selection
end

def operationCompositeFieldTypesInhabited (schema : Schema) (operation : Operation)
    : Prop :=
  selectionSetCompositeFieldTypesInhabited schema (operation.rootType schema)
    operation.selectionSet

-- "Coercible" assumption syntactically ensures that execution has no coercion errors.
-- Completeness needs one argument-coercible extension of every complete Boolean branch
-- explored by the reference checker. Prefixing the extension with the branch assignment
-- keeps those condition values authoritative while allowing the witness to supply any
-- additional variables used by field arguments.
def comparisonBranchesArgumentCoercible (schema : Schema) (left right : Operation)
    : Prop :=
  ∀ conditionValues,
    conditionValues
      ∈ booleanVariableAssignments
          (comparisonConditionVariables left.selectionSet right.selectionSet)
    -> ∃ remainingValues,
        operationArgumentsCoercible schema (conditionValues ++ remainingValues) left
        ∧ operationArgumentsCoercible schema (conditionValues ++ remainingValues) right

-- Public completeness direction for valid operations. Shared-definition compatibility
-- is part of `includes` itself and therefore does not need a separate premise here.
-- Argument-coercible branch extensions and composite-return inhabitance rule out vacuous
-- semantic inclusion by supplying an error-free witness for every checked branch.
-- Its theorem witness is `QueryInclusion.includesBool_complete` in the corresponding
-- proof module.
def IncludesBoolComplete (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationCompositeFieldTypesInhabited schema left
  -> operationCompositeFieldTypesInhabited schema right
  -> comparisonBranchesArgumentCoercible schema left right
  -> includes schema left right
  -> includesBool schema left right = true

end QueryInclusion
end GraphQL
