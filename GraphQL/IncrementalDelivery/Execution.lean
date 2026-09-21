import GraphQL.Execution
import GraphQL.IncrementalDelivery.Operation

/-! Separate execution for incremental-delivery draft PR #1110, revision
045e19363c2b55f127960bd3b5e8072a15b29aec (2026-08-18).

This module accepts GraphQL.IncrementalDelivery.Operation and an opaque WorkScheduler,
and returns ExecutionResult directly. Future events are supplied one observation at a time.
It shares resolver values, response data, input coercion, and null-bubbling primitives
with GraphQL.Execution; field collection, planning, completion, and delivery are separate.
All incremental execution definitions remain together in this file for review.

The draft leaves CreateWorkQueue unspecified and does not yet wire @stream into
CompleteListValue. The model retains finite pure resolver outcomes, but no concrete scheduler.
Named-fragment delivery and incremental validation are not modeled here yet.
Trace observations and correctness statements belong to IncrementalDelivery.Correctness.
-/

namespace GraphQL
namespace IncrementalDelivery
namespace Execution

abbrev ResolverValue (ObjectRef : Type := PUnit) :=
  GraphQL.Execution.ResolverValue ObjectRef

abbrev ResponseValue := GraphQL.Execution.ResponseValue
abbrev Response := GraphQL.Execution.Response
abbrev Result (α : Type) := GraphQL.Execution.Result α
abbrev Resolvers (ObjectRef : Type := PUnit) := GraphQL.Execution.Resolvers ObjectRef
abbrev VariableValues := GraphQL.Execution.VariableValues

namespace ResponseValue

export GraphQL.Execution.ResponseValue (null scalar object list)

end ResponseValue

export GraphQL.Execution (
  lookupVariableValue? coerceArgumentValues inputValueBoolean? runtimeObjectType?
  doesFragmentTypeApplyBool handleFieldError nonNullCompletion singleFieldResult
  resolveFieldValue typeDefinitionsExecutionCompletionFuel selectionSetResultToResponse
)

namespace Result

export GraphQL.Execution.Result (combine)

end Result

variable {ObjectRef : Type}

-----------------------------------------------------------------------------------------
-- Field Collection
-----------------------------------------------------------------------------------------

/-- Spec 6.1.2 `CoerceVariableValues`, default-value branch: partial; for every missing
variable, materialize its constant operation default, including an explicit `null`
default. Supplied values, including supplied `null`, take precedence. Full input coercion
and request errors remain outside the modeled execution result, so supplied values are
retained and assumed already coerced and type-conformant.
-/
def coerceVariableValues (operation : Operation) (variableValues : VariableValues)
    : VariableValues :=
  operation.variableDefinitions.foldl
    (fun coercedValues variableDefinition =>
      match lookupVariableValue? coercedValues variableDefinition.name with
      | some _value => coercedValues
      | none =>
          match variableDefinition.defaultValue with
          | some defaultValue =>
              (variableDefinition.name, defaultValue) :: coercedValues
          | none => coercedValues)
    variableValues

/-- Spec 6.3.2 `CollectFields` inline `@skip`/`@include` checks: local per-directive
helper, not a named spec algorithm. The spec skips or includes a selection exactly when
the `if` condition "is true"; a condition that does not resolve to a Boolean (an undefined
variable, an explicit `null`, or a non-Boolean binding) fails that test without an error,
so it behaves like `false` for both directives: `@skip` keeps the selection and `@include`
drops it.
-/
def directiveAllowsSelectionBool (variableValues : VariableValues)
    : DirectiveApplication -> Bool
  | .skip ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => !value
      | none => true
  | .include ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => value
      | none => false
  | .defer .. | .stream .. => true

/-- Spec 6.3.2 `CollectFields` inline directive checks: local helper over one selection's
directive list, not a named spec algorithm.
-/
def selectionDirectivesAllowBool (variableValues : VariableValues)
    (directives : List DirectiveApplication)
    : Bool :=
  directives.all (fun directive => directiveAllowsSelectionBool variableValues directive)

/-- Response 7, Incremental Pending Notice: an omitted label and an explicit null label
are distinct. Only string literals and null are valid label arguments.
-/
inductive DirectiveLabel where
  | null
  | string (value : String)
deriving Repr

instance : Coe String DirectiveLabel := ⟨DirectiveLabel.string⟩

/-- A fresh defer-usage identity denotes an occurrence, not a label or structural
syntax value. The supply is shared by collection and completion, including distinct
list positions. Only inline fragments are modeled here.
-/

structure DeferUsage where
  key : Nat
  ancestors : List Nat := []
  label : Option DirectiveLabel := none
deriving Repr

/-- Spec 6.3.2 collected field entries: non-spec helper carrying the data needed to
execute one grouped response name.
-/
structure ExecutableField where
  fieldName : Name
  arguments : List Argument
  selectionSet : List Selection
  directives : List DirectiveApplication := []
  deferUsage : Option DeferUsage := none
deriving Repr

abbrev CollectedFieldsMap := List (Name × List ExecutableField)

/-- Spec 6.3.2 collected fields map helper: inserts one existing group into another map.
-/
def addExecutableGroup (group : Name × List ExecutableField)
    : List (Name × List ExecutableField) -> List (Name × List ExecutableField)
  | [] => [group]
  | (responseName, fields) :: rest =>
      if responseName == group.fst then
        (responseName, fields ++ group.snd) :: rest
      else
        (responseName, fields) :: addExecutableGroup group rest

/-- Spec 6.3.2 `CollectFields` grouping merge for list-backed response-name maps. -/
def mergeExecutableGroups (left right : List (Name × List ExecutableField))
    : List (Name × List ExecutableField) :=
  right.foldl (fun grouped group => addExecutableGroup group grouped) left

structure FieldCollection where
  fields : CollectedFieldsMap := []
  newDeferUsages : List DeferUsage := []
deriving Repr

def FieldCollection.append (left right : FieldCollection) : FieldCollection :=
  {
    fields := mergeExecutableGroups left.fields right.fields
    newDeferUsages := left.newDeferUsages ++ right.newDeferUsages
  }

/-- Labels must be string literals or null in valid operations. -/
def directiveLabel? : Option InputValue -> Option DirectiveLabel
  | some (.string value) => some (.string value)
  | some .null => some .null
  | _ => none

/-- The draft uses "is not false", including for explicit null/undefined conditions. -/
def activeDefer? (variableValues : VariableValues)
    : List DirectiveApplication -> Option (Option DirectiveLabel)
  | [] => none
  | .defer condition label :: _ =>
      if inputValueBoolean? variableValues condition == some false then
        none
      else
        some (directiveLabel? label)
  | _ :: rest => activeDefer? variableValues rest

def freshExecutionKey : StateM Nat Nat := do
  let key ← get
  set (key + 1)
  return key

/-! Spec 6.3.2 `CollectFields` and `CollectSubfields`: partial; list-backed ordered
grouping of executable fields by response name.
-/

mutual
  /-- Spec 6.3.2 `CollectFields` selection step: partial; handles built-in directives and
  inline fragments.
  -/
  def collectSelection (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (deferUsage : Option DeferUsage)
      : Selection -> StateM Nat FieldCollection
    | .field responseName fieldName arguments directives selectionSet => do
        if !selectionDirectivesAllowBool variableValues directives then
          return {}
        return {
          fields :=
            [(
              responseName,
              [{
                fieldName := fieldName
                arguments := arguments
                directives := directives
                selectionSet := selectionSet
                deferUsage := deferUsage
              }]
            )]
        }
    | .inlineFragment condition directives selectionSet => do
        if !selectionDirectivesAllowBool variableValues directives then
          return {}
        if !(condition.all (doesFragmentTypeApplyBool schema parentType source)) then
          return {}
        match activeDefer? variableValues directives with
        | none =>
            collectFields schema variableValues parentType source selectionSet deferUsage
        | some label =>
            let key ← freshExecutionKey
            let usage : DeferUsage :=
              {
                key := key
                label := label
                ancestors :=
                  deferUsage.map (fun parent => parent.key :: parent.ancestors) |>.getD []
              }
            let collected ←
              collectFields schema variableValues parentType source selectionSet
                (some usage)
            return { collected with newDeferUsages := usage :: collected.newDeferUsages }

  /-- Spec 6.3.2 `CollectFields`: partial; list-backed ordered grouping of executable
  fields by response name.
  -/
  def collectFields (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selections : List Selection) (deferUsage : Option DeferUsage := none)
      : StateM Nat FieldCollection := do
    match selections with
    | [] => return {}
    | selection :: rest =>
        let head ←
          collectSelection schema variableValues parentType source deferUsage selection
        let tail ← collectFields schema variableValues parentType source rest deferUsage
        return head.append tail
end

/-- Spec 6.3.2 `CollectSubfields`: all grouped fields for one response name contribute
child selections, which are collected under the runtime object type.
-/
def collectSubfields (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (source : ResolverValue ObjectRef)
    : List ExecutableField -> StateM Nat FieldCollection
  | [] => pure {}
  | field :: rest => do
      let head ←
        collectFields schema variableValues objectType source field.selectionSet
          field.deferUsage
      let tail ← collectSubfields schema variableValues objectType source rest
      return head.append tail

-----------------------------------------------------------------------------------------
-- Incremental completion and execution plans
-----------------------------------------------------------------------------------------

/-! Resolvers are pure and return finite lists. Incremental work therefore records
finite completion trees, evaluated here but made observable only by the delivery
source. These are fixed outcomes, not a completion order or host-language futures.
-/

inductive ResponsePathSegment where
  | field (name : Name)
  | index (value : Nat)
deriving Repr, DecidableEq, BEq

abbrev ResponsePath := List ResponsePathSegment

structure DeliveryNode where
  key : Nat
  path : ResponsePath
  label : Option DirectiveLabel := none
deriving Repr

structure DeferredFragment where
  node : DeliveryNode
  ancestors : List DeliveryNode := []
deriving Repr

structure StreamUsage where
  label : Option DirectiveLabel
  initialCount : Nat
deriving Repr

/-- Undefined variables activate the directive argument's default; explicit null does not.
-/
def streamInitialCount? (variables : VariableValues) : InputValue -> Option Nat
  | .int value => if value < 0 then none else some value.toNat
  | .variable name =>
      match lookupVariableValue? variables name with
      | none => some 0
      | some (.int value) => if value < 0 then none else some value.toNat
      | _ => none
  | _ => none

/-- Model helper for the @stream directive contract, not a named draft algorithm. -/
def getStreamUsage (variables : VariableValues)
    : List DirectiveApplication -> Except Nat (Option StreamUsage)
  | [] => .ok none
  | .stream condition label count :: _ =>
      if inputValueBoolean? variables condition == some false then
        .ok none
      else
        match streamInitialCount? variables count with
        | none => .error 1
        | some initialCount =>
            .ok (some { label := directiveLabel? label, initialCount := initialCount })
  | _ :: rest => getStreamUsage variables rest

/-- A task may contribute to multiple fragments, but its data is delivered only once. A
stream contains one finite completion per remaining outer-list item.
-/
inductive Work where
  | empty
  | append (left right : Work)
  | deferred (groups : List DeferredFragment) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
  | stream (node : DeliveryNode) (items : List (Result ResponseValue × Work))
deriving Repr

structure Completion (α : Type) where
  result : Result α
  work : Work := .empty
deriving Repr

namespace Completion

def pure (value : α) : Completion α := { result := .ok (value, 0) }

def error (errors : Nat := 1) : Completion α := { result := .error errors }

def combine (f : α -> β -> γ) (left : Completion α) (right : Completion β)
    : Completion γ :=
  let result := Result.combine f left.result right.result
  match result with
  | .error errors => error errors
  | .ok _ => { result := result, work := .append left.work right.work }

def map (f : α -> β) (completed : Completion α) : Completion β :=
  match completed.result with
  | .error errors => error errors
  | .ok (value, errors) => { result := .ok (f value, errors), work := completed.work }

def catchNull (wrap : α -> ResponseValue) (completed : Completion α)
    : Completion ResponseValue :=
  match completed.result with
  | .error errors => { result := .ok (.null, errors) }
  | .ok (value, errors) =>
      { result := .ok (wrap value, errors), work := completed.work }

def nonNull (completed : Completion ResponseValue) : Completion ResponseValue :=
  match nonNullCompletion completed.result with
  | .error errors => error errors
  | .ok result => { completed with result := .ok result }

end Completion

/-- Spec `GetFilteredDeferUsageSet`. An immediate occurrence dominates all deferred
occurrences. Otherwise remove usages with an ancestor in the set, keeping the full field
details for subcollection.
-/
def getFilteredDeferUsageSet (fields : List ExecutableField) : List Nat :=
  if fields.any (fun field => field.deferUsage.isNone) then
    []
  else
    let usages := fields.filterMap ExecutableField.deferUsage
    let keys := (usages.map DeferUsage.key).eraseDups
    keys.filter
      (fun key =>
        !(usages.any
            (fun usage =>
              usage.key == key && usage.ancestors.any keys.contains)))

def deferUsageSetsEquivalent (left right : List Nat) : Bool :=
  left.all right.contains && right.all left.contains

structure ExecutionPlan where
  collectedFieldsMap : CollectedFieldsMap := []
  newCollectedFieldsMaps : List (List Nat × CollectedFieldsMap) := []
deriving Repr

def addExecutionPartition (usages : List Nat) (group : Name × List ExecutableField)
    : List (List Nat × CollectedFieldsMap) -> List (List Nat × CollectedFieldsMap)
  | [] => [(usages, [group])]
  | (keys, fields) :: rest =>
      if deferUsageSetsEquivalent keys usages then
        (keys, fields ++ [group]) :: rest
      else
        (keys, fields) :: addExecutionPartition usages group rest

/-- Spec `BuildExecutionPlan`: partition only; do not execute or create work here. -/
def buildExecutionPlan (fields : CollectedFieldsMap) (parentDeferUsages : List Nat := [])
    : ExecutionPlan :=
  fields.foldl
    (fun plan group =>
      let usages := getFilteredDeferUsageSet group.2
      if deferUsageSetsEquivalent usages parentDeferUsages then
        { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
      else
        {
          plan with
            newCollectedFieldsMaps :=
              addExecutionPartition usages group plan.newCollectedFieldsMaps
        })
    {}

-----------------------------------------------------------------------------------------
-- Executing Collected Fields & Execution Plans
-----------------------------------------------------------------------------------------

abbrev DeferMap := List DeferredFragment

def lookupDeferredFragment? (deferMap : DeferMap) (key : Nat) : Option DeferredFragment :=
  deferMap.find? (fun group => group.node.key == key)

/-- Spec `GetNewDeferMap`; flattened ancestor lists replace parent-fragment pointers. -/
def getNewDeferMap (usages : List DeferUsage) (path : ResponsePath) (deferMap : DeferMap)
    : DeferMap :=
  usages.foldl
    (fun current usage =>
      current
      ++ [{
            node := { key := usage.key, path := path, label := usage.label }
            ancestors :=
              usage.ancestors.filterMap
                (fun key =>
                  (lookupDeferredFragment? current key).map DeferredFragment.node)
          }])
    deferMap

/-! Spec 6.3.3 `ExecuteCollectedFields`, 6.4 `ExecuteField`, and 6.4.3 `CompleteValue`:
partial fuel-bounded execution model with spec-shaped null bubbling through non-null
wrappers. `Except.error` carries a bubbling error count until a nullable parent can turn
it into response `null`.
-/

mutual
  /-- Spec `ExecuteCollectedFields`: schema lookup, ExecuteField, response-map insertion,
  then work accumulation. Work.append represents the tasks/streams and group union.
  -/
  def executeCollectedFields (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (fields : CollectedFieldsMap) (path : ResponsePath := [])
      (deferUsageSet : List Nat := []) (deferMap : DeferMap := [])
      : StateM Nat (Completion (List (Name × ResponseValue))) := do
    match fields with
    | [] => return .pure []
    | (responseName, group) :: rest =>
        let head ← do
          -- Empty groups and schema misses are counted-error model boundaries.
          match group with
          | [] => pure (.error 1)
          | field :: groupTail =>
              match schema.lookupField parentType field.fieldName with
              | none => pure (.error 1)
              | some definition =>
                  let completed ←
                    executeField schema resolvers variables fuel parentType source
                      definition responseName (field :: groupTail) path deferUsageSet
                      deferMap
                  -- ExecuteCollectedFields owns the response-name entry, not ExecuteField.
                  pure (completed.map (fun value => [(responseName, value)]))
        let tail ←
          executeCollectedFields schema resolvers variables fuel parentType source rest
            path deferUsageSet deferMap
        return Completion.combine List.append head tail

  /-- Spec 6.4 `ExecuteField`: resolve and complete one value with merged subselections.
  The caller supplies the schema definition: its outputType is the spec's fieldType, and
  its arguments supply the shared CoerceArgumentValues projection. responseName is
  explicit so aliases determine paths (the draft says fieldName at this step).
  -/
  def executeField (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (definition : FieldDefinition)
      (responseName : Name) (fields : List ExecutableField) (path : ResponsePath := [])
      (deferUsageSet : List Nat := []) (deferMap : DeferMap := [])
      : StateM Nat (Completion ResponseValue) := do
    match fuel, fields with
    | 0, _ | _, [] => return .error 1
    | fuel + 1, field :: _ =>
        let failed : Completion ResponseValue :=
          { result := handleFieldError definition.outputType }
        match coerceArgumentValues schema variables definition.arguments
                field.arguments with
        | .error => return failed
        | .success arguments =>
            match resolveFieldValue resolvers parentType field.fieldName arguments
                    source with
            | none => return failed
            | some resolved =>
                completeValue schema resolvers variables fuel definition.outputType fields
                  resolved (path ++ [.field responseName]) deferUsageSet deferMap true

  /-- Spec 6.4.3 `CompleteValue`: partial; follows null, list, non-null, and composite
  completion shape. Scalar/enum result coercion is collapsed to string scalar acceptance,
  and abstract type resolution is represented by the runtime object type carried by
  `ResolverValue.object`.
  -/
  def completeValue (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List ExecutableField) (value : ResolverValue ObjectRef)
      (path : ResponsePath := []) (deferUsageSet : List Nat := [])
      (deferMap : DeferMap := []) (allowStream : Bool := true)
      : StateM Nat (Completion ResponseValue) := do
    match fuel, fieldType, value with
    | 0, _, _ => return .error 1
    | fuel, .nonNull inner, value =>
        return (← completeValue schema resolvers variables fuel inner fields value path
                    deferUsageSet deferMap allowStream).nonNull
    | _ + 1, _, .null => return .pure .null
    | _ + 1, .named typeName, .scalar scalar =>
        if (TypeRef.named typeName).isCompositeBool schema then
          return .error 1
        return .pure (.scalar scalar)
    | fuel + 1, .named parentType, source@(.object runtimeType _) =>
        if !schema.typeIncludesObjectBool parentType runtimeType then
          return .error 1
        let collection ← collectSubfields schema variables runtimeType source fields
        let executionPlan := buildExecutionPlan collection.fields deferUsageSet
        let completed ←
          executeExecutionPlan schema resolvers variables fuel runtimeType source
            collection.newDeferUsages executionPlan path deferUsageSet deferMap
        return completed.catchNull ResponseValue.object
    | fuel + 1, .list inner, .list values =>
        completeListValueWithStream schema resolvers variables fuel inner fields values
          path deferUsageSet deferMap allowStream
    | _ + 1, _, _ => return .error 1

  /-- Model extension: the pinned CompleteListValue has no @stream hook. Keep this
  extension distinct from that algorithm. Only the outermost list is eligible; nested list
  wrappers complete synchronously. Reaching initialCount creates a stream boundary even
  when its finite tail is empty; exhaustion before that boundary creates no stream.
  -/
  def completeListValueWithStream (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (inner : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (deferUsageSet : List Nat) (deferMap : DeferMap)
      (allowStream : Bool)
      : StateM Nat (Completion ResponseValue) := do
    let streamUsage :=
      if allowStream then
        getStreamUsage variables (fields.head?.map ExecutableField.directives |>.getD [])
      else
        .ok none
    match streamUsage with
    | .error errors => return { result := .ok (.null, errors) }
    | .ok none =>
        return (← completeListValue schema resolvers variables fuel inner fields values
                    path 0 deferUsageSet deferMap).catchNull
          ResponseValue.list
    | .ok (some usage) =>
        let initial ←
          completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 deferUsageSet deferMap
        match initial.result with
        | .error _ => return initial.catchNull ResponseValue.list
        | .ok _ =>
            let remaining := values.drop usage.initialCount
            if values.length < usage.initialCount then
              return initial.catchNull ResponseValue.list
            let key ← freshExecutionKey
            -- Stream items own their delivery boundary. Enclosing field occurrences
            -- no longer defer their subfields, but nested directive syntax is retained.
            let streamFields :=
              fields.map (fun field => { field with deferUsage := none })
            let items ←
              completeStreamItems schema resolvers variables fuel inner streamFields
                remaining path usage.initialCount
            let completed := initial.catchNull ResponseValue.list
            return {
              completed with
                work :=
                  .append completed.work
                    (.stream { key := key, path := path, label := usage.label } items)
            }

  /-- Spec `CompleteListValue`: complete each indexed item and accumulate values/work.
  index makes the spec's loop counter explicit; normal list completion starts at 0.
  -/
  def completeListValue (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (deferUsageSet : List Nat) (deferMap : DeferMap)
      : StateM Nat (Completion (List ResponseValue)) := do
    match values with
    | [] => return .pure []
    | value :: rest =>
        let head ←
          completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) deferUsageSet deferMap false
        let tail ←
          completeListValue schema resolvers variables fuel itemType fields rest
            path (index + 1) deferUsageSet deferMap
        return Completion.combine List.cons head tail

  /-- Model helper: finite outcomes for the remaining streamed items, each with its own
  completion boundary. The pinned draft gives no algorithm for this step.
  -/
  def completeStreamItems (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat)
      : StateM Nat (List (Result ResponseValue × Work)) := do
    match values with
    | [] => return []
    | value :: rest =>
        let head ←
          completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) [] [] false
        match head.result with
        | .error _ => return [(head.result, .empty)]
        | .ok _ =>
            let tail ←
              completeStreamItems schema resolvers variables fuel itemType fields rest
                path (index + 1)
            return (head.result, head.work) :: tail

  /-- Spec `ExecuteExecutionPlan`: consume an already-built plan. Collection and
  BuildExecutionPlan belong to the caller, not to plan execution.
  -/
  def executeExecutionPlan (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (newDeferUsages : List DeferUsage) (executionPlan : ExecutionPlan)
      (path : ResponsePath := [])
      (deferUsageSet : List Nat := []) (deferMap : DeferMap := [])
      : StateM Nat (Completion (List (Name × ResponseValue))) := do
    let newMap := getNewDeferMap newDeferUsages path deferMap
    let initial ←
      executeCollectedFields schema resolvers variables fuel parentType source
        executionPlan.collectedFieldsMap path deferUsageSet newMap
    match initial.result with
    -- Nullable catching happens in CompleteValue. On bubbling failure, unstarted
    -- siblings may be cancelled; no deferred outcome is exposed from this plan.
    | .error _ => return initial
    | .ok _ =>
        let tasks ←
          collectExecutionGroups schema resolvers variables fuel parentType source
            executionPlan.newCollectedFieldsMaps path newMap
        return { initial with work := .append initial.work tasks }

  /-- Spec `CollectExecutionGroups`: look up owners, construct each execution task, and
  retain it. Finite pure outcomes replace the spec's future computation.
  -/
  def collectExecutionGroups (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap)
      : StateM Nat Work := do
    match partitions with
    | [] => return .empty
    | (usages, fields) :: rest =>
        let groups := usages.filterMap (lookupDeferredFragment? deferMap)
        let completed ←
          executeExecutionGroup schema resolvers variables fuel parentType source fields
            path usages deferMap
        let tail ←
          collectExecutionGroups schema resolvers variables fuel parentType source rest
            path deferMap
        return .append (.deferred groups path completed.result completed.work) tail

  /-- Spec `ExecuteExecutionGroup`. Deferred errors remain in the task result until its
  delivery boundary is processed.
  -/
  def executeExecutionGroup (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (fields : CollectedFieldsMap) (path : ResponsePath)
      (deferUsageSet : List Nat) (deferMap : DeferMap)
      : StateM Nat (Completion (List (Name × ResponseValue))) :=
    executeCollectedFields schema resolvers variables fuel parentType source fields path
      deferUsageSet deferMap
end

-----------------------------------------------------------------------------------------
-- Opaque event source helpers
-----------------------------------------------------------------------------------------

/-- An opaque source language and its observed prefix, not a preselected future trace.
This state is intentionally partial: many next values may be admissible. Hidden task state
is existential in the semantic contract, never supplied to the response mapper.
Observations are finite and single-threaded; host waiting is not an emitted value.
-/
structure EventSource (α : Type) where
  admissible : List α → Prop
  finished : List α → Prop
  history : List α := []

/-- Every intermediate prefix must be allowed, including when several source values are
aggregated into one response. No result being available does not imply finished.
-/
def EventSource.Allows (source : EventSource α) (values : List α) : Prop :=
  ∀ initial, initial.IsPrefix values → source.admissible (source.history ++ initial)

def EventSource.advance (source : EventSource α) (values : List α) : EventSource α :=
  { source with history := source.history ++ values }

def EventSource.IsFinished (source : EventSource α) : Prop :=
  source.finished source.history

/-- A fixed finite source is useful for fixtures/replay, but is not the query default. -/
def EventSource.ofList (values : List α) : EventSource α :=
  { admissible := (·.IsPrefix values), finished := (· = values) }

/-- Available source events grouped for one-at-a-time aggregated observation. Groups are
nonempty and ordered; every intermediate source prefix must remain admissible. This starts
at the source's current history, not at the beginning of a consumed source.
-/
def EventSource.batch (source : EventSource α) : EventSource (List α) :=
  let admitted :=
    fun groups : List (List α) =>
      (∀ group ∈ groups, group ≠ []) ∧ source.Allows groups.flatten
  {
    admissible := admitted,
    finished := fun groups => admitted groups ∧ (source.advance groups.flatten).IsFinished
  }

-----------------------------------------------------------------------------------------
-- Abstract work streams and responses
-----------------------------------------------------------------------------------------

/-! Structural size of finite resolver work, independent of any scheduling policy. -/

mutual
  def Work.size : Work → Nat
    | .empty => 0
    | .append left right => left.size + right.size
    | .deferred _ _ _ children => 1 + children.size
    | .stream _ items => 1 + Work.itemsSize items

  def Work.itemsSize : List (Result ResponseValue × Work) → Nat
    | [] => 0
    | (_, work) :: rest => 1 + work.size + Work.itemsSize rest
end

structure IncrementalPendingNotice where
  id : String
  path : ResponsePath
  label : Option DirectiveLabel := none
deriving Repr

inductive IncrementalResult where
  | object (id : String) (data : List (Name × ResponseValue))
    (errors : Nat := 0) (subPath : ResponsePath := [])
  | list (id : String) (items : List ResponseValue) (errors : Nat := 0)
deriving Repr

structure IncrementalCompletionNotice where
  id : String
  errors : Nat := 0
deriving Repr

structure InitialIncrementalStreamResult extends Response where
  pending : List IncrementalPendingNotice
  hasNext : Bool
deriving Repr

structure IncrementalStreamUpdateResult where
  hasNext : Bool
  pending : List IncrementalPendingNotice := []
  incremental : List IncrementalResult := []
  completed : List IncrementalCompletionNotice := []
deriving Repr

/-- Values of successful execution-group tasks. Their complete owner sets remain in Work;
GROUP_VALUES chooses one contributing delivery group, as in the draft.
-/
structure GroupValue where
  path : ResponsePath
  data : List (Name × ResponseValue)
  errors : Nat := 0
deriving Repr

structure StreamValue where
  item : ResponseValue
  errors : Nat := 0
deriving Repr

/-- Spec-facing work events after any implementation-specific owner normalization.
A GROUP_VALUES owner is the effective publication owner, not necessarily the group whose
completion triggered a raw queue event. Node keys are internal identities, not wire IDs.
-/
inductive WorkEvent where
  | groupValues (group : DeliveryNode) (values : List GroupValue)
  | groupSuccess (group : DeliveryNode) (newGroups newStreams : List DeliveryNode)
  | groupFailure (group : DeliveryNode) (errors : Nat)
  | streamValues (stream : DeliveryNode) (values : List StreamValue)
    (newGroups newStreams : List DeliveryNode)
  | streamSuccess (stream : DeliveryNode)
  | streamFailure (stream : DeliveryNode) (errors : Nat)
  | workQueueTermination
deriving Repr

-----------------------------------------------------------------------------------------
-- Normalizing implementation-specific publication owners
-----------------------------------------------------------------------------------------

/-- A raw shared-task value retains its contributing groups until publication ownership
is selected. This adapter input is not an additional pinned-spec record.
-/
structure SharedGroupValue where
  value : GroupValue
  contributors : List DeliveryNode
deriving Repr

/-- Select a longest-path open contributor, starting with an open contributing provisional
owner. Strict improvement preserves that owner on ties, then the first longer candidate.
This non-spec adapter models publisher-side selection without allocating wire IDs.
-/
def selectGroupOwner (openKeys : List Nat) (provisional : DeliveryNode)
    : List DeliveryNode → DeliveryNode
  | [] => provisional
  | candidate :: rest =>
      let selected :=
        if candidate.key ∈ openKeys ∧ provisional.path.length < candidate.path.length then
          candidate
        else
          provisional
      selectGroupOwner openKeys selected rest

/-- Project a raw GROUP_VALUES event to spec-facing publications. Different shared values
may select different owners, so each becomes one event in the same work batch. Payloads,
errors, and value order are unchanged; this step emits no notices or completions. Other
queue events pass through unchanged. Open keys must reflect the preceding events, including
earlier events in the same batch. Admission still checks provenance and accounting.
-/
def normalizeGroupValues (openKeys : List Nat) (provisional : DeliveryNode)
    (values : List SharedGroupValue)
    : List WorkEvent :=
  values.map
    fun shared =>
      .groupValues (selectGroupOwner openKeys provisional shared.contributors)
        [shared.value]

/-- Spec CreateWorkQueue's result at the normalized, spec-facing event boundary. A concrete
implementation may compose a raw queue with publisher-side owner selection to supply it.
Its implementation is deliberately absent; raw queue events need not conform directly.
-/
structure WorkQueueResult where
  initialGroups : List DeliveryNode
  initialStreams : List DeliveryNode
  workEventStream : EventSource (List WorkEvent)

/-- The implementation of CreateWorkQueue is an explicit parameter, not a program
instruction. Initialization supplies notices and a source, without selecting its future
batches. The conformance contract lives in WorkScheduler.lean.
-/
structure WorkScheduler where
  createWorkQueue : Work → WorkQueueResult

/-- Only the response mapper owns wire identity. Scheduler implementations cannot allocate
IDs, inspect the ID supply, or manufacture response entries.
-/
structure IDState where
  ids : List (Nat × String) := []
  nextID : Nat := 0
deriving Repr

def ensureID (node : DeliveryNode) (state : IDState) : String × IDState :=
  match state.ids.find? (fun entry => entry.1 == node.key) with
  | some (_, id) => (id, state)
  | none =>
      let id := toString state.nextID
      (id, { ids := state.ids ++ [(node.key, id)], nextID := state.nextID + 1 })

def getPendingEntry {m : Type → Type} [Monad m]
    (newGroups newStreams : List DeliveryNode) (idFor : DeliveryNode → m String)
    : m (List IncrementalPendingNotice) :=
  (newGroups ++ newStreams).mapM
    fun node => do
      let id ← idFor node
      return { id, path := node.path, label := node.label }

def getIncrementalEntry {m : Type → Type} [Monad m]
    (group : DeliveryNode) (value : GroupValue) (idFor : DeliveryNode → m String)
    : m IncrementalResult := do
  let id ← idFor group
  return .object id value.data value.errors (value.path.drop group.path.length)

def getCompletedEntry {m : Type → Type} [Monad m]
    (node : DeliveryNode) (errors : Nat) (idFor : DeliveryNode → m String)
    : m IncrementalCompletionNotice := do
  let id ← idFor node
  return { id, errors }

def getIncrementalStreamUpdateResult (hasNext : Bool)
    (completed : List IncrementalCompletionNotice) (incremental : List IncrementalResult)
    (pending : List IncrementalPendingNotice)
    : IncrementalStreamUpdateResult :=
  { hasNext, completed, incremental, pending }

/-- The deterministic part of the spec: translate one work-event batch. -/
def mapWorkEventBatch (events : List WorkEvent)
    : StateM IDState IncrementalStreamUpdateResult := do
  let mut update : IncrementalStreamUpdateResult := { hasNext := true }
  for event in events do
    match event with
    | .groupValues group values =>
        let entries ← values.mapM (fun value => getIncrementalEntry group value ensureID)
        update := { update with incremental := update.incremental ++ entries }
    | .groupSuccess group groups streams =>
        let completed ← getCompletedEntry group 0 ensureID
        let pending ← getPendingEntry groups streams ensureID
        update :=
          {
            update with
              completed := update.completed ++ [completed]
              pending := update.pending ++ pending
          }
    | .groupFailure group errors =>
        let completed ← getCompletedEntry group errors ensureID
        update := { update with completed := update.completed ++ [completed] }
    | .streamValues stream values groups streams =>
        let id ← ensureID stream
        let pending ← getPendingEntry groups streams ensureID
        update :=
          {
            update with
              incremental :=
                update.incremental
                ++ [.list id (values.map StreamValue.item)
                      ((values.map StreamValue.errors).sum)]
              pending := update.pending ++ pending
          }
    | .streamSuccess stream =>
        let completed ← getCompletedEntry stream 0 ensureID
        update := { update with completed := update.completed ++ [completed] }
    | .streamFailure stream errors =>
        let completed ← getCompletedEntry stream errors ensureID
        update := { update with completed := update.completed ++ [completed] }
    | .workQueueTermination => update := { update with hasNext := false }
  return getIncrementalStreamUpdateResult update.hasNext update.completed
    update.incremental update.pending

/-- A resumable response-event producer. Input names an available source event; the mapper
uses a work-event batch, while the batcher uses a nonempty list of upstream inputs. Each
stage computes one response event and threads the mapper-owned ID state. There is no
batching flag, selected future trace, or exposed task-ledger state.
-/
structure ResponseEventStream where
  Input : Type
  source : EventSource Input
  ids : IDState
  mapEvent : Input → StateM IDState IncrementalStreamUpdateResult

/-- Spec MapIncrementalWorkEventsToResponseEvent, represented as a suspended mapper.
Constructing it neither selects source events nor maps any future batch.
-/
def mapIncrementalWorkEventsToResponseEvent
    (source : EventSource (List WorkEvent)) (ids : IDState)
    : ResponseEventStream :=
  { Input := List WorkEvent, source, ids, mapEvent := mapWorkEventBatch }

def combineIncrementalResults (updates : List IncrementalStreamUpdateResult)
    : IncrementalStreamUpdateResult :=
  updates.foldl
    (fun acc update =>
      {
        hasNext := update.hasNext,
        pending := acc.pending ++ update.pending,
        incremental := acc.incremental ++ update.incremental,
        completed := acc.completed ++ update.completed
      })
    { hasNext := false }

/-- Spec BatchIncrementalResults: return a new stream. For each nonempty available group,
consume its upstream events in order, concatenate the list entries, and take hasNext from
the final update. Constructing the stream consumes no upstream input.
-/
def batchIncrementalResults (updates : ResponseEventStream) : ResponseEventStream :=
  {
    Input := List updates.Input,
    source := updates.source.batch,
    ids := updates.ids,
    mapEvent :=
      fun available => do
        let results ← available.mapM updates.mapEvent
        return combineIncrementalResults results
  }

/-- An observation supplies one input to this stage. For a batched stream, that input is
itself a nonempty available group. Admission belongs to the upstream source.
-/
def ResponseEventStream.Accepts (stream : ResponseEventStream) (input : stream.Input)
    : Prop :=
  stream.source.Allows [input]

/-- Deterministic state update after an admissible observation. This does not choose what
becomes available next; several inputs may satisfy Accepts at the same state.
-/
def ResponseEventStream.next (stream : ResponseEventStream) (input : stream.Input)
    (_allowed : stream.Accepts input)
    : IncrementalStreamUpdateResult × ResponseEventStream :=
  let result := (stream.mapEvent input).run stream.ids
  (result.1, { stream with source := stream.source.advance [input], ids := result.2 })

/-- Generalized return type of query execution: ordinary Response or incremental stream.
This model name is broader than Section 7's ordinary "execution result" map. Subscription
streams and request-error results remain out of scope.
-/
inductive ExecutionResult where
  | single (response : Response)
  | incremental (initial : InitialIncrementalStreamResult)
    (subsequent : ResponseEventStream)

/-- Spec YieldIncrementalResults projected to its first result and resumable remainder.
Initialization abstracts waiting for that first result; no future batch is consumed.
Initial notices and subsequent events share one ID map. Only initialization, not future
completion order, determines initial notice identities and order.
-/
def yieldIncrementalResults (scheduler : WorkScheduler) (response : Response)
    (work : Work)
    : InitialIncrementalStreamResult × ResponseEventStream :=
  let result := scheduler.createWorkQueue work
  let (pending, ids) :=
    (getPendingEntry (m := StateM IDState)
      result.initialGroups result.initialStreams ensureID).run
      {}
  (
    { toResponse := response, pending, hasNext := true },
    mapIncrementalWorkEventsToResponseEvent result.workEventStream ids
  )

-----------------------------------------------------------------------------------------
-- Query execution
-----------------------------------------------------------------------------------------

/-- Model-only factoring of ExecuteRootSelectionSet's first three steps: CollectFields,
BuildExecutionPlan, ExecuteExecutionPlan, in that order. ID allocation and response-stream
packaging happen at that public boundary.
-/
def executeRootSelectionSetCore (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selectionSet : List Selection)
    : StateM Nat (Completion (List (Name × ResponseValue))) := do
  let collected ← collectFields schema variableValues parentType source selectionSet
  let executionPlan := buildExecutionPlan collected.fields
  executeExecutionPlan schema resolvers variableValues fuel parentType source
    collected.newDeferUsages executionPlan

/-- Spec 6.3.1 `ExecuteRootSelectionSet` in the model's query-only execution mode. Return
either the ordinary response or the first incremental payload and suspended stream. The
incremental branch passes its suspended remainder through BatchIncrementalResults.
-/
def executeRootSelectionSet (scheduler : WorkScheduler)
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selectionSet : List Selection)
    : ExecutionResult :=
  let (completed, _) :=
    (executeRootSelectionSetCore schema resolvers variableValues fuel parentType source
      selectionSet).run
      0
  let response := selectionSetResultToResponse completed.result
  if completed.work.size == 0 then
    .single response
  else
    let (initial, subsequent) := yieldIncrementalResults scheduler response completed.work
    .incremental initial (batchIncrementalResults subsequent)

/-- Spec 6.2.1 root execution expects a runtime object matching the operation root type.
The model still accepts arbitrary host values, but non-root sources produce a counted
execution error so equivalence statements are not forced to account for invalid roots.
-/
def rootSourceAppliesBool
    (schema : Schema) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Bool :=
  match runtimeObjectType? source with
  | some objectName =>
      schema.typeIncludesObjectBool (operation.rootType schema) objectName
  | none => false

/-- Spec 6.1.2 `CoerceVariableValues` followed by spec 6.2.1 `ExecuteQuery`, at an
explicit recursion fuel. Supplied values are prepared with operation defaults before field
collection. ExecuteRootSelectionSet owns ordinary/incremental response selection and
batching. Depth fuel bounds pure value completion. Scheduling and source observation have
no selection-depth fuel; scheduling is described by a relation on finite observations.
-/
def executeQueryWithFuel (scheduler : WorkScheduler)
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ExecutionResult :=
  let variables := coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    executeRootSelectionSet scheduler schema resolvers variables fuel
      (operation.rootType schema) source operation.selectionSet
  else
    .single { data := .null, errors := 1 }

/-- Schema-aware recursion fuel bound. The operation size bounds the number of
response-field boundaries along a path; the schema factor bounds list/type completion
between two such boundaries. Explicit-fuel execution remains available independently.
-/
def executeQueryFuelBound (schema : Schema) (operation : Operation) : Nat :=
  operation.size * (typeDefinitionsExecutionCompletionFuel schema.types + 1) + 1

/-- Default executable query entry point using the schema-aware completion bound. -/
def executeQuery (scheduler : WorkScheduler) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (operation : Operation) (source : ResolverValue ObjectRef)
    : ExecutionResult :=
  executeQueryWithFuel scheduler schema resolvers variableValues operation
    (executeQueryFuelBound schema operation) source

end Execution
end IncrementalDelivery
end GraphQL
