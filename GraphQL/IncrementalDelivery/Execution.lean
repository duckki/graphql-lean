import GraphQL.Execution
import GraphQL.IncrementalDelivery.EventSource
import GraphQL.IncrementalDelivery.Operation

/-! Separate execution for incremental-delivery draft PR #1110, revision
045e19363c2b55f127960bd3b5e8072a15b29aec (2026-08-18).

This module accepts GraphQL.IncrementalDelivery.Operation and an opaque work-queue
construction function, and returns ExecutionResult directly. Future events are supplied
one observation at a time through the shared EventSource interface.
It shares resolver values, response data, input coercion, and null-bubbling primitives
with GraphQL.Execution; field collection, planning, completion, and delivery are separate.
All incremental execution definitions remain together in this file for review.

The draft leaves CreateWorkQueue unspecified and does not yet wire @stream into
CompleteListValue. The model retains finite pure resolver outcomes, but chooses no
completion order.
Named-fragment delivery and incremental validation are not modeled here yet.
Finite observations live in IncrementalDelivery.Observation; response-correctness
statements live in IncrementalDelivery.Correctness.
-/

namespace GraphQL
namespace IncrementalDelivery

/-- Stable defer/stream object identity, represented by a fresh natural number.
Distinct from resolver object references, structural occurrences, and wire IDs.
This abbreviation documents the role without introducing a separate numeric type.
-/
abbrev NodeRef := Nat

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
  ref : NodeRef
  ancestors : List NodeRef := []
  label : Option DirectiveLabel := none
deriving Repr

/-- Spec 6.3.2 field detail, named `FieldDetails` in GraphQL.js. The field selection is
flattened into its execution-relevant components alongside its enclosing defer usage.
-/
structure FieldDetails where
  fieldName : Name
  arguments : List Argument
  selectionSet : List Selection
  directives : List DirectiveApplication := []
  deferUsage : Option DeferUsage := none
deriving Repr

abbrev CollectedFieldsMap := List (Name × List FieldDetails)

/-- Spec 6.3.2 collected fields map helper: add a field set under its response name.
-/
def CollectedFieldsMap.addFieldSet (group : Name × List FieldDetails)
    : CollectedFieldsMap -> CollectedFieldsMap
  | [] => [group]
  | (responseName, fields) :: rest =>
      if responseName == group.fst then
        (responseName, fields ++ group.snd) :: rest
      else
        (responseName, fields) :: CollectedFieldsMap.addFieldSet group rest

/-- Spec 6.3.2 `CollectFields`: merge list-backed maps, combining matching field sets. -/
def CollectedFieldsMap.merge (left right : CollectedFieldsMap) : CollectedFieldsMap :=
  right.foldl (fun grouped group => CollectedFieldsMap.addFieldSet group grouped) left

structure FieldCollection where
  collectedFieldsMap : CollectedFieldsMap := []
  newDeferUsages : List DeferUsage := []
deriving Repr

def FieldCollection.append (left right : FieldCollection) : FieldCollection :=
  {
    collectedFieldsMap :=
      CollectedFieldsMap.merge left.collectedFieldsMap right.collectedFieldsMap
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

/-- Allocate a stable node reference. The state holds the next unused node reference. -/
def freshNodeRef : StateM NodeRef NodeRef := do
  let ref ← get
  set (ref + 1)
  return ref

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
      : Selection -> StateM NodeRef FieldCollection
    | .field responseName fieldName arguments directives selectionSet => do
        if !selectionDirectivesAllowBool variableValues directives then
          return {}
        return {
          collectedFieldsMap :=
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
            let ref ← freshNodeRef
            let usage : DeferUsage :=
              {
                ref := ref
                label := label
                ancestors :=
                  deferUsage.map (fun parent => parent.ref :: parent.ancestors) |>.getD []
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
      : StateM NodeRef FieldCollection := do
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
    : List FieldDetails -> StateM NodeRef FieldCollection
  | [] => pure {}
  | field :: rest => do
      let head ←
        collectFields schema variableValues objectType source field.selectionSet
          field.deferUsage
      let tail ← collectSubfields schema variableValues objectType source rest
      return head.append tail

-----------------------------------------------------------------------------------------
-- Execution plans
-----------------------------------------------------------------------------------------

/-- Spec `GetFilteredDeferUsageSet`. An immediate occurrence dominates all deferred
occurrences. Otherwise remove usages with an ancestor in the set, keeping the full field
details for subcollection.
-/
def getFilteredDeferUsageSet (fields : List FieldDetails) : List NodeRef :=
  if fields.any (fun field => field.deferUsage.isNone) then
    []
  else
    let usages := fields.filterMap FieldDetails.deferUsage
    let refs := (usages.map DeferUsage.ref).eraseDups
    refs.filter
      (fun ref =>
        !(usages.any
            (fun usage =>
              usage.ref == ref && usage.ancestors.any refs.contains)))

def deferUsageSetsEquivalent (left right : List NodeRef) : Bool :=
  left.all right.contains && right.all left.contains

structure ExecutionPlan where
  collectedFieldsMap : CollectedFieldsMap := []
  newCollectedFieldsMaps : List (List NodeRef × CollectedFieldsMap) := []
deriving Repr

def addExecutionPartition (usages : List NodeRef) (group : Name × List FieldDetails)
    : List (List NodeRef × CollectedFieldsMap) -> List (List NodeRef × CollectedFieldsMap)
  | [] => [(usages, [group])]
  | (refs, fields) :: rest =>
      if deferUsageSetsEquivalent refs usages then
        (refs, fields ++ [group]) :: rest
      else
        (refs, fields) :: addExecutionPartition usages group rest

/-- Spec `BuildExecutionPlan`: partition only; do not execute or create work here. -/
def buildExecutionPlan (fields : CollectedFieldsMap)
    (parentDeferUsages : List NodeRef := [])
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
-- `Work` and `Completion` definitions for incremental completion modeling.
-- * Work models the remaining work to be delivered.
-- * Completion models the initial result and remaining work.
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

/-- Delivery descriptor for defer/stream nodes. In execution-generated work, `ref` is
allocated by `freshNodeRef` and represents JavaScript object identity, not a wire ID.
-/
structure DeliveryNode where
  ref : NodeRef
  path : ResponsePath
  label : Option DirectiveLabel := none
deriving Repr

structure DeferredFragment where
  node : DeliveryNode
  ancestors : List DeliveryNode := []
deriving Repr

/-- Finite resolver work retained after the initial response.

A task may contribute to multiple fragments, but its data is delivered only once.
The structural order and association of `combine` nodes remain observable through work
addresses; `combine` therefore states neither commutativity nor associativity.
-/
inductive Work where
  /-- No deferred or streamed work remains. -/
  | empty
  /-- Join sibling work components without choosing their completion order. -/
  | combine (left right : Work)
  /-- One execution-group task, its contributing fragments, and nested work. -/
  | executionGroup (groups : List DeferredFragment) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
  /-- One stream descriptor and the finite remaining outer-list items. -/
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
  | .ok _ => { result := result, work := .combine left.work right.work }

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

-----------------------------------------------------------------------------------------
-- Executing Collected Fields & Execution Plans
-----------------------------------------------------------------------------------------

abbrev DeferMap := List DeferredFragment

def lookupDeferredFragment? (deferMap : DeferMap) (ref : NodeRef)
    : Option DeferredFragment :=
  deferMap.find? (fun group => group.node.ref == ref)

/-- Spec `GetNewDeferMap`; flattened ancestor lists replace parent-fragment pointers. -/
def getNewDeferMap (usages : List DeferUsage) (path : ResponsePath) (deferMap : DeferMap)
    : DeferMap :=
  usages.foldl
    (fun current usage =>
      current
      ++ [{
            node := { ref := usage.ref, path := path, label := usage.label }
            ancestors :=
              usage.ancestors.filterMap
                (fun ref =>
                  (lookupDeferredFragment? current ref).map DeferredFragment.node)
          }])
    deferMap

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

structure StreamUsage where
  label : Option DirectiveLabel
  initialCount : Nat
deriving Repr

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

/-! Spec 6.3.3 `ExecuteCollectedFields`, 6.4 `ExecuteField`, and 6.4.3 `CompleteValue`:
partial fuel-bounded execution model with spec-shaped null bubbling through non-null
wrappers. `Except.error` carries a bubbling error count until a nullable parent can turn
it into response `null`.
-/

mutual
  /-- Spec `ExecuteCollectedFields`: schema lookup, ExecuteField, response-map insertion,
  then work accumulation. Work.combine represents the tasks/streams and group union.
  -/
  def executeCollectedFields (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (fields : CollectedFieldsMap) (path : ResponsePath := [])
      (deferUsageSet : List NodeRef := []) (deferMap : DeferMap := [])
      : StateM NodeRef (Completion (List (Name × ResponseValue))) := do
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
      (responseName : Name) (fields : List FieldDetails) (path : ResponsePath := [])
      (deferUsageSet : List NodeRef := []) (deferMap : DeferMap := [])
      : StateM NodeRef (Completion ResponseValue) := do
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
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath := []) (deferUsageSet : List NodeRef := [])
      (deferMap : DeferMap := []) (allowStream : Bool := true)
      : StateM NodeRef (Completion ResponseValue) := do
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
        let executionPlan :=
          buildExecutionPlan collection.collectedFieldsMap deferUsageSet
        let completed ←
          executeExecutionPlan schema resolvers variables fuel runtimeType source
            collection.newDeferUsages executionPlan path deferUsageSet deferMap
        return completed.catchNull ResponseValue.object
    | fuel + 1, .list inner, .list values =>
        completeListValueWithStream schema resolvers variables fuel inner fields values
          path deferUsageSet deferMap allowStream
    | _ + 1, _, _ => return .error 1

  /-- Spec `CompleteListValue`: complete each indexed item and accumulate values/work.
  index makes the spec's loop counter explicit; normal list completion starts at 0.
  -/
  def completeListValue (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (deferUsageSet : List NodeRef)
      (deferMap : DeferMap)
      : StateM NodeRef (Completion (List ResponseValue)) := do
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

  /-- Model extension: the pinned CompleteListValue has no @stream hook. Keep this
  extension distinct from that algorithm. Only the outermost list is eligible; nested list
  wrappers complete synchronously. Reaching initialCount creates a stream boundary even
  when its finite tail is empty; exhaustion before that boundary creates no stream.
  -/
  def completeListValueWithStream (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (inner : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (deferUsageSet : List NodeRef) (deferMap : DeferMap)
      (allowStream : Bool)
      : StateM NodeRef (Completion ResponseValue) := do
    let streamUsage :=
      if allowStream then
        getStreamUsage variables (fields.head?.map FieldDetails.directives |>.getD [])
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
            let ref ← freshNodeRef
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
                  .combine completed.work
                    (.stream { ref := ref, path := path, label := usage.label } items)
            }

  /-- Model helper: finite outcomes for the remaining streamed items, each with its own
  completion boundary. The pinned draft gives no algorithm for this step.
  -/
  def completeStreamItems (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat)
      : StateM NodeRef (List (Result ResponseValue × Work)) := do
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
      (deferUsageSet : List NodeRef := []) (deferMap : DeferMap := [])
      : StateM NodeRef (Completion (List (Name × ResponseValue))) := do
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
        return { initial with work := .combine initial.work tasks }

  /-- Spec `CollectExecutionGroups`: look up owners, construct each execution task, and
  retain it. Finite pure outcomes replace the spec's future computation.
  -/
  def collectExecutionGroups (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (partitions : List (List NodeRef × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap)
      : StateM NodeRef Work := do
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
        return .combine (.executionGroup groups path completed.result completed.work) tail

  /-- Spec `ExecuteExecutionGroup`. Deferred errors remain in the task result until its
  delivery boundary is processed.
  -/
  def executeExecutionGroup (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (fields : CollectedFieldsMap) (path : ResponsePath)
      (deferUsageSet : List NodeRef) (deferMap : DeferMap)
      : StateM NodeRef (Completion (List (Name × ResponseValue))) :=
    executeCollectedFields schema resolvers variables fuel parentType source fields path
      deferUsageSet deferMap
end

-----------------------------------------------------------------------------------------
-- Publishing incremental results
-----------------------------------------------------------------------------------------

/-- GraphQL.js `ExecutionGroupValue`, shared with the reference implementation.
`deliveryGroups` is publisher metadata, not a wire field or ownership evidence for the
abstract queue contract. The reference event source checks it against Work; abstract
sources may omit it. After owner selection the response mapper uses only path/data/errors.
-/
structure ExecutionGroupValue where
  path : ResponsePath
  data : List (Name × ResponseValue)
  errors : Nat := 0
  deliveryGroups : List DeliveryNode := []
deriving Repr

/-- GraphQL.js `StreamItemValue`: one completed stream item and its counted errors. -/
structure StreamItemValue where
  item : ResponseValue
  errors : Nat := 0
deriving Repr

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

/-- Wire identity state for response initialization and mapping. The abstract WorkQueue
interface and concrete queue state carry node refs, not wire IDs; the publisher/mapper
layer owns allocation and response entries.
-/
structure IDState where
  ids : List (NodeRef × String) := []
  nextID : Nat := 0
deriving Repr

def ensureID (node : DeliveryNode) (state : IDState) : String × IDState :=
  match state.ids.find? (fun entry => entry.1 == node.ref) with
  | some (_, id) => (id, state)
  | none =>
      let id := toString state.nextID
      (id, { ids := state.ids ++ [(node.ref, id)], nextID := state.nextID + 1 })

def getPendingEntry {m : Type → Type} [Monad m]
    (newGroups newStreams : List DeliveryNode) (idFor : DeliveryNode → m String)
    : m (List IncrementalPendingNotice) :=
  (newGroups ++ newStreams).mapM
    fun node => do
      let id ← idFor node
      return { id, path := node.path, label := node.label }

def getIncrementalEntry {m : Type → Type} [Monad m]
    (group : DeliveryNode) (value : ExecutionGroupValue) (idFor : DeliveryNode → m String)
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

-----------------------------------------------------------------------------------------
-- WorkQueue and ResponseEventStream representations for modeling purposes.
-- * The draft specifies seven queue-event forms and their response mapping.
-- * Concrete representations and the queue implementation remain unspecified.
-- * WorkQueueEvent is the GraphQL.js type name, not a named draft definition.
-- * WorkQueue models the initial pending announcements and opaque queue events.
-----------------------------------------------------------------------------------------

/-- The draft's seven queue-output forms, named `WorkQueueEvent` in GraphQL.js.
Raw queue events carry a provisional owner; spec-facing
events carry the effective owner selected by the publisher. Their values are identical.
Node refs are internal identities, not wire IDs.
Value lists support multi-task group flushes and multi-item stream updates. Atomic
work-history admission checks singleton values; WorkBatching may coalesce them again.
-/
inductive WorkQueueEvent where
  | groupValues (group : DeliveryNode) (values : List ExecutionGroupValue)
  | groupSuccess (group : DeliveryNode) (newGroups newStreams : List DeliveryNode)
  | groupFailure (group : DeliveryNode) (errors : Nat)
  | streamValues (stream : DeliveryNode) (values : List StreamItemValue)
    (newGroups newStreams : List DeliveryNode)
  | streamSuccess (stream : DeliveryNode)
  | streamFailure (stream : DeliveryNode) (errors : Nat)
  | workQueueTermination
deriving Repr

/-- Translate one work-event batch to a subsequent response update, threading existing
mapper IDs. -/
def mapWorkEventBatch (events : List WorkQueueEvent)
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
                ++ [.list id (values.map StreamItemValue.item)
                      ((values.map StreamItemValue.errors).sum)]
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

/-- The observable interface supplied by spec CreateWorkQueue: initial notices and an
opaque source of normalized work events. Concrete state and host inputs remain hidden.
An implementation may compose a raw queue with publisher-side owner selection to supply
this interface; raw queue events need not conform directly. The contract is defined in
WorkQueueSemantics.lean.
-/
structure WorkQueue where
  initialGroups : List DeliveryNode
  initialStreams : List DeliveryNode
  workEventStream : EventSource (List WorkQueueEvent)

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

-----------------------------------------------------------------------------------------
-- Batching and yielding incremental results
-----------------------------------------------------------------------------------------

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

/-- Spec MapIncrementalWorkEventsToResponseEvent, represented as a suspended mapper.
Constructing it neither selects source events nor maps any future batch.
-/
def mapIncrementalWorkEventsToResponseEvent
    (source : EventSource (List WorkQueueEvent)) (ids : IDState)
    : ResponseEventStream :=
  { Input := List WorkQueueEvent, source, ids, mapEvent := mapWorkEventBatch }

/-- Shared initial-response construction: allocate pending notices from a fresh ID supply
and package the root data/errors with hasNext=true. This model-only factoring of
YieldIncrementalResults is also used by the reference implementation. The returned ID
state seeds subsequent response mapping. Initial notices come from queue initialization,
not synthetic work events.
-/
def initializeIncrementalResponse (response : Response)
    (initialGroups initialStreams : List DeliveryNode)
    : InitialIncrementalStreamResult × IDState :=
  let (pending, ids) :=
    (getPendingEntry (m := StateM IDState) initialGroups initialStreams ensureID).run {}
  ({ toResponse := response, pending, hasNext := true }, ids)

/-- Spec YieldIncrementalResults projected to its first result and resumable remainder.
`createWorkQueue` supplies the draft's otherwise unspecified CreateWorkQueue implementation.
Initialization abstracts waiting for that first result; no future batch is consumed.
`initializeIncrementalResponse` supplies the initial envelope and the subsequent mapper's
ID state. Only initialization, not future completion order, determines initial notice
identities and order.
-/
def yieldIncrementalResults (createWorkQueue : Work → WorkQueue) (response : Response)
    (work : Work)
    : InitialIncrementalStreamResult × ResponseEventStream :=
  let result := createWorkQueue work
  let (initial, ids) :=
    initializeIncrementalResponse response result.initialGroups result.initialStreams
  (initial, mapIncrementalWorkEventsToResponseEvent result.workEventStream ids)

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
    : StateM NodeRef (Completion (List (Name × ResponseValue))) := do
  let collected ← collectFields schema variableValues parentType source selectionSet
  let executionPlan := buildExecutionPlan collected.collectedFieldsMap
  executeExecutionPlan schema resolvers variableValues fuel parentType source
    collected.newDeferUsages executionPlan

/-! Executable work count, independent of any completion order.
* `combine` contributes no work record of its own; only execution-group tasks, stream
descriptors, and remaining stream items contribute to the count.
* `Work.size = 0` corresponds to "{tasks} is empty and {streams} is empty" from the spec.
-/

mutual
  def Work.size : Work → Nat
    | .empty => 0
    | .combine left right => left.size + right.size
    | .executionGroup _ _ _ children => 1 + children.size
    | .stream _ items => 1 + Work.itemsSize items

  def Work.itemsSize : List (Result ResponseValue × Work) → Nat
    | [] => 0
    | (_, work) :: rest => 1 + work.size + Work.itemsSize rest
end

/-- Generalized return type of query execution: ordinary Response or incremental stream.
This model name is broader than Section 7's ordinary "execution result" map. Subscription
streams and request-error results remain out of scope.
-/
inductive ExecutionResult where
  | single (response : Response)
  | incremental (initial : InitialIncrementalStreamResult)
    (subsequent : ResponseEventStream)

/-- Spec 6.3.1 `ExecuteRootSelectionSet` in the model's query-only execution mode. Return
either the ordinary response or the first incremental payload and suspended stream. The
incremental branch passes its suspended remainder through BatchIncrementalResults.
-/
def executeRootSelectionSet (createWorkQueue : Work → WorkQueue)
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
    let (initial, subsequent) :=
      yieldIncrementalResults createWorkQueue response completed.work
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
batching. Depth fuel bounds pure value completion. Source observation has no selection-depth
fuel; possible completion orders are described by a relation on finite observations.
-/
def executeQueryWithFuel (createWorkQueue : Work → WorkQueue)
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ExecutionResult :=
  let variables := coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    executeRootSelectionSet createWorkQueue schema resolvers variables fuel
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
def executeQuery (createWorkQueue : Work → WorkQueue) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (operation : Operation) (source : ResolverValue ObjectRef)
    : ExecutionResult :=
  executeQueryWithFuel createWorkQueue schema resolvers variableValues operation
    (executeQueryFuelBound schema operation) source

end Execution
end IncrementalDelivery
end GraphQL
