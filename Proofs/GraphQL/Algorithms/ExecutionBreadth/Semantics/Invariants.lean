import Proofs.GraphQL.Algorithms.Common.SyntaxEq
import GraphQL.Algorithms.ExecutionBreadth
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Collection
import Proofs.GraphQL.Execution.ArgumentCoercion

/-!
Proof-facing invariant vocabulary for the current breadth executor.

The runtime model now has one forward scheduler namespace and one reverse-completion
state split into positional child values plus keyed field blocks:

* `ScheduleKey` identifies one resolver-compatible field batch.
* `ScheduleSegment` keeps the child selection set per parent-scope contribution.
* `PendingChildWork` is an ungrouped list of composite child scopes waiting to be
  scheduled.
* `CompletionState.valueStack` is purely positional; child object values are consumed by
  the next `ValueSlot.child`.
* `CompletionState.fieldStore` is still keyed by `ScheduleKey`, because object scopes pop
  field blocks by collected-field order.

These definitions keep the proof surface aligned with that runtime split, without
reintroducing the deleted keyed child-completion machinery.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

-----------------------------------------------------------------------------------------
-- Queue / stack shapes
-----------------------------------------------------------------------------------------

abbrev FieldStoreShape := List (ScheduleKey × List Nat)

structure CompletionStateShape where
  valueStack : List Nat
  fieldStore : FieldStoreShape
deriving Repr

def responseValueSegmentsShape (segments : ResponseValueSegments) : List Nat :=
  segments.map List.length

def fieldStoreShape (store : FieldStore) : FieldStoreShape :=
  store.map (fun (key, segments) => (key, responseValueSegmentsShape segments))

def completionStackShape (stack : CompletionStack) : CompletionStateShape :=
  {
    valueStack := responseValueSegmentsShape stack.valueStack
    fieldStore := fieldStoreShape stack.fieldStore
  }

def scheduleItemFieldShape (item : ScheduleItem ObjectRef) : ScheduleKey × List Nat :=
  (item.key, item.segmentLengths)

def scheduleQueueFieldShape (queue : ScheduleQueue ObjectRef) : FieldStoreShape :=
  queue.map scheduleItemFieldShape

theorem scheduleKeyEqBool_self (key : ScheduleKey)
    : scheduleKeyEqBool key key = true := by
  cases key with
  | mk parentType responseName fieldName arguments =>
      simp [scheduleKeyEqBool, argumentListEqBool_self]

theorem scheduleKeyEqBool_eq {left right : ScheduleKey}
    : scheduleKeyEqBool left right = true -> left = right := by
  cases left with
  | mk leftParent leftResponse leftField leftArguments =>
      cases right with
      | mk rightParent rightResponse rightField rightArguments =>
          simp [scheduleKeyEqBool, ScheduleKey.mk.injEq]
          intro hparent hresponse hfield harguments
          exact ⟨hparent, hresponse, hfield, argumentListEqBool_eq harguments⟩

theorem scheduleKeyEqBool_false_symm {left right : ScheduleKey}
    : scheduleKeyEqBool left right = false -> scheduleKeyEqBool right left = false := by
  intro hfalse
  cases h : scheduleKeyEqBool right left with
  | false =>
      rfl
  | true =>
      have heq : right = left :=
        scheduleKeyEqBool_eq h
      subst right
      simp [scheduleKeyEqBool_self] at hfalse

theorem completionStackShape_empty
    : completionStackShape (∅ : CompletionStack)
      = { valueStack := [], fieldStore := [] } := by
  rfl

theorem scheduleQueueFieldShape_nil
    : scheduleQueueFieldShape ([] : ScheduleQueue ObjectRef) = [] := by
  rfl

theorem scheduleQueueFieldShape_cons
    (item : ScheduleItem ObjectRef) (queue : ScheduleQueue ObjectRef)
    : scheduleQueueFieldShape (item :: queue)
      = scheduleItemFieldShape item :: scheduleQueueFieldShape queue := by
  rfl

-----------------------------------------------------------------------------------------
-- Concrete spec field results for runtime queue items
-----------------------------------------------------------------------------------------

def singleFieldResultValue (responseName : Name)
    : Result (List (Name × ResponseValue)) -> Result ResponseValue
  | .error errors => .error errors
  | .ok ([(actualName, value)], errors) =>
      if actualName == responseName then
        .ok (value, errors)
      else
        .error (errors + 1)
  | .ok (_fields, errors) =>
      .error (errors + 1)

def scheduleSegmentSpecFieldResults
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (key : ScheduleKey) (segment : ScheduleSegment ObjectRef)
    : List (Result ResponseValue) :=
  segment.sources.map
    (fun source =>
      singleFieldResultValue key.responseName
        (GraphQL.Execution.executeField schema resolvers variableValues fuel source
          key.responseName [key.executableField segment.childSelectionSet]))

def scheduleItemSpecFieldSegments
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (item : ScheduleItem ObjectRef)
    : ResponseValueSegments :=
  item.segments.map
    (scheduleSegmentSpecFieldResults schema resolvers variableValues fuel item.key)

def scheduleItemSpecFieldCompletion
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (item : ScheduleItem ObjectRef)
    : ScheduleKey × ResponseValueSegments :=
  (
    item.key,
    (scheduleItemSpecFieldSegments schema resolvers variableValues fuel item).reverse
  )

def scheduleQueueSpecFieldCompletionStack
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (queue : ScheduleQueue ObjectRef)
    : CompletionStack :=
  {
    valueStack := []
    fieldStore :=
      queue.map (scheduleItemSpecFieldCompletion schema resolvers variableValues fuel)
  }

theorem scheduleSegmentSpecFieldResults_length
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (key : ScheduleKey) (segment : ScheduleSegment ObjectRef)
    : (scheduleSegmentSpecFieldResults schema resolvers variableValues fuel
        key segment).length
      = segment.sources.length := by
  simp [scheduleSegmentSpecFieldResults]

-----------------------------------------------------------------------------------------
-- Proof-facing expected queue
-----------------------------------------------------------------------------------------

/--
Proof-facing queue segment expectation. Runtime queue segments keep only sources and the
child selection-set continuation. The proof view additionally remembers the spec fuel
assigned to each source position.
-/
structure ExpectedQueueSegment (ObjectRef : Type) where
  segment : ScheduleSegment ObjectRef
  specFuels : List Nat
deriving Repr

def expectedQueueSegmentFuelsAligned (segment : ExpectedQueueSegment ObjectRef) : Prop :=
  segment.specFuels.length = segment.segment.sources.length

/--
Proof-facing queue item expectation. The runtime schedule key and segment order are
preserved; only per-source spec fuel is added.
-/
structure ExpectedQueueItem (ObjectRef : Type) where
  key : ScheduleKey
  segments : List (ExpectedQueueSegment ObjectRef)
deriving Repr

def expectedQueueItemFuelsAligned (item : ExpectedQueueItem ObjectRef) : Prop :=
  ∀ segment, segment ∈ item.segments -> expectedQueueSegmentFuelsAligned segment

theorem typeRefCompleteValueFuelBound_pos (fieldType : TypeRef)
    : 0 < typeRefCompleteValueFuelBound fieldType := by
  induction fieldType with
  | named _typeName =>
      simp [typeRefCompleteValueFuelBound]
  | list inner ih =>
      simp [typeRefCompleteValueFuelBound]
  | nonNull inner ih =>
      simpa [typeRefCompleteValueFuelBound] using ih

def expectedQueueSegmentFieldFuelReadyFor
    (fieldType : TypeRef) (segment : ExpectedQueueSegment ObjectRef)
    : Prop :=
  ∀ fuel, fuel ∈ segment.specFuels -> typeRefCompleteValueFuelBound fieldType < fuel

def expectedQueueItemFieldFuelReadyFor
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    : Prop :=
  ∀ segment,
    segment ∈ item.segments -> expectedQueueSegmentFieldFuelReadyFor fieldType segment

def expectedQueueItemStepFuelReady (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    : Prop :=
  match schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      ∀ segment, segment ∈ item.segments -> ∀ fuel, fuel ∈ segment.specFuels -> 0 < fuel
  | some fieldDefinition =>
      expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item

abbrev ExpectedScheduleQueue (ObjectRef : Type) :=
  List (ExpectedQueueItem ObjectRef)

def expectedScheduleQueueFuelsAligned (queue : ExpectedScheduleQueue ObjectRef) : Prop :=
  ∀ item, item ∈ queue -> expectedQueueItemFuelsAligned item

def expectedScheduleQueueItemsNonempty (queue : ExpectedScheduleQueue ObjectRef) : Prop :=
  ∀ item, item ∈ queue -> item.segments ≠ []

def scheduleKeyAbsentFromExpectedQueue
    (key : ScheduleKey) (queue : ExpectedScheduleQueue ObjectRef)
    : Prop :=
  ∀ item, item ∈ queue -> scheduleKeyEqBool key item.key = false

def expectedScheduleQueueKeysDistinct : ExpectedScheduleQueue ObjectRef -> Prop
  | [] => True
  | item :: rest =>
      scheduleKeyAbsentFromExpectedQueue item.key rest
      ∧ expectedScheduleQueueKeysDistinct rest

def expectedScheduleQueueFieldFuelReady
    (schema : Schema)
    (queue : ExpectedScheduleQueue ObjectRef)
    : Prop :=
  ∀ item, item ∈ queue -> expectedQueueItemStepFuelReady schema item

/--
Proof-only spec-fuel budget for executing a child object scope. The constant reserve is
the schema-wide completion-wrapper bound; each syntactic selection pays one
`executeField` tick plus at most that wrapper depth before control reaches the next
child scope.
-/
def specFuelScopeBudget (schema : Schema) (selectionSet : List Selection) (fuel : Nat)
    : Prop :=
  schemaCompleteValueFuelBound schema
    + SelectionSet.size selectionSet * (schemaCompleteValueFuelBound schema + 1)
  < fuel

/--
Proof-only spec-fuel budget for one scheduled field segment. The segment stores the
field's child selection set, so this is exactly one more selection step than the child
scope budget.
-/
def specFuelFieldBudget
    (schema : Schema) (childSelectionSet : List Selection) (fuel : Nat)
    : Prop :=
  schemaCompleteValueFuelBound schema
    + (SelectionSet.size childSelectionSet + 1)
      * (schemaCompleteValueFuelBound schema + 1)
  < fuel

def specFuelValueBudget
    (schema : Schema) (selectionSet : List Selection)
    (fieldType : TypeRef) (fuel : Nat)
    : Prop :=
  schemaCompleteValueFuelBound schema
    + SelectionSet.size selectionSet * (schemaCompleteValueFuelBound schema + 1)
    + typeRefCompleteValueFuelBound fieldType
  < fuel

def expectedQueueSegmentFieldBudgetReady
    (schema : Schema) (segment : ExpectedQueueSegment ObjectRef)
    : Prop :=
  ∀ fuel,
    fuel ∈ segment.specFuels
    -> specFuelFieldBudget schema segment.segment.childSelectionSet fuel

def expectedQueueItemFieldBudgetReady
    (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    : Prop :=
  ∀ segment,
    segment ∈ item.segments -> expectedQueueSegmentFieldBudgetReady schema segment

def expectedScheduleQueueFieldBudgetReady
    (schema : Schema) (queue : ExpectedScheduleQueue ObjectRef)
    : Prop :=
  ∀ item, item ∈ queue -> expectedQueueItemFieldBudgetReady schema item

/--
Proof-facing scheduler shape. Runtime queue items are keyed only by `ScheduleKey`, and
their segments may duplicate the same child selection set for many parent instances. The
breadth fuel bound must count this shape-level work, not source multiplicity.
-/
structure ScheduleFieldShape where
  key : ScheduleKey
  childSelectionSet : List Selection
deriving Repr

def scheduleFieldShapeEqBool (left right : ScheduleFieldShape) : Bool :=
  scheduleKeyEqBool left.key right.key
  && selectionSetEqBool left.childSelectionSet right.childSelectionSet

theorem scheduleFieldShapeEqBool_self (shape : ScheduleFieldShape)
    : scheduleFieldShapeEqBool shape shape = true := by
  cases shape with
  | mk key childSelectionSet =>
      simp [scheduleFieldShapeEqBool, scheduleKeyEqBool_self,
        selectionSetEqBool_self]

theorem scheduleFieldShapeEqBool_eq {left right : ScheduleFieldShape}
    : scheduleFieldShapeEqBool left right = true -> left = right := by
  cases left with
  | mk leftKey leftSelectionSet =>
      cases right with
      | mk rightKey rightSelectionSet =>
          intro hshape
          simp [scheduleFieldShapeEqBool] at hshape
          rcases hshape with ⟨hkey, hselectionSet⟩
          cases scheduleKeyEqBool_eq hkey
          cases selectionSetEqBool_eq hselectionSet
          rfl

def expectedQueueSegmentShape
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ScheduleFieldShape :=
  {
    key := key
    childSelectionSet := segment.segment.childSelectionSet
  }

def collectedGroupScheduleShape (parentType : Name) (group : Name × List ExecutableField)
    : ScheduleFieldShape :=
  {
    key := scheduleKeyForFields parentType group.fst group.snd
    childSelectionSet := childSelectionSetForFields group.snd
  }

def collectedGroupsScheduleShapes
    (parentType : Name) (groups : List (Name × List ExecutableField))
    : List ScheduleFieldShape :=
  groups.map (collectedGroupScheduleShape parentType)

def expectedQueueItemShapes (item : ExpectedQueueItem ObjectRef)
    : List ScheduleFieldShape :=
  item.segments.map (expectedQueueSegmentShape item.key)

def expectedScheduleQueueShapes (queue : ExpectedScheduleQueue ObjectRef)
    : List ScheduleFieldShape :=
  (queue.map expectedQueueItemShapes).flatten

def insertScheduleFieldShape (shape : ScheduleFieldShape)
    : List ScheduleFieldShape -> List ScheduleFieldShape
  | [] => [shape]
  | existing :: rest =>
      if scheduleFieldShapeEqBool shape existing then
        existing :: rest
      else
        existing :: insertScheduleFieldShape shape rest

def scheduleFieldShapeSet (shapes : List ScheduleFieldShape) : List ScheduleFieldShape :=
  shapes.foldl (fun shapes shape => insertScheduleFieldShape shape shapes) []

theorem scheduleFieldShape_mem_insert_of_mem (inserted shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        shape ∈ shapes -> shape ∈ insertScheduleFieldShape inserted shapes
  | [], hmem => by
      simp at hmem
  | existing :: rest, hmem => by
      cases hinsert : scheduleFieldShapeEqBool inserted existing with
      | true =>
          simp [insertScheduleFieldShape, hinsert] at hmem ⊢
          exact hmem
      | false =>
          simp [insertScheduleFieldShape, hinsert] at hmem ⊢
          rcases hmem with hhead | htail
          · exact Or.inl hhead
          · exact Or.inr
              (scheduleFieldShape_mem_insert_of_mem inserted shape rest htail)

theorem scheduleFieldShape_mem_insert_self (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape, shape ∈ insertScheduleFieldShape shape shapes
  | [] => by
      simp [insertScheduleFieldShape]
  | existing :: rest => by
      cases hinsert : scheduleFieldShapeEqBool shape existing with
      | true =>
          have hshape : shape = existing :=
            scheduleFieldShapeEqBool_eq hinsert
          simp [insertScheduleFieldShape, hinsert]
          exact Or.inl hshape
      | false =>
          simp [insertScheduleFieldShape, hinsert]
          exact Or.inr (scheduleFieldShape_mem_insert_self shape rest)

theorem scheduleFieldShape_mem_foldl_insert_of_member (shape : ScheduleFieldShape)
    : ∀ (shapes pending : List ScheduleFieldShape),
        shape ∈ pending
        -> shape
            ∈ shapes.foldl
                (fun shapes shape => insertScheduleFieldShape shape shapes)
                pending := by
  intro shapes
  induction shapes with
  | nil =>
      intro pending hmem
      exact hmem
  | cons inserted shapes ih =>
      intro pending hmem
      exact ih (insertScheduleFieldShape inserted pending)
        (scheduleFieldShape_mem_insert_of_mem inserted shape pending hmem)

theorem scheduleFieldShape_mem_foldl_insert_of_mem (shape : ScheduleFieldShape)
    : ∀ (shapes pending : List ScheduleFieldShape),
        shape ∈ shapes
        -> shape
            ∈ shapes.foldl
                (fun shapes shape => insertScheduleFieldShape shape shapes)
                pending := by
  intro shapes
  induction shapes with
  | nil =>
      intro pending hmem
      simp at hmem
  | cons inserted shapes ih =>
      intro pending hmem
      have hcases : shape = inserted ∨ shape ∈ shapes := by
        simpa using hmem
      rcases hcases with hhead | htail
      · have hin :
            shape ∈ insertScheduleFieldShape inserted pending := by
          rw [← hhead]
          exact
            scheduleFieldShape_mem_insert_self shape pending
        exact scheduleFieldShape_mem_foldl_insert_of_member
          shape shapes (insertScheduleFieldShape inserted pending) hin
      · exact ih (insertScheduleFieldShape inserted pending) htail

theorem scheduleFieldShape_mem_shapeSet_of_mem
    (shape : ScheduleFieldShape) (shapes : List ScheduleFieldShape)
    : shape ∈ shapes -> shape ∈ scheduleFieldShapeSet shapes := by
  intro hmem
  simpa [scheduleFieldShapeSet] using
    scheduleFieldShape_mem_foldl_insert_of_mem shape shapes
      ([] : List ScheduleFieldShape) hmem

def expectedScheduleQueueShapeSet (queue : ExpectedScheduleQueue ObjectRef)
    : List ScheduleFieldShape :=
  scheduleFieldShapeSet (expectedScheduleQueueShapes queue)

def scheduleFieldShapeStepWeight (schema : Schema) (shape : ScheduleFieldShape) : Nat :=
  (SelectionSet.size shape.childSelectionSet + 1) * (schema.objectTypes.length + 1)

def scheduleFieldShapeSetWeight (schema : Schema) : List ScheduleFieldShape -> Nat
  | [] => 0
  | shape :: shapes =>
      scheduleFieldShapeStepWeight schema shape
      + scheduleFieldShapeSetWeight schema shapes

def expectedQueueItemShapeSet (item : ExpectedQueueItem ObjectRef)
    : List ScheduleFieldShape :=
  scheduleFieldShapeSet (expectedQueueItemShapes item)

def expectedQueueItemShapeWeight (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    : Nat :=
  scheduleFieldShapeSetWeight schema (expectedQueueItemShapeSet item)

def expectedQueueItemRawShapeWeight (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    : Nat :=
  scheduleFieldShapeSetWeight schema (expectedQueueItemShapes item)

def expectedScheduleQueueShapeWeight (schema : Schema)
    : ExpectedScheduleQueue ObjectRef -> Nat
  | [] => 0
  | item :: rest =>
      expectedQueueItemShapeWeight schema item
      + expectedScheduleQueueShapeWeight schema rest

def expectedScheduleQueueRawShapeWeight (schema : Schema)
    : ExpectedScheduleQueue ObjectRef -> Nat
  | [] => 0
  | item :: rest =>
      expectedQueueItemRawShapeWeight schema item
      + expectedScheduleQueueRawShapeWeight schema rest

def collectedGroupsShapeWeight
    (schema : Schema) (parentType : Name)
    (groups : List (Name × List ExecutableField))
    : Nat :=
  scheduleFieldShapeSetWeight schema (collectedGroupsScheduleShapes parentType groups)

/--
Queue-frontier descendant shape. The forward queue can contain one scheduled field per
runtime parent type, but those sibling field items often share the same child selection
set and therefore the same future syntactic work. This shape deliberately ignores the
runtime parent type and schedule key so the fuel proof can charge that future work once.
-/
structure SelectionSetShape where
  selectionSet : List Selection
deriving Repr

def selectionSetShapeEqBool (left right : SelectionSetShape) : Bool :=
  selectionSetEqBool left.selectionSet right.selectionSet

theorem selectionSetShapeEqBool_self (shape : SelectionSetShape)
    : selectionSetShapeEqBool shape shape = true := by
  cases shape with
  | mk selectionSet =>
      simp [selectionSetShapeEqBool, selectionSetEqBool_self]

theorem selectionSetShapeEqBool_eq {left right : SelectionSetShape}
    : selectionSetShapeEqBool left right = true -> left = right := by
  cases left with
  | mk leftSelectionSet =>
      cases right with
      | mk rightSelectionSet =>
          intro hshape
          simp [selectionSetShapeEqBool] at hshape
          cases selectionSetEqBool_eq hshape
          rfl

def insertSelectionSetShape (shape : SelectionSetShape)
    : List SelectionSetShape -> List SelectionSetShape
  | [] => [shape]
  | existing :: rest =>
      if selectionSetShapeEqBool shape existing then
        existing :: rest
      else
        existing :: insertSelectionSetShape shape rest

def selectionSetShapeSet (shapes : List SelectionSetShape) : List SelectionSetShape :=
  shapes.foldl (fun shapes shape => insertSelectionSetShape shape shapes) []

theorem selectionSetShape_mem_insert_of_mem (inserted shape : SelectionSetShape)
    : ∀ shapes : List SelectionSetShape,
        shape ∈ shapes -> shape ∈ insertSelectionSetShape inserted shapes
  | [], hmem => by
      simp at hmem
  | existing :: rest, hmem => by
      cases hinsert : selectionSetShapeEqBool inserted existing with
      | true =>
          simp [insertSelectionSetShape, hinsert] at hmem ⊢
          exact hmem
      | false =>
          simp [insertSelectionSetShape, hinsert] at hmem ⊢
          rcases hmem with hhead | htail
          · exact Or.inl hhead
          · exact Or.inr
              (selectionSetShape_mem_insert_of_mem inserted shape rest htail)

theorem selectionSetShape_mem_insert_self (shape : SelectionSetShape)
    : ∀ shapes : List SelectionSetShape, shape ∈ insertSelectionSetShape shape shapes
  | [] => by
      simp [insertSelectionSetShape]
  | existing :: rest => by
      cases hinsert : selectionSetShapeEqBool shape existing with
      | true =>
          have hshape : shape = existing :=
            selectionSetShapeEqBool_eq hinsert
          simp [insertSelectionSetShape, hinsert]
          exact Or.inl hshape
      | false =>
          simp [insertSelectionSetShape, hinsert]
          exact Or.inr (selectionSetShape_mem_insert_self shape rest)

theorem selectionSetShape_mem_foldl_insert_of_member (shape : SelectionSetShape)
    : ∀ (shapes pending : List SelectionSetShape),
        shape ∈ pending
        -> shape
            ∈ shapes.foldl
                (fun shapes shape => insertSelectionSetShape shape shapes)
                pending := by
  intro shapes
  induction shapes with
  | nil =>
      intro pending hmem
      exact hmem
  | cons inserted shapes ih =>
      intro pending hmem
      exact ih (insertSelectionSetShape inserted pending)
        (selectionSetShape_mem_insert_of_mem inserted shape pending hmem)

theorem selectionSetShape_mem_foldl_insert_of_mem (shape : SelectionSetShape)
    : ∀ (shapes pending : List SelectionSetShape),
        shape ∈ shapes
        -> shape
            ∈ shapes.foldl
                (fun shapes shape => insertSelectionSetShape shape shapes)
                pending := by
  intro shapes
  induction shapes with
  | nil =>
      intro pending hmem
      simp at hmem
  | cons inserted shapes ih =>
      intro pending hmem
      have hcases : shape = inserted ∨ shape ∈ shapes := by
        simpa using hmem
      rcases hcases with hhead | htail
      · have hin :
            shape ∈ insertSelectionSetShape inserted pending := by
          rw [← hhead]
          exact selectionSetShape_mem_insert_self shape pending
        exact selectionSetShape_mem_foldl_insert_of_member
          shape shapes (insertSelectionSetShape inserted pending) hin
      · exact ih (insertSelectionSetShape inserted pending) htail

theorem selectionSetShape_mem_shapeSet_of_mem
    (shape : SelectionSetShape) (shapes : List SelectionSetShape)
    : shape ∈ shapes -> shape ∈ selectionSetShapeSet shapes := by
  intro hmem
  simpa [selectionSetShapeSet] using
    selectionSetShape_mem_foldl_insert_of_mem shape shapes
      ([] : List SelectionSetShape) hmem

theorem selectionSetShape_mem_insert_cases (inserted shape : SelectionSetShape)
    : ∀ shapes : List SelectionSetShape,
        shape ∈ insertSelectionSetShape inserted shapes
        -> shape = inserted ∨ shape ∈ shapes
  | [], hmem => by
      simp [insertSelectionSetShape] at hmem
      exact Or.inl hmem
  | existing :: rest, hmem => by
      cases hinsert : selectionSetShapeEqBool inserted existing with
      | true =>
          have hinsertEq : inserted = existing :=
            selectionSetShapeEqBool_eq hinsert
          simp [insertSelectionSetShape, hinsert] at hmem
          rcases hmem with hhead | htail
          · exact Or.inl (by
              rw [hhead, hinsertEq])
          · exact Or.inr (by simp [htail])
      | false =>
          simp [insertSelectionSetShape, hinsert] at hmem
          rcases hmem with hhead | htail
          · exact Or.inr (by simp [hhead])
          · rcases selectionSetShape_mem_insert_cases inserted shape rest htail with
              hinserted | hrest
            · exact Or.inl hinserted
            · exact Or.inr (by simp [hrest])

theorem selectionSetShape_mem_foldl_insert_cases (shape : SelectionSetShape)
    : ∀ (shapes pending : List SelectionSetShape),
        shape
          ∈ shapes.foldl
              (fun shapes shape => insertSelectionSetShape shape shapes)
              pending
        -> shape ∈ pending ∨ shape ∈ shapes := by
  intro shapes
  induction shapes with
  | nil =>
      intro pending hmem
      exact Or.inl hmem
  | cons inserted shapes ih =>
      intro pending hmem
      have htail :=
        ih (insertSelectionSetShape inserted pending) hmem
      rcases htail with hfromInsert | hfromTail
      · rcases selectionSetShape_mem_insert_cases inserted shape pending
            hfromInsert with hinserted | hpending
        · exact Or.inr (by simp [hinserted])
        · exact Or.inl hpending
      · exact Or.inr (by simp [hfromTail])

theorem selectionSetShape_mem_of_mem_shapeSet
    (shape : SelectionSetShape) (shapes : List SelectionSetShape)
    : shape ∈ selectionSetShapeSet shapes -> shape ∈ shapes := by
  intro hmem
  rcases selectionSetShape_mem_foldl_insert_cases shape shapes
      ([] : List SelectionSetShape)
      (by simpa [selectionSetShapeSet] using hmem) with hnil | hraw
  · simp at hnil
  · exact hraw

def selectionSetShapeWeight (schema : Schema) (shape : SelectionSetShape) : Nat :=
  SelectionSet.size shape.selectionSet * (schema.objectTypes.length + 1)

def selectionSetShapeSetWeight (schema : Schema) : List SelectionSetShape -> Nat
  | [] => 0
  | shape :: shapes =>
      selectionSetShapeWeight schema shape + selectionSetShapeSetWeight schema shapes

def selectionSetShapeBreadthWeight (schema : Schema) (shape : SelectionSetShape) : Nat :=
  selectionSetBreadthWeight schema shape.selectionSet

def selectionSetShapeBreadthSetWeight (schema : Schema) : List SelectionSetShape -> Nat
  | [] => 0
  | shape :: shapes =>
      selectionSetShapeBreadthWeight schema shape
      + selectionSetShapeBreadthSetWeight schema shapes

def scheduleFieldShapeChildSelectionSetShape (shape : ScheduleFieldShape)
    : SelectionSetShape :=
  { selectionSet := shape.childSelectionSet }

def expectedScheduleQueueChildSelectionSetShapes (queue : ExpectedScheduleQueue ObjectRef)
    : List SelectionSetShape :=
  (expectedScheduleQueueShapeSet queue).map scheduleFieldShapeChildSelectionSetShape

/--
Proof-only frontier budget for the breadth scheduler.

* `expectedScheduleQueueShapeSet queue).length` counts the current scheduled field
  shapes that can each consume one `drainLoop` step.
* `selectionSetShapeSetWeight` charges the future child-selection work once per distinct
  child selection-set shape, rather than once per runtime parent type. This is the part
  needed for cousin field selections: many concrete parent types may share the same
  future child shapes, and the forward queue merges those child items before they run.
-/
def expectedScheduleQueueFrontierBudget
    (schema : Schema) (queue : ExpectedScheduleQueue ObjectRef)
    : Nat :=
  (expectedScheduleQueueShapeSet queue).length
  + selectionSetShapeSetWeight schema
      (selectionSetShapeSet (expectedScheduleQueueChildSelectionSetShapes queue))

-----------------------------------------------------------------------------------------
-- Materialized child-selection credits
-----------------------------------------------------------------------------------------

/--
Proof-only child-work credit state.

`materialized` records child selection-set shapes whose child field work has already
been enqueued by some earlier item in the current drain pass. A later item may still have
the same child selection set in one of its segments, but it should not be charged again:
enqueueing that later item's children only appends sources to field shapes already in the
forward queue.
-/
abbrev MaterializedChildSelections := List SelectionSetShape

def selectionSetShapeMemberBool (shape : SelectionSetShape)
    : List SelectionSetShape -> Bool
  | [] => false
  | existing :: rest =>
      selectionSetShapeEqBool shape existing || selectionSetShapeMemberBool shape rest

def materializedSelectionExtends (newer older : MaterializedChildSelections) : Prop :=
  ∀ shape,
    selectionSetShapeMemberBool shape older = true
    -> selectionSetShapeMemberBool shape newer = true

def insertSelectionSetShapeCredit
    (shape : SelectionSetShape)
    (materialized : MaterializedChildSelections)
    : MaterializedChildSelections :=
  insertSelectionSetShape shape materialized

def materializedChildSelectionSetShapes
    (materialized : MaterializedChildSelections)
    (shapes : List SelectionSetShape)
    : List SelectionSetShape :=
  shapes.filter (fun shape => selectionSetShapeMemberBool shape materialized)

def unmaterializedChildSelectionSetShapes
    (materialized : MaterializedChildSelections)
    (shapes : List SelectionSetShape)
    : List SelectionSetShape :=
  shapes.filter (fun shape => !selectionSetShapeMemberBool shape materialized)

def expectedQueueItemChildSelectionSetShapes (item : ExpectedQueueItem ObjectRef)
    : List SelectionSetShape :=
  (expectedQueueItemShapeSet item).map scheduleFieldShapeChildSelectionSetShape

def materializeExpectedQueueItem
    (item : ExpectedQueueItem ObjectRef)
    (materialized : MaterializedChildSelections)
    : MaterializedChildSelections :=
  (expectedQueueItemChildSelectionSetShapes item).foldl
    (fun materialized shape =>
      insertSelectionSetShapeCredit shape materialized)
    materialized

/--
The drain-loop budget after some child selection sets have already been materialized.
The first term counts current queue items/shapes still requiring resolver calls. The
second term conservatively charges each item's child-selection credits. The
`materialized` state is still threaded so the proof can mirror drain order, but this
budget deliberately does not discharge shared child-selection credits early; doing so
would require a finer runtime-type coverage invariant proving the already-materialized
child field shapes are present in the remaining queue.
-/
def expectedScheduleQueueCreditBudget
    (schema : Schema) (materialized : MaterializedChildSelections)
    (queue : ExpectedScheduleQueue ObjectRef)
    : Nat :=
  (expectedScheduleQueueShapeSet queue).length
  + selectionSetShapeSetWeight schema
      (selectionSetShapeSet
        (unmaterializedChildSelectionSetShapes materialized
          (expectedScheduleQueueChildSelectionSetShapes queue)))

def expectedQueueItemCurrentShapeCount (item : ExpectedQueueItem ObjectRef) : Nat :=
  (expectedQueueItemShapeSet item).length

def expectedQueueItemUnmaterializedCreditWeight
    (schema : Schema) (materialized : MaterializedChildSelections)
    (item : ExpectedQueueItem ObjectRef)
    : Nat :=
  selectionSetShapeSetWeight schema
    (unmaterializedChildSelectionSetShapes materialized
      (expectedQueueItemChildSelectionSetShapes item))

/--
Ordered proof-only drain budget.

Unlike `expectedScheduleQueueCreditBudget`, this follows queue order and updates the
materialized child-selection credits after each item. That is the invariant needed for
the drain loop: rest items that share a child selection with the head do not keep a stale
future-work charge after the head has already enqueued that child work.
-/
def expectedScheduleQueueDrainBudget (schema : Schema)
    : MaterializedChildSelections -> ExpectedScheduleQueue ObjectRef -> Nat
  | _materialized, [] => 0
  | materialized, item :: rest =>
      expectedQueueItemCurrentShapeCount item
      + expectedQueueItemUnmaterializedCreditWeight schema materialized item
      + expectedScheduleQueueDrainBudget schema
          (materializeExpectedQueueItem item materialized) rest

/--
Credit state after a queue prefix has been processed in drain order.

The ordered drain budget threads the same state. Keeping this function explicit lets
proofs split a queue into a processed prefix and an unprocessed suffix without
re-expanding the budget recursion at every use site.
-/
def materializeExpectedScheduleQueue
    : MaterializedChildSelections -> ExpectedScheduleQueue ObjectRef
      -> MaterializedChildSelections
  | materialized, [] => materialized
  | materialized, item :: rest =>
      materializeExpectedScheduleQueue
        (materializeExpectedQueueItem item materialized) rest

theorem selectionSetShapeMemberBool_insert_self
    (shape : SelectionSetShape)
    (materialized : MaterializedChildSelections)
    : selectionSetShapeMemberBool shape (insertSelectionSetShapeCredit shape materialized)
      = true := by
  induction materialized with
  | nil =>
      simp [insertSelectionSetShapeCredit, insertSelectionSetShape,
        selectionSetShapeMemberBool, selectionSetShapeEqBool_self]
  | cons existing rest ih =>
      cases hshape : selectionSetShapeEqBool shape existing with
      | true =>
          simp [insertSelectionSetShapeCredit, insertSelectionSetShape,
            selectionSetShapeMemberBool, hshape]
      | false =>
          simp [insertSelectionSetShapeCredit, insertSelectionSetShape,
            selectionSetShapeMemberBool, hshape]
          exact ih

theorem selectionSetShapeMemberBool_insert_of_member
    (shape inserted : SelectionSetShape)
    (materialized : MaterializedChildSelections)
    : selectionSetShapeMemberBool shape materialized = true
      -> selectionSetShapeMemberBool shape
            (insertSelectionSetShapeCredit inserted materialized)
          = true := by
  intro hmember
  induction materialized with
  | nil =>
      simp [selectionSetShapeMemberBool] at hmember
  | cons existing rest ih =>
      cases hinsert : selectionSetShapeEqBool inserted existing with
      | true =>
          simpa [insertSelectionSetShapeCredit, insertSelectionSetShape,
            selectionSetShapeMemberBool, hinsert] using hmember
      | false =>
          cases hshape : selectionSetShapeEqBool shape existing with
          | true =>
              simp [insertSelectionSetShapeCredit, insertSelectionSetShape,
                selectionSetShapeMemberBool, hinsert, hshape]
          | false =>
              simp [selectionSetShapeMemberBool, hshape] at hmember
              simp [insertSelectionSetShapeCredit, insertSelectionSetShape,
                selectionSetShapeMemberBool, hinsert, hshape]
              simpa [insertSelectionSetShapeCredit] using ih hmember

theorem selectionSetShapeMemberBool_of_insert_of_ne
    (shape inserted : SelectionSetShape)
    (materialized : MaterializedChildSelections)
    : selectionSetShapeEqBool shape inserted = false
      -> selectionSetShapeMemberBool shape
            (insertSelectionSetShapeCredit inserted materialized)
          = true
      -> selectionSetShapeMemberBool shape materialized = true := by
  intro hneq hmember
  induction materialized with
  | nil =>
      simp [insertSelectionSetShapeCredit, insertSelectionSetShape,
        selectionSetShapeMemberBool, hneq] at hmember
  | cons existing rest ih =>
      cases hinsert : selectionSetShapeEqBool inserted existing with
      | true =>
          simpa [insertSelectionSetShapeCredit, insertSelectionSetShape,
            selectionSetShapeMemberBool, hinsert] using hmember
      | false =>
          cases hshape : selectionSetShapeEqBool shape existing with
          | true =>
              simp [selectionSetShapeMemberBool, hshape]
          | false =>
              simp [insertSelectionSetShapeCredit, insertSelectionSetShape,
                selectionSetShapeMemberBool, hinsert, hshape] at hmember
              have htail := ih hmember
              simpa [selectionSetShapeMemberBool, hshape] using htail

theorem selectionSetShapeMemberBool_foldl_insert_of_member (shape : SelectionSetShape)
    : ∀ (shapes : List SelectionSetShape) (materialized : MaterializedChildSelections),
        selectionSetShapeMemberBool shape materialized = true
        -> selectionSetShapeMemberBool shape
              (shapes.foldl
                (fun materialized shape =>
                  insertSelectionSetShapeCredit shape materialized)
                materialized)
            = true
  | [], _materialized, hmember => by
      simpa using hmember
  | inserted :: rest, materialized, hmember => by
      exact selectionSetShapeMemberBool_foldl_insert_of_member
        shape rest (insertSelectionSetShapeCredit inserted materialized)
        (selectionSetShapeMemberBool_insert_of_member shape inserted
          materialized hmember)

theorem selectionSetShapeMemberBool_foldl_insert_of_mem (shape : SelectionSetShape)
    : ∀ (shapes : List SelectionSetShape) (materialized : MaterializedChildSelections),
        shape ∈ shapes
        -> selectionSetShapeMemberBool shape
              (shapes.foldl
                (fun materialized shape =>
                  insertSelectionSetShapeCredit shape materialized)
                materialized)
            = true
  | [], _materialized, hmem => by
      simp at hmem
  | inserted :: rest, materialized, hmem => by
      simp at hmem
      rcases hmem with hhead | htail
      · subst inserted
        have hself :=
          selectionSetShapeMemberBool_insert_self shape materialized
        exact selectionSetShapeMemberBool_foldl_insert_of_member shape rest
          (insertSelectionSetShapeCredit shape materialized) hself
      · exact selectionSetShapeMemberBool_foldl_insert_of_mem
          shape rest (insertSelectionSetShapeCredit inserted materialized) htail

theorem materializedSelectionExtends_refl (materialized : MaterializedChildSelections)
    : materializedSelectionExtends materialized materialized := by
  intro shape hmember
  exact hmember

theorem materializedSelectionExtends_insert
    (shape : SelectionSetShape)
    (materialized : MaterializedChildSelections)
    : materializedSelectionExtends
        (insertSelectionSetShapeCredit shape materialized) materialized := by
  intro existing hmember
  exact selectionSetShapeMemberBool_insert_of_member existing shape
    materialized hmember

theorem materializedSelectionExtends_insert_of_member
    {newer older : MaterializedChildSelections}
    (shape : SelectionSetShape)
    : selectionSetShapeMemberBool shape newer = true
      -> materializedSelectionExtends newer older
      -> materializedSelectionExtends newer
          (insertSelectionSetShapeCredit shape older) := by
  intro hshape hextends existing hmember
  cases hexisting : selectionSetShapeEqBool existing shape with
  | true =>
      have heq : existing = shape :=
        selectionSetShapeEqBool_eq hexisting
      subst existing
      exact hshape
  | false =>
      have holder : selectionSetShapeMemberBool existing older = true :=
        selectionSetShapeMemberBool_of_insert_of_ne existing shape older
          hexisting hmember
      exact hextends existing holder

theorem materializedSelectionExtends_foldl_insert
    (shapes : List SelectionSetShape)
    (materialized : MaterializedChildSelections)
    : materializedSelectionExtends
        (shapes.foldl
          (fun materialized shape =>
            insertSelectionSetShapeCredit shape materialized)
          materialized)
        materialized := by
  intro shape hmember
  exact selectionSetShapeMemberBool_foldl_insert_of_member
    shape shapes materialized hmember

theorem materializedSelectionExtends_foldl_insert_of_extends
    (shapes : List SelectionSetShape)
    {newer older : MaterializedChildSelections}
    : materializedSelectionExtends newer older
      -> materializedSelectionExtends
          (shapes.foldl
            (fun materialized shape =>
              insertSelectionSetShapeCredit shape materialized)
            newer)
          older := by
  intro hextends shape hmember
  exact selectionSetShapeMemberBool_foldl_insert_of_member
    shape shapes newer (hextends shape hmember)

theorem materializedSelectionExtends_foldl_insert_of_all_member
    (shapes : List SelectionSetShape)
    {newer older : MaterializedChildSelections}
    : (∀ shape, shape ∈ shapes -> selectionSetShapeMemberBool shape newer = true)
      -> materializedSelectionExtends newer older
      -> materializedSelectionExtends newer
          (shapes.foldl
            (fun materialized shape =>
              insertSelectionSetShapeCredit shape materialized)
            older) := by
  intro hshapes hextends
  induction shapes generalizing older with
  | nil =>
      simpa using hextends
  | cons shape rest ih =>
      have hshape : selectionSetShapeMemberBool shape newer = true :=
        hshapes shape (by simp)
      have hrest :
          ∀ restShape, restShape ∈ rest ->
            selectionSetShapeMemberBool restShape newer = true := by
        intro restShape hrestShape
        exact hshapes restShape (by simp [hrestShape])
      exact ih hrest
        (materializedSelectionExtends_insert_of_member shape hshape hextends)

theorem materializeExpectedQueueItem_extends
    (item : ExpectedQueueItem ObjectRef)
    (materialized : MaterializedChildSelections)
    : materializedSelectionExtends
        (materializeExpectedQueueItem item materialized) materialized := by
  simpa [materializeExpectedQueueItem] using
    materializedSelectionExtends_foldl_insert
      (expectedQueueItemChildSelectionSetShapes item) materialized

theorem materializeExpectedQueueItem_extends_of_extends
    (item : ExpectedQueueItem ObjectRef)
    {newer older : MaterializedChildSelections}
    : materializedSelectionExtends newer older
      -> materializedSelectionExtends
          (materializeExpectedQueueItem item newer)
          (materializeExpectedQueueItem item older) := by
  intro hextends
  unfold materializeExpectedQueueItem
  induction expectedQueueItemChildSelectionSetShapes item generalizing newer older with
  | nil =>
      simpa using hextends
  | cons shape rest ih =>
      apply ih
      intro existing hmember
      cases hshape : selectionSetShapeEqBool existing shape with
      | true =>
          have hexisting : existing = shape :=
            selectionSetShapeEqBool_eq hshape
          subst existing
          exact selectionSetShapeMemberBool_insert_self shape newer
      | false =>
          have hold : selectionSetShapeMemberBool existing older = true := by
            exact selectionSetShapeMemberBool_of_insert_of_ne
              existing shape older hshape hmember
          have hnew := hextends existing hold
          exact selectionSetShapeMemberBool_insert_of_member existing shape
            newer hnew

theorem selectionSetShapeMemberBool_materializeExpectedQueueItem_of_mem
    (shape : SelectionSetShape) (item : ExpectedQueueItem ObjectRef)
    (materialized : MaterializedChildSelections)
    : shape ∈ expectedQueueItemChildSelectionSetShapes item
      -> selectionSetShapeMemberBool shape
            (materializeExpectedQueueItem item materialized)
          = true := by
  intro hmem
  simpa [materializeExpectedQueueItem] using
    selectionSetShapeMemberBool_foldl_insert_of_mem
      shape (expectedQueueItemChildSelectionSetShapes item)
      materialized hmem

-----------------------------------------------------------------------------------------
-- Proof-facing schedule-shape universe
-----------------------------------------------------------------------------------------

/--
Concrete parent-type candidates used by the proof-only schedule universe. The root type is
included explicitly because it may be an operation-specific object name; schema object
types cover every concrete runtime object scope produced below the root.
-/
def scheduleUniverseParentTypes (schema : Schema) (rootType : Name) : List Name :=
  rootType :: schema.objectTypes.map ObjectType.name

def scheduleShapesForSelectionSetAtParent
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (selectionSet : List Selection)
    : List ScheduleFieldShape :=
  collectedGroupsScheduleShapes parentType
    (collectFieldsByKey schema variableValues parentType selectionSet)

def scheduleShapesForSelectionSetAtParents
    (schema : Schema) (variableValues : VariableValues)
    : List Name -> List Selection -> List ScheduleFieldShape
  | [], _selectionSet => []
  | parentType :: rest, selectionSet =>
      scheduleShapesForSelectionSetAtParent schema variableValues parentType selectionSet
      ++ scheduleShapesForSelectionSetAtParents schema variableValues rest selectionSet

/--
Fuel-bounded syntactic over-approximation of every field shape that can appear while
draining a breadth queue rooted at `selectionSet`.

This is not runtime fuel. It is only a structurally decreasing proof device: each pass
adds the field groups collected at the current selection set for every possible concrete
parent type, then descends into direct subselection sets with one smaller bound.
-/
def selectionSetScheduleShapeUniverseBounded
    (schema : Schema) (variableValues : VariableValues)
    (parentTypes : List Name)
    : Nat -> List Selection -> List ScheduleFieldShape
  | 0, _selectionSet => []
  | fuel + 1, selectionSet =>
      scheduleShapesForSelectionSetAtParents schema variableValues parentTypes
        selectionSet
      ++ (selectionSet.map
            (fun selection =>
              selectionSetScheduleShapeUniverseBounded schema variableValues
                parentTypes fuel selection.subselections)).flatten

def selectionSetScheduleShapeUniverse
    (schema : Schema) (variableValues : VariableValues)
    (rootType : Name) (selectionSet : List Selection)
    : List ScheduleFieldShape :=
  selectionSetScheduleShapeUniverseBounded schema variableValues
    (scheduleUniverseParentTypes schema rootType)
    (SelectionSet.size selectionSet + 1)
    selectionSet

def operationScheduleShapeUniverse
    (schema : Schema) (variableValues : VariableValues)
    (operation : Operation)
    : List ScheduleFieldShape :=
  selectionSetScheduleShapeUniverse schema variableValues (operation.rootType schema)
    operation.selectionSet

theorem selectionSetShapeSetWeight_insert_le
    (schema : Schema) (shape : SelectionSetShape)
    (shapes : List SelectionSetShape)
    : selectionSetShapeSetWeight schema (insertSelectionSetShape shape shapes)
      <= selectionSetShapeSetWeight schema shapes
          + selectionSetShapeWeight schema shape := by
  induction shapes with
  | nil =>
      simp [insertSelectionSetShape, selectionSetShapeSetWeight]
  | cons existing rest ih =>
      cases hshape : selectionSetShapeEqBool shape existing with
      | true =>
          simp [insertSelectionSetShape, selectionSetShapeSetWeight, hshape]
      | false =>
          simp [insertSelectionSetShape, selectionSetShapeSetWeight, hshape]
          omega

theorem selectionSetShapeBreadthSetWeight_insert_le
    (schema : Schema) (shape : SelectionSetShape)
    (shapes : List SelectionSetShape)
    : selectionSetShapeBreadthSetWeight schema (insertSelectionSetShape shape shapes)
      <= selectionSetShapeBreadthSetWeight schema shapes
          + selectionSetShapeBreadthWeight schema shape := by
  induction shapes with
  | nil =>
      simp [insertSelectionSetShape, selectionSetShapeBreadthSetWeight]
  | cons existing rest ih =>
      cases hshape : selectionSetShapeEqBool shape existing with
      | true =>
          simp [insertSelectionSetShape, selectionSetShapeBreadthSetWeight,
            hshape]
      | false =>
          simp [insertSelectionSetShape, selectionSetShapeBreadthSetWeight,
            hshape]
          omega

theorem selectionSetShapeSet_foldl_weight_le
    (schema : Schema) (pending shapes : List SelectionSetShape)
    : selectionSetShapeSetWeight schema
        (shapes.foldl (fun shapes shape => insertSelectionSetShape shape shapes) pending)
      <= selectionSetShapeSetWeight schema pending
          + selectionSetShapeSetWeight schema shapes := by
  induction shapes generalizing pending with
  | nil =>
      simp [selectionSetShapeSetWeight]
  | cons shape shapes ih =>
      have htail :=
        ih (insertSelectionSetShape shape pending)
      have hinsert :=
        selectionSetShapeSetWeight_insert_le schema shape pending
      simp [selectionSetShapeSetWeight] at htail ⊢
      omega

theorem selectionSetShapeSet_weight_le (schema : Schema) (shapes : List SelectionSetShape)
    : selectionSetShapeSetWeight schema (selectionSetShapeSet shapes)
      <= selectionSetShapeSetWeight schema shapes := by
  simpa [selectionSetShapeSet, selectionSetShapeSetWeight] using
    selectionSetShapeSet_foldl_weight_le schema
      ([] : List SelectionSetShape) shapes

theorem selectionSetShapeBreadthSet_foldl_weight_le
    (schema : Schema) (pending shapes : List SelectionSetShape)
    : selectionSetShapeBreadthSetWeight schema
        (shapes.foldl (fun shapes shape => insertSelectionSetShape shape shapes) pending)
      <= selectionSetShapeBreadthSetWeight schema pending
          + selectionSetShapeBreadthSetWeight schema shapes := by
  induction shapes generalizing pending with
  | nil =>
      simp [selectionSetShapeBreadthSetWeight]
  | cons shape shapes ih =>
      have htail :=
        ih (insertSelectionSetShape shape pending)
      have hinsert :=
        selectionSetShapeBreadthSetWeight_insert_le schema shape pending
      simp [selectionSetShapeBreadthSetWeight] at htail ⊢
      omega

theorem selectionSetShapeBreadthSet_weight_le
    (schema : Schema) (shapes : List SelectionSetShape)
    : selectionSetShapeBreadthSetWeight schema (selectionSetShapeSet shapes)
      <= selectionSetShapeBreadthSetWeight schema shapes := by
  simpa [selectionSetShapeSet, selectionSetShapeBreadthSetWeight] using
    selectionSetShapeBreadthSet_foldl_weight_le schema
      ([] : List SelectionSetShape) shapes

theorem selectionSetShapeSetWeight_insert_le_of_mem
    (schema : Schema) (shape : SelectionSetShape)
    : ∀ shapes : List SelectionSetShape,
        shape ∈ shapes
        -> selectionSetShapeSetWeight schema (insertSelectionSetShape shape shapes)
            <= selectionSetShapeSetWeight schema shapes := by
  intro shapes
  induction shapes with
  | nil =>
      intro hmem
      simp at hmem
  | cons existing rest ih =>
      intro hmem
      cases hinsert : selectionSetShapeEqBool shape existing with
      | true =>
          simp [insertSelectionSetShape, hinsert]
      | false =>
          have htail : shape ∈ rest := by
            have hcases : shape = existing ∨ shape ∈ rest := by
              simpa using hmem
            rcases hcases with hhead | htail
            · subst existing
              simp [selectionSetShapeEqBool_self] at hinsert
            · exact htail
          have hrest := ih htail
          simp [insertSelectionSetShape, hinsert, selectionSetShapeSetWeight]
          omega

theorem selectionSetShapeSetWeight_filter_le
    (schema : Schema) (p : SelectionSetShape -> Bool)
    : ∀ shapes : List SelectionSetShape,
        selectionSetShapeSetWeight schema (shapes.filter p)
        <= selectionSetShapeSetWeight schema shapes
  | [] => by
      simp [selectionSetShapeSetWeight]
  | shape :: shapes => by
      have htail := selectionSetShapeSetWeight_filter_le schema p shapes
      cases h : p shape with
      | true =>
          simp [List.filter, h, selectionSetShapeSetWeight]
          omega
      | false =>
          simp [List.filter, h, selectionSetShapeSetWeight]
          omega

theorem selectionSetShapeSetWeight_set_filter_le
    (schema : Schema) (p : SelectionSetShape -> Bool)
    (shapes : List SelectionSetShape)
    : selectionSetShapeSetWeight schema (selectionSetShapeSet (shapes.filter p))
      <= selectionSetShapeSetWeight schema shapes := by
  exact Nat.le_trans
    (selectionSetShapeSet_weight_le schema (shapes.filter p))
    (selectionSetShapeSetWeight_filter_le schema p shapes)

theorem selectionSetShapeWeight_unmaterialized_insertScheduleFieldShape_le
    (schema : Schema) (materialized : MaterializedChildSelections)
    (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        selectionSetShapeSetWeight schema
          (unmaterializedChildSelectionSetShapes materialized
            ((insertScheduleFieldShape shape shapes).map
              scheduleFieldShapeChildSelectionSetShape))
        <= selectionSetShapeSetWeight schema
              (unmaterializedChildSelectionSetShapes materialized
                (shapes.map scheduleFieldShapeChildSelectionSetShape))
            + selectionSetShapeWeight schema
                (scheduleFieldShapeChildSelectionSetShape shape)
  | [] => by
      cases hmember :
          selectionSetShapeMemberBool
            (scheduleFieldShapeChildSelectionSetShape shape) materialized with
      | true =>
          simp [insertScheduleFieldShape, unmaterializedChildSelectionSetShapes,
            hmember, selectionSetShapeSetWeight]
      | false =>
          simp [insertScheduleFieldShape, unmaterializedChildSelectionSetShapes,
            hmember, selectionSetShapeSetWeight]
  | existing :: rest => by
      cases hshape : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hshape]
      | false =>
          have htail :=
            selectionSetShapeWeight_unmaterialized_insertScheduleFieldShape_le
              schema materialized shape rest
          cases hexisting :
              selectionSetShapeMemberBool
                (scheduleFieldShapeChildSelectionSetShape existing)
                materialized with
          | true =>
              simp [insertScheduleFieldShape, hshape,
                unmaterializedChildSelectionSetShapes, hexisting] at htail ⊢
              exact htail
          | false =>
              simp [insertScheduleFieldShape, hshape,
                unmaterializedChildSelectionSetShapes, hexisting,
                selectionSetShapeSetWeight] at htail ⊢
              omega

theorem selectionSetShapeBreadthWeight_insertScheduleFieldShape_le
    (schema : Schema) (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        selectionSetShapeBreadthSetWeight schema
          ((insertScheduleFieldShape shape shapes).map
            scheduleFieldShapeChildSelectionSetShape)
        <= selectionSetShapeBreadthSetWeight schema
              (shapes.map scheduleFieldShapeChildSelectionSetShape)
            + selectionSetShapeBreadthWeight schema
                (scheduleFieldShapeChildSelectionSetShape shape)
  | [] => by
      simp [insertScheduleFieldShape, selectionSetShapeBreadthSetWeight]
  | existing :: rest => by
      cases hexisting : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hexisting,
            selectionSetShapeBreadthSetWeight]
      | false =>
          have htail :=
            selectionSetShapeBreadthWeight_insertScheduleFieldShape_le
              schema shape rest
          simp [insertScheduleFieldShape, hexisting,
            selectionSetShapeBreadthSetWeight] at htail ⊢
          omega

theorem unmaterializedChildSelectionSetShapes_empty (shapes : List SelectionSetShape)
    : unmaterializedChildSelectionSetShapes [] shapes = shapes := by
  induction shapes with
  | nil =>
      rfl
  | cons shape shapes ih =>
      simp [unmaterializedChildSelectionSetShapes,
        selectionSetShapeMemberBool]

theorem expectedScheduleQueueCreditBudget_empty
    (schema : Schema) (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCreditBudget schema [] queue
      = expectedScheduleQueueFrontierBudget schema queue := by
  simp [expectedScheduleQueueCreditBudget,
    expectedScheduleQueueFrontierBudget,
    unmaterializedChildSelectionSetShapes_empty]

theorem expectedScheduleQueueDrainBudget_nil
    (schema : Schema) (materialized : MaterializedChildSelections)
    : expectedScheduleQueueDrainBudget (ObjectRef := ObjectRef) schema materialized []
      = 0 := by
  rfl

theorem expectedScheduleQueueDrainBudget_cons
    (schema : Schema) (materialized : MaterializedChildSelections)
    (item : ExpectedQueueItem ObjectRef) (rest : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueDrainBudget schema materialized (item :: rest)
      = expectedQueueItemCurrentShapeCount item
        + expectedQueueItemUnmaterializedCreditWeight schema materialized item
        + expectedScheduleQueueDrainBudget schema
            (materializeExpectedQueueItem item materialized) rest := by
  rfl

theorem materializeExpectedScheduleQueue_nil (materialized : MaterializedChildSelections)
    : materializeExpectedScheduleQueue (ObjectRef := ObjectRef) materialized []
      = materialized := by
  rfl

theorem materializeExpectedScheduleQueue_cons
    (materialized : MaterializedChildSelections)
    (item : ExpectedQueueItem ObjectRef) (rest : ExpectedScheduleQueue ObjectRef)
    : materializeExpectedScheduleQueue materialized (item :: rest)
      = materializeExpectedScheduleQueue
          (materializeExpectedQueueItem item materialized) rest := by
  rfl

theorem expectedScheduleQueueDrainBudget_append (schema : Schema)
    : ∀ (materialized : MaterializedChildSelections)
        (left right : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueDrainBudget schema materialized (left ++ right)
        = expectedScheduleQueueDrainBudget schema materialized left
          + expectedScheduleQueueDrainBudget schema
              (materializeExpectedScheduleQueue materialized left) right
  | materialized, [], right => by
      simp [expectedScheduleQueueDrainBudget,
        materializeExpectedScheduleQueue]
  | materialized, item :: left, right => by
      have htail :=
        expectedScheduleQueueDrainBudget_append schema
          (materializeExpectedQueueItem item materialized) left right
      simp [expectedScheduleQueueDrainBudget,
        materializeExpectedScheduleQueue, htail, Nat.add_assoc]

theorem unmaterializedChildSelectionSetShapes_eq_nil_of_all_member
    (materialized : MaterializedChildSelections)
    (shapes : List SelectionSetShape)
    : (∀ shape, shape ∈ shapes -> selectionSetShapeMemberBool shape materialized = true)
      -> unmaterializedChildSelectionSetShapes materialized shapes = [] := by
  intro hmember
  induction shapes with
  | nil =>
      rfl
  | cons shape rest ih =>
      have hhead : selectionSetShapeMemberBool shape materialized = true :=
        hmember shape (by simp)
      have htail :
          ∀ tailShape, tailShape ∈ rest ->
            selectionSetShapeMemberBool tailShape materialized = true := by
        intro tailShape htailMem
        exact hmember tailShape (List.mem_cons_of_mem shape htailMem)
      have htailNil :
          unmaterializedChildSelectionSetShapes materialized rest = [] :=
        ih htail
      simpa [unmaterializedChildSelectionSetShapes, hhead] using htailNil

theorem unmaterializedChildSelectionSetShapes_materializeExpectedQueueItem
    (item : ExpectedQueueItem ObjectRef)
    (materialized : MaterializedChildSelections)
    : unmaterializedChildSelectionSetShapes
        (materializeExpectedQueueItem item materialized)
        (expectedQueueItemChildSelectionSetShapes item)
      = [] := by
  apply unmaterializedChildSelectionSetShapes_eq_nil_of_all_member
  intro shape hshape
  exact selectionSetShapeMemberBool_materializeExpectedQueueItem_of_mem
    (ObjectRef := ObjectRef) shape item materialized hshape

theorem selectionSetShapeSetWeight_unmaterialized_mono
    (schema : Schema)
    {newer older : MaterializedChildSelections}
    : materializedSelectionExtends newer older
      -> ∀ shapes : List SelectionSetShape,
          selectionSetShapeSetWeight schema
            (unmaterializedChildSelectionSetShapes newer shapes)
          <= selectionSetShapeSetWeight schema
              (unmaterializedChildSelectionSetShapes older shapes)
  | hextends, [] => by
      simp [unmaterializedChildSelectionSetShapes,
        selectionSetShapeSetWeight]
  | hextends, shape :: shapes => by
      have htail :=
        selectionSetShapeSetWeight_unmaterialized_mono
          schema hextends shapes
      cases holder : selectionSetShapeMemberBool shape older with
      | true =>
          have hnewer : selectionSetShapeMemberBool shape newer = true :=
            hextends shape holder
          simp [unmaterializedChildSelectionSetShapes, holder, hnewer] at htail ⊢
          exact htail
      | false =>
          cases hnewer : selectionSetShapeMemberBool shape newer with
          | true =>
              simp [unmaterializedChildSelectionSetShapes, holder, hnewer,
                selectionSetShapeSetWeight] at htail ⊢
              omega
          | false =>
              simp [unmaterializedChildSelectionSetShapes, holder, hnewer,
                selectionSetShapeSetWeight] at htail ⊢
              omega

theorem expectedQueueItemUnmaterializedCreditWeight_mono
    (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    {newer older : MaterializedChildSelections}
    : materializedSelectionExtends newer older
      -> expectedQueueItemUnmaterializedCreditWeight schema newer item
          <= expectedQueueItemUnmaterializedCreditWeight schema older item := by
  intro hextends
  simpa [expectedQueueItemUnmaterializedCreditWeight] using
    selectionSetShapeSetWeight_unmaterialized_mono
      schema hextends (expectedQueueItemChildSelectionSetShapes item)

theorem expectedScheduleQueueDrainBudget_mono (schema : Schema)
    : ∀ (queue : ExpectedScheduleQueue ObjectRef)
        {newer older : MaterializedChildSelections},
        materializedSelectionExtends newer older
        -> expectedScheduleQueueDrainBudget schema newer queue
            <= expectedScheduleQueueDrainBudget schema older queue
  | [], _newer, _older, _hextends => by
      simp [expectedScheduleQueueDrainBudget]
  | item :: rest, newer, older, hextends => by
      have hcredit :=
        expectedQueueItemUnmaterializedCreditWeight_mono
          (ObjectRef := ObjectRef) schema item hextends
      have htail :=
        expectedScheduleQueueDrainBudget_mono schema rest
          (materializeExpectedQueueItem_extends_of_extends
            (ObjectRef := ObjectRef) item hextends)
      simp [expectedScheduleQueueDrainBudget]
      omega

theorem scheduleFieldShape_childWeight_add_one_le_stepWeight
    (schema : Schema) (shape : ScheduleFieldShape)
    : selectionSetShapeWeight schema (scheduleFieldShapeChildSelectionSetShape shape) + 1
      <= scheduleFieldShapeStepWeight schema shape := by
  cases shape with
  | mk key childSelectionSet =>
      simp [selectionSetShapeWeight, scheduleFieldShapeChildSelectionSetShape,
        scheduleFieldShapeStepWeight]
      rw [Nat.add_mul, Nat.mul_add]
      simp

theorem scheduleFieldShapes_childRawWeight_add_length_le_weight (schema : Schema)
    : ∀ shapes : List ScheduleFieldShape,
        selectionSetShapeSetWeight schema
            (shapes.map scheduleFieldShapeChildSelectionSetShape)
          + shapes.length
        <= scheduleFieldShapeSetWeight schema shapes
  | [] => by
      simp [selectionSetShapeSetWeight, scheduleFieldShapeSetWeight]
  | shape :: shapes => by
      have htail :=
        scheduleFieldShapes_childRawWeight_add_length_le_weight
          schema shapes
      have hhead :=
        scheduleFieldShape_childWeight_add_one_le_stepWeight schema shape
      simp [selectionSetShapeSetWeight, scheduleFieldShapeSetWeight]
      omega

theorem scheduleFieldShapes_childSetWeight_add_length_le_weight
    (schema : Schema) (shapes : List ScheduleFieldShape)
    : selectionSetShapeSetWeight schema
          (selectionSetShapeSet (shapes.map scheduleFieldShapeChildSelectionSetShape))
        + shapes.length
      <= scheduleFieldShapeSetWeight schema shapes := by
  have hset :=
    selectionSetShapeSet_weight_le schema
      (shapes.map scheduleFieldShapeChildSelectionSetShape)
  have hraw :=
    scheduleFieldShapes_childRawWeight_add_length_le_weight
      schema shapes
  omega

theorem expectedQueueItemOrderedBudget_le_shapeWeight
    (schema : Schema) (materialized : MaterializedChildSelections)
    (item : ExpectedQueueItem ObjectRef)
    : expectedQueueItemCurrentShapeCount item
        + expectedQueueItemUnmaterializedCreditWeight schema materialized item
      <= expectedQueueItemShapeWeight schema item := by
  let shapes := expectedQueueItemShapeSet item
  have hcredit :
      expectedQueueItemUnmaterializedCreditWeight schema materialized item <=
        selectionSetShapeSetWeight schema
          (shapes.map scheduleFieldShapeChildSelectionSetShape) := by
    simpa [expectedQueueItemUnmaterializedCreditWeight,
      unmaterializedChildSelectionSetShapes,
      expectedQueueItemChildSelectionSetShapes, shapes] using
      selectionSetShapeSetWeight_filter_le schema
        (fun shape => !selectionSetShapeMemberBool shape materialized)
        (shapes.map scheduleFieldShapeChildSelectionSetShape)
  have hbudget :=
    scheduleFieldShapes_childRawWeight_add_length_le_weight schema shapes
  have hcurrent :
      expectedQueueItemCurrentShapeCount item = shapes.length := by
    simp [expectedQueueItemCurrentShapeCount, shapes]
  have hweight :
      expectedQueueItemShapeWeight schema item =
        scheduleFieldShapeSetWeight schema shapes := by
    simp [expectedQueueItemShapeWeight, expectedQueueItemShapeSet, shapes]
  rw [hcurrent, hweight]
  omega

theorem expectedScheduleQueueDrainBudget_le_shapeWeight (schema : Schema)
    : ∀ (materialized : MaterializedChildSelections)
        (queue : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueDrainBudget schema materialized queue
        <= expectedScheduleQueueShapeWeight schema queue
  | _materialized, [] => by
      simp [expectedScheduleQueueDrainBudget, expectedScheduleQueueShapeWeight]
  | materialized, item :: rest => by
      have hitem :=
        expectedQueueItemOrderedBudget_le_shapeWeight
          (ObjectRef := ObjectRef) schema materialized item
      have hrest :=
        expectedScheduleQueueDrainBudget_le_shapeWeight schema
          (materializeExpectedQueueItem item materialized) rest
      simp [expectedScheduleQueueDrainBudget,
        expectedScheduleQueueShapeWeight]
      omega

theorem scheduleFieldShapeSetWeight_append
    (schema : Schema) (left right : List ScheduleFieldShape)
    : scheduleFieldShapeSetWeight schema (left ++ right)
      = scheduleFieldShapeSetWeight schema left
        + scheduleFieldShapeSetWeight schema right := by
  induction left with
  | nil =>
      simp [scheduleFieldShapeSetWeight]
  | cons shape rest ih =>
      simp [scheduleFieldShapeSetWeight, ih, Nat.add_assoc]

theorem expectedScheduleQueueShapes_weight_eq_rawShapeWeight (schema : Schema)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        scheduleFieldShapeSetWeight schema (expectedScheduleQueueShapes queue)
        = expectedScheduleQueueRawShapeWeight schema queue
  | [] => by
      simp [expectedScheduleQueueShapes, expectedScheduleQueueRawShapeWeight,
        scheduleFieldShapeSetWeight]
  | item :: rest => by
      have hrest :=
        expectedScheduleQueueShapes_weight_eq_rawShapeWeight schema rest
      change
        scheduleFieldShapeSetWeight schema
            (expectedQueueItemShapes item ++ expectedScheduleQueueShapes rest) =
          expectedQueueItemRawShapeWeight schema item
            + expectedScheduleQueueRawShapeWeight schema rest
      rw [scheduleFieldShapeSetWeight_append, hrest]
      rfl

theorem scheduleFieldShapeSetWeight_insert_le
    (schema : Schema) (shape : ScheduleFieldShape)
    (shapes : List ScheduleFieldShape)
    : scheduleFieldShapeSetWeight schema (insertScheduleFieldShape shape shapes)
      <= scheduleFieldShapeSetWeight schema shapes
          + scheduleFieldShapeStepWeight schema shape := by
  induction shapes with
  | nil =>
      simp [insertScheduleFieldShape, scheduleFieldShapeSetWeight]
  | cons existing rest ih =>
      cases hshape : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, scheduleFieldShapeSetWeight,
            hshape]
      | false =>
          simp [insertScheduleFieldShape, scheduleFieldShapeSetWeight,
            hshape]
          omega

theorem insertScheduleFieldShape_length_le (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        (insertScheduleFieldShape shape shapes).length <= shapes.length + 1
  | [] => by
      simp [insertScheduleFieldShape]
  | existing :: rest => by
      cases hshape : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hshape]
      | false =>
          have htail := insertScheduleFieldShape_length_le shape rest
          simp [insertScheduleFieldShape, hshape]
          omega

theorem scheduleFieldShapeSet_foldl_length_le (pending shapes : List ScheduleFieldShape)
    : (shapes.foldl
        (fun shapes shape => insertScheduleFieldShape shape shapes)
        pending).length
      <= pending.length + shapes.length := by
  induction shapes generalizing pending with
  | nil =>
      simp
  | cons shape shapes ih =>
      have htail :=
        ih (insertScheduleFieldShape shape pending)
      have hinsert :=
        insertScheduleFieldShape_length_le shape pending
      simp at htail ⊢
      omega

theorem scheduleFieldShapeSet_append_single_length_le
    (shapes : List ScheduleFieldShape) (shape : ScheduleFieldShape)
    : (scheduleFieldShapeSet (shapes ++ [shape])).length
      <= (scheduleFieldShapeSet shapes).length + 1 := by
  unfold scheduleFieldShapeSet
  rw [List.foldl_append]
  simp
  exact insertScheduleFieldShape_length_le shape
    (shapes.foldl
      (fun shapes shape => insertScheduleFieldShape shape shapes) [])

theorem scheduleFieldShapeSet_foldl_weight_le
    (schema : Schema) (pending shapes : List ScheduleFieldShape)
    : scheduleFieldShapeSetWeight schema
        (shapes.foldl (fun shapes shape => insertScheduleFieldShape shape shapes) pending)
      <= scheduleFieldShapeSetWeight schema pending
          + scheduleFieldShapeSetWeight schema shapes := by
  induction shapes generalizing pending with
  | nil =>
      simp [scheduleFieldShapeSetWeight]
  | cons shape shapes ih =>
      have htail :=
        ih (insertScheduleFieldShape shape pending)
      have hinsert :=
        scheduleFieldShapeSetWeight_insert_le schema shape pending
      simp [scheduleFieldShapeSetWeight] at htail ⊢
      omega

theorem scheduleFieldShapeSet_weight_le
    (schema : Schema) (shapes : List ScheduleFieldShape)
    : scheduleFieldShapeSetWeight schema (scheduleFieldShapeSet shapes)
      <= scheduleFieldShapeSetWeight schema shapes := by
  simpa [scheduleFieldShapeSet, scheduleFieldShapeSetWeight] using
    scheduleFieldShapeSet_foldl_weight_le schema
      ([] : List ScheduleFieldShape) shapes

theorem scheduleFieldShapeSetWeight_insert_le_of_mem
    (schema : Schema) (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        shape ∈ shapes
        -> scheduleFieldShapeSetWeight schema (insertScheduleFieldShape shape shapes)
            <= scheduleFieldShapeSetWeight schema shapes := by
  intro shapes
  induction shapes with
  | nil =>
      intro hmem
      simp at hmem
  | cons existing rest ih =>
      intro hmem
      cases hinsert : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hinsert]
      | false =>
          have htail : shape ∈ rest := by
            have hcases : shape = existing ∨ shape ∈ rest := by
              simpa using hmem
            rcases hcases with hhead | htail
            · subst existing
              simp [scheduleFieldShapeEqBool_self] at hinsert
            · exact htail
          have hrest := ih htail
          simp [insertScheduleFieldShape, hinsert, scheduleFieldShapeSetWeight]
          omega

theorem insertScheduleFieldShape_eq_self_of_mem (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        shape ∈ shapes -> insertScheduleFieldShape shape shapes = shapes
  | [], hmem => by
      simp at hmem
  | existing :: rest, hmem => by
      cases hinsert : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hinsert]
      | false =>
          have htail : shape ∈ rest := by
            have hcases : shape = existing ∨ shape ∈ rest := by
              simpa using hmem
            rcases hcases with hhead | htail
            · subst existing
              simp [scheduleFieldShapeEqBool_self] at hinsert
            · exact htail
          have hrest := insertScheduleFieldShape_eq_self_of_mem shape rest htail
          simp [insertScheduleFieldShape, hinsert, hrest]

theorem insertScheduleFieldShape_length_le_of_mem (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        shape ∈ shapes
        -> (insertScheduleFieldShape shape shapes).length <= shapes.length := by
  intro shapes hmem
  rw [insertScheduleFieldShape_eq_self_of_mem shape shapes hmem]
  exact Nat.le_refl shapes.length

theorem insertScheduleFieldShape_ne_nil
    (shape : ScheduleFieldShape) (shapes : List ScheduleFieldShape)
    : insertScheduleFieldShape shape shapes ≠ [] := by
  cases shapes with
  | nil =>
      simp [insertScheduleFieldShape]
  | cons existing rest =>
      cases hshape : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hshape]
      | false =>
          simp [insertScheduleFieldShape, hshape]

theorem scheduleFieldShapeSet_foldl_ne_nil
    : ∀ (shapes pending : List ScheduleFieldShape),
        pending ≠ []
        -> shapes.foldl
              (fun shapes shape => insertScheduleFieldShape shape shapes)
              pending
            ≠ []
  | [], pending, hpending => by
      simpa using hpending
  | shape :: shapes, pending, _hpending => by
      exact scheduleFieldShapeSet_foldl_ne_nil shapes
        (insertScheduleFieldShape shape pending)
        (insertScheduleFieldShape_ne_nil shape pending)

theorem scheduleFieldShapeSet_ne_nil_of_ne_nil
    : ∀ shapes : List ScheduleFieldShape, shapes ≠ [] -> scheduleFieldShapeSet shapes ≠ []
  | [], hshapes => by
      exact False.elim (hshapes rfl)
  | shape :: shapes, _hshapes => by
      unfold scheduleFieldShapeSet
      rw [List.foldl_cons]
      exact scheduleFieldShapeSet_foldl_ne_nil shapes
        (insertScheduleFieldShape shape [])
        (insertScheduleFieldShape_ne_nil shape [])

theorem expectedQueueItemCurrentShapeCount_pos (item : ExpectedQueueItem ObjectRef)
    : item.segments ≠ [] -> 0 < expectedQueueItemCurrentShapeCount item := by
  intro hsegments
  unfold expectedQueueItemCurrentShapeCount expectedQueueItemShapeSet
  have hshapes : expectedQueueItemShapes item ≠ [] := by
    cases item with
    | mk key segments =>
        cases segments with
        | nil =>
            exact False.elim (hsegments rfl)
        | cons segment rest =>
            simp [expectedQueueItemShapes]
  have hset :
      scheduleFieldShapeSet (expectedQueueItemShapes item) ≠ [] :=
    scheduleFieldShapeSet_ne_nil_of_ne_nil
      (expectedQueueItemShapes item) hshapes
  cases hsetList : scheduleFieldShapeSet (expectedQueueItemShapes item) with
  | nil =>
      exact False.elim (hset hsetList)
  | cons shape rest =>
      simp

theorem expectedScheduleQueueFrontierBudget_le_rawShapeWeight
    (schema : Schema) (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueFrontierBudget schema queue
      <= expectedScheduleQueueRawShapeWeight schema queue := by
  let shapes := expectedScheduleQueueShapeSet queue
  have hfront :
      expectedScheduleQueueFrontierBudget schema queue <=
        scheduleFieldShapeSetWeight schema shapes := by
    have hshape :=
      scheduleFieldShapes_childSetWeight_add_length_le_weight schema shapes
    change
      shapes.length +
          selectionSetShapeSetWeight schema
            (selectionSetShapeSet
              (shapes.map scheduleFieldShapeChildSelectionSetShape)) <=
        scheduleFieldShapeSetWeight schema shapes
    rw [Nat.add_comm]
    exact hshape
  have hset :
      scheduleFieldShapeSetWeight schema shapes <=
        scheduleFieldShapeSetWeight schema (expectedScheduleQueueShapes queue) := by
    simpa [shapes, expectedScheduleQueueShapeSet] using
      scheduleFieldShapeSet_weight_le schema
        (expectedScheduleQueueShapes queue)
  have hraw :
      scheduleFieldShapeSetWeight schema (expectedScheduleQueueShapes queue) =
        expectedScheduleQueueRawShapeWeight schema queue :=
    expectedScheduleQueueShapes_weight_eq_rawShapeWeight
      (ObjectRef := ObjectRef) schema queue
  omega

theorem expectedQueueItemShapeWeight_appendSegment_le
    (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemShapeWeight schema
        { item with segments := item.segments ++ [segment] }
      <= expectedQueueItemShapeWeight schema item
          + scheduleFieldShapeStepWeight schema
              (expectedQueueSegmentShape item.key segment) := by
  unfold expectedQueueItemShapeWeight expectedQueueItemShapeSet
  have hshapes :
      expectedQueueItemShapes
          { item with segments := item.segments ++ [segment] } =
        expectedQueueItemShapes item ++
          [expectedQueueSegmentShape item.key segment] := by
    simp [expectedQueueItemShapes]
  rw [hshapes]
  unfold scheduleFieldShapeSet
  rw [List.foldl_append]
  simp
  simpa [expectedQueueItemShapeSet, scheduleFieldShapeSet,
    scheduleFieldShapeSetWeight] using
    scheduleFieldShapeSet_foldl_weight_le schema
      ((expectedQueueItemShapes item).foldl
        (fun shapes shape => insertScheduleFieldShape shape shapes) [])
      [expectedQueueSegmentShape item.key segment]

theorem expectedQueueItemShapeSet_appendSegment
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemShapeSet { item with segments := item.segments ++ [segment] }
      = insertScheduleFieldShape
          (expectedQueueSegmentShape item.key segment)
          (expectedQueueItemShapeSet item) := by
  unfold expectedQueueItemShapeSet scheduleFieldShapeSet
  have hshapes :
      expectedQueueItemShapes
          { item with segments := item.segments ++ [segment] } =
        expectedQueueItemShapes item ++
          [expectedQueueSegmentShape item.key segment] := by
    simp [expectedQueueItemShapes]
  rw [hshapes, List.foldl_append]
  rfl

theorem expectedQueueItemShapeWeight_appendSegment_le_of_shape_mem
    (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueSegmentShape item.key segment ∈ expectedQueueItemShapeSet item
      -> expectedQueueItemShapeWeight schema
            { item with segments := item.segments ++ [segment] }
          <= expectedQueueItemShapeWeight schema item := by
  intro hmem
  unfold expectedQueueItemShapeWeight
  rw [expectedQueueItemShapeSet_appendSegment]
  exact scheduleFieldShapeSetWeight_insert_le_of_mem
    schema (expectedQueueSegmentShape item.key segment)
    (expectedQueueItemShapeSet item) hmem

theorem materializeExpectedQueueItem_appendSegment_extends
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    (materialized : MaterializedChildSelections)
    : materializedSelectionExtends
        (materializeExpectedQueueItem
          { item with segments := item.segments ++ [segment] } materialized)
        (materializeExpectedQueueItem item materialized) := by
  unfold materializeExpectedQueueItem
  apply materializedSelectionExtends_foldl_insert_of_all_member
  · intro shape hshape
    have hshapeMem :
        shape ∈
          (insertScheduleFieldShape
            (expectedQueueSegmentShape item.key segment)
            (expectedQueueItemShapeSet item)).map
              scheduleFieldShapeChildSelectionSetShape := by
      rcases List.mem_map.mp hshape with ⟨fieldShape, hfieldShape, hfieldEq⟩
      subst shape
      exact List.mem_map_of_mem
        (scheduleFieldShape_mem_insert_of_mem
          (expectedQueueSegmentShape item.key segment)
          fieldShape (expectedQueueItemShapeSet item) hfieldShape)
    rcases List.mem_map.mp hshapeMem with ⟨fieldShape, hfieldShape, hfieldEq⟩
    subst shape
    simpa [expectedQueueItemChildSelectionSetShapes,
      expectedQueueItemShapeSet_appendSegment] using
      selectionSetShapeMemberBool_foldl_insert_of_mem
        (scheduleFieldShapeChildSelectionSetShape fieldShape)
        ((insertScheduleFieldShape
          (expectedQueueSegmentShape item.key segment)
          (expectedQueueItemShapeSet item)).map
            scheduleFieldShapeChildSelectionSetShape)
        materialized
        (List.mem_map_of_mem hfieldShape)
  · simpa [materializeExpectedQueueItem] using
      materializeExpectedQueueItem_extends
        (ObjectRef := ObjectRef)
        { item with segments := item.segments ++ [segment] } materialized

theorem expectedQueueItemCurrentShapeCount_appendSegment_le
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemCurrentShapeCount
        { item with segments := item.segments ++ [segment] }
      <= expectedQueueItemCurrentShapeCount item + 1 := by
  unfold expectedQueueItemCurrentShapeCount expectedQueueItemShapeSet
  have hshapes :
      expectedQueueItemShapes
          { item with segments := item.segments ++ [segment] } =
        expectedQueueItemShapes item ++
          [expectedQueueSegmentShape item.key segment] := by
    simp [expectedQueueItemShapes]
  rw [hshapes]
  exact scheduleFieldShapeSet_append_single_length_le
    (expectedQueueItemShapes item)
    (expectedQueueSegmentShape item.key segment)

theorem expectedQueueItemCurrentShapeCount_appendSegment_le_of_shape_mem
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueSegmentShape item.key segment ∈ expectedQueueItemShapeSet item
      -> expectedQueueItemCurrentShapeCount
            { item with segments := item.segments ++ [segment] }
          <= expectedQueueItemCurrentShapeCount item := by
  intro hmem
  unfold expectedQueueItemCurrentShapeCount
  rw [expectedQueueItemShapeSet_appendSegment]
  exact insertScheduleFieldShape_length_le_of_mem
    (expectedQueueSegmentShape item.key segment)
    (expectedQueueItemShapeSet item) hmem

theorem expectedQueueItemUnmaterializedCreditWeight_appendSegment_le
    (schema : Schema) (materialized : MaterializedChildSelections)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemUnmaterializedCreditWeight schema materialized
        { item with segments := item.segments ++ [segment] }
      <= expectedQueueItemUnmaterializedCreditWeight schema materialized item
          + selectionSetShapeWeight schema
              (scheduleFieldShapeChildSelectionSetShape
                (expectedQueueSegmentShape item.key segment)) := by
  simp [expectedQueueItemUnmaterializedCreditWeight,
    expectedQueueItemChildSelectionSetShapes,
    expectedQueueItemShapeSet_appendSegment]
  simpa using
    selectionSetShapeWeight_unmaterialized_insertScheduleFieldShape_le
      schema materialized
      (expectedQueueSegmentShape item.key segment)
      (expectedQueueItemShapeSet item)

theorem expectedQueueItemOrderedBudget_appendSegment_le
    (schema : Schema) (materialized : MaterializedChildSelections)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemCurrentShapeCount
          { item with segments := item.segments ++ [segment] }
        + expectedQueueItemUnmaterializedCreditWeight schema materialized
            { item with segments := item.segments ++ [segment] }
      <= expectedQueueItemCurrentShapeCount item
          + expectedQueueItemUnmaterializedCreditWeight schema materialized item
          + scheduleFieldShapeStepWeight schema
              (expectedQueueSegmentShape item.key segment) := by
  have hcurrent :=
    expectedQueueItemCurrentShapeCount_appendSegment_le item segment
  have hcredit :=
    expectedQueueItemUnmaterializedCreditWeight_appendSegment_le
      (ObjectRef := ObjectRef) schema materialized item segment
  have hstep :=
    scheduleFieldShape_childWeight_add_one_le_stepWeight schema
      (expectedQueueSegmentShape item.key segment)
  omega

theorem expectedQueueItemShapeWeight_le_raw
    (schema : Schema) (item : ExpectedQueueItem ObjectRef)
    : expectedQueueItemShapeWeight schema item
      <= expectedQueueItemRawShapeWeight schema item := by
  simpa [expectedQueueItemShapeWeight, expectedQueueItemShapeSet,
    expectedQueueItemRawShapeWeight] using
    scheduleFieldShapeSet_weight_le schema (expectedQueueItemShapes item)

theorem expectedScheduleQueueShapeWeight_le_raw (schema : Schema)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueShapeWeight schema queue
        <= expectedScheduleQueueRawShapeWeight schema queue
  | [] => by simp [expectedScheduleQueueShapeWeight,
      expectedScheduleQueueRawShapeWeight]
  | item :: rest => by
      have hitem :=
        expectedQueueItemShapeWeight_le_raw
          (ObjectRef := ObjectRef) schema item
      have hrest :=
        expectedScheduleQueueShapeWeight_le_raw schema rest
      simp [expectedScheduleQueueShapeWeight,
        expectedScheduleQueueRawShapeWeight]
      omega

theorem collectedGroupScheduleShape_weight_le
    (schema : Schema) (parentType responseName : Name)
    (fields : List ExecutableField)
    : fields ≠ []
      -> scheduleFieldShapeStepWeight schema
            (collectedGroupScheduleShape parentType (responseName, fields))
          <= executableFieldsSize fields * (schema.objectTypes.length + 1) := by
  intro hfields
  have hsize :=
    childSelectionSetForFields_size_succ_le_executableFieldsSize fields hfields
  unfold scheduleFieldShapeStepWeight collectedGroupScheduleShape
  exact Nat.mul_le_mul_right (schema.objectTypes.length + 1) hsize

theorem collectedGroupsShapeWeight_le_executableGroupsSize
    (schema : Schema) (parentType : Name)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty groups
      -> collectedGroupsShapeWeight schema parentType groups
          <= executableGroupsSize groups * (schema.objectTypes.length + 1) := by
  intro hnonempty
  induction groups with
  | nil =>
      simp [collectedGroupsShapeWeight, collectedGroupsScheduleShapes,
        scheduleFieldShapeSetWeight, executableGroupsSize]
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hheadNonempty :
          fields ≠ [] :=
        hnonempty responseName fields (by simp)
      have htailNonempty :
          collectedGroupsNonempty groups := by
        intro tailResponseName tailFields htailMem
        exact hnonempty tailResponseName tailFields (by simp [htailMem])
      have hhead :=
        collectedGroupScheduleShape_weight_le schema parentType responseName
          fields hheadNonempty
      have htail := ih htailNonempty
      have htail' :
          scheduleFieldShapeSetWeight schema
              (groups.map (collectedGroupScheduleShape parentType)) <=
            executableGroupsSize groups * (schema.objectTypes.length + 1) := by
        simpa [collectedGroupsShapeWeight, collectedGroupsScheduleShapes] using
          htail
      simp [collectedGroupsShapeWeight, collectedGroupsScheduleShapes,
        scheduleFieldShapeSetWeight, executableGroupsSize]
      rw [Nat.add_mul]
      omega

theorem executableFieldsSize_pos_of_nonempty (fields : List ExecutableField)
    : fields ≠ [] -> 0 < executableFieldsSize fields := by
  intro hfields
  cases fields with
  | nil =>
      exact False.elim (hfields rfl)
  | cons field rest =>
      simp [executableFieldsSize]
      omega

theorem collectedGroups_length_le_executableGroupsSize
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty groups -> groups.length <= executableGroupsSize groups := by
  intro hnonempty
  induction groups with
  | nil =>
      simp [executableGroupsSize]
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hhead : 0 < executableFieldsSize fields :=
        executableFieldsSize_pos_of_nonempty fields
          (hnonempty responseName fields (by simp))
      have htailNonempty : collectedGroupsNonempty groups := by
        intro tailResponseName tailFields htailMem
        exact hnonempty tailResponseName tailFields (by simp [htailMem])
      have htail := ih htailNonempty
      simp [executableGroupsSize]
      omega

theorem scheduleShapesForSelectionSetAtParent_length_le
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (selectionSet : List Selection)
    : (scheduleShapesForSelectionSetAtParent schema variableValues
        parentType selectionSet).length
      <= SelectionSet.size selectionSet := by
  unfold scheduleShapesForSelectionSetAtParent collectedGroupsScheduleShapes
  have hgroupsNonempty :
      collectedGroupsNonempty
        (collectFieldsByKey schema variableValues parentType selectionSet) :=
    collectFieldsByKey_collectedGroupsNonempty schema variableValues
      parentType selectionSet
  have hlength :=
    collectedGroups_length_le_executableGroupsSize
      (collectFieldsByKey schema variableValues parentType selectionSet)
      hgroupsNonempty
  have hsize :=
    collectFieldsByKey_executableGroupsSize_le schema variableValues
      parentType selectionSet
  simp
  exact Nat.le_trans hlength hsize

theorem scheduleShapesForSelectionSetAtParents_length_le
    (schema : Schema) (variableValues : VariableValues)
    (parentTypes : List Name) (selectionSet : List Selection)
    : (scheduleShapesForSelectionSetAtParents schema variableValues
        parentTypes selectionSet).length
      <= parentTypes.length * SelectionSet.size selectionSet := by
  induction parentTypes with
  | nil =>
      simp [scheduleShapesForSelectionSetAtParents]
  | cons parentType rest ih =>
      have hhead :=
        scheduleShapesForSelectionSetAtParent_length_le
          schema variableValues parentType selectionSet
      simp [scheduleShapesForSelectionSetAtParents]
      rw [Nat.add_mul]
      simp
      omega

def ExpectedQueueItem.toScheduleItem (item : ExpectedQueueItem ObjectRef)
    : ScheduleItem ObjectRef :=
  {
    key := item.key
    segments := item.segments.map ExpectedQueueSegment.segment
  }

def expectedScheduleQueueToQueue (queue : ExpectedScheduleQueue ObjectRef)
    : ScheduleQueue ObjectRef :=
  queue.map ExpectedQueueItem.toScheduleItem

def expectedScheduleQueueWithFuel (fuel : Nat) (queue : ScheduleQueue ObjectRef)
    : ExpectedScheduleQueue ObjectRef :=
  queue.map
    (fun item =>
      {
        key := item.key
        segments :=
          item.segments.map
            (fun segment =>
              {
                segment := segment
                specFuels := List.replicate segment.sources.length fuel
              })
      })

@[simp]
theorem expectedQueueSegments_toSegments_withFuel
    (fuel : Nat) (segments : List (ScheduleSegment ObjectRef))
    : List.map
        (ExpectedQueueSegment.segment
          ∘ fun segment =>
              {
                segment := segment
                specFuels := List.replicate segment.sources.length fuel
              })
        segments
      = segments := by
  induction segments with
  | nil =>
      rfl
  | cons segment rest ih =>
      simp [ih]

theorem expectedScheduleQueueWithFuel_fuelsAligned
    (fuel : Nat) (queue : ScheduleQueue ObjectRef)
    : expectedScheduleQueueFuelsAligned
        (expectedScheduleQueueWithFuel (ObjectRef := ObjectRef) fuel queue) := by
  intro item hitem segment hsegment
  simp [expectedScheduleQueueWithFuel] at hitem
  rcases hitem with ⟨runtimeItem, hruntimeItem, rfl⟩
  simp at hsegment
  rcases hsegment with ⟨runtimeSegment, hruntimeSegment, rfl⟩
  simp [expectedQueueSegmentFuelsAligned]

@[simp]
theorem expectedScheduleQueueToQueue_expectedScheduleQueueWithFuel
    (fuel : Nat) (queue : ScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue
        (expectedScheduleQueueWithFuel (ObjectRef := ObjectRef) fuel queue)
      = queue := by
  induction queue with
  | nil =>
      rfl
  | cons item rest ih =>
      cases item
      simp [expectedScheduleQueueWithFuel, expectedScheduleQueueToQueue,
        ExpectedQueueItem.toScheduleItem, expectedQueueSegments_toSegments_withFuel]
      simpa [expectedScheduleQueueToQueue, expectedScheduleQueueWithFuel,
        ExpectedQueueItem.toScheduleItem] using ih

@[simp]
theorem scheduleQueueFieldShape_expectedScheduleQueueToQueue
    (queue : ExpectedScheduleQueue ObjectRef)
    : scheduleQueueFieldShape (expectedScheduleQueueToQueue queue)
      = queue.map
          (fun item =>
            (
              item.key,
              item.segments.map (fun segment => segment.segment.sources.length)
            )) := by
  induction queue with
  | nil =>
      rfl
  | cons item rest ih =>
      cases item
      simp [expectedScheduleQueueToQueue, scheduleQueueFieldShape,
        scheduleItemFieldShape, ScheduleItem.segmentLengths,
        ScheduleSegment.length, ExpectedQueueItem.toScheduleItem]

-----------------------------------------------------------------------------------------
-- Proof-facing queue updates
-----------------------------------------------------------------------------------------

def enqueueExpectedSegment (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ExpectedScheduleQueue ObjectRef -> ExpectedScheduleQueue ObjectRef
  | [] =>
      [{
        key := key
        segments := [segment]
      }]
  | item :: rest =>
      if scheduleKeyEqBool key item.key then
        { item with segments := item.segments ++ [segment] } :: rest
      else
        item :: enqueueExpectedSegment key segment rest

def enqueueExpectedSegments
    (key : ScheduleKey) (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : ExpectedScheduleQueue ObjectRef :=
  segments.foldl (fun queue segment => enqueueExpectedSegment key segment queue) queue

def enqueueExpectedScheduleItems
    (queue : ExpectedScheduleQueue ObjectRef)
    (items : ExpectedScheduleQueue ObjectRef)
    : ExpectedScheduleQueue ObjectRef :=
  items.foldl
    (fun queue item => enqueueExpectedSegments item.key item.segments queue)
    queue

theorem enqueueExpectedSegments_append
    (key : ScheduleKey)
    (left right : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : enqueueExpectedSegments key (left ++ right) queue
      = enqueueExpectedSegments key right (enqueueExpectedSegments key left queue) := by
  induction left generalizing queue with
  | nil =>
      rfl
  | cons segment left ih =>
      simp [enqueueExpectedSegments]

theorem enqueueExpectedScheduleItems_append
    (queue left right : ExpectedScheduleQueue ObjectRef)
    : enqueueExpectedScheduleItems queue (left ++ right)
      = enqueueExpectedScheduleItems (enqueueExpectedScheduleItems queue left) right := by
  induction left generalizing queue with
  | nil =>
      rfl
  | cons item left ih =>
      simp [enqueueExpectedScheduleItems]

theorem expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le
    (schema : Schema) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueShapeWeight schema (enqueueExpectedSegment key segment queue)
      <= expectedScheduleQueueShapeWeight schema queue
          + scheduleFieldShapeStepWeight schema
              (expectedQueueSegmentShape key segment) := by
  induction queue with
  | nil =>
      simp [enqueueExpectedSegment, expectedScheduleQueueShapeWeight,
        expectedQueueItemShapeWeight, expectedQueueItemShapeSet,
        expectedQueueItemShapes, scheduleFieldShapeSet,
        scheduleFieldShapeSetWeight, insertScheduleFieldShape]
  | cons item rest ih =>
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          have hitem :=
            expectedQueueItemShapeWeight_appendSegment_le
              (ObjectRef := ObjectRef) schema item segment
          simp [enqueueExpectedSegment, hkey, expectedScheduleQueueShapeWeight]
          omega
      | false =>
          simp [enqueueExpectedSegment, hkey, expectedScheduleQueueShapeWeight]
          omega

theorem expectedScheduleQueueShapeWeight_enqueueExpectedSegment_head_le_of_shape_mem
    (schema : Schema) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : scheduleKeyEqBool key item.key = true
      -> expectedQueueSegmentShape item.key segment ∈ expectedQueueItemShapeSet item
      -> expectedScheduleQueueShapeWeight schema
            (enqueueExpectedSegment key segment (item :: rest))
          <= expectedScheduleQueueShapeWeight schema (item :: rest) := by
  intro hkey hmem
  have hkeyEq : key = item.key :=
    scheduleKeyEqBool_eq hkey
  subst key
  have hitem :=
    expectedQueueItemShapeWeight_appendSegment_le_of_shape_mem
      (ObjectRef := ObjectRef) schema item segment hmem
  simp [enqueueExpectedSegment, scheduleKeyEqBool_self,
    expectedScheduleQueueShapeWeight]
  omega

theorem expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le_of_existing_shape
    (schema : Schema) (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueKeysDistinct queue
        -> (∃ item,
              item ∈ queue
              ∧ scheduleKeyEqBool key item.key = true
              ∧ expectedQueueSegmentShape item.key segment
                ∈ expectedQueueItemShapeSet item)
        -> expectedScheduleQueueShapeWeight schema
              (enqueueExpectedSegment key segment queue)
            <= expectedScheduleQueueShapeWeight schema queue
  | [], _hdistinct, hwitness => by
      rcases hwitness with ⟨item, hitem, _hkey, _hshape⟩
      simp at hitem
  | item :: rest, hdistinct, hwitness => by
      rcases hdistinct with ⟨habsent, hrestDistinct⟩
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          have hshape :
              expectedQueueSegmentShape item.key segment ∈
                expectedQueueItemShapeSet item := by
            rcases hwitness with ⟨witness, hwitnessMem, hwitnessKey, hwitnessShape⟩
            have hcases : witness = item ∨ witness ∈ rest := by
              simpa using hwitnessMem
            rcases hcases with hwitnessHead | hwitnessTail
            · subst witness
              exact hwitnessShape
            · have hcontra :
                  scheduleKeyEqBool item.key witness.key = false :=
                habsent witness hwitnessTail
              have hwitnessKey' :
                  scheduleKeyEqBool item.key witness.key = true := by
                simpa [expectedQueueSegmentShape] using hwitnessKey
              rw [hwitnessKey'] at hcontra
              simp at hcontra
          exact
            expectedScheduleQueueShapeWeight_enqueueExpectedSegment_head_le_of_shape_mem
              (ObjectRef := ObjectRef) schema item.key segment item rest
              (scheduleKeyEqBool_self item.key) hshape
      | false =>
          have hkeyFalse : scheduleKeyEqBool key item.key = false := by
            simpa using hkey
          have hrestWitness :
              ∃ restItem, restItem ∈ rest ∧
                scheduleKeyEqBool key restItem.key = true ∧
                  expectedQueueSegmentShape restItem.key segment ∈
                    expectedQueueItemShapeSet restItem := by
            rcases hwitness with ⟨witness, hwitnessMem, hwitnessKey, hwitnessShape⟩
            have hcases : witness = item ∨ witness ∈ rest := by
              simpa using hwitnessMem
            rcases hcases with hwitnessHead | hwitnessTail
            · subst witness
              rw [hwitnessKey] at hkeyFalse
              simp at hkeyFalse
            · exact ⟨witness, hwitnessTail, hwitnessKey, hwitnessShape⟩
          have htail :=
            expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le_of_existing_shape
              schema key segment rest hrestDistinct hrestWitness
          simp [enqueueExpectedSegment, hkeyFalse,
            expectedScheduleQueueShapeWeight]
          exact htail

def expectedScheduleQueueContainsShape
    (queue : ExpectedScheduleQueue ObjectRef)
    (shape : ScheduleFieldShape)
    : Prop :=
  ∃ item,
    item ∈ queue
    ∧ scheduleKeyEqBool shape.key item.key = true
    ∧ shape ∈ expectedQueueItemShapeSet item

theorem expectedScheduleQueueContainsShape_enqueueExpectedSegment_self
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueContainsShape
          (enqueueExpectedSegment key segment queue)
          (expectedQueueSegmentShape key segment)
  | [] => by
      refine ⟨{ key := key, segments := [segment] }, ?_, ?_, ?_⟩
      · simp [enqueueExpectedSegment]
      · simp [expectedQueueSegmentShape, scheduleKeyEqBool_self]
      · simp [expectedQueueItemShapeSet, scheduleFieldShapeSet,
          expectedQueueItemShapes, expectedQueueSegmentShape,
          insertScheduleFieldShape]
  | item :: rest => by
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          refine ⟨{ item with segments := item.segments ++ [segment] }, ?_, ?_, ?_⟩
          · simp [enqueueExpectedSegment, scheduleKeyEqBool_self]
          · simp [expectedQueueSegmentShape, scheduleKeyEqBool_self]
          · rw [expectedQueueItemShapeSet_appendSegment]
            exact scheduleFieldShape_mem_insert_self
              (expectedQueueSegmentShape item.key segment)
              (expectedQueueItemShapeSet item)
      | false =>
          rcases expectedScheduleQueueContainsShape_enqueueExpectedSegment_self
              key segment rest with
            ⟨witness, hwitnessMem, hwitnessKey, hwitnessShape⟩
          exact ⟨witness,
            by simp [enqueueExpectedSegment, hkey, hwitnessMem],
            hwitnessKey, hwitnessShape⟩

theorem expectedScheduleQueueContainsShape_enqueueExpectedSegment_of_contains
    (shape : ScheduleFieldShape) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueContainsShape queue shape
        -> expectedScheduleQueueContainsShape
            (enqueueExpectedSegment key segment queue) shape
  | [], hcontains => by
      rcases hcontains with ⟨item, hitem, _hkey, _hshape⟩
      simp at hitem
  | item :: rest, hcontains => by
      cases henqueue : scheduleKeyEqBool key item.key with
      | true =>
          rcases hcontains with ⟨witness, hwitnessMem, hwitnessKey, hwitnessShape⟩
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq henqueue
          subst key
          have hcases : witness = item ∨ witness ∈ rest := by
            simpa using hwitnessMem
          rcases hcases with hwitnessHead | hwitnessTail
          · subst witness
            refine ⟨{ item with segments := item.segments ++ [segment] }, ?_, ?_, ?_⟩
            · simp [enqueueExpectedSegment, scheduleKeyEqBool_self]
            · simpa using hwitnessKey
            · rw [expectedQueueItemShapeSet_appendSegment]
              exact scheduleFieldShape_mem_insert_of_mem
                (expectedQueueSegmentShape item.key segment) shape
                (expectedQueueItemShapeSet item) hwitnessShape
          · exact ⟨witness,
              by simp [enqueueExpectedSegment, scheduleKeyEqBool_self, hwitnessTail],
              hwitnessKey, hwitnessShape⟩
      | false =>
          rcases hcontains with ⟨witness, hwitnessMem, hwitnessKey, hwitnessShape⟩
          have hcases : witness = item ∨ witness ∈ rest := by
            simpa using hwitnessMem
          rcases hcases with hwitnessHead | hwitnessTail
          · subst witness
            exact ⟨item, by simp [enqueueExpectedSegment, henqueue],
              hwitnessKey, hwitnessShape⟩
          · have htail :
                expectedScheduleQueueContainsShape
                  (enqueueExpectedSegment key segment rest) shape :=
              expectedScheduleQueueContainsShape_enqueueExpectedSegment_of_contains
                shape key segment rest
                ⟨witness, hwitnessTail, hwitnessKey, hwitnessShape⟩
            rcases htail with ⟨tailWitness, htailMem, htailKey, htailShape⟩
            exact ⟨tailWitness,
              by simp [enqueueExpectedSegment, henqueue, htailMem],
              htailKey, htailShape⟩

theorem expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le_of_contains_shape
    (schema : Schema) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueContainsShape queue (expectedQueueSegmentShape key segment)
      -> expectedScheduleQueueShapeWeight schema
            (enqueueExpectedSegment key segment queue)
          <= expectedScheduleQueueShapeWeight schema queue := by
  intro hdistinct hcontains
  exact expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le_of_existing_shape
    (ObjectRef := ObjectRef) schema key segment queue hdistinct
    (by
      rcases hcontains with ⟨item, hitem, hkey, hshape⟩
      have hkeyEq : key = item.key :=
        scheduleKeyEqBool_eq hkey
      subst key
      exact ⟨item, hitem, scheduleKeyEqBool_self item.key, hshape⟩)

theorem expectedScheduleQueueShapeWeight_enqueueExpectedSegments_le
    (schema : Schema) (key : ScheduleKey)
    (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueShapeWeight schema (enqueueExpectedSegments key segments queue)
      <= expectedScheduleQueueShapeWeight schema queue
          + scheduleFieldShapeSetWeight schema
              (segments.map (expectedQueueSegmentShape key)) := by
  induction segments generalizing queue with
  | nil =>
      simp [enqueueExpectedSegments, scheduleFieldShapeSetWeight]
  | cons segment segments ih =>
      have hhead :=
        expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema key segment queue
      have htail :=
        ih (enqueueExpectedSegment key segment queue)
      simp [enqueueExpectedSegments, scheduleFieldShapeSetWeight] at htail ⊢
      omega

theorem expectedScheduleQueueRawShapeWeight_enqueueExpectedSegment_le
    (schema : Schema) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRawShapeWeight schema
        (enqueueExpectedSegment key segment queue)
      <= expectedScheduleQueueRawShapeWeight schema queue
          + scheduleFieldShapeStepWeight schema
              (expectedQueueSegmentShape key segment) := by
  induction queue with
  | nil =>
      simp [enqueueExpectedSegment, expectedScheduleQueueRawShapeWeight,
        expectedQueueItemRawShapeWeight, expectedQueueItemShapes,
        scheduleFieldShapeSetWeight]
  | cons item rest ih =>
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          simp [enqueueExpectedSegment, hkey, expectedScheduleQueueRawShapeWeight,
            expectedQueueItemRawShapeWeight, expectedQueueItemShapes,
            scheduleFieldShapeSetWeight_append, scheduleFieldShapeSetWeight]
          omega
      | false =>
          simp [enqueueExpectedSegment, hkey, expectedScheduleQueueRawShapeWeight]
          omega

theorem expectedScheduleQueueRawShapeWeight_enqueueExpectedSegments_le
    (schema : Schema) (key : ScheduleKey)
    (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRawShapeWeight schema
        (enqueueExpectedSegments key segments queue)
      <= expectedScheduleQueueRawShapeWeight schema queue
          + scheduleFieldShapeSetWeight schema
              (segments.map (expectedQueueSegmentShape key)) := by
  induction segments generalizing queue with
  | nil =>
      simp [enqueueExpectedSegments, scheduleFieldShapeSetWeight]
  | cons segment segments ih =>
      have hhead :=
        expectedScheduleQueueRawShapeWeight_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema key segment queue
      have htail :=
        ih (enqueueExpectedSegment key segment queue)
      simp [enqueueExpectedSegments, scheduleFieldShapeSetWeight] at htail ⊢
      omega

theorem expectedScheduleQueueRawShapeWeight_enqueueExpectedScheduleItems_le
    (schema : Schema)
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRawShapeWeight schema
        (enqueueExpectedScheduleItems queue items)
      <= expectedScheduleQueueRawShapeWeight schema queue
          + expectedScheduleQueueRawShapeWeight schema items := by
  induction items generalizing queue with
  | nil =>
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRawShapeWeight]
  | cons item rest ih =>
      have hhead :=
        expectedScheduleQueueRawShapeWeight_enqueueExpectedSegments_le
          (ObjectRef := ObjectRef) schema item.key item.segments queue
      have htail :=
        ih (enqueueExpectedSegments item.key item.segments queue)
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRawShapeWeight,
        expectedQueueItemRawShapeWeight, expectedQueueItemShapes] at htail ⊢
      omega

theorem expectedScheduleQueueShapeWeight_enqueueExpectedScheduleItems_le
    (schema : Schema)
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueShapeWeight schema (enqueueExpectedScheduleItems queue items)
      <= expectedScheduleQueueShapeWeight schema queue
          + expectedScheduleQueueRawShapeWeight schema items := by
  induction items generalizing queue with
  | nil =>
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRawShapeWeight]
  | cons item rest ih =>
      have hhead :=
        expectedScheduleQueueShapeWeight_enqueueExpectedSegments_le
          (ObjectRef := ObjectRef) schema item.key item.segments queue
      have htail :=
        ih (enqueueExpectedSegments item.key item.segments queue)
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRawShapeWeight,
        expectedQueueItemRawShapeWeight, expectedQueueItemShapes] at htail ⊢
      omega

theorem expectedScheduleQueueDrainBudget_enqueueExpectedScheduleItems_le
    (schema : Schema) (materialized : MaterializedChildSelections)
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueDrainBudget schema materialized
        (enqueueExpectedScheduleItems queue items)
      <= expectedScheduleQueueShapeWeight schema queue
          + expectedScheduleQueueRawShapeWeight schema items := by
  exact Nat.le_trans
    (expectedScheduleQueueDrainBudget_le_shapeWeight
      (ObjectRef := ObjectRef) schema materialized
      (enqueueExpectedScheduleItems queue items))
    (expectedScheduleQueueShapeWeight_enqueueExpectedScheduleItems_le
      (ObjectRef := ObjectRef) schema queue items)

theorem expectedScheduleQueueDrainBudget_enqueueExpectedSegment_le
    (schema : Schema) (materialized : MaterializedChildSelections)
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueDrainBudget schema materialized
          (enqueueExpectedSegment key segment queue)
        <= expectedScheduleQueueDrainBudget schema materialized queue
            + scheduleFieldShapeStepWeight schema (expectedQueueSegmentShape key segment)
  | [] => by
      let emptyItem : ExpectedQueueItem ObjectRef :=
        { key := key, segments := [] }
      have hempty :
          expectedQueueItemCurrentShapeCount emptyItem
              + expectedQueueItemUnmaterializedCreditWeight schema materialized
                emptyItem = 0 := by
        simp [emptyItem, expectedQueueItemCurrentShapeCount,
          expectedQueueItemUnmaterializedCreditWeight,
          expectedQueueItemChildSelectionSetShapes,
          expectedQueueItemShapeSet, expectedQueueItemShapes,
          scheduleFieldShapeSet, unmaterializedChildSelectionSetShapes,
          selectionSetShapeSetWeight]
      have hitem :=
        expectedQueueItemOrderedBudget_appendSegment_le
          (ObjectRef := ObjectRef) schema materialized emptyItem segment
      have hsingleton :
          expectedQueueItemCurrentShapeCount
              ({ key := key, segments := [segment] } :
                ExpectedQueueItem ObjectRef)
              + expectedQueueItemUnmaterializedCreditWeight schema materialized
                ({ key := key, segments := [segment] } :
                  ExpectedQueueItem ObjectRef) <=
            scheduleFieldShapeStepWeight schema
              (expectedQueueSegmentShape key segment) := by
        simp [emptyItem] at hempty
        simp [emptyItem] at hitem
        omega
      simpa [enqueueExpectedSegment, expectedScheduleQueueDrainBudget] using
        hsingleton
  | item :: rest => by
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          have hitem :=
            expectedQueueItemOrderedBudget_appendSegment_le
              (ObjectRef := ObjectRef) schema materialized item segment
          have htail :
              expectedScheduleQueueDrainBudget schema
                  (materializeExpectedQueueItem
                    { item with segments := item.segments ++ [segment] }
                    materialized)
                  rest <=
                expectedScheduleQueueDrainBudget schema
                  (materializeExpectedQueueItem item materialized)
                  rest :=
            expectedScheduleQueueDrainBudget_mono
              (ObjectRef := ObjectRef) schema rest
              (materializeExpectedQueueItem_appendSegment_extends
                (ObjectRef := ObjectRef) item segment materialized)
          simp [enqueueExpectedSegment, hkey, expectedScheduleQueueDrainBudget]
          omega
      | false =>
          have htail :=
            expectedScheduleQueueDrainBudget_enqueueExpectedSegment_le
              schema (materializeExpectedQueueItem item materialized)
              key segment rest
          simp [enqueueExpectedSegment, hkey, expectedScheduleQueueDrainBudget]
          omega

theorem expectedScheduleQueueDrainBudget_enqueueExpectedSegments_ordered_le
    (schema : Schema) (materialized : MaterializedChildSelections)
    (key : ScheduleKey)
    : ∀ (segments : List (ExpectedQueueSegment ObjectRef))
        (queue : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueDrainBudget schema materialized
          (enqueueExpectedSegments key segments queue)
        <= expectedScheduleQueueDrainBudget schema materialized queue
            + scheduleFieldShapeSetWeight schema
                (segments.map (expectedQueueSegmentShape key))
  | [], queue => by
      simp [enqueueExpectedSegments, scheduleFieldShapeSetWeight]
  | segment :: segments, queue => by
      have hhead :=
        expectedScheduleQueueDrainBudget_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema materialized key segment queue
      have htail :=
        expectedScheduleQueueDrainBudget_enqueueExpectedSegments_ordered_le
          schema materialized key segments
          (enqueueExpectedSegment key segment queue)
      simp [enqueueExpectedSegments, scheduleFieldShapeSetWeight] at htail ⊢
      omega

theorem expectedScheduleQueueDrainBudget_enqueueExpectedScheduleItems_ordered_le
    (schema : Schema) (materialized : MaterializedChildSelections)
    : ∀ (queue items : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueDrainBudget schema materialized
          (enqueueExpectedScheduleItems queue items)
        <= expectedScheduleQueueDrainBudget schema materialized queue
            + expectedScheduleQueueRawShapeWeight schema items
  | queue, [] => by
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRawShapeWeight]
  | queue, item :: rest => by
      have hhead :=
        expectedScheduleQueueDrainBudget_enqueueExpectedSegments_ordered_le
          (ObjectRef := ObjectRef) schema materialized item.key item.segments queue
      have htail :=
        expectedScheduleQueueDrainBudget_enqueueExpectedScheduleItems_ordered_le
          schema materialized
          (enqueueExpectedSegments item.key item.segments queue) rest
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRawShapeWeight,
        expectedQueueItemRawShapeWeight, expectedQueueItemShapes] at htail ⊢
      omega

theorem enqueueExpectedSegment_fuelsAligned
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueSegmentFuelsAligned segment
      -> expectedScheduleQueueFuelsAligned queue
      -> expectedScheduleQueueFuelsAligned
          (enqueueExpectedSegment key segment queue) := by
  intro hsegmentAligned hqueue
  induction queue with
  | nil =>
      intro item hitem itemSegment hitemSegment
      simp [enqueueExpectedSegment] at hitem
      subst item
      simp at hitemSegment
      subst itemSegment
      exact hsegmentAligned
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · intro candidate hcandidate candidateSegment hcandidateSegment
        simp [enqueueExpectedSegment, hkey] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          simp at hcandidateSegment
          rcases hcandidateSegment with hcandidateSegment | hcandidateSegment
          · exact hqueue item (by simp) candidateSegment hcandidateSegment
          · subst candidateSegment
            exact hsegmentAligned
        · exact hqueue candidate (by simp [hcandidate]) candidateSegment
            hcandidateSegment
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have hrest :
            expectedScheduleQueueFuelsAligned rest := by
          intro restItem hrestItem
          exact hqueue restItem (by simp [hrestItem])
        have ihRest := ih hrest
        intro candidate hcandidate candidateSegment hcandidateSegment
        simp [enqueueExpectedSegment, hkeyFalse] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hqueue item (by simp) candidateSegment hcandidateSegment
        · exact ihRest candidate hcandidate candidateSegment hcandidateSegment

theorem enqueueExpectedSegment_itemsNonempty
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty queue
      -> expectedScheduleQueueItemsNonempty
          (enqueueExpectedSegment key segment queue) := by
  intro hqueue
  induction queue with
  | nil =>
      intro item hitem
      simp [enqueueExpectedSegment] at hitem
      subst item
      simp
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · intro candidate hcandidate
        simp [enqueueExpectedSegment, hkey] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          intro hsegments
          apply hqueue item (by simp)
          cases item with
          | mk itemKey itemSegments =>
              cases itemSegments with
              | nil =>
                  simp at hsegments
              | cons head tail =>
                  simp at hsegments
        · exact hqueue candidate (by simp [hcandidate])
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have hrest :
            expectedScheduleQueueItemsNonempty rest := by
          intro restItem hrestItem
          exact hqueue restItem (by simp [hrestItem])
        have ihRest := ih hrest
        intro candidate hcandidate
        simp [enqueueExpectedSegment, hkeyFalse] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hqueue item (by simp)
        · exact ihRest candidate hcandidate

theorem enqueueExpectedSegment_absent
    (absentKey key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : scheduleKeyAbsentFromExpectedQueue absentKey queue
      -> scheduleKeyEqBool absentKey key = false
      -> scheduleKeyAbsentFromExpectedQueue absentKey
          (enqueueExpectedSegment key segment queue) := by
  intro hqueue hneq
  induction queue with
  | nil =>
      intro item hitem
      simp [enqueueExpectedSegment] at hitem ⊢
      subst item
      exact hneq
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · intro candidate hcandidate
        simp [enqueueExpectedSegment, hkey] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          have hitemEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          exact hneq
        · exact hqueue candidate (by simp [hcandidate])
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have hrest :
            scheduleKeyAbsentFromExpectedQueue absentKey rest := by
          intro restItem hrestItem
          exact hqueue restItem (by simp [hrestItem])
        have ihRest := ih hrest
        intro candidate hcandidate
        simp [enqueueExpectedSegment, hkeyFalse] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hqueue item (by simp)
        · exact ihRest candidate hcandidate

theorem enqueueExpectedSegment_keysDistinct
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueKeysDistinct
          (enqueueExpectedSegment key segment queue) := by
  intro hqueue
  induction queue with
  | nil =>
      simp [enqueueExpectedSegment, expectedScheduleQueueKeysDistinct,
        scheduleKeyAbsentFromExpectedQueue]
  | cons item rest ih =>
      rcases hqueue with ⟨habsent, hrestDistinct⟩
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · simp [enqueueExpectedSegment, expectedScheduleQueueKeysDistinct, hkey,
          hrestDistinct, habsent]
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have hrestAbsent :
            scheduleKeyAbsentFromExpectedQueue item.key rest := by
          intro restItem hrestItem
          exact habsent restItem (by simp [hrestItem])
        have hitemKeyNe :
            scheduleKeyEqBool item.key key = false :=
          scheduleKeyEqBool_false_symm hkeyFalse
        have hheadAbsent :
            scheduleKeyAbsentFromExpectedQueue item.key
              (enqueueExpectedSegment key segment rest) :=
          enqueueExpectedSegment_absent item.key key segment rest
            hrestAbsent hitemKeyNe
        have htailDistinct :
            expectedScheduleQueueKeysDistinct
              (enqueueExpectedSegment key segment rest) :=
          ih hrestDistinct
        simpa [enqueueExpectedSegment, expectedScheduleQueueKeysDistinct, hkeyFalse]
          using And.intro hheadAbsent htailDistinct

theorem enqueueExpectedSegments_fuelsAligned
    (key : ScheduleKey) (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : (∀ segment, segment ∈ segments -> expectedQueueSegmentFuelsAligned segment)
      -> expectedScheduleQueueFuelsAligned queue
      -> expectedScheduleQueueFuelsAligned
          (enqueueExpectedSegments key segments queue) := by
  intro hsegments hqueue
  induction segments generalizing queue with
  | nil =>
      simpa [enqueueExpectedSegments] using hqueue
  | cons segment rest ih =>
      have hhead : expectedQueueSegmentFuelsAligned segment :=
        hsegments segment (by simp)
      have htail :
          ∀ restSegment, restSegment ∈ rest ->
            expectedQueueSegmentFuelsAligned restSegment := by
        intro restSegment hrestSegment
        exact hsegments restSegment (by simp [hrestSegment])
      exact ih _ htail
        (enqueueExpectedSegment_fuelsAligned key segment queue hhead hqueue)

theorem enqueueExpectedSegments_itemsNonempty
    (key : ScheduleKey) (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty queue
      -> expectedScheduleQueueItemsNonempty
          (enqueueExpectedSegments key segments queue) := by
  intro hqueue
  induction segments generalizing queue with
  | nil =>
      simpa [enqueueExpectedSegments] using hqueue
  | cons segment rest ih =>
      exact ih _
        (enqueueExpectedSegment_itemsNonempty key segment queue hqueue)

theorem enqueueExpectedSegments_keysDistinct
    (key : ScheduleKey) (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueKeysDistinct
          (enqueueExpectedSegments key segments queue) := by
  intro hqueue
  induction segments generalizing queue with
  | nil =>
      simpa [enqueueExpectedSegments] using hqueue
  | cons segment rest ih =>
      exact ih _
        (enqueueExpectedSegment_keysDistinct key segment queue hqueue)

theorem enqueueExpectedScheduleItems_fuelsAligned
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueFuelsAligned items
      -> expectedScheduleQueueFuelsAligned queue
      -> expectedScheduleQueueFuelsAligned
          (enqueueExpectedScheduleItems queue items) := by
  intro hitems hqueue
  induction items generalizing queue with
  | nil =>
      simpa [enqueueExpectedScheduleItems] using hqueue
  | cons item rest ih =>
      have hitem :
          ∀ segment, segment ∈ item.segments ->
            expectedQueueSegmentFuelsAligned segment :=
        hitems item (by simp)
      have hrest :
          expectedScheduleQueueFuelsAligned rest := by
        intro restItem hrestItem
        exact hitems restItem (by simp [hrestItem])
      exact ih _ hrest
        (enqueueExpectedSegments_fuelsAligned item.key item.segments queue
          hitem hqueue)

theorem enqueueExpectedScheduleItems_itemsNonempty
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty queue
      -> expectedScheduleQueueItemsNonempty items
      -> expectedScheduleQueueItemsNonempty
          (enqueueExpectedScheduleItems queue items) := by
  intro hqueue hitems
  induction items generalizing queue with
  | nil =>
      simpa [enqueueExpectedScheduleItems] using hqueue
  | cons item rest ih =>
      have hrest :
          expectedScheduleQueueItemsNonempty rest := by
        intro restItem hrestItem
        exact hitems restItem (by simp [hrestItem])
      exact ih _
        (enqueueExpectedSegments_itemsNonempty item.key item.segments queue hqueue)
        hrest

theorem enqueueExpectedScheduleItems_keysDistinct
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueKeysDistinct items
      -> expectedScheduleQueueKeysDistinct
          (enqueueExpectedScheduleItems queue items) := by
  intro hqueue hitems
  induction items generalizing queue with
  | nil =>
      simpa [enqueueExpectedScheduleItems] using hqueue
  | cons item rest ih =>
      have hrest :
          expectedScheduleQueueKeysDistinct rest := by
        exact hitems.2
      exact ih _
        (enqueueExpectedSegments_keysDistinct item.key item.segments queue hqueue)
        hrest

theorem enqueueExpectedSegment_fieldBudgetReady
    (schema : Schema) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueSegmentFieldBudgetReady schema segment
      -> expectedScheduleQueueFieldBudgetReady schema queue
      -> expectedScheduleQueueFieldBudgetReady schema
          (enqueueExpectedSegment key segment queue) := by
  intro hsegment hqueue
  induction queue with
  | nil =>
      intro item hitem itemSegment hitemSegment
      simp [enqueueExpectedSegment] at hitem
      subst item
      simp at hitemSegment
      subst itemSegment
      exact hsegment
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · intro candidate hcandidate candidateSegment hcandidateSegment
        simp [enqueueExpectedSegment, hkey] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          simp at hcandidateSegment
          rcases hcandidateSegment with hcandidateSegment | hcandidateSegment
          · exact hqueue item (by simp) candidateSegment hcandidateSegment
          · subst candidateSegment
            exact hsegment
        · exact hqueue candidate (by simp [hcandidate]) candidateSegment
            hcandidateSegment
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have hrest :
            expectedScheduleQueueFieldBudgetReady schema rest := by
          intro restItem hrestItem
          exact hqueue restItem (by simp [hrestItem])
        have ihRest := ih hrest
        intro candidate hcandidate candidateSegment hcandidateSegment
        simp [enqueueExpectedSegment, hkeyFalse] at hcandidate
        rcases hcandidate with hcandidate | hcandidate
        · subst candidate
          exact hqueue item (by simp) candidateSegment hcandidateSegment
        · exact ihRest candidate hcandidate candidateSegment hcandidateSegment

theorem enqueueExpectedSegments_fieldBudgetReady
    (schema : Schema) (key : ScheduleKey)
    (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : (∀ segment,
        segment ∈ segments -> expectedQueueSegmentFieldBudgetReady schema segment)
      -> expectedScheduleQueueFieldBudgetReady schema queue
      -> expectedScheduleQueueFieldBudgetReady schema
          (enqueueExpectedSegments key segments queue) := by
  intro hsegments hqueue
  induction segments generalizing queue with
  | nil =>
      simpa [enqueueExpectedSegments] using hqueue
  | cons segment rest ih =>
      have hhead : expectedQueueSegmentFieldBudgetReady schema segment :=
        hsegments segment (by simp)
      have htail :
          ∀ restSegment, restSegment ∈ rest ->
            expectedQueueSegmentFieldBudgetReady schema restSegment := by
        intro restSegment hrestSegment
        exact hsegments restSegment (by simp [hrestSegment])
      exact ih _ htail
        (enqueueExpectedSegment_fieldBudgetReady
          schema key segment queue hhead hqueue)

theorem enqueueExpectedScheduleItems_fieldBudgetReady
    (schema : Schema) (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueFieldBudgetReady schema items
      -> expectedScheduleQueueFieldBudgetReady schema queue
      -> expectedScheduleQueueFieldBudgetReady schema
          (enqueueExpectedScheduleItems queue items) := by
  intro hitems hqueue
  induction items generalizing queue with
  | nil =>
      simpa [enqueueExpectedScheduleItems] using hqueue
  | cons item rest ih =>
      have hitem :
          ∀ segment, segment ∈ item.segments ->
            expectedQueueSegmentFieldBudgetReady schema segment :=
        hitems item (by simp)
      have hrest :
          expectedScheduleQueueFieldBudgetReady schema rest := by
        intro restItem hrestItem
        exact hitems restItem (by simp [hrestItem])
      exact ih _ hrest
        (enqueueExpectedSegments_fieldBudgetReady
          schema item.key item.segments queue hitem hqueue)

theorem expectedScheduleQueueToQueue_enqueueExpectedSegment
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue (enqueueExpectedSegment key segment queue)
      = enqueueSegment key segment.segment (expectedScheduleQueueToQueue queue) := by
  induction queue with
  | nil =>
      rfl
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · simp [enqueueExpectedSegment, enqueueSegment,
          expectedScheduleQueueToQueue, ExpectedQueueItem.toScheduleItem, hkey]
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        simpa [enqueueExpectedSegment, enqueueSegment,
          expectedScheduleQueueToQueue, ExpectedQueueItem.toScheduleItem,
          hkeyFalse] using ih

theorem expectedScheduleQueueToQueue_enqueueExpectedSegments
    (key : ScheduleKey) (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue (enqueueExpectedSegments key segments queue)
      = (segments.map ExpectedQueueSegment.segment).foldl
          (fun queue segment => enqueueSegment key segment queue)
          (expectedScheduleQueueToQueue queue) := by
  induction segments generalizing queue with
  | nil =>
      rfl
  | cons segment rest ih =>
      calc
        expectedScheduleQueueToQueue
              (enqueueExpectedSegments key rest
                (enqueueExpectedSegment key segment queue))
            = (rest.map ExpectedQueueSegment.segment).foldl
                (fun queue segment => enqueueSegment key segment queue)
                (expectedScheduleQueueToQueue
                  (enqueueExpectedSegment key segment queue)) :=
          ih _
        _ = (rest.map ExpectedQueueSegment.segment).foldl
              (fun queue segment => enqueueSegment key segment queue)
              (enqueueSegment key segment.segment
                (expectedScheduleQueueToQueue queue)) := by
          rw [expectedScheduleQueueToQueue_enqueueExpectedSegment]
        _ = ((segment :: rest).map ExpectedQueueSegment.segment).foldl
              (fun queue segment => enqueueSegment key segment queue)
              (expectedScheduleQueueToQueue queue) := by
          rfl

theorem expectedScheduleQueueToQueue_enqueueExpectedScheduleItems
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue (enqueueExpectedScheduleItems queue items)
      = enqueueScheduleItems (expectedScheduleQueueToQueue queue)
          (expectedScheduleQueueToQueue items) := by
  induction items generalizing queue with
  | nil =>
      rfl
  | cons item rest ih =>
      calc
        expectedScheduleQueueToQueue
              (enqueueExpectedScheduleItems
                (enqueueExpectedSegments item.key item.segments queue)
                rest)
            = enqueueScheduleItems
                (expectedScheduleQueueToQueue
                  (enqueueExpectedSegments item.key item.segments queue))
                (expectedScheduleQueueToQueue rest) :=
          ih _
        _ = enqueueScheduleItems
              ((item.segments.map ExpectedQueueSegment.segment).foldl
                (fun queue segment => enqueueSegment item.key segment queue)
                (expectedScheduleQueueToQueue queue))
              (expectedScheduleQueueToQueue rest) := by
          rw [expectedScheduleQueueToQueue_enqueueExpectedSegments]
        _ = enqueueScheduleItems
              (expectedScheduleQueueToQueue queue)
              (item.toScheduleItem :: expectedScheduleQueueToQueue rest) := by
          simp [enqueueScheduleItems, ExpectedQueueItem.toScheduleItem]
        _ = enqueueScheduleItems
              (expectedScheduleQueueToQueue queue)
              (expectedScheduleQueueToQueue (item :: rest)) := by
          rfl

-----------------------------------------------------------------------------------------
-- Proof-facing completion stack for the queue
-----------------------------------------------------------------------------------------

def expectedScheduleSegmentSpecFieldResultsWithFuels
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (childSelectionSet : List Selection)
    : List (ResolverValue ObjectRef) -> List Nat -> List (Result ResponseValue)
  | [], _fuels => []
  | _source :: _sources, [] => []
  | source :: sources, fuel :: fuels =>
      singleFieldResultValue key.responseName
        (GraphQL.Execution.executeField schema resolvers variableValues fuel source
          key.responseName [key.executableField childSelectionSet])
      :: expectedScheduleSegmentSpecFieldResultsWithFuels schema resolvers
          variableValues key childSelectionSet sources fuels

def expectedScheduleSegmentSpecFieldResults
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    : List (Result ResponseValue) :=
  expectedScheduleSegmentSpecFieldResultsWithFuels schema resolvers
    variableValues key segment.segment.childSelectionSet segment.segment.sources
    segment.specFuels

@[simp]
theorem expectedScheduleSegmentSpecFieldResultsWithFuels_replicate
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (key : ScheduleKey)
    (childSelectionSet : List Selection)
    (sources : List (ResolverValue ObjectRef))
    : expectedScheduleSegmentSpecFieldResultsWithFuels schema resolvers
        variableValues key childSelectionSet sources
        (List.replicate sources.length fuel)
      = sources.map
          (fun source =>
            singleFieldResultValue key.responseName
              (GraphQL.Execution.executeField schema resolvers variableValues fuel
                source key.responseName [key.executableField childSelectionSet])) := by
  induction sources with
  | nil =>
      rfl
  | cons source sources ih =>
      change
        expectedScheduleSegmentSpecFieldResultsWithFuels schema resolvers
            variableValues key childSelectionSet (source :: sources)
            (List.replicate (sources.length + 1) fuel) =
          singleFieldResultValue key.responseName
            (GraphQL.Execution.executeField schema resolvers variableValues fuel source
                key.responseName [key.executableField childSelectionSet]) ::
            sources.map (fun source =>
              singleFieldResultValue key.responseName
                (GraphQL.Execution.executeField schema resolvers variableValues fuel
                  source key.responseName [key.executableField childSelectionSet]))
      rw [show List.replicate (sources.length + 1) fuel =
          fuel :: List.replicate sources.length fuel by
        rw [show sources.length + 1 = Nat.succ sources.length by omega]
        rfl]
      simp [expectedScheduleSegmentSpecFieldResultsWithFuels, ih]

@[simp]
theorem expectedScheduleSegmentSpecFieldResults_withFuel
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (key : ScheduleKey)
    (segment : ScheduleSegment ObjectRef)
    : expectedScheduleSegmentSpecFieldResults schema resolvers variableValues key
        {
          segment := segment
          specFuels := List.replicate segment.sources.length fuel
        }
      = scheduleSegmentSpecFieldResults schema resolvers variableValues fuel key
          segment := by
  cases segment
  simp [expectedScheduleSegmentSpecFieldResults,
    scheduleSegmentSpecFieldResults]

def expectedQueueItemCompletion
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : ScheduleKey × ResponseValueSegments :=
  (
    item.key,
    (item.segments.map
      (fun segment =>
        expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
          item.key segment)).reverse
  )

def expectedScheduleQueueCompletionStack
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (queue : ExpectedScheduleQueue ObjectRef)
    : CompletionStack :=
  {
    valueStack := []
    fieldStore := queue.map (expectedQueueItemCompletion schema resolvers variableValues)
  }

theorem expectedScheduleQueueCompletionStack_withFuel
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (queue : ScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (expectedScheduleQueueWithFuel (ObjectRef := ObjectRef) fuel queue)
      = scheduleQueueSpecFieldCompletionStack schema resolvers variableValues
          fuel queue := by
  induction queue with
  | nil =>
      rfl
  | cons item rest ih =>
      simp [expectedScheduleQueueCompletionStack, expectedScheduleQueueWithFuel,
        expectedQueueItemCompletion, scheduleQueueSpecFieldCompletionStack,
        scheduleItemSpecFieldCompletion, scheduleItemSpecFieldSegments,
        Function.comp_def]

theorem expectedScheduleQueueToQueue_withFuel
    (fuel : Nat) (queue : ScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue
        (expectedScheduleQueueWithFuel (ObjectRef := ObjectRef) fuel queue)
      = queue := by
  exact expectedScheduleQueueToQueue_expectedScheduleQueueWithFuel
    (ObjectRef := ObjectRef) fuel queue

theorem expectedScheduleQueueToQueue_append (left right : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue (left ++ right)
      = expectedScheduleQueueToQueue left ++ expectedScheduleQueueToQueue right := by
  simp [expectedScheduleQueueToQueue, List.map_append]

theorem expectedScheduleQueueCompletionStack_append
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (left right : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues (left ++ right)
      = {
        valueStack := []
        fieldStore :=
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            left).fieldStore
          ++ (expectedScheduleQueueCompletionStack schema resolvers variableValues
                right).fieldStore
      } := by
  simp [expectedScheduleQueueCompletionStack, List.map_append]

def pushExpectedFieldSegmentInStore
    (key : ScheduleKey)
    (segmentResults : List (Result ResponseValue))
    : FieldStore -> FieldStore
  | [] =>
      [(key, [segmentResults])]
  | (itemKey, segments) :: store =>
      if scheduleKeyEqBool key itemKey then
        (itemKey, segmentResults :: segments) :: store
      else
        (itemKey, segments) :: pushExpectedFieldSegmentInStore key segmentResults store

def pushExpectedFieldSegment
    (key : ScheduleKey)
    (segmentResults : List (Result ResponseValue))
    (stack : CompletionStack)
    : CompletionStack :=
  {
    stack with
      fieldStore := pushExpectedFieldSegmentInStore key segmentResults stack.fieldStore
  }

def fieldStoreSegmentsNonempty : FieldStore -> Prop
  | [] => True
  | (_key, segments) :: store =>
      segments ≠ [] ∧ fieldStoreSegmentsNonempty store

def completionStackFieldSegmentsNonempty (stack : CompletionStack) : Prop :=
  fieldStoreSegmentsNonempty stack.fieldStore

-----------------------------------------------------------------------------------------
-- Proof-facing child work
-----------------------------------------------------------------------------------------

/--
Proof-facing child work. Runtime `PendingChildWork` already carries exactly one child
source, so the proof layer only adds the spec fuel that should be used when completing
that child scope on the spec side.
-/
structure ExpectedPendingChildWork (ObjectRef : Type) where
  work : PendingChildWork ObjectRef
  specFuel : Nat
deriving Repr

abbrev ExpectedPendingChildWorkList (ObjectRef : Type) :=
  List (ExpectedPendingChildWork ObjectRef)

def expectedPendingChildWorkScopeBudgetReady
    (schema : Schema) (work : ExpectedPendingChildWorkList ObjectRef)
    : Prop :=
  ∀ childWork,
    childWork ∈ work
    -> specFuelScopeBudget schema childWork.work.selectionSet childWork.specFuel

structure PendingScopeShape where
  runtimeType : Name
  selectionSet : List Selection
deriving Repr

def pendingScopeShapeEqBool (left right : PendingScopeShape) : Bool :=
  (left.runtimeType == right.runtimeType)
  && selectionSetEqBool left.selectionSet right.selectionSet

theorem pendingScopeShapeEqBool_self (shape : PendingScopeShape)
    : pendingScopeShapeEqBool shape shape = true := by
  cases shape with
  | mk runtimeType selectionSet =>
      simp [pendingScopeShapeEqBool, selectionSetEqBool_self]

theorem pendingScopeShapeEqBool_eq {left right : PendingScopeShape}
    : pendingScopeShapeEqBool left right = true -> left = right := by
  cases left with
  | mk leftRuntimeType leftSelectionSet =>
      cases right with
      | mk rightRuntimeType rightSelectionSet =>
          intro hshape
          simp [pendingScopeShapeEqBool] at hshape
          rcases hshape with ⟨hruntimeType, hselectionSet⟩
          cases hruntimeType
          cases selectionSetEqBool_eq hselectionSet
          rfl

def expectedPendingChildWorkShape (work : ExpectedPendingChildWork ObjectRef)
    : PendingScopeShape :=
  {
    runtimeType := work.work.runtimeType
    selectionSet := work.work.selectionSet
  }

def expectedPendingChildWorkShapes (work : ExpectedPendingChildWorkList ObjectRef)
    : List PendingScopeShape :=
  work.map expectedPendingChildWorkShape

def expectedPendingChildWorkSelectionSetShape (work : ExpectedPendingChildWork ObjectRef)
    : SelectionSetShape :=
  { selectionSet := work.work.selectionSet }

def expectedPendingChildWorkSelectionSetShapes
    (work : ExpectedPendingChildWorkList ObjectRef)
    : List SelectionSetShape :=
  work.map expectedPendingChildWorkSelectionSetShape

def expectedPendingChildWorkSelectionSetShapeSet
    (work : ExpectedPendingChildWorkList ObjectRef)
    : List SelectionSetShape :=
  selectionSetShapeSet (expectedPendingChildWorkSelectionSetShapes work)

def expectedPendingChildWorkSelectionSetShapeWeight
    (schema : Schema) (work : ExpectedPendingChildWorkList ObjectRef)
    : Nat :=
  selectionSetShapeSetWeight schema (expectedPendingChildWorkSelectionSetShapeSet work)

def insertPendingScopeShape (shape : PendingScopeShape)
    : List PendingScopeShape -> List PendingScopeShape
  | [] => [shape]
  | existing :: rest =>
      if pendingScopeShapeEqBool shape existing then
        existing :: rest
      else
        existing :: insertPendingScopeShape shape rest

def pendingScopeShapeSet (shapes : List PendingScopeShape) : List PendingScopeShape :=
  shapes.foldl (fun shapes shape => insertPendingScopeShape shape shapes) []

theorem pendingScopeShape_mem_insert_of_mem (inserted shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        shape ∈ shapes -> shape ∈ insertPendingScopeShape inserted shapes
  | [], hmem => by
      simp at hmem
  | existing :: rest, hmem => by
      cases hinsert : pendingScopeShapeEqBool inserted existing with
      | true =>
          simp [insertPendingScopeShape, hinsert] at hmem ⊢
          exact hmem
      | false =>
          simp [insertPendingScopeShape, hinsert] at hmem ⊢
          rcases hmem with hhead | htail
          · exact Or.inl hhead
          · exact Or.inr
              (pendingScopeShape_mem_insert_of_mem inserted shape rest htail)

theorem pendingScopeShape_mem_insert_self (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape, shape ∈ insertPendingScopeShape shape shapes
  | [] => by
      simp [insertPendingScopeShape]
  | existing :: rest => by
      cases hinsert : pendingScopeShapeEqBool shape existing with
      | true =>
          have hshape : shape = existing :=
            pendingScopeShapeEqBool_eq hinsert
          simp [insertPendingScopeShape, hinsert]
          exact Or.inl hshape
      | false =>
          simp [insertPendingScopeShape, hinsert]
          exact Or.inr (pendingScopeShape_mem_insert_self shape rest)

theorem pendingScopeShape_mem_foldl_insert_of_member (shape : PendingScopeShape)
    : ∀ (shapes pending : List PendingScopeShape),
        shape ∈ pending
        -> shape
            ∈ shapes.foldl
                (fun shapes shape => insertPendingScopeShape shape shapes)
                pending := by
  intro shapes
  induction shapes with
  | nil =>
      intro pending hmem
      exact hmem
  | cons inserted shapes ih =>
      intro pending hmem
      exact ih (insertPendingScopeShape inserted pending)
        (pendingScopeShape_mem_insert_of_mem inserted shape pending hmem)

theorem pendingScopeShape_mem_foldl_insert_of_mem (shape : PendingScopeShape)
    : ∀ (shapes pending : List PendingScopeShape),
        shape ∈ shapes
        -> shape
            ∈ shapes.foldl
                (fun shapes shape => insertPendingScopeShape shape shapes)
                pending := by
  intro shapes
  induction shapes with
  | nil =>
      intro pending hmem
      simp at hmem
  | cons inserted shapes ih =>
      intro pending hmem
      have hcases : shape = inserted ∨ shape ∈ shapes := by
        simpa using hmem
      rcases hcases with hhead | htail
      · have hin :
            shape ∈ insertPendingScopeShape inserted pending := by
          rw [← hhead]
          exact pendingScopeShape_mem_insert_self shape pending
        exact pendingScopeShape_mem_foldl_insert_of_member
          shape shapes (insertPendingScopeShape inserted pending) hin
      · exact ih (insertPendingScopeShape inserted pending) htail

theorem pendingScopeShape_mem_shapeSet_of_mem
    (shape : PendingScopeShape) (shapes : List PendingScopeShape)
    : shape ∈ shapes -> shape ∈ pendingScopeShapeSet shapes := by
  intro hmem
  simpa [pendingScopeShapeSet] using
    pendingScopeShape_mem_foldl_insert_of_mem shape shapes
      ([] : List PendingScopeShape) hmem

def pendingScopeShapeMemberBool (shape : PendingScopeShape)
    : List PendingScopeShape -> Bool
  | [] => false
  | existing :: rest =>
      pendingScopeShapeEqBool shape existing || pendingScopeShapeMemberBool shape rest

theorem pendingScopeShapeMemberBool_true_of_mem (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        shape ∈ shapes -> pendingScopeShapeMemberBool shape shapes = true
  | [], hmem => by
      simp at hmem
  | existing :: rest, hmem => by
      have hcases : shape = existing ∨ shape ∈ rest := by
        simpa using hmem
      rcases hcases with hhead | htail
      · subst existing
        simp [pendingScopeShapeMemberBool, pendingScopeShapeEqBool_self]
      · cases hshape : pendingScopeShapeEqBool shape existing with
        | true =>
            simp [pendingScopeShapeMemberBool, hshape]
        | false =>
            simp [pendingScopeShapeMemberBool, hshape]
            exact pendingScopeShapeMemberBool_true_of_mem shape rest htail

theorem pendingScopeShapeMemberBool_insert_self
    (shape : PendingScopeShape)
    (seen : List PendingScopeShape)
    : pendingScopeShapeMemberBool shape (insertPendingScopeShape shape seen) = true := by
  induction seen with
  | nil =>
      simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
        pendingScopeShapeEqBool_self]
  | cons existing rest ih =>
      cases hshape : pendingScopeShapeEqBool shape existing with
      | true =>
          simp [insertPendingScopeShape, pendingScopeShapeMemberBool, hshape]
      | false =>
          simp [insertPendingScopeShape, pendingScopeShapeMemberBool, hshape]
          exact ih

theorem pendingScopeShapeMemberBool_insert_of_member
    (shape inserted : PendingScopeShape)
    (seen : List PendingScopeShape)
    : pendingScopeShapeMemberBool shape seen = true
      -> pendingScopeShapeMemberBool shape (insertPendingScopeShape inserted seen)
          = true := by
  intro hmember
  induction seen with
  | nil =>
      simp [pendingScopeShapeMemberBool] at hmember
  | cons existing rest ih =>
      cases hinsert : pendingScopeShapeEqBool inserted existing with
      | true =>
          simpa [insertPendingScopeShape, pendingScopeShapeMemberBool,
            hinsert] using hmember
      | false =>
          cases hshape : pendingScopeShapeEqBool shape existing with
          | true =>
              simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
                hinsert, hshape]
          | false =>
              simp [pendingScopeShapeMemberBool, hshape] at hmember
              simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
                hinsert, hshape]
              exact ih hmember

theorem pendingScopeShapeMemberBool_of_insert_of_ne
    (shape inserted : PendingScopeShape)
    (seen : List PendingScopeShape)
    : pendingScopeShapeEqBool shape inserted = false
      -> pendingScopeShapeMemberBool shape (insertPendingScopeShape inserted seen) = true
      -> pendingScopeShapeMemberBool shape seen = true := by
  intro hneq hmember
  induction seen with
  | nil =>
      simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
        hneq] at hmember
  | cons existing rest ih =>
      cases hinsert : pendingScopeShapeEqBool inserted existing with
      | true =>
          simpa [insertPendingScopeShape, pendingScopeShapeMemberBool,
            hinsert] using hmember
      | false =>
          cases hshape : pendingScopeShapeEqBool shape existing with
          | true =>
              simp [pendingScopeShapeMemberBool, hshape]
          | false =>
              simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
                hinsert, hshape] at hmember
              simpa [pendingScopeShapeMemberBool, hshape] using ih hmember

def pendingScopeShapeStepWeight (schema : Schema) (shape : PendingScopeShape) : Nat :=
  SelectionSet.size shape.selectionSet * (schema.objectTypes.length + 1)

def pendingScopeShapeSetWeight (schema : Schema) : List PendingScopeShape -> Nat
  | [] => 0
  | shape :: shapes =>
      pendingScopeShapeStepWeight schema shape + pendingScopeShapeSetWeight schema shapes

def expectedPendingChildWorkShapeSet (work : ExpectedPendingChildWorkList ObjectRef)
    : List PendingScopeShape :=
  pendingScopeShapeSet (expectedPendingChildWorkShapes work)

def expectedPendingChildWorkShapeWeight
    (schema : Schema) (work : ExpectedPendingChildWorkList ObjectRef)
    : Nat :=
  pendingScopeShapeSetWeight schema (expectedPendingChildWorkShapeSet work)

def pendingScopeShapeUnseenWeight (schema : Schema)
    : List PendingScopeShape -> List PendingScopeShape -> Nat
  | _seen, [] => 0
  | seen, shape :: shapes =>
      if pendingScopeShapeMemberBool shape seen then
        pendingScopeShapeUnseenWeight schema seen shapes
      else
        pendingScopeShapeStepWeight schema shape
        + pendingScopeShapeUnseenWeight schema (insertPendingScopeShape shape seen) shapes

def expectedPendingChildWorkUnseenShapeWeight
    (schema : Schema) (seen : List PendingScopeShape)
    (work : ExpectedPendingChildWorkList ObjectRef)
    : Nat :=
  pendingScopeShapeUnseenWeight schema seen (expectedPendingChildWorkShapes work)

theorem pendingScopeShapeSetWeight_insert_le
    (schema : Schema) (shape : PendingScopeShape)
    (shapes : List PendingScopeShape)
    : pendingScopeShapeSetWeight schema (insertPendingScopeShape shape shapes)
      <= pendingScopeShapeSetWeight schema shapes
          + pendingScopeShapeStepWeight schema shape := by
  induction shapes with
  | nil =>
      simp [insertPendingScopeShape, pendingScopeShapeSetWeight]
  | cons existing rest ih =>
      cases hshape : pendingScopeShapeEqBool shape existing with
      | true =>
          simp [insertPendingScopeShape, pendingScopeShapeSetWeight,
            hshape]
      | false =>
          simp [insertPendingScopeShape, pendingScopeShapeSetWeight,
            hshape]
          omega

theorem pendingScopeShapeMemberBool_false_of_insert_ne_head
    (shape existing : PendingScopeShape) (rest : List PendingScopeShape)
    : pendingScopeShapeEqBool shape existing = false
      -> pendingScopeShapeMemberBool shape (existing :: rest) = false
      -> pendingScopeShapeMemberBool shape rest = false := by
  intro hhead hmember
  simpa [pendingScopeShapeMemberBool, hhead] using hmember

theorem pendingScopeShapeMemberBool_insert_eq_self (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeMemberBool shape shapes = true
        -> insertPendingScopeShape shape shapes = shapes
  | [], hmember => by
      simp [pendingScopeShapeMemberBool] at hmember
  | existing :: rest, hmember => by
      cases hhead : pendingScopeShapeEqBool shape existing with
      | true =>
          simp [insertPendingScopeShape, hhead]
      | false =>
          have htail :
              pendingScopeShapeMemberBool shape rest = true := by
            simpa [pendingScopeShapeMemberBool, hhead] using hmember
          have ih :=
            pendingScopeShapeMemberBool_insert_eq_self shape rest htail
          simp [insertPendingScopeShape, hhead, ih]

theorem pendingScopeShapeSetWeight_insert_eq_of_member
    (schema : Schema) (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeMemberBool shape shapes = true
        -> pendingScopeShapeSetWeight schema (insertPendingScopeShape shape shapes)
            = pendingScopeShapeSetWeight schema shapes := by
  intro shapes hmember
  rw [pendingScopeShapeMemberBool_insert_eq_self shape shapes hmember]

theorem pendingScopeShapeSetWeight_insert_eq_add_of_not_member
    (schema : Schema) (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeMemberBool shape shapes = false
        -> pendingScopeShapeSetWeight schema (insertPendingScopeShape shape shapes)
            = pendingScopeShapeSetWeight schema shapes
              + pendingScopeShapeStepWeight schema shape
  | [], _hmember => by
      simp [insertPendingScopeShape, pendingScopeShapeSetWeight]
  | existing :: rest, hmember => by
      cases hhead : pendingScopeShapeEqBool shape existing with
      | true =>
          simp [pendingScopeShapeMemberBool, hhead] at hmember
      | false =>
          have htail :
              pendingScopeShapeMemberBool shape rest = false :=
            pendingScopeShapeMemberBool_false_of_insert_ne_head
              shape existing rest hhead hmember
          have ih :=
            pendingScopeShapeSetWeight_insert_eq_add_of_not_member
              schema shape rest htail
          simp [insertPendingScopeShape, pendingScopeShapeSetWeight,
            hhead, ih]
          omega

theorem pendingScopeShapeSet_foldl_weight_le
    (schema : Schema) (pending shapes : List PendingScopeShape)
    : pendingScopeShapeSetWeight schema
        (shapes.foldl (fun shapes shape => insertPendingScopeShape shape shapes) pending)
      <= pendingScopeShapeSetWeight schema pending
          + pendingScopeShapeSetWeight schema shapes := by
  induction shapes generalizing pending with
  | nil =>
      simp [pendingScopeShapeSetWeight]
  | cons shape shapes ih =>
      have htail :=
        ih (insertPendingScopeShape shape pending)
      have hinsert :=
        pendingScopeShapeSetWeight_insert_le schema shape pending
      simp [pendingScopeShapeSetWeight] at htail ⊢
      omega

theorem pendingScopeShapeSet_weight_le (schema : Schema) (shapes : List PendingScopeShape)
    : pendingScopeShapeSetWeight schema (pendingScopeShapeSet shapes)
      <= pendingScopeShapeSetWeight schema shapes := by
  simpa [pendingScopeShapeSet, pendingScopeShapeSetWeight] using
    pendingScopeShapeSet_foldl_weight_le schema
      ([] : List PendingScopeShape) shapes

theorem pendingScopeShapeUnseenWeight_add_seen_eq_foldl (schema : Schema)
    : ∀ (shapes seen : List PendingScopeShape),
        pendingScopeShapeUnseenWeight schema seen shapes
          + pendingScopeShapeSetWeight schema seen
        = pendingScopeShapeSetWeight schema
            (shapes.foldl (fun shapes shape => insertPendingScopeShape shape shapes) seen)
  | [], seen => by
      simp [pendingScopeShapeUnseenWeight]
  | shape :: shapes, seen => by
      cases hmember : pendingScopeShapeMemberBool shape seen with
      | true =>
          have hinsert :=
            pendingScopeShapeMemberBool_insert_eq_self shape seen hmember
          have htail :=
            pendingScopeShapeUnseenWeight_add_seen_eq_foldl
              schema shapes seen
          simp [pendingScopeShapeUnseenWeight, hmember, hinsert] at htail ⊢
          exact htail
      | false =>
          have htail :=
            pendingScopeShapeUnseenWeight_add_seen_eq_foldl
              schema shapes (insertPendingScopeShape shape seen)
          have hinsertWeight :=
            pendingScopeShapeSetWeight_insert_eq_add_of_not_member
              schema shape seen hmember
          simp [pendingScopeShapeUnseenWeight, hmember] at htail ⊢
          rw [hinsertWeight] at htail
          omega

theorem pendingScopeShapeUnseenWeight_nil_eq_shapeSetWeight
    (schema : Schema) (shapes : List PendingScopeShape)
    : pendingScopeShapeUnseenWeight schema [] shapes
      = pendingScopeShapeSetWeight schema (pendingScopeShapeSet shapes) := by
  have h :=
    pendingScopeShapeUnseenWeight_add_seen_eq_foldl
      schema shapes ([] : List PendingScopeShape)
  simpa [pendingScopeShapeSet, pendingScopeShapeSetWeight] using h

theorem expectedPendingChildWorkUnseenShapeWeight_nil_eq_shapeWeight
    (schema : Schema) (work : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkUnseenShapeWeight schema [] work
      = expectedPendingChildWorkShapeWeight schema work := by
  simpa [expectedPendingChildWorkUnseenShapeWeight,
    expectedPendingChildWorkShapeWeight, expectedPendingChildWorkShapeSet] using
    pendingScopeShapeUnseenWeight_nil_eq_shapeSetWeight
      schema (expectedPendingChildWorkShapes work)

def pendingScopeShapeBreadthStepWeight (schema : Schema) (shape : PendingScopeShape)
    : Nat :=
  selectionSetBreadthWeight schema shape.selectionSet

def pendingScopeShapeBreadthSetWeight (schema : Schema) : List PendingScopeShape -> Nat
  | [] => 0
  | shape :: shapes =>
      pendingScopeShapeBreadthStepWeight schema shape
      + pendingScopeShapeBreadthSetWeight schema shapes

theorem pendingScopeShapeBreadthSetWeight_append
    (schema : Schema)
    (left right : List PendingScopeShape)
    : pendingScopeShapeBreadthSetWeight schema (left ++ right)
      = pendingScopeShapeBreadthSetWeight schema left
        + pendingScopeShapeBreadthSetWeight schema right := by
  induction left with
  | nil =>
      simp [pendingScopeShapeBreadthSetWeight]
  | cons shape left ih =>
      simp [pendingScopeShapeBreadthSetWeight, ih, Nat.add_assoc]

def expectedPendingChildWorkBreadthShapeWeight
    (schema : Schema) (work : ExpectedPendingChildWorkList ObjectRef)
    : Nat :=
  pendingScopeShapeBreadthSetWeight schema (expectedPendingChildWorkShapeSet work)

def pendingScopeShapeBreadthUnseenWeight (schema : Schema)
    : List PendingScopeShape -> List PendingScopeShape -> Nat
  | _seen, [] => 0
  | seen, shape :: shapes =>
      if pendingScopeShapeMemberBool shape seen then
        pendingScopeShapeBreadthUnseenWeight schema seen shapes
      else
        pendingScopeShapeBreadthStepWeight schema shape
        + pendingScopeShapeBreadthUnseenWeight schema
            (insertPendingScopeShape shape seen) shapes

def expectedPendingChildWorkUnseenBreadthShapeWeight
    (schema : Schema) (seen : List PendingScopeShape)
    (work : ExpectedPendingChildWorkList ObjectRef)
    : Nat :=
  pendingScopeShapeBreadthUnseenWeight schema seen (expectedPendingChildWorkShapes work)

theorem pendingScopeShapeBreadthSetWeight_insert_le
    (schema : Schema) (shape : PendingScopeShape)
    (shapes : List PendingScopeShape)
    : pendingScopeShapeBreadthSetWeight schema (insertPendingScopeShape shape shapes)
      <= pendingScopeShapeBreadthSetWeight schema shapes
          + pendingScopeShapeBreadthStepWeight schema shape := by
  induction shapes with
  | nil =>
      simp [insertPendingScopeShape, pendingScopeShapeBreadthSetWeight]
  | cons existing rest ih =>
      cases hshape : pendingScopeShapeEqBool shape existing with
      | true =>
          simp [insertPendingScopeShape, pendingScopeShapeBreadthSetWeight,
            hshape]
      | false =>
          simp [insertPendingScopeShape, pendingScopeShapeBreadthSetWeight,
            hshape]
          omega

theorem pendingScopeShapeBreadthSetWeight_insert_eq_of_member
    (schema : Schema) (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeMemberBool shape shapes = true
        -> pendingScopeShapeBreadthSetWeight schema (insertPendingScopeShape shape shapes)
            = pendingScopeShapeBreadthSetWeight schema shapes := by
  intro shapes hmember
  rw [pendingScopeShapeMemberBool_insert_eq_self shape shapes hmember]

theorem pendingScopeShapeBreadthSetWeight_insert_eq_add_of_not_member
    (schema : Schema) (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeMemberBool shape shapes = false
        -> pendingScopeShapeBreadthSetWeight schema (insertPendingScopeShape shape shapes)
            = pendingScopeShapeBreadthSetWeight schema shapes
              + pendingScopeShapeBreadthStepWeight schema shape
  | [], _hmember => by
      simp [insertPendingScopeShape, pendingScopeShapeBreadthSetWeight]
  | existing :: rest, hmember => by
      cases hhead : pendingScopeShapeEqBool shape existing with
      | true =>
          simp [pendingScopeShapeMemberBool, hhead] at hmember
      | false =>
          have htail :
              pendingScopeShapeMemberBool shape rest = false :=
            pendingScopeShapeMemberBool_false_of_insert_ne_head
              shape existing rest hhead hmember
          have ih :=
            pendingScopeShapeBreadthSetWeight_insert_eq_add_of_not_member
              schema shape rest htail
          simp [insertPendingScopeShape, pendingScopeShapeBreadthSetWeight,
            hhead, ih]
          omega

theorem pendingScopeShapeBreadthUnseenWeight_add_seen_eq_foldl (schema : Schema)
    : ∀ (shapes seen : List PendingScopeShape),
        pendingScopeShapeBreadthUnseenWeight schema seen shapes
          + pendingScopeShapeBreadthSetWeight schema seen
        = pendingScopeShapeBreadthSetWeight schema
            (shapes.foldl (fun shapes shape => insertPendingScopeShape shape shapes) seen)
  | [], seen => by
      simp [pendingScopeShapeBreadthUnseenWeight]
  | shape :: shapes, seen => by
      cases hmember : pendingScopeShapeMemberBool shape seen with
      | true =>
          have hinsert :=
            pendingScopeShapeMemberBool_insert_eq_self shape seen hmember
          have htail :=
            pendingScopeShapeBreadthUnseenWeight_add_seen_eq_foldl
              schema shapes seen
          simp [pendingScopeShapeBreadthUnseenWeight, hmember, hinsert] at htail ⊢
          exact htail
      | false =>
          have htail :=
            pendingScopeShapeBreadthUnseenWeight_add_seen_eq_foldl
              schema shapes (insertPendingScopeShape shape seen)
          have hinsertWeight :=
            pendingScopeShapeBreadthSetWeight_insert_eq_add_of_not_member
              schema shape seen hmember
          simp [pendingScopeShapeBreadthUnseenWeight, hmember] at htail ⊢
          rw [hinsertWeight] at htail
          omega

theorem pendingScopeShapeBreadthUnseenWeight_nil_eq_shapeSetWeight
    (schema : Schema) (shapes : List PendingScopeShape)
    : pendingScopeShapeBreadthUnseenWeight schema [] shapes
      = pendingScopeShapeBreadthSetWeight schema (pendingScopeShapeSet shapes) := by
  have h :=
    pendingScopeShapeBreadthUnseenWeight_add_seen_eq_foldl
      schema shapes ([] : List PendingScopeShape)
  simpa [pendingScopeShapeSet, pendingScopeShapeBreadthSetWeight] using h

theorem expectedPendingChildWorkUnseenBreadthShapeWeight_nil_eq_shapeWeight
    (schema : Schema) (work : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkUnseenBreadthShapeWeight schema [] work
      = expectedPendingChildWorkBreadthShapeWeight schema work := by
  simpa [expectedPendingChildWorkUnseenBreadthShapeWeight,
    expectedPendingChildWorkBreadthShapeWeight, expectedPendingChildWorkShapeSet] using
    pendingScopeShapeBreadthUnseenWeight_nil_eq_shapeSetWeight
      schema (expectedPendingChildWorkShapes work)

theorem pendingScopeShapeBreadthSet_foldl_weight_le
    (schema : Schema) (pending shapes : List PendingScopeShape)
    : pendingScopeShapeBreadthSetWeight schema
        (shapes.foldl (fun shapes shape => insertPendingScopeShape shape shapes) pending)
      <= pendingScopeShapeBreadthSetWeight schema pending
          + pendingScopeShapeBreadthSetWeight schema shapes := by
  induction shapes generalizing pending with
  | nil =>
      simp [pendingScopeShapeBreadthSetWeight]
  | cons shape shapes ih =>
      have htail :=
        ih (insertPendingScopeShape shape pending)
      have hinsert :=
        pendingScopeShapeBreadthSetWeight_insert_le schema shape pending
      simp [pendingScopeShapeBreadthSetWeight] at htail ⊢
      omega

theorem pendingScopeShapeBreadthSet_weight_le
    (schema : Schema) (shapes : List PendingScopeShape)
    : pendingScopeShapeBreadthSetWeight schema (pendingScopeShapeSet shapes)
      <= pendingScopeShapeBreadthSetWeight schema shapes := by
  simpa [pendingScopeShapeSet, pendingScopeShapeBreadthSetWeight] using
    pendingScopeShapeBreadthSet_foldl_weight_le schema
      ([] : List PendingScopeShape) shapes

def erasePendingScopeShape (shape : PendingScopeShape)
    : List PendingScopeShape -> List PendingScopeShape
  | [] => []
  | existing :: rest =>
      if pendingScopeShapeEqBool existing shape then
        rest
      else
        existing :: erasePendingScopeShape shape rest

def pendingScopeShapeNoDup : List PendingScopeShape -> Prop
  | [] => True
  | shape :: shapes =>
      pendingScopeShapeMemberBool shape shapes = false ∧ pendingScopeShapeNoDup shapes

theorem pendingScopeShapeEqBool_false_comm (left right : PendingScopeShape)
    : pendingScopeShapeEqBool left right = false
      -> pendingScopeShapeEqBool right left = false := by
  intro hfalse
  cases hrev : pendingScopeShapeEqBool right left with
  | false => rfl
  | true =>
      have hrightLeft : right = left :=
        pendingScopeShapeEqBool_eq hrev
      subst right
      simp [pendingScopeShapeEqBool_self] at hfalse

theorem pendingScopeShapeMemberBool_insert_false
    (candidate inserted : PendingScopeShape)
    (shapes : List PendingScopeShape)
    : pendingScopeShapeEqBool candidate inserted = false
      -> pendingScopeShapeMemberBool candidate shapes = false
      -> pendingScopeShapeMemberBool candidate (insertPendingScopeShape inserted shapes)
          = false := by
  intro hcandidate hmember
  induction shapes with
  | nil =>
      simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
        hcandidate]
  | cons existing rest ih =>
      cases hinsert : pendingScopeShapeEqBool inserted existing with
      | true =>
          simpa [insertPendingScopeShape, pendingScopeShapeMemberBool,
            hinsert] using hmember
      | false =>
          cases hhead : pendingScopeShapeEqBool candidate existing with
          | true =>
              simp [pendingScopeShapeMemberBool, hhead] at hmember
          | false =>
              have htail :
                  pendingScopeShapeMemberBool candidate rest = false := by
                simpa [pendingScopeShapeMemberBool, hhead] using hmember
              simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
                hinsert, hhead]
              exact ih htail

theorem pendingScopeShapeNoDup_insert (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeNoDup shapes
        -> pendingScopeShapeNoDup (insertPendingScopeShape shape shapes)
  | [], _hnodup => by
      simp [insertPendingScopeShape, pendingScopeShapeNoDup,
        pendingScopeShapeMemberBool]
  | existing :: rest, hnodup => by
      cases hshape : pendingScopeShapeEqBool shape existing with
      | true =>
          simpa [insertPendingScopeShape, hshape] using hnodup
      | false =>
          rcases hnodup with ⟨hexisting, hrest⟩
          have htail :=
            pendingScopeShapeNoDup_insert shape rest hrest
          have hhead :
              pendingScopeShapeMemberBool existing
                  (insertPendingScopeShape shape rest) = false := by
            exact pendingScopeShapeMemberBool_insert_false existing shape rest
              (pendingScopeShapeEqBool_false_comm shape existing hshape)
              hexisting
          simp [insertPendingScopeShape, pendingScopeShapeNoDup, hshape,
            hhead, htail]

theorem pendingScopeShapeNoDup_foldl_insert
    : ∀ (shapes pending : List PendingScopeShape),
        pendingScopeShapeNoDup pending
        -> pendingScopeShapeNoDup
            (shapes.foldl
              (fun shapes shape => insertPendingScopeShape shape shapes)
              pending)
  | [], pending, hpending => by
      exact hpending
  | shape :: shapes, pending, hpending => by
      exact pendingScopeShapeNoDup_foldl_insert shapes
        (insertPendingScopeShape shape pending)
        (pendingScopeShapeNoDup_insert shape pending hpending)

theorem pendingScopeShapeNoDup_shapeSet (shapes : List PendingScopeShape)
    : pendingScopeShapeNoDup (pendingScopeShapeSet shapes) := by
  simpa [pendingScopeShapeSet, pendingScopeShapeNoDup] using
    pendingScopeShapeNoDup_foldl_insert shapes
      ([] : List PendingScopeShape) (by simp [pendingScopeShapeNoDup])

theorem pendingScopeShapeMemberBool_erase_of_ne_of_member
    (candidate erased : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeEqBool candidate erased = false
        -> pendingScopeShapeMemberBool candidate shapes = true
        -> pendingScopeShapeMemberBool candidate (erasePendingScopeShape erased shapes)
            = true
  | [], _hne, hmember => by
      simp [pendingScopeShapeMemberBool] at hmember
  | existing :: rest, hne, hmember => by
      cases herase : pendingScopeShapeEqBool existing erased with
  | true =>
          have hexisting : existing = erased :=
            pendingScopeShapeEqBool_eq herase
          subst existing
          simp [erasePendingScopeShape, pendingScopeShapeEqBool_self,
            pendingScopeShapeMemberBool, hne] at hmember ⊢
          exact hmember
      | false =>
          cases hhead : pendingScopeShapeEqBool candidate existing with
          | true =>
              simp [erasePendingScopeShape, pendingScopeShapeMemberBool,
                herase, hhead]
          | false =>
              have htail :
                  pendingScopeShapeMemberBool candidate rest = true := by
                simpa [pendingScopeShapeMemberBool, hhead] using hmember
              simp [erasePendingScopeShape, pendingScopeShapeMemberBool,
                herase, hhead]
              exact pendingScopeShapeMemberBool_erase_of_ne_of_member
                candidate erased rest hne htail

theorem pendingScopeShapeBreadthSetWeight_erase_add_eq
    (schema : Schema) (shape : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeMemberBool shape shapes = true
        -> pendingScopeShapeBreadthSetWeight schema shapes
            = pendingScopeShapeBreadthStepWeight schema shape
              + pendingScopeShapeBreadthSetWeight schema
                  (erasePendingScopeShape shape shapes)
  | [], hmember => by
      simp [pendingScopeShapeMemberBool] at hmember
  | existing :: rest, hmember => by
      cases hhead : pendingScopeShapeEqBool shape existing with
      | true =>
          have hshape : shape = existing :=
            pendingScopeShapeEqBool_eq hhead
          subst shape
          simp [erasePendingScopeShape, pendingScopeShapeEqBool_self,
            pendingScopeShapeBreadthSetWeight]
      | false =>
          have htail :
              pendingScopeShapeMemberBool shape rest = true := by
            simpa [pendingScopeShapeMemberBool, hhead] using hmember
          have ih :=
            pendingScopeShapeBreadthSetWeight_erase_add_eq
              schema shape rest htail
          have heraseHead :
              pendingScopeShapeEqBool existing shape = false :=
            pendingScopeShapeEqBool_false_comm shape existing hhead
          simp [erasePendingScopeShape, pendingScopeShapeBreadthSetWeight,
            heraseHead, ih]
          omega

theorem pendingScopeShapeBreadthSetWeight_le_of_memberBool_subset (schema : Schema)
    : ∀ actual possible : List PendingScopeShape,
        pendingScopeShapeNoDup actual
        -> (∀ shape,
              pendingScopeShapeMemberBool shape actual = true
              -> pendingScopeShapeMemberBool shape possible = true)
        -> pendingScopeShapeBreadthSetWeight schema actual
            <= pendingScopeShapeBreadthSetWeight schema possible
  | [], _possible, _hnodup, _hsubset => by
      simp [pendingScopeShapeBreadthSetWeight]
  | shape :: rest, possible, hnodup, hsubset => by
      rcases hnodup with ⟨hshapeRest, hrestNoDup⟩
      have hshapePossible :
          pendingScopeShapeMemberBool shape possible = true :=
        hsubset shape (by simp [pendingScopeShapeMemberBool,
          pendingScopeShapeEqBool_self])
      have hpossibleErase :=
        pendingScopeShapeBreadthSetWeight_erase_add_eq
          schema shape possible hshapePossible
      have hrestSubset :
          ∀ candidate,
            pendingScopeShapeMemberBool candidate rest = true ->
              pendingScopeShapeMemberBool candidate
                (erasePendingScopeShape shape possible) = true := by
        intro candidate hcandidate
        have hcandidatePossible :
            pendingScopeShapeMemberBool candidate possible = true :=
          hsubset candidate (by
            cases hhead : pendingScopeShapeEqBool candidate shape with
            | true =>
                simp [pendingScopeShapeMemberBool, hhead]
            | false =>
                simp [pendingScopeShapeMemberBool, hhead, hcandidate])
        have hcandidateShape :
            pendingScopeShapeEqBool candidate shape = false := by
          cases hcandidateShape : pendingScopeShapeEqBool candidate shape with
          | false => rfl
          | true =>
              have hcandidateEq : candidate = shape :=
                pendingScopeShapeEqBool_eq hcandidateShape
              subst candidate
              rw [hcandidate] at hshapeRest
              simp at hshapeRest
        exact pendingScopeShapeMemberBool_erase_of_ne_of_member
          candidate shape possible hcandidateShape hcandidatePossible
      have hrest :=
        pendingScopeShapeBreadthSetWeight_le_of_memberBool_subset
          schema rest (erasePendingScopeShape shape possible)
          hrestNoDup hrestSubset
      simp [pendingScopeShapeBreadthSetWeight]
      rw [hpossibleErase]
      omega

theorem pendingScopeShapeMemberBool_insert_cases (candidate inserted : PendingScopeShape)
    : ∀ shapes : List PendingScopeShape,
        pendingScopeShapeMemberBool candidate (insertPendingScopeShape inserted shapes)
          = true
        -> pendingScopeShapeEqBool candidate inserted = true
            ∨ pendingScopeShapeMemberBool candidate shapes = true
  | [], hmember => by
      simp [insertPendingScopeShape, pendingScopeShapeMemberBool] at hmember
      exact Or.inl hmember
  | existing :: rest, hmember => by
      cases hinsert : pendingScopeShapeEqBool inserted existing with
      | true =>
          have hinsertEq : inserted = existing :=
            pendingScopeShapeEqBool_eq hinsert
          subst inserted
          exact Or.inr (by simpa [insertPendingScopeShape, hinsert] using hmember)
      | false =>
          cases hhead : pendingScopeShapeEqBool candidate existing with
          | true =>
              exact Or.inr (by simp [pendingScopeShapeMemberBool, hhead])
          | false =>
              simp [insertPendingScopeShape, pendingScopeShapeMemberBool,
                hinsert, hhead] at hmember
              rcases pendingScopeShapeMemberBool_insert_cases
                  candidate inserted rest hmember with hinserted | hrest
              · exact Or.inl hinserted
              · exact Or.inr (by simp [pendingScopeShapeMemberBool,
                  hhead, hrest])

theorem pendingScopeShapeMemberBool_foldl_insert_of_all
    (raw possible : List PendingScopeShape)
    : ∀ pending : List PendingScopeShape,
        (∀ shape,
          pendingScopeShapeMemberBool shape pending = true
          -> pendingScopeShapeMemberBool shape possible = true)
        -> (∀ shape, shape ∈ raw -> pendingScopeShapeMemberBool shape possible = true)
        -> ∀ shape,
            pendingScopeShapeMemberBool shape
                (raw.foldl
                  (fun shapes shape => insertPendingScopeShape shape shapes)
                  pending)
              = true
            -> pendingScopeShapeMemberBool shape possible = true
  | pending, hpending, hall, shape, hshape => by
      cases raw with
      | nil =>
          exact hpending shape hshape
      | cons inserted rest =>
          simp only [List.foldl_cons] at hshape
          have hrestAll :
              ∀ candidate, candidate ∈ rest ->
                pendingScopeShapeMemberBool candidate possible = true := by
            intro candidate hcandidate
            exact hall candidate (by simp [hcandidate])
          have hpending' :
              ∀ candidate,
                pendingScopeShapeMemberBool candidate
                    (insertPendingScopeShape inserted pending) = true ->
                  pendingScopeShapeMemberBool candidate possible = true := by
            intro candidate hcandidate
            rcases pendingScopeShapeMemberBool_insert_cases
                candidate inserted pending hcandidate with hinserted | hpendingMember
            · have hcandidateInserted : candidate = inserted :=
                pendingScopeShapeEqBool_eq hinserted
              subst candidate
              exact hall inserted (by simp)
            · exact hpending candidate hpendingMember
          exact pendingScopeShapeMemberBool_foldl_insert_of_all
            rest possible (insertPendingScopeShape inserted pending)
            hpending' hrestAll shape hshape

theorem pendingScopeShapeMemberBool_shapeSet_of_all
    (raw possible : List PendingScopeShape)
    : (∀ shape, shape ∈ raw -> pendingScopeShapeMemberBool shape possible = true)
      -> ∀ shape,
          pendingScopeShapeMemberBool shape (pendingScopeShapeSet raw) = true
          -> pendingScopeShapeMemberBool shape possible = true := by
  intro hall shape hshape
  exact pendingScopeShapeMemberBool_foldl_insert_of_all
    raw possible ([] : List PendingScopeShape)
    (by intro candidate hcandidate; simp [pendingScopeShapeMemberBool] at hcandidate)
    hall shape
    (by simpa [pendingScopeShapeSet] using hshape)

def expectedPendingChildWorkToPending (work : ExpectedPendingChildWorkList ObjectRef)
    : PendingChildWorkList ObjectRef :=
  work.map ExpectedPendingChildWork.work

def expectedPendingChildWorkSpecResult
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    : Result ResponseValue :=
  objectResultFromFields
    (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
      work.specFuel work.work.source
      (collectFieldsByKey schema variableValues
        work.work.runtimeType work.work.selectionSet))

def expectedPendingChildWorkCompletion
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    : List (Result ResponseValue) :=
  [expectedPendingChildWorkSpecResult schema resolvers variableValues work]

def expectedPendingChildWorkCompletionStack
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    : CompletionStack :=
  {
    valueStack :=
      work.map (expectedPendingChildWorkCompletion schema resolvers variableValues)
    fieldStore := []
  }

mutual
  def expectedPendingChildWorkForCompleteValue
      (schema : Schema) (selectionSet : List Selection)
      : Nat -> TypeRef -> ResolverValue ObjectRef
        -> ExpectedPendingChildWorkList ObjectRef
        -> ExpectedPendingChildWorkList ObjectRef
    | 0, _fieldType, _value, pending => pending
    | fuel, .nonNull inner, value, pending =>
        expectedPendingChildWorkForCompleteValue schema selectionSet
          fuel inner value pending
    | _fuel + 1, .list _inner, .null, pending => pending
    | fuel + 1, .list inner, .list values, pending =>
        expectedPendingChildWorkForCompleteValueList schema selectionSet
          fuel inner values pending
    | _fuel + 1, .list _inner, _value, pending => pending
    | _fuel + 1, .named _typeName, .null, pending => pending
    | _fuel + 1, .named _typeName, .scalar _value, pending => pending
    | fuel + 1, .named parentType, .object runtimeType ref, pending =>
        if schema.typeIncludesObjectBool parentType runtimeType then
          pending
          ++ [{
                work :=
                  {
                    runtimeType := runtimeType
                    selectionSet := selectionSet
                    source := .object runtimeType ref
                  }
                specFuel := fuel
              }]
        else
          pending
    | _fuel + 1, .named _typeName, .list _values, pending => pending

  def expectedPendingChildWorkForCompleteValueList
      (schema : Schema) (selectionSet : List Selection) (fuel : Nat)
      (inner : TypeRef)
      : List (ResolverValue ObjectRef) -> ExpectedPendingChildWorkList ObjectRef
        -> ExpectedPendingChildWorkList ObjectRef
    | [], pending => pending
    | value :: values, pending =>
        let pending :=
          expectedPendingChildWorkForCompleteValue schema selectionSet
            fuel inner value pending
        expectedPendingChildWorkForCompleteValueList schema selectionSet
          fuel inner values pending
end

def expectedPendingChildWorkForResolved
    (schema : Schema) (selectionSet : List Selection) (fieldType : TypeRef)
    : Nat -> Option (ResolverValue ObjectRef) -> ExpectedPendingChildWorkList ObjectRef
      -> ExpectedPendingChildWorkList ObjectRef
  | 0, _resolved, pending => pending
  | _fuel + 1, none, pending => pending
  | fuel + 1, some value, pending =>
      expectedPendingChildWorkForCompleteValue schema selectionSet
        fuel fieldType value pending

def expectedPendingChildWorkForSources
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (selectionSet : List Selection)
    (fieldType : TypeRef)
    (sources : List (ResolverValue ObjectRef)) (fuels : List Nat)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    (variableValues : VariableValues := [])
    : ExpectedPendingChildWorkList ObjectRef :=
  match sources, fuels with
  | [], _fuels => pending
  | _source :: _sources, [] => pending
  | source :: sources, fuel :: fuels =>
      let resolved :=
        GraphQL.Execution.resolveFieldValueByName schema resolvers variableValues
          fieldKey.parentType fieldKey.fieldName fieldKey.arguments source
      let pending :=
        expectedPendingChildWorkForResolved schema selectionSet
          fieldType fuel resolved pending
      expectedPendingChildWorkForSources schema resolvers fieldKey
        selectionSet fieldType sources fuels pending variableValues

def expectedPendingChildWorkForSegment
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segment : ExpectedQueueSegment ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    (variableValues : VariableValues := [])
    : ExpectedPendingChildWorkList ObjectRef :=
  expectedPendingChildWorkForSources schema resolvers fieldKey
    segment.segment.childSelectionSet fieldType segment.segment.sources
    segment.specFuels pending variableValues

def expectedPendingChildWorkForItem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (variableValues : VariableValues := [])
    : ExpectedPendingChildWorkList ObjectRef :=
  item.segments.foldl
    (fun pending segment =>
      expectedPendingChildWorkForSegment schema resolvers item.key fieldType
        segment pending variableValues)
    []

mutual
  theorem expectedPendingChildWorkForCompleteValue_selectionSet_mem
      (schema : Schema) (selectionSet : List Selection)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
          (value : ResolverValue ObjectRef)
          (pending : ExpectedPendingChildWorkList ObjectRef)
          (childWork : ExpectedPendingChildWork ObjectRef),
          childWork
            ∈ expectedPendingChildWorkForCompleteValue schema selectionSet
                fuel fieldType value pending
          -> childWork ∈ pending ∨ childWork.work.selectionSet = selectionSet := by
    intro fuel fieldType
    induction fieldType generalizing fuel with
    | named typeName =>
        intro value pending childWork hmem
        cases fuel with
        | zero =>
            exact Or.inl (by
              simpa [expectedPendingChildWorkForCompleteValue] using hmem)
        | succ fuel =>
            cases value with
            | null =>
                exact Or.inl (by
                  simpa [expectedPendingChildWorkForCompleteValue] using hmem)
            | scalar value =>
                exact Or.inl (by
                  simpa [expectedPendingChildWorkForCompleteValue] using hmem)
            | object runtimeType ref =>
                by_cases hincludes :
                    schema.typeIncludesObjectBool typeName runtimeType = true
                · simp [expectedPendingChildWorkForCompleteValue, hincludes] at hmem
                  rcases hmem with hpending | hnew
                  · exact Or.inl hpending
                  · rcases hnew with rfl
                    exact Or.inr rfl
                · exact Or.inl (by
                    simpa [expectedPendingChildWorkForCompleteValue, hincludes]
                      using hmem)
            | list values =>
                exact Or.inl (by
                  simpa [expectedPendingChildWorkForCompleteValue] using hmem)
    | list inner ih =>
        intro value pending childWork hmem
        cases fuel with
        | zero =>
            exact Or.inl (by
              simpa [expectedPendingChildWorkForCompleteValue] using hmem)
        | succ fuel =>
            cases value with
            | null =>
                exact Or.inl (by
                  simpa [expectedPendingChildWorkForCompleteValue] using hmem)
            | scalar value =>
                exact Or.inl (by
                  simpa [expectedPendingChildWorkForCompleteValue] using hmem)
            | object runtimeType ref =>
                exact Or.inl (by
                  simpa [expectedPendingChildWorkForCompleteValue] using hmem)
            | list values =>
                induction values generalizing pending with
                | nil =>
                    exact Or.inl (by
                      simpa [expectedPendingChildWorkForCompleteValue,
                        expectedPendingChildWorkForCompleteValueList] using hmem)
                | cons value values ihValues =>
                    have htail :=
                      ihValues
                        (expectedPendingChildWorkForCompleteValue schema
                          selectionSet fuel inner value pending)
                        (by
                          simpa [expectedPendingChildWorkForCompleteValue,
                            expectedPendingChildWorkForCompleteValueList] using hmem)
                    rcases htail with hheadPending | hselection
                    · have hhead :=
                        ih fuel value pending childWork hheadPending
                      exact hhead
                    · exact Or.inr hselection
    | nonNull inner ih =>
        intro value pending childWork hmem
        cases fuel with
        | zero =>
            exact Or.inl (by
              simpa [expectedPendingChildWorkForCompleteValue] using hmem)
        | succ fuel =>
            exact ih (fuel + 1) value pending childWork (by
              simpa [expectedPendingChildWorkForCompleteValue] using hmem)

  theorem expectedPendingChildWorkForCompleteValueList_selectionSet_mem
      (schema : Schema) (selectionSet : List Selection) (fuel : Nat)
      (inner : TypeRef)
      : ∀ (values : List (ResolverValue ObjectRef))
          (pending : ExpectedPendingChildWorkList ObjectRef)
          (childWork : ExpectedPendingChildWork ObjectRef),
          childWork
            ∈ expectedPendingChildWorkForCompleteValueList schema selectionSet
                fuel inner values pending
          -> childWork ∈ pending ∨ childWork.work.selectionSet = selectionSet := by
    intro values
    induction values with
    | nil =>
        intro pending childWork hmem
        exact Or.inl (by
          simpa [expectedPendingChildWorkForCompleteValueList] using hmem)
    | cons value values ih =>
        intro pending childWork hmem
        have htail :=
          ih
            (expectedPendingChildWorkForCompleteValue schema selectionSet
              fuel inner value pending)
            childWork
            (by
              simpa [expectedPendingChildWorkForCompleteValueList] using hmem)
        rcases htail with hheadPending | hselection
        · exact
            expectedPendingChildWorkForCompleteValue_selectionSet_mem
              schema selectionSet fuel inner value
              pending childWork hheadPending
        · exact Or.inr hselection
end

theorem expectedPendingChildWorkForResolved_selectionSet_mem
    (schema : Schema) (selectionSet : List Selection)
    (fieldType : TypeRef) (fuel : Nat)
    (resolved : Option (ResolverValue ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForResolved schema selectionSet
            fieldType fuel resolved pending
      -> childWork ∈ pending ∨ childWork.work.selectionSet = selectionSet := by
  intro hmem
  cases fuel with
  | zero =>
      exact Or.inl (by
        simpa [expectedPendingChildWorkForResolved] using hmem)
  | succ fuel =>
      cases resolved with
      | none =>
          exact Or.inl (by
            simpa [expectedPendingChildWorkForResolved] using hmem)
      | some value =>
          exact expectedPendingChildWorkForCompleteValue_selectionSet_mem
            (ObjectRef := ObjectRef) schema selectionSet fuel fieldType value
            pending childWork
            (by simpa [expectedPendingChildWorkForResolved] using hmem)

theorem expectedPendingChildWorkForSources_selectionSet_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (selectionSet : List Selection)
    (fieldType : TypeRef)
    : ∀ (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
        (pending : ExpectedPendingChildWorkList ObjectRef)
        (childWork : ExpectedPendingChildWork ObjectRef),
        childWork
          ∈ expectedPendingChildWorkForSources schema resolvers fieldKey
              selectionSet fieldType sources specFuels pending variableValues
        -> childWork ∈ pending ∨ childWork.work.selectionSet = selectionSet := by
  intro sources
  induction sources with
  | nil =>
      intro specFuels pending childWork hmem
      exact Or.inl (by
        simpa [expectedPendingChildWorkForSources] using hmem)
  | cons source sources ih =>
      intro specFuels pending childWork hmem
      cases specFuels with
      | nil =>
          exact Or.inl (by
            simpa [expectedPendingChildWorkForSources] using hmem)
      | cons fuel fuels =>
          let resolved :=
            GraphQL.Execution.resolveFieldValueByName schema resolvers variableValues
              fieldKey.parentType fieldKey.fieldName fieldKey.arguments source
          have htail :=
            ih fuels
              (expectedPendingChildWorkForResolved schema selectionSet
                fieldType fuel resolved pending)
              childWork
              (by
                simpa [expectedPendingChildWorkForSources, resolved] using hmem)
          rcases htail with hheadPending | hselection
          · exact
              expectedPendingChildWorkForResolved_selectionSet_mem
                (ObjectRef := ObjectRef) schema selectionSet fieldType fuel
                resolved pending childWork hheadPending
          · exact Or.inr hselection

theorem expectedPendingChildWorkForSegment_selectionSet_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segment : ExpectedQueueSegment ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForSegment schema resolvers fieldKey
            fieldType segment pending variableValues
      -> childWork ∈ pending
          ∨ childWork.work.selectionSet = segment.segment.childSelectionSet := by
  intro hmem
  simpa [expectedPendingChildWorkForSegment] using
    expectedPendingChildWorkForSources_selectionSet_mem
      (ObjectRef := ObjectRef) schema resolvers variableValues fieldKey
      segment.segment.childSelectionSet fieldType segment.segment.sources
      segment.specFuels pending childWork hmem

theorem expectedPendingChildWorkForSegments_selectionSet_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    : ∀ (segments : List (ExpectedQueueSegment ObjectRef))
        (pending : ExpectedPendingChildWorkList ObjectRef)
        (childWork : ExpectedPendingChildWork ObjectRef),
        childWork
          ∈ segments.foldl
              (fun pending segment =>
                expectedPendingChildWorkForSegment schema resolvers fieldKey
                  fieldType segment pending variableValues)
              pending
        -> childWork ∈ pending
            ∨ ∃ segment,
                segment ∈ segments
                ∧ childWork.work.selectionSet = segment.segment.childSelectionSet := by
  intro segments
  induction segments with
  | nil =>
      intro pending childWork hmem
      exact Or.inl (by simpa using hmem)
  | cons segment segments ih =>
      intro pending childWork hmem
      have htail :
          childWork ∈
            segments.foldl
              (fun pending segment =>
                expectedPendingChildWorkForSegment schema resolvers fieldKey
                  fieldType segment pending variableValues)
              (expectedPendingChildWorkForSegment schema resolvers fieldKey
                fieldType segment pending variableValues) := by
        simpa [List.foldl_cons] using hmem
      have hrest := ih
        (expectedPendingChildWorkForSegment schema resolvers fieldKey
          fieldType segment pending variableValues)
        childWork htail
      rcases hrest with hheadPending | hrestSegment
      · have hhead :=
          expectedPendingChildWorkForSegment_selectionSet_mem
            (ObjectRef := ObjectRef) schema resolvers variableValues fieldKey fieldType
            segment pending childWork hheadPending
        rcases hhead with hpending | hselection
        · exact Or.inl hpending
        · exact Or.inr ⟨segment, by simp, hselection⟩
      · rcases hrestSegment with ⟨restSegment, hrestMem, hselection⟩
        exact Or.inr ⟨restSegment, by simp [hrestMem], hselection⟩

theorem expectedPendingChildWorkForItem_selectionSet_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForItem schema resolvers fieldType item variableValues
      -> { selectionSet := childWork.work.selectionSet }
          ∈ expectedQueueItemChildSelectionSetShapes item := by
  intro hmem
  have hsegments :=
    expectedPendingChildWorkForSegments_selectionSet_mem
      (ObjectRef := ObjectRef) schema resolvers variableValues item.key fieldType
      item.segments [] childWork
      (by simpa [expectedPendingChildWorkForItem] using hmem)
  rcases hsegments with hnil | hsegment
  · simp at hnil
  · rcases hsegment with ⟨segment, hsegmentMem, hselection⟩
    let shape := expectedQueueSegmentShape item.key segment
    have hraw :
        shape ∈ expectedQueueItemShapes item := by
      exact List.mem_map.mpr ⟨segment, hsegmentMem, rfl⟩
    have hset :
        shape ∈ expectedQueueItemShapeSet item := by
      simpa [expectedQueueItemShapeSet] using
        scheduleFieldShape_mem_shapeSet_of_mem shape
          (expectedQueueItemShapes item) hraw
    exact List.mem_map.mpr
      ⟨shape, hset, by
        simp [shape, expectedQueueSegmentShape,
          scheduleFieldShapeChildSelectionSetShape, hselection]⟩

theorem expectedPendingChildWorkForItem_selectionSet_materialized
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (materialized : MaterializedChildSelections)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork ∈ expectedPendingChildWorkForItem schema resolvers fieldType item
      -> selectionSetShapeMemberBool
            { selectionSet := childWork.work.selectionSet }
            (materializeExpectedQueueItem item materialized)
          = true := by
  intro hmem
  exact selectionSetShapeMemberBool_materializeExpectedQueueItem_of_mem
    (ObjectRef := ObjectRef) { selectionSet := childWork.work.selectionSet }
    item materialized
    (expectedPendingChildWorkForItem_selectionSet_mem
      (ObjectRef := ObjectRef) schema resolvers [] fieldType item childWork hmem)

theorem expectedPendingChildWorkForItem_selectionSetShape_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (shape : SelectionSetShape)
    : shape
        ∈ expectedPendingChildWorkSelectionSetShapes
            (expectedPendingChildWorkForItem schema resolvers fieldType item)
      -> shape ∈ expectedQueueItemChildSelectionSetShapes item := by
  intro hshape
  rcases List.mem_map.mp hshape with ⟨childWork, hchildWork, hshapeEq⟩
  subst shape
  simpa [expectedPendingChildWorkSelectionSetShape] using
    expectedPendingChildWorkForItem_selectionSet_mem
      (ObjectRef := ObjectRef) schema resolvers [] fieldType item childWork
      hchildWork

theorem expectedPendingChildWorkForItem_selectionSetShapeSet_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (shape : SelectionSetShape)
    : shape
        ∈ expectedPendingChildWorkSelectionSetShapeSet
            (expectedPendingChildWorkForItem schema resolvers fieldType item)
      -> shape ∈ expectedQueueItemChildSelectionSetShapes item := by
  intro hshape
  have hraw :
      shape ∈ expectedPendingChildWorkSelectionSetShapes
        (expectedPendingChildWorkForItem schema resolvers fieldType item) :=
    selectionSetShape_mem_of_mem_shapeSet shape
      (expectedPendingChildWorkSelectionSetShapes
        (expectedPendingChildWorkForItem schema resolvers fieldType item))
      (by simpa [expectedPendingChildWorkSelectionSetShapeSet] using hshape)
  exact expectedPendingChildWorkForItem_selectionSetShape_mem
    (ObjectRef := ObjectRef) schema resolvers fieldType item shape hraw

theorem expectedPendingChildWorkForCompleteValue_runtimeType_includes
    (schema : Schema) (selectionSet : List Selection)
    : ∀ (fuel : Nat) (fieldType : TypeRef)
        (value : ResolverValue ObjectRef)
        (pending : ExpectedPendingChildWorkList ObjectRef)
        (childWork : ExpectedPendingChildWork ObjectRef),
        childWork
          ∈ expectedPendingChildWorkForCompleteValue schema selectionSet
              fuel fieldType value pending
        -> childWork ∈ pending
            ∨ schema.typeIncludesObjectBool fieldType.namedType childWork.work.runtimeType
              = true := by
  intro fuel fieldType
  induction fieldType generalizing fuel with
  | named typeName =>
      intro value pending childWork hmem
      cases fuel with
      | zero =>
          exact Or.inl (by
            simpa [expectedPendingChildWorkForCompleteValue] using hmem)
      | succ fuel =>
          cases value with
          | null =>
              exact Or.inl (by
                simpa [expectedPendingChildWorkForCompleteValue] using hmem)
          | scalar value =>
              exact Or.inl (by
                simpa [expectedPendingChildWorkForCompleteValue] using hmem)
          | object runtimeType ref =>
              by_cases hincludes :
                  schema.typeIncludesObjectBool typeName runtimeType = true
              · simp [expectedPendingChildWorkForCompleteValue, hincludes] at hmem
                rcases hmem with hpending | hnew
                · exact Or.inl hpending
                · rcases hnew with rfl
                  exact Or.inr hincludes
              · exact Or.inl (by
                  simpa [expectedPendingChildWorkForCompleteValue, hincludes]
                    using hmem)
          | list values =>
              exact Or.inl (by
                simpa [expectedPendingChildWorkForCompleteValue] using hmem)
  | list inner ih =>
      intro value pending childWork hmem
      cases fuel with
      | zero =>
          exact Or.inl (by
            simpa [expectedPendingChildWorkForCompleteValue] using hmem)
      | succ fuel =>
          cases value with
          | null =>
              exact Or.inl (by
                simpa [expectedPendingChildWorkForCompleteValue] using hmem)
          | scalar value =>
              exact Or.inl (by
                simpa [expectedPendingChildWorkForCompleteValue] using hmem)
          | object runtimeType ref =>
              exact Or.inl (by
                simpa [expectedPendingChildWorkForCompleteValue] using hmem)
          | list values =>
              induction values generalizing pending with
              | nil =>
                  exact Or.inl (by
                    simpa [expectedPendingChildWorkForCompleteValue,
                      expectedPendingChildWorkForCompleteValueList] using hmem)
              | cons value values ihValues =>
                  have htail :=
                    ihValues
                      (expectedPendingChildWorkForCompleteValue schema
                        selectionSet fuel inner value pending)
                      (by
                        simpa [expectedPendingChildWorkForCompleteValue,
                          expectedPendingChildWorkForCompleteValueList] using hmem)
                  rcases htail with hheadPending | hincludes
                  · exact
                      ih fuel value pending childWork hheadPending
                  · exact Or.inr hincludes
  | nonNull inner ih =>
      intro value pending childWork hmem
      cases fuel with
      | zero =>
          exact Or.inl (by
            simpa [expectedPendingChildWorkForCompleteValue] using hmem)
      | succ fuel =>
          exact ih (fuel + 1) value pending childWork (by
            simpa [expectedPendingChildWorkForCompleteValue] using hmem)

theorem expectedPendingChildWorkForCompleteValueList_runtimeType_includes
    (schema : Schema) (selectionSet : List Selection) (fuel : Nat)
    (inner : TypeRef)
    : ∀ (values : List (ResolverValue ObjectRef))
        (pending : ExpectedPendingChildWorkList ObjectRef)
        (childWork : ExpectedPendingChildWork ObjectRef),
        childWork
          ∈ expectedPendingChildWorkForCompleteValueList schema selectionSet
              fuel inner values pending
        -> childWork ∈ pending
            ∨ schema.typeIncludesObjectBool inner.namedType childWork.work.runtimeType
              = true := by
  intro values
  induction values with
  | nil =>
      intro pending childWork hmem
      exact Or.inl (by
        simpa [expectedPendingChildWorkForCompleteValueList] using hmem)
  | cons value values ih =>
      intro pending childWork hmem
      have htail :=
        ih
          (expectedPendingChildWorkForCompleteValue schema selectionSet
            fuel inner value pending)
          childWork
          (by
            simpa [expectedPendingChildWorkForCompleteValueList] using hmem)
      rcases htail with hheadPending | hincludes
      · exact
          expectedPendingChildWorkForCompleteValue_runtimeType_includes
            schema selectionSet fuel inner value pending childWork hheadPending
      · exact Or.inr hincludes

theorem expectedPendingChildWorkForResolved_runtimeType_includes
    (schema : Schema) (selectionSet : List Selection)
    (fieldType : TypeRef) (fuel : Nat)
    (resolved : Option (ResolverValue ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForResolved schema selectionSet
            fieldType fuel resolved pending
      -> childWork ∈ pending
          ∨ schema.typeIncludesObjectBool fieldType.namedType childWork.work.runtimeType
            = true := by
  intro hmem
  cases fuel with
  | zero =>
      exact Or.inl (by
        simpa [expectedPendingChildWorkForResolved] using hmem)
  | succ fuel =>
      cases resolved with
      | none =>
          exact Or.inl (by
            simpa [expectedPendingChildWorkForResolved] using hmem)
      | some value =>
          exact expectedPendingChildWorkForCompleteValue_runtimeType_includes
            (ObjectRef := ObjectRef) schema selectionSet fuel fieldType value
            pending childWork
            (by simpa [expectedPendingChildWorkForResolved] using hmem)

theorem expectedPendingChildWorkForSources_runtimeType_includes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (selectionSet : List Selection)
    (fieldType : TypeRef)
    : ∀ (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
        (pending : ExpectedPendingChildWorkList ObjectRef)
        (childWork : ExpectedPendingChildWork ObjectRef),
        childWork
          ∈ expectedPendingChildWorkForSources schema resolvers fieldKey
              selectionSet fieldType sources specFuels pending variableValues
        -> childWork ∈ pending
            ∨ schema.typeIncludesObjectBool fieldType.namedType childWork.work.runtimeType
              = true := by
  intro sources
  induction sources with
  | nil =>
      intro specFuels pending childWork hmem
      exact Or.inl (by
        simpa [expectedPendingChildWorkForSources] using hmem)
  | cons source sources ih =>
      intro specFuels pending childWork hmem
      cases specFuels with
      | nil =>
          exact Or.inl (by
            simpa [expectedPendingChildWorkForSources] using hmem)
      | cons fuel fuels =>
          let resolved :=
            GraphQL.Execution.resolveFieldValueByName schema resolvers variableValues
              fieldKey.parentType fieldKey.fieldName fieldKey.arguments source
          have htail :=
            ih fuels
              (expectedPendingChildWorkForResolved schema selectionSet
                fieldType fuel resolved pending)
              childWork
              (by
                simpa [expectedPendingChildWorkForSources, resolved] using hmem)
          rcases htail with hheadPending | hincludes
          · exact
              expectedPendingChildWorkForResolved_runtimeType_includes
                (ObjectRef := ObjectRef) schema selectionSet fieldType fuel
                resolved pending childWork hheadPending
          · exact Or.inr hincludes

theorem expectedPendingChildWorkForSegment_runtimeType_includes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segment : ExpectedQueueSegment ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForSegment schema resolvers fieldKey
            fieldType segment pending variableValues
      -> childWork ∈ pending
          ∨ schema.typeIncludesObjectBool fieldType.namedType childWork.work.runtimeType
            = true := by
  intro hmem
  simpa [expectedPendingChildWorkForSegment] using
    expectedPendingChildWorkForSources_runtimeType_includes
      (ObjectRef := ObjectRef) schema resolvers variableValues fieldKey
      segment.segment.childSelectionSet fieldType segment.segment.sources
      segment.specFuels pending childWork hmem

theorem expectedPendingChildWorkForSegments_runtimeType_includes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    : ∀ (segments : List (ExpectedQueueSegment ObjectRef))
        (pending : ExpectedPendingChildWorkList ObjectRef)
        (childWork : ExpectedPendingChildWork ObjectRef),
        childWork
          ∈ segments.foldl
              (fun pending segment =>
                expectedPendingChildWorkForSegment schema resolvers fieldKey
                  fieldType segment pending variableValues)
              pending
        -> childWork ∈ pending
            ∨ schema.typeIncludesObjectBool fieldType.namedType childWork.work.runtimeType
              = true := by
  intro segments
  induction segments with
  | nil =>
      intro pending childWork hmem
      exact Or.inl (by simpa using hmem)
  | cons segment segments ih =>
      intro pending childWork hmem
      have htail :
          childWork ∈
            segments.foldl
              (fun pending segment =>
                expectedPendingChildWorkForSegment schema resolvers fieldKey
                  fieldType segment pending variableValues)
              (expectedPendingChildWorkForSegment schema resolvers fieldKey
                fieldType segment pending variableValues) := by
        simpa [List.foldl_cons] using hmem
      have hrest := ih
        (expectedPendingChildWorkForSegment schema resolvers fieldKey
          fieldType segment pending variableValues)
        childWork htail
      rcases hrest with hheadPending | hincludes
      · exact
          expectedPendingChildWorkForSegment_runtimeType_includes
            (ObjectRef := ObjectRef) schema resolvers variableValues fieldKey fieldType
            segment pending childWork hheadPending
      · exact Or.inr hincludes

theorem expectedPendingChildWorkForItem_runtimeType_includes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForItem schema resolvers fieldType item variableValues
      -> schema.typeIncludesObjectBool fieldType.namedType childWork.work.runtimeType
          = true := by
  intro hmem
  have hsegments :=
    expectedPendingChildWorkForSegments_runtimeType_includes
      (ObjectRef := ObjectRef) schema resolvers variableValues item.key fieldType
      item.segments [] childWork
      (by simpa [expectedPendingChildWorkForItem] using hmem)
  rcases hsegments with hnil | hincludes
  · simp at hnil
  · exact hincludes

theorem expectedPendingChildWorkForItem_runtimeType_mem_possibleTypes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForItem schema resolvers fieldType item variableValues
      -> childWork.work.runtimeType ∈ schema.getPossibleTypes fieldType.namedType := by
  intro hmem
  have hincludes :=
    expectedPendingChildWorkForItem_runtimeType_includes
      (ObjectRef := ObjectRef) schema resolvers variableValues fieldType item childWork hmem
  simpa [Schema.typeIncludesObjectBool] using List.contains_iff_mem.mp hincludes

theorem expectedPendingChildWorkScopeBudgetReady_append
    (schema : Schema)
    (left right : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkScopeBudgetReady schema left
      -> expectedPendingChildWorkScopeBudgetReady schema right
      -> expectedPendingChildWorkScopeBudgetReady schema (left ++ right) := by
  intro hleft hright childWork hmem
  simp at hmem
  rcases hmem with hmem | hmem
  · exact hleft childWork hmem
  · exact hright childWork hmem

theorem expectedPendingChildWorkForCompleteValue_scopeBudgetReady
    (schema : Schema) (selectionSet : List Selection)
    : ∀ (fuel : Nat) (fieldType : TypeRef) (value : ResolverValue ObjectRef)
        (pending : ExpectedPendingChildWorkList ObjectRef),
        specFuelValueBudget schema selectionSet fieldType fuel
        -> expectedPendingChildWorkScopeBudgetReady schema pending
        -> expectedPendingChildWorkScopeBudgetReady schema
            (expectedPendingChildWorkForCompleteValue schema selectionSet
              fuel fieldType value pending) := by
  intro fuel fieldType
  induction fieldType generalizing fuel with
  | named typeName =>
      intro value pending hbudget hpending
      cases fuel with
      | zero =>
          unfold specFuelValueBudget at hbudget
          omega
      | succ fuel =>
          cases value with
          | null =>
              simpa [expectedPendingChildWorkForCompleteValue] using hpending
          | scalar value =>
              simpa [expectedPendingChildWorkForCompleteValue] using hpending
          | object runtimeType ref =>
              by_cases hincludes :
                  schema.typeIncludesObjectBool typeName runtimeType = true
              · intro childWork hmem
                simp [expectedPendingChildWorkForCompleteValue, hincludes] at hmem
                rcases hmem with hmem | hmem
                · exact hpending childWork hmem
                · rcases hmem with rfl
                  unfold specFuelScopeBudget
                  unfold specFuelValueBudget at hbudget
                  simp [typeRefCompleteValueFuelBound] at hbudget
                  omega
              · simpa [expectedPendingChildWorkForCompleteValue, hincludes] using
                  hpending
          | list values =>
              simpa [expectedPendingChildWorkForCompleteValue] using hpending
  | list inner ih =>
      intro value pending hbudget hpending
      cases fuel with
      | zero =>
          unfold specFuelValueBudget at hbudget
          omega
      | succ fuel =>
          have hinnerBudget :
              specFuelValueBudget schema selectionSet inner fuel := by
            unfold specFuelValueBudget at hbudget ⊢
            simp [typeRefCompleteValueFuelBound] at hbudget
            omega
          cases value with
          | null =>
              simpa [expectedPendingChildWorkForCompleteValue] using hpending
          | scalar value =>
              simpa [expectedPendingChildWorkForCompleteValue] using hpending
          | object runtimeType ref =>
              simpa [expectedPendingChildWorkForCompleteValue] using hpending
          | list values =>
              induction values generalizing pending with
              | nil =>
                  simpa [expectedPendingChildWorkForCompleteValue,
                    expectedPendingChildWorkForCompleteValueList] using hpending
              | cons value values ihValues =>
                  have hhead :
                      expectedPendingChildWorkScopeBudgetReady schema
                        (expectedPendingChildWorkForCompleteValue schema
                          selectionSet fuel inner value pending) :=
                    ih fuel value pending hinnerBudget hpending
                  have htail :=
                    ihValues
                      (expectedPendingChildWorkForCompleteValue schema
                        selectionSet fuel inner value pending)
                      hhead
                  simpa [expectedPendingChildWorkForCompleteValue,
                    expectedPendingChildWorkForCompleteValueList] using htail
  | nonNull inner ih =>
      intro value pending hbudget hpending
      cases fuel with
      | zero =>
          unfold specFuelValueBudget at hbudget
          simp [typeRefCompleteValueFuelBound] at hbudget
      | succ fuel =>
          have hinnerBudget :
              specFuelValueBudget schema selectionSet inner (fuel + 1) := by
            simpa [specFuelValueBudget, typeRefCompleteValueFuelBound] using
              hbudget
          simpa [expectedPendingChildWorkForCompleteValue] using
            ih (fuel + 1) value pending hinnerBudget hpending

theorem expectedPendingChildWorkForResolved_scopeBudgetReady
    (schema : Schema) (selectionSet : List Selection)
    (fieldType : TypeRef) (fuel : Nat)
    (resolved : Option (ResolverValue ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : typeRefCompleteValueFuelBound fieldType <= schemaCompleteValueFuelBound schema
      -> specFuelFieldBudget schema selectionSet fuel
      -> expectedPendingChildWorkScopeBudgetReady schema pending
      -> expectedPendingChildWorkScopeBudgetReady schema
          (expectedPendingChildWorkForResolved schema selectionSet
            fieldType fuel resolved pending) := by
  intro hfieldBound hbudget hpending
  cases fuel with
  | zero =>
      unfold specFuelFieldBudget at hbudget
      omega
  | succ fuel =>
      cases resolved with
      | none =>
          simpa [expectedPendingChildWorkForResolved] using hpending
      | some value =>
          have hvalueBudget :
              specFuelValueBudget schema selectionSet fieldType fuel := by
            have hmul :
                (SelectionSet.size selectionSet + 1) *
                    (schemaCompleteValueFuelBound schema + 1) =
                  SelectionSet.size selectionSet *
                      (schemaCompleteValueFuelBound schema + 1) +
                    (schemaCompleteValueFuelBound schema + 1) := by
              rw [Nat.add_mul]
              simp
            unfold specFuelValueBudget
            unfold specFuelFieldBudget at hbudget
            rw [hmul] at hbudget
            omega
          simpa [expectedPendingChildWorkForResolved] using
            expectedPendingChildWorkForCompleteValue_scopeBudgetReady
              (ObjectRef := ObjectRef) schema selectionSet fuel fieldType value
              pending hvalueBudget hpending

theorem expectedPendingChildWorkForSources_scopeBudgetReady
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (selectionSet : List Selection)
    (fieldType : TypeRef)
    : ∀ (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
        (pending : ExpectedPendingChildWorkList ObjectRef),
        typeRefCompleteValueFuelBound fieldType <= schemaCompleteValueFuelBound schema
        -> (∀ fuel, fuel ∈ specFuels -> specFuelFieldBudget schema selectionSet fuel)
        -> expectedPendingChildWorkScopeBudgetReady schema pending
        -> expectedPendingChildWorkScopeBudgetReady schema
            (expectedPendingChildWorkForSources schema resolvers fieldKey
              selectionSet fieldType sources specFuels pending variableValues) := by
  intro sources
  induction sources with
  | nil =>
      intro specFuels pending _hfieldBound _hbudget hpending
      simpa [expectedPendingChildWorkForSources] using hpending
  | cons source sources ih =>
      intro specFuels pending hfieldBound hbudget hpending
      cases specFuels with
      | nil =>
          simpa [expectedPendingChildWorkForSources] using hpending
      | cons fuel fuels =>
          let resolved :=
            GraphQL.Execution.resolveFieldValueByName schema resolvers variableValues
              fieldKey.parentType fieldKey.fieldName fieldKey.arguments source
          have hhead :
              expectedPendingChildWorkScopeBudgetReady schema
                (expectedPendingChildWorkForResolved schema selectionSet fieldType
                  fuel resolved pending) :=
            expectedPendingChildWorkForResolved_scopeBudgetReady
              (ObjectRef := ObjectRef) schema selectionSet fieldType fuel resolved
              pending hfieldBound (hbudget fuel (by simp)) hpending
          have htailBudget :
              ∀ tailFuel, tailFuel ∈ fuels ->
                specFuelFieldBudget schema selectionSet tailFuel := by
            intro tailFuel htailFuel
            exact hbudget tailFuel (by simp [htailFuel])
          have htail :=
            ih fuels
              (expectedPendingChildWorkForResolved schema selectionSet fieldType
                fuel resolved pending)
              hfieldBound htailBudget hhead
          simpa [expectedPendingChildWorkForSources, resolved] using htail

theorem expectedPendingChildWorkForSegment_scopeBudgetReady
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segment : ExpectedQueueSegment ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : typeRefCompleteValueFuelBound fieldType <= schemaCompleteValueFuelBound schema
      -> expectedQueueSegmentFieldBudgetReady schema segment
      -> expectedPendingChildWorkScopeBudgetReady schema pending
      -> expectedPendingChildWorkScopeBudgetReady schema
          (expectedPendingChildWorkForSegment schema resolvers fieldKey
            fieldType segment pending variableValues) := by
  intro hfieldBound hbudget hpending
  simpa [expectedPendingChildWorkForSegment] using
    expectedPendingChildWorkForSources_scopeBudgetReady
      (ObjectRef := ObjectRef) schema resolvers variableValues fieldKey
      segment.segment.childSelectionSet fieldType segment.segment.sources
      segment.specFuels pending hfieldBound hbudget hpending

theorem expectedPendingChildWorkForSegments_scopeBudgetReady
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    : ∀ (segments : List (ExpectedQueueSegment ObjectRef))
        (pending : ExpectedPendingChildWorkList ObjectRef),
        typeRefCompleteValueFuelBound fieldType <= schemaCompleteValueFuelBound schema
        -> (∀ segment,
              segment ∈ segments -> expectedQueueSegmentFieldBudgetReady schema segment)
        -> expectedPendingChildWorkScopeBudgetReady schema pending
        -> expectedPendingChildWorkScopeBudgetReady schema
            (segments.foldl
              (fun pending segment =>
                expectedPendingChildWorkForSegment schema resolvers fieldKey
                  fieldType segment pending variableValues)
              pending) := by
  intro segments
  induction segments with
  | nil =>
      intro pending _hfieldBound _hbudget hpending
      simpa using hpending
  | cons segment segments ih =>
      intro pending hfieldBound hbudget hpending
      have hsegment :
          expectedQueueSegmentFieldBudgetReady schema segment :=
        hbudget segment (by simp)
      have hhead :
          expectedPendingChildWorkScopeBudgetReady schema
            (expectedPendingChildWorkForSegment schema resolvers fieldKey
              fieldType segment pending variableValues) :=
        expectedPendingChildWorkForSegment_scopeBudgetReady
          (ObjectRef := ObjectRef) schema resolvers variableValues fieldKey fieldType segment
          pending hfieldBound hsegment hpending
      have hrestBudget :
          ∀ restSegment, restSegment ∈ segments ->
            expectedQueueSegmentFieldBudgetReady schema restSegment := by
        intro restSegment hrestSegment
        exact hbudget restSegment (by simp [hrestSegment])
      simpa [List.foldl_cons] using
        ih
          (expectedPendingChildWorkForSegment schema resolvers fieldKey
            fieldType segment pending variableValues)
          hfieldBound hrestBudget hhead

theorem expectedPendingChildWorkForItem_scopeBudgetReady
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    : typeRefCompleteValueFuelBound fieldType <= schemaCompleteValueFuelBound schema
      -> expectedQueueItemFieldBudgetReady schema item
      -> expectedPendingChildWorkScopeBudgetReady schema
          (expectedPendingChildWorkForItem schema resolvers fieldType item
            variableValues) := by
  intro hfieldBound hbudget
  simpa [expectedPendingChildWorkForItem] using
    expectedPendingChildWorkForSegments_scopeBudgetReady
      (ObjectRef := ObjectRef) schema resolvers variableValues item.key fieldType item.segments
      [] hfieldBound hbudget
      (by simp [expectedPendingChildWorkScopeBudgetReady])

-----------------------------------------------------------------------------------------
-- Expected scheduling for child work
-----------------------------------------------------------------------------------------

def scheduleExpectedScope
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : ExpectedScheduleQueue ObjectRef × TraceFrame :=
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let keyedGroups :=
    groups.map
      (fun group =>
        (scheduleKeyForFields parentType group.fst group.snd, group.snd))
  let queue :=
    keyedGroups.foldl
      (fun queue group =>
        let segment :=
          {
            segment :=
              {
                sources := sources
                childSelectionSet := childSelectionSetForFields group.snd
              }
            specFuels := specFuels
          }
        enqueueExpectedSegment group.fst segment queue)
      queue
  let fieldKeys := keyedGroups.map Prod.fst
  (queue, .scope [sources.length] fieldKeys)

def scheduleExpectedPendingChildWork (schema : Schema) (variableValues : VariableValues)
    : ExpectedPendingChildWorkList ObjectRef -> ExpectedScheduleQueue ObjectRef
      -> ExpectedScheduleQueue ObjectRef × ScopeFrames
  | [], queue => (queue, [])
  | work :: rest, queue =>
      let head :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      let tail := scheduleExpectedPendingChildWork schema variableValues rest head.fst
      (tail.fst, head.snd :: tail.snd)

theorem scheduleExpectedKeyedGroups_fuelsAligned
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (ScheduleKey × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : specFuels.length = sources.length
      -> expectedScheduleQueueFuelsAligned queue
      -> expectedScheduleQueueFuelsAligned
          (groups.foldl
            (fun queue group =>
              enqueueExpectedSegment
                group.fst
                {
                  segment :=
                    {
                      sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd
                    }
                  specFuels := specFuels
                }
                queue)
            queue) := by
  intro hlength hqueue
  induction groups generalizing queue with
  | nil =>
      simpa
  | cons group groups ih =>
      have hsegment :
          expectedQueueSegmentFuelsAligned
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields group.snd }
              specFuels := specFuels } := by
        simpa [expectedQueueSegmentFuelsAligned] using hlength
      exact ih _
        (enqueueExpectedSegment_fuelsAligned
          group.fst
          { segment :=
              { sources := sources
                childSelectionSet := childSelectionSetForFields group.snd }
            specFuels := specFuels }
          queue hsegment hqueue)

theorem scheduleExpectedKeyedGroups_itemsNonempty
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (ScheduleKey × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty queue
      -> expectedScheduleQueueItemsNonempty
          (groups.foldl
            (fun queue group =>
              enqueueExpectedSegment
                group.fst
                {
                  segment :=
                    {
                      sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd
                    }
                  specFuels := specFuels
                }
                queue)
            queue) := by
  intro hqueue
  induction groups generalizing queue with
  | nil =>
      simpa
  | cons group groups ih =>
      exact ih _
        (enqueueExpectedSegment_itemsNonempty
          group.fst
          { segment :=
              { sources := sources
                childSelectionSet := childSelectionSetForFields group.snd }
            specFuels := specFuels }
          queue hqueue)

theorem scheduleExpectedKeyedGroups_keysDistinct
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (ScheduleKey × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueKeysDistinct
          (groups.foldl
            (fun queue group =>
              enqueueExpectedSegment
                group.fst
                {
                  segment :=
                    {
                      sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd
                    }
                  specFuels := specFuels
                }
                queue)
            queue) := by
  intro hqueue
  induction groups generalizing queue with
  | nil =>
      simpa
  | cons group groups ih =>
      exact ih _
        (enqueueExpectedSegment_keysDistinct
          group.fst
          { segment :=
              { sources := sources
                childSelectionSet := childSelectionSetForFields group.snd }
            specFuels := specFuels }
          queue hqueue)

theorem scheduleExpectedKeyedGroups_preserve_contains_shape
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    : ∀ (groups : List (ScheduleKey × List ExecutableField))
        (queue : ExpectedScheduleQueue ObjectRef)
        (shape : ScheduleFieldShape),
        expectedScheduleQueueContainsShape queue shape
        -> expectedScheduleQueueContainsShape
            (groups.foldl
              (fun queue group =>
                enqueueExpectedSegment
                  group.fst
                  {
                    segment :=
                      {
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := specFuels
                  }
                  queue)
              queue)
            shape
  | [], queue, shape, hcontains => by
      simpa using hcontains
  | group :: groups, queue, shape, hcontains => by
      let segment : ExpectedQueueSegment ObjectRef :=
        { segment :=
            { sources := sources
              childSelectionSet := childSelectionSetForFields group.snd }
          specFuels := specFuels }
      have hhead :
          expectedScheduleQueueContainsShape
            (enqueueExpectedSegment group.fst segment queue) shape :=
        expectedScheduleQueueContainsShape_enqueueExpectedSegment_of_contains
          shape group.fst segment queue hcontains
      simpa [segment] using
        scheduleExpectedKeyedGroups_preserve_contains_shape
          sources specFuels groups
          (enqueueExpectedSegment group.fst segment queue) shape hhead

theorem scheduleExpectedKeyedGroups_contains_group
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    : ∀ (groups : List (ScheduleKey × List ExecutableField))
        (queue : ExpectedScheduleQueue ObjectRef)
        (group : ScheduleKey × List ExecutableField),
        group ∈ groups
        -> expectedScheduleQueueContainsShape
            (groups.foldl
              (fun queue group =>
                enqueueExpectedSegment
                  group.fst
                  {
                    segment :=
                      {
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := specFuels
                  }
                  queue)
              queue)
            (expectedQueueSegmentShape group.fst
              {
                segment :=
                  {
                    sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd
                  }
                specFuels := specFuels
              })
  | [], queue, group, hmem => by
      simp at hmem
  | head :: rest, queue, group, hmem => by
      let headSegment : ExpectedQueueSegment ObjectRef :=
        { segment :=
            { sources := sources
              childSelectionSet := childSelectionSetForFields head.snd }
          specFuels := specFuels }
      let queueAfterHead := enqueueExpectedSegment head.fst headSegment queue
      have hcases : group = head ∨ group ∈ rest := by
        simpa using hmem
      rcases hcases with hhead | hrest
      · subst group
        have hcontainsHead :
            expectedScheduleQueueContainsShape queueAfterHead
              (expectedQueueSegmentShape head.fst headSegment) :=
          expectedScheduleQueueContainsShape_enqueueExpectedSegment_self
            head.fst headSegment queue
        have hpreserved :=
          scheduleExpectedKeyedGroups_preserve_contains_shape
            sources specFuels rest queueAfterHead
            (expectedQueueSegmentShape head.fst headSegment) hcontainsHead
        simpa [headSegment, queueAfterHead] using hpreserved
      · have htail :=
          scheduleExpectedKeyedGroups_contains_group
            sources specFuels rest queueAfterHead group hrest
        simpa [headSegment, queueAfterHead] using htail

theorem scheduleExpectedKeyedGroups_shapeWeight_le_of_contains
    (schema : Schema)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    : ∀ (groups : List (ScheduleKey × List ExecutableField))
        (queue : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueKeysDistinct queue
        -> (∀ group,
              group ∈ groups
              -> expectedScheduleQueueContainsShape queue
                  (expectedQueueSegmentShape group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }))
        -> expectedScheduleQueueShapeWeight schema
              (groups.foldl
                (fun queue group =>
                  enqueueExpectedSegment
                    group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }
                    queue)
                queue)
            <= expectedScheduleQueueShapeWeight schema queue
  | [], queue, _hdistinct, _hcontains => by
      simp
  | group :: rest, queue, hdistinct, hcontains => by
      let segment : ExpectedQueueSegment ObjectRef :=
        { segment :=
            { sources := sources
              childSelectionSet := childSelectionSetForFields group.snd }
          specFuels := specFuels }
      let queueAfterHead := enqueueExpectedSegment group.fst segment queue
      have hhead :
          expectedScheduleQueueShapeWeight schema queueAfterHead <=
            expectedScheduleQueueShapeWeight schema queue :=
        expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le_of_contains_shape
          (ObjectRef := ObjectRef) schema group.fst segment queue hdistinct
          (hcontains group (by simp))
      have hheadDistinct :
          expectedScheduleQueueKeysDistinct queueAfterHead :=
        enqueueExpectedSegment_keysDistinct group.fst segment queue hdistinct
      have hrestContains :
          ∀ restGroup, restGroup ∈ rest ->
            expectedScheduleQueueContainsShape queueAfterHead
              (expectedQueueSegmentShape restGroup.fst
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields restGroup.snd }
                  specFuels := specFuels }) := by
        intro restGroup hrestGroup
        exact expectedScheduleQueueContainsShape_enqueueExpectedSegment_of_contains
          (expectedQueueSegmentShape restGroup.fst
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields restGroup.snd }
              specFuels := specFuels })
          group.fst segment queue
          (hcontains restGroup (by simp [hrestGroup]))
      have htail :=
        scheduleExpectedKeyedGroups_shapeWeight_le_of_contains
          schema sources specFuels rest queueAfterHead hheadDistinct hrestContains
      exact Nat.le_trans (by simpa [scheduleExpectedKeyedGroups_shapeWeight_le_of_contains,
        segment, queueAfterHead] using htail) hhead

theorem scheduleExpectedScope_fuelsAligned
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : specFuels.length = sources.length
      -> expectedScheduleQueueFuelsAligned queue
      -> expectedScheduleQueueFuelsAligned
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst := by
  intro hlength hqueue
  simpa [scheduleExpectedScope] using
    scheduleExpectedKeyedGroups_fuelsAligned
      (ObjectRef := ObjectRef) sources specFuels
      ((collectFieldsByKey schema variableValues parentType selectionSet).map
        (fun group => (scheduleKeyForFields parentType group.fst group.snd, group.snd)))
      queue
      hlength hqueue

theorem scheduleExpectedScope_itemsNonempty
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty queue
      -> expectedScheduleQueueItemsNonempty
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst := by
  intro hqueue
  simpa [scheduleExpectedScope] using
    scheduleExpectedKeyedGroups_itemsNonempty
      (ObjectRef := ObjectRef) sources specFuels
      ((collectFieldsByKey schema variableValues parentType selectionSet).map
        (fun group => (scheduleKeyForFields parentType group.fst group.snd, group.snd)))
      queue
      hqueue

theorem scheduleExpectedScope_keysDistinct
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueKeysDistinct
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst := by
  intro hqueue
  simpa [scheduleExpectedScope] using
    scheduleExpectedKeyedGroups_keysDistinct
      (ObjectRef := ObjectRef) sources specFuels
      ((collectFieldsByKey schema variableValues parentType selectionSet).map
        (fun group => (scheduleKeyForFields parentType group.fst group.snd, group.snd)))
      queue
      hqueue

theorem scheduleExpectedScope_contains_collected_group
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    (group : Name × List ExecutableField)
    : group ∈ collectFieldsByKey schema variableValues parentType selectionSet
      -> expectedScheduleQueueContainsShape
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst
          (collectedGroupScheduleShape parentType group) := by
  intro hgroup
  let keyedGroups :=
    (collectFieldsByKey schema variableValues parentType selectionSet).map
      (fun group =>
        (scheduleKeyForFields parentType group.fst group.snd, group.snd))
  let keyedGroup : ScheduleKey × List ExecutableField :=
    (scheduleKeyForFields parentType group.fst group.snd, group.snd)
  have hkeyedMem : keyedGroup ∈ keyedGroups := by
    exact List.mem_map.mpr ⟨group, hgroup, rfl⟩
  have hcontains :=
    scheduleExpectedKeyedGroups_contains_group
      (ObjectRef := ObjectRef) sources specFuels keyedGroups queue
      keyedGroup hkeyedMem
  simpa [scheduleExpectedScope, keyedGroups, keyedGroup,
    collectedGroupScheduleShape, expectedQueueSegmentShape] using hcontains

theorem scheduleExpectedScope_shapeWeight_repeat_le
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (firstSources secondSources : List (ResolverValue ObjectRef))
    (firstSpecFuels secondSpecFuels : List Nat)
    (selectionSet : List Selection)
    : let firstQueue :=
        (scheduleExpectedScope schema variableValues parentType
          firstSources firstSpecFuels selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      expectedScheduleQueueShapeWeight schema
        (scheduleExpectedScope schema variableValues parentType
          secondSources secondSpecFuels selectionSet firstQueue).fst
      <= expectedScheduleQueueShapeWeight schema firstQueue := by
  intro firstQueue
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let keyedGroups : List (ScheduleKey × List ExecutableField) :=
    groups.map
      (fun group =>
        (scheduleKeyForFields parentType group.fst group.snd, group.snd))
  have hdistinct :
      expectedScheduleQueueKeysDistinct firstQueue := by
    simpa [firstQueue] using
      scheduleExpectedScope_keysDistinct
        (ObjectRef := ObjectRef) schema variableValues parentType
        firstSources firstSpecFuels selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)
        (by simp [expectedScheduleQueueKeysDistinct])
  have hcontains :
      ∀ keyedGroup, keyedGroup ∈ keyedGroups ->
        expectedScheduleQueueContainsShape firstQueue
          (expectedQueueSegmentShape keyedGroup.fst
            { segment :=
                { sources := secondSources
                  childSelectionSet := childSelectionSetForFields keyedGroup.snd }
              specFuels := secondSpecFuels }) := by
    intro keyedGroup hkeyedGroup
    rcases List.mem_map.mp hkeyedGroup with ⟨group, hgroup, rfl⟩
    have hfirstContains :
        expectedScheduleQueueContainsShape firstQueue
          (collectedGroupScheduleShape parentType group) := by
      simpa [firstQueue] using
        scheduleExpectedScope_contains_collected_group
          (ObjectRef := ObjectRef) schema variableValues parentType
          firstSources firstSpecFuels selectionSet
          ([] : ExpectedScheduleQueue ObjectRef) group
          (by simpa [groups] using hgroup)
    simpa [collectedGroupScheduleShape, expectedQueueSegmentShape] using
      hfirstContains
  have hrepeat :=
    scheduleExpectedKeyedGroups_shapeWeight_le_of_contains
      (ObjectRef := ObjectRef) schema secondSources secondSpecFuels
      keyedGroups firstQueue hdistinct hcontains
  simpa [scheduleExpectedScope, firstQueue, groups, keyedGroups] using hrepeat

theorem scheduleExpectedScope_shapeWeight_le_of_contains_groups
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> (∀ group,
            group ∈ collectFieldsByKey schema variableValues parentType selectionSet
            -> expectedScheduleQueueContainsShape queue
                (collectedGroupScheduleShape parentType group))
      -> expectedScheduleQueueShapeWeight schema
            (scheduleExpectedScope schema variableValues parentType
              sources specFuels selectionSet queue).fst
          <= expectedScheduleQueueShapeWeight schema queue := by
  intro hdistinct hcontains
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let keyedGroups : List (ScheduleKey × List ExecutableField) :=
    groups.map
      (fun group =>
        (scheduleKeyForFields parentType group.fst group.snd, group.snd))
  have hkeyedContains :
      ∀ keyedGroup, keyedGroup ∈ keyedGroups ->
        expectedScheduleQueueContainsShape queue
          (expectedQueueSegmentShape keyedGroup.fst
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields keyedGroup.snd }
              specFuels := specFuels }) := by
    intro keyedGroup hkeyedGroup
    rcases List.mem_map.mp hkeyedGroup with ⟨group, hgroup, rfl⟩
    have hgroupContains :
        expectedScheduleQueueContainsShape queue
          (collectedGroupScheduleShape parentType group) :=
      hcontains group (by simpa [groups] using hgroup)
    simpa [collectedGroupScheduleShape, expectedQueueSegmentShape] using
      hgroupContains
  have hfold :=
    scheduleExpectedKeyedGroups_shapeWeight_le_of_contains
      (ObjectRef := ObjectRef) schema sources specFuels keyedGroups queue
      hdistinct hkeyedContains
  simpa [scheduleExpectedScope, groups, keyedGroups] using hfold

def expectedScheduleQueueContainsPendingScopeShape
    (schema : Schema) (variableValues : VariableValues)
    (queue : ExpectedScheduleQueue ObjectRef)
    (shape : PendingScopeShape)
    : Prop :=
  ∀ group,
    group ∈ collectFieldsByKey schema variableValues shape.runtimeType shape.selectionSet
    -> expectedScheduleQueueContainsShape queue
        (collectedGroupScheduleShape shape.runtimeType group)

def expectedScheduleQueueContainsPendingScopeShapeList
    (schema : Schema) (variableValues : VariableValues)
    (queue : ExpectedScheduleQueue ObjectRef)
    (shapes : List PendingScopeShape)
    : Prop :=
  ∀ shape,
    pendingScopeShapeMemberBool shape shapes = true
    -> expectedScheduleQueueContainsPendingScopeShape schema variableValues queue shape

theorem expectedScheduleQueueContainsPendingScopeShapeList_insert
    (schema : Schema) (variableValues : VariableValues)
    (queue : ExpectedScheduleQueue ObjectRef)
    (seen : List PendingScopeShape)
    (shape : PendingScopeShape)
    : expectedScheduleQueueContainsPendingScopeShapeList schema variableValues queue seen
      -> expectedScheduleQueueContainsPendingScopeShape schema variableValues queue shape
      -> expectedScheduleQueueContainsPendingScopeShapeList
          schema variableValues queue
          (insertPendingScopeShape shape seen) := by
  intro hseen hshape candidate hcandidate
  cases hsame : pendingScopeShapeEqBool candidate shape with
  | true =>
      have hcandidateEq : candidate = shape :=
        pendingScopeShapeEqBool_eq hsame
      subst candidate
      exact hshape
  | false =>
      have hseenMember : pendingScopeShapeMemberBool candidate seen = true := by
        exact pendingScopeShapeMemberBool_of_insert_of_ne
          candidate shape seen hsame hcandidate
      exact hseen candidate hseenMember

theorem scheduleExpectedScope_preserve_contains_shape
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    (shape : ScheduleFieldShape)
    : expectedScheduleQueueContainsShape queue shape
      -> expectedScheduleQueueContainsShape
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst
          shape := by
  intro hcontains
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let keyedGroups : List (ScheduleKey × List ExecutableField) :=
    groups.map
      (fun group =>
        (scheduleKeyForFields parentType group.fst group.snd, group.snd))
  have hpreserve :=
    scheduleExpectedKeyedGroups_preserve_contains_shape
      (ObjectRef := ObjectRef) sources specFuels keyedGroups queue shape hcontains
  simpa [scheduleExpectedScope, groups, keyedGroups] using hpreserve

theorem scheduleExpectedScope_preserve_contains_pendingScopeShape
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    (shape : PendingScopeShape)
    : expectedScheduleQueueContainsPendingScopeShape schema variableValues queue shape
      -> expectedScheduleQueueContainsPendingScopeShape
          schema variableValues
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst
          shape := by
  intro hcontains group hgroup
  exact scheduleExpectedScope_preserve_contains_shape
    (ObjectRef := ObjectRef) schema variableValues parentType sources
    specFuels selectionSet queue
    (collectedGroupScheduleShape shape.runtimeType group)
    (hcontains group hgroup)

theorem scheduleExpectedScope_contains_pendingScopeShape_self
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueContainsPendingScopeShape
        schema variableValues
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet queue).fst
        {
          runtimeType := parentType
          selectionSet := selectionSet
        } := by
  intro group hgroup
  exact scheduleExpectedScope_contains_collected_group
    (ObjectRef := ObjectRef) schema variableValues parentType sources specFuels
    selectionSet queue group hgroup

theorem scheduleExpectedScope_preserve_contains_pendingScopeShapeList
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    (seen : List PendingScopeShape)
    : expectedScheduleQueueContainsPendingScopeShapeList schema variableValues queue seen
      -> expectedScheduleQueueContainsPendingScopeShapeList
          schema variableValues
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst
          seen := by
  intro hseen shape hshape
  exact scheduleExpectedScope_preserve_contains_pendingScopeShape
    (ObjectRef := ObjectRef) schema variableValues parentType sources
    specFuels selectionSet queue shape (hseen shape hshape)

theorem scheduleExpectedCollectedGroups_fieldBudgetReady
    (schema : Schema) (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : (∀ responseName fields,
        (responseName, fields) ∈ groups
        -> fields ≠ []
            ∧ SelectionSet.size (childSelectionSetForFields fields) + 1
              <= SelectionSet.size selectionSet)
      -> (∀ fuel, fuel ∈ specFuels -> specFuelScopeBudget schema selectionSet fuel)
      -> expectedScheduleQueueFieldBudgetReady schema queue
      -> expectedScheduleQueueFieldBudgetReady schema
          (groups.foldl
            (fun queue group =>
              enqueueExpectedSegment
                (scheduleKeyForFields parentType group.fst group.snd)
                {
                  segment :=
                    {
                      sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd
                    }
                  specFuels := specFuels
                }
                queue)
            queue) := by
  intro hgroups hfuels hqueue
  induction groups generalizing queue with
  | nil =>
      simpa
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hgroupSize :
          SelectionSet.size (childSelectionSetForFields fields) + 1 <=
            SelectionSet.size selectionSet :=
        (hgroups responseName fields (by simp)).2
      have hsegment :
          expectedQueueSegmentFieldBudgetReady schema
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields fields }
              specFuels := specFuels } := by
        intro fuel hfuel
        have hscope := hfuels fuel hfuel
        unfold specFuelFieldBudget
        unfold specFuelScopeBudget at hscope
        have hmul :
            (SelectionSet.size (childSelectionSetForFields fields) + 1) *
                (schemaCompleteValueFuelBound schema + 1) <=
              SelectionSet.size selectionSet *
                (schemaCompleteValueFuelBound schema + 1) :=
          Nat.mul_le_mul_right
            (schemaCompleteValueFuelBound schema + 1) hgroupSize
        exact Nat.lt_of_le_of_lt
          (Nat.add_le_add_left hmul (schemaCompleteValueFuelBound schema))
          hscope
      have hrestGroups :
          ∀ restResponseName restFields,
            (restResponseName, restFields) ∈ groups ->
              restFields ≠ [] ∧
                SelectionSet.size (childSelectionSetForFields restFields) + 1 <=
                  SelectionSet.size selectionSet := by
        intro restResponseName restFields hmem
        exact hgroups restResponseName restFields (by simp [hmem])
      exact ih _
        hrestGroups
        (enqueueExpectedSegment_fieldBudgetReady
          schema (scheduleKeyForFields parentType responseName fields)
          { segment :=
              { sources := sources
                childSelectionSet := childSelectionSetForFields fields }
            specFuels := specFuels }
          queue hsegment hqueue)

theorem scheduleExpectedScope_fieldBudgetReady
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : (∀ fuel, fuel ∈ specFuels -> specFuelScopeBudget schema selectionSet fuel)
      -> expectedScheduleQueueFieldBudgetReady schema queue
      -> expectedScheduleQueueFieldBudgetReady schema
          (scheduleExpectedScope schema variableValues parentType
            sources specFuels selectionSet queue).fst := by
  intro hfuels hqueue
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  have hgroups :
      ∀ responseName fields, (responseName, fields) ∈ groups ->
        fields ≠ [] ∧
          SelectionSet.size (childSelectionSetForFields fields) + 1 <=
            SelectionSet.size selectionSet := by
    intro responseName fields hmem
    exact ⟨
      collectFieldsByKey_collectedGroupsNonempty schema variableValues
        parentType selectionSet responseName fields (by simpa [groups] using hmem),
      childSelectionSetForFields_size_succ_le_selectionSet_of_collectFieldsByKey_mem
        schema variableValues parentType responseName selectionSet fields
        (by simpa [groups] using hmem)
        (collectFieldsByKey_collectedGroupsNonempty schema variableValues
          parentType selectionSet responseName fields (by simpa [groups] using hmem))⟩
  have hfold : ∀ queue0 : ExpectedScheduleQueue ObjectRef,
      List.foldl
          (fun queue (group : ScheduleKey × List ExecutableField) =>
            enqueueExpectedSegment group.fst
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0
          (groups.map
            (fun group =>
              (scheduleKeyForFields parentType group.fst group.snd, group.snd))) =
        List.foldl
          (fun queue (group : Name × List ExecutableField) =>
            enqueueExpectedSegment
              (scheduleKeyForFields parentType group.fst group.snd)
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0 groups := by
    intro queue0
    induction groups generalizing queue0 with
    | nil =>
        rfl
    | cons group groups ih =>
        exact ih _
  unfold scheduleExpectedScope
  simp
  rw [hfold]
  exact
    scheduleExpectedCollectedGroups_fieldBudgetReady
      (ObjectRef := ObjectRef) schema parentType sources specFuels
      selectionSet groups queue hgroups hfuels hqueue

theorem scheduleExpectedCollectedGroups_shapeWeight_le
    (schema : Schema) (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (Name × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueShapeWeight schema
        (groups.foldl
          (fun queue group =>
            enqueueExpectedSegment
              (scheduleKeyForFields parentType group.fst group.snd)
              {
                segment :=
                  {
                    sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd
                  }
                specFuels := specFuels
              }
              queue)
          queue)
      <= expectedScheduleQueueShapeWeight schema queue
          + collectedGroupsShapeWeight schema parentType groups := by
  induction groups generalizing queue with
  | nil =>
      simp [collectedGroupsShapeWeight, collectedGroupsScheduleShapes,
        scheduleFieldShapeSetWeight]
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hhead :=
        expectedScheduleQueueShapeWeight_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema
          (scheduleKeyForFields parentType responseName fields)
          { segment :=
              { sources := sources
                childSelectionSet := childSelectionSetForFields fields }
            specFuels := specFuels }
          queue
      have htail :=
        ih
          (enqueueExpectedSegment
            (scheduleKeyForFields parentType responseName fields)
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields fields }
              specFuels := specFuels }
            queue)
      have hheadShape :
          scheduleFieldShapeStepWeight schema
              (expectedQueueSegmentShape
                (scheduleKeyForFields parentType responseName fields)
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields fields }
                  specFuels := specFuels }) =
            scheduleFieldShapeStepWeight schema
              (collectedGroupScheduleShape parentType (responseName, fields)) := by
        rfl
      simp [collectedGroupsShapeWeight, collectedGroupsScheduleShapes,
        scheduleFieldShapeSetWeight] at htail ⊢
      rw [hheadShape] at hhead
      omega

theorem scheduleExpectedScope_shapeWeight_le
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueShapeWeight schema
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet queue).fst
      <= expectedScheduleQueueShapeWeight schema queue
          + SelectionSet.size selectionSet * (schema.objectTypes.length + 1) := by
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  have hfold : ∀ queue0 : ExpectedScheduleQueue ObjectRef,
      List.foldl
          (fun queue (group : ScheduleKey × List ExecutableField) =>
            enqueueExpectedSegment group.fst
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0
          (groups.map
            (fun group =>
              (scheduleKeyForFields parentType group.fst group.snd, group.snd))) =
        List.foldl
          (fun queue (group : Name × List ExecutableField) =>
            enqueueExpectedSegment
              (scheduleKeyForFields parentType group.fst group.snd)
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0 groups := by
    intro queue0
    induction groups generalizing queue0 with
    | nil =>
        rfl
    | cons group groups ih =>
        exact ih _
  have hscheduled :
      expectedScheduleQueueShapeWeight schema
          (List.foldl
            (fun queue (group : Name × List ExecutableField) =>
              enqueueExpectedSegment
                (scheduleKeyForFields parentType group.fst group.snd)
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := specFuels }
                queue)
            queue groups) <=
        expectedScheduleQueueShapeWeight schema queue
          + collectedGroupsShapeWeight schema parentType groups :=
    scheduleExpectedCollectedGroups_shapeWeight_le
      (ObjectRef := ObjectRef) schema parentType sources specFuels groups queue
  have hgroupsWeight :
      collectedGroupsShapeWeight schema parentType groups <=
        SelectionSet.size selectionSet * (schema.objectTypes.length + 1) := by
    have hnonempty :
        collectedGroupsNonempty groups := by
      simpa [groups] using
        collectFieldsByKey_collectedGroupsNonempty schema variableValues
          parentType selectionSet
    have hshape :=
      collectedGroupsShapeWeight_le_executableGroupsSize schema parentType
        groups hnonempty
    have hsize :=
      collectFieldsByKey_executableGroupsSize_le schema variableValues
        parentType selectionSet
    have hmul :=
      Nat.mul_le_mul_right (schema.objectTypes.length + 1) hsize
    exact Nat.le_trans hshape (by simpa [groups] using hmul)
  unfold scheduleExpectedScope
  simp
  rw [hfold]
  omega

theorem scheduleExpectedScope_shapeWeight_le_selectionSetShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    : expectedScheduleQueueShapeWeight schema
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= selectionSetShapeWeight schema { selectionSet := selectionSet } := by
  simpa [expectedScheduleQueueShapeWeight, selectionSetShapeWeight] using
    scheduleExpectedScope_shapeWeight_le
      (ObjectRef := ObjectRef) schema variableValues parentType sources
      specFuels selectionSet ([] : ExpectedScheduleQueue ObjectRef)

theorem scheduleExpectedScope_drainBudget_le_selectionSetShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    : expectedScheduleQueueDrainBudget schema []
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= selectionSetShapeWeight schema { selectionSet := selectionSet } := by
  exact Nat.le_trans
    (expectedScheduleQueueDrainBudget_le_shapeWeight
      (ObjectRef := ObjectRef) schema []
      (scheduleExpectedScope schema variableValues parentType
        sources specFuels selectionSet
        ([] : ExpectedScheduleQueue ObjectRef)).fst)
    (scheduleExpectedScope_shapeWeight_le_selectionSetShapeWeight
      (ObjectRef := ObjectRef) schema variableValues parentType sources
      specFuels selectionSet)

theorem scheduleExpectedCollectedGroups_rawShapeWeight_le
    (schema : Schema) (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (Name × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRawShapeWeight schema
        (groups.foldl
          (fun queue group =>
            enqueueExpectedSegment
              (scheduleKeyForFields parentType group.fst group.snd)
              {
                segment :=
                  {
                    sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd
                  }
                specFuels := specFuels
              }
              queue)
          queue)
      <= expectedScheduleQueueRawShapeWeight schema queue
          + collectedGroupsShapeWeight schema parentType groups := by
  induction groups generalizing queue with
  | nil =>
      simp [collectedGroupsShapeWeight, collectedGroupsScheduleShapes,
        scheduleFieldShapeSetWeight]
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hhead :=
        expectedScheduleQueueRawShapeWeight_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema
          (scheduleKeyForFields parentType responseName fields)
          { segment :=
              { sources := sources
                childSelectionSet := childSelectionSetForFields fields }
            specFuels := specFuels }
          queue
      have htail :=
        ih
          (enqueueExpectedSegment
            (scheduleKeyForFields parentType responseName fields)
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields fields }
              specFuels := specFuels }
            queue)
      have hheadShape :
          scheduleFieldShapeStepWeight schema
              (expectedQueueSegmentShape
                (scheduleKeyForFields parentType responseName fields)
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields fields }
                  specFuels := specFuels }) =
            scheduleFieldShapeStepWeight schema
              (collectedGroupScheduleShape parentType (responseName, fields)) := by
        rfl
      simp [collectedGroupsShapeWeight, collectedGroupsScheduleShapes,
        scheduleFieldShapeSetWeight] at htail ⊢
      rw [hheadShape] at hhead
      omega

theorem scheduleExpectedScope_rawShapeWeight_le
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRawShapeWeight schema
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet queue).fst
      <= expectedScheduleQueueRawShapeWeight schema queue
          + SelectionSet.size selectionSet * (schema.objectTypes.length + 1) := by
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  have hfold : ∀ queue0 : ExpectedScheduleQueue ObjectRef,
      List.foldl
          (fun queue (group : ScheduleKey × List ExecutableField) =>
            enqueueExpectedSegment group.fst
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0
          (groups.map
            (fun group =>
              (scheduleKeyForFields parentType group.fst group.snd, group.snd))) =
        List.foldl
          (fun queue (group : Name × List ExecutableField) =>
            enqueueExpectedSegment
              (scheduleKeyForFields parentType group.fst group.snd)
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0 groups := by
    intro queue0
    induction groups generalizing queue0 with
    | nil =>
        rfl
    | cons group groups ih =>
        exact ih _
  have hscheduled :
      expectedScheduleQueueRawShapeWeight schema
          (List.foldl
            (fun queue (group : Name × List ExecutableField) =>
              enqueueExpectedSegment
                (scheduleKeyForFields parentType group.fst group.snd)
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := specFuels }
                queue)
            queue groups) <=
        expectedScheduleQueueRawShapeWeight schema queue
          + collectedGroupsShapeWeight schema parentType groups :=
    scheduleExpectedCollectedGroups_rawShapeWeight_le
      (ObjectRef := ObjectRef) schema parentType sources specFuels groups queue
  have hgroupsWeight :
      collectedGroupsShapeWeight schema parentType groups <=
        SelectionSet.size selectionSet * (schema.objectTypes.length + 1) := by
    have hnonempty :
        collectedGroupsNonempty groups := by
      simpa [groups] using
        collectFieldsByKey_collectedGroupsNonempty schema variableValues
          parentType selectionSet
    have hshape :=
      collectedGroupsShapeWeight_le_executableGroupsSize schema parentType
        groups hnonempty
    have hsize :=
      collectFieldsByKey_executableGroupsSize_le schema variableValues
        parentType selectionSet
    have hmul :=
      Nat.mul_le_mul_right (schema.objectTypes.length + 1) hsize
    exact Nat.le_trans hshape (by simpa [groups] using hmul)
  unfold scheduleExpectedScope
  simp
  rw [hfold]
  omega

theorem scheduleExpectedScope_rawShapeWeight_le_selectionSetShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    : expectedScheduleQueueRawShapeWeight schema
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet
          ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= selectionSetShapeWeight schema { selectionSet := selectionSet } := by
  simpa [expectedScheduleQueueRawShapeWeight, selectionSetShapeWeight] using
    scheduleExpectedScope_rawShapeWeight_le
      (ObjectRef := ObjectRef) schema variableValues parentType sources
      specFuels selectionSet ([] : ExpectedScheduleQueue ObjectRef)

theorem scheduleExpectedPendingChildWork_fuelsAligned
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueFuelsAligned queue
      -> expectedScheduleQueueFuelsAligned
          (scheduleExpectedPendingChildWork schema variableValues work queue).fst := by
  intro hqueue
  induction work generalizing queue with
  | nil =>
      simpa [scheduleExpectedPendingChildWork] using hqueue
  | cons work rest ih =>
      let head :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      have hhead :
          expectedScheduleQueueFuelsAligned head.fst := by
        have haligned : [work.specFuel].length = [work.work.source].length := by
          simp
        simpa [head] using
          scheduleExpectedScope_fuelsAligned
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue haligned hqueue
      simpa [scheduleExpectedPendingChildWork, head] using ih head.fst hhead

theorem scheduleExpectedPendingChildWork_itemsNonempty
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty queue
      -> expectedScheduleQueueItemsNonempty
          (scheduleExpectedPendingChildWork schema variableValues work queue).fst := by
  intro hqueue
  induction work generalizing queue with
  | nil =>
      simpa [scheduleExpectedPendingChildWork] using hqueue
  | cons work rest ih =>
      let head :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      have hhead :
          expectedScheduleQueueItemsNonempty head.fst := by
        simpa [head] using
          scheduleExpectedScope_itemsNonempty
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue hqueue
      simpa [scheduleExpectedPendingChildWork, head] using ih head.fst hhead

theorem scheduleExpectedPendingChildWork_keysDistinct
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueKeysDistinct
          (scheduleExpectedPendingChildWork schema variableValues work queue).fst := by
  intro hqueue
  induction work generalizing queue with
  | nil =>
      simpa [scheduleExpectedPendingChildWork] using hqueue
  | cons work rest ih =>
      let head :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      have hhead :
          expectedScheduleQueueKeysDistinct head.fst := by
        simpa [head] using
          scheduleExpectedScope_keysDistinct
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue hqueue
      simpa [scheduleExpectedPendingChildWork, head] using ih head.fst hhead

theorem scheduleExpectedPendingChildWork_fieldBudgetReady
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedPendingChildWorkScopeBudgetReady schema work
      -> expectedScheduleQueueFieldBudgetReady schema queue
      -> expectedScheduleQueueFieldBudgetReady schema
          (scheduleExpectedPendingChildWork schema variableValues work queue).fst := by
  intro hwork hqueue
  induction work generalizing queue with
  | nil =>
      simpa [scheduleExpectedPendingChildWork] using hqueue
  | cons work rest ih =>
      let head :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      have hhead :
          expectedScheduleQueueFieldBudgetReady schema head.fst := by
        have hfuel :
            ∀ fuel, fuel ∈ [work.specFuel] ->
              specFuelScopeBudget schema work.work.selectionSet fuel := by
          intro fuel hfuel
          simp at hfuel
          subst fuel
          exact hwork work (by simp)
        simpa [head] using
          scheduleExpectedScope_fieldBudgetReady
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue hfuel hqueue
      have hrestWork :
          expectedPendingChildWorkScopeBudgetReady schema rest := by
        intro childWork hchildWork
        exact hwork childWork (by simp [hchildWork])
      simpa [scheduleExpectedPendingChildWork, head] using
        ih head.fst hrestWork hhead

theorem scheduleExpectedPendingChildWork_shapeWeight_le_unseenShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    : ∀ (work : ExpectedPendingChildWorkList ObjectRef)
        (queue : ExpectedScheduleQueue ObjectRef)
        (seen : List PendingScopeShape),
        expectedScheduleQueueKeysDistinct queue
        -> expectedScheduleQueueContainsPendingScopeShapeList
            schema variableValues queue seen
        -> expectedScheduleQueueShapeWeight schema
              (scheduleExpectedPendingChildWork schema variableValues work queue).fst
            <= expectedScheduleQueueShapeWeight schema queue
                + expectedPendingChildWorkUnseenShapeWeight schema seen work
  | [], queue, seen, _hdistinct, _hseen => by
      simp [scheduleExpectedPendingChildWork,
        expectedPendingChildWorkUnseenShapeWeight,
        expectedPendingChildWorkShapes, pendingScopeShapeUnseenWeight]
  | childWork :: rest, queue, seen, hdistinct, hseen => by
      let shape := expectedPendingChildWorkShape childWork
      let head :=
        scheduleExpectedScope schema variableValues childWork.work.runtimeType
          [childWork.work.source] [childWork.specFuel]
          childWork.work.selectionSet queue
      have hheadDistinct :
          expectedScheduleQueueKeysDistinct head.fst := by
        simpa [head] using
          scheduleExpectedScope_keysDistinct
            (ObjectRef := ObjectRef) schema variableValues
            childWork.work.runtimeType [childWork.work.source]
            [childWork.specFuel] childWork.work.selectionSet queue hdistinct
      cases hseenShape : pendingScopeShapeMemberBool shape seen with
      | true =>
          have hseenShapeLiteral :
              pendingScopeShapeMemberBool
                { runtimeType := childWork.work.runtimeType
                  selectionSet := childWork.work.selectionSet } seen = true := by
            simpa [shape, expectedPendingChildWorkShape] using hseenShape
          have hshapeContains :
              expectedScheduleQueueContainsPendingScopeShape
                schema variableValues queue shape :=
            hseen shape hseenShape
          have hheadWeight :
              expectedScheduleQueueShapeWeight schema head.fst <=
                expectedScheduleQueueShapeWeight schema queue := by
            simpa [head, shape, expectedPendingChildWorkShape] using
              scheduleExpectedScope_shapeWeight_le_of_contains_groups
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue
                hdistinct hshapeContains
          simp [head] at hheadWeight
          have hseenHead :
              expectedScheduleQueueContainsPendingScopeShapeList
                schema variableValues head.fst seen := by
            simpa [head] using
              scheduleExpectedScope_preserve_contains_pendingScopeShapeList
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue seen
                hseen
          have htail :=
            scheduleExpectedPendingChildWork_shapeWeight_le_unseenShapeWeight
              schema variableValues rest head.fst seen hheadDistinct hseenHead
          simp [scheduleExpectedPendingChildWork, head,
            expectedPendingChildWorkUnseenShapeWeight,
            expectedPendingChildWorkShapes, expectedPendingChildWorkShape,
            pendingScopeShapeUnseenWeight, hseenShapeLiteral] at htail ⊢
          omega
      | false =>
          have hseenShapeLiteral :
              pendingScopeShapeMemberBool
                { runtimeType := childWork.work.runtimeType
                  selectionSet := childWork.work.selectionSet } seen = false := by
            simpa [shape, expectedPendingChildWorkShape] using hseenShape
          have hheadWeight :
              expectedScheduleQueueShapeWeight schema head.fst <=
                expectedScheduleQueueShapeWeight schema queue +
                  pendingScopeShapeStepWeight schema shape := by
            simpa [head, shape, expectedPendingChildWorkShape,
              pendingScopeShapeStepWeight, selectionSetShapeWeight] using
              scheduleExpectedScope_shapeWeight_le
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue
          simp [head, shape, expectedPendingChildWorkShape] at hheadWeight
          have hseenPreserved :
              expectedScheduleQueueContainsPendingScopeShapeList
                schema variableValues head.fst seen := by
            simpa [head] using
              scheduleExpectedScope_preserve_contains_pendingScopeShapeList
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue seen
                hseen
          have hself :
              expectedScheduleQueueContainsPendingScopeShape
                schema variableValues head.fst shape := by
            simpa [head, shape, expectedPendingChildWorkShape] using
              scheduleExpectedScope_contains_pendingScopeShape_self
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue
          have hseenHead :
              expectedScheduleQueueContainsPendingScopeShapeList
                schema variableValues head.fst
                (insertPendingScopeShape shape seen) :=
            expectedScheduleQueueContainsPendingScopeShapeList_insert
              (ObjectRef := ObjectRef) schema variableValues head.fst seen
              shape hseenPreserved hself
          have htail :=
            scheduleExpectedPendingChildWork_shapeWeight_le_unseenShapeWeight
              schema variableValues rest head.fst
              (insertPendingScopeShape shape seen) hheadDistinct hseenHead
          simp [shape, expectedPendingChildWorkShape] at htail
          simp [scheduleExpectedPendingChildWork, head,
            expectedPendingChildWorkUnseenShapeWeight,
            expectedPendingChildWorkShapes, expectedPendingChildWorkShape,
            pendingScopeShapeUnseenWeight, hseenShapeLiteral] at htail ⊢
          omega

theorem scheduleExpectedPendingChildWork_shapeWeight_le_shapeWeight
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueShapeWeight schema
            (scheduleExpectedPendingChildWork schema variableValues work queue).fst
          <= expectedScheduleQueueShapeWeight schema queue
              + expectedPendingChildWorkShapeWeight schema work := by
  intro hdistinct
  have hseen :
      expectedScheduleQueueContainsPendingScopeShapeList
        schema variableValues queue ([] : List PendingScopeShape) := by
    intro shape hshape
    simp [pendingScopeShapeMemberBool] at hshape
  have hbound :=
    scheduleExpectedPendingChildWork_shapeWeight_le_unseenShapeWeight
      (ObjectRef := ObjectRef) schema variableValues work queue
      ([] : List PendingScopeShape) hdistinct hseen
  simpa [expectedPendingChildWorkUnseenShapeWeight_nil_eq_shapeWeight] using
    hbound

theorem scheduleExpectedPendingChildWork_shapeWeight_le_pendingShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    : ∀ (work : ExpectedPendingChildWorkList ObjectRef)
        (queue : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueShapeWeight schema
          (scheduleExpectedPendingChildWork schema variableValues work queue).fst
        <= expectedScheduleQueueShapeWeight schema queue
            + pendingScopeShapeSetWeight schema (expectedPendingChildWorkShapes work)
  | [], queue => by
      simp [scheduleExpectedPendingChildWork,
        expectedPendingChildWorkShapes, pendingScopeShapeSetWeight]
  | childWork :: rest, queue => by
      let head :=
        scheduleExpectedScope schema variableValues childWork.work.runtimeType
          [childWork.work.source] [childWork.specFuel]
          childWork.work.selectionSet queue
      have hhead :
          expectedScheduleQueueShapeWeight schema head.fst <=
            expectedScheduleQueueShapeWeight schema queue +
              selectionSetShapeWeight schema
                { selectionSet := childWork.work.selectionSet } := by
        simpa [head, selectionSetShapeWeight] using
          scheduleExpectedScope_shapeWeight_le
            (ObjectRef := ObjectRef) schema variableValues
            childWork.work.runtimeType [childWork.work.source]
            [childWork.specFuel] childWork.work.selectionSet queue
      have htail :=
        scheduleExpectedPendingChildWork_shapeWeight_le_pendingShapeWeight
          schema variableValues rest head.fst
      simp [head, selectionSetShapeWeight] at hhead
      simp [scheduleExpectedPendingChildWork, head,
        expectedPendingChildWorkShapes, pendingScopeShapeSetWeight,
        expectedPendingChildWorkShape, pendingScopeShapeStepWeight] at htail ⊢
      omega

theorem scheduleExpectedPendingChildWork_drainBudget_le_pendingShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    : expectedScheduleQueueDrainBudget schema []
        (scheduleExpectedPendingChildWork schema variableValues
          work ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= pendingScopeShapeSetWeight schema (expectedPendingChildWorkShapes work) := by
  exact Nat.le_trans
    (expectedScheduleQueueDrainBudget_le_shapeWeight
      (ObjectRef := ObjectRef) schema []
      (scheduleExpectedPendingChildWork schema variableValues
        work ([] : ExpectedScheduleQueue ObjectRef)).fst)
    (by
      simpa [expectedScheduleQueueShapeWeight] using
        scheduleExpectedPendingChildWork_shapeWeight_le_pendingShapeWeight
          (ObjectRef := ObjectRef) schema variableValues work
          ([] : ExpectedScheduleQueue ObjectRef))

theorem scheduleExpectedPendingChildWork_singleton_drainBudget_le_selectionSetShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    : expectedScheduleQueueDrainBudget schema []
        (scheduleExpectedPendingChildWork schema variableValues
          [work] ([] : ExpectedScheduleQueue ObjectRef)).fst
      <= selectionSetShapeWeight schema { selectionSet := work.work.selectionSet } := by
  simpa [scheduleExpectedPendingChildWork] using
    scheduleExpectedScope_drainBudget_le_selectionSetShapeWeight
      (ObjectRef := ObjectRef) schema variableValues work.work.runtimeType
      [work.work.source] [work.specFuel] work.work.selectionSet

def expectedChildQueueForItem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : ExpectedScheduleQueue ObjectRef × ScopeFrames :=
  match schema.lookupField item.key.parentType item.key.fieldName with
  | none => ([], [])
  | some fieldDefinition =>
      scheduleExpectedPendingChildWork schema variableValues
        (expectedPendingChildWorkForItem schema resolvers fieldDefinition.outputType item
          variableValues)
        []

-----------------------------------------------------------------------------------------
-- Runtime-scope drain budget
-----------------------------------------------------------------------------------------

/-!
The older ordered drain budget is intentionally resolver-independent and therefore
conservative. For the final fuel proof we also need this sharper proof-only budget:
it charges child work by `(runtimeType, selectionSet)` shapes that actually arise from
the resolver result for the current item. This mirrors the forward queue more closely:
once a runtime child scope has been scheduled, later cousin values with the same
runtime type and child selection append sources to the existing scheduled field groups.

The `materialized` parameter is still threaded so this budget has the same shape as the
queue transition, but the credit below deliberately remains conservative and does not
subtract materialized runtime scopes. Discounting those scopes would require a separate
level-boundary invariant: after a scope's field groups start draining, the queue no
longer contains all field groups for that materialized scope, but no later cousin should
append to it either. Avoiding that state machine keeps this proof-facing budget simpler.

This is not an executable algorithm change. It is a semantic accounting device for the
queue proof.
-/

abbrev MaterializedPendingScopes := List PendingScopeShape

def materializeExpectedPendingChildWorkScopes
    (work : ExpectedPendingChildWorkList ObjectRef)
    (materialized : MaterializedPendingScopes)
    : MaterializedPendingScopes :=
  (expectedPendingChildWorkShapes work).foldl
    (fun materialized shape => insertPendingScopeShape shape materialized)
    materialized

theorem scheduleExpectedPendingChildWork_preserve_contains_pendingScopeShapeList
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    (seen : List PendingScopeShape)
    : expectedScheduleQueueContainsPendingScopeShapeList schema variableValues queue seen
      -> expectedScheduleQueueContainsPendingScopeShapeList
          schema variableValues
          (scheduleExpectedPendingChildWork schema variableValues work queue).fst
          seen := by
  intro hseen
  induction work generalizing queue with
  | nil =>
      simpa [scheduleExpectedPendingChildWork] using hseen
  | cons childWork rest ih =>
      let head :=
        scheduleExpectedScope schema variableValues childWork.work.runtimeType
          [childWork.work.source] [childWork.specFuel]
          childWork.work.selectionSet queue
      have hhead :
          expectedScheduleQueueContainsPendingScopeShapeList
            schema variableValues head.fst seen := by
        simpa [head] using
          scheduleExpectedScope_preserve_contains_pendingScopeShapeList
            (ObjectRef := ObjectRef) schema variableValues
            childWork.work.runtimeType [childWork.work.source]
            [childWork.specFuel] childWork.work.selectionSet queue seen
            hseen
      simpa [scheduleExpectedPendingChildWork, head] using
        ih head.fst hhead

theorem scheduleExpectedPendingChildWork_contains_materialized_scopes
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    (materialized : MaterializedPendingScopes)
    : expectedScheduleQueueContainsPendingScopeShapeList
        schema variableValues queue materialized
      -> expectedScheduleQueueContainsPendingScopeShapeList
          schema variableValues
          (scheduleExpectedPendingChildWork schema variableValues work queue).fst
          (materializeExpectedPendingChildWorkScopes work materialized) := by
  intro hmaterialized
  induction work generalizing queue materialized with
  | nil =>
      simpa [scheduleExpectedPendingChildWork,
        materializeExpectedPendingChildWorkScopes,
        expectedPendingChildWorkShapes] using hmaterialized
  | cons childWork rest ih =>
      let shape := expectedPendingChildWorkShape childWork
      let head :=
        scheduleExpectedScope schema variableValues childWork.work.runtimeType
          [childWork.work.source] [childWork.specFuel]
          childWork.work.selectionSet queue
      have hpreserved :
          expectedScheduleQueueContainsPendingScopeShapeList
            schema variableValues head.fst materialized := by
        simpa [head] using
          scheduleExpectedScope_preserve_contains_pendingScopeShapeList
            (ObjectRef := ObjectRef) schema variableValues
            childWork.work.runtimeType [childWork.work.source]
            [childWork.specFuel] childWork.work.selectionSet queue
            materialized hmaterialized
      have hself :
          expectedScheduleQueueContainsPendingScopeShape
            schema variableValues head.fst shape := by
        simpa [head, shape, expectedPendingChildWorkShape] using
          scheduleExpectedScope_contains_pendingScopeShape_self
            (ObjectRef := ObjectRef) schema variableValues
            childWork.work.runtimeType [childWork.work.source]
            [childWork.specFuel] childWork.work.selectionSet queue
      have hhead :
          expectedScheduleQueueContainsPendingScopeShapeList
            schema variableValues head.fst
            (insertPendingScopeShape shape materialized) :=
        expectedScheduleQueueContainsPendingScopeShapeList_insert
          (ObjectRef := ObjectRef) schema variableValues head.fst
          materialized shape hpreserved hself
      have htail :=
        ih head.fst (insertPendingScopeShape shape materialized) hhead
      simpa [scheduleExpectedPendingChildWork,
        materializeExpectedPendingChildWorkScopes,
        expectedPendingChildWorkShapes, expectedPendingChildWorkShape,
        head, shape] using htail

def expectedQueueItemRuntimeChildWork
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : ExpectedPendingChildWorkList ObjectRef :=
  match schema.lookupField item.key.parentType item.key.fieldName with
  | none => []
  | some fieldDefinition =>
      expectedPendingChildWorkForItem schema resolvers fieldDefinition.outputType item
        variableValues

def materializeExpectedQueueItemRuntimeScopes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (materialized : MaterializedPendingScopes)
    : MaterializedPendingScopes :=
  materializeExpectedPendingChildWorkScopes
    (expectedQueueItemRuntimeChildWork schema resolvers variableValues item)
    materialized

def possiblePendingScopeShapesForSelectionSet
    (schema : Schema) (fieldType : TypeRef)
    (selectionSet : List Selection)
    : List PendingScopeShape :=
  (schema.getPossibleTypes fieldType.namedType).map
    (fun runtimeType =>
      {
        runtimeType := runtimeType
        selectionSet := selectionSet
      })

def possiblePendingScopeShapesForSelectionSetShapes
    (schema : Schema) (fieldType : TypeRef)
    (shapes : List SelectionSetShape)
    : List PendingScopeShape :=
  (shapes.map
    (fun shape =>
      possiblePendingScopeShapesForSelectionSet schema fieldType
        shape.selectionSet)).flatten

def expectedQueueItemPossibleRuntimeChildShapes
    (schema : Schema) (fieldType : TypeRef)
    (item : ExpectedQueueItem ObjectRef)
    : List PendingScopeShape :=
  pendingScopeShapeSet
    (possiblePendingScopeShapesForSelectionSetShapes schema fieldType
      (expectedQueueItemChildSelectionSetShapes item))

def expectedQueueItemPossibleRuntimeCreditWeight
    (schema : Schema) (_fieldType : TypeRef)
    (item : ExpectedQueueItem ObjectRef)
    : Nat :=
  selectionSetShapeBreadthSetWeight schema (expectedQueueItemChildSelectionSetShapes item)
  * (schema.objectTypes.length + 1)

theorem possiblePendingScopeShapesForSelectionSet_breadthWeight
    (schema : Schema) (fieldType : TypeRef)
    (selectionSet : List Selection)
    : pendingScopeShapeBreadthSetWeight schema
        (possiblePendingScopeShapesForSelectionSet schema fieldType selectionSet)
      = (schema.getPossibleTypes fieldType.namedType).length
        * selectionSetBreadthWeight schema selectionSet := by
  unfold possiblePendingScopeShapesForSelectionSet
  induction schema.getPossibleTypes fieldType.namedType with
  | nil =>
      simp [pendingScopeShapeBreadthSetWeight]
  | cons runtimeType runtimeTypes ih =>
      simp [pendingScopeShapeBreadthSetWeight,
        pendingScopeShapeBreadthStepWeight, ih,
        Nat.succ_mul]
      omega

theorem possiblePendingScopeShapesForSelectionSet_breadthWeight_le
    (schema : Schema) (fieldType : TypeRef)
    (selectionSet : List Selection)
    : (schema.getPossibleTypes fieldType.namedType).length
        <= schema.objectTypes.length + 1
      -> pendingScopeShapeBreadthSetWeight schema
            (possiblePendingScopeShapesForSelectionSet schema fieldType selectionSet)
          <= selectionSetBreadthWeight schema selectionSet
              * (schema.objectTypes.length + 1) := by
  intro hlength
  rw [possiblePendingScopeShapesForSelectionSet_breadthWeight]
  have hmul :=
    Nat.mul_le_mul_right
      (selectionSetBreadthWeight schema selectionSet) hlength
  simpa [Nat.mul_comm] using hmul

theorem possiblePendingScopeShapesForSelectionSetShapes_breadthWeight_le
    (schema : Schema) (fieldType : TypeRef)
    : ∀ shapes : List SelectionSetShape,
        (schema.getPossibleTypes fieldType.namedType).length
          <= schema.objectTypes.length + 1
        -> pendingScopeShapeBreadthSetWeight schema
              (possiblePendingScopeShapesForSelectionSetShapes schema fieldType shapes)
            <= selectionSetShapeBreadthSetWeight schema shapes
                * (schema.objectTypes.length + 1)
  | [], _hlength => by
      simp [possiblePendingScopeShapesForSelectionSetShapes,
        pendingScopeShapeBreadthSetWeight, selectionSetShapeBreadthSetWeight]
  | shape :: shapes, hlength => by
      have hhead :=
        possiblePendingScopeShapesForSelectionSet_breadthWeight_le
          schema fieldType shape.selectionSet hlength
      have htail :=
        possiblePendingScopeShapesForSelectionSetShapes_breadthWeight_le
          schema fieldType shapes hlength
      simp [possiblePendingScopeShapesForSelectionSetShapes] at htail
      simp [possiblePendingScopeShapesForSelectionSetShapes,
        selectionSetShapeBreadthSetWeight, selectionSetShapeBreadthWeight]
      rw [pendingScopeShapeBreadthSetWeight_append]
      rw [Nat.add_mul]
      omega

theorem expectedQueueItemPossibleRuntimeChildShapes_breadthWeight_le_credit
    (schema : Schema) (fieldType : TypeRef)
    (item : ExpectedQueueItem ObjectRef)
    : (schema.getPossibleTypes fieldType.namedType).length
        <= schema.objectTypes.length + 1
      -> pendingScopeShapeBreadthSetWeight schema
            (expectedQueueItemPossibleRuntimeChildShapes schema fieldType item)
          <= expectedQueueItemPossibleRuntimeCreditWeight schema fieldType item := by
  intro hlength
  have hset :=
    pendingScopeShapeBreadthSet_weight_le schema
      (possiblePendingScopeShapesForSelectionSetShapes schema fieldType
        (expectedQueueItemChildSelectionSetShapes item))
  have hraw :=
    possiblePendingScopeShapesForSelectionSetShapes_breadthWeight_le
      schema fieldType (expectedQueueItemChildSelectionSetShapes item)
      hlength
  exact Nat.le_trans
    (by
      simpa [expectedQueueItemPossibleRuntimeChildShapes] using hset)
    (by
      simpa [expectedQueueItemPossibleRuntimeCreditWeight] using hraw)

theorem expectedQueueItemPossibleRuntimeCreditWeight_appendSegment_le
    (schema : Schema) (fieldType : TypeRef)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemPossibleRuntimeCreditWeight schema fieldType
        { item with segments := item.segments ++ [segment] }
      <= expectedQueueItemPossibleRuntimeCreditWeight schema fieldType item
          + selectionSetShapeBreadthWeight schema
              (scheduleFieldShapeChildSelectionSetShape
                (expectedQueueSegmentShape item.key segment))
            * (schema.objectTypes.length + 1) := by
  have hlinear :
      selectionSetShapeBreadthSetWeight schema
          (expectedQueueItemChildSelectionSetShapes
            { item with segments := item.segments ++ [segment] }) <=
        selectionSetShapeBreadthSetWeight schema
          (expectedQueueItemChildSelectionSetShapes item)
          + selectionSetShapeBreadthWeight schema
            (scheduleFieldShapeChildSelectionSetShape
              (expectedQueueSegmentShape item.key segment)) := by
    simp [expectedQueueItemChildSelectionSetShapes,
      expectedQueueItemShapeSet_appendSegment]
    simpa using
      selectionSetShapeBreadthWeight_insertScheduleFieldShape_le
        schema (expectedQueueSegmentShape item.key segment)
        (expectedQueueItemShapeSet item)
  simp [expectedQueueItemPossibleRuntimeCreditWeight] at hlinear ⊢
  have hmul :=
    Nat.mul_le_mul_right (schema.objectTypes.length + 1) hlinear
  simpa [Nat.add_mul] using hmul

theorem expectedQueueItemPossibleRuntimeCreditWeight_appendSegment_le_of_shape_mem
    (schema : Schema) (fieldType : TypeRef)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueSegmentShape item.key segment ∈ expectedQueueItemShapeSet item
      -> expectedQueueItemPossibleRuntimeCreditWeight schema fieldType
            { item with segments := item.segments ++ [segment] }
          <= expectedQueueItemPossibleRuntimeCreditWeight schema fieldType item := by
  intro hmem
  have hshapeSet :
      expectedQueueItemShapeSet
          { item with segments := item.segments ++ [segment] } =
        expectedQueueItemShapeSet item := by
    rw [expectedQueueItemShapeSet_appendSegment]
    exact insertScheduleFieldShape_eq_self_of_mem
      (expectedQueueSegmentShape item.key segment)
      (expectedQueueItemShapeSet item) hmem
  simp [expectedQueueItemPossibleRuntimeCreditWeight,
    expectedQueueItemChildSelectionSetShapes, hshapeSet]

theorem expectedPendingChildWorkForItem_shape_mem_possibleRuntimeChildShapes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    (childWork : ExpectedPendingChildWork ObjectRef)
    : childWork
        ∈ expectedPendingChildWorkForItem schema resolvers fieldType item variableValues
      -> expectedPendingChildWorkShape childWork
          ∈ expectedQueueItemPossibleRuntimeChildShapes schema fieldType item := by
  intro hchildWork
  have hselection :
      { selectionSet := childWork.work.selectionSet } ∈
        expectedQueueItemChildSelectionSetShapes item :=
    expectedPendingChildWorkForItem_selectionSet_mem
      (ObjectRef := ObjectRef) schema resolvers variableValues fieldType item childWork
      hchildWork
  have hruntime :
      childWork.work.runtimeType ∈
        schema.getPossibleTypes fieldType.namedType :=
    expectedPendingChildWorkForItem_runtimeType_mem_possibleTypes
      (ObjectRef := ObjectRef) schema resolvers variableValues fieldType item childWork
      hchildWork
  have hraw :
      expectedPendingChildWorkShape childWork ∈
        possiblePendingScopeShapesForSelectionSetShapes schema fieldType
          (expectedQueueItemChildSelectionSetShapes item) := by
    have hlist :
        possiblePendingScopeShapesForSelectionSet schema fieldType
            childWork.work.selectionSet ∈
          (expectedQueueItemChildSelectionSetShapes item).map
            (fun shape =>
              possiblePendingScopeShapesForSelectionSet schema fieldType
                shape.selectionSet) :=
      List.mem_map.mpr
        ⟨{ selectionSet := childWork.work.selectionSet },
          hselection, rfl⟩
    have hshape :
        expectedPendingChildWorkShape childWork ∈
          possiblePendingScopeShapesForSelectionSet schema fieldType
            childWork.work.selectionSet := by
      simp [possiblePendingScopeShapesForSelectionSet,
        expectedPendingChildWorkShape, hruntime]
    exact List.mem_flatten.mpr ⟨_,
      by simpa [possiblePendingScopeShapesForSelectionSetShapes] using hlist,
      hshape⟩
  exact pendingScopeShape_mem_shapeSet_of_mem
    (expectedPendingChildWorkShape childWork)
    (possiblePendingScopeShapesForSelectionSetShapes schema fieldType
      (expectedQueueItemChildSelectionSetShapes item))
    hraw

theorem expectedPendingChildWorkForItem_breadthShapeWeight_le_possibleRuntimeChildShapes
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    : expectedPendingChildWorkBreadthShapeWeight schema
        (expectedPendingChildWorkForItem schema resolvers fieldType item variableValues)
      <= pendingScopeShapeBreadthSetWeight schema
          (expectedQueueItemPossibleRuntimeChildShapes schema fieldType item) := by
  let work := expectedPendingChildWorkForItem schema resolvers fieldType item variableValues
  let possible := expectedQueueItemPossibleRuntimeChildShapes schema fieldType item
  have hactualNoDup :
      pendingScopeShapeNoDup
        (expectedPendingChildWorkShapeSet work) := by
    simpa [expectedPendingChildWorkShapeSet] using
      pendingScopeShapeNoDup_shapeSet
        (expectedPendingChildWorkShapes work)
  have hrawPossible :
      ∀ shape, shape ∈ expectedPendingChildWorkShapes work ->
        pendingScopeShapeMemberBool shape possible = true := by
    intro shape hshape
    rcases List.mem_map.mp hshape with ⟨childWork, hchildWork, hshapeEq⟩
    subst shape
    have hpossible :
        expectedPendingChildWorkShape childWork ∈ possible := by
      simpa [work, possible] using
        expectedPendingChildWorkForItem_shape_mem_possibleRuntimeChildShapes
          (ObjectRef := ObjectRef) schema resolvers variableValues fieldType item childWork
          hchildWork
    exact pendingScopeShapeMemberBool_true_of_mem
      (expectedPendingChildWorkShape childWork) possible hpossible
  have hsubset :
      ∀ shape,
        pendingScopeShapeMemberBool shape
            (expectedPendingChildWorkShapeSet work) = true ->
          pendingScopeShapeMemberBool shape possible = true := by
    intro shape hshape
    exact pendingScopeShapeMemberBool_shapeSet_of_all
      (expectedPendingChildWorkShapes work) possible hrawPossible
      shape
      (by simpa [expectedPendingChildWorkShapeSet] using hshape)
  simpa [expectedPendingChildWorkBreadthShapeWeight, work, possible] using
    pendingScopeShapeBreadthSetWeight_le_of_memberBool_subset
      schema
      (expectedPendingChildWorkShapeSet work) possible
      hactualNoDup hsubset

def expectedQueueItemRuntimeCreditWeight
    (schema : Schema) (_resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (_materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    : Nat :=
  match schema.lookupField item.key.parentType item.key.fieldName with
  | none => 0
  | some fieldDefinition =>
      expectedQueueItemPossibleRuntimeCreditWeight schema fieldDefinition.outputType item

def expectedScheduleQueueRuntimeDrainBudget
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    : MaterializedPendingScopes -> ExpectedScheduleQueue ObjectRef -> Nat
  | _materialized, [] => 0
  | materialized, item :: rest =>
      expectedQueueItemCurrentShapeCount item
      + expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
      + expectedScheduleQueueRuntimeDrainBudget schema resolvers
          (materializeExpectedQueueItemRuntimeScopes schema resolvers [] item
            materialized)
          rest

theorem expectedScheduleQueueRuntimeDrainBudget_nil
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    : expectedScheduleQueueRuntimeDrainBudget
        (ObjectRef := ObjectRef) schema resolvers materialized []
      = 0 := by
  rfl

theorem expectedScheduleQueueRuntimeDrainBudget_cons
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef) (rest : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized (item :: rest)
      = expectedQueueItemCurrentShapeCount item
        + expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
        + expectedScheduleQueueRuntimeDrainBudget schema resolvers
            (materializeExpectedQueueItemRuntimeScopes schema resolvers [] item
              materialized)
            rest := by
  rfl

theorem expectedQueueItemRuntimeChildWork_lookup_none
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> expectedQueueItemRuntimeChildWork schema resolvers variableValues item = [] := by
  intro hlookup
  simp [expectedQueueItemRuntimeChildWork, hlookup]

theorem expectedQueueItemRuntimeCreditWeight_lookup_none
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> expectedQueueItemRuntimeCreditWeight schema resolvers materialized item = 0 := by
  intro hlookup
  simp [expectedQueueItemRuntimeCreditWeight, hlookup]

theorem materializeExpectedQueueItemRuntimeScopes_lookup_none
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> materializeExpectedQueueItemRuntimeScopes schema resolvers variableValues item
            materialized
          = materialized := by
  intro hlookup
  simp [materializeExpectedQueueItemRuntimeScopes,
    materializeExpectedPendingChildWorkScopes,
    expectedQueueItemRuntimeChildWork_lookup_none
      (ObjectRef := ObjectRef) schema resolvers variableValues item hlookup,
    expectedPendingChildWorkShapes]

theorem expectedQueueItemRuntimeChildWork_lookup_some
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemRuntimeChildWork schema resolvers variableValues item
          = expectedPendingChildWorkForItem schema resolvers
              fieldDefinition.outputType item variableValues := by
  intro hlookup
  simp [expectedQueueItemRuntimeChildWork, hlookup]

theorem expectedQueueItemRuntimeCreditWeight_nil_lookup_some
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemRuntimeCreditWeight schema resolvers [] item
          = expectedQueueItemPossibleRuntimeCreditWeight schema
              fieldDefinition.outputType item := by
  intro hlookup
  simp [expectedQueueItemRuntimeCreditWeight, hlookup]

theorem expectedQueueItemRuntimeCreditWeight_appendSegment_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemRuntimeCreditWeight schema resolvers materialized
        { item with segments := item.segments ++ [segment] }
      <= expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
          + selectionSetShapeBreadthWeight schema
              (scheduleFieldShapeChildSelectionSetShape
                (expectedQueueSegmentShape item.key segment))
            * (schema.objectTypes.length + 1) := by
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedQueueItemRuntimeCreditWeight, hlookup]
  | some fieldDefinition =>
      simpa [expectedQueueItemRuntimeCreditWeight, hlookup] using
        expectedQueueItemPossibleRuntimeCreditWeight_appendSegment_le
          (ObjectRef := ObjectRef) schema fieldDefinition.outputType item
          segment

theorem expectedQueueItemRuntimeCreditWeight_appendSegment_le_of_shape_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueSegmentShape item.key segment ∈ expectedQueueItemShapeSet item
      -> expectedQueueItemRuntimeCreditWeight schema resolvers materialized
            { item with segments := item.segments ++ [segment] }
          <= expectedQueueItemRuntimeCreditWeight schema resolvers materialized item := by
  intro hmem
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedQueueItemRuntimeCreditWeight, hlookup]
  | some fieldDefinition =>
      simpa [expectedQueueItemRuntimeCreditWeight, hlookup] using
        expectedQueueItemPossibleRuntimeCreditWeight_appendSegment_le_of_shape_mem
          (ObjectRef := ObjectRef) schema fieldDefinition.outputType item
          segment hmem

def expectedQueueSegmentRuntimeStepWeight
    (schema : Schema) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    : Nat :=
  1
  + selectionSetShapeBreadthWeight schema
      (scheduleFieldShapeChildSelectionSetShape (expectedQueueSegmentShape key segment))
    * (schema.objectTypes.length + 1)

def scheduleFieldShapeRuntimeStepWeight (schema : Schema) (shape : ScheduleFieldShape)
    : Nat :=
  1
  + selectionSetShapeBreadthWeight schema (scheduleFieldShapeChildSelectionSetShape shape)
    * (schema.objectTypes.length + 1)

def scheduleFieldShapeRuntimeSetWeight (schema : Schema) : List ScheduleFieldShape -> Nat
  | [] => 0
  | shape :: shapes =>
      scheduleFieldShapeRuntimeStepWeight schema shape
      + scheduleFieldShapeRuntimeSetWeight schema shapes

def scheduleFieldShapeMemberBool (shape : ScheduleFieldShape)
    : List ScheduleFieldShape -> Bool
  | [] => false
  | existing :: rest =>
      scheduleFieldShapeEqBool shape existing || scheduleFieldShapeMemberBool shape rest

def scheduleFieldShapeUnseenRuntimeWeight (schema : Schema)
    : List ScheduleFieldShape -> List ScheduleFieldShape -> Nat
  | _seen, [] => 0
  | seen, shape :: shapes =>
      if scheduleFieldShapeMemberBool shape seen then
        scheduleFieldShapeUnseenRuntimeWeight schema seen shapes
      else
        scheduleFieldShapeRuntimeStepWeight schema shape
        + scheduleFieldShapeUnseenRuntimeWeight schema
            (insertScheduleFieldShape shape seen) shapes

def expectedScheduleQueueMergedRuntimeStepWeight
    (schema : Schema) (queue : ExpectedScheduleQueue ObjectRef)
    : Nat :=
  scheduleFieldShapeRuntimeSetWeight schema (expectedScheduleQueueShapeSet queue)

theorem expectedQueueSegmentRuntimeStepWeight_eq_shape
    (schema : Schema) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueSegmentRuntimeStepWeight schema key segment
      = scheduleFieldShapeRuntimeStepWeight schema
          (expectedQueueSegmentShape key segment) := by
  rfl

theorem scheduleFieldShapeRuntimeSetWeight_insert_le
    (schema : Schema) (shape : ScheduleFieldShape)
    (shapes : List ScheduleFieldShape)
    : scheduleFieldShapeRuntimeSetWeight schema (insertScheduleFieldShape shape shapes)
      <= scheduleFieldShapeRuntimeSetWeight schema shapes
          + scheduleFieldShapeRuntimeStepWeight schema shape := by
  induction shapes with
  | nil =>
      simp [insertScheduleFieldShape, scheduleFieldShapeRuntimeSetWeight]
  | cons existing rest ih =>
      cases hshape : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, scheduleFieldShapeRuntimeSetWeight,
            hshape]
      | false =>
          simp [insertScheduleFieldShape, scheduleFieldShapeRuntimeSetWeight,
            hshape]
          omega

theorem scheduleFieldShapeRuntimeSetWeight_insert_le_of_mem
    (schema : Schema) (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        shape ∈ shapes
        -> scheduleFieldShapeRuntimeSetWeight schema
              (insertScheduleFieldShape shape shapes)
            <= scheduleFieldShapeRuntimeSetWeight schema shapes := by
  intro shapes
  induction shapes with
  | nil =>
      intro hmem
      simp at hmem
  | cons existing rest ih =>
      intro hmem
      cases hinsert : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hinsert]
      | false =>
          have htail : shape ∈ rest := by
            have hcases : shape = existing ∨ shape ∈ rest := by
              simpa using hmem
            rcases hcases with hhead | htail
            · subst existing
              simp [scheduleFieldShapeEqBool_self] at hinsert
            · exact htail
          have hrest := ih htail
          simp [insertScheduleFieldShape, hinsert,
            scheduleFieldShapeRuntimeSetWeight]
          omega

theorem scheduleFieldShapeRuntimeSet_foldl_weight_le
    (schema : Schema) (pending shapes : List ScheduleFieldShape)
    : scheduleFieldShapeRuntimeSetWeight schema
        (shapes.foldl (fun shapes shape => insertScheduleFieldShape shape shapes) pending)
      <= scheduleFieldShapeRuntimeSetWeight schema pending
          + scheduleFieldShapeRuntimeSetWeight schema shapes := by
  induction shapes generalizing pending with
  | nil =>
      simp [scheduleFieldShapeRuntimeSetWeight]
  | cons shape shapes ih =>
      have htail :=
        ih (insertScheduleFieldShape shape pending)
      have hinsert :=
        scheduleFieldShapeRuntimeSetWeight_insert_le schema shape pending
      simp [scheduleFieldShapeRuntimeSetWeight] at htail ⊢
      omega

theorem scheduleFieldShapeRuntimeSet_weight_le
    (schema : Schema) (shapes : List ScheduleFieldShape)
    : scheduleFieldShapeRuntimeSetWeight schema (scheduleFieldShapeSet shapes)
      <= scheduleFieldShapeRuntimeSetWeight schema shapes := by
  simpa [scheduleFieldShapeSet, scheduleFieldShapeRuntimeSetWeight] using
    scheduleFieldShapeRuntimeSet_foldl_weight_le schema
      ([] : List ScheduleFieldShape) shapes

theorem scheduleFieldShapeMemberBool_insert_self
    (shape : ScheduleFieldShape)
    (seen : List ScheduleFieldShape)
    : scheduleFieldShapeMemberBool shape (insertScheduleFieldShape shape seen)
      = true := by
  induction seen with
  | nil =>
      simp [insertScheduleFieldShape, scheduleFieldShapeMemberBool,
        scheduleFieldShapeEqBool_self]
  | cons existing rest ih =>
      cases hshape : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, scheduleFieldShapeMemberBool, hshape]
      | false =>
          simp [insertScheduleFieldShape, scheduleFieldShapeMemberBool, hshape]
          exact ih

theorem scheduleFieldShapeMemberBool_insert_of_member
    (shape inserted : ScheduleFieldShape)
    (seen : List ScheduleFieldShape)
    : scheduleFieldShapeMemberBool shape seen = true
      -> scheduleFieldShapeMemberBool shape (insertScheduleFieldShape inserted seen)
          = true := by
  intro hmember
  induction seen with
  | nil =>
      simp [scheduleFieldShapeMemberBool] at hmember
  | cons existing rest ih =>
      cases hinsert : scheduleFieldShapeEqBool inserted existing with
      | true =>
          simpa [insertScheduleFieldShape, scheduleFieldShapeMemberBool,
            hinsert] using hmember
      | false =>
          cases hshape : scheduleFieldShapeEqBool shape existing with
          | true =>
              simp [insertScheduleFieldShape, scheduleFieldShapeMemberBool,
                hinsert, hshape]
          | false =>
              simp [scheduleFieldShapeMemberBool, hshape] at hmember
              simp [insertScheduleFieldShape, scheduleFieldShapeMemberBool,
                hinsert, hshape]
              exact ih hmember

theorem scheduleFieldShapeMemberBool_of_insert_of_ne
    (shape inserted : ScheduleFieldShape)
    (seen : List ScheduleFieldShape)
    : scheduleFieldShapeEqBool shape inserted = false
      -> scheduleFieldShapeMemberBool shape (insertScheduleFieldShape inserted seen)
          = true
      -> scheduleFieldShapeMemberBool shape seen = true := by
  intro hneq hmember
  induction seen with
  | nil =>
      simp [insertScheduleFieldShape, scheduleFieldShapeMemberBool,
        hneq] at hmember
  | cons existing rest ih =>
      cases hinsert : scheduleFieldShapeEqBool inserted existing with
      | true =>
          simpa [insertScheduleFieldShape, scheduleFieldShapeMemberBool,
            hinsert] using hmember
      | false =>
          cases hshape : scheduleFieldShapeEqBool shape existing with
          | true =>
              simp [scheduleFieldShapeMemberBool, hshape]
          | false =>
              simp [insertScheduleFieldShape, scheduleFieldShapeMemberBool,
                hinsert, hshape] at hmember
              simpa [scheduleFieldShapeMemberBool, hshape] using ih hmember

theorem scheduleFieldShapeMemberBool_false_of_insert_ne_head
    (shape existing : ScheduleFieldShape) (rest : List ScheduleFieldShape)
    : scheduleFieldShapeEqBool shape existing = false
      -> scheduleFieldShapeMemberBool shape (existing :: rest) = false
      -> scheduleFieldShapeMemberBool shape rest = false := by
  intro hhead hmember
  simpa [scheduleFieldShapeMemberBool, hhead] using hmember

theorem scheduleFieldShapeMemberBool_insert_eq_self (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        scheduleFieldShapeMemberBool shape shapes = true
        -> insertScheduleFieldShape shape shapes = shapes
  | [], hmember => by
      simp [scheduleFieldShapeMemberBool] at hmember
  | existing :: rest, hmember => by
      cases hhead : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [insertScheduleFieldShape, hhead]
      | false =>
          have htail :
              scheduleFieldShapeMemberBool shape rest = true := by
            simpa [scheduleFieldShapeMemberBool, hhead] using hmember
          have ih :=
            scheduleFieldShapeMemberBool_insert_eq_self shape rest htail
          simp [insertScheduleFieldShape, hhead, ih]

theorem scheduleFieldShapeRuntimeSetWeight_insert_eq_of_member
    (schema : Schema) (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        scheduleFieldShapeMemberBool shape shapes = true
        -> scheduleFieldShapeRuntimeSetWeight schema
              (insertScheduleFieldShape shape shapes)
            = scheduleFieldShapeRuntimeSetWeight schema shapes := by
  intro shapes hmember
  rw [scheduleFieldShapeMemberBool_insert_eq_self shape shapes hmember]

theorem scheduleFieldShapeRuntimeSetWeight_insert_eq_add_of_not_member
    (schema : Schema) (shape : ScheduleFieldShape)
    : ∀ shapes : List ScheduleFieldShape,
        scheduleFieldShapeMemberBool shape shapes = false
        -> scheduleFieldShapeRuntimeSetWeight schema
              (insertScheduleFieldShape shape shapes)
            = scheduleFieldShapeRuntimeSetWeight schema shapes
              + scheduleFieldShapeRuntimeStepWeight schema shape
  | [], _hmember => by
      simp [insertScheduleFieldShape, scheduleFieldShapeRuntimeSetWeight]
  | existing :: rest, hmember => by
      cases hhead : scheduleFieldShapeEqBool shape existing with
      | true =>
          simp [scheduleFieldShapeMemberBool, hhead] at hmember
      | false =>
          have htail :
              scheduleFieldShapeMemberBool shape rest = false :=
            scheduleFieldShapeMemberBool_false_of_insert_ne_head
              shape existing rest hhead hmember
          have ih :=
            scheduleFieldShapeRuntimeSetWeight_insert_eq_add_of_not_member
              schema shape rest htail
          simp [insertScheduleFieldShape, scheduleFieldShapeRuntimeSetWeight,
            hhead, ih]
          omega

theorem scheduleFieldShapeUnseenRuntimeWeight_add_seen_eq_foldl (schema : Schema)
    : ∀ (shapes seen : List ScheduleFieldShape),
        scheduleFieldShapeUnseenRuntimeWeight schema seen shapes
          + scheduleFieldShapeRuntimeSetWeight schema seen
        = scheduleFieldShapeRuntimeSetWeight schema
            (shapes.foldl
              (fun shapes shape => insertScheduleFieldShape shape shapes)
              seen)
  | [], seen => by
      simp [scheduleFieldShapeUnseenRuntimeWeight]
  | shape :: shapes, seen => by
      cases hmember : scheduleFieldShapeMemberBool shape seen with
      | true =>
          have hinsert :=
            scheduleFieldShapeMemberBool_insert_eq_self shape seen hmember
          have htail :=
            scheduleFieldShapeUnseenRuntimeWeight_add_seen_eq_foldl
              schema shapes seen
          simp [scheduleFieldShapeUnseenRuntimeWeight, hmember, hinsert] at htail ⊢
          exact htail
      | false =>
          have htail :=
            scheduleFieldShapeUnseenRuntimeWeight_add_seen_eq_foldl
              schema shapes (insertScheduleFieldShape shape seen)
          have hinsertWeight :=
            scheduleFieldShapeRuntimeSetWeight_insert_eq_add_of_not_member
              schema shape seen hmember
          simp [scheduleFieldShapeUnseenRuntimeWeight, hmember] at htail ⊢
          rw [hinsertWeight] at htail
          omega

theorem scheduleFieldShapeUnseenRuntimeWeight_nil_eq_shapeSetWeight
    (schema : Schema) (shapes : List ScheduleFieldShape)
    : scheduleFieldShapeUnseenRuntimeWeight schema [] shapes
      = scheduleFieldShapeRuntimeSetWeight schema (scheduleFieldShapeSet shapes) := by
  have h :=
    scheduleFieldShapeUnseenRuntimeWeight_add_seen_eq_foldl
      schema shapes ([] : List ScheduleFieldShape)
  simpa [scheduleFieldShapeSet, scheduleFieldShapeRuntimeSetWeight] using h

theorem scheduleFieldShapeUnseenRuntimeWeight_append (schema : Schema)
    : ∀ (left right seen : List ScheduleFieldShape),
        scheduleFieldShapeUnseenRuntimeWeight schema seen (left ++ right)
        = scheduleFieldShapeUnseenRuntimeWeight schema seen left
          + scheduleFieldShapeUnseenRuntimeWeight schema
              (left.foldl (fun seen shape => insertScheduleFieldShape shape seen) seen)
              right
  | [], right, seen => by
      simp [scheduleFieldShapeUnseenRuntimeWeight]
  | shape :: shapes, right, seen => by
      cases hmember : scheduleFieldShapeMemberBool shape seen with
      | true =>
          have hinsert :=
            scheduleFieldShapeMemberBool_insert_eq_self shape seen hmember
          have htail :=
            scheduleFieldShapeUnseenRuntimeWeight_append
              schema shapes right seen
          simp [scheduleFieldShapeUnseenRuntimeWeight, hmember,
            hinsert, htail]
      | false =>
          have htail :=
            scheduleFieldShapeUnseenRuntimeWeight_append
              schema shapes right (insertScheduleFieldShape shape seen)
          simp [scheduleFieldShapeUnseenRuntimeWeight, hmember,
            htail, Nat.add_assoc]

def scheduleFieldShapeSeenExtends (newer older : List ScheduleFieldShape) : Prop :=
  ∀ shape,
    scheduleFieldShapeMemberBool shape older = true
    -> scheduleFieldShapeMemberBool shape newer = true

theorem scheduleFieldShapeSeenExtends_empty (seen : List ScheduleFieldShape)
    : scheduleFieldShapeSeenExtends seen [] := by
  intro shape hmember
  simp [scheduleFieldShapeMemberBool] at hmember

theorem scheduleFieldShapeSeenExtends_insert_both
    {newer older : List ScheduleFieldShape}
    (shape : ScheduleFieldShape)
    : scheduleFieldShapeSeenExtends newer older
      -> scheduleFieldShapeSeenExtends
          (insertScheduleFieldShape shape newer)
          (insertScheduleFieldShape shape older) := by
  intro hextends candidate hcandidate
  cases hsame : scheduleFieldShapeEqBool candidate shape with
  | true =>
      have hcandidateEq : candidate = shape :=
        scheduleFieldShapeEqBool_eq hsame
      subst candidate
      exact scheduleFieldShapeMemberBool_insert_self shape newer
  | false =>
      have holder : scheduleFieldShapeMemberBool candidate older = true :=
        scheduleFieldShapeMemberBool_of_insert_of_ne
          candidate shape older hsame hcandidate
      exact scheduleFieldShapeMemberBool_insert_of_member
        candidate shape newer (hextends candidate holder)

theorem scheduleFieldShapeSeenExtends_insert_old
    {newer older : List ScheduleFieldShape}
    (shape : ScheduleFieldShape)
    : scheduleFieldShapeSeenExtends newer older
      -> scheduleFieldShapeMemberBool shape newer = true
      -> scheduleFieldShapeSeenExtends newer (insertScheduleFieldShape shape older) := by
  intro hextends hshape candidate hcandidate
  cases hsame : scheduleFieldShapeEqBool candidate shape with
  | true =>
      have hcandidateEq : candidate = shape :=
        scheduleFieldShapeEqBool_eq hsame
      subst candidate
      exact hshape
  | false =>
      have holder : scheduleFieldShapeMemberBool candidate older = true :=
        scheduleFieldShapeMemberBool_of_insert_of_ne
          candidate shape older hsame hcandidate
      exact hextends candidate holder

theorem scheduleFieldShapeUnseenRuntimeWeight_mono_seen (schema : Schema)
    : ∀ (shapes newer older : List ScheduleFieldShape),
        scheduleFieldShapeSeenExtends newer older
        -> scheduleFieldShapeUnseenRuntimeWeight schema newer shapes
            <= scheduleFieldShapeUnseenRuntimeWeight schema older shapes
  | [], _newer, _older, _hextends => by
      simp [scheduleFieldShapeUnseenRuntimeWeight]
  | shape :: shapes, newer, older, hextends => by
      cases holder : scheduleFieldShapeMemberBool shape older with
      | true =>
          have hnewer : scheduleFieldShapeMemberBool shape newer = true :=
            hextends shape holder
          have htail :=
            scheduleFieldShapeUnseenRuntimeWeight_mono_seen
              schema shapes newer older hextends
          simp [scheduleFieldShapeUnseenRuntimeWeight, holder, hnewer]
          exact htail
      | false =>
          cases hnewer : scheduleFieldShapeMemberBool shape newer with
          | true =>
              have hextendsTail :
                  scheduleFieldShapeSeenExtends newer
                    (insertScheduleFieldShape shape older) :=
                scheduleFieldShapeSeenExtends_insert_old shape
                  hextends hnewer
              have htail :=
                scheduleFieldShapeUnseenRuntimeWeight_mono_seen
                  schema shapes newer
                  (insertScheduleFieldShape shape older) hextendsTail
              simp [scheduleFieldShapeUnseenRuntimeWeight, holder, hnewer]
              omega
          | false =>
              have hextendsTail :
                  scheduleFieldShapeSeenExtends
                    (insertScheduleFieldShape shape newer)
                    (insertScheduleFieldShape shape older) :=
                scheduleFieldShapeSeenExtends_insert_both shape hextends
              have htail :=
                scheduleFieldShapeUnseenRuntimeWeight_mono_seen
                  schema shapes
                  (insertScheduleFieldShape shape newer)
                  (insertScheduleFieldShape shape older) hextendsTail
              simp [scheduleFieldShapeUnseenRuntimeWeight, holder, hnewer]
              omega

theorem scheduleFieldShapeRuntimeSetWeight_append_set_le
    (schema : Schema) (left right : List ScheduleFieldShape)
    : scheduleFieldShapeRuntimeSetWeight schema (scheduleFieldShapeSet (left ++ right))
      <= scheduleFieldShapeRuntimeSetWeight schema (scheduleFieldShapeSet left)
          + scheduleFieldShapeRuntimeSetWeight schema (scheduleFieldShapeSet right) := by
  have hsplit :=
    scheduleFieldShapeUnseenRuntimeWeight_append schema left right
      ([] : List ScheduleFieldShape)
  have hmono :
      scheduleFieldShapeUnseenRuntimeWeight schema
          (left.foldl
            (fun seen shape => insertScheduleFieldShape shape seen)
            ([] : List ScheduleFieldShape))
          right <=
        scheduleFieldShapeUnseenRuntimeWeight schema
          ([] : List ScheduleFieldShape) right :=
    scheduleFieldShapeUnseenRuntimeWeight_mono_seen schema right
      (left.foldl
        (fun seen shape => insertScheduleFieldShape shape seen)
        ([] : List ScheduleFieldShape))
      ([] : List ScheduleFieldShape)
      (scheduleFieldShapeSeenExtends_empty _)
  rw [← scheduleFieldShapeUnseenRuntimeWeight_nil_eq_shapeSetWeight schema
      (left ++ right)]
  rw [hsplit]
  rw [scheduleFieldShapeUnseenRuntimeWeight_nil_eq_shapeSetWeight schema left]
  rw [← scheduleFieldShapeUnseenRuntimeWeight_nil_eq_shapeSetWeight schema right]
  omega

theorem scheduleFieldShapeRuntimeSetWeight_eq_length_add_childBreadth (schema : Schema)
    : ∀ shapes : List ScheduleFieldShape,
        scheduleFieldShapeRuntimeSetWeight schema shapes
        = shapes.length
          + selectionSetShapeBreadthSetWeight schema
              (shapes.map scheduleFieldShapeChildSelectionSetShape)
            * (schema.objectTypes.length + 1)
  | [] => by
      simp [scheduleFieldShapeRuntimeSetWeight,
        selectionSetShapeBreadthSetWeight]
  | shape :: shapes => by
      have htail :=
        scheduleFieldShapeRuntimeSetWeight_eq_length_add_childBreadth
          schema shapes
      simp [scheduleFieldShapeRuntimeSetWeight,
        scheduleFieldShapeRuntimeStepWeight,
        selectionSetShapeBreadthSetWeight, htail]
      rw [Nat.add_mul]
      omega

theorem expectedQueueItemRuntimeBudget_le_runtimeStepWeight
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    : expectedQueueItemCurrentShapeCount item
        + expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
      <= scheduleFieldShapeRuntimeSetWeight schema (expectedQueueItemShapeSet item) := by
  have hset :=
    scheduleFieldShapeRuntimeSetWeight_eq_length_add_childBreadth
      schema (expectedQueueItemShapeSet item)
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedQueueItemCurrentShapeCount,
        expectedQueueItemRuntimeCreditWeight, hlookup] at hset ⊢
      omega
  | some fieldDefinition =>
      simp [expectedQueueItemCurrentShapeCount,
        expectedQueueItemRuntimeCreditWeight,
        expectedQueueItemPossibleRuntimeCreditWeight,
        expectedQueueItemChildSelectionSetShapes, hlookup] at hset ⊢
      omega

def expectedQueueSegmentsRuntimeStepWeight (schema : Schema) (key : ScheduleKey)
    : List (ExpectedQueueSegment ObjectRef) -> Nat
  | [] => 0
  | segment :: segments =>
      expectedQueueSegmentRuntimeStepWeight schema key segment
      + expectedQueueSegmentsRuntimeStepWeight schema key segments

def expectedScheduleQueueRuntimeStepWeight (schema : Schema)
    : ExpectedScheduleQueue ObjectRef -> Nat
  | [] => 0
  | item :: rest =>
      expectedQueueSegmentsRuntimeStepWeight schema item.key item.segments
      + expectedScheduleQueueRuntimeStepWeight schema rest

theorem expectedQueueItemRuntimeStepBudget_appendSegment_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueItemCurrentShapeCount
          { item with segments := item.segments ++ [segment] }
        + expectedQueueItemRuntimeCreditWeight schema resolvers materialized
            { item with segments := item.segments ++ [segment] }
      <= expectedQueueItemCurrentShapeCount item
          + expectedQueueItemRuntimeCreditWeight schema resolvers materialized item
          + expectedQueueSegmentRuntimeStepWeight schema item.key segment := by
  have hcurrent :=
    expectedQueueItemCurrentShapeCount_appendSegment_le item segment
  have hcredit :=
    expectedQueueItemRuntimeCreditWeight_appendSegment_le
      (ObjectRef := ObjectRef) schema resolvers materialized item segment
  simp [expectedQueueSegmentRuntimeStepWeight]
  omega

theorem expectedQueueItemRuntimeStepBudget_appendSegment_le_of_shape_mem
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (item : ExpectedQueueItem ObjectRef)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueSegmentShape item.key segment ∈ expectedQueueItemShapeSet item
      -> expectedQueueItemCurrentShapeCount
              { item with segments := item.segments ++ [segment] }
            + expectedQueueItemRuntimeCreditWeight schema resolvers materialized
                { item with segments := item.segments ++ [segment] }
          <= expectedQueueItemCurrentShapeCount item
              + expectedQueueItemRuntimeCreditWeight schema resolvers materialized
                  item := by
  intro hmem
  have hcurrent :=
    expectedQueueItemCurrentShapeCount_appendSegment_le_of_shape_mem
      item segment hmem
  have hcredit :=
    expectedQueueItemRuntimeCreditWeight_appendSegment_le_of_shape_mem
      (ObjectRef := ObjectRef) schema resolvers materialized item segment hmem
  omega

theorem expectedScheduleQueueRuntimeDrainBudget_materialized_irrel
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    : ∀ (queue : ExpectedScheduleQueue ObjectRef)
        (left right : MaterializedPendingScopes),
        expectedScheduleQueueRuntimeDrainBudget schema resolvers left queue
        = expectedScheduleQueueRuntimeDrainBudget schema resolvers right queue
  | [], _left, _right => by
      simp [expectedScheduleQueueRuntimeDrainBudget]
  | item :: rest, left, right => by
      have htail :=
        expectedScheduleQueueRuntimeDrainBudget_materialized_irrel
          schema resolvers rest
          (materializeExpectedQueueItemRuntimeScopes schema resolvers [] item left)
          (materializeExpectedQueueItemRuntimeScopes schema resolvers [] item right)
      have hcredit :
          expectedQueueItemRuntimeCreditWeight schema resolvers left item =
            expectedQueueItemRuntimeCreditWeight schema resolvers right item := by
        simp [expectedQueueItemRuntimeCreditWeight]
      simp [expectedScheduleQueueRuntimeDrainBudget, htail, hcredit]

theorem expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
          (enqueueExpectedSegment key segment queue)
        <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
            + expectedQueueSegmentRuntimeStepWeight schema key segment
  | [] => by
      let emptyItem : ExpectedQueueItem ObjectRef :=
        { key := key, segments := [] }
      have hitem :=
        expectedQueueItemRuntimeStepBudget_appendSegment_le
          (ObjectRef := ObjectRef) schema resolvers materialized emptyItem
          segment
      simp [enqueueExpectedSegment, expectedScheduleQueueRuntimeDrainBudget,
        expectedQueueItemCurrentShapeCount, expectedQueueItemShapeSet,
        expectedQueueItemShapes, scheduleFieldShapeSet,
        expectedQueueItemRuntimeCreditWeight,
        expectedQueueItemPossibleRuntimeCreditWeight,
        expectedQueueItemChildSelectionSetShapes,
        selectionSetShapeBreadthSetWeight, emptyItem] at hitem ⊢
      cases hlookup : schema.lookupField key.parentType key.fieldName <;>
        simp [hlookup] at hitem ⊢ <;>
        omega
  | item :: rest => by
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          have hitem :=
            expectedQueueItemRuntimeStepBudget_appendSegment_le
              (ObjectRef := ObjectRef) schema resolvers materialized item
              segment
          have htail :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers
                  (materializeExpectedQueueItemRuntimeScopes schema resolvers []
                    { item with segments := item.segments ++ [segment] }
                    materialized)
                  rest =
                expectedScheduleQueueRuntimeDrainBudget schema resolvers
                  (materializeExpectedQueueItemRuntimeScopes schema resolvers []
                    item materialized)
                  rest :=
            expectedScheduleQueueRuntimeDrainBudget_materialized_irrel
              (ObjectRef := ObjectRef) schema resolvers rest _ _
          simp [enqueueExpectedSegment, hkey,
            expectedScheduleQueueRuntimeDrainBudget, htail]
          omega
      | false =>
          have htail :=
            expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_le
              schema resolvers
              (materializeExpectedQueueItemRuntimeScopes schema resolvers [] item
                materialized)
              key segment rest
          simp [enqueueExpectedSegment, hkey,
            expectedScheduleQueueRuntimeDrainBudget]
          omega

theorem
    expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_le_of_contains_shape
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueKeysDistinct queue
        -> expectedScheduleQueueContainsShape queue
            (expectedQueueSegmentShape key segment)
        -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
              (enqueueExpectedSegment key segment queue)
            <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
  | [], _hdistinct, hcontains => by
      rcases hcontains with ⟨item, hitem, _hkey, _hshape⟩
      simp at hitem
  | item :: rest, hdistinct, hcontains => by
      rcases hdistinct with ⟨habsent, hrestDistinct⟩
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          have hshape :
              expectedQueueSegmentShape item.key segment ∈
                expectedQueueItemShapeSet item := by
            rcases hcontains with ⟨witness, hwitnessMem, hwitnessKey,
              hwitnessShape⟩
            have hcases : witness = item ∨ witness ∈ rest := by
              simpa using hwitnessMem
            rcases hcases with hwitnessHead | hwitnessTail
            · subst witness
              exact hwitnessShape
            · have hcontra :
                  scheduleKeyEqBool item.key witness.key = false :=
                habsent witness hwitnessTail
              have hwitnessKey' :
                  scheduleKeyEqBool item.key witness.key = true := by
                simpa [expectedQueueSegmentShape] using hwitnessKey
              rw [hwitnessKey'] at hcontra
              simp at hcontra
          have hitem :=
            expectedQueueItemRuntimeStepBudget_appendSegment_le_of_shape_mem
              (ObjectRef := ObjectRef) schema resolvers materialized item
              segment hshape
          have htail :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers
                  (materializeExpectedQueueItemRuntimeScopes schema resolvers []
                    { item with segments := item.segments ++ [segment] }
                    materialized)
                  rest =
                expectedScheduleQueueRuntimeDrainBudget schema resolvers
                  (materializeExpectedQueueItemRuntimeScopes schema resolvers []
                    item materialized)
                  rest :=
            expectedScheduleQueueRuntimeDrainBudget_materialized_irrel
              (ObjectRef := ObjectRef) schema resolvers rest _ _
          simp [enqueueExpectedSegment, scheduleKeyEqBool_self,
            expectedScheduleQueueRuntimeDrainBudget, htail]
          omega
      | false =>
          have hkeyFalse : scheduleKeyEqBool key item.key = false := by
            simpa using hkey
          have hrestContains :
              expectedScheduleQueueContainsShape rest
                (expectedQueueSegmentShape key segment) := by
            rcases hcontains with ⟨witness, hwitnessMem, hwitnessKey,
              hwitnessShape⟩
            have hcases : witness = item ∨ witness ∈ rest := by
              simpa using hwitnessMem
            rcases hcases with hwitnessHead | hwitnessTail
            · subst witness
              have hwitnessKey' :
                  scheduleKeyEqBool key item.key = true := by
                simpa [expectedQueueSegmentShape] using hwitnessKey
              rw [hwitnessKey'] at hkeyFalse
              simp at hkeyFalse
            · exact ⟨witness, hwitnessTail, hwitnessKey, hwitnessShape⟩
          have htail :=
            expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_le_of_contains_shape
              schema resolvers
              (materializeExpectedQueueItemRuntimeScopes schema resolvers [] item
                materialized)
              key segment rest hrestDistinct hrestContains
          simp [enqueueExpectedSegment, hkeyFalse,
            expectedScheduleQueueRuntimeDrainBudget]
          exact htail

theorem expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegments_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (key : ScheduleKey) (segments : List (ExpectedQueueSegment ObjectRef))
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
          (enqueueExpectedSegments key segments queue)
        <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
            + expectedQueueSegmentsRuntimeStepWeight schema key segments := by
  intro queue
  induction segments generalizing queue with
  | nil =>
      simp [enqueueExpectedSegments, expectedQueueSegmentsRuntimeStepWeight]
  | cons segment segments ih =>
      have hhead :=
        expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema resolvers materialized key segment
          queue
      have htail :=
        ih (enqueueExpectedSegment key segment queue)
      simp [enqueueExpectedSegments, expectedQueueSegmentsRuntimeStepWeight] at htail ⊢
      omega

theorem expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedScheduleItems_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
        (enqueueExpectedScheduleItems queue items)
      <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
          + expectedScheduleQueueRuntimeStepWeight schema items := by
  induction items generalizing queue with
  | nil =>
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRuntimeStepWeight]
  | cons item rest ih =>
      have hhead :=
        expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegments_le
          (ObjectRef := ObjectRef) schema resolvers materialized item.key
          item.segments queue
      have htail :=
        ih (enqueueExpectedSegments item.key item.segments queue)
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueRuntimeStepWeight]
        at htail ⊢
      omega

def expectedScheduleQueueContainsShapeList
    (queue : ExpectedScheduleQueue ObjectRef)
    (seen : List ScheduleFieldShape)
    : Prop :=
  ∀ shape,
    scheduleFieldShapeMemberBool shape seen = true
    -> expectedScheduleQueueContainsShape queue shape

theorem expectedScheduleQueueContainsShapeList_preserve_enqueueExpectedSegment
    (shapeKey : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    (seen : List ScheduleFieldShape)
    : expectedScheduleQueueContainsShapeList queue seen
      -> expectedScheduleQueueContainsShapeList
          (enqueueExpectedSegment shapeKey segment queue) seen := by
  intro hseen shape hmember
  exact expectedScheduleQueueContainsShape_enqueueExpectedSegment_of_contains
    shape shapeKey segment queue (hseen shape hmember)

theorem expectedScheduleQueueContainsShapeList_insert
    (queue : ExpectedScheduleQueue ObjectRef)
    (seen : List ScheduleFieldShape)
    (shape : ScheduleFieldShape)
    : expectedScheduleQueueContainsShapeList queue seen
      -> expectedScheduleQueueContainsShape queue shape
      -> expectedScheduleQueueContainsShapeList queue
          (insertScheduleFieldShape shape seen) := by
  intro hseen hshape candidate hcandidate
  cases hsame : scheduleFieldShapeEqBool candidate shape with
  | true =>
      have hcandidateEq : candidate = shape :=
        scheduleFieldShapeEqBool_eq hsame
      subst candidate
      exact hshape
  | false =>
      have hseenMember : scheduleFieldShapeMemberBool candidate seen = true :=
        scheduleFieldShapeMemberBool_of_insert_of_ne
          candidate shape seen hsame hcandidate
      exact hseen candidate hseenMember

theorem expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_unseen_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    (seen : List ScheduleFieldShape)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueContainsShapeList queue seen
      ->  let shape := expectedQueueSegmentShape key segment
          expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
              (enqueueExpectedSegment key segment queue)
            <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
                + (if scheduleFieldShapeMemberBool shape seen then
                      0
                    else
                      scheduleFieldShapeRuntimeStepWeight schema shape)
          ∧ expectedScheduleQueueContainsShapeList
              (enqueueExpectedSegment key segment queue)
              (if scheduleFieldShapeMemberBool shape seen then
                  seen
                else
                  insertScheduleFieldShape shape seen) := by
  intro hdistinct hseen
  let shape := expectedQueueSegmentShape key segment
  cases hmember : scheduleFieldShapeMemberBool shape seen with
  | true =>
      have hcontains : expectedScheduleQueueContainsShape queue shape :=
        hseen shape hmember
      have hbudget :=
        expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_le_of_contains_shape
          (ObjectRef := ObjectRef) schema resolvers materialized key segment
          queue hdistinct (by simpa [shape] using hcontains)
      have hcontainsList :
          expectedScheduleQueueContainsShapeList
            (enqueueExpectedSegment key segment queue) seen :=
        expectedScheduleQueueContainsShapeList_preserve_enqueueExpectedSegment
          key segment queue seen hseen
      simpa [shape, hmember, expectedQueueSegmentRuntimeStepWeight_eq_shape]
        using And.intro hbudget hcontainsList
  | false =>
      have hbudget :=
        expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema resolvers materialized key segment
          queue
      have hpreserved :
          expectedScheduleQueueContainsShapeList
            (enqueueExpectedSegment key segment queue) seen :=
        expectedScheduleQueueContainsShapeList_preserve_enqueueExpectedSegment
          key segment queue seen hseen
      have hself :
          expectedScheduleQueueContainsShape
            (enqueueExpectedSegment key segment queue) shape := by
        simpa [shape] using
          expectedScheduleQueueContainsShape_enqueueExpectedSegment_self
            key segment queue
      have hcontainsList :
          expectedScheduleQueueContainsShapeList
            (enqueueExpectedSegment key segment queue)
            (insertScheduleFieldShape shape seen) :=
        expectedScheduleQueueContainsShapeList_insert
          (enqueueExpectedSegment key segment queue) seen shape
          hpreserved hself
      have hbudgetShape :
          expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
              (enqueueExpectedSegment key segment queue) <=
            expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue +
              scheduleFieldShapeRuntimeStepWeight schema
                (expectedQueueSegmentShape key segment) := by
        simpa [expectedQueueSegmentRuntimeStepWeight_eq_shape] using hbudget
      simpa [shape, hmember] using And.intro hbudgetShape hcontainsList

theorem expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegments_unseen_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (key : ScheduleKey)
    : ∀ (segments : List (ExpectedQueueSegment ObjectRef))
        (queue : ExpectedScheduleQueue ObjectRef)
        (seen : List ScheduleFieldShape),
        expectedScheduleQueueKeysDistinct queue
        -> expectedScheduleQueueContainsShapeList queue seen
        -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                (enqueueExpectedSegments key segments queue)
              <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                    queue
                  + scheduleFieldShapeUnseenRuntimeWeight schema seen
                      (segments.map (expectedQueueSegmentShape key))
            ∧ expectedScheduleQueueContainsShapeList
                (enqueueExpectedSegments key segments queue)
                ((segments.map (expectedQueueSegmentShape key)).foldl
                  (fun seen shape => insertScheduleFieldShape shape seen)
                  seen)
  | [], queue, seen, _hdistinct, hseen => by
      simp [enqueueExpectedSegments, scheduleFieldShapeUnseenRuntimeWeight,
        hseen]
  | segment :: segments, queue, seen, hdistinct, hseen => by
      let shape := expectedQueueSegmentShape key segment
      let queueAfterHead := enqueueExpectedSegment key segment queue
      have hhead :=
        expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegment_unseen_le
          (ObjectRef := ObjectRef) schema resolvers materialized key segment
          queue seen hdistinct hseen
      have hheadDistinct :
          expectedScheduleQueueKeysDistinct queueAfterHead :=
        enqueueExpectedSegment_keysDistinct key segment queue hdistinct
      cases hmember : scheduleFieldShapeMemberBool shape seen with
      | true =>
          have hbudgetHead :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queueAfterHead <=
                expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queue := by
            simpa [shape, queueAfterHead, hmember] using hhead.1
          have hseenHead :
              expectedScheduleQueueContainsShapeList queueAfterHead seen := by
            simpa [shape, queueAfterHead, hmember] using hhead.2
          have htail :=
            expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegments_unseen_le
              schema resolvers materialized key segments queueAfterHead seen
              hheadDistinct hseenHead
          have htailBudget :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  (List.foldl (fun queue segment =>
                    enqueueExpectedSegment key segment queue)
                    (enqueueExpectedSegment key segment queue) segments) <=
                expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queueAfterHead +
                  scheduleFieldShapeUnseenRuntimeWeight schema seen
                    (segments.map (expectedQueueSegmentShape key)) := by
            simpa [queueAfterHead, enqueueExpectedSegments] using htail.1
          have htailContains :
              expectedScheduleQueueContainsShapeList
                (List.foldl (fun queue segment =>
                  enqueueExpectedSegment key segment queue)
                  (enqueueExpectedSegment key segment queue) segments)
                ((segments.map (expectedQueueSegmentShape key)).foldl
                  (fun seen shape => insertScheduleFieldShape shape seen)
                  seen) := by
            simpa [queueAfterHead, enqueueExpectedSegments] using htail.2
          have hinsert :=
            scheduleFieldShapeMemberBool_insert_eq_self shape seen hmember
          simp [enqueueExpectedSegments, scheduleFieldShapeUnseenRuntimeWeight,
            shape, hmember, hinsert]
          exact ⟨by omega, htailContains⟩
      | false =>
          have hbudgetHead :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queueAfterHead <=
                expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queue +
                  scheduleFieldShapeRuntimeStepWeight schema shape := by
            simpa [shape, queueAfterHead, hmember] using hhead.1
          have hseenHead :
              expectedScheduleQueueContainsShapeList queueAfterHead
                (insertScheduleFieldShape shape seen) := by
            simpa [shape, queueAfterHead, hmember] using hhead.2
          have htail :=
            expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegments_unseen_le
              schema resolvers materialized key segments queueAfterHead
              (insertScheduleFieldShape shape seen) hheadDistinct hseenHead
          have htailBudget :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  (List.foldl (fun queue segment =>
                    enqueueExpectedSegment key segment queue)
                    (enqueueExpectedSegment key segment queue) segments) <=
                expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queueAfterHead +
                  scheduleFieldShapeUnseenRuntimeWeight schema
                    (insertScheduleFieldShape shape seen)
                    (segments.map (expectedQueueSegmentShape key)) := by
            simpa [queueAfterHead, enqueueExpectedSegments] using htail.1
          have htailContains :
              expectedScheduleQueueContainsShapeList
                (List.foldl (fun queue segment =>
                  enqueueExpectedSegment key segment queue)
                  (enqueueExpectedSegment key segment queue) segments)
                ((segments.map (expectedQueueSegmentShape key)).foldl
                  (fun seen shape => insertScheduleFieldShape shape seen)
                  (insertScheduleFieldShape shape seen)) := by
            simpa [queueAfterHead, enqueueExpectedSegments] using htail.2
          have hbudgetHeadShape :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queueAfterHead <=
                expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queue +
                  scheduleFieldShapeRuntimeStepWeight schema
                    (expectedQueueSegmentShape key segment) := by
            simpa [shape] using hbudgetHead
          have htailBudgetShape :
              expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  (List.foldl (fun queue segment =>
                    enqueueExpectedSegment key segment queue)
                    (enqueueExpectedSegment key segment queue) segments) <=
                expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                  queueAfterHead +
                  scheduleFieldShapeUnseenRuntimeWeight schema
                    (insertScheduleFieldShape
                      (expectedQueueSegmentShape key segment) seen)
                    (segments.map (expectedQueueSegmentShape key)) := by
            simpa [shape] using htailBudget
          simp [enqueueExpectedSegments, scheduleFieldShapeUnseenRuntimeWeight,
            shape, hmember]
          exact ⟨by omega, htailContains⟩

theorem expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedScheduleItems_unseen_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    : ∀ (items queue : ExpectedScheduleQueue ObjectRef) (seen : List ScheduleFieldShape),
        expectedScheduleQueueKeysDistinct queue
        -> expectedScheduleQueueContainsShapeList queue seen
        -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                (enqueueExpectedScheduleItems queue items)
              <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
                    queue
                  + scheduleFieldShapeUnseenRuntimeWeight schema seen
                      (expectedScheduleQueueShapes items)
            ∧ expectedScheduleQueueContainsShapeList
                (enqueueExpectedScheduleItems queue items)
                ((expectedScheduleQueueShapes items).foldl
                  (fun seen shape => insertScheduleFieldShape shape seen)
                  seen)
  | [], queue, seen, _hdistinct, hseen => by
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueShapes,
        scheduleFieldShapeUnseenRuntimeWeight, hseen]
  | item :: rest, queue, seen, hdistinct, hseen => by
      let queueAfterItem := enqueueExpectedSegments item.key item.segments queue
      let itemShapes := item.segments.map (expectedQueueSegmentShape item.key)
      have hitem :=
        expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedSegments_unseen_le
          (ObjectRef := ObjectRef) schema resolvers materialized item.key
          item.segments queue seen hdistinct hseen
      have hitemDistinct :
          expectedScheduleQueueKeysDistinct queueAfterItem :=
        enqueueExpectedSegments_keysDistinct item.key item.segments queue hdistinct
      have hrest :=
        expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedScheduleItems_unseen_le
          schema resolvers materialized rest queueAfterItem
          (itemShapes.foldl
            (fun seen shape => insertScheduleFieldShape shape seen)
            seen)
          hitemDistinct
          (by simpa [queueAfterItem, itemShapes] using hitem.2)
      have hunseenAppend :=
        scheduleFieldShapeUnseenRuntimeWeight_append schema
          itemShapes (expectedScheduleQueueShapes rest) seen
      have hunseenAppend' :
          scheduleFieldShapeUnseenRuntimeWeight schema seen
              (item.segments.map (expectedQueueSegmentShape item.key) ++
                (rest.map expectedQueueItemShapes).flatten) =
            scheduleFieldShapeUnseenRuntimeWeight schema seen
              (item.segments.map (expectedQueueSegmentShape item.key)) +
              scheduleFieldShapeUnseenRuntimeWeight schema
                ((item.segments.map (expectedQueueSegmentShape item.key)).foldl
                  (fun seen shape => insertScheduleFieldShape shape seen)
                  seen)
                (rest.map expectedQueueItemShapes).flatten := by
        simpa [itemShapes, expectedScheduleQueueShapes] using hunseenAppend
      simp [enqueueExpectedScheduleItems, expectedScheduleQueueShapes,
        expectedQueueItemShapes, queueAfterItem, itemShapes] at hitem hrest ⊢
      rw [hunseenAppend']
      exact ⟨by omega, hrest.2⟩

theorem expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedScheduleItems_merged_le
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (materialized : MaterializedPendingScopes)
    (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized
            (enqueueExpectedScheduleItems queue items)
          <= expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
              + expectedScheduleQueueMergedRuntimeStepWeight schema items := by
  intro hdistinct
  have hseen :
      expectedScheduleQueueContainsShapeList queue ([] : List ScheduleFieldShape) := by
    intro shape hshape
    simp [scheduleFieldShapeMemberBool] at hshape
  have hbudget :=
    expectedScheduleQueueRuntimeDrainBudget_enqueueExpectedScheduleItems_unseen_le
      (ObjectRef := ObjectRef) schema resolvers materialized items queue
      ([] : List ScheduleFieldShape) hdistinct hseen
  simpa [expectedScheduleQueueMergedRuntimeStepWeight,
    expectedScheduleQueueShapeSet,
    scheduleFieldShapeUnseenRuntimeWeight_nil_eq_shapeSetWeight] using
    hbudget.1

def expectedScheduleQueueRuntimeItemStepWeight (schema : Schema)
    : ExpectedScheduleQueue ObjectRef -> Nat
  | [] => 0
  | item :: rest =>
      scheduleFieldShapeRuntimeSetWeight schema (expectedQueueItemShapeSet item)
      + expectedScheduleQueueRuntimeItemStepWeight schema rest

theorem expectedScheduleQueueMergedRuntimeStepWeight_le_runtimeItemStepWeight
    (schema : Schema)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueMergedRuntimeStepWeight schema queue
        <= expectedScheduleQueueRuntimeItemStepWeight schema queue
  | [] => by
      simp [expectedScheduleQueueMergedRuntimeStepWeight,
        expectedScheduleQueueShapeSet, expectedScheduleQueueShapes,
        scheduleFieldShapeSet, scheduleFieldShapeRuntimeSetWeight,
        expectedScheduleQueueRuntimeItemStepWeight]
  | item :: rest => by
      have hsplit :=
        scheduleFieldShapeRuntimeSetWeight_append_set_le schema
          (expectedQueueItemShapes item)
          (expectedScheduleQueueShapes rest)
      have hrest :=
        expectedScheduleQueueMergedRuntimeStepWeight_le_runtimeItemStepWeight
          schema rest
      simp [expectedScheduleQueueMergedRuntimeStepWeight,
        expectedScheduleQueueShapeSet, expectedScheduleQueueShapes,
        expectedQueueItemShapeSet,
        expectedScheduleQueueRuntimeItemStepWeight] at hsplit hrest ⊢
      omega

theorem expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le
    (schema : Schema)
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueRuntimeItemStepWeight schema
          (enqueueExpectedSegment key segment queue)
        <= expectedScheduleQueueRuntimeItemStepWeight schema queue
            + expectedQueueSegmentRuntimeStepWeight schema key segment
  | [] => by
      have hsingle :=
        scheduleFieldShapeRuntimeSetWeight_insert_le schema
          (expectedQueueSegmentShape key segment) []
      simpa [enqueueExpectedSegment,
        expectedScheduleQueueRuntimeItemStepWeight,
        expectedQueueItemShapeSet, expectedQueueItemShapes,
        scheduleFieldShapeSet,
        expectedQueueSegmentRuntimeStepWeight_eq_shape,
        scheduleFieldShapeRuntimeSetWeight] using hsingle
  | item :: rest => by
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          have hitem :
              scheduleFieldShapeRuntimeSetWeight schema
                  (expectedQueueItemShapeSet
                    { item with segments := item.segments ++ [segment] }) <=
                scheduleFieldShapeRuntimeSetWeight schema
                  (expectedQueueItemShapeSet item)
                  + expectedQueueSegmentRuntimeStepWeight schema item.key segment := by
            have hinsert :=
              scheduleFieldShapeRuntimeSetWeight_insert_le schema
                (expectedQueueSegmentShape item.key segment)
                (expectedQueueItemShapeSet item)
            rw [expectedQueueItemShapeSet_appendSegment]
            simpa [expectedQueueSegmentRuntimeStepWeight_eq_shape] using hinsert
          simp [enqueueExpectedSegment, hkey,
            expectedScheduleQueueRuntimeItemStepWeight]
          omega
      | false =>
          have htail :=
            expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le
              schema key segment rest
          simp [enqueueExpectedSegment, hkey,
            expectedScheduleQueueRuntimeItemStepWeight]
          omega

theorem
    expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_head_le_of_shape_mem
    (schema : Schema) (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (item : ExpectedQueueItem ObjectRef) (rest : ExpectedScheduleQueue ObjectRef)
    : scheduleKeyEqBool key item.key = true
      -> expectedQueueSegmentShape item.key segment ∈ expectedQueueItemShapeSet item
      -> expectedScheduleQueueRuntimeItemStepWeight schema
            (enqueueExpectedSegment key segment (item :: rest))
          <= expectedScheduleQueueRuntimeItemStepWeight schema (item :: rest) := by
  intro hkey hmem
  have hkeyEq : key = item.key :=
    scheduleKeyEqBool_eq hkey
  subst key
  have hitem :
      scheduleFieldShapeRuntimeSetWeight schema
          (expectedQueueItemShapeSet
            { item with segments := item.segments ++ [segment] }) <=
        scheduleFieldShapeRuntimeSetWeight schema
          (expectedQueueItemShapeSet item) := by
    rw [expectedQueueItemShapeSet_appendSegment]
    exact scheduleFieldShapeRuntimeSetWeight_insert_le_of_mem
      schema (expectedQueueSegmentShape item.key segment)
      (expectedQueueItemShapeSet item) hmem
  simp [enqueueExpectedSegment, scheduleKeyEqBool_self,
    expectedScheduleQueueRuntimeItemStepWeight]
  omega

theorem
    expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le_of_existing_shape
    (schema : Schema) (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    : ∀ queue : ExpectedScheduleQueue ObjectRef,
        expectedScheduleQueueKeysDistinct queue
        -> (∃ item,
              item ∈ queue
              ∧ scheduleKeyEqBool key item.key = true
              ∧ expectedQueueSegmentShape item.key segment
                ∈ expectedQueueItemShapeSet item)
        -> expectedScheduleQueueRuntimeItemStepWeight schema
              (enqueueExpectedSegment key segment queue)
            <= expectedScheduleQueueRuntimeItemStepWeight schema queue
  | [], _hdistinct, hwitness => by
      rcases hwitness with ⟨item, hitem, _hkey, _hshape⟩
      simp at hitem
  | item :: rest, hdistinct, hwitness => by
      rcases hdistinct with ⟨habsent, hrestDistinct⟩
      cases hkey : scheduleKeyEqBool key item.key with
      | true =>
          have hkeyEq : key = item.key :=
            scheduleKeyEqBool_eq hkey
          subst key
          have hshape :
              expectedQueueSegmentShape item.key segment ∈
                expectedQueueItemShapeSet item := by
            rcases hwitness with ⟨witness, hwitnessMem, hwitnessKey, hwitnessShape⟩
            have hcases : witness = item ∨ witness ∈ rest := by
              simpa using hwitnessMem
            rcases hcases with hwitnessHead | hwitnessTail
            · subst witness
              exact hwitnessShape
            · have hcontra :
                  scheduleKeyEqBool item.key witness.key = false :=
                habsent witness hwitnessTail
              have hwitnessKey' :
                  scheduleKeyEqBool item.key witness.key = true := by
                simpa [expectedQueueSegmentShape] using hwitnessKey
              rw [hwitnessKey'] at hcontra
              simp at hcontra
          exact
            expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_head_le_of_shape_mem
              (ObjectRef := ObjectRef) schema item.key segment item rest
              (scheduleKeyEqBool_self item.key) hshape
      | false =>
          have hkeyFalse : scheduleKeyEqBool key item.key = false := by
            simpa using hkey
          have hrestWitness :
              ∃ restItem, restItem ∈ rest ∧
                scheduleKeyEqBool key restItem.key = true ∧
                  expectedQueueSegmentShape restItem.key segment ∈
                    expectedQueueItemShapeSet restItem := by
            rcases hwitness with ⟨witness, hwitnessMem, hwitnessKey, hwitnessShape⟩
            have hcases : witness = item ∨ witness ∈ rest := by
              simpa using hwitnessMem
            rcases hcases with hwitnessHead | hwitnessTail
            · subst witness
              rw [hwitnessKey] at hkeyFalse
              simp at hkeyFalse
            · exact ⟨witness, hwitnessTail, hwitnessKey, hwitnessShape⟩
          have htail :=
            expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le_of_existing_shape
              schema key segment rest hrestDistinct hrestWitness
          simp [enqueueExpectedSegment, hkeyFalse,
            expectedScheduleQueueRuntimeItemStepWeight]
          exact htail

theorem
    expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le_of_contains_shape
    (schema : Schema) (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueContainsShape queue (expectedQueueSegmentShape key segment)
      -> expectedScheduleQueueRuntimeItemStepWeight schema
            (enqueueExpectedSegment key segment queue)
          <= expectedScheduleQueueRuntimeItemStepWeight schema queue := by
  intro hdistinct hcontains
  exact expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le_of_existing_shape
    (ObjectRef := ObjectRef) schema key segment queue hdistinct
    (by
      rcases hcontains with ⟨item, hitem, hkey, hshape⟩
      have hkeyEq : key = item.key :=
        scheduleKeyEqBool_eq hkey
      subst key
      exact ⟨item, hitem, scheduleKeyEqBool_self item.key, hshape⟩)

theorem scheduleExpectedKeyedGroups_runtimeItemStepWeight_le_of_contains
    (schema : Schema)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    : ∀ (groups : List (ScheduleKey × List ExecutableField))
        (queue : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueKeysDistinct queue
        -> (∀ group,
              group ∈ groups
              -> expectedScheduleQueueContainsShape queue
                  (expectedQueueSegmentShape group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }))
        -> expectedScheduleQueueRuntimeItemStepWeight schema
              (groups.foldl
                (fun queue group =>
                  enqueueExpectedSegment
                    group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }
                    queue)
                queue)
            <= expectedScheduleQueueRuntimeItemStepWeight schema queue
  | [], queue, _hdistinct, _hcontains => by
      simp
  | group :: rest, queue, hdistinct, hcontains => by
      let segment : ExpectedQueueSegment ObjectRef :=
        { segment :=
            { sources := sources
              childSelectionSet := childSelectionSetForFields group.snd }
          specFuels := specFuels }
      let queueAfterHead := enqueueExpectedSegment group.fst segment queue
      have hhead :
          expectedScheduleQueueRuntimeItemStepWeight schema queueAfterHead <=
            expectedScheduleQueueRuntimeItemStepWeight schema queue :=
        expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le_of_contains_shape
          (ObjectRef := ObjectRef) schema group.fst segment queue hdistinct
          (hcontains group (by simp))
      have hheadDistinct :
          expectedScheduleQueueKeysDistinct queueAfterHead :=
        enqueueExpectedSegment_keysDistinct group.fst segment queue hdistinct
      have hrestContains :
          ∀ restGroup, restGroup ∈ rest ->
            expectedScheduleQueueContainsShape queueAfterHead
              (expectedQueueSegmentShape restGroup.fst
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields restGroup.snd }
                  specFuels := specFuels }) := by
        intro restGroup hrestGroup
        exact expectedScheduleQueueContainsShape_enqueueExpectedSegment_of_contains
          (expectedQueueSegmentShape restGroup.fst
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields restGroup.snd }
              specFuels := specFuels })
          group.fst segment queue
          (hcontains restGroup (by simp [hrestGroup]))
      have htail :=
        scheduleExpectedKeyedGroups_runtimeItemStepWeight_le_of_contains
          schema sources specFuels rest queueAfterHead hheadDistinct
          hrestContains
      exact Nat.le_trans (by
        simpa [scheduleExpectedKeyedGroups_runtimeItemStepWeight_le_of_contains,
          segment, queueAfterHead] using htail) hhead

theorem scheduleExpectedScope_runtimeItemStepWeight_le_of_contains_groups
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> (∀ group,
            group ∈ collectFieldsByKey schema variableValues parentType selectionSet
            -> expectedScheduleQueueContainsShape queue
                (collectedGroupScheduleShape parentType group))
      -> expectedScheduleQueueRuntimeItemStepWeight schema
            (scheduleExpectedScope schema variableValues parentType
              sources specFuels selectionSet queue).fst
          <= expectedScheduleQueueRuntimeItemStepWeight schema queue := by
  intro hdistinct hcontains
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let keyedGroups : List (ScheduleKey × List ExecutableField) :=
    groups.map
      (fun group =>
        (scheduleKeyForFields parentType group.fst group.snd, group.snd))
  have hkeyedContains :
      ∀ keyedGroup, keyedGroup ∈ keyedGroups ->
        expectedScheduleQueueContainsShape queue
          (expectedQueueSegmentShape keyedGroup.fst
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields keyedGroup.snd }
              specFuels := specFuels }) := by
    intro keyedGroup hkeyedGroup
    rcases List.mem_map.mp hkeyedGroup with ⟨group, hgroup, rfl⟩
    have hgroupContains :
        expectedScheduleQueueContainsShape queue
          (collectedGroupScheduleShape parentType group) :=
      hcontains group (by simpa [groups] using hgroup)
    simpa [collectedGroupScheduleShape, expectedQueueSegmentShape] using
      hgroupContains
  have hfold :=
    scheduleExpectedKeyedGroups_runtimeItemStepWeight_le_of_contains
      (ObjectRef := ObjectRef) schema sources specFuels keyedGroups queue
      hdistinct hkeyedContains
  simpa [scheduleExpectedScope, groups, keyedGroups] using hfold

theorem collectedGroupScheduleShape_runtimeStepWeight_le
    (schema : Schema) (parentType responseName : Name)
    (fields : List ExecutableField)
    : fields ≠ []
      -> scheduleFieldShapeRuntimeStepWeight schema
            (collectedGroupScheduleShape parentType (responseName, fields))
          <= executableFieldsBreadthWeight schema fields := by
  intro hfields
  simpa [scheduleFieldShapeRuntimeStepWeight,
    collectedGroupScheduleShape, scheduleFieldShapeChildSelectionSetShape,
    selectionSetShapeBreadthWeight, Nat.mul_comm] using
    childSelectionSetForFields_runtimeStepWeight_le_executableFieldsBreadthWeight
      schema fields hfields

theorem scheduleExpectedCollectedGroups_runtimeItemStepWeight_le
    (schema : Schema) (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (Name × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : collectedGroupsNonempty groups
      -> expectedScheduleQueueRuntimeItemStepWeight schema
            (groups.foldl
              (fun queue group =>
                enqueueExpectedSegment
                  (scheduleKeyForFields parentType group.fst group.snd)
                  {
                    segment :=
                      {
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := specFuels
                  }
                  queue)
              queue)
          <= expectedScheduleQueueRuntimeItemStepWeight schema queue
              + executableGroupsBreadthWeight schema groups := by
  intro hnonempty
  induction groups generalizing queue with
  | nil =>
      simp [executableGroupsBreadthWeight]
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hhead :=
        expectedScheduleQueueRuntimeItemStepWeight_enqueueExpectedSegment_le
          (ObjectRef := ObjectRef) schema
          (scheduleKeyForFields parentType responseName fields)
          { segment :=
              { sources := sources
                childSelectionSet := childSelectionSetForFields fields }
            specFuels := specFuels }
          queue
      have hheadStep :
          expectedQueueSegmentRuntimeStepWeight schema
              (scheduleKeyForFields parentType responseName fields)
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields fields }
                specFuels := specFuels } <=
            executableFieldsBreadthWeight schema fields := by
        simpa [expectedQueueSegmentRuntimeStepWeight_eq_shape,
          expectedQueueSegmentShape, collectedGroupScheduleShape] using
          collectedGroupScheduleShape_runtimeStepWeight_le
            schema parentType responseName fields
            (hnonempty responseName fields (by simp))
      have htailNonempty : collectedGroupsNonempty groups := by
        intro tailResponseName tailFields htailMem
        exact hnonempty tailResponseName tailFields (by simp [htailMem])
      have htail :=
        ih
          (enqueueExpectedSegment
            (scheduleKeyForFields parentType responseName fields)
            { segment :=
                { sources := sources
                  childSelectionSet := childSelectionSetForFields fields }
              specFuels := specFuels }
            queue)
          htailNonempty
      simp [executableGroupsBreadthWeight] at htail ⊢
      omega

theorem scheduleExpectedScope_runtimeItemStepWeight_le
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueRuntimeItemStepWeight schema
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet queue).fst
      <= expectedScheduleQueueRuntimeItemStepWeight schema queue
          + selectionSetBreadthWeight schema selectionSet := by
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  have hfold : ∀ queue0 : ExpectedScheduleQueue ObjectRef,
      List.foldl
          (fun queue (group : ScheduleKey × List ExecutableField) =>
            enqueueExpectedSegment group.fst
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0
          (groups.map
            (fun group =>
              (scheduleKeyForFields parentType group.fst group.snd, group.snd))) =
        List.foldl
          (fun queue (group : Name × List ExecutableField) =>
            enqueueExpectedSegment
              (scheduleKeyForFields parentType group.fst group.snd)
              { segment :=
                  { sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd }
                specFuels := specFuels }
              queue)
          queue0 groups := by
    intro queue0
    induction groups generalizing queue0 with
    | nil =>
        rfl
    | cons group groups ih =>
        exact ih _
  have hscheduled :
      expectedScheduleQueueRuntimeItemStepWeight schema
          (List.foldl
            (fun queue (group : Name × List ExecutableField) =>
              enqueueExpectedSegment
                (scheduleKeyForFields parentType group.fst group.snd)
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := specFuels }
                queue)
            queue groups) <=
        expectedScheduleQueueRuntimeItemStepWeight schema queue
          + executableGroupsBreadthWeight schema groups :=
    scheduleExpectedCollectedGroups_runtimeItemStepWeight_le
      (ObjectRef := ObjectRef) schema parentType sources specFuels groups queue
      (by
        simpa [groups] using
          collectFieldsByKey_collectedGroupsNonempty schema variableValues
            parentType selectionSet)
  have hgroupsWeight :
      executableGroupsBreadthWeight schema groups <=
        selectionSetBreadthWeight schema selectionSet := by
    simpa [groups] using
      collectFieldsByKey_executableGroupsBreadthWeight_le
        schema variableValues parentType selectionSet
  unfold scheduleExpectedScope
  simp
  rw [hfold]
  omega

theorem scheduleExpectedPendingChildWork_runtimeItemStepWeight_le_unseenBreadthShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    : ∀ (work : ExpectedPendingChildWorkList ObjectRef)
        (queue : ExpectedScheduleQueue ObjectRef)
        (seen : List PendingScopeShape),
        expectedScheduleQueueKeysDistinct queue
        -> expectedScheduleQueueContainsPendingScopeShapeList
            schema variableValues queue seen
        -> expectedScheduleQueueRuntimeItemStepWeight schema
              (scheduleExpectedPendingChildWork schema variableValues work queue).fst
            <= expectedScheduleQueueRuntimeItemStepWeight schema queue
                + expectedPendingChildWorkUnseenBreadthShapeWeight schema seen work
  | [], queue, seen, _hdistinct, _hseen => by
      simp [scheduleExpectedPendingChildWork,
        expectedPendingChildWorkUnseenBreadthShapeWeight,
        expectedPendingChildWorkShapes, pendingScopeShapeBreadthUnseenWeight]
  | childWork :: rest, queue, seen, hdistinct, hseen => by
      let shape := expectedPendingChildWorkShape childWork
      let head :=
        scheduleExpectedScope schema variableValues childWork.work.runtimeType
          [childWork.work.source] [childWork.specFuel]
          childWork.work.selectionSet queue
      have hheadDistinct :
          expectedScheduleQueueKeysDistinct head.fst := by
        simpa [head] using
          scheduleExpectedScope_keysDistinct
            (ObjectRef := ObjectRef) schema variableValues
            childWork.work.runtimeType [childWork.work.source]
            [childWork.specFuel] childWork.work.selectionSet queue hdistinct
      cases hseenShape : pendingScopeShapeMemberBool shape seen with
      | true =>
          have hseenShapeLiteral :
              pendingScopeShapeMemberBool
                { runtimeType := childWork.work.runtimeType
                  selectionSet := childWork.work.selectionSet } seen = true := by
            simpa [shape, expectedPendingChildWorkShape] using hseenShape
          have hshapeContains :
              expectedScheduleQueueContainsPendingScopeShape
                schema variableValues queue shape :=
            hseen shape hseenShape
          have hheadWeight :
              expectedScheduleQueueRuntimeItemStepWeight schema head.fst <=
                expectedScheduleQueueRuntimeItemStepWeight schema queue := by
            simpa [head, shape, expectedPendingChildWorkShape] using
              scheduleExpectedScope_runtimeItemStepWeight_le_of_contains_groups
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue
                hdistinct hshapeContains
          have hseenHead :
              expectedScheduleQueueContainsPendingScopeShapeList
                schema variableValues head.fst seen := by
            simpa [head] using
              scheduleExpectedScope_preserve_contains_pendingScopeShapeList
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue seen
                hseen
          have htail :=
            scheduleExpectedPendingChildWork_runtimeItemStepWeight_le_unseenBreadthShapeWeight
              schema variableValues rest head.fst seen hheadDistinct hseenHead
          have hheadWeight' := hheadWeight
          simp [head] at hheadWeight' htail
          simp [scheduleExpectedPendingChildWork,
            expectedPendingChildWorkUnseenBreadthShapeWeight,
            expectedPendingChildWorkShapes, expectedPendingChildWorkShape,
            pendingScopeShapeBreadthUnseenWeight, hseenShapeLiteral] at htail ⊢
          omega
      | false =>
          have hseenShapeLiteral :
              pendingScopeShapeMemberBool
                { runtimeType := childWork.work.runtimeType
                  selectionSet := childWork.work.selectionSet } seen = false := by
            simpa [shape, expectedPendingChildWorkShape] using hseenShape
          have hheadWeight :
              expectedScheduleQueueRuntimeItemStepWeight schema head.fst <=
                expectedScheduleQueueRuntimeItemStepWeight schema queue +
                  pendingScopeShapeBreadthStepWeight schema shape := by
            simpa [head, shape, expectedPendingChildWorkShape,
              pendingScopeShapeBreadthStepWeight] using
              scheduleExpectedScope_runtimeItemStepWeight_le
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue
          have hseenPreserved :
              expectedScheduleQueueContainsPendingScopeShapeList
                schema variableValues head.fst seen := by
            simpa [head] using
              scheduleExpectedScope_preserve_contains_pendingScopeShapeList
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue seen
                hseen
          have hself :
              expectedScheduleQueueContainsPendingScopeShape
                schema variableValues head.fst shape := by
            simpa [head, shape, expectedPendingChildWorkShape] using
              scheduleExpectedScope_contains_pendingScopeShape_self
                (ObjectRef := ObjectRef) schema variableValues
                childWork.work.runtimeType [childWork.work.source]
                [childWork.specFuel] childWork.work.selectionSet queue
          have hseenHead :
              expectedScheduleQueueContainsPendingScopeShapeList
                schema variableValues head.fst
                (insertPendingScopeShape shape seen) :=
            expectedScheduleQueueContainsPendingScopeShapeList_insert
              (ObjectRef := ObjectRef) schema variableValues head.fst seen
              shape hseenPreserved hself
          have htail :=
            scheduleExpectedPendingChildWork_runtimeItemStepWeight_le_unseenBreadthShapeWeight
              schema variableValues rest head.fst
              (insertPendingScopeShape shape seen) hheadDistinct hseenHead
          have hheadWeight' := hheadWeight
          simp [head] at hheadWeight' htail
          simp [shape, expectedPendingChildWorkShape] at hheadWeight' htail
          simp [scheduleExpectedPendingChildWork,
            expectedPendingChildWorkUnseenBreadthShapeWeight,
            expectedPendingChildWorkShapes, expectedPendingChildWorkShape,
            pendingScopeShapeBreadthUnseenWeight, hseenShapeLiteral] at htail ⊢
          omega

theorem scheduleExpectedPendingChildWork_runtimeItemStepWeight_le_breadthShapeWeight
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueKeysDistinct queue
      -> expectedScheduleQueueRuntimeItemStepWeight schema
            (scheduleExpectedPendingChildWork schema variableValues work queue).fst
          <= expectedScheduleQueueRuntimeItemStepWeight schema queue
              + expectedPendingChildWorkBreadthShapeWeight schema work := by
  intro hdistinct
  have hseen :
      expectedScheduleQueueContainsPendingScopeShapeList
        schema variableValues queue ([] : List PendingScopeShape) := by
    intro shape hshape
    simp [pendingScopeShapeMemberBool] at hshape
  have hbound :=
    scheduleExpectedPendingChildWork_runtimeItemStepWeight_le_unseenBreadthShapeWeight
      (ObjectRef := ObjectRef) schema variableValues work queue
      ([] : List PendingScopeShape) hdistinct hseen
  simpa [expectedPendingChildWorkUnseenBreadthShapeWeight_nil_eq_shapeWeight] using
    hbound

theorem expectedScheduleQueueRuntimeDrainBudget_le_itemStepWeight
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    : ∀ (materialized : MaterializedPendingScopes)
        (queue : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueRuntimeDrainBudget schema resolvers materialized queue
        <= expectedScheduleQueueRuntimeItemStepWeight schema queue
  | _materialized, [] => by
      simp [expectedScheduleQueueRuntimeDrainBudget,
        expectedScheduleQueueRuntimeItemStepWeight]
  | materialized, item :: rest => by
      have hitem :=
        expectedQueueItemRuntimeBudget_le_runtimeStepWeight
          (ObjectRef := ObjectRef) schema resolvers materialized item
      have hrest :=
        expectedScheduleQueueRuntimeDrainBudget_le_itemStepWeight
          schema resolvers
          (materializeExpectedQueueItemRuntimeScopes schema resolvers [] item
            materialized)
          rest
      simp [expectedScheduleQueueRuntimeDrainBudget,
        expectedScheduleQueueRuntimeItemStepWeight]
      omega

theorem expectedChildQueueForItem_fuelsAligned
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : expectedScheduleQueueFuelsAligned
        (expectedChildQueueForItem schema resolvers variableValues item).fst := by
  unfold expectedChildQueueForItem
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedScheduleQueueFuelsAligned]
  | some fieldDefinition =>
      simpa [hlookup] using
        scheduleExpectedPendingChildWork_fuelsAligned
          (ObjectRef := ObjectRef) schema variableValues
          (expectedPendingChildWorkForItem schema resolvers
            fieldDefinition.outputType item variableValues)
          []
          (by simp [expectedScheduleQueueFuelsAligned])

theorem expectedChildQueueForItem_itemsNonempty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : expectedScheduleQueueItemsNonempty
        (expectedChildQueueForItem schema resolvers variableValues item).fst := by
  unfold expectedChildQueueForItem
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedScheduleQueueItemsNonempty]
  | some fieldDefinition =>
      simpa [hlookup] using
        scheduleExpectedPendingChildWork_itemsNonempty
          (ObjectRef := ObjectRef) schema variableValues
          (expectedPendingChildWorkForItem schema resolvers
            fieldDefinition.outputType item variableValues)
          []
          (by simp [expectedScheduleQueueItemsNonempty])

theorem expectedChildQueueForItem_keysDistinct
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : expectedScheduleQueueKeysDistinct
        (expectedChildQueueForItem schema resolvers variableValues item).fst := by
  unfold expectedChildQueueForItem
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      simp [expectedScheduleQueueKeysDistinct]
  | some fieldDefinition =>
      simpa [hlookup] using
        scheduleExpectedPendingChildWork_keysDistinct
          (ObjectRef := ObjectRef) schema variableValues
          (expectedPendingChildWorkForItem schema resolvers
            fieldDefinition.outputType item variableValues)
          []
          (by simp [expectedScheduleQueueKeysDistinct])

theorem expectedChildQueueForItem_rawShapeWeight_lookup_none
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> expectedScheduleQueueRawShapeWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          = 0 := by
  intro hlookup
  simp [expectedChildQueueForItem, hlookup,
    expectedScheduleQueueRawShapeWeight]

theorem expectedChildQueueForItem_shapeWeight_lookup_some_le_pendingShapeWeight
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedScheduleQueueShapeWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedPendingChildWorkShapeWeight schema
              (expectedPendingChildWorkForItem schema resolvers
                fieldDefinition.outputType item variableValues) := by
  intro hlookup
  unfold expectedChildQueueForItem
  simp [hlookup]
  simpa [expectedScheduleQueueShapeWeight] using
    scheduleExpectedPendingChildWork_shapeWeight_le_shapeWeight
      (ObjectRef := ObjectRef) schema variableValues
      (expectedPendingChildWorkForItem schema resolvers
        fieldDefinition.outputType item variableValues)
      ([] : ExpectedScheduleQueue ObjectRef)
      (by simp [expectedScheduleQueueKeysDistinct])

theorem expectedChildQueueForItem_drainBudget_lookup_some_le_pendingShapeWeight
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedScheduleQueueDrainBudget schema []
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedPendingChildWorkShapeWeight schema
              (expectedPendingChildWorkForItem schema resolvers
                fieldDefinition.outputType item variableValues) := by
  intro hlookup
  exact Nat.le_trans
    (expectedScheduleQueueDrainBudget_le_shapeWeight
      (ObjectRef := ObjectRef) schema []
      (expectedChildQueueForItem schema resolvers variableValues item).fst)
    (expectedChildQueueForItem_shapeWeight_lookup_some_le_pendingShapeWeight
      (ObjectRef := ObjectRef) schema resolvers variableValues item
      fieldDefinition hlookup)

theorem
    expectedChildQueueForItem_mergedRuntimeStepWeight_lookup_some_le_pendingBreadthShapeWeight
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedScheduleQueueMergedRuntimeStepWeight schema
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          <= expectedPendingChildWorkBreadthShapeWeight schema
              (expectedPendingChildWorkForItem schema resolvers
                fieldDefinition.outputType item variableValues) := by
  intro hlookup
  let work :=
    expectedPendingChildWorkForItem schema resolvers
      fieldDefinition.outputType item variableValues
  have hmerged :=
    expectedScheduleQueueMergedRuntimeStepWeight_le_runtimeItemStepWeight
      (ObjectRef := ObjectRef) schema
      (scheduleExpectedPendingChildWork schema variableValues
        work ([] : ExpectedScheduleQueue ObjectRef)).fst
  have hitem :=
    scheduleExpectedPendingChildWork_runtimeItemStepWeight_le_breadthShapeWeight
      (ObjectRef := ObjectRef) schema variableValues work
      ([] : ExpectedScheduleQueue ObjectRef)
      (by simp [expectedScheduleQueueKeysDistinct])
  simp [expectedScheduleQueueRuntimeItemStepWeight] at hitem
  unfold expectedChildQueueForItem
  simp [hlookup]
  exact Nat.le_trans hmerged hitem

theorem expectedScheduleQueueToQueue_scheduleExpectedScopeGroups
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (ScheduleKey × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue
        (groups.foldl
          (fun queue group =>
            enqueueExpectedSegment group.fst
              {
                segment :=
                  {
                    sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd
                  }
                specFuels := specFuels
              }
              queue)
          queue)
      = groups.foldl
          (fun queue group =>
            enqueueSegment group.fst
              {
                sources := sources
                childSelectionSet := childSelectionSetForFields group.snd
              }
              queue)
          (expectedScheduleQueueToQueue queue) := by
  induction groups generalizing queue with
  | nil =>
      rfl
  | cons group groups ih =>
      calc
        expectedScheduleQueueToQueue
              (groups.foldl
                (fun queue group =>
                  enqueueExpectedSegment group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet :=
                            childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }
                    queue)
                (enqueueExpectedSegment group.fst
                  {
                    segment :=
                      {
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := specFuels
                  }
                  queue))
            = groups.foldl
                (fun queue group =>
                  enqueueSegment group.fst
                    {
                      sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd
                    }
                    queue)
                (expectedScheduleQueueToQueue
                  (enqueueExpectedSegment group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }
                    queue)) :=
          ih _
        _ = groups.foldl
              (fun queue group =>
                enqueueSegment group.fst
                  {
                    sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd
                  }
                  queue)
              (enqueueSegment group.fst
                {
                  sources := sources
                  childSelectionSet := childSelectionSetForFields group.snd
                }
                (expectedScheduleQueueToQueue queue)) := by
          rw [expectedScheduleQueueToQueue_enqueueExpectedSegment]

theorem expectedScheduleQueueToQueue_scheduleExpectedScope
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue
        (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet queue).fst
      = (scheduleScope schema variableValues parentType sources
          selectionSet (expectedScheduleQueueToQueue queue)).fst := by
  simp [scheduleExpectedScope, scheduleScope,
    expectedScheduleQueueToQueue_scheduleExpectedScopeGroups]

theorem scheduleExpectedScope_frame
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : (scheduleExpectedScope schema variableValues parentType
        sources specFuels selectionSet queue).snd
      = (scheduleScope schema variableValues parentType sources
          selectionSet (expectedScheduleQueueToQueue queue)).snd := by
  simp [scheduleExpectedScope, scheduleScope]

theorem scheduleExpectedScope_frame_independent
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (left right : ExpectedScheduleQueue ObjectRef)
    : (scheduleExpectedScope schema variableValues parentType
        sources specFuels selectionSet left).snd
      = (scheduleExpectedScope schema variableValues parentType
          sources specFuels selectionSet right).snd := by
  simp [scheduleExpectedScope]

theorem expectedScheduleQueueToQueue_scheduleExpectedPendingChildWork
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueToQueue
        (scheduleExpectedPendingChildWork schema variableValues work queue).fst
      = (schedulePendingChildWork schema variableValues
          (expectedPendingChildWorkToPending work)
          (expectedScheduleQueueToQueue queue)).fst := by
  induction work generalizing queue with
  | nil =>
      rfl
  | cons work rest ih =>
      let expectedScheduled :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      let runtimeScheduled :=
        scheduleScope schema variableValues work.work.runtimeType
          [work.work.source] work.work.selectionSet
          (expectedScheduleQueueToQueue queue)
      have hscheduled :
          expectedScheduleQueueToQueue expectedScheduled.fst =
            runtimeScheduled.fst := by
        simpa [expectedScheduled, runtimeScheduled] using
          expectedScheduleQueueToQueue_scheduleExpectedScope
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue
      have htail := ih expectedScheduled.fst
      rw [hscheduled] at htail
      simpa [scheduleExpectedPendingChildWork, schedulePendingChildWork,
        expectedPendingChildWorkToPending, expectedScheduled, runtimeScheduled] using htail

theorem scheduleExpectedPendingChildWork_frames
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : (scheduleExpectedPendingChildWork schema variableValues work queue).snd
      = (schedulePendingChildWork schema variableValues
          (expectedPendingChildWorkToPending work)
          (expectedScheduleQueueToQueue queue)).snd := by
  induction work generalizing queue with
  | nil =>
      rfl
  | cons work rest ih =>
      let expectedScheduled :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      let runtimeScheduled :=
        scheduleScope schema variableValues work.work.runtimeType
          [work.work.source] work.work.selectionSet
          (expectedScheduleQueueToQueue queue)
      have hscheduled :
          expectedScheduleQueueToQueue expectedScheduled.fst =
            runtimeScheduled.fst := by
        simpa [expectedScheduled, runtimeScheduled] using
          expectedScheduleQueueToQueue_scheduleExpectedScope
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue
      have hframe :
          expectedScheduled.snd = runtimeScheduled.snd := by
        simpa [expectedScheduled, runtimeScheduled] using
          scheduleExpectedScope_frame
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue
      have htail := ih expectedScheduled.fst
      rw [hscheduled] at htail
      change expectedScheduled.snd ::
            (scheduleExpectedPendingChildWork schema variableValues rest
              expectedScheduled.fst).snd =
          runtimeScheduled.snd ::
            (schedulePendingChildWork schema variableValues
              (expectedPendingChildWorkToPending rest)
              runtimeScheduled.fst).snd
      rw [hframe]
      exact congrArg (fun tail => runtimeScheduled.snd :: tail) htail

theorem scheduleExpectedPendingChildWork_frames_independent
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (left right : ExpectedScheduleQueue ObjectRef)
    : (scheduleExpectedPendingChildWork schema variableValues work left).snd
      = (scheduleExpectedPendingChildWork schema variableValues work right).snd := by
  induction work generalizing left right with
  | nil =>
      rfl
  | cons work rest ih =>
      let leftHead :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet left
      let rightHead :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet right
      have hhead : leftHead.snd = rightHead.snd := by
        simpa [leftHead, rightHead] using
          scheduleExpectedScope_frame_independent
            (ObjectRef := ObjectRef) schema variableValues work.work.runtimeType
            [work.work.source] [work.specFuel] work.work.selectionSet left right
      have htail : (scheduleExpectedPendingChildWork schema variableValues rest
          leftHead.fst).snd =
        (scheduleExpectedPendingChildWork schema variableValues rest
          rightHead.fst).snd :=
        ih leftHead.fst rightHead.fst
      simp [scheduleExpectedPendingChildWork, leftHead, rightHead, hhead, htail]

-----------------------------------------------------------------------------------------
-- Queue-level semantic predicates
-----------------------------------------------------------------------------------------

def expectedQueueTraceMatchesSpec
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (trace : ExecutionTrace) (queue : ExpectedScheduleQueue ObjectRef)
    : Prop :=
  completeFrames trace.reverse ∅
  = expectedScheduleQueueCompletionStack schema resolvers variableValues queue

def drainLoopMatchesExpectedSpec
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (breadthFuel : Nat)
    (queue : ExpectedScheduleQueue ObjectRef)
    : Prop :=
  expectedQueueTraceMatchesSpec schema resolvers variableValues
    (drainLoop schema (ResolverMap.fromSpecResolvers resolvers) variableValues
      breadthFuel (expectedScheduleQueueToQueue queue))
    queue

def expectedDrainStepMatchesSpec
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : Prop :=
  let expectedChild := expectedChildQueueForItem schema resolvers variableValues item
  let executed :=
    executeScheduleItem schema (ResolverMap.fromSpecResolvers resolvers)
      variableValues item.toScheduleItem
  expectedScheduleQueueToQueue expectedChild.fst = executed.fst
  ∧ completeFrames executed.snd.reverse
      (expectedScheduleQueueCompletionStack schema resolvers variableValues
        (enqueueExpectedScheduleItems rest expectedChild.fst))
    = expectedScheduleQueueCompletionStack schema resolvers variableValues (item :: rest)

def expectedDrainQueueReady
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    : Nat -> ExpectedScheduleQueue ObjectRef -> Prop
  | 0, [] => True
  | 0, _ :: _ => False
  | _fuel + 1, [] => True
  | fuel + 1, item :: rest =>
      expectedScheduleQueueFuelsAligned (item :: rest)
      ∧ expectedScheduleQueueItemsNonempty (item :: rest)
      ∧ expectedScheduleQueueKeysDistinct (item :: rest)
      ∧ expectedQueueItemStepFuelReady schema item
      ∧ expectedDrainQueueReady schema resolvers variableValues fuel
          (enqueueExpectedScheduleItems rest
            (expectedChildQueueForItem schema resolvers variableValues item).fst)

end ExecutionBreadth

end Algorithms

end GraphQL
