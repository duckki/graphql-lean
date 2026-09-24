import Tests.GraphQL.IncrementalDelivery.Execution

/-! Spec algorithm boundaries, response mapping, and caller-controlled lazy batching. -/

namespace GraphQL.IncrementalDelivery.Tests.SpecInterfaces

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Tests

/-- The ordinary response remains definitionally the main execution model's type. -/
example (response : GraphQL.Execution.Response) : Response := response

example (response : Response) : GraphQL.Execution.Response := response
example (response : Response) : ExecutionResult := .single response

def selectedField : ExecutableField :=
  {
    fieldName := "a",
    arguments := [],
    selectionSet := [],
    directives := [],
    deferUsage := none
  }

/-! ExecuteExecutionPlan consumes the supplied partitions. It must not rebuild a plan from
field metadata: this immediate field is deliberately placed in a task here.
-/

#guard
  let supplied : ExecutionPlan :=
    { newCollectedFieldsMaps := [([], [("alias", [selectedField])])] }
  let (completed, nextKey) :=
    (executeExecutionPlan schema resolvers [] 5 "Query" (.object "Query" 0)
      [] supplied).run
      0
  same completed.result (.ok ([], 0)) && completed.work.size == 1 && nextKey == 0

/-! In normal callers, planning is explicit and the same field executes immediately. -/

#guard
  let supplied := buildExecutionPlan [("alias", [selectedField])]
  let completed :=
    ((executeExecutionPlan schema resolvers [] 5 "Query" (.object "Query" 0)
        [] supplied).run
      0).1
  same completed.result (.ok ([("alias", .scalar "a")], 0)) && completed.work.size == 0

/-! ExecuteField returns a value; ExecuteCollectedFields owns the response-name entry. -/

#guard
  let definition : FieldDefinition := { name := "a", outputType := .named "String" }
  let completed :=
    ((executeField schema resolvers [] 5 "Query" (.object "Query" 0)
        definition "alias" [selectedField]).run
      0).1
  same completed.result (.ok (.scalar "a", 0)) && completed.work.size == 0

/-! The named CompleteListValue is the draft's ordinary item loop, not the stream hook. -/

#guard
  let fields := [{ selectedField with directives := [.stream] }]
  let completed :=
    ((completeListValue schema resolvers [] 5 (.named "String") fields
        [.scalar "x", .scalar "y"] [] 0 [] []).run
      0).1
  same completed.result (.ok ([.scalar "x", .scalar "y"], 0)) && completed.work.size == 0

/-! Composite completion performs its own collect/build/execute sequence, preserving both
immediate data and deferred work at the caller's alias-based path.
-/

mutual
  private def noticePaths : Work → List ResponsePath
    | .empty => []
    | .combine left right => noticePaths left ++ noticePaths right
    | .executionGroup groups _ _ children =>
        groups.map (·.node.path) ++ noticePaths children
    | .stream node items => node.path :: itemNoticePaths items

  private def itemNoticePaths : List (Result ResponseValue × Work) → List ResponsePath
    | [] => []
    | (_, work) :: rest => noticePaths work ++ itemNoticePaths rest
end

#guard
  let fields :=
    [{ selectedField with selectionSet := [field "name", defer [field "age"]] }]
  let (completed, nextKey) :=
    (completeValue schema resolvers [] 10 (.named "User") fields (.object "User" 1)
      [.field "alias"]).run
      0
  same completed.result (.ok (.object [("name", .scalar "name1")], 0))
  && completed.work.size == 1
  && nextKey == 1
  && same (noticePaths completed.work) [[.field "alias"]]

def group : DeliveryNode := { key := 10, path := [.field "user"], label := some "later" }
def stream : DeliveryNode := { key := 20, path := [.field "values"] }

#guard
  let entries : StateM IDState (List IncrementalPendingNotice) :=
    getPendingEntry [group] [stream] ensureID
  let (pending, state) := entries.run {}
  let (id, reused) := ensureID group state
  same pending
    [
      { id := "0", path := group.path, label := group.label },
      { id := "1", path := stream.path }
    ]
  && id == "0"
  && reused.nextID == 2
  && same reused state

#guard
  let initial : StateM IDState (List IncrementalPendingNotice) :=
    getPendingEntry [group] [stream] ensureID
  let (_, ids) := initial.run {}
  let events :=
    [
      WorkEvent.groupValues group
        [{
          path := [.field "user", .field "profile"],
          data := [("name", .scalar "Ada")],
          errors := 2
        }],
      .streamValues stream [{ item := .scalar "x" }, { item := .null, errors := 1 }] []
        [],
      .groupSuccess group [] [],
      .streamFailure stream 3,
      .workQueueTermination
    ]
  let (update, final) := (mapWorkEventBatch events).run ids
  same update
    {
      hasNext := false,
      incremental :=
        [
          .object "0" [("name", .scalar "Ada")] 2 [.field "profile"],
          .list "1" [.scalar "x", .null] 1
        ],
      completed := [{ id := "0" }, { id := "1", errors := 3 }]
    }
  && final.nextID == 2

/-! Installing the mapper consumes no work-event batch and allocates no future ID. -/

#guard
  let mapped :=
    mapIncrementalWorkEventsToResponseEvent (.ofList [[.workQueueTermination]]) {}
  mapped.source.history.isEmpty && mapped.ids.nextID == 0

def first : IncrementalStreamUpdateResult :=
  { hasNext := true, incremental := [.list "0" [.scalar "x"]] }

def last : IncrementalStreamUpdateResult :=
  { hasNext := false, completed := [{ id := "0" }] }

def firstBatch : List WorkEvent := [.streamValues stream [{ item := .scalar "x" }] [] []]
def lastBatch : List WorkEvent := [.streamSuccess stream, .workQueueTermination]

def mapped : ResponseEventStream :=
  mapIncrementalWorkEventsToResponseEvent (.ofList [firstBatch, lastBatch])
    { ids := [(stream.key, "0")], nextID := 1 }

example : mapped.Accepts firstBatch := by
  intro initial h
  exact h.trans ⟨[lastBatch], rfl⟩

/-- Generic fixture witness: a batcher accepts any nonempty admitted upstream group. The
batching algorithm itself belongs to Execution, not to this test helper.
-/
theorem batchAccepts (upstream : ResponseEventStream) (available : List upstream.Input)
    (nonempty : available ≠ []) (admitted : upstream.source.Allows available)
    : (batchIncrementalResults upstream).Accepts available := by
  change ∀ initial : List (List upstream.Input), initial.IsPrefix [available] →
    (∀ group ∈ initial, group ≠ []) ∧ upstream.source.Allows initial.flatten
  intro initial h
  cases initial with
  | nil =>
      refine ⟨by simp, ?_⟩
      intro values hp
      exact admitted values (hp.trans ⟨available, rfl⟩)
  | cons first rest =>
      obtain ⟨sameFirst, prefixRest⟩ := List.cons_prefix_cons.mp h
      have empty := List.prefix_nil.mp prefixRest
      subst rest
      subst first
      exact ⟨by simpa using nonempty, by simpa using admitted⟩

#guard
  let batched := batchIncrementalResults mapped
  let (one, rest) :=
    batched.next [firstBatch]
      (batchAccepts mapped _
        (by simp)
        (by
          intro initial h
          exact h.trans ⟨[lastBatch], rfl⟩))
  let (two, tail) :=
    batched.next [firstBatch, lastBatch]
      (batchAccepts mapped _
        (by simp)
        (by
          intro initial h
          exact h))
  same one first
  && same two (combineIncrementalResults [first, last])
  && rest.source.history.length == 1
  && tail.source.history.length == 1
  && rest.ids.nextID == 1
  && tail.ids.nextID == 1

/-- The batcher works over response producers, not only over the work-event mapper. -/
def plainUpdates : ResponseEventStream :=
  {
    Input := IncrementalStreamUpdateResult,
    source := .ofList [first, last],
    ids := {},
    mapEvent := fun update => pure update
  }

/-! Rebatching is composition of stream transformations, not setting a Boolean flag. -/

#guard
  let once := batchIncrementalResults plainUpdates
  let twice := batchIncrementalResults once
  let allowedOnce := batchAccepts plainUpdates [first, last] (by simp) (fun _ h => h)
  let allowedTwice := batchAccepts once [[first, last]] (by simp) allowedOnce
  same (twice.next [[first, last]] allowedTwice).1
    (combineIncrementalResults [first, last])

/-- A new batching stage begins at the current source position; it never replays prior
input.
-/
def afterFirst : ResponseEventStream :=
  { plainUpdates with source := plainUpdates.source.advance [first] }

#guard
  let batched := batchIncrementalResults afterFirst
  let admitted : afterFirst.source.Allows [last] := by
    intro initial h
    obtain ⟨suffix, h⟩ := h
    refine ⟨suffix, ?_⟩
    change first :: (initial ++ suffix) = [first, last]
    exact congrArg (List.cons first) h
  same (batched.next [last] (batchAccepts afterFirst _ (by simp) admitted)).1 last

/-! All three response-entry lists retain order, and only the final hasNext is used. -/

#guard
  let left : IncrementalStreamUpdateResult :=
    {
      hasNext := true,
      pending := [{ id := "a", path := [] }],
      incremental := [.list "a" [.scalar "x"]],
      completed := [{ id := "old" }]
    }
  let right : IncrementalStreamUpdateResult :=
    {
      hasNext := false,
      pending := [{ id := "b", path := [] }],
      incremental := [.list "b" [.scalar "y"]],
      completed := [{ id := "a" }, { id := "b" }]
    }
  same (combineIncrementalResults [left, right])
    {
      hasNext := false,
      pending := left.pending ++ right.pending,
      incremental := left.incremental ++ right.incremental,
      completed := left.completed ++ right.completed
    }

/-! Changing future events cannot change the initial data and errors. -/

#guard
  let leftScheduler : WorkScheduler :=
    ⟨fun _ =>
      { initialGroups := [group], initialStreams := [], workEventStream := .ofList [] }⟩
  let rightScheduler : WorkScheduler :=
    ⟨fun _ =>
      {
        initialGroups := [stream],
        initialStreams := [],
        workEventStream := .ofList [[.workQueueTermination]]
      }⟩
  match start leftScheduler [field "a", defer [field "b"]],
        start rightScheduler [field "a", defer [field "b"]] with
  | .incremental left _, .incremental right _ =>
      same left.toResponse right.toResponse && !same left.pending right.pending
  | _, _ => false

end GraphQL.IncrementalDelivery.Tests.SpecInterfaces
