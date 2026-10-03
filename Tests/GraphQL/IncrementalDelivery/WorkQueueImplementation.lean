import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Executable reductions at the graph-event, queue, and publisher boundaries. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkQueueImplementation
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def group : DeliveryNode := { ref := 0, path := [] }
private def childGroup : DeliveryNode := { ref := 2, path := [] }
private def stream : DeliveryNode := { ref := 1, path := [] }
private def initialResponse : Response := { data := .object [] }

/-- Test-only fold of raw queue batches, retaining productive batches. -/
private def run (initialWork : ReferenceWorkQueue.Work) (batches : List (List GraphEvent))
    : State × List (List WorkQueueEvent) :=
  batches.foldl
    (fun (state, outputs) batch =>
      let (next, events) := state.handleGraphEvents batch
      (next, if events.isEmpty then outputs else outputs ++ [events]))
    (State.initialize initialWork, [])

/-- The reference conformance statement targets the constructed observable queue. -/
example (h : createWorkQueueForScheduleConforms)
    : ∀ work schedule,
        let queue := createWorkQueueForSchedule work schedule
        ExecutedWork work
        → work.size ≠ 0
        → schedule.ValidFor work
        → queue.Conforms work :=
  h

private def orphanWork : Execution.Work :=
  .combine (.stream stream []) (.executionGroup [] [] (.ok ([], 0)) .empty)

/-- The generated-work premise excludes the ownerless raw-work counterexample. -/
example : ¬ExecutedWork orphanWork := by
  intro generated
  have task : TaskAt orphanWork (.executionGroup [1]) [] none
      (.object [] (.ok ([], 0))) := .executionGroup (.right .root)
  exact (generated.taskOwners_nonempty task) rfl

private def groupWork : Execution.Work :=
  .executionGroup [{ node := group }] [] (.ok ([("x", .scalar "X")], 0)) .empty

private def groupValue : ExecutionGroupValue :=
  { deliveryGroups := [group], path := [], data := [("x", .scalar "X")] }

private def groupSuccess : GraphEvent :=
  .taskSuccess (.executionGroup []) { value := groupValue }

/-- The root task descriptor used by the source-law fixture. -/
private theorem groupTaskAt
    : TaskAt groupWork (.executionGroup []) [group.ref] none
        (.object [] (.ok ([("x", .scalar "X")], 0))) := by
  refine ⟨[{ node := group }], [], .ok ([("x", .scalar "X")], 0), .empty, [], ?_, rfl, rfl⟩
  rfl

/-- The fixture's host event agrees with the finite execution-generated Work. -/
example : groupSuccess.MatchesWork groupWork := by
  refine ⟨[group.ref], none, groupTaskAt, rfl, ?_⟩
  rfl

example : groupSuccess.Ready groupWork [] := by
  refine ⟨[group.ref], none, .object [] (.ok ([("x", .scalar "X")], 0)),
    groupTaskAt, ?_⟩
  intro source h
  cases h

/-- One `TASK_SUCCESS` integrates no children, flushes the group, and terminates. -/
example
    : (run (Work.fromExecution groupWork) [[groupSuccess]]).2
      = [[
          .groupValues group [groupValue],
          .groupSuccess group [] [],
          .workQueueTermination
        ]] := by
  rfl

/-- The separate publisher preserves data, completion, and the terminal flag. -/
example
    : ((ResponseStreamCursor.initialize initialResponse groupWork).2.run
        [[groupSuccess]]).1
      = [{
          hasNext := false
          incremental := [.object "0" [("x", .scalar "X")]]
          completed := [{ id := "0" }]
        }] := by
  rfl

private def failingGroupWork : Execution.Work :=
  .executionGroup [{ node := group }] [] (.error 2) .empty

/-- `TASK_FAILURE` closes the announced group and reports its error count. -/
example
    : (run (Work.fromExecution failingGroupWork)
        [[.taskFailure (.executionGroup []) 2]]).2
      = [[.groupFailure group 2, .workQueueTermination]] := by
  cbv

private def nestedWork : Execution.Work :=
  .executionGroup [{ node := group }] [] (.ok ([], 0))
    (.executionGroup [{ node := childGroup, ancestors := [group] }]
      [] (.ok ([], 0)) .empty)

private def parentSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [])
    {
      value := { deliveryGroups := [group], path := [], data := [] }
      work :=
        Work.fromExecution
          (.executionGroup [{ node := childGroup, ancestors := [group] }]
            [] (.ok ([], 0)) .empty)
          [0]
    }

private def childSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [0])
    { value := { deliveryGroups := [childGroup], path := [], data := [] } }

/-- Child Work enters the queue only when its producer's result arrives. -/
example
    : (run (Work.fromExecution nestedWork) [[parentSuccess], [childSuccess]]).2
      = [
        [
          .groupValues group [{ deliveryGroups := [group], path := [], data := [] }],
          .groupSuccess group [childGroup] []
        ],
        [
          .groupValues childGroup
            [{ deliveryGroups := [childGroup], path := [], data := [] }],
          .groupSuccess childGroup [] [],
          .workQueueTermination
        ]
      ] := by
  rfl

/-- A child result is not a legal host event before WorkQueue starts its group. -/
example : inputsStarted nestedWork [[childSuccess]] = false := by
  rfl

example : inputsStarted nestedWork [[parentSuccess], [childSuccess]] = true := by
  rfl

private def deepGroup : DeliveryNode := { ref := 3, path := [.field "obj"] }

private def sharedWork : Execution.Work :=
  .executionGroup [{ node := group }, { node := deepGroup }]
    [] (.ok ([("x", .scalar "X")], 0)) .empty

private def sharedValue : ExecutionGroupValue :=
  {
    deliveryGroups := [group, deepGroup],
    path := [.field "obj"],
    data := [("x", .scalar "X")]
  }

private def sharedSuccess : GraphEvent :=
  .taskSuccess (.executionGroup []) { value := sharedValue }

private def rawAncestorOwnerWork : Execution.Work :=
  .executionGroup
    [{ node := group }, { node := childGroup, ancestors := [group] }]
    [] (.ok ([("x", .scalar "X")], 0)) .empty

private def rawAncestorOwnerSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [])
    {
      value :=
        {
          deliveryGroups := [group, childGroup], path := [], data := [("x", .scalar "X")]
        }
    }

private theorem rawAncestorOwnerTaskAt
    : TaskAt rawAncestorOwnerWork (.executionGroup []) [group.ref, childGroup.ref] none
        (.object [] (.ok ([("x", .scalar "X")], 0))) := by
  exact .executionGroup .root

/-- The shared-owner regression uses a legal fixed-outcome host settlement. -/
example : rawAncestorOwnerSuccess.MatchesWork rawAncestorOwnerWork := by
  exact ⟨[group.ref, childGroup.ref], none, rawAncestorOwnerTaskAt, rfl, rfl⟩

example : rawAncestorOwnerSuccess.Ready rawAncestorOwnerWork [] := by
  refine ⟨[group.ref, childGroup.ref], none,
    .object [] (.ok ([("x", .scalar "X")], 0)), rawAncestorOwnerTaskAt, ?_⟩
  intro source impossible
  cases impossible

example : inputsStarted rawAncestorOwnerWork [[rawAncestorOwnerSuccess]] = true := by
  rfl

/-- On raw ancestor/co-owner work, an already-accounted child is silently pruned.
Witness: evaluate the handler and final drain; this is not an execution-generated fixture.
-/
example
    : (run (Work.fromExecution rawAncestorOwnerWork) [[rawAncestorOwnerSuccess]]).2
      = [[
          .groupValues group
            [{
              deliveryGroups := [group, childGroup],
              path := [],
              data := [("x", .scalar "X")]
            }],
          .groupSuccess group [] [],
          .workQueueTermination
        ]] := by
  cbv

/-- The silently accounted raw co-owner receives no pending notice. -/
example
    : ((ResponseStreamCursor.initialize initialResponse rawAncestorOwnerWork).2.run
        [[rawAncestorOwnerSuccess]]).1.map
        IncrementalStreamUpdateResult.pending
      = [[]] := by
  cbv

/-- The final drain removes the empty child and terminates this raw fixture.
Witness: direct reduction, without claiming generated-work conformance.
-/
example
    : let final :=
        (run (Work.fromExecution rawAncestorOwnerWork) [[rawAncestorOwnerSuccess]]).1
      (final.groupNode? childGroup.ref).map (fun node => (node.pending, node.tasks))
        = none
      ∧ final.terminated = true := by
  constructor <;> cbv

private def grandchildGroup : DeliveryNode := { ref := 6, path := [] }

private def rawAncestorNestedWork : Execution.Work :=
  .executionGroup
    [{ node := group }, { node := childGroup, ancestors := [group] }]
    [] (.ok ([("x", .scalar "X")], 0))
    (.executionGroup
      [{ node := grandchildGroup, ancestors := [childGroup, group] }]
      [] (.ok ([], 0)) .empty)

private def rawAncestorNestedSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [])
    {
      value :=
        {
          deliveryGroups := [group, childGroup], path := [], data := [("x", .scalar "X")]
        }
      work :=
        Work.fromExecution
          (.executionGroup
            [{ node := grandchildGroup, ancestors := [childGroup, group] }]
            [] (.ok ([], 0)) .empty)
          [0]
    }

/-- Pruning the accounted raw co-owner promotes its still-outstanding descendant. -/
example
    : (run (Work.fromExecution rawAncestorNestedWork) [[rawAncestorNestedSuccess]]).2
      = [[
          .groupValues group
            [{
              deliveryGroups := [group, childGroup],
              path := [],
              data := [("x", .scalar "X")]
            }],
          .groupSuccess group [grandchildGroup] []
        ]] := by
  cbv

/-- The raw WorkQueue attributes the shared value to its triggering group. -/
example
    : ((run (Work.fromExecution sharedWork) [[sharedSuccess]]).2.head?).map List.head?
      = some (some (.groupValues group [sharedValue])) := by
  rfl

/-- The publisher remaps that same value to the deepest announced contributor. -/
example
    : ((ResponseStreamCursor.initialize initialResponse sharedWork).2.run
        [[sharedSuccess]]).1.map
        IncrementalStreamUpdateResult.incremental
      = [[.object "1" [("x", .scalar "X")] 0 []]] := by
  rfl

private def emptyStreamWork : Execution.Work := .stream stream []

/-- An exhausted empty stream retains its pending/completed lifecycle. -/
example
    : (run (Work.fromExecution emptyStreamWork) [[.streamSuccess stream]]).2
      = [[.streamSuccess stream, .workQueueTermination]] := by
  rfl

private def oneItemStreamWork : Execution.Work :=
  .stream stream [(.ok (.scalar "a", 0), .empty)]

private def oneItemEvent : GraphEvent :=
  .streamItems stream [{ occurrence := .item [] 0, value := { item := .scalar "a" } }]

/-- Stream items arrive in a GraphQL.js `STREAM_ITEMS` batch, not as task settlements. -/
example
    : (run (Work.fromExecution oneItemStreamWork)
        [[oneItemEvent, .streamSuccess stream]]).2
      = [[
          .streamValues stream [{ item := .scalar "a" }] [] [],
          .streamSuccess stream,
          .workQueueTermination
        ]] := by
  rfl

private def failingStreamWork : Execution.Work := .stream stream [(.error 1, .empty)]

/-- Stream failure is a graph event in its own right. -/
example
    : (run (Work.fromExecution failingStreamWork) [[.streamFailure stream 1]]).2
      = [[.streamFailure stream 1, .workQueueTermination]] := by
  rfl

private def streamChildWork : Execution.Work :=
  .stream stream
    [(.ok (.scalar "a", 0), .executionGroup [{ node := group }] [] (.ok ([], 0)) .empty)]

private def generatedStreamFailureSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [{ name := "usersStrict", outputType := .list (.nonNull (.named "User")) }]
          },
        .object
          {
            name := "User"
            fields :=
              [
                { name := "required", outputType := .nonNull (.named "String") },
                { name := "name", outputType := .named "String" }
              ]
          }
      ]
  }

private def generatedStreamFailureResolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ field _ source =>
        match field, source with
        | "usersStrict", _ =>
            some (.list [.object "User" 1, .object "User" 2])
        | "required", .object _ 1 => some (.scalar "ok")
        | "required", .object _ _ => none
        | "name", .object _ ref => some (.scalar (toString ref))
        | _, _ => none
    resolve_argumentsEquivalent := by intros; rfl
  }

private def generatedStreamFailureSelections : List Selection :=
  [GraphQL.IncrementalDelivery.Tests.field "usersStrict"
    [
      GraphQL.IncrementalDelivery.Tests.field "required",
      GraphQL.IncrementalDelivery.Tests.defer
        [GraphQL.IncrementalDelivery.Tests.field "name"] (some "child")
    ]
    [.stream]]

private def generatedStreamFailureWork : Execution.Work :=
  ((executeRootSelectionSetCore generatedStreamFailureSchema
      generatedStreamFailureResolvers [] 40 "Query" (.object "Query" 0)
      generatedStreamFailureSelections).run
    0).1.work

private def generatedFailureStream : DeliveryNode :=
  { ref := 0, path := [.field "usersStrict"] }

private def generatedFailureChild : DeliveryNode :=
  {
    ref := 1
    path := [.field "usersStrict", .index 0]
    label := some (.string "child")
  }

private def generatedFirstItem : GraphEvent :=
  .streamItems generatedFailureStream
    [{
      occurrence := .item [0, 0, 1] 0
      value := { item := .object [("required", .scalar "ok")] }
      work := (streamItemWork? generatedStreamFailureWork (.item [0, 0, 1] 0)).getD {}
    }]

private def generatedStreamFailureInputs : List (List GraphEvent) :=
  [[generatedFirstItem], [.streamFailure generatedFailureStream 1]]

private def generatedChildAfterStreamFailure : GraphEvent :=
  .taskSuccess (.executionGroup [0, 0, 1, 0, 1, 0])
    {
      value :=
        {
          deliveryGroups := [generatedFailureChild]
          path := [.field "usersStrict", .index 0]
          data := [("name", .scalar "1")]
        }
    }

example : ExecutedWork generatedStreamFailureWork := by
  refine ⟨Nat, generatedStreamFailureSchema, generatedStreamFailureResolvers,
    [], 40, "Query", .object "Query" 0, generatedStreamFailureSelections, rfl⟩

example
    : inputsStarted generatedStreamFailureWork generatedStreamFailureInputs = true := by
  native_decide

example
    : let queue :=
        (run (Work.fromExecution generatedStreamFailureWork)
          generatedStreamFailureInputs).1
      queue.rootGroups = [generatedFailureChild.ref]
      ∧ queue.rootStreams = []
      ∧ queue.terminated = false := by
  native_decide

/-- A previously started child group remains executable after the stream
fails on a later item. This checks the generated-work queue boundary, not yet
the full graph-event source law or abstract scheduler admission. -/
example
    : inputsStarted generatedStreamFailureWork
        (generatedStreamFailureInputs ++ [[generatedChildAfterStreamFailure]])
      = true := by
  native_decide

/-- The child result and completion still follow the stream failure notice. -/
example
    : (match (run (Work.fromExecution generatedStreamFailureWork)
                (generatedStreamFailureInputs
                  ++ [[generatedChildAfterStreamFailure]])).2 with
        | [
          [.streamValues _ _ _ _],
          [.streamFailure _ _],
          [.groupValues child _, .groupSuccess closed _ _, .workQueueTermination]
        ] =>
            child.ref == generatedFailureChild.ref
            && closed.ref == generatedFailureChild.ref
        | _ => false)
      = true := by
  native_decide

private def streamChildEvent : GraphEvent :=
  .streamItems stream
    [{
      occurrence := .item [] 0
      value := { item := .scalar "a" }
      work :=
        Work.fromExecution (.executionGroup [{ node := group }] [] (.ok ([], 0)) .empty)
          [0]
    }]

/-- An item result carries newly lowered child work; the queue then starts its group. -/
example
    : (run (Work.fromExecution streamChildWork) [[streamChildEvent]]).2
      = [[.streamValues stream [{ item := .scalar "a" }] [group] []]] := by
  rfl

example
    : streamItemWork? streamChildWork (.item [] 0)
      = some
          (Work.fromExecution
            (.executionGroup [{ node := group }] [] (.ok ([], 0)) .empty) [0]) := by
  rfl

private def otherGroup : DeliveryNode := { ref := 4, path := [] }

private def earlyFailureWork : Execution.Work :=
  .combine
    (.executionGroup [{ node := group }] [] (.ok ([], 0)) .empty)
    (.executionGroup
      [{ node := otherGroup }, { node := childGroup, ancestors := [group] }]
      [] (.error 1) .empty)

private def earlyParentSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [0])
    { value := { deliveryGroups := [group], path := [], data := [] } }

/-- A latent failed group is retained until its parent announces it, then reports its
cached failure in the same batch. Witness: evaluate both handler boundaries.
-/
example
    : (run (Work.fromExecution earlyFailureWork)
        [[.taskFailure (.executionGroup [1]) 1], [earlyParentSuccess]]).2
      = [
        [.groupFailure otherGroup 1],
        [
          .groupValues group [{ deliveryGroups := [group], path := [], data := [] }],
          .groupSuccess group [childGroup] [],
          .groupFailure childGroup 1,
          .workQueueTermination
        ]
      ] := by
  cbv

/-- The publisher allocates a pending ID for the retained failed child at release.
-/
example
    : ((ResponseStreamCursor.initialize initialResponse earlyFailureWork).2.run
        [[.taskFailure (.executionGroup [1]) 1], [earlyParentSuccess]]).1.map
        IncrementalStreamUpdateResult.pending
      = [[], [{ id := "2", path := childGroup.path, label := childGroup.label }]] := by
  cbv

private def secondRootGroup : DeliveryNode := { ref := 5, path := [] }

private def twoEarlyFailuresWork : Execution.Work :=
  .combine
    (.executionGroup [{ node := group }] [] (.ok ([], 0)) .empty)
    (.combine
      (.executionGroup
        [{ node := otherGroup }, { node := childGroup, ancestors := [group] }]
        [] (.error 1) .empty)
      (.executionGroup
        [{ node := secondRootGroup }, { node := childGroup, ancestors := [group] }]
        [] (.error 2) .empty))

/-- Several retained failures are accumulated and reported after normal child announcement. -/
example
    : (run (Work.fromExecution twoEarlyFailuresWork)
        [
          [.taskFailure (.executionGroup [1, 0]) 1],
          [.taskFailure (.executionGroup [1, 1]) 2],
          [.taskSuccess (.executionGroup [0])
            { value := { deliveryGroups := [group], path := [], data := [] } }]
        ]).2
      = [
        [.groupFailure otherGroup 1],
        [.groupFailure secondRootGroup 2],
        [
          .groupValues group [{ deliveryGroups := [group], path := [], data := [] }],
          .groupSuccess group [childGroup] [],
          .groupFailure childGroup 3,
          .workQueueTermination
        ]
      ] := by
  cbv

private def repeatedGroupWork : Execution.Work :=
  .combine
    (.executionGroup [{ node := group }] [] (.ok ([], 0)) .empty)
    (.executionGroup [{ node := group }] [] (.ok ([], 0)) .empty)

/-- Repeated group descriptors still yield one initial pending notice. -/
example
    : (State.initialize (Work.fromExecution repeatedGroupWork)).initialGroups
      = [group] := by
  rfl

/-- Reintegration does not announce an already live group a second time. -/
private def onceIntegrated : State :=
  (({} : State).addGroups [{ node := group }]).1

example : (onceIntegrated.addGroups [{ node := group }]).2 = [] := by
  rfl

private def laterTask : Task :=
  { occurrence := .executionGroup [9], groups := [group] }

/-- A task integrated into an already active group is started immediately. -/
example
    : (((State.initialize (Work.fromExecution groupWork)).addTask laterTask).taskNode?
        (.executionGroup [9])).isSome
      = true := by
  rfl

private def reintroductionSelections : List Selection :=
  [
    GraphQL.IncrementalDelivery.Tests.defer
      [
        GraphQL.IncrementalDelivery.Tests.field "required",
        GraphQL.IncrementalDelivery.Tests.field "user"
          [GraphQL.IncrementalDelivery.Tests.field "name"]
      ]
      (some "G"),
    GraphQL.IncrementalDelivery.Tests.defer
      [GraphQL.IncrementalDelivery.Tests.field "user"
        [GraphQL.IncrementalDelivery.Tests.field "age"]]
      (some "H")
  ]

private def reintroductionWork : Execution.Work :=
  ((executeRootSelectionSetCore GraphQL.IncrementalDelivery.Tests.schema
      GraphQL.IncrementalDelivery.Tests.resolvers [] 40 "Query"
      (.object "Query" 0) reintroductionSelections).run
    0).1.work

/-- This overlapping-defer scenario comes from actual query execution. -/
example : ExecutedWork reintroductionWork := by
  refine ⟨Nat, GraphQL.IncrementalDelivery.Tests.schema,
    GraphQL.IncrementalDelivery.Tests.resolvers, [], 40, "Query",
    .object "Query" 0, reintroductionSelections, rfl⟩

private def reintroducedG : DeliveryNode :=
  { ref := 0, path := [], label := some (.string "G") }

private def survivingH : DeliveryNode :=
  { ref := 1, path := [], label := some (.string "H") }

private def reintroductionFailure : GraphEvent :=
  .taskFailure (.executionGroup [1, 0]) 1

private def reintroductionSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [1, 1, 0])
    {
      value :=
        {
          deliveryGroups := [reintroducedG, survivingH]
          path := []
          data := [("user", .object [])]
        }
      work := (taskChildWork? reintroductionWork (.executionGroup [1, 1, 0])).getD {}
    }

private def survivingChildSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [1, 1, 0, 0, 0, 1, 1, 0])
    {
      value :=
        {
          deliveryGroups := [survivingH]
          path := [.field "user"]
          data := [("age", .scalar "1")]
        }
      work := {}
    }

private def reintroductionInputs : List (List GraphEvent) :=
  [[reintroductionFailure], [reintroductionSuccess], [survivingChildSuccess]]

/-- The removed group's ref remains invalidated by its original failed contributor.
Witness: the root failure's structural task address, independent of publications.
-/
private theorem reintroduction_invalidated
    : GroupInvalidated reintroductionWork [.executionGroup [1, 0]] reintroducedG.ref := by
  have known : TaskHasOwners reintroductionWork (.executionGroup [1, 0])
      [reintroducedG.ref] := by
    refine ⟨none, .object [] (.error 1), ?_⟩
    refine ⟨[{ node := reintroducedG }], [], .error 1, .empty, [], ?_, rfl, rfl⟩
    cbv
  exact .task known (by simp) (by simp)

/-- Cleanup invalidation embeds into full causal failure without assuming that
all producer cancellation is group cleanup. Witness: the checked one-way bridge.
-/
example (published : Occurrence → Prop)
    : Causality.NodeFailed reintroductionWork [.executionGroup [1, 0]]
        published reintroducedG.ref :=
  reintroduction_invalidated.toCausality published

/-- All three events are started when the host settles them in this order. -/
example : inputsStarted reintroductionWork reintroductionInputs = true := by
  native_decide

/-- Surviving shared work cannot recreate a failed group, even as an inert shell.
Witness: execute the original shared-child fixture with permanent registration refs.
-/
example
    : let finalState :=
        (run (Work.fromExecution reintroductionWork) reintroductionInputs).1
      finalState.terminated = true
      ∧ finalState.rootGroups = []
      ∧ (finalState.groupNode? reintroducedG.ref).isNone = true
      ∧ GroupInvalidated reintroductionWork [.executionGroup [1, 0]]
          reintroducedG.ref := by
  exact ⟨by cbv, by cbv, by cbv, reintroduction_invalidated⟩

/-- The removed group has no task links after child integration.
Witness: the group lookup remains absent rather than returning a recreated shell.
-/
example
    : let state :=
        (run (Work.fromExecution reintroductionWork)
          [[reintroductionFailure], [reintroductionSuccess]]).1
      ((state.groupNode? reintroducedG.ref).map
        (fun node => node.tasks.contains (.executionGroup [1, 1, 0]))).getD
        false
      = false := by
  native_decide

/-- Child integration leaves no stale zero-pending shell for the failed owner.
Witness: evaluate the actual group-node lookup after shared settlement.
-/
example
    : let state :=
        (run (Work.fromExecution reintroductionWork)
          [[reintroductionFailure], [reintroductionSuccess]]).1
      (state.groupNode? reintroducedG.ref).map
        (fun node => (node.pending, node.tasks.length))
      = none := by
  cbv

private def settledSharedWork : ReferenceWorkQueue.Work :=
  {
    groups := [{ node := group }, { node := deepGroup }]
    tasks :=
      [
        { occurrence := .executionGroup [], groups := [group, deepGroup] },
        { occurrence := .executionGroup [1], groups := [deepGroup] }
      ]
  }

/-- A flushed shared task remains registered but is no longer a member of a
still-active co-owner. Release proofs must quantify only over started or
newly requested tasks, not all registered definitions. -/
example
    : let state :=
        (State.initialize settledSharedWork).taskSuccess (.executionGroup [])
          { value := sharedValue }
      state.1.rootGroups = [deepGroup.ref]
      ∧ (state.1.tasks.map Task.occurrence).contains (.executionGroup []) = true
      ∧ ((state.1.groupNode? deepGroup.ref).map
          (fun node => node.tasks.contains (.executionGroup []))).getD
          false
        = false := by
  native_decide

end GraphQL.IncrementalDelivery.Tests.WorkQueueImplementation
