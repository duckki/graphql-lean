import Tests.GraphQL.IncrementalDelivery.Execution
import Tests.GraphQL.IncrementalDelivery.Fixtures.WorkDeclarations

open GraphQL.IncrementalDelivery.Tests (declaredTask)

/-! Definition-level checks of failure reporting through both executable queues.
Collected diagnostics remain in Work. Failed group completions collect cached task
causes; each task still contributes only its selected boundary explanation.
No conformance or query-correctness proof modules are imported here.
-/

namespace GraphQL.IncrementalDelivery.Tests.DeliveryFailureReporting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open ReferenceWorkQueue (GraphEvent)

private def complete (selections : List Selection)
    : Completion (List (Name × ResponseValue)) :=
  ((executeRootSelectionSetCore schema resolvers [] 40 "Query" (.object "Query" 0)
      selections).run
    0).1

private def bothFinish (completed : Completion (List (Name × ResponseValue)))
    (inputs : List (List GraphEvent)) (counts : List Nat)
    : Bool :=
  let reference := ReferenceWorkQueue.replayIncrementalResponse completed inputs
  let alternative := AlternativeWorkQueue.replayIncrementalResponse completed inputs
  ReferenceWorkQueue.inputsStarted completed.work inputs
  && reference.2.2
  && alternative.2.2
  && same reference alternative
  && (reference.2.1.flatMap (·.completed)).map (·.errors) == counts

private def groupOutcome? (work : Work) (address : Address)
    : Option (TaskOutcome (List (Name × ResponseValue))) := do
  let location ← locateWork work address
  match location.current with
  | .executionGroup _ _ outcome _ => some outcome
  | _ => none

private def failed : Completion (List (Name × ResponseValue)) :=
  complete [defer [field "fail", field "required"]]

-- The discarded deferred payload retains two diagnostics but reports one cause.
#guard same (groupOutcome? failed.work [1, 0] |>.map (·.result)) (some (.error 2))
#guard same (groupOutcome? failed.work [1, 0] |>.map (·.deliveryResult)) (some (.error 1))
#guard bothFinish failed [[.taskFailure (.executionGroup [1, 0]) 1]] [1]

private def failedWork : Work :=
  declaredTask [⟨{ ref := 0, path := [] }, []⟩] []
    { result := .error 2, cause := some 1 } .empty

example : GraphEvent.MatchesWork failedWork (.taskFailure (.executionGroup []) 1) := by
  refine ⟨[0], none, [], ?_⟩
  exact ⟨
    [⟨{ ref := 0, path := [] }, []⟩],
    [],
    { result := .error 2, cause := some 1 },
    .empty,
    [],
    by rfl,
    rfl,
    rfl
  ⟩

-- Pure sibling traversal still collects both diagnostics in the reverse order.
private def reversed := complete [defer [field "required", field "fail"]]

#guard same (groupOutcome? reversed.work [1, 0] |>.map (·.result)) (some (.error 2))
#guard bothFinish reversed [[.taskFailure (.executionGroup [1, 0]) 1]] [1]

-- Ordinary and initial-envelope accounting keeps the original additive result.
#guard
  same (selectionSetResultToResponse (complete [field "fail", field "required"]).result)
    { data := .null, errors := 2 : Response }
#guard
  (ReferenceWorkQueue.replayIncrementalResponse
    (complete [field "fail", defer [field "a"]]) []).1.errors
  == 1

private def parent : DeliveryNode := { ref := 2, path := [], label := some (.string "P") }

private def child : DeliveryNode := { ref := 3, path := [], label := some (.string "C") }

private def childFailure (errors : Nat) : GraphEvent := .groupFailure ⟨child, errors⟩

private def outcomeEvents (events : List GraphEvent) : List GraphEvent :=
  events.filter
    (fun event =>
      match event with
      | .groupFailure _ => false
      | _ => true)

private def shared :=
  complete
    [
      defer [field "required" [] [] (some "first")] (some "R1"),
      defer [field "required" [] [] (some "second")] (some "R2"),
      defer
        [
          field "a",
          defer
            [
              field "required" [] [] (some "first"),
              field "required" [] [] (some "second")
            ]
            (some "C")
        ]
        (some "P")
    ]

private def sharedInputs : List (List GraphEvent) :=
  [
    [.taskFailure (.executionGroup [1, 0]) 1],
    [.taskFailure (.executionGroup [1, 1, 0]) 1],
    [.taskSuccess (.executionGroup [1, 1, 1, 0])
      {
        value := { deliveryGroups := [parent], path := [], data := [("a", .scalar "a")] },
        work :=
          ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
      }]
  ]

-- C is latent while two shared tasks fail through distinct healthy root owners.
-- Its eventual completion includes both cached task causes, without nullable diagnostics.
#guard bothFinish shared (sharedInputs ++ [[childFailure 2]]) [1, 1, 0, 2]

-- Cache inspection precedes FIFO TASK_FAILURE dispatch within an available host batch.
-- P completes first; the two root failures precede C's one queued aggregate notice.
private def queuedSharedInputs : List (List GraphEvent) :=
  [sharedInputs[2]! ++ sharedInputs[0]! ++ sharedInputs[1]! ++ [childFailure 2]]

#guard bothFinish shared queuedSharedInputs [0, 1, 1, 2]

-- PR #4870's queued-failure test: removal precedes notification. The parent handler
-- returns C's notice separately, so the remaining TASK_FAILURE inputs precede it.
private def queuedAfterParent :=
  let initial :=
    ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution shared.work)
  let batch := queuedSharedInputs[0]!
  match batch with
  | [] => (initial, [], [])
  | event :: _ => initial.handleGraphEvent event (GraphEvent.availableFailures batch)

#guard (queuedAfterParent.1.groupNode? 3).isNone
#guard
  !(queuedAfterParent.2.1.any
      (fun event =>
        match event with
        | .groupFailure _ _ => true
        | _ => false))
#guard
  queuedAfterParent.2.2.map (fun failure => (failure.group.ref, failure.errors))
  == [(3, 2)]

private def alternativeAfterParent :=
  let initial := AlternativeWorkQueue.State.initialize shared.work
  let batch := queuedSharedInputs[0]!
  match batch with
  | [] => (initial, [], [], [])
  | event :: _ => initial.handleGraphEvent event (GraphEvent.availableFailures batch)

#guard (alternativeAfterParent.1.queue.groupNode? 3).isNone
#guard
  alternativeAfterParent.2.2.2.map (fun failure => (failure.group.ref, failure.errors))
  == [(3, 2)]
#guard
  ((AlternativeWorkQueue.State.initialize shared.work).handleGraphEvents
    queuedSharedInputs[0]!).state.queue.groupFailureEvents.isEmpty

-- A host-batch boundary does not forward the pending notice on its own.
private def queuedBeforeControl :=
  let initial :=
    ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution shared.work)
  initial.handleGraphEvents (outcomeEvents queuedSharedInputs[0]!)

#guard
  queuedBeforeControl.1.groupFailureEvents.map
    (fun failure => (failure.group.ref, failure.errors))
  == [(3, 2)]
#guard !queuedBeforeControl.1.terminated
#guard
  !(queuedBeforeControl.2.any
      (fun event =>
        match event with
        | .groupFailure group _ => group.ref == 3
        | _ => false))

private def eventTrace (events : List WorkQueueEvent) : List (String × Nat × Nat) :=
  events.filterMap
    (fun event =>
      match event with
      | .groupValues node _ => some ("values", node.ref, 0)
      | .groupSuccess node _ _ => some ("success", node.ref, 0)
      | .groupFailure node errors => some ("failure", node.ref, errors)
      | .workQueueTermination => some ("termination", 0, 0)
      | _ => none)

private def queuedTrace : List (String × Nat × Nat) :=
  [
    ("values", 2, 0),
    ("success", 2, 0),
    ("failure", 0, 1),
    ("failure", 1, 1),
    ("failure", 3, 2),
    ("termination", 0, 0)
  ]

#guard
  eventTrace
    ((ReferenceWorkQueue.State.initialize
        (ReferenceWorkQueue.Work.fromExecution shared.work)).runNormalized
      queuedSharedInputs).2.flatten
  == queuedTrace
#guard
  eventTrace
    ((AlternativeWorkQueue.State.initialize shared.work).runNormalized
      queuedSharedInputs).2.flatten
  == queuedTrace

-- The same notification order can describe different cache availability. Keeping the
-- outcome batches separate lets C start before either rejection becomes available.
-- The queued aggregate control therefore belongs only to the cached-batch run.
private def splitQueuedInputs : List (List GraphEvent) :=
  (outcomeEvents queuedSharedInputs.flatten).map (fun event => [event])

#guard same (outcomeEvents queuedSharedInputs.flatten) splitQueuedInputs.flatten
#guard bothFinish shared splitQueuedInputs [0, 1, 1, 1]
#guard
  eventTrace
    ((ReferenceWorkQueue.State.initialize
        (ReferenceWorkQueue.Work.fromExecution shared.work)).runNormalized
      splitQueuedInputs).2.flatten
  == [
    ("values", 2, 0),
    ("success", 2, 0),
    ("failure", 0, 1),
    ("failure", 3, 1),
    ("failure", 1, 1),
    ("termination", 0, 0)
  ]

-- A future rejection does not join a completion already emitted when C started.
private def pendingSharedInputs : List (List GraphEvent) :=
  [sharedInputs[0]!, sharedInputs[2]! ++ [childFailure 1], sharedInputs[1]!]

#guard bothFinish shared pendingSharedInputs [1, 0, 1, 1]

private def cached :=
  let initial :=
    ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution shared.work)
  (initial.handleGraphEvents sharedInputs[0]!).1

private def cachedTwice := (cached.handleGraphEvents sharedInputs[1]!).1

-- Rejections remain on their shared tasks; the latent group keeps both memberships.
#guard (cachedTwice.taskNode? (.executionGroup [1, 0]) |>.bind (·.rejection)) == some 1
#guard (cachedTwice.taskNode? (.executionGroup [1, 1, 0]) |>.bind (·.rejection)) == some 1
#guard (cachedTwice.groupNode? 3 |>.map (·.tasks.length)) == some 2
#guard (cachedTwice.groupNode? 3 |>.map (·.pending)) == some 2

private def outerOne : DeliveryNode := { ref := 0, path := [] }
private def outerTwo : DeliveryNode := { ref := 1, path := [] }

-- Distinct raw counts expose the aggregate without mixing in collected diagnostics.
-- The second task settles first; releasing C sums the two retained boundary counts.
private def replayOrder : Completion (List (Name × ResponseValue)) :=
  {
    result := .ok ([], 0),
    work :=
      .combine
        (declaredTask [⟨outerOne, []⟩, ⟨child, [parent]⟩] []
          { result := .error 3, cause := some 3 } .empty)
        (.combine
          (declaredTask [⟨outerTwo, []⟩, ⟨child, [parent]⟩] []
            { result := .error 5, cause := some 5 } .empty)
          (declaredTask [⟨parent, []⟩] [] { result := .ok ([("a", .scalar "a")], 0) }
            .empty))
  }

private def replayOrderInputs : List (List GraphEvent) :=
  [
    [.taskFailure (.executionGroup [1, 0]) 5],
    [.taskFailure (.executionGroup [0]) 3],
    [.taskSuccess (.executionGroup [1, 1])
      {
        value := { deliveryGroups := [parent], path := [], data := [("a", .scalar "a")] }
      }]
  ]

#guard bothFinish replayOrder (replayOrderInputs ++ [[childFailure 8]]) [5, 3, 0, 8]

-- Startup failures close each released owner with its own cached cause collection.
-- Replaying the first rejected task through every active co-owner would report C as 1.
private def siblings :=
  complete
    [
      defer [field "required" [] [] (some "first")] (some "R1"),
      defer [field "required" [] [] (some "second")] (some "R2"),
      defer
        [
          field "a",
          defer
            [
              field "required" [] [] (some "first"),
              field "required" [] [] (some "second")
            ]
            (some "C"),
          defer [field "required" [] [] (some "first")] (some "D")
        ]
        (some "P")
    ]

private def siblingFailure : GraphEvent :=
  .groupFailure ⟨{ ref := 4, path := [], label := some (.string "D") }, 1⟩

#guard
  bothFinish siblings (sharedInputs ++ [[childFailure 2, siblingFailure]]) [1, 1, 0, 2, 1]
#guard bothFinish siblings [queuedSharedInputs[0]! ++ [siblingFailure]] [0, 1, 1, 2, 1]

-- Failures received after startup retain the first triggering task's boundary count.
private def activeFailures : Completion (List (Name × ResponseValue)) :=
  {
    result := .ok ([], 0),
    work :=
      .combine
        (declaredTask [⟨outerOne, []⟩] [] { result := .error 3 } .empty)
        (declaredTask [⟨outerOne, []⟩] [] { result := .error 5 } .empty)
  }

#guard bothFinish activeFailures [[.taskFailure (.executionGroup [0]) 3]] [3]

-- The admission relation admits several distinct causes without changing TaskAt.
example
    : NodeFailureCauses activeFailures.work
        [.executionGroup [0], .executionGroup [1]] outerOne.ref 8 := by
  refine ⟨
    [(.executionGroup [0], 3), (.executionGroup [1], 5)],
    by decide,
    by decide,
    ?_,
    rfl
  ⟩
  intro occurrence count member
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by simp, [outerOne.ref], none, .object [] (.error 3), ?_, by simp, rfl, by decide⟩
    exact ⟨[⟨outerOne, []⟩], [], { result := .error 3 }, .empty, [], rfl, rfl, rfl⟩
  · refine ⟨by simp, [outerOne.ref], none, .object [] (.error 5), ?_, by simp, rfl, by decide⟩
    exact ⟨[⟨outerOne, []⟩], [], { result := .error 5 }, .empty, [], rfl, rfl, rfl⟩

-- A positive number alone cannot stand in for reporting-availability evidence.
example (work : Work) (ref : Nat) (errors : Nat)
    : ¬NodeFailureCauses work [] ref errors := by
  rintro ⟨causes, nonempty, _, supported, _⟩
  cases causes with
  | nil => exact nonempty rfl
  | cons cause rest =>
      have impossible := (supported cause.1 cause.2 List.mem_cons_self).1
      exact List.not_mem_nil impossible

-- The aggregate remains a positive delivery-failure explanation.
example (work : Work) (available : List Occurrence) (ref : Nat)
    : ¬NodeFailureCauses work available ref 0 := by
  rintro ⟨causes, nonempty, _, supported, total⟩
  cases causes with
  | nil => exact nonempty rfl
  | cons cause rest =>
      obtain ⟨_, _, _, _, _, _, _, positive⟩ :=
        supported cause.1 cause.2 List.mem_cons_self
      simp only [List.map_cons, List.sum_cons] at total
      omega

private def sharedValue :=
  complete
    [
      defer [field "required", field "a"] (some "R"),
      defer [field "b", defer [field "a"] (some "C")] (some "P")
    ]

private def valueOwner : DeliveryNode :=
  { ref := 0, path := [], label := some (.string "R") }

private def valueParent : DeliveryNode :=
  { ref := 1, path := [], label := some (.string "P") }

private def valueChild : DeliveryNode :=
  { ref := 2, path := [], label := some (.string "C") }

private def valueSettlement : GraphEvent :=
  .taskSuccess (.executionGroup [1, 1, 0])
    {
      value :=
        {
          deliveryGroups := [valueOwner, valueChild],
          path := [],
          data := [("a", .scalar "a")]
        },
      work := ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 1, 0, 0]
    }

private def parentSettlement : GraphEvent :=
  .taskSuccess (.executionGroup [1, 1, 1, 0])
    {
      value :=
        { deliveryGroups := [valueParent], path := [], data := [("b", .scalar "b")] },
      work :=
        ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

-- A successful shared result is delivered once, whether it settles before or after release.
private def valueInputs (beforeRelease : Bool) : List (List GraphEvent) :=
  [.taskFailure (.executionGroup [1, 0]) 1]
  :: (if beforeRelease then
        [[valueSettlement], [parentSettlement]]
      else
        [[parentSettlement], [valueSettlement]])

#guard
  [true, false].all
    fun beforeRelease =>
      let inputs := valueInputs beforeRelease
      bothFinish sharedValue inputs [1, 0, 0]
      && ((ReferenceWorkQueue.replayIncrementalResponse sharedValue inputs).2.1.flatMap
            (·.incremental)).length
          == 2

private def objectSchema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "child", outputType := .named "Child" },
                { name := "requiredChild", outputType := .nonNull (.named "Child") },
                { name := "items", outputType := .list (.nonNull (.named "Child")) },
                { name := "nullableItems", outputType := .list (.named "Child") }
              ]
          },
        .object
          {
            name := "Child",
            fields :=
              [
                { name := "x", outputType := .named "String" },
                { name := "bad", outputType := .nonNull (.named "String") }
              ]
          }
      ]
  }

private def objectResolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ name _ _ =>
        match name with
        | "x" | "bad" => none
        | "items" | "nullableItems" => some (.list [.object "Child" 1])
        | _ => some (.object "Child" 1)
    resolve_argumentsEquivalent := by intros; rfl
  }

private def objectComplete (selections : List Selection)
    : Completion (List (Name × ResponseValue)) :=
  ((executeRootSelectionSetCore objectSchema objectResolvers [] 40 "Query"
      (.object "Query" 0) selections).run
    0).1

private def childFields := [field "x", field "bad"]
private def nullable := objectComplete [defer [field "child" childFields]]
private def required := objectComplete [defer [field "requiredChild" childFields]]
private def owner : DeliveryNode := { ref := 0, path := [] }

-- Catching inside the delivered object preserves both diagnostics with null data.
#guard
  bothFinish nullable
    [[.taskSuccess (.executionGroup [1, 0])
        {
          value :=
            {
              deliveryGroups := [owner],
              path := [],
              data := [("child", .null)],
              errors := 2
            },
          work := ReferenceWorkQueue.Work.fromExecution (.combine .empty .empty) [1, 0, 0]
        }]]
    [0]
#guard
  ((ReferenceWorkQueue.replayIncrementalResponse nullable
      [[.taskSuccess (.executionGroup [1, 0])
          {
            value :=
              {
                deliveryGroups := [owner],
                path := [],
                data := [("child", .null)],
                errors := 2
              }
          }]]).2.1.flatMap
    (·.incremental)).map
    (·.errors)
  == [2]

-- A non-null wrapper rethrows the retained child cause at the actual delivery boundary.
#guard same (groupOutcome? required.work [1, 0] |>.map (·.result)) (some (.error 2))
#guard bothFinish required [[.taskFailure (.executionGroup [1, 0]) 1]] [1]

private def stream (name : Name) :=
  objectComplete [field name childFields [.stream (.boolean true) none (.int 0)]]

private def streamNode (name : Name) : DeliveryNode := { ref := 0, path := [.field name] }

private def itemOutcome? (completed : Completion (List (Name × ResponseValue)))
    : Option (TaskOutcome ResponseValue) := do
  let location ← locateWork completed.work [0, 0, 1]
  match location.current with
  | .stream _ items => items.head?.map (·.1)
  | _ => none

#guard same (itemOutcome? (stream "items") |>.map (·.result)) (some (.error 2))
#guard same (itemOutcome? (stream "items") |>.map (·.deliveryResult)) (some (.error 1))
#guard bothFinish (stream "items") [[.streamFailure (streamNode "items") 1]] [1]

private def streamWork : Work :=
  .stream (streamNode "items") [({ result := .error 2, cause := some 1 }, .empty)]

example : GraphEvent.MatchesWork streamWork (.streamFailure (streamNode "items") 1) := by
  refine ⟨[], [({ result := .error 2, cause := some 1 }, .empty)], none, [], by rfl, ?_⟩
  exact ⟨{ result := .error 2, cause := some 1 }, .empty, by simp, rfl⟩

example : GraphEvent.Ready streamWork [] (.streamFailure (streamNode "items") 1) := by
  refine ⟨
    [],
    [({ result := .error 2, cause := some 1 }, .empty)],
    none,
    [],
    by rfl,
    ?_,
    ?_
  ⟩
  · simp
  · exact ⟨{ result := .error 2, cause := some 1 }, .empty, rfl, rfl⟩

-- Nullable items remain successful null patches carrying both diagnostics.
#guard
  bothFinish (stream "nullableItems")
    [
      [.streamItems (streamNode "nullableItems")
        [{ occurrence := .item [0, 0, 1] 0, value := { item := .null, errors := 2 } }]],
      [.streamSuccess (streamNode "nullableItems")]
    ] [0]
#guard
  ((ReferenceWorkQueue.replayIncrementalResponse (stream "nullableItems")
      [
        [.streamItems (streamNode "nullableItems")
          [{ occurrence := .item [0, 0, 1] 0, value := { item := .null, errors := 2 } }]],
        [.streamSuccess (streamNode "nullableItems")]
      ]).2.1.flatMap
    (·.incremental)).map
    (·.errors)
  == [2]

-- Permissive raw outcomes retain zero; projection never invents an error.
#guard same ({ result := .error 0 } : TaskOutcome Unit).deliveryResult (.error 0)

end GraphQL.IncrementalDelivery.Tests.DeliveryFailureReporting
