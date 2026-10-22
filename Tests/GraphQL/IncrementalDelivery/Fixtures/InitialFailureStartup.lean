import Tests.GraphQL.IncrementalDelivery.Execution

/-! Initial root activation observes synchronous rejections before FIFO notifications.
The initial declaration order is independent of contributor encounter order.
-/

namespace GraphQL.IncrementalDelivery.Tests.InitialFailureStartup
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 40 "Query" (.object "Query" 0)
      [
        defer [field "required" [] [] (some "first")] (some "R1"),
        defer [field "required" [] [] (some "second")] (some "R2"),
        defer
          [
            field "required" [] [] (some "first"),
            field "required" [] [] (some "second"),
            field "a"
          ]
          (some "R3")
      ]).run
    0).1

private def first : WorkQueueSemantics.Occurrence := .executionGroup [1, 0]
private def second : WorkQueueSemantics.Occurrence := .executionGroup [1, 1, 0]
private def privateTask : WorkQueueSemantics.Occurrence := .executionGroup [1, 1, 1, 0]
private def startup : InitialStartup := { failures := [(first, 1), (second, 1)] }

private def outcomes : List GraphEvent := [.taskFailure first 1, .taskFailure second 1]

private def inputs : List (List GraphEvent) :=
  [outcomes ++ [.groupFailure ⟨{ref := 2,path := [],label := some (.string "R3")},2⟩]]

private def initialization :=
  State.initialize (Work.fromExecution completed.work) startup

private def initial := initialization

private def reference :=
  ReferenceWorkQueue.replayIncrementalResponse completed inputs startup

private def alternative :=
  AlternativeWorkQueue.replayIncrementalResponse completed inputs startup

#guard initial.initialGroups.map (·.ref) == [0, 1, 2]
#guard
  initialization.groupFailureEvents.map
    (fun failure => (failure.group.ref, failure.errors))
  == [(2, 2)]
#guard (initial.groupNode? 2).isNone
#guard (initial.taskNode? privateTask).isNone
#guard ReferenceWorkQueue.inputsStarted completed.work inputs startup
#guard same reference alternative
#guard reference.2.2
#guard (reference.2.1.flatMap (·.completed)).map (·.errors) == [1, 1, 2]
#guard reference.1.pending.map (·.id) == ["0", "1", "2"]
#guard ((initial.handleGraphEvents inputs[0]!).1.handleGraphEvents []).2.isEmpty

-- An asynchronous rejection is not made synchronous just because its notification is
-- eventually present in the first supplied batch. Empty startup availability keeps the
-- active-owner path, with one triggering cause for R3.
private def asynchronous : InitialStartup := {}

private def asyncReference :=
  ReferenceWorkQueue.replayIncrementalResponse completed [outcomes] asynchronous

private def asyncAlternative :=
  AlternativeWorkQueue.replayIncrementalResponse completed [outcomes] asynchronous

#guard same asyncReference asyncAlternative
#guard (asyncReference.2.1.flatMap (·.completed)).map (·.errors) == [1, 1, 1]
#guard
  (State.initialize (Work.fromExecution completed.work)
    asynchronous).groupFailureEvents.isEmpty
#guard
  (State.initialize (Work.fromExecution completed.work) asynchronous).taskNode?
    privateTask
  |>.isSome

-- Shared contributors do not move R3 ahead of the earlier R2 declaration.
#guard
  (State.initialize (Work.fromExecution completed.work)).initialGroups.map (·.ref)
  == [0, 1, 2]

-- Declaration order also matters when a successful parent releases the roots.
private def nested :=
  ((executeRootSelectionSetCore schema resolvers [] 40 "Query" (.object "Query" 0)
      [defer
        [
          field "b",
          defer [field "required" [] [] (some "first")] (some "R1"),
          defer [field "required" [] [] (some "second")] (some "R2"),
          defer
            [
              field "required" [] [] (some "first"),
              field "required" [] [] (some "second"),
              field "a"
            ]
            (some "R3")
        ]
        (some "P")]).run
    0).1

private def nestedWork := (taskChildWork? nested.work (.executionGroup [1, 0])).getD {}

private def parentResult : GraphEvent :=
  .taskSuccess (.executionGroup [1, 0])
    {
      value :=
        {
          path := []
          data := [("b", .scalar "b")]
          deliveryGroups := [{ref := 0, path := [], label := some (.string "P")}]
        }
      work := nestedWork
    }

private def nestedFailures : List GraphEvent :=
  (Work.fromExecution nested.work).tasks.filterMap
    fun task =>
      match task.occurrence with
      | .executionGroup address =>
          match WorkQueueSemantics.locateWork nested.work address with
          | none => none
          | some location =>
              match location.current with
              | .executionGroup _ _ outcome _ =>
                  match outcome.deliveryResult with
                  | .error errors => some (.taskFailure task.occurrence errors)
                  | _ => none
              | _ => none
      | _ => none

private def nestedInputs : List (List GraphEvent) :=
  [[parentResult]
    ++ nestedFailures
    ++ [.groupFailure ⟨{ref := 3,path := [],label := some (.string "R3")},2⟩]]
#guard nestedFailures.length == 2
private def nestedReference :=
  ReferenceWorkQueue.replayIncrementalResponse nested nestedInputs

private def nestedAlternative :=
  AlternativeWorkQueue.replayIncrementalResponse nested nestedInputs

#guard ReferenceWorkQueue.inputsStarted nested.work nestedInputs
#guard same nestedReference nestedAlternative
#guard nestedReference.2.2
#guard (nestedReference.2.1.flatMap (·.completed)).map (·.errors) == [0, 1, 1, 2]

end GraphQL.IncrementalDelivery.Tests.InitialFailureStartup
