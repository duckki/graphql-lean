import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! Executable registration-projection checks independent of conformance proofs. -/

namespace AlternativeRegistrationChecks

open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)
open Execution (DeliveryNode)

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError name)

private def same [Repr α] (name : String) (left right : α) : IO Unit :=
  check name (reprStr left == reprStr right)

private def node (key : Nat) : DeliveryNode := { ref := key, path := [] }

private def task (id : Nat) (owners : List Nat) : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [id], groups := owners.map node }

private def state : State :=
  {
    queue :=
      {
        rootGroups := [1]
        rootStreams := [4]
        registeredGroups := [0, 1, 2, 3]
        groupNodes :=
          [
            { group := { node := node 1 }, tasks := [.executionGroup [9]], pending := 1 },
            { group := { node := node 2 } },
            { group := { node := node 3 }, failure := some 1 }
          ]
        tasks := [task 9 [1]]
        taskNodes := [{ task := task 9 [1] }]
        streams := [{ node := node 4 }]
      }
  }

private def success (work : ReferenceWorkQueue.Work) : GraphEvent :=
  .taskSuccess (.executionGroup [9]) { value := { path := [], data := [] }, work }

private def item (index : Nat) (work : ReferenceWorkQueue.Work)
    : ReferenceWorkQueue.StreamItem :=
  { occurrence := .item [] index, value := { item := .scalar "item" }, work }

private def parity (name : String) (work : Execution.Work)
    (inputs : List (List GraphEvent))
    : IO Unit := do
  let reference :=
    (ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
      inputs
  let alternative := (State.initialize work).runNormalized inputs
  same (name ++ ": outputs") alternative.2 reference.2
  same (name ++ ": residual") alternative.1 (State.fromReference reference.1)
  let completed : Execution.Completion (List (GraphQL.Name × Execution.ResponseValue)) :=
    { result := .ok ([], 0), work }
  same (name ++ ": response")
    (replayIncrementalResponse completed inputs)
    (ReferenceWorkQueue.replayIncrementalResponse completed inputs)

#eval
  do
    for (owners, expected)
        in [
          ([1], TaskRegistration.active),
          ([2], .registered),
          ([3], .registered),
          ([0], .rejected),
          ([], .rejected),
          ([0, 2], .registered),
          ([3, 1], .active)
        ] do
      let (registered, disposition) := state.addTask (task 10 owners)
      same "owner-loop classification" disposition expected
      check "registration does not start tasks"
        ((registered.queue.taskNode? (.executionGroup [10])).isNone)
      for owner in owners do
        match state.queue.groupNode? owner with
        | none => pure ()
        | some old =>
            check "live owner gets a contributor and counter"
              ((registered.queue.groupNode? owner).any
                (fun (current : ReferenceWorkQueue.GroupNode) =>
                  current.tasks.contains (.executionGroup [10])
                  && current.pending == old.pending + 1))
    let active := task 10 [1]
    let dormant := task 11 [2]
    let failedDormant := task 12 [3]
    let rejected := task 13 [0]
    let fresh := task 14 [5]
    let activeAgain := task 15 [0, 1]
    let work : ReferenceWorkQueue.Work :=
      {
        groups := [{ node := node 5 }]
        tasks := [active, dormant, rejected, failedDormant, fresh, activeAgain]
        streams := [{ node := node 6 }]
      }
    let (registered, projections) := state.maybeIntegrateWork work
    same "scope-ordered active subset" projections.activeTasks [active, activeAgain]
    same "rejected subset only" projections.rejectedTasks [rejected]
    same "new owners installed before tasks" projections.newGroups [node 5]
    same "new sources exposed" projections.newStreams [node 6]
    same "task catalogue preserved" registered.queue.tasks
      (state.queue.tasks ++ work.tasks)
    same "no eager starts during integration" registered.queue.taskNodes
      state.queue.taskNodes
    let (started, targets) := registered.startNewWork projections.newWork projections
    same "disposal consumes rejected projection" targets [.task rejected.occurrence]
    for selected in [active, fresh, activeAgain] do
      check "active and newly released tasks start"
        ((started.queue.taskNode? selected.occurrence).isSome)
    for selected in [dormant, failedDormant, rejected] do
      check "unreleased or rejected task stays unstarted"
        ((started.queue.taskNode? selected.occurrence).isNone)
    same "all released roots installed" started.queue.rootGroups [1, 5]
    same "all released sources installed" started.queue.rootStreams [4, 6]
    let (stopped, silent) :=
      ({ registered with stopped := true }).startNewWork projections.newWork projections
    same "closed activation unchanged" stopped { registered with stopped := true }
    check "closed activation silent" silent.isEmpty
    let duplicate : ReferenceWorkQueue.Work := { tasks := [rejected, rejected] }
    let (_, _, effects) := state.handleGraphEvent (success duplicate)
    same "handoff before one rejected-task abort" effects
      [.adopt (.executionGroup [9]), .abortTask rejected.occurrence]
    let (_, _, activeEffects) := state.handleGraphEvent (success { tasks := [active] })
    same "accepted active task is not rejected" activeEffects
      [.adopt (.executionGroup [9])]
    let (activeResult, _, _) := state.handleGraphEvent (success { tasks := [active] })
    check "newly active child starts after settlement"
      ((activeResult.queue.taskNode? active.occurrence).isSome)
    check "new contribution prevents premature owner completion"
      ((activeResult.queue.groupNode? 1).any
        (fun (group : ReferenceWorkQueue.GroupNode) => group.pending == 1))
    let secondRejected := task 16 []
    let (_, _, itemEffects) :=
      state.handleGraphEvent
        (.streamItems (node 4)
          [item 0 duplicate, item 1 { tasks := [rejected, secondRejected] }])
    same "per-item disposal before next handoff and acknowledgement" itemEffects
      [
        .adopt (.item [] 0),
        .abortTask rejected.occurrence,
        .adopt (.item [] 1),
        .abortTask secondRejected.occurrence,
        .acknowledge 4
      ]
    let (ignored, ignoredEvents, ignoredEffects) :=
      state.handleGraphEvent (.streamItems (node 7) [item 0 duplicate])
    same "inactive receipt registers nothing" ignored state
    check "inactive receipt publishes nothing" ignoredEvents.isEmpty
    same "inactive receipt still acknowledged" ignoredEffects [.acknowledge 7]
    let (missing, _, missingEffects) :=
      state.handleGraphEvent
        (.taskSuccess rejected.occurrence
          { value := { path := [], data := [] }, work := duplicate })
    same "missing task result does not register" missing state
    check "missing task result does not adopt" missingEffects.isEmpty
    let result : Execution.Result (List (GraphQL.Name × Execution.ResponseValue)) :=
      .ok ([("x", .scalar "X")], 0)
    let simple : Execution.Work := .executionGroup [{ node := node 1 }] [] result .empty
    let simpleDone : GraphEvent :=
      .taskSuccess (.executionGroup [])
        { value := { path := [], data := [("x", .scalar "X")] } }
    parity "startup/prefix" simple []
    parity "completion" simple [[simpleDone]]
    let child : Execution.Work :=
      .executionGroup [{ node := node 5, ancestors := [node 1] }] [] result .empty
    let nested : Execution.Work := .executionGroup [{ node := node 1 }] [] result child
    let parentDone : GraphEvent :=
      .taskSuccess (.executionGroup [])
        {
          value := { path := [], data := [("x", .scalar "X")] }
          work := ReferenceWorkQueue.Work.fromExecution child [0]
        }
    let childDone : GraphEvent :=
      .taskSuccess (.executionGroup [0])
        { value := { path := [], data := [("x", .scalar "X")] } }
    parity "nested release" nested [[parentDone]]
    parity "nested same batch" nested [[parentDone, childDone]]
    let shared : Execution.Work :=
      .executionGroup [{ node := node 1 }, { node := node 2 }] [] result .empty
    parity "shared owners" shared [[simpleDone]]
    let staged := Execution.Work.combine simple simple
    let first : GraphEvent :=
      .taskSuccess (.executionGroup [0])
        { value := { path := [], data := [("x", .scalar "X")] } }
    let last : GraphEvent :=
      .taskSuccess (.executionGroup [1])
        { value := { path := [], data := [("x", .scalar "X")] } }
    parity "staged prefix" staged [[first]]
    parity "staged completion" staged [[first], [last]]
    parity "staged failure" staged [[first], [.taskFailure (.executionGroup [1]) 1]]
    let source : Execution.Work := .stream (node 4) [(.ok (.scalar "item", 0), child)]
    let admitted := item 0 (ReferenceWorkQueue.Work.fromExecution child [0])
    parity "item child release" source [[.streamItems (node 4) [admitted]]]
    parity "accepted child survives source failure" source
      [[.streamItems (node 4) [admitted]], [.streamFailure (node 4) 1], [childDone]]
    let held : Execution.Work := .stream (node 6) []
    let stagedSource :=
      Execution.Work.combine (.executionGroup [{ node := node 1 }] [] result held) simple
    let heldDone : GraphEvent :=
      .taskSuccess (.executionGroup [0])
        {
          value := { path := [], data := [("x", .scalar "X")] }
          work := ReferenceWorkQueue.Work.fromExecution held [0, 0]
        }
    parity "held source" stagedSource [[heldDone]]
    parity "held source failure disposal" stagedSource
      [[heldDone], [.taskFailure (.executionGroup [1]) 1]]
    let finite : Execution.Work :=
      .stream (node 4) ((List.range 128).map (fun _ => (.ok (.scalar "item", 0), .empty)))
    let batches : List (List GraphEvent) :=
      (List.range 128).map (fun index => [.streamItems (node 4) [item index {}]])
    parity "long stream prefix" finite (batches.take 64)
    parity "long stream completion" finite
      (batches ++ [[ReferenceWorkQueue.GraphEvent.streamSuccess (node 4)]])

end AlternativeRegistrationChecks
