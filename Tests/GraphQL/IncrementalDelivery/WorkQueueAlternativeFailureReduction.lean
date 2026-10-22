import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! Executable fused-removal checks, independent of implementation proof modules.
Raw fixtures isolate ownership/operation order; they are not native refinement witnesses.
-/

namespace AlternativeFailureReductionChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError name)

private def same [Repr α] (name : String) (actual expected : α) : IO Unit :=
  check name (reprStr actual == reprStr expected)

private def node (key : Nat) : Execution.DeliveryNode := { ref := key, path := [] }

private def task (id : Nat) (owners : List Nat) : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [id], groups := owners.map node }

private def shared : State :=
  {
    queue :=
      {
        rootGroups := [1, 2]
        registeredGroups := [1, 2]
        groupNodes :=
          [
            {
              group := { node := node 1 },
              tasks := [.executionGroup [9], .executionGroup [10]],
              pending := 2
            },
            {
              group := { node := node 2 },
              tasks := [.executionGroup [9], .executionGroup [10]],
              pending := 2
            }
          ]
        tasks := [task 9 [1, 2], task 10 [1, 2]]
        taskNodes :=
          [{ task := task 9 [1, 2] }, { task := task 10 [1, 2], childStreams := [7] }]
        streams := [{ node := node 7 }]
      }
  }

#eval
  do
    let (first, targets) := shared.removeGroup 1
    check "live co-owner prevents disposal" targets.isEmpty
    check "shared computation stays live"
      ((first.queue.taskNode? (.executionGroup [10])).isSome)
    let (last, allTargets) := first.removeGroup 2 targets
    same "last owner disposes tasks and held source in task order" allTargets
      [.task (.executionGroup [9]), .task (.executionGroup [10]), .stream 7]
    check "last-owner unlink drops the computation"
      ((last.queue.taskNode? (.executionGroup [10])).isNone)
    same "held-source operations are retained after unlinking"
      (allTargets.flatMap CleanupTarget.effects)
      [
        .abortTask (.executionGroup [9]),
        .abortTask (.executionGroup [10]),
        .cancelSource 7,
        .abortStreamQueue 7
      ]
    let failedCoOwner :=
      {
        shared with
          queue :=
            ({
              shared.queue with
                rootGroups := [1],
                taskNodes :=
                  [
                    { task := task 9 [1, 2], rejection := some 1 },
                    { task := task 10 [1, 2], childStreams := [7] }
                  ]
            }).putGroupNode
              {
                group := { node := node 2 }
                tasks := [.executionGroup [9], .executionGroup [10]]
                pending := 2
              }
      }
    check "failed but live dormant co-owner still owns work"
      (failedCoOwner.removeGroup 1).2.isEmpty
    let (failed, notices, effects) := shared.taskFailure (.executionGroup [9]) 2
    same "settling input is not aborted; shared source is disposed once"
      (effects.flatMap CleanupTarget.effects)
      [.abortTask (.executionGroup [10]), .cancelSource 7, .abortStreamQueue 7]
    same "both announced failed owners retain wire order" notices
      [.groupFailure (node 1) 2, .groupFailure (node 2) 2]
    same "direct failure retains reference accounting" failed.queue
      (shared.queue.taskFailure (.executionGroup [9]) 2).1
    let duplicateStreams :=
      {
        shared with
          queue :=
            {
              shared.queue with
                taskNodes :=
                  [
                    { task := task 9 [1, 2], childStreams := [7, 7] },
                    { task := task 10 [1, 2], childStreams := [7] }
                  ]
            }
      }
    let (removed, requested) := duplicateStreams.removeGroup 1 [.stream 7]
    let (_, requested) := removed.removeGroup 2 requested
    same "temporary cleanup prefix spans repeated tasks/sources and multiple cuts"
      requested [.stream 7, .task (.executionGroup [9]), .task (.executionGroup [10])]
    let tree : State :=
      {
        queue :=
          {
            rootGroups := [1]
            registeredGroups := [1, 3, 4]
            groupNodes :=
              [
                {
                  group := { node := node 1 },
                  childGroups := [99, 3, 4],
                  tasks := [.executionGroup [10]],
                  pending := 1
                },
                {
                  group := { node := node 3, parent := some 1 },
                  tasks := [.executionGroup [11]],
                  pending := 1
                },
                {
                  group := { node := node 4, parent := some 1 },
                  tasks := [.executionGroup [12]],
                  pending := 1
                }
              ]
            tasks := [task 10 [1], task 11 [3], task 12 [4]]
            taskNodes := [{ task := task 10 [1] }, { task := task 11 [3] }]
          }
      }
    let (pruned, targets) := tree.removeGroup 1
    same "task-before-child preorder includes unstarted tasks" targets
      [
        .task (.executionGroup [10]),
        .task (.executionGroup [11]),
        .task (.executionGroup [12])
      ]
    same "stale child links do not consume the live-node budget" pruned.queue
      (tree.queue.removeGroup 1)
    same "reference cancellation bookkeeping order" pruned.queue.cancelledGroups [4, 3, 1]
    let ready : State :=
      {
        queue :=
          {
            rootGroups := [1, 2]
            registeredGroups := [1, 2]
            groupNodes :=
              [
                { group := { node := node 1 }, tasks := [.executionGroup [10]] },
                {
                  group := { node := node 2 },
                  tasks := [.executionGroup [10], .executionGroup [11]],
                  pending := 1,
                }
              ]
            tasks := [task 10 [1, 2], task 11 [2]]
            taskNodes :=
              [
                {
                  task := task 10 [1, 2],
                  value := some { path := [], data := [] },
                  childStreams := [7]
                },
                { task := task 11 [2], rejection := some 1 }
              ]
            streams := [{ node := node 7 }]
          }
      }
    let (released, events, targets, queued) := ready.drainReadyGroups
    check "successful publication is transfer, not disposal" targets.isEmpty
    check "later co-owner failure cannot cancel a released source"
      (released.queue.rootStreams.contains 7)
    let reference := ready.queue.drainReadyGroups
    same "mixed success/failure drain keeps reference state" released.queue reference.1
    same "ready drain keeps reference immediate wire events" events reference.2.1
    same "ready drain keeps reference startup notices" queued reference.2.2
    let cached : State :=
      {
        queue :=
          {
            rootGroups := [1]
            registeredGroups := [1, 2]
            groupNodes :=
              [
                {
                  group := { node := node 1 },
                  childGroups := [2],
                  tasks := [.executionGroup [9]],
                  pending := 1
                },
                {
                  group := { node := node 2, parent := some 1 },
                  tasks := [.executionGroup [10], .executionGroup [11]],
                  pending := 2
                }
              ]
            tasks := [task 9 [1], task 10 [2], task 11 [2]]
            taskNodes :=
              [{ task := task 9 [1] }, { task := task 11 [2], rejection := some 2 }]
          }
      }
    let success : GraphEvent :=
      .taskSuccess (.executionGroup [9]) { value := { path := [], data := [] } }
    let reduced := ({ state := cached } : GraphBatchResult).handleGraphEvent success
    same "released cached failure disposes an unstarted task inline" reduced.effects
      [.adopt (.executionGroup [9]), .abortTask (.executionGroup [10])]
    same "cached failure uses the shared accounting result" reduced.state.queue
      (cached.queue.dispatchGraphEvent success).1
    same "cached failure keeps wire result" reduced.workQueueEvents
      (cached.queue.handleGraphEvent success).2.1
    same "cached startup failure is queued separately"
      reduced.state.queue.groupFailureEvents
      (cached.queue.dispatchGraphEvent success).1.groupFailureEvents
    let receipt : State :=
      { cached with queue := { cached.queue with rootGroups := [2], rootStreams := [4] } }
    let receiptInput : GraphEvent :=
      .streamItems (node 4)
        [{ occurrence := .item [] 0, value := { item := .scalar "item" } }]
    let receiptStep := receipt.handleGraphEvent receiptInput
    same "active cached failure waits for its FIFO notification" receiptStep.2.2.1
      [.adopt (.item [] 0), .acknowledge 4]
    let receiptBatch :=
      receipt.handleGraphEvents [receiptInput, .taskFailure (.executionGroup [11]) 2]
    same "receipt acknowledgement precedes FIFO failure cleanup" receiptBatch.effects
      [.adopt (.item [] 0), .acknowledge 4, .abortTask (.executionGroup [10])]
    same "receipt carrier precedes FIFO failure notice" receiptBatch.workQueueEvents
      [
        .streamValues (node 4) [{ item := .scalar "item" }] [] [],
        .groupFailure (node 2) 2
      ]

end AlternativeFailureReductionChecks
