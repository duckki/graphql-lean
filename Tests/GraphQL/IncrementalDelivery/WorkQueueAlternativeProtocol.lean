import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReaderLifecycle
import Tests.GraphQL.IncrementalDelivery.Fixtures.WorkDeclarations

open GraphQL.IncrementalDelivery.Tests (declaredTask)

namespace AlternativeProtocolChecks
open GraphQL (Name)
open GraphQL.IncrementalDelivery
open Execution
open WorkQueueSemantics

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError name)

private def same [Repr α] (name : String) (left right : α) : IO Unit :=
  check name (reprStr left == reprStr right)

private def group : DeliveryNode := { ref := 0, path := [] }
private def child : DeliveryNode := { ref := 2, path := [] }
private def stream : DeliveryNode := { ref := 1, path := [] }
private def held : DeliveryNode := { ref := 3, path := [] }
private def response : Response := { data := .object [] }

private def value (owners : List DeliveryNode) : ExecutionGroupValue :=
  { deliveryGroups := owners, path := [], data := [("x", .scalar "X")] }

private def task (owners : List DeferredFragment) (children : Execution.Work := .empty)
    : Execution.Work :=
  declaredTask owners [] ({ result := .ok ([("x", .scalar "X")], 0) }) children

private def success (occurrence : Occurrence) (owners : List DeliveryNode)
    (work : ReferenceWorkQueue.Work := {})
    : ReferenceWorkQueue.GraphEvent :=
  .taskSuccess occurrence { value := value owners, work }

private def item (address : Address) (index : Nat) (work : ReferenceWorkQueue.Work := {})
    : ReferenceWorkQueue.StreamItem :=
  { occurrence := .item address index, value := { item := .scalar "I" }, work }

private def parity (name : String) (work : Execution.Work)
    (inputs : List (List ReferenceWorkQueue.GraphEvent))
    : IO Unit := do
  let reference :=
    (ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution work)).runNormalized
      inputs
  let actual := (AlternativeWorkQueue.State.initialize work).runNormalized inputs
  same (name ++ ": normalized output") actual.2 reference.2
  same (name ++ ": projected state") actual.1
    (AlternativeWorkQueue.State.fromReference reference.1)
  let completed : Completion (List (Name × ResponseValue)) :=
    { result := .ok ([], 0), work }
  same (name ++ ": response replay")
    (AlternativeWorkQueue.replayIncrementalResponse completed inputs)
    (ReferenceWorkQueue.replayIncrementalResponse completed inputs)
  let (updates, cursor, effects) :=
    (AlternativeWorkQueue.ResponseStreamCursor.buildResponse response work).2.run inputs
  let (expected, _, _) :=
    (ReferenceWorkQueue.initializeIncrementalResponse response work).2.1.run
      (ReferenceWorkQueue.initializeIncrementalResponse response work).2.2 inputs
  same (name ++ ": cursor updates") updates expected
  check (name ++ ": termination/finish agree")
    (cursor.finished == cursor.queue.queue.terminated)
  if cursor.finished then
    check (name ++ ": terminal IDs cleared") cursor.publisher.ids.ids.isEmpty
    check (name ++ ": terminal active cleared") cursor.publisher.active.isEmpty
    check (name ++ ": terminal tasks cleared") cursor.queue.queue.tasks.isEmpty
    check (name ++ ": terminal streams cleared") cursor.queue.queue.streams.isEmpty
    check (name ++ ": once-only finish")
      ((effects.filter
          (fun effect =>
            match effect with
            | .responseFinished => true
            | _ => false)).length
        == 1)
    let (_, late, lateActions) := cursor.handleBatch inputs.flatten
    same (name ++ ": late step unchanged") late cursor
    check (name ++ ": late step silent") lateActions.isEmpty

#eval
  do
    let simple := task [{ node := group }]
    let settled := success (.executionGroup []) [group]
    parity "simple stagedPrefix" simple []
    parity "empty host batches" simple [[], []]
    parity "simple complete" simple [[settled]]
    parity "finished late/empty batches" simple [[settled], [], [settled]]
    let childWork := task [{ node := child, ancestors := [group] }]
    let nested := task [{ node := group }] childWork
    let parent :=
      success (.executionGroup []) [group]
        (ReferenceWorkQueue.Work.fromExecution childWork [0])
    let childDone := success (.executionGroup [0]) [child]
    parity "nested stagedPrefix" nested [[parent]]
    parity "nested separate batches" nested [[parent], [childDone]]
    parity "nested single batch" nested [[parent, childDone]]
    for errors in [0, 1, 4] do
      let failure : Execution.Work :=
        declaredTask [{ node := group }] [] ({ result := .error errors }) .empty
      parity ("fatal " ++ toString errors) failure
        [[.taskFailure (.executionGroup []) errors]]
    let shared := task [{ node := group }, { node := child }]
    parity "shared owners" shared [[success (.executionGroup []) [group, child]]]
    let two := Execution.Work.combine simple simple
    parity "shared staging stagedPrefix" two [[success (.executionGroup [0]) [group]]]
    parity "shared staging complete" two
      [[success (.executionGroup [0]) [group]], [success (.executionGroup [1]) [group]]]
    parity "shared staging failure" two
      [[success (.executionGroup [0]) [group]], [.taskFailure (.executionGroup [1]) 0]]
    let finite : Execution.Work :=
      .stream stream
        ((List.range 128).map (fun _ => ({ result := .ok (.scalar "I", 0) }, .empty)))
    let streamBatches :=
      (List.range 128).map
        (fun index => [ReferenceWorkQueue.GraphEvent.streamItems stream [item [] index]])
    parity "long stream stagedPrefix" finite (streamBatches.take 64)
    parity "long stream complete" finite
      (streamBatches ++ [[ReferenceWorkQueue.GraphEvent.streamSuccess stream]])
    parity "source failure" finite
      [[.streamItems stream [item [] 0]], [.streamFailure stream 2]]
    parity "empty boundary" (.stream stream []) [[.streamSuccess stream]]
    let childStream : Execution.Work :=
      .stream stream [({ result := .ok (.scalar "I", 0) }, childWork)]
    let sourceItem := item [] 0 (ReferenceWorkQueue.Work.fromExecution childWork [0])
    parity "accepted child survives source failure" childStream
      [[.streamItems stream [sourceItem]], [.streamFailure stream 1], [childDone]]
    let reduced :=
      (AlternativeWorkQueue.State.initialize finite).handleGraphEvents
        [.streamItems stream [item [] 0, item [] 1], .streamFailure stream 2]
    same "FIFO adoption/ack/source cancellation" reduced.effects
      [
        AlternativeWorkQueue.HostEffect.adopt (.item [] 0),
        .adopt (.item [] 1),
        .acknowledge stream.ref,
        .cancelSource stream.ref
      ]
    let taskActions :=
      (AlternativeWorkQueue.State.initialize simple).handleGraphEvents [settled]
    same "task ownership handoff" taskActions.effects
      [AlternativeWorkQueue.HostEffect.adopt (.executionGroup [])]
    let stagedPrefix :=
      (AlternativeWorkQueue.State.initialize two).handleGraphEvents
        [success (.executionGroup [0]) [group]]
    let (stopped, cancelled) := stagedPrefix.state.cancel
    same "shared tasks deduplicated" cancelled
      [
        AlternativeWorkQueue.HostEffect.abortTask (.executionGroup [0]),
        .abortTask (.executionGroup [1])
      ]
    check "early stop not work completion" (!stopped.queue.terminated)
    check "stop clears accounting"
      (stopped.queue.tasks.isEmpty && stopped.queue.groupNodes.isEmpty)
    check "repeat stop silent" (stopped.cancel.2.isEmpty)
    let heldWork : Execution.Work := .stream held []
    let stagedWork := Execution.Work.combine (task [{ node := group }] heldWork) simple
    let staged :=
      (AlternativeWorkQueue.State.initialize stagedWork).handleGraphEvents
        [success (.executionGroup [0]) [group]
          (ReferenceWorkQueue.Work.fromExecution heldWork [0, 0])]
    same "held streams included before child traversal" staged.state.cancel.2
      [
        AlternativeWorkQueue.HostEffect.abortTask (.executionGroup [0]),
        .cancelSource held.ref,
        .abortStreamQueue held.ref,
        .abortTask (.executionGroup [1])
      ]
    same "cancelTask observes abort identity before held sources"
      (staged.state.cancelTask (.executionGroup [0]))
      [AlternativeWorkQueue.CleanupTarget.task (.executionGroup [0]), .stream held.ref]
    same "cancelGroup preserves task-before-child traversal"
      (staged.state.cancelGroup (staged.state.queue.groupNodes.length + 1) [group.ref] [])
      [
        AlternativeWorkQueue.CleanupTarget.task (.executionGroup [0]),
        .stream held.ref,
        .task (.executionGroup [1])
      ]
    same "cancelStream cancels producer before queue"
      (AlternativeWorkQueue.cancelStream held.ref)
      [AlternativeWorkQueue.HostEffect.cancelSource held.ref, .abortStreamQueue held.ref]
    let discarded := staged.state.handleGraphEvents [.taskFailure (.executionGroup [1]) 1]
    same "failure disposes held stream before retirement" discarded.effects
      [
        AlternativeWorkQueue.HostEffect.abortTask (.executionGroup [0]),
        .cancelSource held.ref,
        .abortStreamQueue held.ref
      ]
    check "terminal stop cannot repeat pruning cleanup" discarded.state.cancel.2.isEmpty
    let other : DeliveryNode := { ref := 4, path := [] }
    let sharedHeld :=
      Execution.Work.combine
        (task [{ node := group }, { node := other }] heldWork)
        (Execution.Work.combine simple (task [{ node := other }]))
    let sharedStaged :=
      (AlternativeWorkQueue.State.initialize sharedHeld).handleGraphEvents
        [success (.executionGroup [0]) [group, other]
          (ReferenceWorkQueue.Work.fromExecution heldWork [0, 0])]
    let surviving :=
      sharedStaged.state.handleGraphEvents [.taskFailure (.executionGroup [1, 0]) 1]
    check "shared healthy owner prevents disposal" surviving.effects.isEmpty
    check "shared held source still reachable"
      (surviving.state.cleanupTargets.contains (.stream held.ref))
    let lastOwner :=
      surviving.state.handleGraphEvents [.taskFailure (.executionGroup [1, 1]) 1]
    same "last owner disposes shared held source once" lastOwner.effects
      [
        AlternativeWorkQueue.HostEffect.abortTask (.executionGroup [0]),
        .cancelSource held.ref,
        .abortStreamQueue held.ref
      ]
    let releasedWork :=
      Execution.Work.combine
        (task [{ node := group }, { node := other }] heldWork) (task [{ node := other }])
    let released :=
      (AlternativeWorkQueue.State.initialize releasedWork).handleGraphEvents
        [
          success (.executionGroup [0]) [group, other]
            (ReferenceWorkQueue.Work.fromExecution heldWork [0, 0]),
          .taskFailure (.executionGroup [1]) 1
        ]
    same "successful transfer survives co-owner failure" released.effects
      [AlternativeWorkQueue.HostEffect.adopt (.executionGroup [0])]
    check "released source stays active"
      (released.state.queue.rootStreams.contains held.ref)
    let parentTask : ReferenceWorkQueue.Task := ⟨.executionGroup [], [group]⟩
    let childTask : ReferenceWorkQueue.Task := ⟨.executionGroup [0], [child]⟩
    let retained : AlternativeWorkQueue.State :=
      {
        queue :=
          {
            rootGroups := [group.ref]
            groupNodes :=
              [
                {
                  group := ⟨group, none⟩,
                  childGroups := [child.ref],
                  tasks := [parentTask.occurrence],
                  pending := 1
                },
                {
                  group := ⟨child, some group.ref⟩,
                  tasks := [childTask.occurrence, .executionGroup [99]],
                  pending := 2
                }
              ]
            tasks := [parentTask, childTask, ⟨.executionGroup [99], [child]⟩]
            taskNodes :=
              [
                { task := parentTask },
                { task := childTask, childStreams := [held.ref] },
                { task := ⟨.executionGroup [99], [child]⟩, rejection := some 1 }
              ]
            streams := [⟨held⟩]
          }
      }
    let drained := retained.handleGraphEvents [success parentTask.occurrence [group]]
    same "success release drains retained failure with disposal" drained.effects
      [
        AlternativeWorkQueue.HostEffect.adopt parentTask.occurrence,
        .abortTask childTask.occurrence,
        .cancelSource held.ref,
        .abortStreamQueue held.ref
      ]
    let (_, cursor) :=
      AlternativeWorkQueue.ResponseStreamCursor.buildResponse response two
    let (closed, effects) := cursor.close
    same "cleanup before completion hook" effects
      [
        AlternativeWorkQueue.HostEffect.abortTask (.executionGroup [0]),
        .abortTask (.executionGroup [1]),
        .responseFinished
      ]
    check "reader close distinct from work completion"
      (closed.finished && !closed.queue.queue.terminated)
    check "closed registry cleared"
      (closed.publisher.ids.ids.isEmpty && closed.publisher.active.isEmpty)
    check "ID counter preserved"
      (closed.publisher.ids.nextID == cursor.publisher.ids.nextID)
    check "repeat close silent" closed.close.2.isEmpty
    let (late, unchanged, effects) :=
      closed.handleBatch [success (.executionGroup [0]) [group]]
    check "closed late update suppressed" late.isNone
    same "closed late cursor unchanged" unchanged closed
    check "closed late effects suppressed" effects.isEmpty
    let rawEnded : AlternativeWorkQueue.State := { queue := { terminated := true } }
    check "terminated kernel guard"
      (rawEnded.handleGraphEvents [settled]).workQueueEvents.isEmpty
    let rootSource := AlternativeWorkQueue.State.initialize (.stream stream [])
    same "stop cancels source before queue abort" rootSource.cancel.2
      [
        AlternativeWorkQueue.HostEffect.cancelSource stream.ref,
        .abortStreamQueue stream.ref
      ]
    let sourceFailure := rootSource.handleGraphEvents [.streamFailure stream 1]
    same "source failure does not abort stream Queue" sourceFailure.effects
      [AlternativeWorkQueue.HostEffect.cancelSource stream.ref]
    let duplicated : AlternativeWorkQueue.State :=
      { queue := { rootStreams := [stream.ref, stream.ref] } }
    same "one cancel/abort pair per cleanup target" duplicated.cancel.2
      [
        AlternativeWorkQueue.HostEffect.cancelSource stream.ref,
        .abortStreamQueue stream.ref
      ]
    let (_, sourceCursor) :=
      AlternativeWorkQueue.ResponseStreamCursor.buildResponse response (.stream stream [])
    same "source cleanup precedes response finish" sourceCursor.close.2
      [
        AlternativeWorkQueue.HostEffect.cancelSource stream.ref,
        .abortStreamQueue stream.ref,
        .responseFinished
      ]
    IO.println "19 reference replay fixtures and host-protocol checks passed."

end AlternativeProtocolChecks

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-- Pin the exact public targets rather than only fixture behavior.
example : replayMatchesReference := replayMatchesReference_holds

example : createWorkQueueForScheduleMatchesReference :=
  createWorkQueueForScheduleMatchesReference_holds

example : responseReplayMatchesReference := responseReplayMatchesReference_holds
example : createWorkQueueForScheduleConforms := createWorkQueueForScheduleConforms_holds

#print axioms replayMatchesReference_holds
#print axioms createWorkQueueForScheduleMatchesReference_holds
#print axioms responseReplayMatchesReference_holds
#print axioms createWorkQueueForScheduleConforms_holds
#print axioms State.cancel_cleanupStarts_nodup
#print axioms State.taskFailure_cleanupStarts_nodup
#print axioms State.disposeRejectedTasks_nodup
#print axioms State.streamItems_adoptedProducers
#print axioms State.streamItems_consumptionBoundary
#print axioms State.streamItems_acknowledges_once
#print axioms State.streamItems_cleanupStarts_nodup
#print axioms State.taskSuccess_cleanupStarts_nodup
#print axioms State.handleGraphEvent_noFinish
#print axioms ResponseStreamCursor.run_finishCount_le_one

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
