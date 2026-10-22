import Tests.GraphQL.IncrementalDelivery.Execution

/-! Native-order regressions for PR #4870: declarations, activation, queued failure dispatch,
and wire-owner selection. Both queues consume the same complete GraphEvent FIFO.
-/

namespace GraphQL.IncrementalDelivery.Tests.GraphQLJsAlignment
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open ReferenceWorkQueue (GraphEvent InitialStartup)

private def complete (selections : List Selection) :=
  ((executeRootSelectionSetCore schema resolvers [] 40 "Query" (.object "Query" 0)
      selections).run
    0).1

private def success (work : Work) (address : Address) : GraphEvent :=
  let occurrence := Occurrence.executionGroup address
  match locateWork work address with
  | some {current := .executionGroup groups path outcome _, ..} =>
      match outcome.deliveryResult with
      | .ok (data, errors) =>
          .taskSuccess occurrence
            {
              value := {path, data, errors, deliveryGroups := groups.map (·.node)},
              work := (ReferenceWorkQueue.taskChildWork? work occurrence).getD {}
            }
      | .error errors => .taskFailure occurrence errors
  | _ => .taskFailure occurrence 0

private def notice (ref : NodeRef) (path : ResponsePath) (label : String) (errors : Nat)
    : GraphEvent :=
  .groupFailure ⟨{ref, path, label := some (.string label)}, errors⟩

private def both (completed : Completion (List (Name × ResponseValue)))
    (startup : InitialStartup) (inputs : List (List GraphEvent))
    : Bool :=
  let reference := ReferenceWorkQueue.replayIncrementalResponse completed inputs startup
  let alternative :=
    AlternativeWorkQueue.replayIncrementalResponse completed inputs startup
  ReferenceWorkQueue.inputsStarted completed.work inputs startup
  && same reference alternative
  && reference.2.2
  && alternative.2.2

-----------------------------------------------------------------------------------------
-- Creation refs are not registration order across response paths
-----------------------------------------------------------------------------------------

private def counted :=
  complete
    [
      field "user" [defer [field "required"] (some "A")],
      defer [field "user" [field "required"], field "required"] (some "P"),
      defer
        [field "b", defer [field "user" [field "required"], field "required"] (some "C")]
        (some "R")
    ]

private def countedStartup : InitialStartup :=
  {failures := [(.executionGroup [0,0,1,0],1), (.executionGroup [1,0],1)]}

private def countedInitial :=
  ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution counted.work) countedStartup

private def countedInputs : List (List GraphEvent) :=
  [[
    .taskFailure (.executionGroup [0,0,1,0]) 1,
    notice 0 [] "P" 1,
    success counted.work [1,1,0],
    notice 2 [] "C" 1
  ]]

private def countedResponse :=
  ReferenceWorkQueue.replayIncrementalResponse counted countedInputs countedStartup

-- Native integration registers user-level A before the enclosing plan's P and R.
#guard
  same (countedInitial.initialGroups.map (·.label))
    [some (.string "A"),some (.string "P"),some (.string "R")]
-- A's cached shared failure prevents P's private non-null task from starting.
#guard (countedInitial.taskNode? (.executionGroup [1,0])).isNone
#guard both counted countedStartup countedInputs
#guard (countedResponse.2.1.flatMap (·.completed)).map (·.errors) == [1,1,0,1]
#guard countedResponse.1.pending.map (·.id) == ["0","1","2"]
#guard (countedResponse.2.1.flatMap (·.pending)).map (·.id) == ["3"]

-----------------------------------------------------------------------------------------
-- A queued failure precedes later callbacks, including successful shared publication
-----------------------------------------------------------------------------------------

private def wired :=
  complete
    [
      field "user"
        [
          defer [field "required"] (some "A"),
          defer [field "required",field "name"] (some "B")
        ],
      defer [field "b",defer [field "user" [field "name"]] (some "C")] (some "P")
    ]

private def wiredStartup : InitialStartup := {failures := [(.executionGroup [0,0,1,0],1)]}

private def wiredInputs : List (List GraphEvent) :=
  [[
    .taskFailure (.executionGroup [0,0,1,0]) 1,
    notice 3 [.field "user"] "B" 1,
    success wired.work [1,0],
    success wired.work [0,0,1,1,0]
  ]]

private def wiredResponse :=
  ReferenceWorkQueue.replayIncrementalResponse wired wiredInputs wiredStartup

#guard both wired wiredStartup wiredInputs
#guard
  same (wiredResponse.1.pending.map (·.label))
    [some (.string "A"),some (.string "B"),some (.string "P")]
#guard (wiredResponse.2.1.flatMap (·.completed)).map (·.id) == ["0","1","2","3"]
-- B's notice has already retired its ID: C owns the shared value, with subPath user.
#guard
  same (wiredResponse.2.1.flatMap (·.incremental))
    [
      .object "2" [("b",.scalar "b")] 0 [],
      .object "3" [("name",.scalar "name1")] 0 [.field "user"]
    ]

private def ordered :=
  complete
    [
      defer [field "required"] (some "A"),
      defer [field "required",field "a"] (some "B"),
      defer [field "b"] (some "C")
    ]

private def orderedStartup : InitialStartup := {failures := [(.executionGroup [1,0],1)]}

private def orderedInputs : List (List GraphEvent) :=
  [[
    .taskFailure (.executionGroup [1,0]) 1,
    notice 1 [] "B" 1,
    success ordered.work [1,1,1,0]
  ]]

private def orderedResponse :=
  ReferenceWorkQueue.replayIncrementalResponse ordered orderedInputs orderedStartup
#guard both ordered orderedStartup orderedInputs
#guard (orderedResponse.2.1.flatMap (·.completed)).map (·.id) == ["0","1","2"]

-----------------------------------------------------------------------------------------
-- Same-path declaration order and cached multi-task aggregates remain native
-----------------------------------------------------------------------------------------

private def shared :=
  complete
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
    ]

private def sharedStartup : InitialStartup :=
  {failures := [(.executionGroup [1,0],1),(.executionGroup [1,1,0],1)]}

private def sharedInitial :=
  ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution shared.work) sharedStartup

private def sharedInputs : List (List GraphEvent) :=
  [[
    .taskFailure (.executionGroup [1,0]) 1,
    .taskFailure (.executionGroup [1,1,0]) 1,
    notice 2 [] "R3" 2
  ]]
#guard sharedInitial.initialGroups.map (·.ref) == [0,1,2]
#guard (sharedInitial.taskNode? (.executionGroup [1,1,1,0])).isNone
#guard both shared sharedStartup sharedInputs
#guard
  ((ReferenceWorkQueue.replayIncrementalResponse shared sharedInputs
      sharedStartup).2.1.flatMap
    (·.completed)).map
    (·.errors)
  == [1,1,2]

-----------------------------------------------------------------------------------------
-- Newly released groups inspect all available causes before FIFO notifications
-----------------------------------------------------------------------------------------

private def cached :=
  complete
    [
      defer [field "required" [] [] (some "first")] (some "R1"),
      defer [field "required" [] [] (some "second")] (some "R2"),
      defer
        [
          field "b",
          defer
            [
              field "required" [] [] (some "first"),
              field "required" [] [] (some "second"),
              field "a"
            ]
            (some "C")
        ]
        (some "P")
    ]

private def cachedInputs : List (List GraphEvent) :=
  [[
    success cached.work [1,1,1,0],
    .taskFailure (.executionGroup [1,0]) 1,
    .taskFailure (.executionGroup [1,1,0]) 1,
    notice 3 [] "C" 2
  ]]
#guard both cached {} cachedInputs
#guard
  ((ReferenceWorkQueue.replayIncrementalResponse cached cachedInputs).2.1.flatMap
    (·.completed)).map
    (·.errors)
  == [0,1,1,2]

-----------------------------------------------------------------------------------------
-- Queue provenance and persistence across replay boundaries
-----------------------------------------------------------------------------------------

#guard sharedInitial.acceptsGraphEvent (notice 2 [] "R3" 2)
#guard !sharedInitial.acceptsGraphEvent (notice 2 [] "R3" 1)
#guard !sharedInitial.acceptsGraphEvent (notice 0 [] "R1" 2)
#guard
  same (sharedInitial.runNormalized []).1.groupFailureEvents
    sharedInitial.groupFailureEvents
private def beforeNotice :=
  sharedInitial.handleGraphEvents
    [.taskFailure (.executionGroup [1,0]) 1, .taskFailure (.executionGroup [1,1,0]) 1]
#guard !beforeNotice.1.terminated
#guard beforeNotice.1.rootGroups.isEmpty
#guard beforeNotice.1.groupFailureEvents.length == 1
private def afterNotice := beforeNotice.1.handleGraphEvents [notice 2 [] "R3" 2]
#guard afterNotice.1.terminated
#guard afterNotice.1.groupFailureEvents.isEmpty
#guard !afterNotice.1.acceptsGraphEvent (notice 2 [] "R3" 2)

-----------------------------------------------------------------------------------------
-- Overlapping fields can declare a child before its parent
-----------------------------------------------------------------------------------------

private def childFirst :=
  complete
    [
      field "user" [field "name"],
      defer [field "user" [defer [field "age"] (some "C")]] (some "P"),
      field "users" [defer [field "name"] (some "A")]
    ]

private def childFirstWork := ReferenceWorkQueue.Work.fromExecution childFirst.work

private def childFirstRegistration :=
  ({} : ReferenceWorkQueue.State).addGroups childFirstWork.groups

private def childFirstInitial := ReferenceWorkQueue.State.initialize childFirstWork

-- Collection allocates P first, but immediate field completion declares C before P.
#guard childFirstWork.groups.map (fun group => group.node.ref) == [1,2,3,0]
-- Visiting C first installs P before its child and before the unrelated A roots.
#guard childFirstRegistration.1.registeredGroups == [0,1,2,3]
#guard childFirstRegistration.2.map (·.ref) == [0,2,3]
-- Pruning P's empty shell promotes C at P's position in the root traversal.
#guard childFirstInitial.initialGroups.map (·.ref) == [1,2,3]

private def childFirstInputs : List (List GraphEvent) :=
  [childFirstWork.tasks.map
    (fun task =>
      match task.occurrence with
      | .executionGroup address => success childFirst.work address
      | .item _ _ => .taskFailure task.occurrence 0)]

private def childFirstResponse :=
  ReferenceWorkQueue.replayIncrementalResponse childFirst childFirstInputs

#guard both childFirst {} childFirstInputs
#guard
  same
    (childFirstResponse.1.pending.map
      (fun pending => (pending.id,pending.label,pending.path)))
    [
      ("0",some (.string "C"),[.field "user"]),
      ("1",some (.string "A"),[.field "users",.index 0]),
      ("2",some (.string "A"),[.field "users",.index 1])
    ]
#guard
  same (childFirstResponse.2.1.flatMap (·.incremental))
    [
      .object "0" [("age",.scalar "1")] 0 [],
      .object "1" [("name",.scalar "name1")] 0 [],
      .object "2" [("name",.scalar "name2")] 0 []
    ]
#guard (childFirstResponse.2.1.flatMap (·.completed)).map (·.id) == ["0","1","2"]

-----------------------------------------------------------------------------------------
-- Parent recursion fixes child-link order and propagates removed-parent refusal
-----------------------------------------------------------------------------------------

private def candidate (ref : NodeRef) (parent : Option NodeRef := none)
    : ReferenceWorkQueue.Group :=
  {node := {ref, path := []}, parent}

private def nestedCandidates :=
  [
    candidate 4 (some 2),
    candidate 3 (some 1),
    candidate 2 (some 1),
    candidate 1,
    candidate 5,
    candidate 2 (some 1)
  ]

private def nestedRegistration :=
  ({} : ReferenceWorkQueue.State).addGroups nestedCandidates

#guard nestedRegistration.1.registeredGroups == [1,2,4,3,5]
#guard nestedRegistration.2.map (·.ref) == [1,5]
#guard (nestedRegistration.1.groupNode? 1).map (·.childGroups) == some [2,3]
#guard (nestedRegistration.1.groupNode? 2).map (·.childGroups) == some [4]

private def refusedCandidates :=
  [candidate 20 (some 30), candidate 1, candidate 30 (some 70)]

private def failedParent : ReferenceWorkQueue.State :=
  {registeredGroups := [70], cancelledGroups := [70]}

private def refusedRegistration := failedParent.addGroups refusedCandidates

#guard refusedRegistration.1.registeredGroups == [70,30,20,1]
#guard refusedRegistration.1.cancelledGroups == [70,30,20]
#guard refusedRegistration.1.groupNodes.map (fun node => node.group.node.ref) == [1]
#guard refusedRegistration.2.map (·.ref) == [1]
-- Repeated raw ancestry cannot reinstall either discarded record or reannounce the root.
#guard (refusedRegistration.1.addGroups refusedCandidates).2.isEmpty
#guard same (refusedRegistration.1.addGroups refusedCandidates).1 refusedRegistration.1

-- Missing live parents also refuse installation after successful retirement; no failure
-- marker is invented for that case.
private def retiredParent : ReferenceWorkQueue.State := {registeredGroups := [70]}
private def retiredRegistration := retiredParent.addGroups [candidate 30 (some 70)]
#guard retiredRegistration.1.registeredGroups == [70,30]
#guard retiredRegistration.1.groupNodes.isEmpty
#guard retiredRegistration.1.cancelledGroups.isEmpty
#guard retiredRegistration.2.isEmpty

-----------------------------------------------------------------------------------------
-- Callback eligibility survives starting and retiring within one native batch
-----------------------------------------------------------------------------------------

private def withinBatchSelections : List Selection :=
  [defer
    [
      field "a",
      defer
        [field "required" [] [] (some "first"), field "required" [] [] (some "second")]
        (some "A"),
      defer [field "required" [] [] (some "second")] (some "B")
    ]
    (some "P")]

private def withinBatch := complete withinBatchSelections

private theorem withinBatch_generated
    : ReferenceWorkQueue.ExecutedWork withinBatch.work := by
  exact ⟨Nat, schema, resolvers, [], 40, "Query", .object "Query" 0,
    withinBatchSelections, rfl⟩

private def withinBatchParent := success withinBatch.work [1,0]
private def withinBatchFirst : GraphEvent := .taskFailure (.executionGroup [1,1,0]) 1
private def withinBatchSecond : GraphEvent := .taskFailure (.executionGroup [1,1,1,0]) 1
private def withinBatchNotice := notice 2 [] "B" 1

private def withinBatchInputs : List GraphEvent :=
  [withinBatchParent, withinBatchFirst, withinBatchSecond, withinBatchNotice]

private def withinBatchInitial :=
  ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution withinBatch.work)

private def withinBatchAvailable := GraphEvent.availableFailures withinBatchInputs

private def withinBatchReleased :=
  (withinBatchInitial.dispatchGraphEvent withinBatchParent withinBatchAvailable).1

private def withinBatchRetired :=
  (withinBatchReleased.dispatchGraphEvent withinBatchFirst withinBatchAvailable).1

-- The shared task is live after P, but absent at entry and after A's failure.
#guard !withinBatchInitial.acceptsGraphEvent withinBatchSecond
#guard withinBatchReleased.acceptsGraphEvent withinBatchSecond
#guard !withinBatchRetired.acceptsGraphEvent withinBatchSecond
#guard withinBatchInitial.acceptsBatch withinBatchInputs
#guard both withinBatch {} [withinBatchInputs]

private def withinBatchResponse :=
  ReferenceWorkQueue.replayIncrementalResponse withinBatch [withinBatchInputs]

#guard (withinBatchResponse.2.1.flatMap (·.completed)).map (·.errors) == [0,1,1]
#guard (withinBatchResponse.2.1.flatMap (·.completed)).map (·.id) == ["0","1","2"]

-- Removing the stale callback also removes its available rejection and B's queued notice.
#guard
  !withinBatchInitial.acceptsBatch [withinBatchParent,withinBatchFirst,withinBatchNotice]
-- Earlier eligibility belongs to this batch only, and never licenses internal notices.
#guard !withinBatchRetired.acceptsBatch [withinBatchSecond]
#guard !withinBatchInitial.acceptsBatch [withinBatchNotice,withinBatchParent]
#guard !withinBatchInitial.acceptsBatch (withinBatchInputs ++ [withinBatchNotice])
#guard !withinBatchInitial.acceptsBatch [.taskFailure (.executionGroup [99]) 1]

end GraphQL.IncrementalDelivery.Tests.GraphQLJsAlignment
