import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Definition-level regressions for outcomes settled before their owner's announcement.
These checks intentionally do not import implementation proofs awaiting migration.
-/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedOutcomes
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated fixtures: an independent owner R and a child C waiting for P
-----------------------------------------------------------------------------------------

private def root : DeliveryNode := { ref := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { ref := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 2, path := [], label := some (.string "C") }
private def firstTask : Occurrence := .executionGroup [1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def parentData : List (Name × ResponseValue) := [("b", .scalar "b")]
private def sharedData : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work (sharedResult : Result (List (Name × ResponseValue))) : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] sharedResult
          (match sharedResult with
            | .ok _ => .combine .empty .empty
            | .error _ => .empty))
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (parentData, 0))
            (.combine .empty .empty))
          .empty)))

private def failureWork : Execution.Work := work (.error 2)
private def successWork : Execution.Work := work (.ok (sharedData, 0))

private def cancellationWork : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩] [] (.error 1) .empty)
      (.combine (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] (.error 2) .empty)
        (.combine (.executionGroup [⟨parent, []⟩] [] (.error 1) .empty) .empty)))

private def first : GraphEvent := .taskFailure firstTask 1
private def sharedFailure : GraphEvent := .taskFailure sharedTask 2

private def sharedValue : ExecutionGroupValue :=
  { deliveryGroups := [root, child], path := [], data := sharedData }

private def sharedSuccess : GraphEvent :=
  .taskSuccess sharedTask
    {
      value := sharedValue,
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 0, 0]
    }

private def parentValue : ExecutionGroupValue :=
  { deliveryGroups := [parent], path := [], data := parentData }

private def finish : GraphEvent :=
  .taskSuccess parentTask
    {
      value := parentValue,
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def queue (work : Execution.Work) : State :=
  State.initialize (Work.fromExecution work)

private def updates (work : Execution.Work) (inputs : List (List GraphEvent))
    : List IncrementalStreamUpdateResult :=
  ((ResponseStreamCursor.initialize { data := .object [] } work).2.run inputs).1

/-- The two-error shared failure comes from actual query execution.
Witness: reduction of the pure resolver fixture, including its nullable field error.
-/
theorem failure_generated : ExecutedWork failureWork := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first"), field "fail", field "required"]
        (some "R"),
      defer [field "b", defer [field "fail", field "required"] (some "C")] (some "P")],
    ?_⟩
  cbv

/-- The successful shared value also comes from generated work, not a raw queue fixture.
Witness: reduction of the corresponding query with a successful shared field.
-/
theorem success_generated : ExecutedWork successWork := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first"), field "a"] (some "R"),
      defer [field "b", defer [field "a"] (some "C")] (some "P")], ?_⟩
  cbv

/-- Parent cancellation is also exercised on generated, fixed-outcome work.
Witness: the independent parent field is a second failing non-null alias.
-/
theorem cancellation_generated : ExecutedWork cancellationWork := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first"), field "fail", field "required"]
        (some "R"),
      defer [field "required" [] [] (some "second"),
        defer [field "fail", field "required"] (some "C")] (some "P")], ?_⟩
  cbv

/-- Both shared settlements and parent results match their generated source payloads.
Witness: structural addresses, exact contributor lists, and separately lowered child work.
-/
theorem source_payloads
    : sharedFailure.MatchesWork failureWork
      ∧ sharedSuccess.MatchesWork successWork
      ∧ finish.MatchesWork failureWork
      ∧ finish.MatchesWork successWork := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨[root.ref, child.ref], none, [], ?_⟩
    exact ⟨[⟨root, []⟩, ⟨child, [parent]⟩], [], .error 2, .empty, [], rfl, rfl, rfl⟩
  · refine ⟨[root.ref, child.ref], none, ?_, rfl, rfl⟩
    exact ⟨[⟨root, []⟩, ⟨child, [parent]⟩], [], .ok (sharedData, 0),
      .combine .empty .empty, [], rfl, rfl, rfl⟩
  · refine ⟨[parent.ref], none, ?_, rfl, rfl⟩
    exact ⟨[⟨parent, []⟩], [], .ok (parentData, 0), .combine .empty .empty,
      [], rfl, rfl, rfl⟩
  · refine ⟨[parent.ref], none, ?_, rfl, rfl⟩
    exact ⟨[⟨parent, []⟩], [], .ok (parentData, 0), .combine .empty .empty,
      [], rfl, rfl, rfl⟩

/-- Both settlement orders remain eligible under the unchanged start checker.
Witness: executable start/handler replay, including the silent middle settlement.
-/
theorem inputs_started
    : inputsStarted failureWork [[first], [sharedFailure], [finish]] = true
      ∧ inputsStarted failureWork [[sharedFailure], [finish]] = true
      ∧ inputsStarted successWork [[first], [sharedSuccess], [finish]] = true
      ∧ inputsStarted successWork [[first], [finish], [sharedSuccess]] = true := by
  cbv

-----------------------------------------------------------------------------------------
-- Failures wait for announcement without needing an extra response update
-----------------------------------------------------------------------------------------

/-- A latent failure survives without an early notice or completion.
Witness: replay leaves C's error retained and the still-active parent unfinished.
-/
theorem failure_retained
    : let before := ((queue failureWork).handleGraphEvents [first]).1
      let (after, events) := before.handleGraphEvents [sharedFailure]
      events = []
      ∧ (after.groupNode? child.ref).map GroupNode.failure = some (some 2)
      ∧ (after.pruneEmptyGroups [child]).2 = [child]
      ∧ after.rootGroups = [parent.ref]
      ∧ after.terminated = false := by
  cbv

/-- Normal parent release announces C before reporting its retained error.
Witness: exact normalized output; the silent source settlement adds no output batch.
-/
theorem failure_released
    : ((queue failureWork).runNormalized [[first], [sharedFailure], [finish]]).2
      = [
        [.groupFailure root 1],
        [
          .groupValues parent
            [{ path := [], data := parentData, errors := 0, deliveryGroups := [parent] }],
          .groupSuccess parent [child] [],
          .groupFailure child 2,
          .workQueueTermination
        ]
      ] := by
  cbv

/-- Pending and failed completion for C share one update with P's release.
Witness: the actual queue, publisher, and response mapper allocate C's ID before use.
-/
theorem failure_wire
    : updates failureWork [[first], [sharedFailure], [finish]]
      = [
        { hasNext := true, completed := [{ id := "0", errors := 1 }] },
        {
          hasNext := false,
          pending := [{ id := "2", path := [], label := child.label }],
          incremental := [.object "1" parentData],
          completed := [{ id := "1" }, { id := "2", errors := 2 }]
        }
      ] := by
  cbv

/-- Coalesced source inputs require only one wire update, not a separate error flush.
Witness: direct response-cursor reduction with the same three settlements in one batch.
-/
theorem failure_one_batch
    : updates failureWork [[first, sharedFailure, finish]]
      = [{
          hasNext := false,
          pending := [{ id := "2", path := [], label := child.label }],
          incremental := [.object "1" parentData],
          completed :=
            [{ id := "0", errors := 1 }, { id := "1" }, { id := "2", errors := 2 }]
        }] := by
  cbv

/-- Reporting the failure through R does not silently discard C's later lifecycle.
Witness: an initially shared failure completes R now and C on normal parent release.
-/
theorem shared_failure_before_owner_closes
    : updates failureWork [[sharedFailure], [finish]]
      = [
        { hasNext := true, completed := [{ id := "0", errors := 2 }] },
        {
          hasNext := false,
          pending := [{ id := "2", path := [], label := child.label }],
          incremental := [.object "1" parentData],
          completed := [{ id := "1" }, { id := "2", errors := 2 }]
        }
      ] := by
  cbv

/-- A genuinely failed parent cancels its latent child instead of announcing it.
Witness: queue-handler reduction on the generated failing-parent fixture.
-/
theorem parent_failure_cancels
    : let before := ((queue cancellationWork).handleGraphEvents [first, sharedFailure]).1
      let (after, events) := before.handleGraphEvents [.taskFailure parentTask 1]
      events = [.groupFailure parent 1, .workQueueTermination]
      ∧ after.groupNode? child.ref = none
      ∧ after.taskNodes = []
      ∧ after.terminated = true := by
  cbv

-----------------------------------------------------------------------------------------
-- Settled successful values survive until publication, then lose all memberships
-----------------------------------------------------------------------------------------

/-- Zero pending does not make C empty while its successful value remains unpublished.
Witness: exact stored value, zero counter, and preservation by empty-shell pruning.
-/
theorem success_retained
    : let before := ((queue successWork).handleGraphEvents [first]).1
      let (after, events) := before.handleGraphEvents [sharedSuccess]
      events = []
      ∧ (after.groupNode? child.ref).map GroupNode.pending = some 0
      ∧ (after.taskNode? sharedTask).bind TaskNode.value = some sharedValue
      ∧ (after.pruneEmptyGroups [child]).2 = [child] := by
  cbv

/-- An early value drains after C's pending notice in the parent's response update.
Witness: exact wire data contains the shared field once and completes every announced ID.
-/
theorem success_before_parent
    : updates successWork [[first], [sharedSuccess], [finish]]
      = [
        { hasNext := true, completed := [{ id := "0", errors := 1 }] },
        {
          hasNext := false,
          pending := [{ id := "2", path := [], label := child.label }],
          incremental := [.object "1" parentData, .object "2" sharedData],
          completed := [{ id := "1" }, { id := "2" }]
        }
      ] := by
  cbv

/-- The reverse settlement order still delivers the same field once, in a later update.
Witness: direct response replay separates C's pending notice from its later data.
-/
theorem success_after_parent
    : updates successWork [[first], [finish], [sharedSuccess]]
      = [
        { hasNext := true, completed := [{ id := "0", errors := 1 }] },
        {
          hasNext := true,
          pending := [{ id := "2", path := [], label := child.label }],
          incremental := [.object "1" parentData],
          completed := [{ id := "1" }]
        },
        {
          hasNext := false,
          incremental := [.object "2" sharedData],
          completed := [{ id := "2" }]
        }
      ] := by
  cbv

/-- Removing the other owner after settlement also preserves the latent shared value.
Witness: both source orders reach the identical complete wire output.
-/
theorem success_survives_owner_failure
    : updates successWork [[sharedSuccess], [first], [finish]]
      = updates successWork [[first], [sharedSuccess], [finish]] := by
  cbv

/-- Flushing removes the shared occurrence everywhere and terminates without replay.
Witness: queue replay plus a later empty poll; no stored value or second output remains.
-/
theorem drained_once
    : let final :=
        ((queue successWork).runNormalized [[first], [sharedSuccess], [finish]]).1
      final.taskNodes = []
      ∧ final.groupNodes = []
      ∧ final.terminated = true
      ∧ (final.handleGraphEvents []).2 = [] := by
  cbv

-----------------------------------------------------------------------------------------
-- Local release/pruning checks, independent of the generated source fixtures
-----------------------------------------------------------------------------------------

private def sharedOnly : Execution.Work :=
  .combine
    (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] (.ok (sharedData, 0)) .empty)
    (.executionGroup [⟨parent, []⟩] [] (.ok (parentData, 0)) .empty)

/-- A shared value already published through R leaves no latent work to announce for C.
Witness: a small raw-work fixture exercises successful membership removal and pruning.
-/
theorem already_published_is_pruned
    : ((queue sharedOnly).runNormalized
        [
          [.taskSuccess (.executionGroup [0]) { value := sharedValue }],
          [.taskSuccess (.executionGroup [1]) { value := parentValue }]
        ]).2
      = [
        [
          .groupValues root
            [{
              path := [], data := sharedData, errors := 0, deliveryGroups := [root, child]
            }],
          .groupSuccess root [] []
        ],
        [
          .groupValues parent
            [{ path := [], data := parentData, errors := 0, deliveryGroups := [parent] }],
          .groupSuccess parent [] [],
          .workQueueTermination
        ]
      ] := by
  cbv

private def grandchild : DeliveryNode := { ref := 3, path := [] }

private def cascade : State :=
  {
    rootGroups := [parent.ref],
    groupNodes :=
      [
        { group := ⟨parent, none⟩, childGroups := [child.ref], tasks := [parentTask] },
        {
          group := ⟨child, some parent.ref⟩,
          childGroups := [grandchild.ref],
          tasks := [sharedTask]
        },
        { group := ⟨grandchild, some child.ref⟩, failure := some 2 }
      ],
    taskNodes :=
      [
        { task := ⟨parentTask, [parent]⟩, value := some parentValue },
        { task := ⟨sharedTask, [child]⟩, value := some sharedValue }
      ]
  }

/-- Draining follows a ready release chain, with each notice preceding its completion.
Witness: a local settled-state fixture exhausts three levels without another host input.
-/
theorem recursive_release
    : cascade.drainReadyGroups.2
        = [
          .groupValues parent [parentValue],
          .groupSuccess parent [child] [],
          .groupValues child [sharedValue],
          .groupSuccess child [grandchild] [],
          .groupFailure grandchild 2
        ]
      ∧ cascade.drainReadyGroups.1.groupNodes = [] := by
  cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedOutcomes
