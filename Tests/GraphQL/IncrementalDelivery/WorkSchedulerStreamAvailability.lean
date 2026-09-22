import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskAnnouncementReplay
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Generated stream contributor availability, independent of the migration umbrella.
The fixture is shared with the broader stream-root regressions.
-/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerStreamRoots
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A generated stream with separate successful and failing deferred fields per item
-----------------------------------------------------------------------------------------

/-- The root stream shared by the item-registration regressions. -/
def stream : DeliveryNode := { key := 0, path := [.field "users"] }

/-- The successful deferred group introduced by the item at `index`. -/
def successGroup (index : Nat) : DeliveryNode :=
  {
    key := 2 * index + 1,
    path := [.field "users", .index index],
    label := some (.string "S")
  }

/-- The failing deferred group introduced by the item at `index`. -/
def failureGroup (index : Nat) : DeliveryNode :=
  {
    key := 2 * index + 2,
    path := [.field "users", .index index],
    label := some (.string "F")
  }

/-- The fixed response data of the successful item-local task. -/
def data (index : Nat) : List (Name × ResponseValue) :=
  [("name", .scalar ("name" ++ toString (index + 1)))]

/-- Each item introduces separate successful and failing deferred tasks. -/
def children (index : Nat) : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨successGroup index, []⟩] (successGroup index).path
        (.ok (data index, 0)) (.combine .empty .empty))
      (.combine
        (.executionGroup [⟨failureGroup index, []⟩] (failureGroup index).path (.error 1)
          .empty)
        .empty))

/-- The two finite stream outcomes, with their own deferred regions. -/
def entries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (.object [], 0), children 0), (.ok (.object [], 0), children 1)]

/-- The exact finite work produced by the fixture query. -/
def work : Execution.Work :=
  .combine (.combine (.combine .empty (.stream stream entries)) .empty) .empty

/-- An item settlement carries its value and address-indexed lowered child work. -/
def item (index : Nat) : StreamItem :=
  {
    occurrence := .item [0, 0, 1] index,
    value := { item := .object [] },
    work := Work.fromExecution (children index) ([0, 0, 1] ++ [index])
  }

/-- The first item arrives before its deferred tasks settle. -/
def first : GraphEvent := .streamItems stream [item 0]

/-- The second item arrives after the first item's deferred settlements. -/
def second : GraphEvent := .streamItems stream [item 1]

/-- The first item's successful deferred task address. -/
def successfulTask : Occurrence := .executionGroup [0, 0, 1, 0, 1, 0]

/-- The first item's failing deferred task address. -/
def failedTask : Occurrence := .executionGroup [0, 0, 1, 0, 1, 1, 0]

/-- The failed non-null field contributes one execution error. -/
def failure : GraphEvent := .taskFailure failedTask 1

/-- The successful name task returns its data and empty child work. -/
def success : GraphEvent :=
  .taskSuccess successfulTask
    {
      value :=
        {
          deliveryGroups := [successGroup 0]
          path := (successGroup 0).path
          data := data 0
        }
      work := Work.fromExecution (.combine .empty .empty) [0, 0, 1, 0, 1, 0, 0]
    }

/-- A prefix containing one item, then both of its deferred outcomes. -/
def before : List (List GraphEvent) := [[first], [success, failure]]

/-- The normalized executable state after the shared mixed-outcome prefix. -/
def queue : State :=
  ((State.initialize (Work.fromExecution work)).runNormalized before).1

/-- The example is produced by the actual query executor with pure finite resolvers.
Witness: evaluate a two-item stream containing separate name and required-field defers. -/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [field "users" [defer [field "name"] (some "S"),
      defer [field "required"] (some "F")] [.stream]], ?_⟩
  cbv

/-- The root stream's concrete location identifies both item sources.
Witness: direct structural navigation in the generated work. -/
theorem streamLocated : Located work [0, 0, 1] (.stream stream entries) none [] := by
  cbv

/-- Each item has fixed object data and exactly its own lowered child work.
Witness: its indexed stream entry, including both success and failure task outcomes. -/
theorem itemMatches (index : Nat) (bound : index < 2)
    : ∃ owners producer,
        TaskAt work (item index).occurrence owners producer
          (.item stream (.ok ((item index).value.item, (item index).value.errors)))
        ∧ streamItemWork? work (item index).occurrence = some (item index).work := by
  have entry : entries[index]? = some (.ok (.object [], 0), children index) := by
    have casesIndex : index = 0 ∨ index = 1 := by omega
    rcases casesIndex with rfl | rfl <;> rfl
  refine ⟨[stream.key], none, ?_, ?_⟩
  · exact ⟨stream, entries, [], .ok (.object [], 0), children index,
      streamLocated, entry, rfl, rfl⟩
  · have located : locateWork work [0, 0, 1] = some ⟨.stream stream entries, none, []⟩ :=
      streamLocated
    simp [streamItemWork?, item, located, entry]

/-- The first item's name task succeeds. Witness: its exact execution-group descriptor. -/
theorem successKnown
    : TaskAt work successfulTask [(successGroup 0).key] (some (item 0).occurrence)
        (.object (successGroup 0).path (.ok (data 0, 0))) := by
  refine ⟨[⟨successGroup 0, []⟩], (successGroup 0).path, _, .combine .empty .empty,
    [], ?_, rfl, rfl⟩
  cbv

/-- The first item's required-field task fails. Witness: its fixed non-null outcome. -/
theorem failureKnown
    : TaskAt work failedTask [(failureGroup 0).key] (some (item 0).occurrence)
        (.object (failureGroup 0).path (.error 1)) := by
  refine ⟨[⟨failureGroup 0, []⟩], (failureGroup 0).path, _, .empty, [], ?_, rfl, rfl⟩
  cbv

/-- Stream arrival, successful release, and failure form a valid source prefix.
Witness: matched fixed outcomes, distinct settlements, and prior producing item. -/
theorem before_valid : ValidGraphEvents work before.flatten := by
  have initial : ValidGraphEvents work [first] :=
    .append .nil (by
      intro entry member
      have same := List.mem_singleton.mp member
      subst entry
      exact itemMatches 0 (by decide))
      (by simp [first, item, GraphEvent.Fresh, GraphEvent.identities])
      ⟨[0, 0, 1], entries, none, [], streamLocated, by simp, by simp,
        (by intro source impossible; cases impossible), by cbv⟩
  have released : ValidGraphEvents work [first, success] :=
    .append initial ⟨_, _, successKnown, by cbv, by cbv⟩
      (by simp [first, success, item, successfulTask, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, successKnown, by
        intro source same
        cases same
        simp [first, GraphEvent.successes]⟩
  exact .append released ⟨_, _, _, failureKnown⟩
    (by simp [first, success, failure, item, successfulTask, failedTask,
      GraphEvent.Fresh, GraphEvent.identities])
    ⟨
      _,
      _,
      _,
      failureKnown,
      by
        intro source same
        cases same
        simp [first, success, GraphEvent.successes]
    ⟩

/-- The next item matches its generated payload and child work.
Witness: the second stream entry's exact source descriptor. -/
theorem second_matches : second.MatchesWork work := by
  intro entry member
  have same := List.mem_singleton.mp member
  subst entry
  exact itemMatches 1 (by decide)

/-- The next item is legal after the success/failure prefix, not just individually matched.
Witness: the next contiguous index, fresh identities, and a root-produced stream. -/
theorem continuation_valid : ValidGraphEvents work (before.flatten ++ [second]) := by
  exact .append before_valid second_matches
    (by simp [before, first, success, failure, second, item, successfulTask, failedTask,
      GraphEvent.Fresh, GraphEvent.identities])
    ⟨
      [0, 0, 1],
      entries,
      none,
      [],
      streamLocated,
      by simp,
      by simp [before, first, success, failure, GraphEvent.identities],
      (by intro source impossible; cases impossible),
      by cbv
    ⟩

/-- The queue has actually started every event, and has not terminated before the next item.
Witness: the executable acceptance checker for both prefix and continuation. -/
theorem inputs_started
    : inputsStarted work before = true
      ∧ inputsStarted work (before ++ [[second]]) = true := by
  constructor <;> cbv

/-- A task started by the next stream item has a notice after earlier success and failure.
Witness: a genuine live lookup instantiates general source-prefix announcement ownership;
the initial group list is empty, so its witness comes from an actual item carrier.
-/
theorem next_item_task_announced
    : let initial := State.initialize (Work.fromExecution work)
      let events := before.flatten ++ [second]
      ∃ owners owner,
        TaskHasOwners work (.executionGroup [0, 0, 1, 1, 1, 0]) owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ initial.initialGroups.map DeliveryNode.key
            ++ (initial.rawEventReplay events).2.flatMap rawGroupNoticeKeys := by
  have found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          (before.flatten ++ [second])).taskNode? (.executionGroup [0, 0, 1, 1, 1, 0])
        = some { task := ⟨.executionGroup [0, 0, 1, 1, 1, 0], [successGroup 1]⟩ } := by cbv
  exact createWorkQueue_replayGraphEvents_announcedOwner continuation_valid found

-----------------------------------------------------------------------------------------
-- Region separation closes registration and accounting through arbitrary stream batches
-----------------------------------------------------------------------------------------

/-- The initial frontier consists of the one dependency-free root stream.
Witness: its generated descriptor and empty-history eligibility; no item need exist yet.
-/
theorem initialized
    : Initializes work (State.initialize (Work.fromExecution work)).initialGroups
        (State.initialize (Work.fromExecution work)).initialStreams := by
  change Initializes work [] [stream]
  refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
  intro node member
  have same := List.mem_singleton.mp member
  subst node
  exact ⟨
    [],
    none,
    ⟨[0, 0, 1], entries, streamLocated⟩,
    by simp [announcedKeys, pendingKeys],
    .inl ⟨fun failure => failure.nonempty rfl, .inl rfl⟩,
    by simp,
    .inl rfl
  ⟩

/-- After success and failure in item zero, item one's keys are still unregistered.
Witness: source freshness and disjoint generated regions at the actual replay boundary.
This uses no pending ledger, evaluated group map, or health assumption. -/
theorem next_item_available
    : State.StreamRegistrationsAvailable
        ((State.initialize (Work.fromExecution work)).replayGraphEvents before.flatten)
        work [failedTask] [item 1] := by
  exact createWorkQueue_replay_streamRegistrationsAvailable generated before_valid
    second_matches
    (by
      simp [before, first, success, failure, item, successfulTask, failedTask,
        GraphEvent.Fresh, GraphEvent.identities])

/-- Two items in one event have available registrations in their sequential states.
Witness: the region inventory is enlarged after item zero, before proving item one's
availability. The second item is not checked against the empty queue. -/
theorem same_batch_items_available
    : (State.initialize (Work.fromExecution work)).StreamRegistrationsAvailable work []
        [item 0, item 1] := by
  apply (createWorkQueue_regionInventory work).streamItems_available generated
    (stream := stream)
  · intro entry member
    rcases List.mem_cons.mp member with same | last
    · subst entry
      exact itemMatches 0 (by decide)
    · have same := List.mem_singleton.mp last
      subst entry
      exact itemMatches 1 (by decide)
  · simp [item]
  · simp

/-- Normalized owner accounting survives a mixed outcome prefix and the next stream item.
Witness: unconditional joint owner/ancestry replay on the generated valid started inputs;
all integration availability is derived internally, including the next item's child groups.
-/
theorem continuation_ownerAccounting
    : ∃ parents : Nat → Keys,
        ((State.initialize (Work.fromExecution work)).runNormalized
          (before ++ [[second]])).1.OwnerAccounting
          work parents (before ++ [[second]]).flatten := by
  have valid : ValidGraphEvents work (before ++ [[second]]).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using continuation_valid
  obtain ⟨parents, _, accounting⟩ :=
    generated.runNormalized_ownerAncestry (before ++ [[second]]) valid inputs_started.2
  exact ⟨parents, accounting.accounting⟩

/-- Two items may settle in one event, without settling their child tasks first.
Witness: fixed generated outcomes, fresh item identities, contiguous indices, and an
already-started root stream. -/
theorem together_valid_started
    : ValidGraphEvents work [.streamItems stream [item 0, item 1]]
      ∧ inputsStarted work [[.streamItems stream [item 0, item 1]]] = true := by
  constructor
  · refine .append .nil ?_ ?_ ?_
    · intro entry member
      rcases List.mem_cons.mp member with same | last
      · subst entry
        exact itemMatches 0 (by decide)
      · have same := List.mem_singleton.mp last
        subst entry
        exact itemMatches 1 (by decide)
    · simp [item, GraphEvent.Fresh, GraphEvent.identities]
    · exact ⟨[0, 0, 1], entries, none, [], streamLocated, by simp, by simp,
        (by intro source impossible; cases impossible), by cbv⟩
  · cbv

/-- Multi-item integration preserves all exact counters and healthy contributor owners.
Witness: unconditional joint replay derives availability at each intermediate item state
and preserves ancestry through the event's final recursive drain.
-/
theorem together_ownerAccounting
    : ∃ parents : Nat → Keys,
        ((State.initialize (Work.fromExecution work)).runNormalized
          [[.streamItems stream [item 0, item 1]]]).1.OwnerAccounting
          work parents [.streamItems stream [item 0, item 1]] := by
  obtain ⟨parents, _, accounting⟩ :=
    generated.runNormalized_ownerAncestry
      [[.streamItems stream [item 0, item 1]]]
      together_valid_started.1 together_valid_started.2
  exact ⟨parents, accounting.accounting⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerStreamRoots
