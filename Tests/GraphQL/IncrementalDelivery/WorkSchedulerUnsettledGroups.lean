import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Healthy registration before group success, with streamed work and cancellation. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerUnsettledGroups
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def stream : DeliveryNode := { ref := 0, path := [.field "users"] }

private def child (index : Nat) : DeliveryNode :=
  {
    ref := index + 1, path := [.field "users", .index index], label := some (.string "C")
  }

private def children (index : Nat) : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨child index, []⟩] (child index).path
        (if index = 0 then .error 1 else .ok ([("required", .scalar "ok")], 0))
        (if index = 0 then .empty else .combine .empty .empty))
      .empty)

private def entries : List (Result ResponseValue × Execution.Work) :=
  [(.ok (.object [], 0), children 0), (.ok (.object [], 0), children 1)]

private def work : Execution.Work :=
  .combine (.combine (.combine .empty (.stream stream entries)) .empty) .empty

private def item (index : Nat) : StreamItem :=
  {
    occurrence := .item [0, 0, 1] index
    value := { item := .object [] }
    work := Work.fromExecution (children index) ([0, 0, 1] ++ [index])
  }

private def first : GraphEvent := .streamItems stream [item 0]
private def second : GraphEvent := .streamItems stream [item 1]
private def both : GraphEvent := .streamItems stream [item 0, item 1]
private def failedTask : Occurrence := .executionGroup [0, 0, 1, 0, 1, 0]
private def failure : GraphEvent := .taskFailure failedTask 1
private def finish : GraphEvent := .streamSuccess stream

private def splitInputs : List (List GraphEvent) := [[first], [failure], [second, finish]]
private def joinedInputs : List (List GraphEvent) := [[both], [failure, finish]]

private def mixedResolvers : Resolvers Nat :=
  {
    resolve :=
      fun parent name _ source =>
        match name, source with
        | "required", .object _ 2 => some (.scalar "ok")
        | _, _ => resolvers.resolve parent name [] source
    resolve_argumentsEquivalent := by intros; rfl
  }

/-- The first object's deferred non-null field fails; the second succeeds.
Witness: evaluate the actual executor against pure resolvers with distinct item outcomes.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, mixedResolvers, [], 50, "Query", .object "Query" 0,
    [field "users" [defer [field "required"] (some "C")] [.stream]], ?_⟩
  cbv

/-- The root stream is at the generated field/list work location.
Witness: structural navigation through the executor's combine boundaries. -/
private theorem streamLocated
    : Located work [0, 0, 1] (.stream stream entries) none [] := by
  cbv

/-- Each successful item returns empty object data and its own deferred child work.
Witness: the indexed stream entry, plus exact immediate lowering of that entry's children.
-/
private theorem itemMatches (index : Nat) (bound : index < 2)
    : ∃ owners producer,
        TaskAt work (item index).occurrence owners producer
          (.item stream (.ok ((item index).value.item, (item index).value.errors)))
        ∧ streamItemWork? work (item index).occurrence = some (item index).work := by
  have entry : entries[index]? = some (.ok (.object [], 0), children index) := by
    have casesIndex : index = 0 ∨ index = 1 := by omega
    rcases casesIndex with rfl | rfl <;> rfl
  refine ⟨[stream.ref], none, ?_, ?_⟩
  · exact ⟨stream, entries, [], .ok (.object [], 0), children index,
      streamLocated, entry, rfl, rfl⟩
  · have located : locateWork work [0, 0, 1] = some ⟨.stream stream entries, none, []⟩ :=
      streamLocated
    simp [streamItemWork?, item, located, entry]

/-- The first child's failed task has the first stream item as producer.
Witness: its exact located execution group, not a manually supplied failure count. -/
private theorem failedKnown
    : TaskAt work failedTask [(child 0).ref] (some (item 0).occurrence)
        (.object (child 0).path (.error 1)) := by
  refine ⟨[⟨child 0, []⟩], (child 0).path, .error 1, .empty, [], ?_, rfl, rfl⟩
  cbv

/-- The split-item history stays valid when a child fails before the next item arrives.
Witness: exact outcomes, fresh identities, producer-before-child, and contiguous items. -/
theorem split_valid : ValidGraphEvents work splitInputs.flatten := by
  have firstValid : ValidGraphEvents work [first] :=
    .append .nil (by
      intro entry member
      have same : entry = item 0 := List.mem_singleton.mp member
      subst entry
      exact itemMatches 0 (by decide))
      (by simp [first, item, GraphEvent.Fresh, GraphEvent.identities])
      ⟨[0, 0, 1], entries, none, [], streamLocated, by simp, by simp,
        (by intro source impossible; cases impossible), by cbv⟩
  have failureValid : ValidGraphEvents work [first, failure] :=
    .append firstValid ⟨_, _, _, failedKnown⟩
      (by simp [first, failure, item, failedTask, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, failedKnown, by
        intro source equal
        cases equal
        simp [first, GraphEvent.successes]⟩
  have secondValid : ValidGraphEvents work [first, failure, second] :=
    .append failureValid (by
      intro entry member
      have same : entry = item 1 := List.mem_singleton.mp member
      subst entry
      exact itemMatches 1 (by decide))
      (by simp [first, second, failure, item, failedTask, GraphEvent.Fresh,
        GraphEvent.identities])
      ⟨[0, 0, 1], entries, none, [], streamLocated, by simp,
        by simp [first, failure, GraphEvent.identities],
        (by intro source impossible; cases impossible), by cbv⟩
  exact .append secondValid ⟨[], none, .stream streamLocated⟩
    (by simp [first, second, failure, finish, GraphEvent.Fresh, GraphEvent.identities])
    ⟨
      [0, 0, 1],
      entries,
      none,
      [],
      streamLocated,
      (by intro source impossible; cases impossible),
      by cbv
    ⟩

/-- Joining both item settlements is also allowed by the original source semantics.
Witness: the same fixed entries and one two-item contiguous settlement batch. -/
theorem joined_valid : ValidGraphEvents work joinedInputs.flatten := by
  have itemsValid : ValidGraphEvents work [both] :=
    .append .nil (by
      intro entry member
      rcases List.mem_cons.mp member with same | later
      · subst entry
        exact itemMatches 0 (by decide)
      · have same := List.mem_singleton.mp later
        subst entry
        exact itemMatches 1 (by decide))
      (by simp [both, item, GraphEvent.Fresh, GraphEvent.identities])
      ⟨[0, 0, 1], entries, none, [], streamLocated, by simp, by simp,
        (by intro source impossible; cases impossible), by cbv⟩
  have failureValid : ValidGraphEvents work [both, failure] :=
    .append itemsValid ⟨_, _, _, failedKnown⟩
      (by simp [both, failure, item, failedTask, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, failedKnown, by
        intro source equal
        cases equal
        simp [both, GraphEvent.successes]⟩
  exact .append failureValid ⟨[], none, .stream streamLocated⟩
    (by simp [both, failure, finish, GraphEvent.Fresh, GraphEvent.identities])
    ⟨
      [0, 0, 1],
      entries,
      none,
      [],
      streamLocated,
      (by intro source impossible; cases impossible),
      by cbv
    ⟩

/-- Both batching choices obey actual queue start/stop checks.
Witness: evaluate the executable source-acceptance checker, without native axioms. -/
theorem inputs_started
    : inputsStarted work splitInputs = true ∧ inputsStarted work joinedInputs = true := by
  constructor <;> cbv

/-- Both stream arrival shapes retain exact healthy accounting and retired ancestry.
Witness: the current joint replay theorem, without a task-bearing-registration assumption.
-/
theorem split_accounting
    : ∃ parents,
        ((State.initialize (Work.fromExecution work)).runNormalized
          splitInputs).1.OwnerAncestry
          work parents splitInputs.flatten := by
  obtain ⟨parents, _, ledger⟩ :=
    generated.runNormalized_ownerAncestry splitInputs split_valid inputs_started.1
  exact ⟨parents, ledger⟩

/-- Multi-item settlement has the same accounting guarantee as separate arrivals.
Witness: the same replay theorem includes the intermediate item-integration states.
-/
theorem joined_accounting
    : ∃ parents,
        ((State.initialize (Work.fromExecution work)).runNormalized
          joinedInputs).1.OwnerAncestry
          work parents joinedInputs.flatten := by
  obtain ⟨parents, _, ledger⟩ :=
    generated.runNormalized_ownerAncestry joinedInputs joined_valid inputs_started.2
  exact ⟨parents, ledger⟩

/-- Both arrival shapes leave precisely the second child's task outstanding.
Witness: reduction of the queue states, not equality of differently batched wire events.
-/
theorem surviving_state
    : ((State.initialize (Work.fromExecution work)).runNormalized splitInputs).1
        = ((State.initialize (Work.fromExecution work)).runNormalized joinedInputs).1
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          splitInputs).1.rootGroups
        = [(child 1).ref]
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          splitInputs).1.groupNode?
          (child 0).ref
        = none := by
  constructor
  · cbv
  · constructor <;> cbv

/-- A failed child's permanent registration survives the later item.
Witness: direct registry membership; failure does not permit duplicate registration.
-/
theorem failed_owner_is_registered
    : (child 0).ref
      ∈ ((State.initialize (Work.fromExecution work)).runNormalized
          splitInputs).1.registeredGroups := by
  cbv
  exact List.mem_cons_self

private def successfulTask : Occurrence := .executionGroup [0, 0, 1, 1, 1, 0]

private def successResult : TaskResult :=
  {
    value :=
      {
        deliveryGroups := [child 1]
        path := (child 1).path
        data := [("required", .scalar "ok")]
      }
    work := Work.fromExecution (.combine .empty .empty) [0, 0, 1, 1, 1, 0, 0]
  }

/-- The second child's success is fixed by generated work, not chosen by the scheduler.
Witness: its exact task location and producing stream-item occurrence. -/
private theorem successKnown
    : TaskAt work successfulTask [(child 1).ref] (some (item 1).occurrence)
        (.object (child 1).path (.ok ([("required", .scalar "ok")], 0))) := by
  refine ⟨[⟨child 1, []⟩], (child 1).path, _, .combine .empty .empty, [], ?_, rfl, rfl⟩
  cbv

/-- Successful settlement is a legal continuation of the split stream/failure prefix.
Witness: fixed data/child work, fresh occurrence identity, and prior item publication. -/
theorem success_continuation_valid
    : ValidGraphEvents work
        (splitInputs.flatten ++ [.taskSuccess successfulTask successResult]) := by
  exact .append split_valid ⟨_, _, successKnown, by cbv, by cbv⟩
    (by
      simp [splitInputs, first, second, failure, finish, GraphEvent.Fresh,
        GraphEvent.identities, item, failedTask, successfulTask])
    ⟨
      _,
      _,
      _,
      successKnown,
      by
        intro source same
        cases same
        simp [splitInputs, first, second, failure, finish, GraphEvent.successes]
    ⟩

/-- The complete continuation respects the queue's actual start/termination discipline.
Witness: evaluate the public checker, including the final successful task batch. -/
theorem success_continuation_started
    : inputsStarted work (splitInputs ++ [[.taskSuccess successfulTask successResult]])
      = true := by
  cbv

/-- The first successful child settlement preserves the joint replay invariant.
Witness: the unrestricted owner/ancestry theorem on the checked complete continuation.
-/
theorem first_streamed_success_accounting
    : let batches := splitInputs ++ [[.taskSuccess successfulTask successResult]]
      ∃ parents,
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.OwnerAncestry
          work parents batches.flatten := by
  obtain ⟨parents, _, ledger⟩ := generated.runNormalized_ownerAncestry
    (splitInputs ++ [[.taskSuccess successfulTask successResult]])
    (by simpa using success_continuation_valid) success_continuation_started
  exact ⟨parents, ledger⟩

/-- Mixed replay retains one fresh release inventory through task failure and termination.
Witness: the general normalized theorem uses the legal item/failure/success history; an
extra empty call after termination changes neither publications nor release support.
-/
theorem normalized_release_inventory_after_failure
    : let batches := splitInputs ++ [[.taskSuccess successfulTask successResult], []]
      let replay := (State.initialize (Work.fromExecution work)).runNormalized batches
      replay.1.terminated = true
      ∧ ∃ published : List ObjectPublication,
          published.map (fun publication => publication.2)
            = replay.2.flatten.flatMap normalizedObjectValues
          ∧ (published.map Prod.fst).Nodup
          ∧ NormalizedStreamReleasePublications work published replay.2.flatten := by
  have valid : ValidGraphEvents work
      (splitInputs ++ [[GraphEvent.taskSuccess successfulTask successResult], []]).flatten := by
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      using success_continuation_valid
  obtain ⟨published, values, ledger, supported⟩ :=
    createWorkQueue_runNormalized_streamReleasePublications generated valid
  exact ⟨by cbv, published, values, ledger.unique, supported⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerUnsettledGroups
