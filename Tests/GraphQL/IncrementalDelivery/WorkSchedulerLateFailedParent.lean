import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Minimality
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A shared success can register a child after its failed parent has been removed. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerLateFailedParent
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated shared work and the concrete late-registration replay
-----------------------------------------------------------------------------------------

private def p : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def q : DeliveryNode := ⟨1, [], some (.string "Q")⟩
private def r : DeliveryNode := ⟨2, [], some (.string "R")⟩
private def s : DeliveryNode := ⟨3, [], some (.string "S")⟩
private def c : DeliveryNode := ⟨4, [.field "user"], some (.string "C")⟩
private def d : DeliveryNode := ⟨5, [.field "user"], some (.string "D")⟩
private def pTask : Occurrence := .executionGroup [1, 0]
private def uTask : Occurrence := .executionGroup [1, 1, 0]
private def xTask : Occurrence := .executionGroup [1, 1, 0, 0, 0, 1, 0]
private def yTask : Occurrence := .executionGroup [1, 1, 0, 0, 0, 1, 1, 0]
private def qTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def rTask : Occurrence := .executionGroup [1, 1, 1, 1, 0]
private def userData : List (Name × ResponseValue) := [("user", .object [])]
private def keepData : List (Name × ResponseValue) := [("keepQ", .scalar "a")]

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [⟨c, [p]⟩, ⟨d, [q]⟩, ⟨r, []⟩] [.field "user"] (.error 1) .empty)
        (.combine
          (.executionGroup [⟨d, [q]⟩, ⟨s, []⟩] [.field "user"] (.error 1) .empty)
          .empty)))
    .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨p, []⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨p, []⟩, ⟨q, []⟩, ⟨r, []⟩, ⟨s, []⟩] []
          (.ok (userData, 0)) children)
        (.combine
          (.executionGroup [⟨q, []⟩] [] (.ok (keepData, 0)) (.combine .empty .empty))
          (.combine (.executionGroup [⟨r, []⟩] [] (.error 2) .empty) .empty))))

private def killP : GraphEvent := .taskFailure pTask 1
private def killY : GraphEvent := .taskFailure yTask 1
private def killR : GraphEvent := .taskFailure rTask 2
private def killX : GraphEvent := .taskFailure xTask 1

private def expand : GraphEvent :=
  .taskSuccess uTask
    {
      value :=
        { path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s] }
      work := Work.fromExecution children [1, 1, 0, 0]
    }

private def finish : GraphEvent :=
  .taskSuccess qTask
    {
      value := { path := [], data := keepData, errors := 0, deliveryGroups := [q] }
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def inputs : List (List GraphEvent) :=
  [[killP], [expand], [killY], [killR], [killX], [finish]]

private def rejectedOutputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure p 1],
    [.groupFailure s 1],
    [.groupFailure r 2],
    [
      .groupValues q
        [{ path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s] }],
      .groupValues q
        [{ path := [], data := keepData, errors := 0, deliveryGroups := [q] }],
      .groupSuccess q [d] [],
      .groupFailure d 2,
      .workQueueTermination
    ]
  ]

private def correctedOutputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure p 1],
    [.groupFailure s 1],
    [.groupFailure r 2],
    [
      .groupValues q
        [{ path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s] }],
      .groupValues q
        [{ path := [], data := keepData, errors := 0, deliveryGroups := [q] }],
      .groupSuccess q [d] [],
      .groupFailure d 1,
      .workQueueTermination
    ]
  ]

/-- Pure query execution generates every task and ancestor in this fixture.
Witness: shared user selections create C/D/R and D/S tasks; R also owns a two-error task.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "pBad"),
      field "user" [defer [field "required" [] [] (some "x")] (some "C")]] (some "P"),
     defer [field "a" [] [] (some "keepQ"),
      field "user" [defer [field "required" [] [] (some "x"),
        field "required" [] [] (some "y")] (some "D")]] (some "Q"),
     defer [field "required" [] [] (some "rBad"), field "required" [] [] (some "rBad2"),
      field "user" [field "required" [] [] (some "x")]] (some "R"),
     defer [field "user" [field "required" [] [] (some "y")]] (some "S")], ?_⟩
  cbv

/-- P's private failure descriptor. Witness: the root task's structural address. -/
private theorem p_known : TaskAt work pTask [p.key] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

/-- P's first failure establishes causal support for every key it cancels.
Witness: the general handler theorem with generated parent metadata and actual task
registration; no admitted output or presumed final cancellation state is used. -/
theorem first_failure_cancellation_supported
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).handleGraphEvent killP).1 work
        [pTask] := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  apply State.CancelledRecordsSupported.handleGraphEvent
    (createWorkQueue_cancelledRecordsSupported _ _ _)
    (createWorkQueue_cachedFailuresSupported _ _ _)
    (createWorkQueue_startedTasksRegistered _)
    (createWorkQueue_fromSpec_registeredTasksMatch _)
    (createWorkQueue_groupNodesMatchWork _)
    (createWorkQueue_childLinksCanonical _ parents
      (fun _ member =>
        workFromSpec_groups_parentCanonical
          (Located.root (root := work)) canonical member))
    canonical killP ⟨_, _, _, p_known⟩
  intro occurrence errors same _ _ _
  have equal : occurrence = pTask := by cases same; rfl
  simp [equal]

/-- The shared producer descriptor. Witness: its four root owners and fixed user value. -/
private theorem u_known
    : TaskAt work uTask [p.key, q.key, r.key, s.key] none
        (.object [] (.ok (userData, 0))) :=
  ⟨_, [], .ok (userData, 0), children, [], rfl, rfl, rfl⟩

/-- X's descriptor. Witness: the first nested failure under the shared producer. -/
private theorem x_known
    : TaskAt work xTask [c.key, d.key, r.key] (some uTask)
        (.object [.field "user"] (.error 1)) :=
  ⟨_, _, .error 1, .empty, _, rfl, rfl, rfl⟩

/-- Y's descriptor. Witness: the second nested failure under the shared producer. -/
private theorem y_known
    : TaskAt work yTask [d.key, s.key] (some uTask)
        (.object [.field "user"] (.error 1)) :=
  ⟨_, _, .error 1, .empty, _, rfl, rfl, rfl⟩

/-- Q's remaining success descriptor. Witness: its root address and fixed scalar value. -/
private theorem q_known
    : TaskAt work qTask [q.key] none (.object [] (.ok (keepData, 0))) :=
  ⟨_, [], .ok (keepData, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩

/-- R's private two-error descriptor. Witness: the last root task's structural address. -/
private theorem r_known : TaskAt work rTask [r.key] none (.object [] (.error 2)) :=
  ⟨_, [], .error 2, .empty, [], rfl, rfl, rfl⟩

/-- Every settlement matches its fixed outcome, is fresh, and follows its producer.
Witness: six source-extension steps; the nested failures follow the shared user success.
-/
theorem source_valid : ValidGraphEvents work inputs.flatten := by
  have zero : ValidGraphEvents work [killP] :=
    .append .nil ⟨_, _, _, p_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP])
      ⟨_, _, _, p_known, by intro source impossible; cases impossible⟩
  have one : ValidGraphEvents work [killP, expand] :=
    .append zero ⟨_, _, u_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, pTask, uTask])
      ⟨_, _, _, u_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [killP, expand, killY] :=
    .append one ⟨_, _, _, y_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY,
        pTask, uTask, yTask])
      ⟨_, _, _, y_known, by simp [GraphEvent.successes, killP, expand]⟩
  have three : ValidGraphEvents work [killP, expand, killY, killR] :=
    .append two ⟨_, _, _, r_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY, killR,
        pTask, uTask, yTask, rTask])
      ⟨_, _, _, r_known, by intro source impossible; cases impossible⟩
  have four : ValidGraphEvents work [killP, expand, killY, killR, killX] :=
    .append three ⟨_, _, _, x_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY, killR, killX,
        pTask, uTask, yTask, rTask, xTask])
      ⟨_, _, _, x_known, by simp [GraphEvent.successes, killP, expand, killY, killR]⟩
  exact .append four ⟨_, _, q_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY, killR, killX,
      finish, pTask, uTask, yTask, rTask, xTask, qTask])
    ⟨_, _, _, q_known, by intro source impossible; cases impossible⟩

/-- The actual start checker accepts all six settlements, including the late failure.
Witness: executable initialization and replay; X was started through R before R failed.
-/
theorem inputs_started : inputsStarted work inputs = true := by cbv

/-- The actual guard excludes X's ignored failure from the final cause inventory.
Witness: evaluate the existing accepted-failure projection through all six source events.
-/
theorem accepted_failure_inventory
    : (State.initialize (Work.fromExecution work)).objectFailureContributions
        inputs.flatten
      = [rTask, yTask, pTask] := by cbv

/-- Every cancellation in the complete split-batch replay has an accepted failure cause.
Witness: the general generated-replay theorem and the actual guard-selected inventory,
which omits X while covering late registration and the final retained-failure drain. -/
theorem replay_cancellation_supported
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.CancelledRecordsSupported
        work [rTask, yTask, pTask] := by
  have supported := generated.runNormalized_cancelledRecordsSupported inputs source_valid
    inputs_started
  simpa only [accepted_failure_inventory] using supported

/-- Joined input batching derives the same cancellation causes without counting X.
Witness: start discipline for the joined batch and general normalized replay support. -/
theorem joined_cancellation_supported
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).runNormalized [inputs.flatten]).1
        work [rTask, yTask, pTask] := by
  have valid : ValidGraphEvents work [inputs.flatten].flatten := by
    simpa using source_valid
  have supported := generated.runNormalized_cancelledRecordsSupported [inputs.flatten]
    valid (by cbv)
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
    accepted_failure_inventory]
    using supported

/-- The queue emits P1, S1, R2, then announces D and reports only Y's one error.
Witness: executable queue and publisher replay, including the final termination marker.
-/
theorem output
    : let queue := State.initialize (Work.fromExecution work)
      queue.initialGroups = [p, q, r, s]
      ∧ queue.initialStreams = []
      ∧ (queue.runNormalized inputs).2 = correctedOutputs := by cbv

/-- P's retirement blocks late registration of C and prevents its use as a healthy owner.
Witness: replay up to X's settlement retains cancellation keys for both P and C.
-/
theorem late_child_stays_cancelled
    : let before :=
        ((State.initialize (Work.fromExecution work)).runNormalized (inputs.take 4)).1
      before.groupNode? p.key = none
      ∧ before.groupNode? c.key = none
      ∧ before.cancelledGroups.contains p.key = true
      ∧ before.cancelledGroups.contains c.key = true
      ∧ before.groupIsHealthy c.key = false := by cbv

/-- The same correction holds when the host supplies all settlements in one batch.
Witness: executable replay preserves the corrected atomic outputs under joined input.
-/
theorem joined_output
    : ((State.initialize (Work.fromExecution work)).runNormalized [inputs.flatten]).2
      = [correctedOutputs.flatten] := by cbv

/-- C's cancellation does not discard X while another contributing owner is healthy.
Witness: after the shared success, D and R still admit X's settlement and R closes.
-/
theorem healthy_coowner_preserved
    : let before :=
        ((State.initialize (Work.fromExecution work)).runNormalized (inputs.take 2)).1
      before.taskHasHealthyOwner ⟨xTask, [c, d, r]⟩ = true
      ∧ (before.taskFailure xTask 1).2 = [.groupFailure r 1] := by cbv

private def grandchild : DeliveryNode := ⟨6, [.field "user"], none⟩

/-- A refused child carries cancellation onward to later grandchildren.
Witness: two successive registrations after P's failed retirement install no live nodes.
-/
theorem transitive_late_registration
    : let retired : State := { registeredGroups := [p.key], cancelledGroups := [p.key] }
      let next := (retired.addGroup ⟨c, some p.key⟩).addGroup ⟨grandchild, some c.key⟩
      next.groupNodes = []
      ∧ next.cancelledGroups.contains grandchild.key = true
      ∧ next.registeredGroups.contains grandchild.key = true := by cbv

/-- Refusal permanently retires C, regardless of any later host events or batching.
Witness: the general refused-child retirement theorem, not finite trace enumeration. -/
theorem late_child_never_recreated (later : List (List GraphEvent))
    : let retired : State := { registeredGroups := [p.key], cancelledGroups := [p.key] }
      (((retired.addGroup ⟨c, some p.key⟩).runNormalized later).1.groupNode? c.key)
      = none := by
  apply State.addGroup_cancelled_child_never_recreated
  · simp [p, c]
  · rfl
  · rfl
  · simp

/-- Candidate order cannot hide the subsequently discovered cancellation of a parent.
Witness: register a grandchild first, then retire C; the missing-parent walk rejects it.
-/
theorem child_first_registration
    : let retired : State := { registeredGroups := [p.key], cancelledGroups := [p.key] }
      let next := (retired.addGroups [⟨grandchild, some c.key⟩, ⟨c, some p.key⟩]).1
      next.groupNode? c.key = none ∧ next.groupIsHealthy grandchild.key = false := by cbv

/-- Initialization of the generated fixture does not invent a cancelled group.
Witness: the general initialization equation, independent of outcomes and source order. -/
theorem initialization_has_no_cancellations
    : (State.initialize (Work.fromExecution work)).cancelledGroups = [] :=
  createWorkQueue_cancelledGroups_empty _

/-- Closing P successfully neither adds P nor forgets any earlier cancellation keys.
Witness: the general successful-closure equation for an arbitrary retained history. -/
theorem successful_retirement_keeps_cancellations (prior : Keys)
    : let parent : GroupNode := { group := ⟨p, none⟩ }
      let queue : State :=
        {
          registeredGroups := [p.key],
          cancelledGroups := prior,
          rootGroups := [p.key],
          groupNodes := [parent]
        }
      (queue.finishGroupSuccess parent).1.cancelledGroups = prior := by
  exact State.finishGroupSuccess_cancelledGroups _ _

/-- Successful removal remains distinct from cancellation for future health walks.
Witness: successful group closure and empty-group pruning leave no cancellation key.
-/
theorem successful_retirement_preserved
    : let parent : GroupNode := { group := ⟨p, none⟩ }
      let initial : State :=
        { registeredGroups := [p.key], rootGroups := [p.key], groupNodes := [parent] }
      let closed := (initial.finishGroupSuccess parent).1
      let pruned := (initial.pruneEmptyGroups [p]).1
      (closed.addGroup ⟨c, some p.key⟩).groupIsHealthy c.key = true
      ∧ (pruned.addGroup ⟨c, some p.key⟩).groupIsHealthy c.key = true := by cbv

/-- Failure retirement remembers both existing descendants and the removed ancestor.
Witness: traverse P/C and reject a subsequently arriving grandchild of C.
-/
theorem existing_descendants_retired
    : let initial := (({} : State).addGroups [⟨p, none⟩, ⟨c, some p.key⟩]).1
      let retired := initial.removeGroup p.key
      retired.cancelledGroups.contains p.key = true
      ∧ retired.cancelledGroups.contains c.key = true
      ∧ (retired.addGroup ⟨grandchild, some c.key⟩).groupNode? grandchild.key = none := by
  cbv

-----------------------------------------------------------------------------------------
-- Exact completion counts determine the required failure ordering
-----------------------------------------------------------------------------------------

/-- These six occurrences exhaust the tasks. Witness: the finite observation inventory. -/
private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = pTask
      ∨ occurrence = uTask
      ∨ occurrence = xTask
      ∨ occurrence = yTask
      ∨ occurrence = qTask
      ∨ occurrence = rTask := by
  have member := known.observationToken
  simpa [observationTokens, work, children, pTask, uTask, xTask, yTask, qTask, rTask]
    using member

open Classical in
/-- A unique list counts a chosen occurrence at most once. Witness: list induction. -/
private theorem sum_indicator (failed : List Occurrence) (unique : failed.Nodup)
    (target : Occurrence) (amount : Nat)
    : (failed.map (fun occurrence => if occurrence = target then amount else 0)).sum
      = if target ∈ failed then amount else 0 := by
  induction failed with
  | nil => simp
  | cons occurrence rest ih =>
      have fresh := List.nodup_cons.mp unique
      by_cases same : occurrence = target
      · subst occurrence
        simp [ih fresh.2, fresh.1]
      · simp [same, Ne.symm same, ih fresh.2]

/-- Summing contributions distributes over addition. Witness: list induction. -/
private theorem sum_add (failed : List Occurrence) (left right : Occurrence → Nat)
    : (failed.map (fun occurrence => left occurrence + right occurrence)).sum
      = (failed.map left).sum + (failed.map right).sum := by
  induction failed with
  | nil => simp
  | cons occurrence rest ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

open Classical in
/-- Only the four failing tasks contribute errors, once each in a unique inventory.
Witness: fixed task descriptors determine each summand; finite indicator sums count it.
-/
private theorem counts {failed key errors} (unique : failed.Nodup)
    (counted : NodeErrors work failed key errors)
    : errors
      = (if pTask ∈ failed then if key ∈ [p.key] then 1 else 0 else 0)
        + (if xTask ∈ failed then if key ∈ [c.key, d.key, r.key] then 1 else 0 else 0)
        + (if yTask ∈ failed then if key ∈ [d.key, s.key] then 1 else 0 else 0)
        + (if rTask ∈ failed then if key ∈ [r.key] then 2 else 0 else 0) := by
  obtain ⟨contribution, values, total⟩ := counted
  have exactValue : ∀ occurrence ∈ failed,
      contribution occurrence =
        (if occurrence = pTask then if key ∈ [p.key] then 1 else 0 else 0)
        + (if occurrence = xTask then if key ∈ [c.key, d.key, r.key] then 1 else 0 else 0)
        + (if occurrence = yTask then if key ∈ [d.key, s.key] then 1 else 0 else 0)
        + (if occurrence = rTask then if key ∈ [r.key] then 2 else 0 else 0) := by
    intro occurrence member
    obtain ⟨owners, producer, payload, known, assigned⟩ := values occurrence member
    rcases task_cases known with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨rfl, _, rfl⟩ := known.unique p_known
      simpa [pTask, xTask, yTask, rTask, Payload.failure] using assigned
    · obtain ⟨rfl, _, rfl⟩ := known.unique u_known
      simpa [pTask, uTask, xTask, yTask, rTask, Payload.failure] using assigned
    · obtain ⟨rfl, _, rfl⟩ := known.unique x_known
      simpa [pTask, xTask, yTask, rTask, Payload.failure] using assigned
    · obtain ⟨rfl, _, rfl⟩ := known.unique y_known
      simpa [pTask, xTask, yTask, rTask, Payload.failure] using assigned
    · obtain ⟨rfl, _, rfl⟩ := known.unique q_known
      simpa [pTask, qTask, xTask, yTask, rTask, Payload.failure] using assigned
    · obtain ⟨rfl, _, rfl⟩ := known.unique r_known
      simpa [pTask, xTask, yTask, rTask, Payload.failure] using assigned
  rw [total, List.map_congr_left exactValue]
  simp only [sum_add, sum_indicator failed unique]

/-- P's report forces its own failure; S's report forces Y; R2 excludes X; D2 needs X.
Witness: specialize the exact finite count formula at the four reporting group keys.
-/
private theorem count_constraints {failed} (unique : failed.Nodup)
    : (NodeErrors work failed p.key 1 → pTask ∈ failed)
      ∧ (NodeErrors work failed s.key 1 → yTask ∈ failed)
      ∧ (NodeErrors work failed r.key 2 → rTask ∈ failed ∧ xTask ∉ failed)
      ∧ (NodeErrors work failed d.key 2 → xTask ∈ failed) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro counted
    have total := counts unique counted
    apply Classical.byContradiction
    intro absent
    simp [p, r, c, d, s, absent] at total
  · intro counted
    have total := counts unique counted
    apply Classical.byContradiction
    intro absent
    simp [p, r, c, d, s, absent] at total
  · intro counted
    have total := counts unique counted
    by_cases recorded : rTask ∈ failed
    · refine ⟨recorded, ?_⟩
      intro included
      simp [p, r, c, d, s, recorded, included] at total
    · by_cases included : xTask ∈ failed
        <;> simp [p, r, c, d, s, recorded, included] at total
  · intro counted
    have total := counts unique counted
    apply Classical.byContradiction
    intro absent
    by_cases included : yTask ∈ failed
      <;> simp [p, r, d, s, absent, included] at total

/-- Visible failures have bounded cuts. Witness: invert filtering and mapping. -/
private theorem cut_of_member {failures bound occurrence}
    (member : occurrence ∈ failedBefore failures bound)
    : ∃ cut, (cut, occurrence) ∈ failures ∧ cut ≤ bound := by
  obtain ⟨⟨cut, other⟩, kept, same⟩ := List.mem_map.mp member
  obtain ⟨included, bounded⟩ := List.mem_filter.mp kept
  dsimp only at same
  subst other
  exact ⟨cut, included, of_decide_eq_true bounded⟩

/-- A strictly earlier failure cut must occur before a selected entry in ordered evidence.
Witness: any later-list occurrence would reverse the witness's nondecreasing cut order.
-/
private theorem prior_entry {initial matching events failures before after cut occurrence}
    (witness : FailureWitness work initial matching events failures)
    (split : failures = before ++ (cut, occurrence) :: after)
    {earlier previous} (member : (earlier, previous) ∈ failures) (less : earlier < cut)
    : (earlier, previous) ∈ before := by
  rw [split] at member
  rcases List.mem_append.mp member with prior | later
  · exact prior
  · rcases List.mem_cons.mp later with same | later
    · have equal := (Prod.mk.inj same).1
      omega
    · obtain ⟨middle, rest, afterEq⟩ := List.mem_iff_append.mp later
      have earlierSplit : failures = (before ++ (cut, occurrence) :: middle)
          ++ (earlier, previous) :: rest := by
        simp only [split, afterEq, List.append_assoc, List.cons_append]
      have bound := (witness _ earlier previous rest earlierSplit).2.1
        (cut, occurrence) (by simp)
      dsimp only at bound
      omega

/-- C inherits P's failure despite its separate producer. Witness: X's descriptor. -/
private theorem c_known : NodeAt work c .group [p.key] (some uTask) :=
  ⟨[1, 1, 0, 0, 0, 1, 0], _, _, .error 1, .empty, _, ⟨c, [p]⟩, rfl, by simp, rfl, rfl⟩

/-- Late registration propagates P's actual failure to C's retained cancellation key.
Witness: structural parent metadata instantiates the general provenance-preservation proof.
-/
theorem late_child_cancellation_supported
    : let retired : State := { registeredGroups := [p.key], cancelledGroups := [p.key] }
      (retired.addGroups [⟨c, some p.key⟩]).1.CancelledGroupsSupported work [pTask] := by
  apply State.CancelledGroupsSupported.addGroups
  · intro key member
    have same : key = p.key := List.mem_singleton.mp member
    subst key
    exact .task ⟨none, .object [] (.error 1), p_known⟩ (by simp) (by simp)
  · intro group member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[p.key], some uTask, c_known, rfl⟩

/-- The P, Y, and R failures cancel X, including C's inherited failure through P.
Witness: at their latest cut all three X owners have failed and X remains unpublished.
-/
private theorem x_cancelled {matching events before pCut yCut rCut}
    (pRecorded : (pCut, pTask) ∈ before) (yRecorded : (yCut, yTask) ∈ before)
    (rRecorded : (rCut, rTask) ∈ before)
    (pBound : pCut ≤ events.length) (yBound : yCut ≤ events.length)
    (rBound : rCut ≤ events.length) (unpublished : ¬Published matching events xTask)
    : TaskCancelled work matching events before xTask := by
  let cut := max pCut (max yCut rCut)
  have recorded : cut ∈ before.map Prod.fst := by
    have hp : pCut ∈ before.map Prod.fst := List.mem_map.mpr ⟨_, pRecorded, rfl⟩
    have hy : yCut ∈ before.map Prod.fst := List.mem_map.mpr ⟨_, yRecorded, rfl⟩
    have hr : rCut ∈ before.map Prod.fst := List.mem_map.mpr ⟨_, rRecorded, rfl⟩
    by_cases py : pCut ≤ yCut
    · by_cases yr : yCut ≤ rCut
      · simpa [cut, Nat.max_eq_right yr, Nat.max_eq_right (Nat.le_trans py yr)] using hr
      · simpa [cut, Nat.max_eq_left (by omega : rCut ≤ yCut), Nat.max_eq_right py] using hy
    · by_cases pr : pCut ≤ rCut
      · simpa [cut, Nat.max_eq_right (by omega : yCut ≤ rCut), Nat.max_eq_right pr] using hr
      · have equal : cut = pCut := by dsimp [cut]; omega
        simpa [equal] using hp
  refine ⟨
    cut,
    recorded,
    by dsimp [cut]; omega,
    Causality.TaskCancelled.owners ⟨_, _, x_known⟩ ?_ (by simp) ?_
  ⟩
  · intro published
    apply unpublished
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · intro key member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .groupDependency (dependency := p.key) ⟨c, some uTask, c_known, rfl⟩ (by simp)
        (.task ⟨_, _, p_known⟩ (by simp) (mem_failedBefore pRecorded (by dsimp [cut]; omega)))
    · exact .task ⟨_, _, y_known⟩ (by simp)
        (mem_failedBefore yRecorded (by dsimp [cut]; omega))
    · exact .task ⟨_, _, r_known⟩ (by simp)
        (mem_failedBefore rRecorded (by dsimp [cut]; omega))

/-- No explanation can report P1, S1, R2 in order and later report D2 for this work.
Witness: exact counts require X strictly after the three cuts cancelling all its owners,
contradicting failure licensing. This excludes every matching and failure-cut choice.
-/
theorem closure_counts_unexplained {events : List Execution.WorkQueueEvent}
    {matching failures} {i j k l : Nat} (atP : events[i]? = some (.groupFailure p 1))
    (atS : events[j]? = some (.groupFailure s 1))
    (atR : events[k]? = some (.groupFailure r 2))
    (atD : events[l]? = some (.groupFailure d 2)) (pBefore : i ≤ k) (sBefore : j ≤ k)
    : ¬Explains work [p, q, r, s] [] events matching failures := by
  intro explained
  have pAllowed := explained.2.2 i _ atP
  have sAllowed := explained.2.2 j _ atS
  have rAllowed := explained.2.2 k _ atR
  have dAllowed := explained.2.2 l _ atD
  simp only [EventAllowed, failedBefore_filter _ (Nat.le_refl _)]
    at pAllowed sAllowed rAllowed dAllowed
  have unique (bound : Nat) : (failedBefore failures bound).Nodup :=
    explained.failures_nodup.sublist (List.filter_sublist.map Prod.snd)
  have pRequired := (count_constraints (unique _)).1 pAllowed.2.2.2
  have yRequired := (count_constraints (unique _)).2.1 sAllowed.2.2.2
  obtain ⟨rRequired, xExcluded⟩ := (count_constraints (unique _)).2.2.1 rAllowed.2.2.2
  have xRequired := (count_constraints (unique _)).2.2.2 dAllowed.2.2.2
  obtain ⟨pCut, pMember, pBound⟩ := cut_of_member pRequired
  obtain ⟨yCut, yMember, yBound⟩ := cut_of_member yRequired
  obtain ⟨rCut, rMember, rBound⟩ := cut_of_member rRequired
  obtain ⟨xCut, xMember, _⟩ := cut_of_member xRequired
  have late : (events.take k).length < xCut := by
    apply Classical.byContradiction
    intro early
    apply xExcluded
    exact mem_failedBefore xMember (by omega)
  simp only [List.length_take] at pBound yBound rBound late
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp xMember
  have priorP := prior_entry explained.2.1 split pMember (by omega)
  have priorY := prior_entry explained.2.1 split yMember (by omega)
  have priorR := prior_entry explained.2.1 split rMember (by omega)
  have license := explained.2.1 before xCut xTask after split
  apply license.2.2.2
  apply x_cancelled priorP priorY priorR
  · simp only [List.length_take, Nat.min_eq_left license.1]; omega
  · simp only [List.length_take, Nat.min_eq_left license.1]; omega
  · simp only [List.length_take, Nat.min_eq_left license.1]; omega
  · intro published
    have full : Published matching events xTask := by
      simpa only [List.take_append_drop] using published.append (events.drop xCut)
    have impossible := explained.published_succeeds x_known full
    cases impossible

-----------------------------------------------------------------------------------------
-- Value batching cannot repair the completion reports
-----------------------------------------------------------------------------------------

/-- Keep completion error reports while forgetting value and success events. -/
private def isGroupFailure : Execution.WorkQueueEvent → Bool
  | .groupFailure .. => true
  | _ => false

/-- Value combination never touches failure controls. Witness: constructor inspection. -/
private theorem combine_failureControls {left right merged}
    (compatible : combineValues left right = some merged)
    : isGroupFailure left = false
      ∧ isGroupFailure right = false
      ∧ isGroupFailure merged = false := by
  cases left <;> cases right <;> simp only [combineValues] at compatible
    <;> try contradiction
  all_goals split at compatible
  all_goals cases compatible
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- Value grouping preserves failure controls. Witness: induction on grouping evidence. -/
private theorem grouping_failureControls {events grouped}
    (grouping : ValueGrouping events grouped)
    : events.filter isGroupFailure = grouped.filter isGroupFailure := by
  induction grouping with
  | nil => rfl
  | separate head _ ih => simp only [List.filter_cons]; split <;> simp_all
  | combine head _ compatible ih =>
      obtain ⟨left, right, merged⟩ := combine_failureControls compatible
      simpa only [List.filter_cons, left, right, merged, Bool.false_eq_true,
        ite_false] using ih

/-- Batching preserves ordered failure controls. Witness: per-batch filter equations. -/
private theorem batching_failureControls {events batches}
    (batching : WorkBatching events batches)
    : events.filter isGroupFailure = batches.flatten.filter isGroupFailure := by
  induction batching with
  | nil => rfl
  | cons _ values _ ih =>
      simp only [List.flatten_cons, List.filter_append, grouping_failureControls values, ih]

/-- Filtering retains enough order to force the incompatible error counts.
Witness: split around P, S, R, and D, recovering ordered positions in any atomic history.
-/
private theorem output_controls_unexplained {events matching failures}
    (same : events.filter isGroupFailure = rejectedOutputs.flatten.filter isGroupFailure)
    : ¬Explains work [p, q, r, s] [] events matching failures := by
  change events.filter isGroupFailure =
    [.groupFailure p 1, .groupFailure s 1, .groupFailure r 2, .groupFailure d 2] at same
  obtain ⟨beforeP, restP, splitP, _, _, tailP⟩ := List.filter_eq_cons_iff.mp same
  obtain ⟨beforeS, restS, splitS, _, _, tailS⟩ := List.filter_eq_cons_iff.mp tailP
  obtain ⟨beforeR, restR, splitR, _, _, tailR⟩ := List.filter_eq_cons_iff.mp tailS
  have dMember : Execution.WorkQueueEvent.groupFailure d 2 ∈ events := by
    have filtered : Execution.WorkQueueEvent.groupFailure d 2 ∈ events.filter isGroupFailure := by
      rw [same]
      simp
    exact (List.mem_filter.mp filtered).1
  obtain ⟨l, atD⟩ := List.mem_iff_getElem?.mp dMember
  have atP : events[beforeP.length]? = some (.groupFailure p 1) := by
    simp [splitP]
  have atS : events[beforeP.length + 1 + beforeS.length]? = some (.groupFailure s 1) := by
    simp [splitP, splitS, List.getElem?_append_right, List.getElem?_cons, Nat.add_assoc]
  have atR : events[beforeP.length + 1 + beforeS.length + 1 + beforeR.length]? =
      some (.groupFailure r 2) := by
    simp [splitP, splitS, splitR, List.getElem?_append_right, List.getElem?_cons,
      Nat.add_assoc]
  exact closure_counts_unexplained atP atS atR atD (by omega) (by omega)

/-- The former output is rejected for every failure witness, matching, and batching.
Witness: all regroupings preserve P1, S1, R2, and D2; their counts contradict licensing.
The pre-correction runner produced this trace, not merely a failed candidate explanation.
-/
theorem output_not_valid : ¬ValidHistory work ⟨[p, q, r, s], [], rejectedOutputs⟩ := by
  rintro (⟨events, matching, failures, explained, batching⟩ |
    ⟨events, matching, failures, explained, _, batching⟩)
  · exact output_controls_unexplained (batching_failureControls batching) explained
  · have same := batching_failureControls batching
    simp only [List.filter_append, isGroupFailure, List.filter_cons_of_neg,
      Bool.false_eq_true, not_false_eq_true, List.filter_nil, List.append_nil] at same
    exact output_controls_unexplained same explained

-----------------------------------------------------------------------------------------
-- The same generated work and host source remain within the public conformance premises
-----------------------------------------------------------------------------------------

/-- All nodes in this stream-free work agree with the key-to-descriptor assignment. -/
private def NodesAssigned (assigned : Nat → DeliveryNode) : Execution.Work → Prop
  | .empty => True
  | .combine left right => NodesAssigned assigned left ∧ NodesAssigned assigned right
  | .executionGroup groups _ _ nested =>
      (∀ group ∈ groups, group.node = assigned group.node.key)
      ∧ NodesAssigned assigned nested
  | .stream .. => False

/-- Structural navigation preserves the node assignment. Witness: navigation induction. -/
private theorem NodesAssigned.located {assigned root address current producer owners}
    (assignment : NodesAssigned assigned root)
    (located : Located root address current producer owners)
    : NodesAssigned assigned current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact assignment
  | left prior ih => exact ih.1
  | right prior ih => exact ih.2
  | executionGroup prior ih => exact ih.2
  | item prior entry ih => exact False.elim ih

/-- Each descriptor agrees with its assigned node. Witness: its located group occurrence. -/
private theorem NodesAssigned.node {assigned work node kind dependencies producer}
    (assignment : NodesAssigned assigned work)
    (known : NodeAt work node kind dependencies producer)
    : node = assigned node.key := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member => exact (assignment.located located.toCurrent).1 _ member
  | stream located => exact False.elim (assignment.located located.toCurrent)

/-- Repeated group keys have identical full node metadata throughout this generated work.
Witness: a six-node assignment is preserved by structural navigation to every descriptor.
-/
theorem node_keys_coherent : NodeKeyCoherent work := by
  let assigned (key : Nat) :=
    if key = 0 then p else if key = 1 then q else if key = 2 then r else
      if key = 3 then s else if key = 4 then c else d
  have assignment : NodesAssigned assigned work := by
    simp [NodesAssigned, assigned, work, children, p, q, r, s, c, d]
  intro first firstKind firstDeps firstProducer second secondKind secondDeps secondProducer
    firstKnown secondKnown same
  rw [assignment.node firstKnown, assignment.node secondKnown, same]

/-- The four initial notices are legal, root-produced groups with outstanding work.
Witness: all four own the shared producer, which is not initially accounted for.
-/
theorem initialized
    : let queue := State.initialize (Work.fromExecution work)
      Initializes work queue.initialGroups queue.initialStreams := by
  have eligible {node : DeliveryNode} (owner : node.key ∈ [p.key, q.key, r.key, s.key])
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
    refine ⟨by simp [announcedKeys, pendingKeys],
      Or.inl ⟨by simp [NodeFailed], Or.inr ?_⟩, by simp, by simp⟩
    intro accounted
    rcases accounted uTask _ ⟨_, _, u_known⟩ owner with cancelled | published
    · simp [TaskCancelled] at cancelled
    · simp [Published] at published
  have known {node : DeliveryNode} (member : node ∈ [p, q, r, s])
      : NodeAt work node .group [] none := by
    refine ⟨[1, 1, 0], _, [], .ok (userData, 0), children, [], ⟨node, []⟩,
      rfl, ?_, rfl, rfl⟩
    simpa only [List.mem_cons, List.not_mem_nil, or_false, DeferredFragment.mk.injEq,
      and_true] using member
  change Initializes work [p, q, r, s] []
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  refine ⟨[], none, known member, eligible ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp

private def source : EventSource (List GraphEvent) :=
  { admissible := fun batches => batches.IsPrefix inputs, finished := fun _ => False }

/-- An opaque prefix source supplies this replay under every existing source law.
Witness: source admission is prefix closure of the checked fixed-outcome input trace.
-/
theorem source_validGraphEvents
    : ∀ batches, source.admissible batches → ValidGraphEvents work batches.flatten := by
  intro batches admitted
  obtain ⟨tail, same⟩ := admitted
  apply source_valid.prefix
  exact ⟨tail.flatten, by rw [← List.flatten_append, ← same]⟩

/-- Every admitted input prefix settles only started tasks before termination.
Witness: evaluate the unchanged start checker at each of the seven source prefixes.
-/
theorem source_respectsStarts
    : ∀ batches, source.admissible batches → inputsStarted work batches = true := by
  intro batches admitted
  change batches.IsPrefix inputs at admitted
  have same := List.prefix_iff_eq_take.mp admitted
  have bound : batches.length ≤ 6 := admitted.length_le
  have lengths : batches.length = 0 ∨ batches.length = 1 ∨ batches.length = 2
      ∨ batches.length = 3 ∨ batches.length = 4 ∨ batches.length = 5
      ∨ batches.length = 6 := by omega
  rcases lengths with length | length | length | length | length | length | length
    <;> rw [same, length] <;> cbv

/-- This source satisfies both graph-event validity and actual-start admission.
Witness: the checked prefixes of its fixed finite input trace.
-/
theorem source_conforms : source.ValidFor work :=
  ⟨
    rfl,
    ⟨inputs, rfl⟩,
    fun _ _ before after => before.trans after,
    fun batches admitted =>
      ⟨source_validGraphEvents batches admitted, source_respectsStarts batches admitted⟩
  ⟩

/-- The corrected implementation no longer emits the rejected completion counts.
Witness: exact replay reports one error for D; the former trace reports two.
-/
theorem runner_avoids_rejected_output
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      ≠ rejectedOutputs := by
  rw [output.2.2]
  simp [correctedOutputs, rejectedOutputs]

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerLateFailedParent
