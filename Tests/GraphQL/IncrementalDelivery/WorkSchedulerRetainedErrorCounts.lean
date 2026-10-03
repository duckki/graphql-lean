import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingHealthy
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureContributions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureTotals
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureCuts
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A latent shared owner must retain errors from independently failed contributors.
Generated-work regressions check accumulation and reject the former first-error output.
-/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedErrorCounts
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def firstRoot : DeliveryNode :=
  { ref := 0, path := [], label := some (.string "R") }

private def secondRoot : DeliveryNode :=
  { ref := 1, path := [], label := some (.string "S") }

private def parent : DeliveryNode := { ref := 2, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 3, path := [], label := some (.string "C") }
private def firstTask : Occurrence := .executionGroup [1, 0]
private def secondTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def data : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨firstRoot, []⟩, ⟨child, [parent]⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨secondRoot, []⟩, ⟨child, [parent]⟩] [] (.error 2) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (data, 0)) (.combine .empty .empty))
          .empty)))

private def first : GraphEvent := .taskFailure firstTask 1
private def second : GraphEvent := .taskFailure secondTask 2

private def finish : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def batches (childErrors : Nat) : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure firstRoot 1],
    [.groupFailure secondRoot 2],
    [
      .groupValues parent
        [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
      .groupSuccess parent [child] [],
      .groupFailure child childErrors,
      .workQueueTermination
    ]
  ]

/-- Both failed partitions and their shared latent owner are execution-generated.
Witness: two root defers overlap different fields of C, which waits for healthy P.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first")] (some "R"),
      defer [field "fail", field "required" [] [] (some "second")] (some "S"),
      defer [field "a", defer [field "required" [] [] (some "first"),
        field "fail", field "required" [] [] (some "second")] (some "C")]
        (some "P")], ?_⟩
  cbv

private theorem first_known
    : TaskAt work firstTask [firstRoot.ref, child.ref] none (.object [] (.error 1)) :=
  ⟨[⟨firstRoot, []⟩, ⟨child, [parent]⟩], [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem second_known
    : TaskAt work secondTask [secondRoot.ref, child.ref] none (.object [] (.error 2)) :=
  ⟨[⟨secondRoot, []⟩, ⟨child, [parent]⟩], [], .error 2, .empty, [], rfl, rfl, rfl⟩

private theorem parent_known
    : TaskAt work parentTask [parent.ref] none (.object [] (.ok (data, 0))) :=
  ⟨[⟨parent, []⟩], [], .ok (data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩

/-- The independent failures and parent success obey all graph-event laws.
Witness: fixed outcomes, fresh identities, and absence of structural producers.
-/
theorem inputs_valid : ValidGraphEvents work [first, second, finish] := by
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, _, first_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first])
      ⟨_, _, _, first_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [first, second] :=
    .append one ⟨_, _, _, second_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first, second,
        firstTask, secondTask])
      ⟨_, _, _, second_known, by intro source impossible; cases impossible⟩
  exact .append two ⟨_, _, parent_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, first, second, finish,
      firstTask, secondTask, parentTask])
    ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩

/-- The real runner accepts both failures and C reports their accumulated error count.
Witness: exact queue/publisher replay, including C's normal announcement and termination.
-/
theorem output
    : inputsStarted work [[first], [second], [finish]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[first], [second], [finish]]).2
        = batches 3 := by
  cbv

/-- C's two recorded contributors require three errors, not the retained first count.
Witness: exact source payloads instantiate the independent NodeErrors contract.
-/
theorem expected_errors : NodeErrors work [firstTask, secondTask] child.ref 3 := by
  refine ⟨fun occurrence => if occurrence = firstTask then 1 else 2, ?_, ?_⟩
  · intro occurrence member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, _, _, first_known, by simp [Payload.failure]⟩
    · exact ⟨_, _, _, second_known,
        by simp [Payload.failure, firstTask, secondTask]⟩
  · simp [firstTask, secondTask]

/-- Reporting one error cannot account for the two-error contributor.
Witness: the general per-contributor lower bound in NodeErrors.
-/
theorem wrong_errors {failed : List Occurrence} (recorded : secondTask ∈ failed)
    : ¬NodeErrors work failed child.ref 1 := by
  intro counted
  have bound := counted.contribution_le recorded second_known
    (by simp : child.ref ∈ [secondRoot.ref, child.ref])
  change 2 ≤ 1 at bound
  omega

/-- Only the three displayed task occurrences can contribute errors.
Witness: the finite structural observation-token inventory.
-/
private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = firstTask ∨ occurrence = secondTask ∨ occurrence = parentTask := by
  have member := known.observationToken
  simpa [observationTokens, work, firstTask, secondTask, parentTask] using member

/-- S's positive completion count forces the second failed task into any explanation.
Witness: every other task contributes zero errors to S.
-/
private theorem second_recorded {failed : List Occurrence}
    (counted : NodeErrors work failed secondRoot.ref 2)
    : secondTask ∈ failed := by
  classical
  apply Classical.byContradiction
  intro absent
  obtain ⟨contribution, counts, total⟩ := counted
  have zero : ∀ occurrence ∈ failed, contribution occurrence = 0 := by
    intro occurrence member
    obtain ⟨owners, producer, payload, known, same⟩ := counts occurrence member
    rcases task_cases known with rfl | rfl | rfl
    · obtain ⟨rfl, _, rfl⟩ := known.unique first_known
      simpa [firstRoot, secondRoot, child, Payload.failure] using same
    · exact (absent member).elim
    · obtain ⟨rfl, _, rfl⟩ := known.unique parent_known
      simpa [parent, secondRoot, Payload.failure] using same
  have sumZero : (failed.map contribution).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro value member
    obtain ⟨occurrence, inFailed, rfl⟩ := List.mem_map.mp member
    exact zero occurrence inFailed
  omega

/-- No matching or failure-cut evidence explains the former first-error atomic output.
Witness: S forces the two-error failure before C closes; C then reports less than that
single contributor, contradicting NodeErrors independently of the first failure.
-/
theorem firstOnly_unexplained (matching : PublicationMatching) (failures : FailureCuts)
    : ¬Explains work [firstRoot, secondRoot, parent] []
        ((batches 1).flatten.take 5) matching failures := by
  intro explained
  have secondAllowed := explained.2.2 1 (.groupFailure secondRoot 2) rfl
  have childAllowed := explained.2.2 4 (.groupFailure child 1) rfl
  simp only [EventAllowed, failedBefore_filter _ (Nat.le_refl _)]
    at secondAllowed childAllowed
  have recorded : secondTask ∈ failedBefore failures 1 :=
    second_recorded secondAllowed.2.2.2
  have later : secondTask ∈ failedBefore failures 4 := by
    obtain ⟨entry, member, same⟩ := List.mem_map.mp recorded
    obtain ⟨member, cut⟩ := List.mem_filter.mp member
    exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr
      ⟨member, by simpa using Nat.le_trans (of_decide_eq_true cut) (by decide : 1 ≤ 4)⟩,
      same⟩
  exact wrong_errors later childAllowed.2.2.2

/-- Keep only group-failure controls when comparing alternative batching witnesses. -/
private def isGroupFailure : Execution.WorkQueueEvent → Bool
  | .groupFailure .. => true
  | _ => false

/-- Value coalescing cannot absorb or manufacture a group failure.
Witness: the two compatible value constructors have no failure controls.
-/
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

/-- All possible value groupings retain failure controls in their original order.
Witness: induction over separate/coalesced value outputs.
-/
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

/-- Work batching retains failure controls, including their order and exact counts.
Witness: the per-batch grouping equality and induction over batch concatenation.
-/
private theorem batching_failureControls {events outputs}
    (batching : WorkBatching events outputs)
    : events.filter isGroupFailure = outputs.flatten.filter isGroupFailure := by
  induction batching with
  | nil => rfl
  | cons _ values _ ih =>
      simp only [List.flatten_cons, List.filter_append,
        grouping_failureControls values, ih]

/-- An ordered pair in a subsequence has strictly ordered original event indices.
Witness: list induction either skips the head or selects it as the first element.
-/
private theorem pair_positions {α : Type} {left right : α} {events : List α}
    (ordered : [left, right].Sublist events)
    : ∃ i j : Nat, i < j ∧ events[i]? = some left ∧ events[j]? = some right := by
  induction events with
  | nil => cases ordered
  | cons head tail ih =>
      cases ordered with
      | cons _ smaller =>
          obtain ⟨i, j, before, firstAt, secondAt⟩ := ih smaller
          exact ⟨i + 1, j + 1, by omega, firstAt, secondAt⟩
      | cons_cons _ smaller =>
          obtain ⟨j, secondAt⟩ :=
            List.mem_iff_getElem?.mp (List.singleton_sublist.mp smaller)
          exact ⟨0, j + 1, by omega, rfl, secondAt⟩

/-- Any explanation containing S's failure before C's low count is impossible.
Witness: ordered failure cuts retain S's two-error contributor when C closes.
-/
private theorem ordered_failures_unexplained {events matching failures}
    (ordered : [.groupFailure secondRoot 2, .groupFailure child 1].Sublist events)
    : ¬Explains work [firstRoot, secondRoot, parent] [] events matching failures := by
  intro explained
  obtain ⟨i, j, before, secondAt, childAt⟩ := pair_positions ordered
  have secondAllowed := explained.2.2 i (.groupFailure secondRoot 2) secondAt
  have childAllowed := explained.2.2 j (.groupFailure child 1) childAt
  simp only [EventAllowed, failedBefore_filter _ (Nat.le_refl _)]
    at secondAllowed childAllowed
  have recorded := second_recorded secondAllowed.2.2.2
  have later : secondTask ∈ failedBefore failures (events.take j).length := by
    obtain ⟨entry, member, same⟩ := List.mem_map.mp recorded
    obtain ⟨member, cut⟩ := List.mem_filter.mp member
    refine List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨member, ?_⟩, same⟩
    have earlier := of_decide_eq_true cut
    simp only [List.length_take] at earlier ⊢
    exact decide_eq_true (by omega)
  exact wrong_errors later childAllowed.2.2.2

/-- The emitted failure controls contain S before C under every atomic explanation.
Witness: batching preserves the exact failure subsequence; filtering only removes events.
-/
private theorem failure_pair {events : List Execution.WorkQueueEvent}
    (same : events.filter isGroupFailure = (batches 1).flatten.filter isGroupFailure)
    : [.groupFailure secondRoot 2, .groupFailure child 1].Sublist events := by
  have ordered : [.groupFailure secondRoot 2, .groupFailure child 1].Sublist
      (events.filter isGroupFailure) := by
    rw [same]
    exact (List.Sublist.refl _).cons _
  exact ordered.trans List.filter_sublist

/-- No alternative atomic explanation or batching admits the former first-error history.
Witness: every grouping retains S's two-error failure before C's one-error completion.
-/
theorem firstOnly_invalid
    : ¬ValidHistory work ⟨[firstRoot, secondRoot, parent], [], batches 1⟩ := by
  rintro (⟨events, matching, failures, explained, batching⟩ |
    ⟨events, matching, failures, explained, _, batching⟩)
  · exact ordered_failures_unexplained
      (failure_pair (batching_failureControls batching)) explained
  · have same := batching_failureControls batching
    simp only [List.filter_append, isGroupFailure, List.filter_cons_of_neg,
      Bool.false_eq_true, not_false_eq_true, List.filter_nil, List.append_nil] at same
    exact ordered_failures_unexplained (failure_pair same) explained

-----------------------------------------------------------------------------------------
-- Admission of accumulated errors
-----------------------------------------------------------------------------------------

private def matching : PublicationMatching := fun _ => parentTask
private def failures : FailureCuts := [(0, firstTask), (0, secondTask)]
private def initial : NodeRefs := [firstRoot.ref, parent.ref, secondRoot.ref]
private def events : List Execution.WorkQueueEvent := (batches 3).flatten.take 5

/-- The three task addresses expose only R, S, P and the repeated descriptor for C.
Witness: structural task exhaustiveness and explicit lookups at those addresses.
-/
private theorem node_cases {node kind dependencies producer}
    (known : NodeAt work node kind dependencies producer)
    : kind = .group
      ∧ producer = none
      ∧ ((node = firstRoot ∧ dependencies = [])
          ∨ (node = secondRoot ∧ dependencies = [])
          ∨ (node = parent ∧ dependencies = [])
          ∨ (node = child ∧ dependencies = [parent.ref])) := by
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have group : kind = .group := by
    have role := Correctness.node_ref_role roles known
    cases kind with
    | group => rfl
    | stream => change false = true at role; cases role
  subst kind
  obtain ⟨address, groups, path, result, children, enclosing, group,
    located, member, rfl, rfl⟩ := known
  have task : TaskAt work (.executionGroup address)
      (groups.map (fun group => group.node.ref)) producer (.object path result) :=
    ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩
  rcases task_cases task with same | same | same
  · have addressEq : address = [1, 0] := Occurrence.executionGroup.inj same
    subst address
    have equal : groups = [⟨firstRoot, []⟩, ⟨child, [parent]⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp
  · have addressEq : address = [1, 1, 0] := Occurrence.executionGroup.inj same
    subst address
    have equal : groups = [⟨secondRoot, []⟩, ⟨child, [parent]⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp
  · have addressEq : address = [1, 1, 1, 0] := Occurrence.executionGroup.inj same
    subst address
    have equal : groups = [⟨parent, []⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    have equal := List.mem_singleton.mp member
    subst group
    simp

private theorem first_node : NodeAt work firstRoot .group [] none :=
  ⟨[1, 0], _, [], .error 1, .empty, [], ⟨firstRoot, []⟩, rfl, by simp, rfl, rfl⟩

private theorem second_node : NodeAt work secondRoot .group [] none :=
  ⟨[1, 1, 0], _, [], .error 2, .empty, [], ⟨secondRoot, []⟩, rfl, by simp, rfl, rfl⟩

private theorem parent_node : NodeAt work parent .group [] none :=
  ⟨
    [1, 1, 1, 0],
    _,
    [],
    .ok (data, 0),
    .combine .empty .empty,
    [],
    ⟨parent, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem child_node : NodeAt work child .group [parent.ref] none :=
  ⟨[1, 0], _, [], .error 1, .empty, [], ⟨child, [parent]⟩, rfl, by simp, rfl, rfl⟩

/-- An independent root with no failed contributor has no causal failure derivation.
Witness: it has no dependencies or producer, and every direct failure is excluded.
-/
private theorem root_healthy {node failed published}
    (known : NodeAt work node .group [] none) (notChild : node.ref ≠ child.ref)
    (noOwner
      : ∀ occurrence ∈ failed,
          ∀ owners, TaskHasOwners work occurrence owners → node.ref ∉ owners)
    : ¬Causality.NodeFailed work failed published node.ref := by
  intro cause
  cases cause with
  | task task owner recorded => exact noOwner _ recorded _ task owner
  | groupDependency other member _ =>
      obtain ⟨other, birth, descriptor, same⟩ := other
      rcases (node_cases descriptor).2.2 with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at member
      · simp at member
      · simp at member
      · exact notChild same.symm
  | streamDependencies other _ _ =>
      obtain ⟨other, birth, descriptor, _⟩ := other
      cases (node_cases descriptor).1
  | producers _ noRoot _ _ => exact noRoot ⟨node, .group, [], known, rfl⟩

/-- Both independent failures leave P healthy at every observed prefix.
Witness: neither failed task owns P, and P has no parent or structural producer.
-/
private theorem parent_healthy (observed : List Execution.WorkQueueEvent)
    : ¬NodeFailed work matching observed failures parent.ref := by
  rintro ⟨cut, member, _, cause⟩
  have zero : cut = 0 := by simpa [failures] using member
  subst cut
  apply root_healthy parent_node (by decide) ?_ cause
  intro occurrence member owners ⟨birth, payload, known⟩
  change occurrence ∈ [firstTask, secondTask] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · obtain ⟨rfl, _, _⟩ := known.unique first_known
    decide
  · obtain ⟨rfl, _, _⟩ := known.unique second_known
    decide

/-- P cannot be cancelled by the two recorded failures.
Witness: its only owner remains healthy and its task has no structural producer.
-/
private theorem parent_uncancelled (observed : List Execution.WorkQueueEvent)
    : ¬TaskCancelled work matching observed failures parentTask := by
  rintro ⟨cut, member, bound, cause⟩
  cases cause with
  | owners known _ _ failed =>
      obtain ⟨birth, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique parent_known
      exact parent_healthy observed ⟨cut, member, bound, failed parent.ref (by simp)⟩
  | producerFailed known _ _ | producerCancelled known _ _ =>
      obtain ⟨owners, payload, known⟩ := known
      cases (known.unique parent_known).2.1

/-- The first failure does not cancel the second task through their shared latent C.
Witness: the second task still has its independent healthy owner S.
-/
private theorem second_uncancelled
    : ¬TaskCancelled work matching [] [(0, firstTask)] secondTask := by
  rintro ⟨cut, member, _, cause⟩
  have zero : cut = 0 := by simpa using member
  subst cut
  cases cause with
  | owners known _ _ failed =>
      obtain ⟨birth, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique second_known
      apply root_healthy second_node (by decide) ?_ (failed secondRoot.ref (by simp))
      intro occurrence member owners ⟨birth, payload, task⟩
      change occurrence ∈ [firstTask] at member
      have same := List.mem_singleton.mp member
      subst occurrence
      obtain ⟨rfl, _, _⟩ := task.unique first_known
      decide
  | producerFailed known _ _ | producerCancelled known _ _ =>
      obtain ⟨owners, payload, known⟩ := known
      cases (known.unique second_known).2.1

/-- Both failures may be recorded before output because their root owners are open.
Witness: ordered licensing uses R for the first task and still-healthy S for the second.
-/
private theorem failure_licensed
    : FailureWitness work initial matching events failures := by
  intro before cut occurrence after equal
  cases before with
  | nil =>
      simp only [failures, List.nil_append, List.cons.injEq, Prod.mk.injEq] at equal
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
      refine ⟨by decide, by simp, ?_, by simp [TaskCancelled]⟩
      exact ⟨
        _,
        _,
        _,
        first_known,
        rfl,
        .root ⟨_, _, first_known⟩,
        firstRoot.ref,
        by simp,
        by decide
      ⟩
  | cons entry rest =>
      cases rest with
      | nil =>
          simp only [failures, List.cons_append, List.nil_append, List.cons.injEq,
            Prod.mk.injEq] at equal
          obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := equal
          refine ⟨by decide, by simp, ?_, second_uncancelled⟩
          exact ⟨
            _,
            _,
            _,
            second_known,
            rfl,
            .root ⟨_, _, second_known⟩,
            secondRoot.ref,
            by simp,
            by decide
          ⟩
      | cons next rest =>
          have lengths := congrArg List.length equal
          simp [failures] at lengths

/-- Initial notices select the three independent roots with outstanding task outcomes.
Witness: each root's unpublished contributor and empty prior failure evidence.
-/
private theorem initial_eligible {node occurrence owners payload}
    (known : TaskAt work occurrence owners none payload) (owner : node.ref ∈ owners)
    : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
  refine ⟨
    by simp [announcedRefs, pendingRefs],
    Or.inl ⟨by simp [NodeFailed], Or.inr ?_⟩,
    by simp,
    by simp
  ⟩
  intro accounted
  rcases accounted occurrence owners ⟨_, _, known⟩ owner with cancelled | published
  · simp [TaskCancelled] at cancelled
  · simp [Published] at published

private theorem initialized : Initializes work [firstRoot, parent, secondRoot] [] := by
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨[], none, first_node, initial_eligible first_known (by simp)⟩
  · exact ⟨[], none, parent_node, initial_eligible parent_known (by simp)⟩
  · exact ⟨[], none, second_node, initial_eligible second_known (by simp)⟩

/-- Every owner receives exactly the sum of its two recorded task contributions.
Witness: the fixed one-error and two-error payloads, with zero for non-owners.
-/
private theorem recorded_errors {ref errors}
    (total
      : errors
        = (if ref ∈ [firstRoot.ref, child.ref] then 1 else 0)
          + (if ref ∈ [secondRoot.ref, child.ref] then 2 else 0))
    : NodeErrors work [firstTask, secondTask] ref errors := by
  refine ⟨fun occurrence => if occurrence = firstTask then
    (if ref ∈ [firstRoot.ref, child.ref] then 1 else 0)
    else (if ref ∈ [secondRoot.ref, child.ref] then 2 else 0), ?_, ?_⟩
  · intro occurrence member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨_, _, _, first_known, by simp [Payload.failure]⟩
    · exact ⟨_, _, _, second_known,
        by simp [Payload.failure, firstTask, secondTask]⟩
  · simpa [firstTask, secondTask] using total

private theorem first_failure_allowed
    : EventAllowed work initial matching [] failures (.groupFailure firstRoot 1) := by
  refine ⟨⟨[], none, first_node⟩, by unfold Open; decide, ?_, recorded_errors (by decide)⟩
  exact NodeFailed.task first_known (by simp) (by simp [failures, failedBefore])

private theorem second_failure_allowed
    : EventAllowed work initial matching (events.take 1) failures
        (.groupFailure secondRoot 2) := by
  refine ⟨
    ⟨[], none, second_node⟩,
    by unfold Open; decide,
    ?_,
    recorded_errors (by decide)
  ⟩
  exact NodeFailed.task second_known (by simp) (by simp [failures, failedBefore])

private theorem parent_value_allowed
    : EventAllowed work initial matching (events.take 2) failures
        (.groupValues parent
          [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }]) := by
  refine ⟨[parent.ref], none,
    { path := [], data := data, deliveryGroups := [parent] },
    rfl, parent_known, ?_, ?_⟩
  · refine ⟨?_, parent_uncancelled _, by simp, trivial⟩
    rintro ⟨index, event, selected, value, _⟩
    match index with
    | 0 => cases selected; exact value
    | 1 => cases selected; exact value
    | index + 2 => simp [events, batches] at selected
  · have opened : OpenOwner work initial (events.take 2) [parent.ref] parent :=
      ⟨⟨.group, [], none, parent_node⟩, by simp, by unfold Open; decide⟩
    refine ⟨opened, ⟨parent, opened, parent_healthy _⟩, ?_⟩
    intro other available
    obtain ⟨kind, dependencies, producer, known⟩ := available.1
    rcases (node_cases known).2.2 with
      ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- P's successful value is visible before its closure releases C.
Witness: the third atomic output is matched to P's unique successful task.
-/
private theorem parent_published : Published matching (events.take 3) parentTask :=
  ⟨
    2,
    .groupValues parent
      [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
    rfl,
    trivial,
    rfl
  ⟩

private theorem parent_success_allowed
    : EventAllowed work initial matching (events.take 3) failures
        (.groupSuccess parent [child] []) := by
  refine ⟨⟨[], none, parent_node⟩, by unfold Open; decide, parent_healthy _, ?_, ?_⟩
  · rintro occurrence owners ⟨birth, payload, known⟩ owner
    rcases task_cases known with rfl | rfl | rfl
    · obtain ⟨rfl, _, _⟩ := known.unique first_known
      simp [firstRoot, parent, child] at owner
    · obtain ⟨rfl, _, _⟩ := known.unique second_known
      simp [secondRoot, parent, child] at owner
    · exact Or.inr parent_published
  · refine ⟨by decide, ?_, by simp⟩
    intro node member
    have same := List.mem_singleton.mp member
    subst node
    refine ⟨[parent.ref], none, child_node, by decide, Or.inr ?_, by simp, ?_⟩
    · exact ⟨rfl, firstTask, [firstRoot.ref, child.ref],
        by simp [failedBefore, failures], ⟨_, _, first_known⟩, by simp⟩
    · intro ref member
      have same := List.mem_singleton.mp member
      subst ref
      exact ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩

private theorem child_failure_allowed
    : EventAllowed work initial matching (events.take 4) failures
        (.groupFailure child 3) := by
  refine ⟨
    ⟨[parent.ref], none, child_node⟩,
    by unfold Open; decide,
    ?_,
    recorded_errors (by decide)
  ⟩
  exact NodeFailed.task first_known (by simp) (by simp [failures, failedBefore])

/-- The corrected five atomic outputs share a coherent admission witness.
Witness: two independently licensed failures and P's unique successful publication.
-/
theorem atomic_explanation
    : Explains work [firstRoot, parent, secondRoot] [] events matching failures := by
  refine ⟨initialized, failure_licensed, ?_⟩
  intro index event selected
  match index with
  | 0 => cases selected; exact first_failure_allowed
  | 1 => cases selected; exact second_failure_allowed
  | 2 => cases selected; exact parent_value_allowed
  | 3 => cases selected; exact parent_success_allowed
  | 4 => cases selected; exact child_failure_allowed
  | index + 5 => simp [events, batches] at selected

/-- All work is accounted for and every announced group is closed after C reports.
Witness: the two recorded failures cancel their tasks, while P publishes successfully.
-/
private theorem terminal : Terminal work initial matching events failures := by
  constructor
  · intro occurrence owners producer payload known
    rcases task_cases known with rfl | rfl | rfl
    · apply Or.inl
      refine ⟨0, by simp [failures], by simp, ?_⟩
      apply Causality.TaskCancelled.owners ⟨_, _, first_known⟩
        (by simp [Published]) (by simp)
      intro ref member
      exact Causality.NodeFailed.task ⟨_, _, first_known⟩ member
        (by simp [failedBefore, failures])
    · apply Or.inl
      refine ⟨0, by simp [failures], by simp, ?_⟩
      apply Causality.TaskCancelled.owners ⟨_, _, second_known⟩
        (by simp [Published]) (by simp)
      intro ref member
      exact Causality.NodeFailed.task ⟨_, _, second_known⟩ member
        (by simp [failedBefore, failures])
    · exact Or.inr ⟨2, .groupValues parent [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }], rfl, trivial, rfl⟩
  · intro node kind dependencies producer known
    apply Or.inl
    rcases (node_cases known).2.2 with
      ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- The generated runner now yields an admitted terminal history with C's full count.
Witness: exact initialized replay, coherent atomic admission, and the actual three batches.
-/
theorem runner_admitted
    : let queue := State.initialize (Work.fromExecution work)
      AdmissibleRun work
        ⟨
          queue.initialGroups,
          queue.initialStreams,
          (queue.runNormalized [[first], [second], [finish]]).2
        ⟩ := by
  change AdmissibleRun work
    ⟨[firstRoot, parent, secondRoot], [],
      ((State.initialize (Work.fromExecution work)).runNormalized
        [[first], [second], [finish]]).2⟩
  rw [output.2]
  refine ⟨events, matching, failures, atomic_explanation, terminal, ?_⟩
  exact .cons (batch := [.groupFailure firstRoot 1]) (by simp) (.separate _ .nil)
    (.cons (batch := [.groupFailure secondRoot 2]) (by simp) (.separate _ .nil)
      (.cons
        (batch :=
          [
            .groupValues parent
              [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
            .groupSuccess parent [child] [],
            .groupFailure child 3,
            .workQueueTermination
          ])
        (by simp) (.separate _ (.separate _ (.separate _ (.separate _ .nil)))) .nil))

/-- Reversing the two independent failures still retains the same accumulated count.
Witness: executable replay accepts the reversed starts and reports C's total of three.
-/
theorem reversed_output
    : inputsStarted work [[second], [first], [finish]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[second], [first], [finish]]).2
        = [
          [.groupFailure secondRoot 2],
          [.groupFailure firstRoot 1],
          (batches 3)[2]!
        ] := by
  cbv

/-- Multiple settlements in one host batch retain the same total and control order.
Witness: direct runner replay, without an intervening observation between the failures.
-/
theorem batched_output
    : inputsStarted work [[first, second, finish]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[first, second, finish]]).2
        = [(batches 3).flatten] := by
  cbv

/-- Before P settles, C has a real retained cache with both errors accumulated.
Witness: exact replay of the two failure batches, before the release-time drain.
-/
theorem retained_cache
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
      (queue.groupNode? child.ref).map GroupNode.failure = some (some 3) := by
  cbv

/-- The nonempty retained cache is backed by an actual contributing source failure.
Witness: the general replay provenance theorem, instantiated before C is released.
-/
theorem retained_failure_provenance
    : ∃ occurrence errors owners,
        .taskFailure occurrence errors ∈ [first, second]
        ∧ TaskHasOwners work occurrence owners
        ∧ child.ref ∈ owners := by
  let queue := ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
  have cache := retained_cache
  change (queue.groupNode? child.ref).map GroupNode.failure = some (some 3) at cache
  cases found : queue.groupNode? child.ref with
  | none => simp [found] at cache
  | some node =>
      have failure : node.failure = some 3 := by simpa [found] using cache
      have source := createWorkQueue_runNormalized_cachedFailure_hasSource
        (work := work) (batches := [[first], [second]])
        (inputs_valid.prefix ⟨[finish], rfl⟩) (List.mem_of_find?_eq_some found)
        (by simp [failure])
      simpa [queue.groupNode?_ref found] using source

/-- The second failing task adds its two errors once to each surviving C cache.
Witness: instantiate the general distinct-contributor fold theorem on the real prefix.
The separate `retained_cache` witness checks that C actually survives with total three.
-/
theorem second_failure_increments_once
    : let before :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).1
      ∀ node ∈ (before.taskFailure secondTask 2).1.groupNodes,
        node.group.node.ref = child.ref
        → ∃ old ∈ before.groupNodes,
            old.group.node.ref = child.ref
            ∧ node.failure = some (old.failure.getD 0 + 2) := by
  let before := ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).1
  change ∀ node ∈ (before.taskFailure secondTask 2).1.groupNodes,
    node.group.node.ref = child.ref → ∃ old ∈ before.groupNodes,
      old.group.node.ref = child.ref ∧ node.failure = some (old.failure.getD 0 + 2)
  intro node member ref
  let task : TaskNode := { task := ⟨secondTask, [secondRoot, child]⟩ }
  have found : before.taskNode? secondTask = some task := by
    dsimp only [before, task]
    cbv
  obtain ⟨old, live, same, count⟩ := before.taskFailure_cachedErrors secondTask 2 task found
    (by decide) (node := node) member
  refine ⟨old, live, same.trans ref, ?_⟩
  have eligible : before.taskHasHealthyOwner task.task = true := by
    dsimp only [before, task]
    cbv
  simpa [task, ref, eligible] using count

/-- P's success releases C's earlier three-error cache without changing its total.
Witness: the general task-success cache-origin theorem applied to an actual failed closure.
-/
theorem released_total_has_exact_cache
    : let before :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
      ∃ node ∈ before.groupNodes,
        node.group.node.ref = child.ref ∧ node.failure = some 3 := by
  let before := ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
  apply before.taskSuccess_groupFailure_cached parentTask
    { value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0] }
    (group := child) (errors := 3)
  dsimp only [before]
  cbv
  exact .tail _ (.tail _ (.head _))

/-- The retained failed child still has canonical metadata before its parent releases.
Witness: the generated-replay metadata theorem on an actual nonempty-cache prefix,
together with the independently checked three-error lookup.
-/
theorem retained_metadata
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
      ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ queue.ChildLinksCanonical parents
        ∧ queue.GroupNodesMatchWork work
        ∧ (queue.groupNode? child.ref).map GroupNode.failure = some (some 3) := by
  obtain ⟨parents, canonical, links, provenance⟩ := generated.runNormalized_groupMetadata
    (batches := [[first], [second]]) (inputs_valid.prefix ⟨[finish], rfl⟩)
  exact ⟨parents, canonical, links, provenance, retained_cache⟩

/-- C's retained total is an exact sum of distinct contributing failures in the prefix.
Witness: the general generated replay theorem, with the independently checked cache lookup.
-/
theorem retained_distinct_source_total
    : GroupFailureTotal work [first, second] child.ref 3 := by
  let queue := ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
  have cache := retained_cache
  change (queue.groupNode? child.ref).map GroupNode.failure = some (some 3) at cache
  have totals := generated.runNormalized_cachedFailureTotals (batches := [[first], [second]])
    (inputs_valid.prefix ⟨[finish], rfl⟩) (by cbv)
  cases found : queue.groupNode? child.ref with
  | none => simp [found] at cache
  | some node =>
      have failure : node.failure = some 3 := by simpa [found] using cache
      have total := totals node (List.mem_of_find?_eq_some found) 3 failure
      simpa [queue.groupNode?_ref found] using total

/-- The later failed closure retains a distinct-source total, not P's successful payload.
Witness: the all-handler output theorem after the two-failure source prefix; evaluation
checks the actual group failure in this success handler's output.
-/
theorem released_distinct_source_total
    : GroupFailureTotal work [first, second, finish] child.ref 3 := by
  apply generated.replayGraphEvents_groupFailureTotal
    (before := [first, second])
    (inputs_valid.prefix ⟨[finish], rfl⟩) finish ⟨_, _, parent_known, rfl, rfl⟩
    (group := child) (errors := 3)
  cbv
  exact .tail _ (.tail _ (.head _))

/-- The total predicate does not allow counting the same one-error failure three times.
Witness: the general singleton-source bound forces total one, contradicting total three.
-/
theorem duplicate_contributor_rejected : ¬GroupFailureTotal work [first] child.ref 3 := by
  intro total
  have impossible := total.singleton_count
  contradiction

/-- Normalized delayed completion retains its three-error distinct-source total.
Witness: the general multi-batch theorem on both separate and joined host batches.
Exact runner equations check that the failed closure really occurs in each output.
-/
theorem normalized_distinct_source_totals
    : GroupFailureOrigin work [[first], [second], [finish]].flatten child 3
      ∧ GroupFailureOrigin work [[first, second, finish]].flatten child 3 := by
  constructor
  · apply createWorkQueue_runNormalized_groupFailure_source generated inputs_valid
      (batches := [[first], [second], [finish]])
    rw [output.2]
    simp [batches]
  · apply createWorkQueue_runNormalized_groupFailure_source generated inputs_valid
      (batches := [[first, second, finish]])
    rw [batched_output.2]
    simp [batches]

/-- Actual atomic output supports distinct, reachable, unpublished failure contributors.
Witness: one general publication matching and the migrated failed-group accounting theorem.
The witness is shared with P's successful publication, not chosen for each failed task.
-/
theorem normalized_failure_contributors
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized
          [[first], [second], [finish]]).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
      ∃ contributions : List (Occurrence × Nat),
        contributions ≠ []
        ∧ (contributions.map Prod.fst).Nodup
        ∧ (contributions.map Prod.snd).sum = 3
        ∧ ∀ occurrence count,
            (occurrence, count) ∈ contributions
            → GraphEvent.taskFailure occurrence count ∈ [first, second, finish]
              ∧ (∃ owners producer path,
                  TaskAt work occurrence owners producer (.object path (.error count))
                  ∧ child.ref ∈ owners)
              ∧ Reachable work occurrence
              ∧ ¬Published matching atoms occurrence := by
  obtain ⟨matching, _, exactValues⟩ := createWorkQueue_runNormalized_publicationMatching
    (batches := [[first], [second], [finish]]) inputs_valid output.1
  refine ⟨matching, ?_⟩
  apply createWorkQueue_runNormalized_groupFailure_accounting generated inputs_valid matching
    (fun index event selected value => (exactValues index event selected value).1)
    (batches := [[first], [second], [finish]]) (group := child) (index := 4)
  rw [output.2]
  rfl

/-- A real retained failure keeps exact counts while another contributor is unsettled.
Witness: source-derived all-owner accounting, with executable lookup checking C's one
remaining task. No healthy-owner restriction or output-admission premise is supplied.
-/
theorem retained_pending_accounting
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).1
      (∃ settled,
        settled.Subset ([first].flatMap (fun event => event.identities.1))
        ∧ queue.PendingAccounting work settled)
      ∧ (queue.groupNode? child.ref).map (fun node => (node.pending, node.failure))
        = some (1, some 1) := by
  constructor
  · exact generated.runNormalized_pendingAccounting [[first]]
      (inputs_valid.prefix ⟨[second, finish], rfl⟩) (by cbv)
  · cbv

/-- The real delayed completion admits an exact nonempty distinct NodeErrors inventory.
Witness: the general normalized-output bridge, without supplying a counted-task list.
The inventory still has to be related to the shared failure-cut witness separately.
-/
theorem normalized_nodeErrors_inventory
    : ∃ failed : List Occurrence,
        failed ≠ []
        ∧ failed.Nodup
        ∧ NodeErrors work failed child.ref 3
        ∧ ∀ occurrence ∈ failed,
            ∃ count owners producer path,
              GraphEvent.taskFailure occurrence count ∈ [first, second, finish]
              ∧ TaskAt work occurrence owners producer (.object path (.error count))
              ∧ child.ref ∈ owners := by
  apply createWorkQueue_runNormalized_groupFailure_nodeErrorsWitness generated inputs_valid
    (batches := [[first], [second], [finish]]) (group := child)
  rw [output.2]
  simp [batches, publicationAtoms]

/-- Count transport allows another group's failures and a different inventory order.
Witness: the singleton-source sum and the general complete-contributor bridge; S's
failure contributes zero to R. This is error arithmetic, not a cut-timing claim.
-/
theorem unrelated_failure_preserves_root_total
    : NodeErrors work [secondTask, firstTask] firstRoot.ref 1 := by
  have one : NodeErrors work [firstTask] firstRoot.ref 1 := by
    apply failureContributions_nodeErrors (parts := [(firstTask, 1)]) (by simp)
    intro occurrence errors member
    cases List.mem_singleton.mp member
    exact ⟨_, _, _, first_known, by simp⟩
  apply nodeErrors_of_complete_contributors one (by simp) (by decide)
    (by simp [List.Subset])
  · intro occurrence member
    rcases List.mem_cons.mp member with rfl | remaining
    · exact ⟨_, _, _, second_known⟩
    · cases List.mem_singleton.mp remaining
      exact ⟨_, _, _, first_known⟩
  · intro occurrence member owners known owner
    rcases List.mem_cons.mp member with rfl | remaining
    · obtain ⟨producer, payload, task⟩ := known
      rw [(task.unique second_known).1] at owner
      simp [firstRoot, secondRoot, child] at owner
    · exact remaining

/-- The actual candidate cut reports C's two contributions after reordering the sum.
Witness: build NodeErrors from occurrence/count pairs, then transport it to the visible
cut inventory by completeness and uniqueness, rather than hard-coding a count function.
-/
theorem retained_cut_error_total
    : NodeErrors work (failedBefore failures 4) child.ref 3 := by
  have both : NodeErrors work [secondTask, firstTask] child.ref 3 := by
    apply failureContributions_nodeErrors (parts := [(secondTask, 2), (firstTask, 1)])
      (by decide)
    intro occurrence errors member
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact ⟨_, _, _, second_known, by simp⟩
    · cases List.mem_singleton.mp remaining
      exact ⟨_, _, _, first_known, by simp⟩
  change NodeErrors work [firstTask, secondTask] child.ref 3
  apply nodeErrors_of_complete_contributors both (by decide) (by decide)
    (by simp [List.Subset, or_comm])
  · intro occurrence member
    rcases List.mem_cons.mp member with rfl | remaining
    · exact ⟨_, _, _, first_known⟩
    · cases List.mem_singleton.mp remaining
      exact ⟨_, _, _, second_known⟩
  · intro occurrence member _ _ _
    simpa [or_comm] using member

/-- Omitting C's second failed contributor violates the transport premise.
Witness: its actual task descriptor owns C but its identity is absent from the short list.
-/
theorem missing_contributor_not_complete
    : ¬(∀ occurrence ∈ [firstTask, secondTask],
          ∀ owners,
            TaskHasOwners work occurrence owners
            → child.ref ∈ owners
            → occurrence ∈ [firstTask]) := by
  intro complete
  have missing := complete secondTask (by simp) [secondRoot.ref, child.ref]
    ⟨none, _, second_known⟩ (by simp)
  simp [firstTask, secondTask] at missing

-----------------------------------------------------------------------------------------
-- Actual source boundaries retain past contributors without admitting future failures
-----------------------------------------------------------------------------------------

private def replayCandidateCuts : FailureCuts :=
  let queue := State.initialize (Work.fromExecution work)
  sourceObjectFailureCuts 0
    (queue.sourceRunBlocks { active := queue.initialGroups ++ queue.initialStreams }
      [[first], [second], [finish]]).2.2

/-- Actual source-handler cuts separate the two failures before the delayed release.
Witness: evaluate the candidate constructor over the real queue/publisher annotation.
These positions differ from the earlier hand-picked simultaneous witness, but preserve
the delayed completion's contributor inventory.
-/
theorem replay_candidate_cut_positions
    : replayCandidateCuts = [(0, firstTask), (1, secondTask)] := by cbv

/-- Both failed tasks retain a healthy owner, so selecting eligible labels keeps both cuts.
Witness: the actual queue guard at each source boundary, including the cached shared child.
-/
theorem eligible_replay_candidates_eq
    : let queue := State.initialize (Work.fromExecution work)
      sourceObjectFailureCuts 0
        (queue.eligibleFailureBlocks
          (queue.sourceRunBlocks { active := queue.initialGroups ++ queue.initialStreams }
            [[first], [second], [finish]]).2.2)
      = replayCandidateCuts := by cbv

/-- The first closure's candidate inventory cannot contain the later failing task.
Witness: exact source boundaries, not merely membership in the complete input sequence.
-/
theorem early_replay_cut_excludes_later_failure
    : secondTask ∉ failedBefore replayCandidateCuts 0 := by
  rw [replay_candidate_cut_positions]
  simp [failedBefore, firstTask, secondTask]

/-- The delayed three-error closure's exact inventory is contained in its visible cuts.
Witness: the general normalized candidate-cut theorem, without choosing contributors.
Completeness of arbitrary visible cuts remains a separate obligation.
-/
theorem delayed_replay_cut_inventory
    : ∃ failed : List Occurrence,
        failed ≠ []
        ∧ failed.Nodup
        ∧ NodeErrors work failed child.ref 3
        ∧ failed.Subset (failedBefore replayCandidateCuts 4) := by
  apply createWorkQueue_sourceObjectFailureCuts_nodeErrorsInventory generated inputs_valid
    (batches := [[first], [second], [finish]]) (group := child)
  rw [output.2]
  rfl

/-- The released failed child has a historical cause under the actual candidate cut list.
Witness: general prefix-total coverage reuses an earlier failure, although the current
source handler is successful. No already-admitted-history premise is supplied.
-/
theorem delayed_replay_nodeFailed (matching : PublicationMatching)
    : NodeFailed work matching (((batches 3).flatten.flatMap publicationAtoms).take 4)
        replayCandidateCuts child.ref := by
  have result := createWorkQueue_sourceObjectFailureCuts_nodeFailed generated inputs_valid
    matching (batches := [[first], [second], [finish]]) (index := 4) (group := child)
    (errors := 3) (by rw [output.2]; rfl)
  simpa only [output.2, replayCandidateCuts] using result

/-- The actual candidate cuts give the same three-error child total as the admitted fixture.
Witness: the general complete-count theorem at the actual closing atom. Neither the cut
positions nor the contributing task list are supplied manually; licensing is separate.
-/
theorem replay_candidate_child_errors
    : NodeErrors work (failedBefore replayCandidateCuts 4) child.ref 3 := by
  rw [← eligible_replay_candidates_eq]
  apply createWorkQueue_sourceObjectFailureCuts_nodeErrors generated inputs_valid output.1
    (batches := [[first], [second], [finish]]) (group := child)
  rw [output.2]
  rfl

/-- Every actual group completion has its exact count under the full visible candidate list.
Witness: the generic complete block-to-cut theorem for arbitrary output index and count.
This covers both immediate failures and the delayed accumulated failure in one statement.
-/
theorem every_candidate_total_complete {index : Nat} {group : DeliveryNode} {errors : Nat}
    (atEvent
      : ((batches 3).flatten.flatMap publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : NodeErrors work (failedBefore replayCandidateCuts index) group.ref errors := by
  rw [← eligible_replay_candidates_eq]
  apply createWorkQueue_sourceObjectFailureCuts_nodeErrors generated inputs_valid output.1
    (batches := [[first], [second], [finish]])
  rw [output.2]
  exact atEvent

/-- Joining host batches preserves complete error counting at the delayed closing atom.
Witness: the same candidate-cut theorem on the actual one-batch runner, not a rebatched
synthetic trace or a hand-chosen failure inventory.
-/
theorem joined_candidate_child_errors
    : let queue := State.initialize (Work.fromExecution work)
      let cuts :=
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks
            (queue.sourceRunBlocks
              { active := queue.initialGroups ++ queue.initialStreams }
              [[first, second, finish]]).2.2)
      NodeErrors work (failedBefore cuts 4) child.ref 3 := by
  apply createWorkQueue_sourceObjectFailureCuts_nodeErrors generated inputs_valid batched_output.1
    (batches := [[first, second, finish]]) (group := child)
  rw [batched_output.2]
  rfl

/-- Silent earlier handlers remain visible, while even silent later handlers stay excluded.
Witness: the structural block-visibility theorem around a nonempty completion block.
This isolates index arithmetic; it does not claim these synthetic blocks are a queue run.
-/
theorem silent_contributor_boundaries (later : List SourceOutputBlock)
    : failedBefore
        (sourceObjectFailureCuts 0
          ([(some first, []), (some second, [])]
            ++ (some finish, [.groupFailure child 3]) :: later)) 0
      = [firstTask, secondTask] := by
  simpa [sourceObjectFailureCuts, GraphEvent.objectFailure?, first, second, finish]
    using sourceObjectFailureCuts_visible 0 [(some first, []), (some second, [])] later
      (some finish, [.groupFailure child 3]) 0 (by decide)

-----------------------------------------------------------------------------------------
-- Full source accounting rules out omitted contributors, not just repeated ones
-----------------------------------------------------------------------------------------

/-- Every received failure contributes in this healthy-co-owner regression.
Witness: the guard-filtered replay ledger equals the full two-failure source ledger here.
-/
private theorem both_failures_eligible
    : (State.initialize (Work.fromExecution work)).objectFailureContributions
        [first, second]
      = GraphEvent.failureSettlements [first, second] := by cbv

/-- Actual replay derives full-inventory accounting even while the failed child is latent.
Witness: the general generated-replay theorem; the failure list is fixed by all inputs,
not existentially selected for the cached total.
-/
theorem retained_complete_accounting
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
      queue.GroupErrorAccounting work
        (GraphEvent.failureSettlements [first, second]) := by
  have counted := generated.runNormalized_groupErrorAccounting [[first], [second]]
    (inputs_valid.prefix ⟨[finish], rfl⟩) (by cbv)
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append,
    both_failures_eligible]
    using counted

/-- C's released total counts both failures under the complete source inventory.
Witness: the general replay-and-success-output theorem, with actual handler membership.
No explicit counted-task list or contributor-completeness premise is supplied.
-/
theorem released_complete_source_total
    : NodeErrors work (GraphEvent.failureSettlements [first, second]) child.ref 3 := by
  rw [← both_failures_eligible]
  apply generated.runNormalized_taskSuccess_nodeErrors [[first], [second]]
    (inputs_valid.prefix ⟨[finish], rfl⟩) (by cbv) parentTask
    {
      value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }
    (group := child) (errors := 3)
  cbv
  exact .tail _ (.tail _ (.head _))

/-- A fresh group's zero count already accounts for all earlier failures.
Witness: the fresh-ref clause derived from replay, not an empty-cache initialization guess.
-/
theorem fresh_ref_has_zero_prior_errors
    : NodeErrors work (GraphEvent.failureSettlements [first, second]) 99 0 :=
  retained_complete_accounting.fresh 99 (by cbv; intro impossible; nomatch impossible)

/-- A distinct-source subtotal can still omit a contributor; complete accounting rejects it.
Witness: R's one-error task supplies a valid subtotal, but C also owns the two-error task,
whose contribution alone exceeds one under the full source inventory.
-/
theorem partial_total_is_not_complete
    : GroupFailureTotal work [first, second] child.ref 1
      ∧ ¬NodeErrors work (GraphEvent.failureSettlements [first, second]) child.ref 1 := by
  refine ⟨GroupFailureTotal.single (by simp [first]) first_known (by simp), ?_⟩
  intro counted
  have bound := counted.contribution_le (occurrence := secondTask)
    (by simp [GraphEvent.failureSettlements, GraphEvent.groupFailures, first, second])
    second_known (by simp)
  simp [Payload.failure] at bound

-----------------------------------------------------------------------------------------
-- The drain exhausts active caches and immediate failures keep complete error totals
-----------------------------------------------------------------------------------------

/-- Retaining C's failure leaves no error cache on any active group at the input boundary.
Witness: the unconditional actual-runner invariant, even though the latent cache is nonempty.
-/
theorem retained_active_caches_clear
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
      queue.NoActiveCachedFailure :=
  createWorkQueue_runNormalized_noActiveCachedFailure _ _

/-- All three actual closing handlers report complete totals for their full source prefixes.
Witness: one general all-handler theorem covers immediate R/S failures and C's delayed
release. S's total retains R in the inventory but counts R's contribution as zero.
-/
theorem every_handler_total_complete
    : NodeErrors work (GraphEvent.failureSettlements [first]) firstRoot.ref 1
      ∧ NodeErrors work (GraphEvent.failureSettlements [first, second]) secondRoot.ref 2
      ∧ NodeErrors work (GraphEvent.failureSettlements [first, second, finish]) child.ref
          3 := by
  refine ⟨?_, ?_, ?_⟩
  · apply generated.runNormalized_groupFailure_nodeErrors [] .nil (by cbv) first
      ⟨_, _, _, first_known⟩ (group := firstRoot) (errors := 1)
    cbv
    exact .head _
  · have selected : State.objectFailureContribution
          ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).1 second
          ++ (State.initialize (Work.fromExecution work)).objectFailureContributions [first]
        = GraphEvent.failureSettlements [first, second] := by cbv
    rw [← selected]
    apply generated.runNormalized_groupFailure_nodeErrors [[first]]
      (inputs_valid.prefix ⟨[second, finish], rfl⟩) (by cbv) second
      ⟨_, _, _, second_known⟩ (group := secondRoot) (errors := 2)
    cbv
    exact .head _
  · have selected : State.objectFailureContribution
          ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1 finish
          ++ (State.initialize (Work.fromExecution work)).objectFailureContributions [first, second]
        = GraphEvent.failureSettlements [first, second, finish] := by cbv
    rw [← selected]
    apply generated.runNormalized_groupFailure_nodeErrors [[first], [second]]
      (inputs_valid.prefix ⟨[finish], rfl⟩) (by cbv) finish
      ⟨_, _, parent_known, rfl, rfl⟩ (group := child) (errors := 3)
    cbv
    exact .tail _ (.tail _ (.head _))

/-- The all-live drain bound follows from source replay before and after retained release.
Witness: the general pending-bound theorem on the failing prefix and completed runner.
-/
theorem retained_pending_bounds
    : ((State.initialize (Work.fromExecution work)).runNormalized
        [[first], [second]]).1.PendingBound
        (fun _ => True) ([first, second].flatMap (fun event => event.identities.1))
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[first], [second], [finish]]).1.PendingBound
          (fun _ => True)
          ([first, second, finish].flatMap (fun event => event.identities.1)) := by
  exact ⟨
    generated.runNormalized_pendingBound [[first], [second]]
      (inputs_valid.prefix ⟨[finish], rfl⟩) (by cbv),
    generated.runNormalized_pendingBound [[first], [second], [finish]] inputs_valid
      output.1
  ⟩

/-- A retained failed child does not obstruct healthy counters or started-task links.
Witness: the new source-ledger bridge on the real first-failure prefix; executable counts
show that C is still live while P and the remaining healthy shared owner await work.
-/
theorem retained_healthy_accounting
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first]]).1
      queue.HealthyPendingTracks work [] [firstTask]
      ∧ queue.HealthyTaskLinks work [] [firstTask]
      ∧ (queue.groupNode? parent.ref).map GroupNode.pending = some 1
      ∧ (queue.groupNode? secondRoot.ref).map GroupNode.pending = some 1
      ∧ (queue.groupNode? child.ref).map GroupNode.failure = some (some 1) := by
  have recovered := generated.runNormalized_healthyPendingAndLinks [[first]]
    (inputs_valid.prefix ⟨[second, finish], rfl⟩) (by cbv)
  exact ⟨recovered.1, recovered.2, by cbv⟩

-----------------------------------------------------------------------------------------
-- Recursive drain accounting with a surviving shared owner
-----------------------------------------------------------------------------------------

/-- The parent can legally settle before the second independent failure.
Witness: producer-free task readiness and executable start checks for the two batches.
-/
theorem release_before_second_failure_inputs
    : ValidGraphEvents work [first, finish]
      ∧ inputsStarted work [[first], [finish]] = true := by
  refine ⟨?_, by cbv⟩
  exact .append (before := [first]) (event := finish)
    (inputs_valid.prefix ⟨[second, finish], rfl⟩) ⟨_, _, parent_known, rfl, rfl⟩
    (by
      simp [GraphEvent.Fresh, GraphEvent.identities, first, finish, firstTask, parentTask])
    ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩

/-- Releasing the parent before the second failure preserves its other live owner.
Witness: the full source-event ownership theorem on a generated nonterminal replay;
execution confirms P's success, C's cached failure, and S's remaining task membership.
-/
theorem release_before_second_failure_retains_owner
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [finish]]).1
      queue.HealthyRegisteredTaskAccounting work [parentTask, firstTask] [firstTask]
      ∧ (queue.groupNode? secondRoot.ref).map (fun node => (node.pending, node.tasks))
        = some (1, [secondTask])
      ∧ queue.groupNode? child.ref = none
      ∧ queue.terminated = false := by
  have owners := (generated.runNormalized_healthyRegisteredOwners
    [[first], [finish]] release_before_second_failure_inputs.1
    release_before_second_failure_inputs.2).1
  refine ⟨?_, by cbv⟩
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append,
    GraphEvent.taskSettlements, GraphEvent.failureSettlements, List.flatMap_cons,
    List.flatMap_nil, first, finish, GraphEvent.groupSuccesses, GraphEvent.groupFailures,
    List.nil_append, List.cons_append, List.reverse_cons, List.reverse_nil]
    using owners

/-- Unconditional normalized replay derives surviving ownership from source inputs alone.
Witness: joint owner/ancestry preservation derives integration availability internally;
the exact ledger bridge recovers success-only coordinates after retained-failure release.
-/
theorem release_before_second_failure_replay_owners
    : ((State.initialize (Work.fromExecution work)).runNormalized
        [[first], [finish]]).1.HealthyRegisteredTaskAccounting
        work [parentTask] [firstTask] := by
  obtain ⟨parents, canonical, accounted⟩ := generated.runNormalized_ownerAncestry
    [[first], [finish]] release_before_second_failure_inputs.1
    release_before_second_failure_inputs.2
  exact accounted.accounting.healthyRegisteredTasks

/-- An internal release-boundary fixture using the generated work's descriptors.
S deliberately overcounts its one pending task: the drain theorem needs only a bound,
not equality. P releases failed C, whose remaining task is also still owned by S.
-/
private def releaseBoundary : State :=
  {
    rootGroups := [secondRoot.ref, parent.ref]
    registeredGroups := [secondRoot.ref, parent.ref, child.ref]
    tasks := [⟨secondTask, [secondRoot, child]⟩]
    groupNodes :=
      [
        { group := ⟨secondRoot, none⟩, tasks := [secondTask], pending := 3 },
        { group := ⟨parent, none⟩, childGroups := [child.ref] },
        {
          group := ⟨child, some parent.ref⟩,
          tasks := [secondTask],
          pending := 1,
          failure := some 1
        }
      ]
  }

/-- Healthy ownership survives both drain branches with real remaining work.
Witness: the general drain theorem with canonical generated descriptors, a supported
cache, and a strict pending bound; reduction verifies both closures and S's survival.
This is an internal-state regression, not an additional query-realization claim.
-/
theorem drain_preserves_shared_owner
    : releaseBoundary.drainReadyGroups.1.HealthyRegisteredTaskAccounting
        work [] [firstTask]
      ∧ releaseBoundary.drainReadyGroups.2
        = [.groupSuccess parent [child] [], .groupFailure child 1]
      ∧ (releaseBoundary.drainReadyGroups.1.groupNode? secondRoot.ref).map GroupNode.tasks
        = some [secondTask] := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have links : releaseBoundary.ChildLinksCanonical parents := by
    have childParents := (canonical child [parent.ref] (groupRecordAt_of_nodeAt child_node)).symm
    simp [State.ChildLinksCanonical, releaseBoundary, childParents]
  have matching : releaseBoundary.GroupNodesMatchWork work := by
    intro node member
    simp only [releaseBoundary, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨[], groupRecordAt_of_nodeAt second_node⟩
    · exact ⟨[], groupRecordAt_of_nodeAt parent_node⟩
    · exact ⟨[parent.ref], groupRecordAt_of_nodeAt child_node⟩
  have support : releaseBoundary.CachedFailuresSupported work [firstTask] := by
    intro node member cached
    simp only [releaseBoundary, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · contradiction
    · contradiction
    · refine ⟨firstTask, by simp, [firstRoot.ref, child.ref], ?_, by simp⟩
      exact ⟨none, .object [] (.error 1),
        [⟨firstRoot, []⟩, ⟨child, [parent]⟩], [], .error 1, .empty, [], rfl, rfl, rfl⟩
  have accounted : releaseBoundary.HealthyRegisteredTaskAccounting work [] [firstTask] := by
    intro task member _ ref contributor _
    have same := List.mem_singleton.mp member
    subst task
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      at contributor
    rcases contributor with rfl | rfl
    · exact ⟨{ group := ⟨secondRoot, none⟩, tasks := [secondTask], pending := 3 },
        by simp [releaseBoundary], rfl, by simp⟩
    · exact ⟨{ group := ⟨child, some parent.ref⟩
               tasks := [secondTask]
               pending := 1
               failure := some 1 }, by simp [releaseBoundary], rfl, by simp⟩
  have bounded : releaseBoundary.PendingBound (fun _ => True) [] := by
    simp [State.PendingBound, releaseBoundary, unsettledCount]
  have unique : releaseBoundary.GroupRefsUnique := by
    unfold State.GroupRefsUnique
    decide
  have taskMatching : releaseBoundary.RegisteredTasksMatch work := by
    intro task member
    have same := List.mem_singleton.mp member
    subst task
    exact ⟨⟨_, _, _, rfl, second_known⟩, rfl⟩
  refine ⟨accounted.drainReadyGroups bounded unique support taskMatching generated
    links matching canonical, ?_⟩
  cbv

/-- Retirement certificates survive parent success followed by its cached failed child.
Witness: the general joint drain theorem with generated ancestry and cache provenance;
the surviving root has no dependencies, while the newly retired parent is recorded.
The fixture is an internal drain boundary, not an extra source-law assumption.
-/
theorem drain_preserves_ancestor_certificates
    : releaseBoundary.drainReadyGroups.1.RootAncestorsRetired work
      ∧ releaseBoundary.drainReadyGroups.1.HealthyRetiredAncestors work [firstTask]
      ∧ releaseBoundary.drainReadyGroups.1.RetiredGroup parent.ref
      ∧ releaseBoundary.drainReadyGroups.1.RetiredGroup child.ref := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have links : releaseBoundary.ChildLinksCanonical parents := by
    have childParents := (canonical child [parent.ref] (groupRecordAt_of_nodeAt child_node)).symm
    simp [State.ChildLinksCanonical, releaseBoundary, childParents]
  have matching : releaseBoundary.GroupNodesMatchWork work := by
    intro node member
    simp only [releaseBoundary, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨[], groupRecordAt_of_nodeAt second_node⟩
    · exact ⟨[], groupRecordAt_of_nodeAt parent_node⟩
    · exact ⟨[parent.ref], groupRecordAt_of_nodeAt child_node⟩
  have support : releaseBoundary.CachedFailuresSupported work [firstTask] := by
    intro node member cached
    simp only [releaseBoundary, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · contradiction
    · contradiction
    · exact ⟨firstTask, by simp, [firstRoot.ref, child.ref],
        ⟨none, .object [] (.error 1), first_known⟩, by simp⟩
  have roots : releaseBoundary.RootAncestorsRetired work := by
    intro ref active
    simp only [releaseBoundary, List.mem_cons, List.not_mem_nil, or_false] at active
    rcases active with rfl | rfl
    · exact State.AncestorsRetired.of_descriptor generated second_node (by simp)
    · exact State.AncestorsRetired.of_descriptor generated parent_node (by simp)
  have retirement : releaseBoundary.HealthyRetiredAncestors work [firstTask] := by
    intro ref retired _
    exact (retired.2 (by simpa [releaseBoundary] using retired.1)).elim
  have registered : releaseBoundary.LiveGroupsRegistered := by
    simp [State.LiveGroupsRegistered, releaseBoundary]
  have tasks : releaseBoundary.TaskGroupsRegistered := by
    simp [State.TaskGroupsRegistered, releaseBoundary]
  have preserved := State.drainReadyGroups_retirement roots retirement generated matching
    links canonical registered tasks support
  refine ⟨preserved.1, preserved.2, ?_⟩
  cbv
  change (2 ∈ ([1, 2, 3] : List Nat) ∧ 2 ∉ ([1] : List Nat))
    ∧ (3 ∈ ([1, 2, 3] : List Nat) ∧ 3 ∉ ([1] : List Nat))
  decide

/-- Item-triggered draining also transfers the old cache count to its failed closure.
Witness: the generic item-handler output theorem and an exact nonempty output check.
This is an internal handler boundary, not a claim that this fixture is a generated run.
-/
theorem item_release_preserves_cached_count
    : let stream : DeliveryNode := { ref := 4, path := [.field "items"] }
      let item : StreamItem :=
        { occurrence := .item [4] 0, value := { item := .scalar "item" } }
      let before := { releaseBoundary with rootStreams := [stream.ref] }
      (before.streamItems stream [item]).2
        = [
          .streamValues stream [item.value] [] [],
          .groupSuccess parent [child] [],
          .groupFailure child 1
        ]
      ∧ ∃ node ∈ before.groupNodes,
          node.group.node.ref = child.ref ∧ node.failure = some 1 := by
  dsimp only
  constructor
  · cbv
  · apply State.streamItems_groupFailure_cached { releaseBoundary with rootStreams := [4] }
      { ref := 4, path := [.field "items"] }
      [{ occurrence := .item [4] 0, value := { item := .scalar "item" } }]
      (group := child) (errors := 1)
    cbv
    exact .tail _ (.tail _ (.head _))

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedErrorCounts
