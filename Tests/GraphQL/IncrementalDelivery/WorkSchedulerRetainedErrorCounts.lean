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
Generated-work regressions distinguish collected diagnostics from selected causes,
retain both rejected computations, and reject invented additive completion counts.
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
      (.executionGroup [⟨firstRoot, []⟩, ⟨child, [parent]⟩] []
        ({ result := .error 1, cause := some 1 }) .empty)
      (.combine
        (.executionGroup [⟨secondRoot, []⟩, ⟨child, [parent]⟩] []
          ({ result := .error 2, cause := some 1 }) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] ({ result := .ok (data, 0) })
            (.combine .empty .empty))
          .empty)))

private def first : GraphEvent := .taskFailure firstTask 1
private def second : GraphEvent := .taskFailure secondTask 1

private def finish : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def batches (childErrors : Nat) : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure firstRoot 1],
    [.groupFailure secondRoot 1],
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
  ⟨
    [⟨firstRoot, []⟩, ⟨child, [parent]⟩],
    [],
    { result := .error 1, cause := some 1 },
    .empty,
    [],
    rfl,
    rfl,
    rfl
  ⟩

private theorem second_known
    : TaskAt work secondTask [secondRoot.ref, child.ref] none (.object [] (.error 1)) :=
  ⟨
    [⟨secondRoot, []⟩, ⟨child, [parent]⟩],
    [],
    { result := .error 2, cause := some 1 },
    .empty,
    [],
    rfl,
    rfl,
    rfl
  ⟩

private theorem parent_known
    : TaskAt work parentTask [parent.ref] none (.object [] (.ok (data, 0))) :=
  ⟨
    [⟨parent, []⟩],
    [],
    { result := .ok (data, 0) },
    .combine .empty .empty,
    [],
    rfl,
    rfl,
    rfl
  ⟩

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

/-- The runner reports one selected cause for C after both independent failures. -/
theorem output
    : inputsStarted work [[first], [second], [finish]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[first], [second], [finish]]).2
        = batches 1 := by cbv

/-- Only the three displayed task occurrences can contribute errors.
Witness: the finite structural observation-token inventory.
-/
private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = firstTask ∨ occurrence = secondTask ∨ occurrence = parentTask := by
  have member := known.observationToken
  simpa [observationTokens, work, firstTask, secondTask, parentTask] using member

private def matching : PublicationMatching := fun _ => parentTask
private def failures : FailureCuts := [(0, firstTask), (0, secondTask)]
private def initial : NodeRefs := [firstRoot.ref, parent.ref, secondRoot.ref]
private def events : List Execution.WorkQueueEvent := (batches 1).flatten.take 5

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
      (groups.map (fun group => group.node.ref)) producer (.object path result.deliveryResult) :=
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
  ⟨
    [1, 0],
    _,
    [],
    { result := .error 1, cause := some 1 },
    .empty,
    [],
    ⟨firstRoot, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem second_node : NodeAt work secondRoot .group [] none :=
  ⟨
    [1, 1, 0],
    _,
    [],
    { result := .error 2, cause := some 1 },
    .empty,
    [],
    ⟨secondRoot, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem parent_node : NodeAt work parent .group [] none :=
  ⟨
    [1, 1, 1, 0],
    _,
    [],
    { result := .ok (data, 0) },
    .combine .empty .empty,
    [],
    ⟨parent, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem child_node : NodeAt work child .group [parent.ref] none :=
  ⟨
    [1, 0],
    _,
    [],
    { result := .error 1, cause := some 1 },
    .empty,
    [],
    ⟨child, [parent]⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

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

/-- Either retained contributor can supply the same selected positive boundary cause. -/
theorem first_cause {failed ref} (recorded : firstTask ∈ failed)
    (owner : ref ∈ [firstRoot.ref, child.ref])
    : NodeFailureCause work failed ref 1 :=
  ⟨
    firstTask,
    recorded,
    _,
    none,
    .object [] (.error 1),
    first_known,
    owner,
    rfl,
    by decide
  ⟩

theorem second_cause {failed ref} (recorded : secondTask ∈ failed)
    (owner : ref ∈ [secondRoot.ref, child.ref])
    : NodeFailureCause work failed ref 1 :=
  ⟨
    secondTask,
    recorded,
    _,
    none,
    .object [] (.error 1),
    second_known,
    owner,
    rfl,
    by decide
  ⟩

/-- Generated failures count their selected primitive cause, independently of diagnostics. -/
theorem cause_count {failed ref errors} (cause : NodeFailureCause work failed ref errors)
    : errors = 1 :=
  generated.nodeFailureCause_count cause

/-- Adding the two diagnostic totals is not an admissible completion explanation. -/
theorem aggregate_rejected {failed ref} : ¬NodeFailureCause work failed ref 3 := by
  intro cause
  have equal := cause_count cause
  omega

private theorem first_failure_allowed
    : EventAllowed work initial matching [] failures (.groupFailure firstRoot 1) := by
  refine ⟨
    ⟨[], none, first_node⟩,
    by unfold Open; decide,
    ?_,
    first_cause (by simp [failures, failedBefore]) (by simp)
  ⟩
  exact NodeFailed.task first_known (by simp) (by simp [failures, failedBefore])

private theorem second_failure_allowed
    : EventAllowed work initial matching (events.take 1) failures
        (.groupFailure secondRoot 1) := by
  refine ⟨
    ⟨[], none, second_node⟩,
    by unfold Open; decide,
    ?_,
    second_cause (by simp [failures, failedBefore]) (by simp)
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
        (.groupFailure child 1) := by
  refine ⟨
    ⟨[parent.ref], none, child_node⟩,
    by unfold Open; decide,
    ?_,
    first_cause (by simp [failures, failedBefore]) (by simp)
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
    · refine Or.inl ⟨?_, ?_⟩
      · refine ⟨0, by simp [failures], by simp, ?_⟩
        apply Causality.TaskCancelled.owners ⟨_, _, first_known⟩
          (by simp [Published]) (by simp)
        intro ref member
        exact Causality.NodeFailed.task ⟨_, _, first_known⟩ member
          (by simp [failedBefore, failures])
      · rw [(known.unique first_known).2.2, Payload.path]
        exact ⟨firstRoot, 1, by decide, ⟨[], rfl⟩,
          Or.inl (by simp [events, batches])⟩
    · refine Or.inl ⟨?_, ?_⟩
      · refine ⟨0, by simp [failures], by simp, ?_⟩
        apply Causality.TaskCancelled.owners ⟨_, _, second_known⟩
          (by simp [Published]) (by simp)
        intro ref member
        exact Causality.NodeFailed.task ⟨_, _, second_known⟩ member
          (by simp [failedBefore, failures])
      · rw [(known.unique second_known).2.2, Payload.path]
        exact ⟨secondRoot, 1, by decide, ⟨[], rfl⟩,
          Or.inl (by simp [events, batches])⟩
    · exact Or.inr ⟨2, .groupValues parent [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }], rfl, trivial, rfl⟩
  · intro node kind dependencies producer known
    apply Or.inl
    rcases (node_cases known).2.2 with
      ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- The generated runner now yields an admitted terminal history with C's selected cause.
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
    (.cons (batch := [.groupFailure secondRoot 1]) (by simp) (.separate _ .nil)
      (.cons
        (batch :=
          [
            .groupValues parent
              [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
            .groupSuccess parent [child] [],
            .groupFailure child 1,
            .workQueueTermination
          ])
        (by simp) (.separate _ (.separate _ (.separate _ (.separate _ .nil)))) .nil))

/-- Reversing the two independent failures still retains the same selected cause.
Witness: executable replay accepts the reversed starts and reports C's one selected cause.
-/
theorem reversed_output
    : inputsStarted work [[second], [first], [finish]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[second], [first], [finish]]).2
        = [
          [.groupFailure secondRoot 1],
          [.groupFailure firstRoot 1],
          (batches 1)[2]!
        ] := by
  cbv

/-- Multiple settlements in one host batch retain the same selected cause and control order.
Witness: direct runner replay, without an intervening observation between the failures.
-/
theorem batched_output
    : inputsStarted work [[first, second, finish]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[first, second, finish]]).2
        = [(batches 1).flatten] := by
  cbv

/-- Dormant C retains both task computations and their original diagnostic inventories. -/
theorem retained_rejections
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[first], [second]]).1
      (queue.taskNode? firstTask).bind TaskNode.rejection = some 1
      ∧ (queue.taskNode? secondTask).bind TaskNode.rejection = some 1
      ∧ (queue.groupNode? child.ref).map GroupNode.tasks = some [firstTask, secondTask]
      ∧ (queue.groupNode? child.ref).map GroupNode.pending = some 2
      ∧ (queue.groupNode? child.ref).bind (fun group => queue.rejectedTask? group)
        = some (firstTask, 1) := by cbv

/-- Reversing settlement order still replays the first registered rejected computation. -/
theorem retained_registration_order
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[second], [first]]).1
      (queue.groupNode? child.ref).bind (fun group => queue.rejectedTask? group)
      = some (firstTask, 1) := by cbv

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

/-- Every actual source block carries a positive contributing cause at its own boundary.
Silent settlements remain in the source prefix; future failures are unavailable. -/
theorem source_block_causes
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      SourceBlocksHaveCompleteTotals work []
        (queue.eligibleFailureBlocks
          (queue.sourceRunBlocks publisher [[first], [second], [finish]]).2.2) := by
  exact createWorkQueue_sourceRunBlocks_completeTotals generated
    (batches := [[first], [second], [finish]]) inputs_valid output.1

/-- No atomic explanation can invent an additive failure completion for this work. -/
theorem aggregate_unexplained {events : List Execution.WorkQueueEvent} {matching failures}
    {index : Nat} (selected : events[index]? = some (.groupFailure child 3))
    : ¬Explains work [firstRoot, parent, secondRoot] [] events matching failures := by
  intro explained
  have allowed := explained.2.2 index (.groupFailure child 3) selected
  exact aggregate_rejected allowed.2.2.2

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

/-- Coalescing values or changing atomic batching cannot admit the aggregate count. -/
theorem aggregate_invalid
    : ¬ValidHistory work ⟨[firstRoot, parent, secondRoot], [], batches 3⟩ := by
  rintro (⟨events, matching, failures, explained, batching⟩ |
    ⟨events, matching, failures, explained, _, batching⟩)
  · have same := batching_failureControls batching
    have member : .groupFailure child 3 ∈ events.filter isGroupFailure := by
      rw [same]
      simp [batches, isGroupFailure]
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp member).1
    exact aggregate_unexplained selected explained
  · have same := batching_failureControls batching
    simp only [List.filter_append, isGroupFailure, List.filter_cons_of_neg,
      Bool.false_eq_true, not_false_eq_true, List.filter_nil, List.append_nil] at same
    have member : .groupFailure child 3 ∈ events.filter isGroupFailure := by
      rw [same]
      simp [batches, isGroupFailure]
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp member).1
    exact aggregate_unexplained selected explained

#print axioms cause_count
#print axioms atomic_explanation
#print axioms runner_admitted
#print axioms release_before_second_failure_replay_owners

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedErrorCounts
