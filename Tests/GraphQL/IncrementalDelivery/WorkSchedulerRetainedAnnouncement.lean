import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.NoticeEligibility
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Retained failures admit delayed group notices without relaxing data or child release.
These generated-work regressions do not import the implementation-proof umbrella.
-/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedAnnouncement
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : DeliveryNode := { ref := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { ref := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 2, path := [], label := some (.string "C") }
private def sharedTask : Occurrence := .executionGroup [1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 0]
private def data : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨parent, []⟩] [] (.ok (data, 0)) (.combine .empty .empty))
        .empty))

private def failed : GraphEvent := .taskFailure sharedTask 1

private def succeeded : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 0, 0]
    }

private def initial : NodeRefs := [root.ref, parent.ref]

private def beforeNotice : List Execution.WorkQueueEvent :=
  [
    .groupFailure root 1,
    .groupValues parent
      [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }]
  ]

private def events : List Execution.WorkQueueEvent :=
  beforeNotice ++ [.groupSuccess parent [child] [], .groupFailure child 1]

-----------------------------------------------------------------------------------------
-- Generated inputs and exact reference output
-----------------------------------------------------------------------------------------

/-- The shared failed task and independent successful parent are execution-generated.
Witness: reduction of the query against the fixed pure resolver environment.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required"] (some "R"),
      defer [field "a", defer [field "required"] (some "C")] (some "P")], ?_⟩
  cbv

/-- Exact metadata for the only failed task. Witness: its structural work address. -/
private theorem shared_known
    : TaskAt work sharedTask [root.ref, child.ref] none (.object [] (.error 1)) := by
  exact ⟨[⟨root, []⟩, ⟨child, [parent]⟩], [], .error 1, .empty, [], rfl, rfl, rfl⟩

/-- Exact metadata for the independent parent. Witness: its structural work address. -/
private theorem parent_known
    : TaskAt work parentTask [parent.ref] none (.object [] (.ok (data, 0))) := by
  exact ⟨[⟨parent, []⟩], [], .ok (data, 0), .combine .empty .empty,
    [], rfl, rfl, rfl⟩

/-- Both settlements obey the unchanged fixed-outcome, freshness, and readiness laws.
Witness: two source append rules; both tasks have no structural producer.
-/
theorem inputs_valid : ValidGraphEvents work [failed, succeeded] := by
  have one : ValidGraphEvents work [failed] :=
    .append .nil ⟨_, _, _, shared_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, failed])
      ⟨_, _, _, shared_known, by intro producer impossible; cases impossible⟩
  exact .append one ⟨_, _, parent_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, failed, succeeded,
      sharedTask, parentTask])
    ⟨_, _, _, parent_known, by intro producer impossible; cases impossible⟩

/-- The actual queue admits these starts and announces C before its delayed completion.
Witness: exact normalized replay, with termination in the parent's output batch.
-/
theorem output
    : inputsStarted work [[failed], [succeeded]] = true
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          [[failed], [succeeded]]).2
        = [
          [.groupFailure root 1],
          [
            .groupValues parent
              [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
            .groupSuccess parent [child] [],
            .groupFailure child 1,
            .workQueueTermination
          ]
        ] := by
  cbv

/-- Only the two displayed tasks occur. Witness: the finite structural token inventory. -/
private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = sharedTask ∨ occurrence = parentTask := by
  have member := known.observationToken
  simpa [observationTokens, work, sharedTask, parentTask] using member

-----------------------------------------------------------------------------------------
-- One coherent explanation of the retained-failure output
-----------------------------------------------------------------------------------------

private def matching : PublicationMatching := fun _ => parentTask
private def failures : FailureCuts := [(0, sharedTask)]

/-- The shared task exposes exactly its two descriptors; P is a separate root descriptor.
Witness: the only two task addresses and reduction of their structural lookups.
-/
private theorem node_cases {node kind dependencies producer}
    (known : NodeAt work node kind dependencies producer)
    : kind = .group
      ∧ producer = none
      ∧ ((node = root ∧ dependencies = [])
          ∨ (node = child ∧ dependencies = [parent.ref])
          ∨ (node = parent ∧ dependencies = [])) := by
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
  rcases task_cases task with same | same
  · have addressEq : address = [1, 0] := Occurrence.executionGroup.inj same
    subst address
    have equal : groups = [⟨root, []⟩, ⟨child, [parent]⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp
  · have addressEq : address = [1, 1, 0] := Occurrence.executionGroup.inj same
    subst address
    have equal : groups = [⟨parent, []⟩] ∧ producer = none := by
      have equal := located.symm
      simp [work, locateWork, locateWork.go, WorkLocation.child?] at equal
      exact ⟨equal.1.1, equal.2.1⟩
    rcases equal with ⟨rfl, rfl⟩
    have equal := List.mem_singleton.mp member
    subst group
    simp

private theorem root_node : NodeAt work root .group [] none :=
  ⟨[1, 0], _, [], .error 1, .empty, [], ⟨root, []⟩, rfl, by simp, rfl, rfl⟩

private theorem parent_node : NodeAt work parent .group [] none :=
  ⟨
    [1, 1, 0],
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

/-- The retained R/C failure cannot fail independent P.
Witness: P owns only its successful task, has no dependency, and has a root descriptor.
-/
private theorem parent_healthy (observed : List Execution.WorkQueueEvent)
    : ¬NodeFailed work matching observed failures parent.ref := by
  rintro ⟨cut, member, _, cause⟩
  have zero : cut = 0 := by simpa [failures] using member
  subst cut
  change Causality.NodeFailed work [sharedTask] _ parent.ref at cause
  cases cause with
  | task known owner recorded =>
      have same := List.mem_singleton.mp recorded
      subst_vars
      obtain ⟨birth, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique shared_known
      simp [root, parent, child] at owner
  | groupDependency known member _ =>
      obtain ⟨node, birth, known, same⟩ := known
      rcases (node_cases known).2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all [root, parent, child]
  | streamDependencies known _ _ =>
      obtain ⟨node, birth, known, _⟩ := known
      cases (node_cases known).1
  | producers _ noRoot _ _ => exact noRoot ⟨parent, .group, [], parent_node, rfl⟩

/-- P's successful publication is already visible before its completion notice.
Witness: unbatched value event one is matched to the independent parent task.
-/
private theorem parent_published : Published matching beforeNotice parentTask :=
  ⟨
    1,
    .groupValues parent
      [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
    rfl,
    trivial,
    rfl
  ⟩

/-- The previously rejected child notice is now permitted on P's healthy closure.
Witness: shared failure at cut zero, P's prior publication, and its carrier completion.
-/
theorem notice_allowed
    : EventAllowed work initial matching beforeNotice failures
        (.groupSuccess parent [child] []) := by
  change (∃ dependencies producer, NodeAt work parent .group dependencies producer)
    ∧ Open initial beforeNotice parent.ref
    ∧ ¬NodeFailed work matching beforeNotice failures parent.ref
    ∧ NodeAccounted work matching beforeNotice failures parent.ref
    ∧ Announcements work initial matching
        (beforeNotice ++ [.groupSuccess parent [] []]) failures [child] []
  refine ⟨⟨[], none, parent_node⟩, by unfold Open; decide, parent_healthy _, ?_, ?_⟩
  · rintro occurrence owners ⟨birth, payload, known⟩ owner
    rcases task_cases known with rfl | rfl
    · obtain ⟨rfl, _, _⟩ := known.unique shared_known
      simp [root, parent, child] at owner
    · exact Or.inr parent_published
  · refine ⟨by decide, ?_, by simp⟩
    intro node member
    have same := List.mem_singleton.mp member
    subst node
    refine ⟨[parent.ref], none, child_node, by decide, Or.inr ?_, by simp, ?_⟩
    · exact ⟨rfl, sharedTask, [root.ref, child.ref], by simp [failedBefore, failures],
        ⟨_, _, shared_known⟩, by simp⟩
    · intro ref member
      have same := List.mem_singleton.mp member
      subst ref
      exact ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩

/-- P remains uncancelled until its independent success.
Witness: its root producer and sole healthy owner rule out every cancellation cause.
-/
private theorem parent_uncancelled (observed : List Execution.WorkQueueEvent)
    : ¬TaskCancelled work matching observed failures parentTask := by
  rintro ⟨cut, member, bound, cause⟩
  have zero : cut = 0 := by simpa [failures] using member
  subst cut
  cases cause with
  | owners known _ _ failed =>
      obtain ⟨birth, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique parent_known
      exact parent_healthy observed ⟨0, member, bound, failed parent.ref (by simp)⟩
  | producerFailed known _ _ | producerCancelled known _ _ =>
      obtain ⟨owners, payload, known⟩ := known
      cases (known.unique parent_known).2.1

/-- Both R and C use the same one-error contribution without inventing a failure.
Witness: the singleton recorded task and its fixed error payload.
-/
private theorem shared_errors {ref} (owner : ref ∈ [root.ref, child.ref])
    : NodeErrors work [sharedTask] ref 1 := by
  refine ⟨fun _ => 1, ?_, rfl⟩
  intro occurrence member
  have same := List.mem_singleton.mp member
  subst occurrence
  exact ⟨_, _, _, shared_known, by simp [owner, Payload.failure]⟩

/-- Root-frontier notices use only the original healthy/outstanding-work branch.
Witness: the contributing unpublished task with empty failure evidence.
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

private theorem initialized : Initializes work [root, parent] [] := by
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨[], none, root_node, initial_eligible shared_known (by simp)⟩
  · exact ⟨[], none, parent_node, initial_eligible parent_known (by simp)⟩

/-- The retained failure was licensed by R before any output, not by unannounced C.
Witness: the failed reachable root task, open R, and empty prior failure list.
-/
private theorem failure_licensed
    : FailureWitness work initial matching events failures := by
  intro before cut occurrence after equal
  have sizes := congrArg List.length equal
  simp only [failures, List.length_append, List.length_cons, List.length_nil] at sizes
  have emptyBefore : before = [] := List.eq_nil_of_length_eq_zero (by omega)
  have emptyAfter : after = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst before
  subst after
  have same : (0, sharedTask) = (cut, occurrence) := by simpa [failures] using equal
  cases same
  refine ⟨by decide, by simp, ?_, by simp [TaskCancelled]⟩
  exact ⟨
    _,
    _,
    _,
    shared_known,
    rfl,
    .root ⟨_, _, shared_known⟩,
    root.ref,
    by simp,
    by decide
  ⟩

private theorem root_failure_allowed
    : EventAllowed work initial matching [] failures (.groupFailure root 1) := by
  refine ⟨⟨[], none, root_node⟩, by unfold Open; decide, ?_, shared_errors (by simp)⟩
  exact NodeFailed.task shared_known (by simp) (by simp [failures, failedBefore])

private theorem parent_value_allowed
    : EventAllowed work initial matching [.groupFailure root 1] failures
        (.groupValues parent
          [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }]) := by
  refine ⟨[parent.ref], none, { path := [], data, deliveryGroups := [parent] },
    rfl, parent_known, ?_, ?_⟩
  · refine ⟨?_, parent_uncancelled _, by simp, trivial⟩
    rintro ⟨index, event, selected, value, _⟩
    cases index with
    | zero => cases selected; exact value
    | succ index => simp at selected
  · have opened : OpenOwner work initial [.groupFailure root 1] [parent.ref] parent :=
      ⟨⟨.group, [], none, parent_node⟩, by simp, by unfold Open; decide⟩
    refine ⟨opened, ⟨parent, opened, parent_healthy _⟩, ?_⟩
    intro other available
    obtain ⟨kind, dependencies, producer, known⟩ := available.1
    rcases (node_cases known).2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

private theorem child_failure_allowed
    : EventAllowed work initial matching
        (beforeNotice ++ [.groupSuccess parent [child] []]) failures
        (.groupFailure child 1) := by
  refine ⟨
    ⟨[parent.ref], none, child_node⟩,
    by unfold Open; decide,
    ?_,
    shared_errors (by simp)
  ⟩
  exact NodeFailed.task shared_known (by simp) (by simp [failures, failedBefore])

/-- Every atom of the actual R/P/C output sequence is admitted under one coherent witness.
Witness: P supplies the sole publication; the shared R/C failure is recorded at cut zero.
-/
theorem atomic_explanation
    : Explains work [root, parent] [] events matching failures := by
  refine ⟨initialized, failure_licensed, ?_⟩
  intro index event selected
  match index with
  | 0 => cases selected; exact root_failure_allowed
  | 1 => cases selected; exact parent_value_allowed
  | 2 => cases selected; exact notice_allowed
  | 3 => cases selected; exact child_failure_allowed
  | index + 4 => simp [events, beforeNotice] at selected

/-- The completed trace accounts for both tasks and closes all three noticed groups.
Witness: the shared failure cancels its unpublished task; P publishes exactly once.
-/
private theorem terminal : Terminal work initial matching events failures := by
  constructor
  · intro occurrence owners producer payload known
    rcases task_cases known with rfl | rfl
    · apply Or.inl
      refine ⟨0, by simp [failures], by simp, ?_⟩
      apply Causality.TaskCancelled.owners ⟨_, _, shared_known⟩
        (by simp [Published]) (by simp)
      intro ref member
      exact Causality.NodeFailed.task ⟨_, _, shared_known⟩ member (by simp [failedBefore, failures])
    · exact Or.inr (parent_published.append _)
  · intro node kind dependencies producer known
    apply Or.inl
    rcases (node_cases known).2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- The actual reference runner's batching, including termination, satisfies admission.
Witness: the atomic explanation and terminal accounting, partitioned at the two inputs.
-/
theorem output_admitted
    : AdmissibleRun work
        ⟨
          [root, parent],
          [],
          ((State.initialize (Work.fromExecution work)).runNormalized
            [[failed], [succeeded]]).2
        ⟩ := by
  rw [output.2]
  refine ⟨events, matching, failures, atomic_explanation, terminal, ?_⟩
  exact .cons (batch := [.groupFailure root 1]) (by simp) (.separate _ .nil)
    (.cons
      (batch :=
        [
          .groupValues parent
            [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
          .groupSuccess parent [child] [],
          .groupFailure child 1,
          .workQueueTermination
        ])
      (by simp) (.separate _ (.separate _ (.separate _ (.separate _ .nil)))) .nil)

/-- Even a recorded child failure cannot bypass a failed ancestor.
Witness: the dependency-health guard is shared by both announcement alternatives.
-/
theorem failed_parent_blocks_notice (otherWork : Execution.Work)
    (observed : List Execution.WorkQueueEvent) (cuts : FailureCuts)
    (failedParent : NodeFailed otherWork matching observed cuts parent.ref)
    : ¬CanAnnounce otherWork initial matching observed cuts child .group [parent.ref]
        none := by
  intro notice
  exact canAnnounce_group_dependency_healthy notice (by simp) failedParent

-----------------------------------------------------------------------------------------
-- A failed parent still cancels the latent child
-----------------------------------------------------------------------------------------

private def cancellationWork : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] (.error 1) .empty)
      (.combine (.executionGroup [⟨parent, []⟩] [] (.error 1) .empty) .empty))

/-- The failed-parent variant also comes from execution, not an inconsistent raw outcome.
Witness: an independent failing non-null alias supplies P's error.
-/
theorem cancellation_generated : ExecutedWork cancellationWork := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required"] (some "R"),
      defer [field "required" [] [] (some "second"),
        defer [field "required"] (some "C")] (some "P")], ?_⟩
  cbv

/-- Recorded failures of both R/C and P still do not permit C's notice.
Witness: its own recorded failure satisfies the new branch, but failed P blocks release.
-/
theorem cancelled_child_rejected
    : let observed := [.groupFailure root 1, .groupFailure parent 1]
      let cuts := [(0, sharedTask), (1, parentTask)]
      HasRecordedFailure cancellationWork cuts observed.length child.ref
      ∧ ¬CanAnnounce cancellationWork initial matching observed cuts
          child .group [parent.ref] none := by
  have shared : TaskAt cancellationWork sharedTask [root.ref, child.ref] none
      (.object [] (.error 1)) :=
    ⟨[⟨root, []⟩, ⟨child, [parent]⟩], [], .error 1, .empty, [], rfl, rfl, rfl⟩
  have independent : TaskAt cancellationWork parentTask [parent.ref] none
      (.object [] (.error 1)) :=
    ⟨[⟨parent, []⟩], [], .error 1, .empty, [], rfl, rfl, rfl⟩
  constructor
  · exact ⟨sharedTask, [root.ref, child.ref], by simp [failedBefore],
      ⟨_, _, shared⟩, by simp⟩
  · apply failed_parent_blocks_notice
    exact NodeFailed.task independent (by simp) (by simp [failedBefore])

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedAnnouncement
