import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ClosingFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentHealth
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionReplay
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Root ancestry stays healthy while dormant task rejections await normal release. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerClosingHealth
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : DeliveryNode := ⟨0, [], some (.string "R")⟩
private def parent : DeliveryNode := ⟨1, [], some (.string "P")⟩
private def child : DeliveryNode := ⟨2, [], some (.string "C")⟩
private def nested : DeliveryNode := ⟨3, [], some (.string "D")⟩
private def firstTask : Occurrence := .executionGroup [1, 0]
private def secondTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]

private def work : Execution.Work :=
  .combine .empty
    (.declareGroups
      [⟨root, []⟩, ⟨parent, []⟩, ⟨child, [parent]⟩, ⟨nested, [child, parent]⟩]
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] []
          ({ result := .error 1, cause := some 1 }) .empty)
        (.combine
          (.executionGroup [⟨root, []⟩, ⟨nested, [child, parent]⟩] []
            ({ result := .error 1, cause := some 1 }) .empty)
          (.combine
            (.executionGroup [⟨parent, []⟩] []
              ({ result := .ok ([("a", .scalar "a")], 0) }) (.combine .empty .empty))
            .empty))))

private def first : GraphEvent := .taskFailure firstTask 1
private def second : GraphEvent := .taskFailure secondTask 1
private def inputs : List (List GraphEvent) := [[first], [second]]
private def initial : State := State.initialize (Work.fromExecution work)

/-- Execution generates two shared failures and an independent successful parent task.
Witness: the second latent owner D is a child of the first failure's owner C. -/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first"),
      field "required" [] [] (some "second")] (some "R"),
      defer [field "a", defer [field "required" [] [] (some "first"),
        defer [field "required" [] [] (some "second")] (some "D")] (some "C")]
        (some "P")], ?_⟩
  cbv

private theorem first_known
    : TaskAt work firstTask [root.ref, child.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem second_known
    : TaskAt work secondTask [root.ref, nested.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

/-- Both host failures are fresh, match pure outcomes, and were requested by the queue.
Witness: root producer readiness plus the source append rules and start checker. -/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, _, first_known⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, first_known, by intro source impossible; cases impossible⟩
  exact ⟨
    .append one ⟨_, _, _, second_known⟩
      (by
        simp [first, second, firstTask, secondTask, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, second_known, by intro source impossible; cases impossible⟩,
    by cbv
  ⟩

/-- The concrete initial R/P notices satisfy the independent initialization relation.
Witness: both generated contributors have no ancestor or producer dependencies. -/
theorem initialized : Initializes work initial.initialGroups initial.initialStreams := by
  have rootKnown : NodeAt work root .group [] none := by
    refine ⟨[1, 0], [⟨root, []⟩, ⟨child, [parent]⟩], [],
      { result := .error 1, cause := some 1 }, .empty, [],
      ⟨root, []⟩, ?_, by simp, rfl, rfl⟩
    cbv
  have parentKnown : NodeAt work parent .group [] none := by
    refine ⟨[1, 1, 1, 0], [⟨parent, []⟩], [], { result := .ok ([("a", .scalar "a")], 0) },
      .combine .empty .empty, [], ⟨parent, []⟩, ?_, by simp, rfl, rfl⟩
    cbv
  have eligible (group : DeliveryNode) (known : NodeAt work group .group [] none)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] group .group [] none :=
    ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨fun failure => failure.nonempty rfl,
        Or.inr (group_not_initially_accounted known)⟩, by simp, by simp⟩
  have notices : initial.initialGroups = [root, parent] ∧ initial.initialStreams = [] := by
    cbv
  rw [notices.1, notices.2]
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro group member
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨[], none, rootKnown, eligible _ rootKnown⟩
  · have same := List.mem_singleton.mp tail
    subst group
    exact ⟨[], none, parentKnown, eligible _ parentKnown⟩

/-- The presence check accepts the late rejection and retains both source tokens.
The independent parent remains the sole active root. -/
theorem accepted_inventory
    : let before := (initial.handleGraphEvent first).1
      before.taskNode? secondTask = some { task := ⟨secondTask, [root, nested]⟩ }
      ∧ (before.taskNode? secondTask).map TaskNode.rejection = some none
      ∧ initial.objectFailureContributions inputs.flatten = [secondTask, firstTask]
      ∧ (initial.runNormalized inputs).1.rootGroups = [parent.ref]
      ∧ (initial.runNormalized inputs).2 = [[.groupFailure root 1]] := by
  cbv

/-- A nonempty surviving frontier is healthy under the exact accepted-failure inventory.
Witness: the general normalized closing-replay theorem, not evaluation of root health. -/
theorem surviving_root_health
    : (initial.runNormalized inputs).1.RootGroupsHealthy work
        [secondTask, firstTask] := by
  have healthy := createWorkQueue_runNormalized_rootsHealthy_closingContributions generated
    initialized inputs source_valid.1 source_valid.2 (by
      intro event member
      simp only [inputs, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> trivial)
  change (initial.runNormalized inputs).1.RootGroupsHealthy work
    (initial.admittedObjectFailureContributionsForBatches inputs) at healthy
  have counted : initial.admittedObjectFailureContributionsForBatches inputs
      = [secondTask, firstTask] := by cbv
  rw [counted] at healthy
  exact healthy

-----------------------------------------------------------------------------------------
-- A failed child may be released with healthy ancestry, then drained immediately
-----------------------------------------------------------------------------------------

private def parentResult : TaskResult :=
  {
    value :=
      {
        path := [], data := [("a", .scalar "a")], errors := 0, deliveryGroups := [parent]
      },
    work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
  }

private def parentNode : GroupNode :=
  {
    group := ⟨parent, none⟩,
    tasks := [parentTask],
    pending := 1,
    childGroups := [child.ref]
  }

/-- The actual parent's pre-closure state: its value is stored and its count decremented. -/
private def ready : State :=
  ((initial.replayGraphEvents [first]).putTaskNode
    { task := ⟨parentTask, [parent]⟩, value := some parentResult.value }).putGroupNode
    { parentNode with pending := 0 }

/-- Releasing cached-failed C preserves healthy ancestry, without claiming C is healthy.
Witness: exact replay error counts and the general success/pruning theorem. The ready
state stores P's value and decrements its counter; its full drain agrees with the actual
task-success handler, including C's failure after its pending notice carrier.
-/
theorem failed_child_release_health
    : let closed := ready.finishGroupSuccess { parentNode with pending := 0 }
      closed.1.MissingParentAncestorsHealthy work [firstTask]
      ∧ GroupAncestorsHealthy work [firstTask] child.ref
      ∧ GroupRecordInvalidated work [firstTask] child.ref
      ∧ ready.drainReadyGroups.1.MissingParentAncestorsHealthy work [firstTask]
      ∧ ready.drainReadyGroups
        = (initial.replayGraphEvents [first]).taskSuccess parentTask parentResult := by
  have valid : ValidGraphEvents work [first] := source_valid.1.prefix ⟨[second], rfl⟩
  obtain ⟨parents, canonical, ledger⟩ := generated.replayGraphEvents_ownerAccounting_of_started
    [first] valid (by cbv)
  have parentMember : parentNode ∈ (initial.replayGraphEvents [first]).groupNodes := by
    cbv; exact List.mem_cons_self
  have beforeCounts := (createWorkQueue_retainedFailures
    (Work.fromExecution work) work).replayGraphEvents
    (before := []) (available := []) (createWorkQueue_pendingAccounting work generated.declarations) generated
    (by intro occurrence member; cases member) [first] valid (by cbv)
  change (initial.replayGraphEvents [first]).RetainedFailures work [firstTask] at beforeCounts
  have storedCounts := beforeCounts.putTaskNode
    (occurrence := parentTask) (old := { task := ⟨parentTask, [parent]⟩ }) (by cbv)
    { task := ⟨parentTask, [parent]⟩, value := some parentResult.value } rfl (by simp)
  have readyCounts : ready.RetainedFailures work [firstTask] :=
    storedCounts.putGroupNodeSameTasks (by cbv; decide) parentNode
      (by cbv; exact List.mem_cons_self) { parentNode with pending := 0 } rfl rfl
  have readyMatching : ready.GroupNodesMatchWork work :=
    ledger.groups.putGroupNode _ (ledger.groups parentNode parentMember)
  have readyLinks : ready.ChildLinksCanonical parents :=
    ledger.childLinks.putGroupNode _ (ledger.childLinks parentNode parentMember)
  have readyFields : ready.GroupParentsCanonical parents :=
    ledger.canonical.putGroupNode _ (ledger.canonical parentNode parentMember)
  have missing : ready.MissingParentAncestorsHealthy work [firstTask] := by
    apply State.MissingParentAncestorsHealthy.of_presentParents
    intro node member ref parentEq
    have nodes : ready.groupNodes =
        [{ parentNode with pending := 0 },
          { group := ⟨child, some parent.ref⟩, tasks := [firstTask], pending := 1,
            childGroups := [nested.ref] },
          { group := ⟨nested, some child.ref⟩, tasks := [secondTask], pending := 1 }] := by cbv
    rw [nodes] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases parentEq
    · cases Option.some.inj parentEq; cbv
    · cases Option.some.inj parentEq; cbv
  have parentRecord : GroupRecordAt work parent [] :=
    groupRecordAt_of_nodeAt
      (show NodeAt work parent .group [] none from
        ⟨[1, 1, 1, 0], _, [], { result := .ok ([("a", .scalar "a")], 0) },
          .combine .empty .empty, [], ⟨parent, []⟩,
          rfl, List.mem_cons_self, rfl, rfl⟩)
  have ancestors : GroupAncestorsHealthy work [firstTask] parent.ref :=
    GroupAncestorsHealthy.of_record generated parentRecord (by simp)
  have failedKnown : ∀ occurrence ∈ [firstTask],
      ∃ owners producer payload,
        TaskAt work occurrence owners producer payload ∧ payload.failure.isSome = true := by
    intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, _, _, first_known, rfl⟩
  have member : { parentNode with pending := 0 } ∈ ready.groupNodes := by
    cbv; exact List.mem_cons_self
  have closed := missing.finishGroupSuccess generated readyMatching readyLinks readyFields
    canonical readyCounts failedKnown member (by simp [parentNode, firstTask, parentTask]) ancestors
  have childReleased : child ∈
      (ready.finishGroupSuccess { parentNode with pending := 0 }).2.2.newGroups := by
    cbv; exact List.mem_cons_self
  have roots : ready.RootAncestorsHealthy work [firstTask] := by
    intro ref member
    have refs : ready.rootGroups = [parent.ref] := by cbv
    rw [refs] at member
    exact (List.mem_singleton.mp member) ▸ ancestors
  exact ⟨
    closed.1,
    closed.2 child childReleased,
    .task ⟨none, _, first_known⟩ (by simp) List.mem_cons_self,
    (missing.drainReadyGroups generated readyMatching readyLinks readyFields canonical
      readyCounts failedKnown roots
      (ledger.pending.sound.putGroupNode { parentNode with pending := 0 }
        (fun occurrence listed =>
          ledger.pending.sound parentNode parentMember occurrence listed))
      ledger.pending.matching
      (settled := [parentTask])
      (by
        intro node member _
        have nodes : ready.groupNodes =
            [{ parentNode with pending := 0 },
              { group := ⟨child, some parent.ref⟩, tasks := [firstTask], pending := 1,
                childGroups := [nested.ref] },
              { group := ⟨nested, some child.ref⟩, tasks := [secondTask], pending := 1 }] := by cbv
        rw [nodes] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;>
          simp [unsettledCount, parentNode, parentTask, firstTask, secondTask])
      (by simp [parentTask, firstTask])).1,
    by cbv
  ⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerClosingHealth
