import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Success promotes healthy nested ancestors after an independent task failure. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerAncestorHealth
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def node (key : Nat) (label : String) : DeliveryNode :=
  { key, path := [], label := some (.string label) }

private def parent : DeliveryNode := node 0 "P"
private def child : DeliveryNode := node 1 "C"
private def grandchild : DeliveryNode := node 2 "G"
private def bad : DeliveryNode := node 3 "F"
private def parentTask : Occurrence := .executionGroup [1, 0]
private def childTask : Occurrence := .executionGroup [1, 1, 0]
private def failedTask : Occurrence := .executionGroup [1, 1, 1, 1, 0]
private def emptyChildren : Execution.Work := .combine .empty .empty

private def leaf (group : DeliveryNode) (ancestors : List DeliveryNode) (field : Name)
    : Execution.Work :=
  .executionGroup [⟨group, ancestors⟩] [] (.ok ([(field, .scalar field)], 0))
    emptyChildren

private def work : Execution.Work :=
  .combine .empty
    (.combine (leaf parent [] "a")
      (.combine (leaf child [parent] "b")
        (.combine (leaf grandchild [child, parent] "c")
          (.combine (.executionGroup [⟨bad, []⟩] [] (.error 1) .empty) .empty))))

private def result (group : DeliveryNode) (field : Name) (address : Address)
    : TaskResult :=
  {
    value := { deliveryGroups := [group], path := [], data := [(field, .scalar field)] },
    work := Work.fromExecution emptyChildren (address ++ [0])
  }

private def parentResult := result parent "a" [1, 0]
private def childResult := result child "b" [1, 1, 0]
private def failure : GraphEvent := .taskFailure failedTask 1
private def parentSuccess : GraphEvent := .taskSuccess parentTask parentResult
private def childSuccess : GraphEvent := .taskSuccess childTask childResult
private def initial : State := State.initialize (Work.fromExecution work)
private def afterFailure : State := (initial.runNormalized [[failure]]).1
private def afterParent : State := (initial.runNormalized [[failure], [parentSuccess]]).1

/-- The three-level defer chain and independent failure are produced by real execution.
Witness: evaluate the nested query; the grandchild has the nontrivial list [C, P]. -/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "a", defer [field "b", defer [field "c"] (some "G")] (some "C")]
      (some "P"), defer [field "required"] (some "F")], ?_⟩
  cbv

/-- Full ancestry is proved by the general execution witness, not assumed for this fixture.
Witness: generated work discharges the exact parent-chain proposition. -/
theorem ancestry_chains : GroupAncestryChains work := generated.groupAncestryChains

/-- The independent group's fixed result is the supplied failure.
Witness: direct structural navigation to its execution-group task. -/
private theorem failureKnown
    : TaskAt work failedTask [bad.key] none (.object [] (.error 1)) := by
  exact ⟨[⟨bad, []⟩], [], _, .empty, [], rfl, rfl, rfl⟩

/-- The parent's value and child-work lowering match the fixed task.
Witness: structural lookup and exact matching of the supplied host result. -/
private theorem parentMatches : parentSuccess.MatchesWork work := by
  refine ⟨[parent.key], none, ?_, ?_, ?_⟩
  · exact ⟨[⟨parent, []⟩], [], _, emptyChildren, [], rfl, rfl, rfl⟩
  · cbv
  · cbv

/-- The child's value likewise matches its fixed task and empty produced work.
Witness: structural lookup under the next combined execution partition. -/
private theorem childMatches : childSuccess.MatchesWork work := by
  refine ⟨[child.key], none, ?_, ?_, ?_⟩
  · exact ⟨[⟨child, [parent]⟩], [], _, emptyChildren, [], rfl, rfl, rfl⟩
  · cbv
  · cbv

/-- The failure followed by both successes obeys the existing smaller source semantics.
Witness: exact results, distinct task occurrences, and root producer readiness. -/
theorem inputs_valid : ValidGraphEvents work [failure, parentSuccess, childSuccess] := by
  have failed : ValidGraphEvents work [failure] := .append .nil ⟨_, _, [], failureKnown⟩
    (by simp [failure, GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, failureKnown, by intro source impossible; cases impossible⟩
  have parentReady : parentSuccess.Ready work [failure] := by
    refine ⟨[parent.key], none, .object [] (.ok ([("a", .scalar "a")], 0)), ?_,
      by intro source impossible; cases impossible⟩
    exact ⟨[⟨parent, []⟩], [], _, emptyChildren, [], rfl, rfl, rfl⟩
  have first : ValidGraphEvents work [failure, parentSuccess] := .append failed parentMatches
    (by simp [failure, parentSuccess, failedTask, parentTask, GraphEvent.Fresh,
      GraphEvent.identities]) parentReady
  apply ValidGraphEvents.append first childMatches
  · simp [failure, parentSuccess, childSuccess, failedTask, parentTask, childTask,
      GraphEvent.Fresh, GraphEvent.identities]
  · refine ⟨[child.key], none, .object [] (.ok ([("b", .scalar "b")], 0)), ?_,
      by intro source impossible; cases impossible⟩
    exact ⟨[⟨child, [parent]⟩], [], _, emptyChildren, [], rfl, rfl, rfl⟩

/-- The queue starts each latent descendant before its corresponding settlement.
Witness: evaluate the unchanged input-start checker through both nested promotions. -/
theorem inputs_started
    : inputsStarted work [[failure], [parentSuccess], [childSuccess]] = true := by
  cbv

/-- Only the parent and independent failing group are initially announced.
Witness: their dependency-free descriptors satisfy the unchanged initialization law. -/
theorem initialized : Initializes work initial.initialGroups initial.initialStreams := by
  have parentKnown : NodeAt work parent .group [] none := by
    exact ⟨[1, 0], [⟨parent, []⟩], [], _, emptyChildren, [], ⟨parent, []⟩,
      rfl, by simp, rfl, rfl⟩
  have badKnown : NodeAt work bad .group [] none := by
    exact ⟨[1, 1, 1, 1, 0], [⟨bad, []⟩], [], .error 1, .empty, [], ⟨bad, []⟩,
      rfl, by simp, rfl, rfl⟩
  have eligible (group : DeliveryNode) (known : NodeAt work group .group [] none)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] group .group [] none := by
    exact ⟨by simp [announcedKeys, pendingKeys], Or.inl ⟨fun failure => failure.nonempty rfl,
        Or.inr (group_not_initially_accounted known)⟩, by simp, by simp⟩
  have notices : initial.initialGroups = [parent, bad] ∧ initial.initialStreams = [] := by
    cbv
  rw [notices.1, notices.2]
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro group member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨[], none, parentKnown, eligible _ parentKnown⟩
  · exact ⟨[], none, badKnown, eligible _ badKnown⟩

private def childNode : GroupNode :=
  {
    group := ⟨child, some parent.key⟩,
    tasks := [childTask],
    pending := 1,
    childGroups := [grandchild.key]
  }

private def grandchildNode : GroupNode :=
  {
    group := ⟨grandchild, some child.key⟩,
    tasks := [.executionGroup [1, 1, 1, 0]],
    pending := 1
  }

/-- The promoted child retains the completed parent's full-ancestry descriptor.
Witness: its original execution-group occurrence in the generated work. -/
private theorem childKnown : NodeAt work child .group [parent.key] none := by
  exact ⟨
    [1, 1, 0],
    [⟨child, [parent]⟩],
    [],
    _,
    emptyChildren,
    [],
    ⟨child, [parent]⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

/-- The grandchild records both ancestors even after the parent has completed.
Witness: structural navigation to the final successful nested partition. -/
private theorem grandchildKnown
    : NodeAt work grandchild .group [child.key, parent.key] none := by
  exact ⟨
    [1, 1, 1, 0],
    [⟨grandchild, [child, parent]⟩],
    [],
    _,
    emptyChildren,
    [],
    ⟨grandchild, [child, parent]⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

/-- The unrelated failure cannot invalidate a group or any of its recorded ancestors.
Witness: generated invalidation has one failed contributor; descriptor uniqueness fixes
that contributor to F, which is excluded by the supplied dependency-key check.
-/
private theorem independent_healthy {group dependencies producer}
    (known : NodeAt work group .group dependencies producer)
    (apart : bad.key ∉ group.key :: dependencies)
    : ¬GroupInvalidated work [failedTask] group.key := by
  intro failure
  obtain ⟨occurrence, owners, owner, task, member, contributes, related⟩ :=
    (generated.groupInvalidated_iff known).mp failure
  have same := List.mem_singleton.mp member
  subst occurrence
  obtain ⟨birth, payload, taskKnown⟩ := task
  have ownersEq := (taskKnown.unique failureKnown).1
  rw [ownersEq] at contributes
  exact apart ((List.mem_singleton.mp contributes) ▸ related)

/-- Success activates each next nested group while keeping the earlier failure independent.
Witness: exact active-root lists and each promoted group's full dependency descriptor.
-/
theorem promoted_roots
    : afterParent.rootGroups = [child.key]
      ∧ (afterParent.taskSuccess childTask childResult).1.rootGroups
        = [grandchild.key] := by
  constructor <;> cbv

/-- The first promoted root is healthy after the independent failure.
Witness: the child descriptor excludes F from both ownership and ancestry.
-/
theorem first_promotion_healthy : afterParent.RootGroupsHealthy work [failedTask] := by
  intro key member
  have same := List.mem_singleton.mp (promoted_roots.1 ▸ member)
  subst key
  exact independent_healthy childKnown (by decide)

/-- The second promoted root retains the same health guarantee through both ancestors.
Witness: the grandchild descriptor and the nonempty evaluated root frontier.
-/
theorem second_promotion_healthy
    : (afterParent.taskSuccess childTask childResult).1.RootGroupsHealthy
        work [failedTask] := by
  intro key member
  have same := List.mem_singleton.mp (promoted_roots.2 ▸ member)
  subst key
  exact independent_healthy grandchildKnown (by decide)

/-- The active child has retired task-bearing ancestors according to current replay.
Witness: project the joint owner/ancestry invariant, then select the actual active child.
-/
theorem promoted_child_ancestors_retired
    : afterParent.AncestorsRetired work child.key := by
  obtain ⟨_, _, ledger⟩ := generated.runNormalized_ownerAncestry
    [[failure], [parentSuccess]] (inputs_valid.prefix ⟨[childSuccess], rfl⟩) (by cbv)
  exact ledger.roots child.key
    (by
      change child.key ∈ afterParent.rootGroups
      rw [promoted_roots.1]
      simp)

/-- Split and joined inputs preserve the same full owner/retirement invariant.
Witness: unrestricted replay, with the actual host checker for each batching.
-/
theorem successive_promotions_accounted
    : ∀ batches ∈
        [
          [[failure], [parentSuccess], [childSuccess]],
          [[failure, parentSuccess, childSuccess]]
        ],
        ∃ parents,
          (initial.runNormalized batches).1.OwnerAncestry
            work parents batches.flatten := by
  intro batches member
  have shapes : batches = [[failure], [parentSuccess], [childSuccess]] ∨
      batches = [[failure, parentSuccess, childSuccess]] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  have valid : ValidGraphEvents work batches.flatten := by
    rcases shapes with rfl | rfl <;> exact inputs_valid
  have started : inputsStarted work batches = true := by
    rcases shapes with rfl | rfl <;> cbv
  obtain ⟨parents, _, ledger⟩ :=
    generated.runNormalized_ownerAncestry batches valid started
  exact ⟨parents, ledger⟩

/-- Both task-bearing ancestors are permanently retired after the two promotions.
Witness: current replay's root certificate, not an invariant requiring every registry
record to own a task. The grandchild's original record identifies both ancestors.
-/
theorem grandchild_ancestors_retired
    : ∀ batches ∈
        [
          [[failure], [parentSuccess], [childSuccess]],
          [[failure, parentSuccess, childSuccess]]
        ],
        (initial.runNormalized batches).1.RetiredGroup child.key
        ∧ (initial.runNormalized batches).1.RetiredGroup parent.key := by
  intro batches member
  obtain ⟨parents, ledger⟩ := successive_promotions_accounted batches member
  have roots : (initial.runNormalized batches).1.rootGroups = [grandchild.key] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cbv
  have chain := ledger.roots grandchild.key (by rw [roots]; simp)
  have childOwners : TaskHasOwners work childTask [child.key] :=
    ⟨none, _, ⟨[⟨child, [parent]⟩], [], _, emptyChildren, [], rfl, rfl, rfl⟩⟩
  have parentOwners : TaskHasOwners work parentTask [parent.key] :=
    ⟨none, _, ⟨[⟨parent, []⟩], [], _, emptyChildren, [], rfl, rfl, rfl⟩⟩
  have record := groupRecordAt_of_nodeAt grandchildKnown
  exact ⟨
    chain grandchild _ record rfl child.key (by simp) _ _ childOwners (by simp),
    chain grandchild _ record rfl parent.key (by simp) _ _ parentOwners (by simp)
  ⟩

/-- Completion removes the old parent but retains the child-to-grandchild live suffix.
Witness: concrete lookups and permanent registration after the checked source prefix.
-/
theorem completed_parent_retired
    : afterParent.RetiredGroup parent.key
      ∧ afterParent.groupNode? child.key = some childNode
      ∧ afterParent.groupNode? grandchild.key = some grandchildNode := by
  constructor
  · cbv
    change (0 ∈ ([0, 1, 2, 3] : List Nat)) ∧ 0 ∉ ([1, 2] : List Nat)
    decide
  · constructor <;> cbv

/-- A missing completed parent is compatible with a genuinely healthy live child.
Witness: checked retirement and independent-failure health, stated directly over lookups.
-/
theorem healthy_child_has_completed_gap
    : afterParent.groupNode? parent.key = none
      ∧ afterParent.groupNode? child.key = some childNode
      ∧ ¬GroupInvalidated work [failedTask] child.key :=
  ⟨
    completed_parent_retired.1.lookup_none,
    completed_parent_retired.2.1,
    independent_healthy childKnown (by decide)
  ⟩

/-- The remaining live suffix is connected despite the older completed-parent gap.
Witness: the stored child link and both concrete live endpoints.
-/
theorem live_suffix_connected : afterParent.LiveDescendant child.key grandchild.key :=
  .child completed_parent_retired.2.1 (by simp [childNode])
    (.self completed_parent_retired.2.2)

-----------------------------------------------------------------------------------------
-- The independent failure can instead arrive after successful promotion
-----------------------------------------------------------------------------------------

private def afterParentOnly : State := (initial.runNormalized [[parentSuccess]]).1
private def afterLaterFailure : State := (afterParentOnly.taskFailure failedTask 1).1

/-- The same independent failure can settle after the successful parent instead.
Witness: fixed outcomes and distinct identities in the reversed legal host order. -/
theorem later_failure_inputs_valid : ValidGraphEvents work [parentSuccess, failure] := by
  have first : ValidGraphEvents work [parentSuccess] := .append .nil parentMatches
    (by simp [GraphEvent.Fresh, GraphEvent.identities, parentSuccess])
    ⟨[parent.key], none, .object [] (.ok ([("a", .scalar "a")], 0)),
      ⟨[⟨parent, []⟩], [], _, emptyChildren, [], rfl, rfl, rfl⟩,
      by intro source impossible; cases impossible⟩
  exact .append first ⟨_, _, [], failureKnown⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, failure, parentSuccess, failedTask,
      parentTask])
    ⟨_, _, _, failureKnown, by intro source impossible; cases impossible⟩

/-- Both reordered events settle tasks that the actual queue has started.
Witness: evaluate the public start checker, including the post-promotion boundary. -/
theorem later_failure_inputs_started
    : inputsStarted work [[parentSuccess], [failure]] = true := by cbv

/-- Reversing the failure and parent success still preserves joint accounting.
Witness: current replay accounting for the alternate valid, actually started input.
-/
theorem later_failure_replay_accounted
    : ∃ parents,
        (initial.runNormalized [[parentSuccess], [failure]]).1.OwnerAncestry
          work parents [parentSuccess, failure] := by
  obtain ⟨parents, _, ledger⟩ := generated.runNormalized_ownerAncestry
    [[parentSuccess], [failure]] later_failure_inputs_valid later_failure_inputs_started
  exact ⟨parents, ledger⟩

/-- The later independent failure leaves a nonempty healthy child frontier.
Witness: exact active-root membership and the same structural independence proof.
-/
theorem later_failure_rootsHealthy
    : afterLaterFailure.RootGroupsHealthy work [failedTask]
      ∧ afterLaterFailure.rootGroups = [child.key] := by
  have roots : afterLaterFailure.rootGroups = [child.key] := by cbv
  refine ⟨?_, roots⟩
  intro key active
  have same := List.mem_singleton.mp (roots ▸ active)
  subst key
  exact independent_healthy childKnown (by decide)

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerAncestorHealth
