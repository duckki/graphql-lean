import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Cancelled groups stay retired when generated shared work integrates later children. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerReactivation
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A generated nested-defer query with two shared object fields
-----------------------------------------------------------------------------------------

private def selections : List Selection :=
  [
    defer
      [
        field "a",
        defer
          [
            field "required",
            field "user" [field "name"] [] (some "u1"),
            field "user" [field "name"] [] (some "u2")
          ]
          (some "C")
      ]
      (some "P"),
    defer
      [
        field "user" [field "age"] [] (some "u1"),
        field "user" [field "age"] [] (some "u2")
      ]
      (some "R"),
    defer [field "required"] (some "S")
  ]

private def node (key : Nat) (label : String) : DeliveryNode :=
  { key, path := [], label := some (.string label) }

private def parent : DeliveryNode := node 0 "P"
private def child : DeliveryNode := node 1 "C"
private def survivor : DeliveryNode := node 2 "R"
private def failureOwner : DeliveryNode := node 3 "S"
private def childFragment : DeferredFragment := ⟨child, [parent]⟩

private def parentTask : Occurrence := .executionGroup [1, 0]
private def failedTask : Occurrence := .executionGroup [1, 1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 1, 0]

private def leaf (group : DeferredFragment) (alias name value : String)
    : Execution.Work :=
  .executionGroup [group] [.field alias] (.ok ([(name, .scalar value)], 0))
    (.combine .empty .empty)

private def objectChildren (alias : String) : Execution.Work :=
  .combine .empty
    (.combine (leaf childFragment alias "name" "name1")
      (.combine (leaf ⟨survivor, []⟩ alias "age" "1") .empty))

private def sharedChildren : Execution.Work :=
  .combine (objectChildren "u1") (.combine (objectChildren "u2") .empty)

private def sharedData : List (Name × ResponseValue) :=
  [("u1", .object []), ("u2", .object [])]

/-- The explicit finite tree makes structural witnesses small; `generated` below
checks it against the actual query executor rather than assuming this shape.
-/
private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨parent, []⟩] [] (.ok ([("a", .scalar "a")], 0))
        (.combine .empty .empty))
      (.combine
        (.executionGroup [childFragment, ⟨failureOwner, []⟩] [] (.error 1) .empty)
        (.combine
          (.executionGroup [childFragment, ⟨survivor, []⟩] [] (.ok (sharedData, 0))
            sharedChildren)
          .empty)))

/-- This is execution-generated work for pure finite resolvers, not an arbitrary tree.
Witness: evaluate the displayed query against the shared schema and resolver fixture.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0, selections, ?_⟩
  cbv

/-- P's own field completes successfully. Witness: its fixed generated task location. -/
private theorem parent_known
    : TaskAt work parentTask [parent.key] none
        (.object [] (.ok ([("a", .scalar "a")], 0))) := by
  refine ⟨[⟨parent, []⟩], [], _, .combine .empty .empty, [], ?_, rfl, rfl⟩
  cbv

/-- C and S share the non-null failure. Witness: its fixed generated task location. -/
private theorem failure_known
    : TaskAt work failedTask [child.key, failureOwner.key] none
        (.object [] (.error 1)) := by
  refine ⟨[childFragment, ⟨failureOwner, []⟩], [], _, .empty, [], ?_, rfl, rfl⟩
  cbv

/-- C and R share both object fields. Witness: their generated task and child work. -/
private theorem shared_known
    : TaskAt work sharedTask [child.key, survivor.key] none
        (.object [] (.ok (sharedData, 0))) := by
  refine ⟨[childFragment, ⟨survivor, []⟩], [], _, sharedChildren, [], ?_, rfl, rfl⟩
  cbv

-----------------------------------------------------------------------------------------
-- All supplied inputs obey the existing host contract
-----------------------------------------------------------------------------------------

private def failure : GraphEvent := .taskFailure failedTask 1

private def sharedSuccess : GraphEvent :=
  .taskSuccess sharedTask
    {
      value := { deliveryGroups := [child, survivor], path := [], data := sharedData },
      work := Work.fromExecution sharedChildren [1, 1, 1, 0, 0]
    }

private def parentSuccess : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data := [("a", .scalar "a")] },
      work := Work.fromExecution (.combine .empty .empty) [1, 0, 0]
    }

private def batches : List (List GraphEvent) :=
  [[failure], [sharedSuccess], [parentSuccess]]

private def initial : State := State.initialize (Work.fromExecution work)

private def beforeRelease : State :=
  (initial.runNormalized [[failure], [sharedSuccess]]).1

private def finalState : State := (initial.runNormalized batches).1

/-- Fixed outcomes, exact child work, freshness, and producer order all hold.
Witness: three append rules; every supplied task has no structural producer.
-/
theorem inputs_valid : ValidGraphEvents work batches.flatten := by
  have first : ValidGraphEvents work [failure] :=
    .append .nil ⟨_, _, [], failure_known⟩ (by
      simp [failure, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, failure_known, by intro source impossible; cases impossible⟩
  have second : ValidGraphEvents work [failure, sharedSuccess] :=
    .append first ⟨_, _, shared_known, by cbv, by cbv⟩ (by
      simp [failure, sharedSuccess, GraphEvent.Fresh, GraphEvent.identities,
        failedTask, sharedTask])
      ⟨_, _, _, shared_known, by intro source impossible; cases impossible⟩
  exact .append second ⟨_, _, parent_known, by cbv, by cbv⟩
    (by
      simp [failure, sharedSuccess, parentSuccess, GraphEvent.Fresh, GraphEvent.identities,
        failedTask, sharedTask, parentTask])
    ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩

/-- Every event settles an actually started task before queue termination.
Witness: evaluate the public start-discipline checker on the same input batches.
-/
theorem inputs_started : inputsStarted work batches = true := by cbv

/-- Initial notices are legal: P, S, and R are root-produced groups without dependencies.
Witness: their actual work descriptors and empty-history announcement eligibility.
-/
theorem initialized : Initializes work initial.initialGroups initial.initialStreams := by
  have parentKnown : NodeAt work parent .group [] none := by
    refine ⟨[1, 0], [⟨parent, []⟩], [], .ok ([("a", .scalar "a")], 0),
      .combine .empty .empty, [],
      ⟨parent, []⟩, ?_, by simp, rfl, rfl⟩
    cbv
  have failureKnown : NodeAt work failureOwner .group [] none := by
    refine ⟨[1, 1, 0], [childFragment, ⟨failureOwner, []⟩], [], .error 1, .empty, [],
      ⟨failureOwner, []⟩, ?_, by simp, rfl, rfl⟩
    cbv
  have survivorKnown : NodeAt work survivor .group [] none := by
    refine ⟨[1, 1, 1, 0], [childFragment, ⟨survivor, []⟩], [],
      .ok (sharedData, 0), sharedChildren, [],
      ⟨survivor, []⟩, ?_, by simp, rfl, rfl⟩
    cbv
  have eligible (group : DeliveryNode) (known : NodeAt work group .group [] none)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] group .group [] none :=
    ⟨by simp [announcedKeys, pendingKeys], Or.inl ⟨fun failure => failure.nonempty rfl,
        Or.inr (group_not_initially_accounted known)⟩, by simp, by simp⟩
  have notices : initial.initialGroups = [parent, failureOwner, survivor]
      ∧ initial.initialStreams = [] := by cbv
  rw [notices.1, notices.2]
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro group member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨[], none, parentKnown, eligible _ parentKnown⟩
  · exact ⟨[], none, failureKnown, eligible _ failureKnown⟩
  · exact ⟨[], none, survivorKnown, eligible _ survivorKnown⟩

-----------------------------------------------------------------------------------------
-- Reintegration retains cancellation and releases only surviving work
-----------------------------------------------------------------------------------------

/-- A latent failed child stays cached until P releases it, then is removed.
Witness: both prefix lookups retain the error, while completed release removes the node.
-/
theorem child_retained_until_release
    : ((initial.runNormalized [[failure]]).1.groupNode? child.key).map GroupNode.failure
        = some (some 1)
      ∧ (beforeRelease.groupNode? child.key).map GroupNode.failure = some (some 1)
      ∧ finalState.groupNode? child.key = none := by
  constructor
  · cbv
  · constructor <;> cbv

/-- Once normally announced and completed, the child's key cannot be recreated.
Witness: its actual permanent retirement and unrestricted replay preservation.
-/
theorem child_never_recreated (future : List (List GraphEvent))
    : (finalState.runNormalized future).1.groupNode? child.key = none := by
  have retired : finalState.RetiredGroup child.key :=
    State.RetiredGroup.of_lookup_none (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self) child_retained_until_release.2.2
  exact retired.never_recreated future

/-- An empty group pruned during initialization also cannot be recreated later.
Witness: the permanent registration key and unrestricted retirement preservation.
-/
theorem pruned_group_never_recreated (future : List (List GraphEvent))
    : ((State.initialize { groups := [⟨child, none⟩] }).runNormalized future).1.groupNode?
        child.key
      = none := by
  have retired : (State.initialize { groups := [⟨child, none⟩] }).RetiredGroup child.key := by
    constructor
    · change 1 ∈ [1]
      decide
    · change 1 ∉ ([] : List Nat)
      decide
  exact retired.never_recreated future

/-- Shared success preserves the surviving contributor's two child tasks.
Witness: the nonzero live pending count and the final active root.
-/
theorem surviving_children_registered
    : (beforeRelease.groupNode? survivor.key).map GroupNode.pending = some 2
      ∧ finalState.rootGroups = [survivor.key] := by
  constructor <;> cbv

/-- Normal parent release announces the failed child and reports its cached error.
Witness: evaluate the same generated three-event history, including its silent middle batch.
-/
theorem normalized_output
    : (initial.runNormalized batches).2
      = [
        [.groupFailure failureOwner 1],
        [
          .groupValues parent
            [{ path := [], data := [("a", .scalar "a")], deliveryGroups := [parent] }],
          .groupSuccess parent [child] [],
          .groupFailure child 1
        ]
      ] := by
  cbv

/-- Registration is supported by tasks or their ancestors, not necessarily direct ownership.
Witness: the current generic registration-provenance theorem on the valid replay.
-/
theorem registrations_supported
    : finalState.RegistrationsSupportedBy (Task.SupportsGroup work) :=
  createWorkQueue_runNormalized_registrationsSupported inputs_valid

/-- The shared failure/success sequence preserves healthy owners and ancestry.
Witness: current joint replay accounting, without any extra integration-availability law.
-/
theorem replay_accounted
    : ∃ parents, finalState.OwnerAncestry work parents batches.flatten := by
  obtain ⟨parents, _, ledger⟩ :=
    generated.runNormalized_ownerAncestry batches inputs_valid inputs_started
  exact ⟨parents, ledger⟩

private def releaseBeforeFailure : List (List GraphEvent) :=
  [[parentSuccess, failure], [sharedSuccess]]

/-- Parent success may precede the shared failure while preserving the host contract.
Witness: fixed matching outcomes, fresh producer-free tasks, and the executable checker.
-/
theorem release_before_failure_valid
    : ValidGraphEvents work releaseBeforeFailure.flatten
      ∧ inputsStarted work releaseBeforeFailure = true := by
  have first : ValidGraphEvents work [parentSuccess] :=
    .append .nil ⟨_, _, parent_known, by cbv, by cbv⟩
      (by simp [parentSuccess, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩
  have second : ValidGraphEvents work [parentSuccess, failure] :=
    .append first ⟨_, _, [], failure_known⟩
      (by simp [parentSuccess, failure, GraphEvent.Fresh, GraphEvent.identities,
        parentTask, failedTask])
      ⟨_, _, _, failure_known, by intro source impossible; cases impossible⟩
  constructor
  · exact .append second ⟨_, _, shared_known, by cbv, by cbv⟩
      (by simp [parentSuccess, failure, sharedSuccess, GraphEvent.Fresh, GraphEvent.identities,
        parentTask, failedTask, sharedTask])
      ⟨_, _, _, shared_known, by intro source impossible; cases impossible⟩
  · cbv

/-- Reversing parent release and failure preserves the same internal accounting.
Witness: the unrestricted joint replay theorem with the alternate checked source order.
-/
theorem release_before_failure_accounted
    : ∃ parents,
        (initial.runNormalized releaseBeforeFailure).1.OwnerAncestry
          work parents releaseBeforeFailure.flatten := by
  obtain ⟨parents, _, ledger⟩ := generated.runNormalized_ownerAncestry
    releaseBeforeFailure release_before_failure_valid.1 release_before_failure_valid.2
  exact ⟨parents, ledger⟩

/-- The failed child is absent after either complete placement of the parent success.
Witness: concrete final lookups; unlike the historical test, no early retirement is assumed.
-/
theorem failed_child_absent_both_orders
    : finalState.groupNode? child.key = none
      ∧ (initial.runNormalized releaseBeforeFailure).1.groupNode? child.key = none := by
  constructor <;> cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerReactivation
