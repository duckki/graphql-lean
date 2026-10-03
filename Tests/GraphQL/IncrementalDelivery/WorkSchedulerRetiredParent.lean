import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupInvalidation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredAncestorHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MissingParentRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplayClosure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthStability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredRecordHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A successful missing parent remains healthy after a later independent failure. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetiredParent
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def child : DeliveryNode := ⟨1, [], some (.string "C")⟩
private def other : DeliveryNode := ⟨2, [], some (.string "R")⟩
private def parentTask : Occurrence := .executionGroup [1, 0]
private def otherTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def noChildren : Execution.Work := .combine .empty .empty
private def parentData : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨parent, []⟩] [] (.ok (parentData, 0)) noChildren)
      (.combine
        (.executionGroup [⟨child, [parent]⟩] []
          (.ok ([("b", .scalar "b")], 0)) noChildren)
        (.combine (.executionGroup [⟨other, []⟩] [] (.error 1) .empty) .empty)))

private def success : GraphEvent :=
  .taskSuccess parentTask
    {
      value :=
        { path := [], data := parentData, errors := 0, deliveryGroups := [parent] },
      work := Work.fromExecution noChildren [1, 0, 0]
    }

private def failure : GraphEvent := .taskFailure otherTask 1
private def inputs : List (List GraphEvent) := [[success], [failure]]
private def initial : State := State.initialize (Work.fromExecution work)
private def retired : State := (initial.runNormalized inputs).1
private def afterSuccess : State := (initial.handleGraphEvent success).1

/-- Execution generates this nested success and independent failure without raw work hacks.
Witness: evaluate the query with P/C nesting and an unrelated non-null error in R.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "a", defer [field "b"] (some "C")] (some "P"),
      defer [field "required"] (some "R")], ?_⟩
  cbv

/-- The only failed task contributes exclusively to R.
Witness: direct lookup of its generated root-task address.
-/
private theorem other_known
    : TaskAt work otherTask [other.ref] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

/-- Both source settlements obey fixed outcomes, freshness, readiness, and start discipline.
Witness: the two root descriptors and evaluation of the unchanged start checker.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have parentKnown
      : TaskAt work parentTask [parent.ref] none (.object [] (.ok (parentData, 0))) :=
    ⟨_, [], .ok (parentData, 0), noChildren, [], rfl, rfl, rfl⟩
  have first : ValidGraphEvents work [success] :=
    .append .nil ⟨_, _, parentKnown, rfl, rfl⟩
      (by simp [success, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parentKnown, by intro producer impossible; cases impossible⟩
  refine ⟨.append first ⟨_, _, _, other_known⟩ ?_ ?_, by cbv⟩
  · simp [success, failure, GraphEvent.Fresh, GraphEvent.identities, parentTask, otherTask]
  · exact ⟨_, _, _, other_known, by intro producer impossible; cases impossible⟩

/-- The surviving child's absent successful parent is permanently retired, not unseen.
Witness: apply the general generated-replay parent-registration theorem to C's live
record and missing-parent lookup; registration is not separately computed for the fixture.
-/
theorem missing_parent_retired : retired.RetiredGroup parent.ref := by
  let node : GroupNode :=
    { group := ⟨child, some parent.ref⟩, tasks := [.executionGroup [1, 1, 0]], pending := 1 }
  exact generated.runNormalized_missingParentRetired source_valid.1 node
    (by cbv; exact List.mem_cons_self)
    parent.ref rfl
    (by cbv)

/-- Before R's failure, actual source replay keeps the registered-task accounting ledger.
Witness: the general started owner-replay theorem, with no supplied child-availability
callback, output admission, or missing-parent health premise.
-/
private theorem after_success_accounting
    : afterSuccess.HealthyRegisteredTaskAccounting work [parentTask] [] := by
  obtain ⟨_, _, accounting⟩ := generated.replayGraphEvents_ownerAccounting_of_started [success]
    (source_valid.1.prefix ⟨[failure], rfl⟩) (by cbv)
  exact accounting.owners

/-- The actual missing-parent boundary retains a nonvacuous retirement certificate.
Witness: the general generated-replay theorem at the one-event prefix; its bookkeeping
records agree with the actual handler, independently of the batch-control flag.
-/
theorem after_success_retirement : afterSuccess.MissingParentAncestorsRetired work := by
  have valid : ValidGraphEvents work [[success]].flatten :=
    source_valid.1.prefix ⟨[failure], rfl⟩
  exact (generated.runNormalized_missingParentAncestorsRetired valid).of_sameRecords
    (by cbv) (by cbv) (by cbv)

/-- P remains healthy under every valid started continuation after its success, not just
the particular independent failure below. Witness: general retired-record stability;
the prefix supplies permanent retirement and an empty accepted-failure inventory.
-/
theorem successful_parent_health_stable (events : List GraphEvent)
    (valid : ValidGraphEvents work events) (started : initial.acceptsBatch events = true)
    (earlier : [success].IsPrefix events)
    : ¬GroupRecordInvalidated work (initial.objectFailureContributions events)
        parent.ref := by
  have known : GroupRecordAt work parent [] :=
    groupRecordAt_of_nodeAt
      (show NodeAt work parent .group [] none from
        ⟨[1, 0], _, [], .ok (parentData, 0), noChildren, [], ⟨parent, []⟩,
          rfl, List.mem_cons_self, rfl, rfl⟩)
  have retired : (initial.replayGraphEvents [success]).RetiredGroup parent.ref := by
    constructor
    · cbv; exact List.mem_cons_self
    · have refs : (initial.replayGraphEvents [success]).groupNodes.map
          (fun node => node.group.node.ref) = [child.ref, other.ref] := by cbv
      rw [refs]; decide
  exact generated.retiredRecord_health_stable valid started known earlier retired
    (fun invalid => invalid.nonempty (by cbv))

/-- The independent accepted failure cannot retroactively invalidate retired P.
Witness: instantiate arbitrary-continuation stability and compute only the token ledger.
-/
theorem retired_parent_health_after_failure
    : ¬GroupRecordInvalidated work [otherTask] parent.ref := by
  have healthy := successful_parent_health_stable inputs.flatten source_valid.1
    (by cbv) ⟨[failure], rfl⟩
  have inventory : initial.objectFailureContributions inputs.flatten = [otherTask] := by cbv
  rwa [inventory] at healthy

/-- All uncancelled retired records are healthy after P succeeds and R fails.
Witness: the concrete registry leaves only P as an uncancelled retirement; its health is
the general continuation theorem, not a direct enumeration of failure causes.
-/
theorem retired_records_healthy : retired.UncancelledRetiredHealthy work [otherTask] := by
  intro node dependencies known gone uncancelled
  have registry : retired.registeredGroups = [parent.ref, child.ref, other.ref] := by cbv
  have live : retired.groupNodes.map (fun node => node.group.node.ref) = [child.ref] := by cbv
  have cancelled : retired.cancelledGroups = [other.ref] := by cbv
  have registered := gone.1
  rw [registry] at registered
  rw [cancelled] at uncancelled
  have absent := gone.2
  rw [live] at absent
  have ref : node.ref = parent.ref := by
    exact (List.mem_cons.mp registered).resolve_right (by
        intro member
        rcases List.mem_cons.mp member with same | last
        · exact absent (List.mem_singleton.mpr same)
        · exact uncancelled last)
  exact ref ▸ retired_parent_health_after_failure

/-- Later registration cannot invalidate the successfully retired parent certificate.
Witness: general arbitrary-chunk integration preserves the proved nonempty-failure
retirement invariant; refused records are cancelled and cannot enter its healthy branch.
-/
theorem late_integration_retired_health (newWork : ReferenceWorkQueue.Work)
    (producer : Option Occurrence)
    : (retired.maybeIntegrateWork newWork producer).1.UncancelledRetiredHealthy
        work [otherTask] :=
  retired_records_healthy.maybeIntegrateWork newWork producer

/-- Recording R's fresh failure cannot invalidate the already-retired parent boundary.
Witness: the general retired-ancestor inventory theorem with the actual pending-task
ledger. This precedes the failure handler's state changes and does not assume its guard
soundness or re-prove health by enumerating possible invalidation causes.
-/
theorem missing_parent_health_at_new_failure
    : afterSuccess.MissingParentAncestorsHealthy work [otherTask] := by
  let task : Task := ⟨otherTask, [other]⟩
  have tasks : afterSuccess.tasks =
      [⟨parentTask, [parent]⟩, ⟨.executionGroup [1, 1, 0], [child]⟩, task] := by cbv
  have registered : task ∈ afterSuccess.tasks := by rw [tasks]; simp
  have matching : TaskMatches work task := ⟨⟨_, _, _, rfl, other_known⟩, rfl⟩
  exact (State.MissingParentAncestorsHealthy.of_empty afterSuccess work).append_fresh
    after_success_retirement generated after_success_accounting registered matching
    (by simp [task, otherTask, parentTask])

/-- The same generic argument survives the actual independent failure cleanup.
Witness: apply removal preservation, then identify replay's surviving records and
cancellation refs with that cleanup. No direct enumeration of failure causes is used.
-/
theorem missing_parent_health_after_cleanup
    : retired.MissingParentAncestorsHealthy work [otherTask] := by
  have safe := missing_parent_health_at_new_failure.removeGroup other.ref
  have nodes : retired.groupNodes = (afterSuccess.removeGroup other.ref).groupNodes := by cbv
  have cancelled
      : retired.cancelledGroups = (afterSuccess.removeGroup other.ref).cancelledGroups := by
    cbv
  simpa only [State.MissingParentAncestorsHealthy, State.groupNode?, nodes, cancelled]
    using safe

/-- C keeps a live parent link after P succeeds and R fails, although P's record is gone.
Witness: concrete replay and the nonempty accepted-failure inventory; P was not cancelled.
Thus missing-parent health cannot be replaced by requiring every parent record to exist.
-/
theorem successful_missing_parent
    : ∃ node ∈ retired.groupNodes,
        node.group.node = child
        ∧ node.group.parent = some parent.ref
        ∧ retired.groupNode? parent.ref = none
        ∧ parent.ref ∉ retired.cancelledGroups
        ∧ retired.groupIsHealthy child.ref = true
        ∧ initial.objectFailureContributions inputs.flatten = [otherTask] := by
  refine ⟨{
    group := ⟨child, some parent.ref⟩,
    tasks := [.executionGroup [1, 1, 0]], pending := 1
  }, ?_⟩
  cbv
  refine ⟨List.mem_cons_self, ?_, trivial⟩
  intro member
  have impossible : (0 : Nat) = 2 := List.mem_singleton.mp member
  cases impossible

/-- The absent parent and its live child really are healthy under the accepted failure.
Witness: generated ancestry reduces each possible invalidation to R owning P or C,
contradicting R's exact fixed task descriptor. This does not assume guard soundness.
-/
theorem successful_ancestry_healthy
    : ¬GroupInvalidated work [otherTask] parent.ref
      ∧ ¬GroupInvalidated work [otherTask] child.ref := by
  have root : NodeAt work parent .group [] none :=
    ⟨[1, 0], _, [], .ok (parentData, 0), noChildren, [], ⟨parent, []⟩,
      rfl, by simp, rfl, rfl⟩
  have nested : NodeAt work child .group [parent.ref] none :=
    ⟨[1, 1, 0], _, [], .ok ([("b", .scalar "b")], 0), noChildren, [],
      ⟨child, [parent]⟩, rfl, by simp, rfl, rfl⟩
  have excludes {node dependencies producer}
      (known : NodeAt work node .group dependencies producer)
      (separate : other.ref ∉ node.ref :: dependencies)
      : ¬GroupInvalidated work [otherTask] node.ref := by
    intro invalid
    obtain ⟨occurrence, owners, ref, ⟨birth, payload, task⟩, member, owner, ancestor⟩ :=
      (generated.groupInvalidated_iff known).mp invalid
    obtain rfl := List.mem_singleton.mp member
    rw [(task.unique other_known).1] at owner
    obtain rfl := List.mem_singleton.mp owner
    exact separate ancestor
  exact ⟨excludes root (by decide), excludes nested (by decide)⟩

/-- Successful retirement satisfies the actual record-aware missing-parent obligation.
Witness: generic preservation across the fresh failure's inventory extension and cleanup.
No guard-soundness theorem is used to establish this premise.
-/
theorem missing_parent_boundary
    : retired.MissingParentAncestorsHealthy work [otherTask] :=
  missing_parent_health_after_cleanup

/-- General guard reflection handles this genuine missing-parent replay boundary.
Witness: generated source laws now supply the boundary through joint health replay;
no fixture-specific missing-parent premise is needed by guard reflection.
-/
theorem guard_reflection_after_retirement
    : ¬GroupRecordInvalidated work [otherTask] child.ref := by
  have inventory : initial.objectFailureContributions inputs.flatten = [otherTask] := by cbv
  have reflected := generated.replayGraphEvents_groupIsHealthy_recordUninvalidated
    inputs.flatten source_valid.1 (by cbv) (ref := child.ref) (by cbv)
  change ¬GroupRecordInvalidated work (initial.objectFailureContributions inputs.flatten)
    child.ref at reflected
  rwa [inventory] at reflected

/-- Every received prefix preserves the missing-parent boundary in this concrete replay.
Witness: the general health-replay theorem, with source validity and start acceptance
restricted to that prefix. No enumeration of the possible prefixes is needed.
-/
theorem prefix_missing_parent_health
    : ∀ received : List GraphEvent,
        received.IsPrefix inputs.flatten
        → (initial.replayGraphEvents received).MissingParentAncestorsHealthy work
            (initial.objectFailureContributions received) := by
  intro received before
  have valid := source_valid.1.prefix before
  obtain ⟨after, same⟩ := before
  have accepted : initial.acceptsBatch inputs.flatten = true := by cbv
  rw [← same] at accepted
  exact (generated.replayGraphEvents_retiredHealth received valid
    (State.acceptsBatch_prefix accepted)).2.2

/-- The general cut theorem supplies an uninvalidated owner after successful retirement.
Witness: use actual source acceptance and the independently proved prefix boundary,
without assuming causal health or an explained output history.
-/
theorem accepted_failure_owner_uninvalidated
    : ∃ owners ref,
        TaskHasOwners work otherTask owners
        ∧ ref ∈ owners
        ∧ ¬GroupRecordInvalidated work [] ref := by
  have cut
      : let publisher : IncrementalPublisher :=
          { active := initial.initialGroups ++ initial.initialStreams }
        sourceObjectFailureCuts 0
          (initial.eligibleFailureBlocks (initial.sourceRunBlocks publisher inputs).2.2)
        = [] ++ (2, otherTask) :: [] := by cbv
  exact createWorkQueue_eligibleObjectFailureCuts_uninvalidatedOwner
    generated source_valid.1 source_valid.2 prefix_missing_parent_health cut

/-- An actually cancelled missing parent takes the opposite guard branch.
Witness: changing only P's retained cancellation marker rejects the same live child.
This last check isolates the guard; the modified state is not claimed to be generated.
-/
theorem cancelled_missing_parent_rejected
    : ({ retired with cancelledGroups := parent.ref :: retired.cancelledGroups }
        : State).groupIsHealthy
        child.ref
      = false := by
  cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetiredParent
