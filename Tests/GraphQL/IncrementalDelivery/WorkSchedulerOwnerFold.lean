import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationAdmission
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerFoldCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! The single-pass shared-owner fold has a genuine intermediate publication boundary. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerOwnerFold
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def firstOwner : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def lastOwner : DeliveryNode := ⟨1, [], some (.string "Q")⟩
private def sharedTask : Occurrence := .executionGroup [1, 0]
private def lastTask : Occurrence := .executionGroup [1, 1, 0]

private def sharedValue : ExecutionGroupValue :=
  {
    path := [],
    data := [("a", .scalar "a")],
    errors := 0,
    deliveryGroups := [firstOwner, lastOwner]
  }

private def lastValue : ExecutionGroupValue :=
  { path := [], data := [("b", .scalar "b")], errors := 0, deliveryGroups := [lastOwner] }

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨firstOwner, []⟩, ⟨lastOwner, []⟩] []
        (.ok (sharedValue.data, 0)) (.combine .empty .empty))
      (.combine
        (.executionGroup [⟨lastOwner, []⟩] []
          (.ok (lastValue.data, 0)) (.combine .empty .empty))
        .empty))

private def first : GraphEvent := .taskSuccess lastTask ⟨lastValue, {}⟩
private def finish : GraphEvent := .taskSuccess sharedTask ⟨sharedValue, {}⟩
private def initial : State := State.initialize (Work.fromExecution work)
private def incoming : TaskNode := { task := ⟨sharedTask, [firstOwner, lastOwner]⟩ }

private def prepared : State :=
  ((initial.replayGraphEvents [first]).putTaskNode
    { incoming with value := some sharedValue }).maybeIntegrateWork
    {} (some sharedTask)
  |>.1

private def middle : State × List WorkQueueEvent × NewWork :=
  [firstOwner].foldl successGroupStep (prepared, [], {})

private theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "a"] (some "P"), defer [field "a", field "b"] (some "Q")], ?_⟩
  cbv

private theorem valid : ValidGraphEvents work [first, finish] := by
  have lastKnown : TaskAt work lastTask [lastOwner.ref] none
      (.object [] (.ok (lastValue.data, 0))) :=
    ⟨_, [], _, .combine .empty .empty, [], rfl, rfl, rfl⟩
  have sharedKnown : TaskAt work sharedTask [firstOwner.ref, lastOwner.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    ⟨_, [], _, .combine .empty .empty, [], rfl, rfl, rfl⟩
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, lastKnown, rfl, rfl⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, lastKnown, by intro source impossible; cases impossible⟩
  exact .append one ⟨_, _, sharedKnown, rfl, rfl⟩
    (by
      simp [first, finish, GraphEvent.Fresh, GraphEvent.identities, sharedTask, lastTask])
    ⟨_, _, _, sharedKnown, by intro source impossible; cases impossible⟩

namespace RetainedCoverage

private def leftChild : DeliveryNode := ⟨2, [], some (.string "C")⟩
private def rightChild : DeliveryNode := ⟨3, [], some (.string "D")⟩

private def left : GroupNode :=
  { group := ⟨firstOwner, none⟩, childGroups := [leftChild.ref], pending := 1 }

private def right : GroupNode :=
  { group := ⟨lastOwner, none⟩, childGroups := [rightChild.ref], pending := 1 }

private def leftLeaf : GroupNode :=
  {
    group := ⟨leftChild, some firstOwner.ref⟩,
    tasks := [.executionGroup [2]],
    pending := 1
  }

private def rightLeaf : GroupNode :=
  {
    group := ⟨rightChild, some lastOwner.ref⟩,
    tasks := [.executionGroup [3]],
    pending := 1
  }

private def queue : State :=
  {
    rootGroups := [firstOwner.ref, lastOwner.ref],
    groupNodes := [left, right, leftLeaf, rightLeaf]
  }

private def parents : Nat → NodeRefs :=
  fun ref =>
    if ref = leftChild.ref then
      [firstOwner.ref]
    else if ref = rightChild.ref then
      [lastOwner.ref]
    else
      []

private theorem forest : queue.RemovalForest parents := by
  refine ⟨?_, ?_, ?_⟩
  · simp [State.ChildGroupsUnique, queue, left, right, leftLeaf, rightLeaf]
  · simp [State.ChildLinksCanonical, queue, left, right, leftLeaf, rightLeaf,
      parents, firstOwner, lastOwner, leftChild, rightChild]
  · intro parent child parentMember childMember linked
    simp only [queue, List.mem_cons, List.not_mem_nil, or_false] at parentMember childMember
    rcases parentMember with rfl | rfl | rfl | rfl <;>
      rcases childMember with rfl | rfl | rfl | rfl <;>
      simp_all [left, right, leftLeaf, rightLeaf, firstOwner, lastOwner, leftChild, rightChild]

/-- A child released early in the owner fold stays covered while a later owner closes.
Witness: the generic retained-root coverage theorem, with activation after both passes.
This is a concrete queue-bookkeeping fixture, not a generated-work claim.
-/
theorem earlier_release_survives_later_closure
    : let middle := successGroupStep (queue, [], {}) firstOwner
      let folded := [firstOwner, lastOwner].foldl successGroupStep (queue, [], {})
      let final := folded.1.startNewWork folded.2.2
      leftChild.ref ∉ middle.1.rootGroups
      ∧ leftChild ∈ middle.2.2.newGroups
      ∧ ∃ root ∈ final.rootGroups, final.LiveDescendant root leftChild.ref := by
  intro middle folded final
  refine ⟨by change 2 ∉ [1]; decide, by cbv; exact List.mem_cons_self, ?_⟩
  apply State.successGroupFold_activated_root_coverage (queue := queue)
    (by unfold State.GroupRefsUnique; decide) forest [firstOwner, lastOwner]
  · refine ⟨firstOwner.ref, List.mem_cons_self, ?_⟩
    exact .child (node := left) (by cbv) List.mem_cons_self (.self (node := leftLeaf) (by cbv))
  · exact ⟨leftLeaf, by cbv⟩

end RetainedCoverage

/-- The first owner publishes the shared task while the later owner's stored task remains.
Witness: exact reduction of the single-pass prefix, not the handler's final queue.
-/
theorem actual_intermediate_boundary
    : middle.2.1 = [.groupValues firstOwner [sharedValue], .groupSuccess firstOwner [] []]
      ∧ ∃ node ∈ middle.1.groupNodes, lastTask ∈ node.tasks := by
  refine ⟨
    by cbv,
    ⟨{ group := ⟨lastOwner, none⟩, tasks := [lastTask], pending := 1 }, ?_, ?_⟩
  ⟩
  · cbv; exact .head _
  · exact List.mem_cons_self

/-- The common conformance matching clears its first value before the second owner runs.
Witness: exact matching identifies the first ledger label. The carrier-position theorem
recovers its emitting owner boundary and proves exclusion there. The later task remains
in that queue, so the theorem cannot have used its eventual final-state removal.
-/
theorem shared_owner_intermediate_exclusion
    : ∃ w : ConformancePlan.Witness,
        ConformancePlan.GroupPublicationAdmission work w
        ∧ middle.1.TaskMembershipAbsent (w.matching 0)
        ∧ ∃ node ∈ middle.1.groupNodes, lastTask ∈ node.tasks := by
  let inputs := [[first], [finish]]
  have source : ValidGraphEvents work inputs.flatten := valid
  have started : inputsStarted work inputs = true := by cbv
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger, _, _, _, admitted⟩ :=
    ConformancePlan.mixed_groupPublicationCertificates generated source started
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])
  have selected : w.events[0]? = some (.groupValues firstOwner [sharedValue]) := by
    rw [history]; cbv
  have matched := matching.atObject 0 firstOwner [sharedValue] selected
  cases labels : published with
  | nil => simp [labels] at matched
  | cons head tail =>
      have same : head.1 = w.matching 0 := by simpa [labels] using matched
      refine ⟨w, admitted, ?_, actual_intermediate_boundary.2⟩
      rw [← same]
      obtain ⟨steps, bounded, exactPrefix, cleared⟩ :=
        createWorkQueue_taskSuccess_ownerCarrierMemberships
        (before := [first]) (after := []) (incoming := incoming)
        (index := 1) (group := firstOwner) (groups := []) (streams := [])
        covered source (by cbv) (by cbv) (by cbv)
      have zero : steps = 0 := by
        cases steps with
        | zero => rfl
        | succ steps =>
            have bound : steps + 1 < 2 := bounded
            have zero : steps = 0 := by omega
            subst steps
            have size := congrArg List.length exactPrefix
            change 2 = 4 at size
            omega
      subst steps
      apply cleared head
      change head ∈ published.take 1
      rw [labels]; simp

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerOwnerFold
