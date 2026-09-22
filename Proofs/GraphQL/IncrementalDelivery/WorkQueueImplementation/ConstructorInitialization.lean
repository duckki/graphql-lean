import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialAncestorAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ImmediateStreamCoverage

/-! The reference constructor derives the work-queue initialization contract.
No event-source or supplied initial-notice premise is needed.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Nonempty executed work cannot lose every initial notice during pruning
-----------------------------------------------------------------------------------------

/-- A producer-free group contributor lies below an actual initial group notice.
Witness: root lowering registers its task, initial accounting retains the unsettled
owner's live membership, and complete pruning puts that live group below an active root.
-/
theorem ExecutedWork.initialGroup_notice_exists {work group dependencies}
    (generated : ExecutedWork work)
    (known : NodeAt work group .group dependencies none)
    : (State.initialize (Work.fromExecution work)).initialGroups ≠ [] := by
  obtain ⟨address, groups, path, result, children, enclosing, fragment,
    located, member, rfl, rfl⟩ := known
  have taskKnown : TaskAt work (.executionGroup address)
      (groups.map (fun group => group.node.key)) none (.object path result) :=
    .executionGroup located
  obtain ⟨task, registered, _, owners⟩ :=
    TaskAt.executionGroup_initial_registered taskKnown
  have contributes : fragment.node.key ∈ task.groups.map Execution.DeliveryNode.key := by
    rw [owners]
    exact List.mem_map_of_mem member
  obtain ⟨node, live, same, _⟩ := createWorkQueue_healthyRegisteredTaskAccounting work
    task registered (by simp) fragment.node.key contributes
    (fun failure => failure.nonempty rfl)
  have found := (createWorkQueue_groupKeysUnique (Work.fromExecution work)).groupNode?_of_mem live
  rw [same] at found
  obtain ⟨root, active, _⟩ :=
    generated.initial_live_group_root_coverage fragment.node.key ⟨node, found⟩
  rw [createWorkQueue_rootGroups] at active
  intro empty
  simp [empty] at active

/-- Every nonempty executed work tree produces a nonempty initial notice frontier.
Witness: generated ownership gives a first group or stream boundary. A root group has
an active covering notice; a root stream is directly announced, even with no items.
-/
theorem ExecutedWork.initialNotices_nonempty {work} (generated : ExecutedWork work)
    (nonempty : work.size ≠ 0)
    : (State.initialize (Work.fromExecution work)).initialGroups
        ++ (State.initialize (Work.fromExecution work)).initialStreams
      ≠ [] := by
  have candidates : initialCandidates work ≠ [] := by
    obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
      selections, equal⟩ := generated
    obtain ⟨_, parents, _, coherent, _⟩ :=
      Semantics.GeneralScheduling.executeRoot_continuity schema resolvers variables fuel
        parentType source selections 0
    rw [equal] at coherent
    exact initialCandidates_nonempty coherent nonempty
  obtain ⟨⟨node, kind, dependencies⟩, member⟩ :=
    List.exists_mem_of_ne_nil _ candidates
  have known := initialCandidates_known Located.root member
  intro empty
  obtain ⟨groupsEmpty, streamsEmpty⟩ := List.append_eq_nil_iff.mp empty
  cases kind with
  | group => exact generated.initialGroup_notice_exists known groupsEmpty
  | stream =>
      have noticed := NodeAt.stream_initial_notice known
      simp [streamsEmpty] at noticed

-----------------------------------------------------------------------------------------
-- Initialization is a consequence of execution, not a caller or source assumption
-----------------------------------------------------------------------------------------

/-- The concrete reference constructor initializes every nonempty executed work tree.
Witness: distinct notice keys, producer-free eligible groups, eligible streams, and
nonempty frontier are all derived independently from actual lowering and pruning.
-/
theorem ExecutedWork.initializes {work} (generated : ExecutedWork work)
    (nonempty : work.size ≠ 0)
    : Initializes work (State.initialize (Work.fromExecution work)).initialGroups
        (State.initialize (Work.fromExecution work)).initialStreams := by
  apply (generated.initializes_iff_groups_and_nonempty).mpr
  refine ⟨?_, generated.initialNotices_nonempty nonempty⟩
  intro group noticed
  obtain ⟨dependencies, known⟩ := generated.initialGroups_nodeAt noticed
  exact ⟨dependencies, known, generated.initialGroups_ancestors_taskless noticed known⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
