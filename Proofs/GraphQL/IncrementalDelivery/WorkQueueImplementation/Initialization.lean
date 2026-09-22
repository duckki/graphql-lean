import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPruningNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyPending
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupAccounting

/-! Static obligations for deriving the reference constructor's initialization premise.
These equivalences remove empty-history accounting from the proof goal. They do not add
source assumptions or assume that the concrete constructor meets the remaining obligations.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

-----------------------------------------------------------------------------------------
-- Empty-history eligibility is a static contributor condition
-----------------------------------------------------------------------------------------

/-- Before any settlement or publication, a dependency is satisfied exactly when it has
no contributing task. Witness: an owner supplies a node descriptor; empty accounting can
neither publish nor cancel that task. The reverse direction is vacuous accounting.
-/
theorem dependencySatisfied_initial_iff_noContributor {work matching key}
    : DependencySatisfied work [] matching [] [] key
      ↔ ∀ occurrence owners, TaskHasOwners work occurrence owners → key ∉ owners := by
  constructor
  · intro satisfied occurrence owners task owner
    rcases satisfied.2 with absent | completed | ⟨_, accounted⟩
    · obtain ⟨producer, payload, known⟩ := task
      obtain ⟨node, kind, dependencies, birth, descriptor, same⟩ := known.owner_known owner
      exact absent ⟨birth, node, kind, dependencies, descriptor, same⟩
    · simp [completedKeys] at completed
    · rcases accounted occurrence owners task owner with cancelled | published
      · exact cancelled.nonempty rfl
      · simp [Published] at published
  · intro absent
    refine ⟨fun failure => failure.nonempty rfl, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · simp [announcedKeys, pendingKeys]
    · intro occurrence owners task owner
      exact False.elim (absent occurrence owners task owner)

/-- A known group is initially eligible exactly when it is producer-free and none of
its ancestors owns a task anywhere in the execution work. Witness: empty publication
forces a missing producer, and the dependency equivalence removes dynamic accounting.
-/
theorem group_canAnnounce_initial_iff {work node dependencies producer}
    (known : NodeAt work node .group dependencies producer)
    : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group
        dependencies producer
      ↔ producer = none
        ∧ ∀ key ∈ dependencies,
            ∀ occurrence owners, TaskHasOwners work occurrence owners → key ∉ owners := by
  constructor
  · intro eligible
    refine ⟨?_, fun key member =>
      dependencySatisfied_initial_iff_noContributor.mp (eligible.2.2.2 key member)⟩
    cases producer with
    | none => rfl
    | some occurrence =>
        have impossible := eligible.2.2.1 occurrence rfl
        simp [Published] at impossible
  · rintro ⟨rfl, absent⟩
    refine ⟨by simp [announcedKeys, pendingKeys],
      Or.inl ⟨fun failure => failure.nonempty rfl,
        Or.inr (group_not_initially_accounted known)⟩, ?_, ?_⟩
    · intro occurrence impossible
      cases impossible
    · intro key member
      exact dependencySatisfied_initial_iff_noContributor.mpr (absent key member)

-----------------------------------------------------------------------------------------
-- What the concrete constructor already guarantees
-----------------------------------------------------------------------------------------

/-- Every actual initial stream is eligible, even if its item list is empty.
Witness: lowering gives no producer or dependencies; empty failure cuts are healthy.
This fact needs no executed-work or initialization premise.
-/
theorem initialStreams_canAnnounce (work : Execution.Work) {stream}
    (member : stream ∈ (State.initialize (Work.fromExecution work)).initialStreams)
    : NodeAt work stream .stream [] none
      ∧ CanAnnounce work [] (fun _ => .executionGroup []) [] [] stream .stream []
          none := by
  refine ⟨
    (createWorkQueue_initialStreams_nodeAt work).2 stream member,
    by simp [announcedKeys, pendingKeys],
    Or.inl ⟨fun failure => failure.nonempty rfl, Or.inl rfl⟩,
    ?_,
    Or.inl rfl
  ⟩
  intro occurrence impossible
  cases impossible

/-- Root-stream registration emits distinct stream keys, even for repeated raw input.
Witness: the fresh-stream fold appends only keys absent from its selected prefix.
-/
theorem State.addStreams_newKeys_unique (queue : State) (streams : List Stream)
    : (((queue.addStreams streams none).2).map DeliveryNode.key).Nodup := by
  let step (selected : List Stream) (stream : Stream) :=
    if (queue.stream? stream.node.key).isSome
        || selected.any (fun known => known.node.key == stream.node.key) then
      selected
    else
      selected ++ [stream]
  have loop (more selected : List Stream)
      (unique : (selected.map (fun stream => stream.node.key)).Nodup)
      : ((more.foldl step selected).map (fun stream => stream.node.key)).Nodup := by
    induction more generalizing selected with
    | nil => exact unique
    | cons stream rest ih =>
        apply ih
        dsimp only [step]
        split
        · exact unique
        · rename_i fresh
          rw [List.map_append, List.map_singleton, List.nodup_append]
          refine ⟨unique, by simp, ?_⟩
          intro key member other included same
          obtain rfl := List.mem_singleton.mp included
          obtain ⟨prior, priorMember, priorKey⟩ := List.mem_map.mp member
          have present : selected.any (fun known => known.node.key == stream.node.key)
              = true :=
            List.any_eq_true.mpr
              ⟨prior, priorMember, beq_iff_eq.mpr (priorKey.trans same)⟩
          exact fresh (by simp [present])
  simpa only [State.addStreams, List.map_map, step, Function.comp_def]
    using loop streams [] (by simp)

/-- Actual initial stream notices have distinct keys for arbitrary execution work.
Witness: initialization retains the root-stream registration result exactly.
-/
theorem initialStreams_unique (work : Execution.Work)
    : ((State.initialize (Work.fromExecution work)).initialStreams.map
        DeliveryNode.key).Nodup :=
  State.addStreams_newKeys_unique _ _

/-- Initial group notices retain contributor-or-ancestor registration metadata.
Witness: immediate lowering supplies each candidate and registry record; pruning only
keeps these descriptors or promotes registered children.
-/
theorem initialGroups_recordAt (work : Execution.Work)
    {group} (member : group ∈ (State.initialize (Work.fromExecution work)).initialGroups)
    : ∃ dependencies, GroupRecordAt work group dependencies := by
  let input := Work.fromExecution work
  let integrated := ({} : State).maybeIntegrateWork input
  have supplied : ∀ candidate ∈ input.groups,
      ∃ dependencies, GroupRecordAt work candidate.node dependencies := by
    intro candidate included
    obtain ⟨dependencies, known, _⟩ := workFromSpec_groups_recordAt Located.root included
    exact ⟨dependencies, known⟩
  have empty : ({} : State).GroupNodesMatchWork work := by
    intro node impossible
    cases impossible
  have registered : integrated.1.GroupNodesMatchWork work :=
    empty.maybeIntegrateWork input supplied
  apply registered.pruneEmptyGroups_notices integrated.2.newGroups ?_ group member
  intro candidate included
  obtain ⟨record, recordMember, same, _⟩ :=
    ({} : State).addGroups_newGroup_candidate input.groups included
  exact same ▸ supplied record recordMember

/-- Every actual initial group notice has a producer-free contributor descriptor.
Witness: task installation supports roots only by immediate lowered contributors;
generated descriptor coherence identifies that contributor with the announced record.
-/
theorem ExecutedWork.initialGroups_nodeAt {work : Execution.Work}
    (generated : ExecutedWork work)
    {group} (member : group ∈ (State.initialize (Work.fromExecution work)).initialGroups)
    : ∃ dependencies, NodeAt work group .group dependencies none := by
  have support : (State.initialize (Work.fromExecution work)).GroupKeySupport
      (fun key => ∃ node dependencies, NodeAt work node .group dependencies none
        ∧ node.key = key) := by
    apply createWorkQueue_groupKeySupport
    intro task included owner contributes
    obtain ⟨address, payload, occurrence, known⟩ :=
      workFromSpec_tasks_taskAt Located.root included
    rw [occurrence] at known
    exact TaskAt.executionGroup_owner known (List.mem_map_of_mem contributes)
  have active : group.key ∈ (State.initialize (Work.fromExecution work)).rootGroups := by
    rw [createWorkQueue_rootGroups]
    exact List.mem_map_of_mem member
  obtain ⟨node, dependencies, known, same⟩ := support.roots group.key active
  obtain ⟨recordDependencies, record⟩ := initialGroups_recordAt work member
  have equal := generated.record_eq_node record known same.symm
  exact ⟨dependencies, equal ▸ known⟩

/-- The complete initialized frontier has distinct keys on executed work.
Witness: generated pruning gives unique group keys, stream registration gives unique
stream keys, and execution assigns disjoint key roles to groups and streams.
-/
theorem ExecutedWork.initialNoticeKeys_unique {work : Execution.Work}
    (generated : ExecutedWork work)
    : (((State.initialize (Work.fromExecution work)).initialGroups
        ++ (State.initialize (Work.fromExecution work)).initialStreams).map
        DeliveryNode.key).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨generated.initialGroups_unique, initialStreams_unique work, ?_⟩
  intro key member other included same
  obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨stream, streamMember, rfl⟩ := List.mem_map.mp included
  obtain ⟨dependencies, known⟩ := generated.initialGroups_nodeAt groupMember
  exact generated.groupStreamKeysDisjoint known
    ((createWorkQueue_initialStreams_nodeAt work).2 stream streamMember) same

-----------------------------------------------------------------------------------------
-- Exact remaining constructor obligations, without history or source premises
-----------------------------------------------------------------------------------------

/-- Concrete initialization reduces exactly to distinct keys, producer-free groups with
taskless ancestors, and a nonempty frontier. Witness: stream eligibility is unconditional;
group eligibility is the static characterization above. No obligation is assumed here.
-/
theorem initializes_iff_static_frontier (work : Execution.Work)
    : let queue := State.initialize (Work.fromExecution work)
      Initializes work queue.initialGroups queue.initialStreams
      ↔ ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.key).Nodup
        ∧ (∀ group ∈ queue.initialGroups,
            ∃ dependencies,
              NodeAt work group .group dependencies none
              ∧ ∀ key ∈ dependencies,
                  ∀ occurrence owners,
                    TaskHasOwners work occurrence owners → key ∉ owners)
        ∧ queue.initialGroups ++ queue.initialStreams ≠ [] := by
  intro queue
  constructor
  · intro initialized
    refine ⟨initialized.1.1, ?_, initialized.2⟩
    intro group member
    obtain ⟨dependencies, producer, known, eligible⟩ := initialized.1.2.1 group member
    obtain ⟨rfl, absent⟩ := (group_canAnnounce_initial_iff known).mp eligible
    exact ⟨dependencies, known, absent⟩
  · rintro ⟨unique, groups, nonempty⟩
    refine ⟨⟨unique, ?_, ?_⟩, nonempty⟩
    · intro group member
      obtain ⟨dependencies, known, absent⟩ := groups group member
      exact ⟨dependencies, none, known,
        (group_canAnnounce_initial_iff known).mpr ⟨rfl, absent⟩⟩
    · intro stream member
      exact ⟨[], none, initialStreams_canAnnounce work member⟩

/-- Executed-work initialization has only two remaining obligations: eligible group
descriptors and a nonempty frontier. Witness: the static characterization and disjoint
group/stream key roles derive uniqueness rather than assuming it separately.
-/
theorem ExecutedWork.initializes_iff_groups_and_nonempty {work : Execution.Work}
    (generated : ExecutedWork work)
    : let queue := State.initialize (Work.fromExecution work)
      Initializes work queue.initialGroups queue.initialStreams
      ↔ (∀ group ∈ queue.initialGroups,
          ∃ dependencies,
            NodeAt work group .group dependencies none
            ∧ ∀ key ∈ dependencies,
                ∀ occurrence owners, TaskHasOwners work occurrence owners → key ∉ owners)
        ∧ queue.initialGroups ++ queue.initialStreams ≠ [] := by
  intro queue
  constructor
  · exact fun facts => ((initializes_iff_static_frontier work).mp facts).2
  · rintro ⟨groups, nonempty⟩
    apply (initializes_iff_static_frontier work).mpr
    exact ⟨generated.initialNoticeKeys_unique, groups, nonempty⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
