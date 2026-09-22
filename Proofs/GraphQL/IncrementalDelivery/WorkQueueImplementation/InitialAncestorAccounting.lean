import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAncestorAccounting

/-! Initial group eligibility follows from concrete retirement and generated work.
The argument uses the empty source history, not an assumed initialization contract.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A group retired before the first settlement cannot have an object contributor
-----------------------------------------------------------------------------------------

/-- An initially retired group has no structural object contributor on executed work.
Witness: healthy retirement forces registration and successful settlement of every
contributor, but the initial source history contains no settlements.
-/
theorem ExecutedWork.initial_retired_noObjectContributor
    {work key address owners producer payload} (generated : ExecutedWork work)
    (retired : (State.initialize (Work.fromExecution work)).RetiredGroup key)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    : key ∉ owners := by
  intro contributes
  have healthy : ¬GroupRecordInvalidated work
      ((State.initialize (Work.fromExecution work)).objectFailureContributions []) key :=
    fun invalid => invalid.nonempty rfl
  obtain ⟨task, registered, occurrence, groups⟩ :=
    generated.retired_structuralContributor_registered (events := []) .nil rfl
      known contributes retired healthy
  obtain ⟨result, impossible⟩ :=
    generated.replayGraphEvents_retiredContributor_succeeded (events := []) .nil rfl
      registered (groups.symm ▸ contributes) retired healthy
  exact List.not_mem_nil impossible

-----------------------------------------------------------------------------------------
-- Concrete pruning already accounts for every ancestor of an initial group
-----------------------------------------------------------------------------------------

/-- No ancestor of an actual initial group owns any task in executed work.
Witness: pruning retires each task-bearing ancestor before promoting the group. Empty
replay excludes object contributors; execution's key roles exclude stream-item owners.
The task quantifier covers the entire work tree, including not-yet-lowered children.
-/
theorem ExecutedWork.initialGroups_ancestors_taskless
    {work group dependencies} (generated : ExecutedWork work)
    (noticed : group ∈ (State.initialize (Work.fromExecution work)).initialGroups)
    (known : NodeAt work group .group dependencies none)
    : ∀ key ∈ dependencies,
        ∀ occurrence owners, TaskHasOwners work occurrence owners → key ∉ owners := by
  have active : group.key ∈ (State.initialize (Work.fromExecution work)).rootGroups := by
    rw [createWorkQueue_rootGroups]
    exact List.mem_map_of_mem noticed
  intro key ancestor occurrence owners task contributes
  have record := groupRecordAt_of_nodeAt known
  have retired := generated.initialRootAncestorsRetired group.key active
    group dependencies record rfl key ancestor occurrence owners task contributes
  obtain ⟨producer, payload, descriptor⟩ := task
  cases occurrence with
  | executionGroup address =>
      exact generated.initial_retired_noObjectContributor retired descriptor contributes
  | item address ordinal =>
      obtain ⟨stream, items, enclosing, result, children, located, _, sameOwners, _⟩ :=
        descriptor
      rw [sameOwners] at contributes
      exact generated.groupRecord_ancestor_ne_stream record ancestor (.stream located)
        (List.mem_singleton.mp contributes)

/-- Every group actually announced at initialization is eligible on executed work.
Witness: immediate contributor provenance gives its producer-free descriptor; concrete
retirement rules out all ancestor tasks, satisfying the static eligibility equivalence.
-/
theorem ExecutedWork.initialGroups_canAnnounce {work} (generated : ExecutedWork work)
    {group} (noticed : group ∈ (State.initialize (Work.fromExecution work)).initialGroups)
    : ∃ dependencies,
        NodeAt work group .group dependencies none
        ∧ CanAnnounce work [] (fun _ => .executionGroup []) [] [] group .group
            dependencies none := by
  obtain ⟨dependencies, known⟩ := generated.initialGroups_nodeAt noticed
  exact ⟨dependencies, known, (group_canAnnounce_initial_iff known).mpr
    ⟨rfl, generated.initialGroups_ancestors_taskless noticed known⟩⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
