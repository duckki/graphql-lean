import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationActivationSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationAccounting

/-! Registration-phase retention is independent of computation start and stored values. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)
private abbrev Kernel := ReferenceWorkQueue.State

/-- The reference membership frame needed during registration, before any settlement.
These are derived bookkeeping facts, not native acquisition or endpoint assumptions.
-/
structure RegistrationFrame (queue : Kernel) (settled : List Occurrence) : Prop where
  keys : queue.GroupRefsUnique
  live : queue.LiveGroupsRegistered
  contributors : queue.TaskGroupsRegistered
  links : queue.UnsettledTaskLinks settled

/-- Complete registration preserves the frame, including links of newly returned tasks. -/
theorem RegistrationFrame.integrate {state : State} {settled}
    (frame : RegistrationFrame state.queue settled) (work : ReferenceWorkQueue.Work)
    (covered
      : ∀ task ∈ work.tasks,
        ∀ key ∈ task.groups.map DeliveryNode.ref,
          ∃ group ∈ work.groups, group.node.ref = key)
    (producer : Option Occurrence := none)
    : RegistrationFrame (state.maybeIntegrateWork work producer).1.queue settled := by
  have registration := state.maybeIntegrateWork_registrationCore work producer
  have registered := state.queue.maybeIntegrateWork_registration frame.live frame.contributors
    work covered producer
  refine ⟨state.maybeIntegrateWork_groupKeysUnique frame.keys work producer, ?_, ?_,
    state.maybeIntegrateWork_unsettledTaskLinks frame.links frame.keys frame.contributors work producer⟩
  · change (registrationCore (state.maybeIntegrateWork work producer).1.queue).LiveGroupsRegistered
    rw [registration]; exact registered.1
  · change (registrationCore (state.maybeIntegrateWork work producer).1.queue).TaskGroupsRegistered
    rw [registration]; exact registered.2.1

/-- Empty-shell pruning retains the membership frame without a health requirement. -/
theorem RegistrationFrame.prune {queue : Kernel} {settled}
    (frame : RegistrationFrame queue settled) (groups : List DeliveryNode)
    : RegistrationFrame (queue.pruneEmptyGroups groups).1 settled := by
  have registered := ReferenceWorkQueue.State.pruneEmptyGroups_registration
    frame.live frame.contributors groups
  exact ⟨frame.keys.pruneEmptyGroups groups, registered.1, registered.2.1,
    frame.links.pruneEmptyGroups groups⟩

/-- Actual delayed starts retain the registration frame, even for a stopped reader. -/
theorem RegistrationFrame.start {state : State} {settled}
    (frame : RegistrationFrame state.queue settled) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    : RegistrationFrame (state.startNewWork roots integrated targets).1.queue
        settled := by
  have groups := State.startNewWork_groupNodes state roots integrated targets
  have catalogues := State.startNewWork_catalogues state roots integrated targets
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [ReferenceWorkQueue.State.GroupRefsUnique, groups] using frame.keys
  · simpa only [ReferenceWorkQueue.State.LiveGroupsRegistered, groups, catalogues.2] using frame.live
  · simpa only [ReferenceWorkQueue.State.TaskGroupsRegistered, catalogues.1, catalogues.2]
      using frame.contributors
  · simpa only [ReferenceWorkQueue.State.UnsettledTaskLinks, ReferenceWorkQueue.State.TaskLinkedOn,
      groups, catalogues.1] using frame.links

-----------------------------------------------------------------------------------------
-- A linked task blocks empty-shell removal independently of computation start
-----------------------------------------------------------------------------------------

/-- A task membership prevents pruning of each of its live contributing owners.
The occurrence may be unstarted; stored values and owner health are irrelevant here.
-/
theorem pruneEmptyGroups_linkedOwner_present {queue : Kernel} {occurrence keys key}
    (links : queue.TaskLinkedOn occurrence keys) (contributes : key ∈ keys)
    (present : key ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    (groups : List DeliveryNode)
    : key
      ∈ (queue.pruneEmptyGroups groups).1.groupNodes.map
          (fun node => node.group.node.ref) := by
  have loop (fuel : Nat) (current : Kernel) (more kept : List DeliveryNode)
      (links : current.TaskLinkedOn occurrence keys)
      (present : key ∈ current.groupNodes.map (fun node => node.group.node.ref))
      : key ∈ (ReferenceWorkQueue.State.pruneEmptyGroups.go fuel current more kept).1.groupNodes.map
          (fun node => node.group.node.ref) := by
    induction fuel generalizing current more kept with
    | zero => exact present
    | succ fuel ih =>
        cases more with
        | nil => exact present
        | cons group rest =>
            simp only [ReferenceWorkQueue.State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _ links present
            · rename_i node found
              split
              · rename_i empty
                have different : key ≠ group.ref := by
                  intro same
                  have nodeKey := ReferenceWorkQueue.State.groupNode?_ref found
                  have listed := links node (List.mem_of_find?_eq_some found)
                    (nodeKey.symm ▸ same ▸ contributes)
                  have noTasks : node.tasks = [] :=
                    List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).1
                  simp only [noTasks, List.not_mem_nil] at listed
                have nextLinks : ReferenceWorkQueue.State.TaskLinkedOn
                    { current with groupNodes :=
                      current.groupNodes.filter (fun entry => entry.group.node.ref != group.ref) }
                    occurrence keys := by
                  intro owner live contributor
                  exact links owner (List.mem_filter.mp live).1 contributor
                apply ih _ _ _ nextLinks
                obtain ⟨owner, live, same⟩ := List.mem_map.mp present
                exact List.mem_map.mpr ⟨owner,
                  List.mem_filter.mpr ⟨live, by simp [same, different]⟩, same⟩
              · exact ih _ _ _ links present
  exact loop _ queue groups [] links present

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
