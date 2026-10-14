import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRequests

/-! Resource safety follows the actual failed-task owner fold, including successive shared
owners and latent failures. The settling computation is excluded: it has finished, rather
than been aborted. No output-driven cleanup view or generated-state premise is needed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
open ReferenceWorkQueue (TaskNode)

-----------------------------------------------------------------------------------------
-- Preserve held sources through the actual failure fold
-----------------------------------------------------------------------------------------

private theorem failureStep_safety (errors : Nat)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode)
    : let next := fusedFailureGroupStep errors acc group
      acc.2.2.Subset next.2.2
      ∧ ∀ occurrence node key,
          acc.1.queue.taskNode? occurrence = some node
          → key ∈ node.childStreams
          → next.1.queue.taskNode? occurrence = some node ∨ .stream key ∈ next.2.2 := by
  unfold fusedFailureGroupStep
  split
  · exact ⟨List.Subset.refl _, fun _ _ _ found _ => .inl found⟩
  · split
    · rename_i node found active
      have safety := FusedRemovalSafety_holds acc.1 node.group.node.ref acc.2.2
      exact ⟨safety.1, safety.2.2⟩
    · exact ⟨List.Subset.refl _, fun _ _ _ found _ => .inl found⟩

private theorem failureFold_safety (errors : Nat)
    (groups : List Execution.DeliveryNode)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    : let next := groups.foldl (fusedFailureGroupStep errors) acc
      acc.2.2.Subset next.2.2
      ∧ ∀ occurrence node key,
          acc.1.queue.taskNode? occurrence = some node
          → key ∈ node.childStreams
          → next.1.queue.taskNode? occurrence = some node ∨ .stream key ∈ next.2.2 := by
  induction groups generalizing acc with
  | nil => exact ⟨List.Subset.refl _, fun _ _ _ found _ => .inl found⟩
  | cons group rest ih =>
      have first := failureStep_safety errors acc group
      have later := ih (fusedFailureGroupStep errors acc group)
      refine ⟨first.1.trans later.1, ?_⟩
      intro occurrence node key found held
      rcases first.2 occurrence node key found held with kept | requested
      · exact later.2 occurrence node key kept held
      · exact .inr (later.1 requested)

/-- Every other exact held-source record is retained or cancelled by this actual handler.
This is raw finite-state safety; generated provenance is only needed to show that an older
buffer is different from the fresh settling input.
-/
theorem
    _root_.GraphQL.IncrementalDelivery.AlternativeWorkQueue.State.taskFailure_heldSource
    (state : State) (failed : Occurrence) (errors : Nat) {occurrence : Occurrence}
    {node : TaskNode} {key : Nat} (different : occurrence ≠ failed)
    (found : state.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    : (state.taskFailure failed errors).1.queue.taskNode? occurrence = some node
      ∨ .cancelSource key ∈ (state.taskFailure failed errors).2.2 := by
  cases selected : state.queue.taskNode? failed with
  | none => simpa only [State.taskFailure, selected] using (Or.inl found)
  | some task =>
      have retained := (state.queue.removeTask_lookup_other different).trans found
      simp only [State.taskFailure, selected]
      split
      · exact .inl retained
      · rcases (failureFold_safety errors task.task.groups
            ({ state with queue := state.queue.removeTask failed }, [], [])).2
            occurrence node key retained held with kept | requested
        · exact .inl kept
        · exact .inr (List.mem_flatMap.mpr ⟨.stream key, requested, List.mem_cons_self⟩)

-----------------------------------------------------------------------------------------
-- Observe only cleanup starts emitted by the same handler
-----------------------------------------------------------------------------------------

/-- Construct cleanup requests from the actual handler, not inferred failure notices.
Already requested, released and foreign leases remain unchanged.
-/
def ResourceState.observeHandlerCleanup (resources : ResourceState) (state : State)
    (event : GraphEvent)
    : ResourceState × List ResourceAction :=
  resources.requestQueueCleanup
    ((state.handleGraphEvent event).2.2.filterMap HostEffect.cleanupStart?)

theorem ResourceState.observeHandlerCleanup_replay (resources : ResourceState)
    (state : State) (event : GraphEvent)
    : ResourceReplay resources (resources.observeHandlerCleanup state event).2
        (resources.observeHandlerCleanup state event).1 :=
  resources.requestQueueCleanup_replay _

/-- Every constructed request is licensed by an actual effect in this handler reduction. -/
theorem ResourceState.observeHandlerCleanup_actions (resources : ResourceState)
    (state : State) (event : GraphEvent) {action : ResourceAction}
    (member : action ∈ (resources.observeHandlerCleanup state event).2)
    : ∃ effect ∈ (state.handleGraphEvent event).2.2,
        ∃ target,
          effect.cleanupStart? = some target ∧ action = .requestCleanup target := by
  obtain ⟨target, listed, same⟩ := resources.requestQueueCleanup_actions _ _ member
  obtain ⟨effect, emitted, identifies⟩ := List.mem_filterMap.mp listed
  exact ⟨effect, emitted, target, identifies, same⟩

/-- One actual handler endpoint and one compatible resource history retain or request each
nonsettling queue-owned held source. Requesting cleanup does not assert asynchronous release
or completeness of native acquisition inventories.
-/
def FusedTaskFailureResourceSafety : Prop :=
  ∀ (state : State) (failed : Occurrence) (errors : Nat) (resources : ResourceState),
    let reduced := state.taskFailure failed errors
    let observed := resources.observeHandlerCleanup state (.taskFailure failed errors)
    ResourceReplay resources observed.2 observed.1
    ∧ (∀ action ∈ observed.2,
        ∃ effect ∈ reduced.2.2,
          ∃ target, effect.cleanupStart? = some target ∧ action = .requestCleanup target)
    ∧ ∀ occurrence node key,
        occurrence ≠ failed
        → state.queue.taskNode? occurrence = some node
        → key ∈ node.childStreams
        → resources (.stream key) = .owned .queue
        → reduced.1.queue.taskNode? occurrence = some node
          ∨ observed.1 (.stream key) = .cleanupRequested .queue

theorem FusedTaskFailureResourceSafety_holds : FusedTaskFailureResourceSafety := by
  intro state failed errors resources
  refine ⟨resources.observeHandlerCleanup_replay _ _,
    fun _ member => resources.observeHandlerCleanup_actions _ _ member, ?_⟩
  intro occurrence node key different found held owned
  rcases state.taskFailure_heldSource failed errors different found held with kept | requested
  · exact .inl kept
  · exact .inr (resources.requestQueueCleanup_owned _ _
      (List.mem_filterMap.mpr ⟨.cancelSource key, requested, rfl⟩) owned)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
