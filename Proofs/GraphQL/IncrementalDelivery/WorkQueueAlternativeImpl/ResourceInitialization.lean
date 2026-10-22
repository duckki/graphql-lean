import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.TerminalResourceInvariant
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConstructorInitialization

/-! Initialize the record invariant from immutable identities of independently acquired
producer-free work. No complete native acquisition inventory is inferred from descriptors.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence TaskAt NodeAt)

-----------------------------------------------------------------------------------------
-- Native initial identities are structural, not desired record locations
-----------------------------------------------------------------------------------------

/-- Initial independently queue-owned leases map to producer-free Work identities.
This asks for no endpoint, membership, live owner, cleanup effect, or inventory completeness.
-/
def InitialResourcesMatchWork (work : Work) (resources : ResourceState) : Prop :=
  (∀ occurrence,
    resources (.task occurrence) = .owned .queue
    → ∃ address owners payload,
        occurrence = .executionGroup address ∧ TaskAt work occurrence owners none payload)
  ∧ (∀ key,
      resources (.stream key) = .owned .queue
      → ∃ source dependencies,
          source.ref = key ∧ NodeAt work source .stream dependencies none)

/-- Every generated producer-free computation has an actual initial membership.
Nonempty owners, registration, pruning and live membership come from original proofs.
-/
theorem generatedInitial_taskRepresented {work address owners payload}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (known : TaskAt work (.executionGroup address) owners none payload)
    : RecordTargetRepresented (State.initialize work).queue
        (.task (.executionGroup address)) := by
  rw [State.initialize_queue]
  obtain ⟨task, registered, same, groups⟩ := ReferenceWorkQueue.TaskAt.executionGroup_initial_registered known
  obtain ⟨key, contributes⟩ := List.exists_mem_of_ne_nil _ (generated.taskOwners_nonempty known)
  obtain ⟨group, live, keyEq, linked⟩ := ReferenceWorkQueue.createWorkQueue_healthyRegisteredTaskAccounting work generated
    task registered (by simp) key (groups.symm ▸ contributes) (fun failure => failure.nonempty rfl)
  have found := (ReferenceWorkQueue.createWorkQueue_groupRefsUnique (ReferenceWorkQueue.Work.fromExecution work)).groupNode?_of_mem live
  exact .task found (same ▸ linked)
    (ReferenceWorkQueue.createWorkQueue_taskRejections
      (ReferenceWorkQueue.Work.fromExecution work)
      (fun occurrence _ => occurrence ≠ .executionGroup address)).unrejected_lookup

-----------------------------------------------------------------------------------------
-- The initial invariant is constructed, not assumed from native stop coverage
-----------------------------------------------------------------------------------------

/-- Initial structural correspondence supplies real task/source locations and an empty
processed-task history. It neither acquires leases nor claims all native leases were listed.
-/
def GeneratedInitialResourcesRepresented : Prop :=
  ∀ work,
    ReferenceWorkQueue.ExecutedWork work
    → ∀ resources,
        InitialResourcesMatchWork work resources
        → QueueResourcesRepresented (State.initialize work).queue [] resources

/-- Root task accounting and unconditional stream announcement construct initialization. -/
theorem GeneratedInitialResourcesRepresented_holds
    : GeneratedInitialResourcesRepresented := by
  intro work generated resources identities
  constructor
  · intro occurrence owned
    obtain ⟨address, owners, payload, same, known⟩ := identities.1 occurrence owned
    exact ⟨same.symm ▸ generatedInitial_taskRepresented generated (same ▸ known), by simp⟩
  · intro key owned
    obtain ⟨source, dependencies, same, known⟩ := identities.2 key owned
    have noticed := ReferenceWorkQueue.NodeAt.stream_initial_notice known
    have active := ReferenceWorkQueue.createWorkQueue_initialStreams_active _ noticed
    rw [State.initialize_queue]
    exact .activeStream (same ▸ active)

-----------------------------------------------------------------------------------------
-- Safe inter-input resource observations create no queue-owned lease
-----------------------------------------------------------------------------------------

/-- Between dispatches, producer acquisition and completion/cleanup observations are
allowed. Queue acquisition belongs to initialization; adoption belongs to actual dispatch.
This is a proof trace category, not a new host event-source or fairness condition.
-/
def InterInputResourceAction : ResourceAction → Prop
  | .acquire _ (.producer _) | .requestCleanup _ | .settleCleanup _ | .finishNormally _ =>
      True
  | .acquire _ .queue | .adopt _ _ => False

/-- A legal inter-input step cannot create queue ownership, regardless of its target. -/
theorem ResourceStep.interInput_owned_origin {before action after}
    (step : ResourceStep before action after) (external : InterInputResourceAction action)
    (target : CleanupTarget) (owned : after target = .owned .queue)
    : before target = .owned .queue := by
  cases step with
  | acquire selected owner fresh =>
      cases owner with
      | queue => cases external
      | producer occurrence =>
          by_cases same : target = selected
          · subst target
            simp [ResourceState.set] at owned
          · simpa only [ResourceState.set, same, ↓reduceIte] using owned
  | adopt => cases external
  | request selected owner initial =>
      by_cases same : target = selected
      · subst target; simp [ResourceState.set] at owned
      · simpa only [ResourceState.set, same, ↓reduceIte] using owned
  | settle selected owner initial =>
      by_cases same : target = selected
      · subst target; simp [ResourceState.set] at owned
      · simpa only [ResourceState.set, same, ↓reduceIte] using owned
  | finish selected owner initial =>
      by_cases same : target = selected
      · subst target; simp [ResourceState.set] at owned
      · simpa only [ResourceState.set, same, ↓reduceIte] using owned

/-- Any independently supplied legal inter-input trace preserves current record and
pending-history evidence. It does not construct callback/acquisition completeness.
-/
theorem QueueResourcesRepresented.interInputReplay {queue settled before actions after}
    (represented : QueueResourcesRepresented queue settled before)
    (replay : ResourceReplay before actions after)
    (external : ∀ action ∈ actions, InterInputResourceAction action)
    : QueueResourcesRepresented queue settled after := by
  induction replay with
  | nil => exact represented
  | @cons before action middle actions after step rest ih =>
      have origin := step.interInput_owned_origin (external action List.mem_cons_self)
      have next : QueueResourcesRepresented queue settled middle :=
        ⟨fun occurrence owned => represented.1 occurrence (origin _ owned),
          fun key owned => represented.2 key (origin _ owned)⟩
      exact ih next (fun action member => external action (List.mem_cons_of_mem _ member))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
