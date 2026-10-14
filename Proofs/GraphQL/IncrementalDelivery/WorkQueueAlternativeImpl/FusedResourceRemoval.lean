import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRequests

/-! Construct compatible resource-request evidence from the actual fused removal endpoint.
No registration snapshot, output-driven failure observer or desired disposal premise is
used. Native acquisitions and asynchronous settlement remain separate observations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- Observe exactly the cleanup identities returned by this actual removal. Only leases
already owned by the queue receive requests; foreign/unacquired leases stay unchanged.
-/
def ResourceState.observeFusedRemoval (resources : ResourceState) (state : State)
    (root : Nat)
    : ResourceState × List ResourceAction :=
  resources.requestQueueCleanup (state.removeGroup root).2

/-- Exact actual-endpoint resource safety. One constructed history licenses every request
by an actual cleanup effect and retains or requests every initially queue-owned held source.
Cleanup-requested is not released, and no native acquisition inventory is manufactured.
-/
def FusedRemovalResourceSafety : Prop :=
  ∀ (state : State) (root : Nat) (resources : ResourceState),
    let reduced := state.removeGroup root
    let observed := resources.observeFusedRemoval state root
    ResourceReplay resources observed.2 observed.1
    ∧ (∀ action ∈ observed.2,
        ∃ effect ∈ reduced.2.flatMap CleanupTarget.effects,
          ∃ target, effect.cleanupStart? = some target ∧ action = .requestCleanup target)
    ∧ ∀ occurrence node key,
        state.queue.taskNode? occurrence = some node
        → key ∈ node.childStreams
        → resources (.stream key) = .owned .queue
        → reduced.1.queue.taskNode? occurrence = some node
          ∨ observed.1 (.stream key) = .cleanupRequested .queue

theorem FusedRemovalResourceSafety_holds : FusedRemovalResourceSafety := by
  intro state root resources
  refine ⟨resources.requestQueueCleanup_replay _, ?_, ?_⟩
  · intro action member
    obtain ⟨target, listed, same⟩ := resources.requestQueueCleanup_actions _ action member
    have labeled : target ∈ ((state.removeGroup root).2.flatMap CleanupTarget.effects).filterMap
        HostEffect.cleanupStart? := by
      rw [cleanupEffects_starts]
      exact listed
    obtain ⟨effect, emitted, identifies⟩ := List.mem_filterMap.mp labeled
    exact ⟨effect, emitted, target, identifies, same⟩
  · intro occurrence node key found held owned
    rcases (FusedRemovalSafety_holds state root []).2.2 occurrence node key found held with
      retained | requested
    · exact .inl retained
    · exact .inr (resources.requestQueueCleanup_owned _ _ requested owned)

/-- Observing this removal leaves every non-queue lease unchanged, including unadopted
producer suffixes and cleanup already requested by an earlier independent transition.
-/
theorem ResourceState.observeFusedRemoval_foreign (resources : ResourceState)
    (state : State) (root : Nat) (target : CleanupTarget)
    (foreign : resources target ≠ .owned .queue)
    : (resources.observeFusedRemoval state root).1 target = resources target :=
  resources.requestQueueCleanup_foreign _ target foreign

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
