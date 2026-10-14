import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiveContributorReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedOwnerExistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StopTraversal
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningTaskOwnership

/-! Compose generated owner existence, root reachability, and the actual stop traversal
at one replay boundary. Native acquisition inventories remain independent obligations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode)

-----------------------------------------------------------------------------------------
-- A checked root composition separates replay coverage from acquired-lease representation
-----------------------------------------------------------------------------------------

/-- Stop reaches every generated stored task's abort and held-source targets.
No caller supplies a live owner, a healthy owner, or a root path. This is model-record
coverage, not a claim that native acquired leases are completely represented by records.
-/
def GeneratedBufferedStopCoverage : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ occurrence (node : TaskNode),
        let state := ((State.initialize work).runNormalized inputs).1
        state.queue.taskNode? occurrence = some node
        → node.value.isSome = true
        → (state.cancelTask occurrence).Subset state.cleanupTargets

/-- Checked conjecture-graph composition; the live-contributor leaf is proved separately.
Owner existence, membership links, traversal topology, and catalogue provenance are all
derived at the same actual history, rather than selected as unrelated witnesses.
-/
theorem GeneratedBufferedStopCoverage_of_liveContributors
    (coverage : GeneratedLiveContributorCoverage)
    : GeneratedBufferedStopCoverage := by
  intro work inputs generated valid started occurrence node
  dsimp only
  intro found stored
  let state := ((State.initialize work).runNormalized inputs).1
  have member := (ReferenceWorkQueue.State.taskNode?_some found).1
  have sameOccurrence := (ReferenceWorkQueue.State.taskNode?_some found).2
  have invariants := generatedReplay_taskInvariants generated inputs valid started
  obtain ⟨key, contributes, live⟩ :=
    generatedReplay_bufferedOwnersPresent generated valid started node member stored
  obtain ⟨group, foundGroup⟩ : ∃ group, state.queue.groupNode? key = some group := by
    cases lookup : state.queue.groupNode? key with
    | some group => exact ⟨group, rfl⟩
    | none => exact False.elim ((state.queue.groupNode?_eq_none_iff key).mp lookup live)
  have covered := coverage work inputs generated valid started node.task
    (invariants.1 node member) key contributes ⟨group, foundGroup⟩
  obtain ⟨root, active, path⟩ := covered
  have linked := invariants.2.2 node member stored group (List.mem_of_find?_eq_some foundGroup)
    ((ReferenceWorkQueue.State.groupNode?_ref foundGroup).symm ▸ contributes)
  exact GeneratedRootedStopCoverage_holds work inputs generated valid started root key
    group occurrence active path foundGroup (sameOccurrence ▸ linked)

/-- Generated replay discharges the last internal contributor-coverage leaf. -/
theorem GeneratedBufferedStopCoverage_holds : GeneratedBufferedStopCoverage :=
  GeneratedBufferedStopCoverage_of_liveContributors GeneratedLiveContributorCoverage_holds

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
