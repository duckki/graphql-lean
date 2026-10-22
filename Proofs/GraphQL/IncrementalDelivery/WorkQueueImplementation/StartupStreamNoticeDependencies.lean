import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseOwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches

/-! Startup group-carried streams retain their actual releasing dependency. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every actual startup raw group carrier names a dependency of each carried stream.
Forwarded failure controls cannot create a successful carrier or release a stream.
-/
theorem State.rawBatchesWithStartup_streamDependencies {queue work}
    (generated : ExecutedWork work) (sound : State.GroupMembershipSound queue)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) (batches : List (List GraphEvent))
    (sources : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : StreamReleaseDependencies work (queue.rawBatches batches).2 := by
  have ordinary (more : List (List GraphEvent)) (current : State)
      (sound : current.GroupMembershipSound) (matching : current.RegisteredTasksMatch work)
      (links : current.ChildStreamsMatchWork work)
      (sources : ∀ event ∈ more.flatten, event.MatchesWork work)
      : StreamReleaseDependencies work (current.rawBatches more).2 := by
    induction more generalizing current with
    | nil => exact .nil work
    | cons batch rest ih =>
        have first : ∀ event ∈ batch, event.MatchesWork work :=
          fun event member => sources event (List.mem_append_left _ member)
        exact (current.handleGraphEvents_streamDependencies generated sound matching links
          batch first).append (ih _ (sound.handleGraphEvents batch)
            (matching.handleGraphEvents batch first) (links.handleGraphEvents batch first)
            (fun event member => sources event (List.mem_append_right _ member)))
  exact ordinary batches queue sound matching links sources

/-- Every actual atomic startup group carrier retains the contributing stream dependency.
The raw output, actual publisher and atomization all preserve that carrier's descriptors.
-/
theorem State.startup_runNormalized_atomicStreamReleaseDependencies {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      NormalizedStreamReleaseDependencies work
        ((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms) := by
  let initial := State.initialize (Work.fromExecution work) startup
  have owners := State.initializeWithStartup_taskOwnerFrame work startup
  have raw := State.rawBatchesWithStartup_streamDependencies generated owners.sound owners.matching
    (State.initializeWithStartup_childStreamsMatchWork _ startup work) inputs
    (fun event member => valid.event_matches member)
  dsimp only
  rw [State.runNormalized_rawBatches]
  intro group groups streams member
  obtain ⟨index, atAtom⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨position, atNormalized, _⟩ := publicationAtoms_groupSuccess_prefix _ atAtom
  obtain ⟨rawPosition, atRaw, _⟩ := IncrementalPublisher.normalizeBatch_groupSuccess _ _
    atNormalized
  exact raw group groups streams (List.mem_of_getElem? atRaw)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
