import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupPublicationFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchedPublicationProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchedPublisherRegistry

/-! Startup queues retain ordinary raw batch replay and exact publication provenance. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Any initialized queue normalizes its actual raw batches under its initial publisher. -/
theorem State.runNormalized_rawBatches (queue : State) (batches : List (List GraphEvent))
    : let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      = (publisher.normalizeBatch (queue.rawBatches batches).2).2.flatMap
          publicationAtoms :=
  (queue.sourceRunBlocks_agrees batches).2.symm.trans
    (queue.sourceRunBlocks_rawBatches _ batches)

/-- Every actual startup raw object uses a contributing release group. -/
theorem State.startup_rawBatches_publicationContributors {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      RawPublicationContributors (initial.rawBatches batches).2 := by
  have owners := State.initializeWithStartup_taskOwnerFrame work startup
  have initial :
      (State.initialize (Work.fromExecution work) startup).ContributorProvenance
      work := ⟨owners.matching, owners.sound, State.initializeWithStartup_storedValues _ startup _⟩
  exact (initial.rawBatches batches (fun _ member => valid.event_matches member)).2

/-- A startup raw object value has the exact successful source event, including its
contributor-bearing value. Equal response payloads never identify its task occurrence.
-/
theorem State.startup_rawBatches_valueSource {work batches group values value}
    (startup : InitialStartup) (valid : ValidGraphEvents work batches.flatten)
    (emitted
      : let initial := State.initialize (Work.fromExecution work) startup
        WorkQueueEvent.groupValues group values ∈ (initial.rawBatches batches).2)
    (member : value ∈ values)
    : ∃ occurrence result,
        GraphEvent.taskSuccess occurrence result ∈ batches.flatten
        ∧ result.value = value
        ∧ (GraphEvent.taskSuccess occurrence result).MatchesWork work := by
  let initial := State.initialize (Work.fromExecution work) startup
  obtain ⟨published, exactValues, inventory⟩ :=
    (State.initializeWithStartup_publicationInventory (Work.fromExecution work) startup).rawBatches
      batches valid
  have inValues : value ∈ published.map Prod.snd := by
    rw [exactValues]
    exact List.mem_flatMap.mpr ⟨_, emitted, member⟩
  obtain ⟨publication, selected, same⟩ := List.mem_map.mp inValues
  obtain ⟨result, supplied, stored⟩ := inventory.provenance publication
    (List.mem_append_right _ selected)
  exact ⟨publication.1, result, supplied, stored.trans same, valid.event_matches supplied⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
