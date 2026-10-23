import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeMetadata

/-! Actual startup notices retain exact stream descriptors from the original work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Synchronous group cleanup preserves the original registered stream descriptors. -/
theorem State.initializeWithStartup_streams (input : Work) (startup : InitialStartup)
    : (State.initialize input startup).streams = (State.initialize input).streams := by
  unfold State.initialize
  dsimp only [State.initialize]
  simp only [State.enqueueGroupFailures, State.startNewWork_streams]

/-- Every atomic startup stream notice names a structural node of the original work.
No owner openness, notice freshness, abstract admission or source fairness is assumed.
-/
theorem State.startup_runNormalized_atomicStreamNoticesLocated {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∀ event ∈ (initial.runNormalized batches).2.flatten.flatMap publicationAtoms,
        StreamNoticesSatisfy (StreamLocated work) event := by
  let initial := State.initialize (Work.fromExecution work) startup
  have registry : initial.StreamsSatisfy (StreamLocated work) := by
    intro stream member
    rw [State.initializeWithStartup_streams] at member
    exact ⟨[], none, (createWorkQueue_initialStreams_nodeAt work).1 stream member⟩
  have notices := registry.runWithPublisher_notices
    { active := initial.initialGroups ++ initial.initialStreams } batches
    (fun event member => (valid.event_matches member).childStreamsLocated)
  dsimp only
  intro event member
  obtain ⟨original, emitted, atom⟩ := List.mem_flatMap.mp member
  exact publicationAtoms_streamNoticesSatisfy original (notices original emitted) event
    atom

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
