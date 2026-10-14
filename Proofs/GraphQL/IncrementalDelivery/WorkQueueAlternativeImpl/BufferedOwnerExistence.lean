import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerExistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshot
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulBufferRetention

/-! Generated stored-owner evidence at actual alternative replay and registration points. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Exact alternative replay and the next registration boundary
-----------------------------------------------------------------------------------------

/-- Every stored task in actual generated alternative replay retains a live owner. -/
theorem generatedReplay_bufferedOwnersPresent {work inputs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((State.initialize work).runNormalized inputs).1.queue.BufferedOwnersPresent := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · intro node member; cases member
  · exact generated.runNormalized_bufferedOwnersPresent inputs valid started

private theorem eagerRegistrationSnapshot_bufferedOwners
    {queue : ReferenceWorkQueue.State} {work settled}
    (owners : queue.BufferedOwnersPresent) (links : queue.StoredTaskLinks)
    (accounted : queue.PendingAccounting work settled) (event : GraphEvent)
    (matching : event.MatchesWork work)
    : (eagerRegistrationSnapshot queue event).BufferedOwnersPresent := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using owners
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false =>
              simpa only [eagerRegistrationSnapshot, found, healthy, Bool.false_eq_true,
                ↓reduceIte] using owners
          | true =>
              simp only [eagerRegistrationSnapshot, found, healthy, ↓reduceIte]
              exact (owners.putTaskNode { node with value := some result.value }
                (fun _ => ReferenceWorkQueue.taskHasHealthyOwner_present healthy)).integrate
                result.work (some occurrence)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte]
            using owners
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          exact (owners.prepareItems links accounted matching).1
  | taskFailure | streamSuccess | streamFailure => exact owners

/-- Each stored registration-snapshot task has a live contributor, including new adoption.
Neither owner existence nor contributor health is an additional input-source law.
-/
def GeneratedSnapshotBufferedOwners : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
        event).BufferedOwnersPresent

/-- Handler-preserved owner existence supplies the same actual registration snapshot. -/
theorem GeneratedSnapshotBufferedOwners_holds : GeneratedSnapshotBufferedOwners := by
  intro work inputs event generated valid started
  obtain ⟨earlier, matching, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have projection := generatedSnapshot_projection generated valid started
  have eager : (eagerRegistrationSnapshot
      ((State.initialize work).runNormalized inputs).1.queue event).BufferedOwnersPresent := by
    rw [State.runNormalized_initialize work inputs generated earlier started]
    simp only [State.fromReference]
    split
    · cases event with
      | streamItems =>
          simp only [eagerRegistrationSnapshot, State.clearRecords, List.contains_nil,
            Bool.false_eq_true, ↓reduceIte]
          intro node member; cases member
      | taskSuccess | taskFailure | streamSuccess | streamFailure =>
          intro node member; cases member
    · obtain ⟨settled, _, accounted⟩ := generated.runNormalized_pendingAccounting inputs earlier started
      exact eagerRegistrationSnapshot_bufferedOwners
        (generated.runNormalized_bufferedOwnersPresent inputs earlier started)
        (generated.runNormalized_storedTaskLinks inputs earlier started) accounted event matching
  have groups := congrArg (fun queue : ReferenceWorkQueue.State => queue.groupNodes.map
    (fun node => node.group.node.ref)) projection.core
  change (registrationSnapshot _ event).groupNodes.map (fun node => node.group.node.ref)
    = (eagerRegistrationSnapshot _ event).groupNodes.map (fun node => node.group.node.ref) at groups
  intro node member stored
  obtain ⟨owner, contributes, live⟩ := eager node (projection.nodes member) stored
  exact ⟨owner, contributes, groups.symm ▸ live⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
