import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeSnapshotPublication

/-! Successful notice carriers retain their structural ancestor contributions at actual cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Both successful handler kinds publish notice ancestors before their exact carrier. -/
theorem OwnerPublicationFrame.noticeAncestor_contributor_before
    {queue work parents before published localPublications event index group groups
      streams child dependencies ref address owners producer payload}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task errors,
          (task, errors) ∈ available
          → (GraphEvent.taskFailure task errors).MatchesWork work)
    (covered : queue.ReplayClosuresCovered [event] localPublications available)
    (selected
      : (queue.handleGraphEvent event available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value) ∈ published
        ∨ (Occurrence.executionGroup address, value)
          ∈ localPublications.take
              (((queue.handleGraphEvent event available).2.1.take index).flatMap
                WorkQueueEvent.objectValues).length := by
  cases event with
  | taskSuccess occurrence result =>
      exact frame.taskSuccess_noticeAncestor_contributor_before generated canonical valid
        accepted available licensed covered selected noticed known ancestor task contributes
  | streamItems stream items =>
      exact frame.streamItems_noticeAncestor_contributor_before generated canonical valid
        accepted available licensed covered selected noticed known ancestor task contributes
  | taskFailure occurrence errors =>
      exact False.elim ((queue.cacheTaskFailures available).taskFailure_noGroupSuccess
        occurrence errors group groups streams (List.mem_of_getElem? selected))
  | streamSuccess stream =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member
  | groupFailure notice =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.groupFailure] at member
      split at member
      · cases member
      · split at member <;> simp at member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
