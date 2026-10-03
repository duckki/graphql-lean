import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamReleaseCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncements

/-! Buffered child streams are released or retained while a contributing owner survives. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Track actual child notices independently of the occurrence-labelled value ledger
-----------------------------------------------------------------------------------------

/-- Each buffered child stream is announced or its exact producer and owner survive.
`events` is the actual output between `queue` and `next`. A chosen contributing owner
must initially be live and not be recorded as cancelled at the endpoint. This is derived
implementation evidence, not a condition imposed on the source or scheduler contract.
-/
def State.BufferedStreamsConserved (queue : State) (events : List WorkQueueEvent)
    (next : State)
    : Prop :=
  ∀ occurrence node value stream,
    queue.taskNode? occurrence = some node
    → node.value = some value
    → stream ∈ node.childStreams
    → ∀ owner ∈ node.task.groups.map Execution.DeliveryNode.ref,
        owner ∈ queue.groupNodes.map (fun group => group.group.node.ref)
        → owner ∉ next.cancelledGroups
        → stream ∈ events.flatMap rawStreamNoticeRefs
          ∨ (next.taskNode? occurrence = some node
              ∧ owner ∈ next.groupNodes.map (fun group => group.group.node.ref))

/-- An unchanged queue retains the exact buffered producer and live contributor.
Witness: the supplied lookup and owner membership; no notice is emitted.
-/
theorem State.BufferedStreamsConserved.refl (queue : State)
    : queue.BufferedStreamsConserved [] queue := by
  intro occurrence node value stream found stored linked owner contributes live uncancelled
  exact .inr ⟨found, live⟩

/-- Sequential conservation retains the same producer, linked stream, and chosen owner.
Witness: earlier notices persist; otherwise the retained lookup feeds the next certificate.
Monotone cancellation history transports the endpoint qualification to the first step.
-/
theorem State.BufferedStreamsConserved.append {queue middle next : State} {first later}
    (before : queue.BufferedStreamsConserved first middle)
    (after : middle.BufferedStreamsConserved later next)
    (cancelled : middle.cancelledGroups.Subset next.cancelledGroups)
    : queue.BufferedStreamsConserved (first ++ later) next := by
  intro occurrence node value stream found stored linked owner contributes live uncancelled
  rw [List.flatMap_append]
  rcases before occurrence node value stream found stored linked owner contributes live
      (fun member => uncancelled (cancelled member)) with noticed | retained
  · exact .inl (List.mem_append_left _ noticed)
  · rcases after occurrence node value stream retained.1 stored linked owner contributes
        retained.2 uncancelled with noticed | retained
    · exact .inl (List.mem_append_right _ noticed)
    · exact .inr retained

/-- Empty-publication owner conservation also retains every linked child stream.
Witness: the impossible empty publication branch leaves the exact node and owner intact.
-/
theorem State.BufferedStreamsConserved.of_emptyOwners {queue next : State}
    (conserved : queue.StoredOwnersConserved [] next) (events : List WorkQueueEvent)
    : queue.BufferedStreamsConserved events next := by
  intro occurrence node value stream found stored linked owner contributes live uncancelled
  have retained := conserved occurrence node value found stored owner contributes live uncancelled
  exact .inr (retained.resolve_left (by simp))

/-- Healthy retirement of a buffered contributor forces its attached stream's notice.
Witness: the conservation alternative cannot retain an owner absent from the endpoint.
-/
theorem State.BufferedStreamsConserved.retired_notice {queue next : State} {events}
    (conserved : queue.BufferedStreamsConserved events next)
    {occurrence node value stream owner}
    (found : queue.taskNode? occurrence = some node) (stored : node.value = some value)
    (linked : stream ∈ node.childStreams)
    (contributes : owner ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (live : owner ∈ queue.groupNodes.map (fun group => group.group.node.ref))
    (retired : owner ∉ next.groupNodes.map (fun group => group.group.node.ref))
    (uncancelled : owner ∉ next.cancelledGroups)
    : stream ∈ events.flatMap rawStreamNoticeRefs := by
  exact (conserved occurrence node value stream found stored linked owner contributes live
    uncancelled).resolve_right (fun retained => retired retained.2)

/-- Preparation may preserve a buffered-stream certificate through exact old lookups.
Witness: transport the same linked node and initial owner to the prepared state.
-/
theorem State.BufferedStreamsConserved.of_lookups {queue prepared next : State} {events}
    (conserved : prepared.BufferedStreamsConserved events next)
    (retained
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → prepared.taskNode? occurrence = some node)
    (refs : queue.GroupRefsIncluded prepared)
    : queue.BufferedStreamsConserved events next := by
  intro occurrence node value stream found stored linked owner contributes live uncancelled
  exact conserved occurrence node value stream (retained occurrence node value found stored)
    stored linked owner contributes (refs owner live) uncancelled

-----------------------------------------------------------------------------------------
-- Actual successful flushing supplies the release branch, not a guessed publication
-----------------------------------------------------------------------------------------

/-- A successful flush releases each selected buffered child or retains its whole producer.
Witness: complete child-stream selection handles selected memberships; an unselected lookup
survives unchanged, and stored-task links retain the chosen contributing group.
-/
theorem State.finishGroupSuccess_bufferedStreamsConserved {queue : State}
    (links : queue.StoredTaskLinks) (inventory : queue.ChildStreamInventory)
    (group : GroupNode) (present : group ∈ queue.groupNodes)
    : queue.BufferedStreamsConserved (queue.finishGroupSuccess group).2.1
        (queue.finishGroupSuccess group).1 := by
  intro occurrence node value stream found stored linked owner contributes live uncancelled
  classical
  by_cases selected : occurrence ∈ group.tasks
  · exact .inl ((queue.finishGroupSuccess_streamNotices group) ▸
      inventory.finishGroupSuccess_childRef_covered group selected found linked)
  · have retained := (queue.finishGroupSuccess_lookup_unselected group selected).trans found
    exact .inr ⟨retained, State.finishGroupSuccess_bufferedOwner_present links group present
      (State.taskNode?_some retained).1 (by simp [stored]) contributes live⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
