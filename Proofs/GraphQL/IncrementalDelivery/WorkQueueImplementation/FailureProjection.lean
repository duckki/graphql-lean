import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskSettlements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! The object failures accepted by each actual pre-settlement owner guard. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The object-failure token accepted by the handler's pre-settlement owner guard.
`queue` is the actual state before `event`; stream failures have a separate item inventory.
This proof-only projection records possible contributions, not licensed failure cuts.
-/
def State.objectFailureContribution (queue : State) : GraphEvent → List Occurrence
  | .taskFailure occurrence _ =>
      match queue.taskNode? occurrence with
      | none => []
      | some node => if queue.taskHasHealthyOwner node.task then [occurrence] else []
  | _ => []

/-- Contributing object failures in reverse settlement order along actual handler replay.
`events` is the supplied source prefix. The projection neither filters source inputs nor
changes execution; ignored settlements still update the replay state normally.
-/
def State.objectFailureContributions (queue : State) : List GraphEvent → List Occurrence
  | [] => []
  | event :: rest =>
      (queue.handleGraphEvent event).1.objectFailureContributions rest
      ++ queue.objectFailureContribution event

/-- Splitting source replay preserves the guard state at every recorded contribution.
Witness: list induction through the same executable handlers used by sequential replay.
-/
theorem State.objectFailureContributions_append (queue : State)
    (before after : List GraphEvent)
    : queue.objectFailureContributions (before ++ after)
      = (queue.replayGraphEvents before).objectFailureContributions after
        ++ queue.objectFailureContributions before := by
  induction before generalizing queue with
  | nil => simp [objectFailureContributions, replayGraphEvents]
  | cons event rest ih =>
      simp only [List.cons_append, objectFailureContributions, replayGraphEvents, ih,
        List.append_assoc, List.foldl_cons]

/-- Contributing object failures form an order-preserving subset of source failures.
Witness: each pre-settlement guard either keeps its one failure token or omits it;
induction composes those choices through the actual successive queue states.
-/
theorem State.objectFailureContributions_sublist (queue : State)
    (events : List GraphEvent)
    : (queue.objectFailureContributions events).Sublist
        (GraphEvent.failureSettlements events) := by
  induction events generalizing queue with
  | nil => exact .refl _
  | cons event rest ih =>
      have order : GraphEvent.failureSettlements (event :: rest)
          = GraphEvent.failureSettlements rest ++ event.groupFailures := by
        cases event <;> simp [GraphEvent.failureSettlements, GraphEvent.groupFailures]
      rw [objectFailureContributions, order]
      apply List.Sublist.append (ih (queue.handleGraphEvent event).1)
      cases event <;> simp only [objectFailureContribution, GraphEvent.groupFailures]
      all_goals try exact .refl _
      split
      · exact List.nil_sublist _
      · split
        · exact .refl _
        · exact List.nil_sublist _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
