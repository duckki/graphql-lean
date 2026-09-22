import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents

/-! Source-side task settlement ledgers, separate from executable queue bookkeeping. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Only successful execution-group tasks change the group settlement ledger.
Stream items settle separately and never decrement group pending counts. -/
def GraphEvent.groupSuccesses : GraphEvent → List Occurrence
  | .taskSuccess occurrence _ => [occurrence]
  | _ => []

/-- Failed execution-group tasks enlarge the queue-local failure list. -/
def GraphEvent.groupFailures : GraphEvent → List Occurrence
  | .taskFailure occurrence _ => [occurrence]
  | _ => []

/-- Successful execution-group settlements are stored newest first to match
the local pending-count update lemma. -/
def GraphEvent.groupSettlements (events : List GraphEvent) : List Occurrence :=
  (events.flatMap GraphEvent.groupSuccesses).reverse

/-- Failed execution-group settlements use the same newest-first convention. -/
def GraphEvent.failureSettlements (events : List GraphEvent) : List Occurrence :=
  (events.flatMap GraphEvent.groupFailures).reverse

/-- Every successful group-task settlement is one of the source's task
identities, even though stream-item identities are omitted from this ledger. -/
theorem GraphEvent.groupSettlements_subsetIdentities (events : List GraphEvent)
    : (GraphEvent.groupSettlements events).Subset
        (events.flatMap (fun event => event.identities.1)) := by
  intro occurrence member
  have recorded : occurrence ∈ events.flatMap GraphEvent.groupSuccesses := by
    simpa [GraphEvent.groupSettlements] using member
  obtain ⟨event, eventMember, successMember⟩ := List.mem_flatMap.mp recorded
  have identity : occurrence ∈ event.identities.1 := by
    cases event <;> simp_all [GraphEvent.groupSuccesses, GraphEvent.identities]
  exact List.mem_flatMap.mpr ⟨event, eventMember, identity⟩

/-- Extending the event prefix prepends exactly that event's group-task
settlements and failures to the two proof-side ledgers. -/
theorem GraphEvent.groupSettlements_append (before : List GraphEvent) (event : GraphEvent)
    : GraphEvent.groupSettlements (before ++ [event])
      = event.groupSuccesses ++ GraphEvent.groupSettlements before := by
  cases event <;> simp [GraphEvent.groupSettlements, GraphEvent.groupSuccesses,
    List.flatMap_append, List.reverse_append]

/-- Appending an event records exactly its task failure, newest first.
Witness: event case analysis and list reversal over concatenation. -/
theorem GraphEvent.failureSettlements_append (before : List GraphEvent)
    (event : GraphEvent)
    : GraphEvent.failureSettlements (before ++ [event])
      = event.groupFailures ++ GraphEvent.failureSettlements before := by
  cases event <;> simp [GraphEvent.failureSettlements, GraphEvent.groupFailures,
    List.flatMap_append, List.reverse_append]

/-- Concatenated input lists concatenate their failure ledgers newest segment first.
Witness: flat-map distributes over append and reversing swaps the two segments.
-/
theorem GraphEvent.failureSettlements_append_list (before after : List GraphEvent)
    : GraphEvent.failureSettlements (before ++ after)
      = GraphEvent.failureSettlements after ++ GraphEvent.failureSettlements before := by
  simp [GraphEvent.failureSettlements, List.flatMap_append, List.reverse_append]

/-- Every source failure in the object-settlement inventory has its fixed failed payload.
Witness: source-prefix induction; only taskFailure extends this existing queue ledger.
-/
theorem ValidGraphEvents.failureSettlements_known {work events}
    (valid : ValidGraphEvents work events)
    : ∀ occurrence ∈ GraphEvent.failureSettlements events,
        ∃ owners producer path errors,
          TaskAt work occurrence owners producer (.object path (.error errors)) := by
  induction valid with
  | nil => simp [GraphEvent.failureSettlements]
  | @append before event valid matching fresh ready ih =>
      rw [GraphEvent.failureSettlements_append]
      cases event with
      | taskSuccess | streamItems | streamSuccess | streamFailure => exact ih
      | taskFailure occurrence errors =>
          intro task member
          rcases List.mem_cons.mp member with same | earlier
          · subst task
            obtain ⟨owners, producer, path, known⟩ := matching
            exact ⟨owners, producer, path, errors, known⟩
          · exact ih task earlier

/-- Record a processed object-task outcome; stream identities need no group-counter token.
This list update is proof notation only, not executable queue state or a source policy.
-/
def GraphEvent.recordTaskOutcome (event : GraphEvent) (settled : List Occurrence)
    : List Occurrence :=
  match event with
  | .taskSuccess occurrence _ | .taskFailure occurrence _ => occurrence :: settled
  | _ => settled

/-- All processed execution-group outcomes, newest first, including failures.
This proof ledger omits stream items, which never decrement group counters.
-/
def GraphEvent.taskSettlements (events : List GraphEvent) : List Occurrence :=
  (events.flatMap (fun event => event.groupSuccesses ++ event.groupFailures)).reverse

/-- Recording one more event agrees with the all-outcomes source projection.
Witness: concatenate its singleton task outcome and reverse the chronological list.
-/
theorem GraphEvent.taskSettlements_append (before : List GraphEvent) (event : GraphEvent)
    : GraphEvent.taskSettlements (before ++ [event])
      = event.recordTaskOutcome (GraphEvent.taskSettlements before) := by
  cases event <;> simp [GraphEvent.taskSettlements, GraphEvent.groupSuccesses,
    GraphEvent.groupFailures, GraphEvent.recordTaskOutcome, List.flatMap_append]

/-- An all-outcomes token is exactly a successful or failed group-task settlement.
Witness: membership in the two source projections; ordering is irrelevant to membership.
-/
theorem GraphEvent.mem_taskSettlements {events : List GraphEvent}
    {occurrence : Occurrence}
    : occurrence ∈ GraphEvent.taskSettlements events
      ↔ occurrence ∈ GraphEvent.groupSettlements events
        ∨ occurrence ∈ GraphEvent.failureSettlements events := by
  simp only [GraphEvent.taskSettlements, GraphEvent.groupSettlements,
    GraphEvent.failureSettlements, List.mem_reverse, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨event, member, success | failure⟩
    · exact Or.inl ⟨event, member, success⟩
    · exact Or.inr ⟨event, member, failure⟩
  · rintro (⟨event, member, success⟩ | ⟨event, member, failure⟩)
    · exact ⟨event, member, Or.inl success⟩
    · exact ⟨event, member, Or.inr failure⟩

/-- Both successful and failed task tokens are source settlement identities.
Witness: event case analysis, independent of source validity or queue state.
-/
theorem GraphEvent.taskSettlements_subsetIdentities (events : List GraphEvent)
    : (GraphEvent.taskSettlements events).Subset
        (events.flatMap (fun event => event.identities.1)) := by
  intro occurrence member
  obtain ⟨event, eventMember, token⟩ := List.mem_flatMap.mp (List.mem_reverse.mp member)
  apply List.mem_flatMap.mpr
  refine ⟨event, eventMember, ?_⟩
  cases event <;> simp_all [GraphEvent.groupSuccesses, GraphEvent.groupFailures,
    GraphEvent.identities]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
