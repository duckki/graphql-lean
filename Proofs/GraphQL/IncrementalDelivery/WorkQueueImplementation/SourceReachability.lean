import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationReadiness

/-! Valid source settlements have a structurally reachable chain of successful producers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A task is reachable if its producer is an earlier reachable successful source settlement.
Witness: root tasks use Reachable.root; produced tasks retain their exact source support
and the earlier settlement's fixed successful outcome. This is not publication readiness.
-/
theorem task_reachable_of_source_support {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (prior
      : ∀ occurrence ∈ events.flatMap GraphEvent.successes, Reachable work occurrence)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (supported
      : ∀ source, producer = some source → source ∈ events.flatMap GraphEvent.successes)
    : Reachable work occurrence := by
  cases producer with
  | none => exact .root ⟨owners, payload, known⟩
  | some source =>
      have settled := supported source rfl
      exact .child ⟨owners, payload, known⟩ (valid.successes_succeed settled) (prior source settled)

/-- Every successful settlement in a valid generated-work source prefix is reachable.
Witness: induction on source readiness, with exact task descriptors for object successes
and generated stream-producer uniqueness for item batches. This asserts no queue output.
-/
theorem ValidGraphEvents.successes_reachable {work events}
    (valid : ValidGraphEvents work events) (generated : ExecutedWork work)
    : ∀ occurrence ∈ events.flatMap GraphEvent.successes, Reachable work occurrence := by
  induction valid with
  | nil => simp
  | @append before event valid matching fresh ready ih =>
      intro occurrence member
      simp only [List.flatMap_append, List.flatMap_singleton, List.mem_append] at member
      rcases member with earlier | latest
      · exact ih occurrence earlier
      · cases event with
        | taskSuccess task result =>
            have same := List.mem_singleton.mp latest
            subst occurrence
            obtain ⟨owners, producer, payload, known, supported⟩ := ready
            exact task_reachable_of_source_support valid ih known supported
        | streamItems stream items =>
            obtain ⟨item, inItems, same⟩ := List.mem_map.mp latest
            subst occurrence
            obtain ⟨owners, producer, known, _⟩ := matching item inItems
            obtain ⟨address, entries, parent, dependencies, located, _, _, supported, _⟩ := ready
            obtain ⟨_, enclosing, descriptor⟩ := itemTask_owner_nodeAt known
            have sameParent := generated.streamProducer_unique descriptor (.stream located) rfl
            exact task_reachable_of_source_support valid ih known
              (fun source hasProducer => supported source (sameParent.symm.trans hasProducer))
        | taskFailure | streamSuccess | streamFailure => cases latest

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
