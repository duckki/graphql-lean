import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamItemSafety

/-! Arbitrarily nested item-produced streams inherit historical cancellation safety. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A structural fragment of producer ancestry, not additional scheduler state
-----------------------------------------------------------------------------------------

/-- An item's finite producer chain contains only stream items, and each stream has no
defer dependencies. This proof-only fragment includes root items and arbitrary nesting
through item values. Other work, including deferred children and failures, is unrestricted.
-/
inductive ItemLineage (work : Execution.Work) : Occurrence → Prop where
  | step {address ordinal stream result producer}
    (known
      : TaskAt work (.item address ordinal) [stream.key] producer (.item stream result))
    (located : NodeAt work stream .stream [] producer)
    (parents : ∀ source, producer = some source → ItemLineage work source)
    : ItemLineage work (.item address ordinal)

/-- A normalized stream action references its own stream key.
Witness: inspect the three stream constructors; other events have no stream action.
-/
theorem streamAction_reference {event key closing}
    (action : streamAction event = some (key, closing))
    : key ∈ streamReferenceKeys event := by
  cases event <;> simp_all [streamAction, streamReferenceKeys]

-----------------------------------------------------------------------------------------
-- Induction follows actual successful producers and keeps all mixed failure cuts
-----------------------------------------------------------------------------------------

/-- A published item with item-only ancestry is safe under a full mixed failure inventory.
Witness: induct on its structural producer chain. Actual stream-reference support locates
the producer's publication, giving fixed success and inductive safety. Stream order and
the empty dependency list then supply safety at this item's own publication boundary.
No `Explains`, `FailureWitness`, or safety of unrelated object publications is assumed.
-/
theorem ItemLineage.published_safe_mixed
    {work events streamCuts objectCuts failures matching occurrence}
    (lineage : ItemLineage work occurrence)
    (cuts : StreamFailureCuts work events streamCuts)
    (partition : failures.Perm (streamCuts ++ objectCuts))
    (objects
      : ∀ entry ∈ objectCuts,
          ∃ owners producer path count,
            TaskAt work entry.2 owners producer (.object path (.error count)))
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (exactValues
      : ∀ index event,
          events[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (ready
      : ∀ index event,
          events[index]? = some event
          → ∀ stream dependencies producer,
              stream.key ∈ streamReferenceKeys event
              → NodeAt work stream .stream dependencies producer
              → ∀ source,
                  producer = some source → Published matching (events.take index) source)
    (published : Published matching events occurrence)
    : ¬TaskCancelled work matching events failures occurrence := by
  induction lineage with
  | @step address ordinal stream result producer known located parents ih =>
      obtain ⟨index, event, selected, value, matched⟩ := published
      have source := matched ▸ exactValues index event selected value
      have reference := streamAction_reference
        (source.itemOwner_action ⟨producer, .item stream result, known⟩ List.mem_cons_self)
      have parentPublished (parent : Occurrence) (same : producer = some parent)
          : Published matching events parent := by
        obtain ⟨position, prior, _, atPrior, isValue, matched⟩ :=
          (ready index event selected stream [] producer reference located parent same).before
        exact ⟨position, prior, atPrior, isValue, matched⟩
      apply cuts.item_safe_mixed partition objects generated failedPayloads ordered
        selected value matched source located known _ _ (.inl rfl)
      · intro parent same
        obtain ⟨position, prior, atPrior, isValue, matched⟩ := parentPublished parent same
        exact matched ▸ (exactValues position prior atPrior isValue).succeeds
      · intro parent same
        exact ih parent same (parentPublished parent same)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
