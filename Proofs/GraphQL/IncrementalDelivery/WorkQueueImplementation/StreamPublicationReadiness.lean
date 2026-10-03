import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamProducerReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationSafety

/-! Actual publication readiness reuses producer support and derives cancellation safety.
The arbitrary-cut stream equivalence remains available independently of owner health.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact item provenance supplies the stream descriptor and its sole owner
-----------------------------------------------------------------------------------------

/-- An item task's owner is its stream, with the same structural producer as that stream.
Witness: object occurrences cannot have item payloads; the item location supplies NodeAt.
No generated-ref assumption is needed for this structural projection.
-/
theorem itemTask_owner_nodeAt {work occurrence owners producer stream result}
    (known : TaskAt work occurrence owners producer (.item stream result))
    : owners = [stream.ref]
      ∧ ∃ dependencies, NodeAt work stream .stream dependencies producer := by
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, value, children, enclosing, located, _, impossible⟩ := known
      cases impossible
  | item address index =>
      obtain ⟨node, items, enclosing, value, children, located, _, owner, payload⟩ := known
      cases payload
      exact ⟨owner, enclosing, address, items, located⟩

/-- For a fresh ordered item, producer support leaves exactly the cancellation clause.
Witness: the item's exact stream descriptor instantiates producer publication; the prior
ordinal supplies CanPublish's predecessor clause. The failure-cut list is arbitrary and
is neither dropped nor assumed valid, so this does not discharge cancellation safety.
-/
theorem itemTask_canPublish_iff_not_cancelled
    {work occurrence owners producer stream result} {matching : PublicationMatching}
    {before : List Execution.WorkQueueEvent}
    (known : TaskAt work occurrence owners producer (.item stream result))
    (fresh : ¬Published matching before occurrence)
    (support
      : ∀ dependencies,
          NodeAt work stream .stream dependencies producer
          → ∀ source, producer = some source → Published matching before source)
    (ordered
      : ∀ address first second,
          occurrence = .item address second
          → first < second
          → Published matching before (.item address first))
    (failures : FailureCuts)
    : CanPublish work matching before failures occurrence producer
      ↔ ¬TaskCancelled work matching before failures occurrence := by
  constructor
  · exact fun ready => ready.2.1
  · intro uncancelled
    obtain ⟨_, dependencies, located⟩ := itemTask_owner_nodeAt known
    refine ⟨fresh, uncancelled, support dependencies located, ?_⟩
    cases occurrence with
    | executionGroup => trivial
    | item address index =>
        cases index with
        | zero => trivial
        | succ index => exact ordered address index (index + 1) rfl (by omega)

-----------------------------------------------------------------------------------------
-- Reuse the actual-output matching without supplying stream metadata separately
-----------------------------------------------------------------------------------------

/-- Every actual item publication satisfies all CanPublish clauses except cancellation.
Witness: retain the common matching's freshness/order and use exact item provenance to
recover the stream's sole owner and producer. Prior notice support gives that producer's
publication. The equivalence keeps any supplied failure cuts; it is not full admission.
-/
theorem createWorkQueue_runNormalized_streamPublicationReadinessMatching
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index))
        ∧ (∀ index stream values groups streams,
            atoms[index]? = some (.streamValues stream values groups streams)
            → ∃ value producer,
                values = [value]
                ∧ TaskAt work (matching index) [stream.ref] producer
                    (.item stream (.ok (value.item, value.errors)))
                ∧ ∀ failures,
                    CanPublish work matching (atoms.take index) failures (matching index)
                      producer
                    ↔ ¬TaskCancelled work matching (atoms.take index) failures
                        (matching index)) := by
  obtain ⟨matching, batching, values, _, references⟩ :=
    createWorkQueue_runNormalized_streamProducerReadinessMatching generated valid started
  refine ⟨matching, batching, ?_, ?_⟩
  · intro index event atEvent value
    exact ⟨(values index event atEvent value).1, (values index event atEvent value).2.1⟩
  · intro index stream items groups streams atEvent
    obtain ⟨source, fresh, ordered⟩ := values index _ atEvent trivial
    cases items with
    | nil => cases source
    | cons item rest =>
        cases rest with
        | cons next tail => cases source
        | nil =>
            obtain ⟨owners, producer, known⟩ := source
            have owner := (itemTask_owner_nodeAt known).1
            refine ⟨item, producer, rfl, owner ▸ known, ?_⟩
            intro failures
            apply itemTask_canPublish_iff_not_cancelled known fresh _ ordered failures
            intro dependencies located source same
            exact references index _ atEvent stream dependencies producer
              List.mem_cons_self located source same

-----------------------------------------------------------------------------------------
-- Owner health and producer support replace a separate publication-cancellation proof
-----------------------------------------------------------------------------------------

/-- The actual mixed matching yields CanPublish once its publication support is proved.
Witness: retain exact provenance, freshness, and item order from normalized replay, then
derive cancellation exclusion with PublicationSupport.canPublish. The failure cuts need
only actual failed payloads here, not an already-licensed FailureWitness. Support remains
a local refinement obligation, never a new host-source or public Conformance premise.
-/
theorem createWorkQueue_runNormalized_supportedPublicationReadinessMatching
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index))
        ∧ ∀ failures,
            (∀ cut occurrence,
              (cut, occurrence) ∈ failures
              → ∃ owners producer payload,
                  TaskAt work occurrence owners producer payload
                  ∧ payload.failure.isSome = true)
            → PublicationSupport work matching atoms failures
            → ∀ index event,
                atoms[index]? = some event
                → IsValue event
                → ∀ owners producer payload,
                    TaskAt work (matching index) owners producer payload
                    → CanPublish work matching (atoms.take index) failures
                        (matching index) producer := by
  obtain ⟨matching, batching, values, _, _⟩ :=
    createWorkQueue_runNormalized_streamProducerReadinessMatching generated valid started
  refine ⟨matching, batching, ?_, ?_⟩
  · exact fun index event selected value =>
      ⟨(values index event selected value).1, (values index event selected value).2.1⟩
  · intro failures failedPayloads support index event selected value owners producer payload known
    exact support.canPublish failedPayloads selected value known
      (values index event selected value).2.1 (values index event selected value).2.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
