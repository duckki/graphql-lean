import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamProducerMatching

/-! Prior stream notices transport producer publication to later stream references. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A key in a stream-notice projection has an actual descriptor satisfying the event's property.
Witness: only group-success and stream-value carriers add such keys, by mapping their nodes.
-/
theorem StreamNoticesSatisfy.of_key {property event key}
    (known : StreamNoticesSatisfy property event) (noticed : key ∈ streamNoticeKeys event)
    : ∃ stream, stream.key = key ∧ property stream := by
  cases event with
  | groupSuccess group groups streams =>
      obtain ⟨stream, member, same⟩ := List.mem_map.mp noticed
      exact ⟨stream, same, known stream member⟩
  | streamValues stream items groups streams =>
      obtain ⟨child, member, same⟩ := List.mem_map.mp noticed
      exact ⟨child, same, known child member⟩
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases noticed

/-- A referenced generated stream's structural producer has already published before that event.
Witness: references have strictly prior stream notices. Initial notices are producer-free;
later notices carry a producer publication no later than their carrier. Generated-key
uniqueness identifies that producer with any structural descriptor for the referenced key.
The supplied matching is unchanged; this proves producer support, not cancellation or Open.
-/
theorem createWorkQueue_runNormalized_streamReference_producerPublished
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (matching : PublicationMatching)
    (notices
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → StreamNoticesSatisfy
              (fun child =>
                ∃ dependencies occurrence,
                  NodeAt work child .stream dependencies (some occurrence)
                  ∧ Published matching (atoms.take (index + 1)) occurrence) event)
    {index event}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    {stream dependencies producer source}
    (reference : stream.key ∈ streamReferenceKeys event)
    (known : NodeAt work stream .stream dependencies producer)
    (hasProducer : producer = some source)
    : Published matching
        ((((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms).take
          index) source := by
  have announced := (createWorkQueue_runNormalized_atomicStreamReferences valid).atEvent
    atEvent reference
  rcases List.mem_append.mp announced with initial | earlier
  · have absent := generated.initialStream_producerNone known initial
    rw [hasProducer] at absent
    cases absent
  · obtain ⟨carrier, member, key⟩ := List.mem_flatMap.mp earlier
    obtain ⟨position, atPrefix⟩ := List.mem_iff_getElem?.mp member
    have bound : position < index := by
      have size := (List.getElem?_eq_some_iff.mp atPrefix).choose
      simp only [List.length_take] at size
      omega
    have atCarrier := (List.getElem?_take_of_lt bound).symm.trans atPrefix
    obtain ⟨child, sameKey, owners, occurrence, located, published⟩ :=
      (notices position carrier atCarrier).of_key key
    have sameProducer := generated.streamProducer_unique known located sameKey.symm
    have same := Option.some.inj (hasProducer.symm.trans sameProducer)
    subst source
    exact published_take_mono published (by omega)

-----------------------------------------------------------------------------------------
-- One matching jointly supports stream notices and all subsequent stream references
-----------------------------------------------------------------------------------------

/-- The joint actual-output matching supports every stream producer at notices and later references.
Witness: retain the existing common matching for fresh/ordered publications and both release
paths, then transport notice support through the independently proved strict-prior reference
invariant. Later references use their stream's structural descriptor, not payload equality.
Cancellation, notice freshness/openness, dependency satisfaction, owner eligibility, and
terminal accounting remain separate obligations before full Conformance.
-/
theorem createWorkQueue_runNormalized_streamProducerReadinessMatching
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
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ (∀ index event,
            atoms[index]? = some event
            → StreamNoticesSatisfy
                (fun child =>
                  ∃ dependencies occurrence,
                    NodeAt work child .stream dependencies (some occurrence)
                    ∧ Published matching (atoms.take (index + 1)) occurrence) event)
        ∧ (∀ index event,
            atoms[index]? = some event
            → ∀ stream dependencies producer,
                stream.key ∈ streamReferenceKeys event
                → NodeAt work stream .stream dependencies producer
                → ∀ source,
                    producer = some source
                    → Published matching (atoms.take index) source) := by
  obtain ⟨matching, batching, values, notices⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching generated valid started
  refine ⟨matching, batching, values, notices, ?_⟩
  intro index event atEvent stream dependencies producer reference known source hasProducer
  exact createWorkQueue_runNormalized_streamReference_producerPublished generated valid matching
    notices atEvent reference known hasProducer

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
