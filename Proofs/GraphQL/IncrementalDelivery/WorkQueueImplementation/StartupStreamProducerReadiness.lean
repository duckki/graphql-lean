import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamProducerReadiness

/-! Actual startup stream references retain their producer's earlier publication. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial streams are producer-free. Every later reference inherits producer publication
from its strictly earlier notice, on the supplied matching and actual startup history.
-/
theorem ExecutedWork.startup_streamReference_producerPublished {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (startup : InitialStartup) (valid : ValidGraphEvents work batches.flatten)
    (matching : PublicationMatching)
    (notices
      : let atoms :=
          (((State.initialize (Work.fromExecution work) startup)).runNormalized
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
      : ((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    {stream dependencies producer source}
    (reference : stream.ref ∈ streamReferenceRefs event)
    (known : NodeAt work stream .stream dependencies producer)
    (hasProducer : producer = some source)
    : Published matching
        (((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms).take
          index) source := by
  have announced := (State.startup_runNormalized_atomicStreamReferences startup valid).atEvent
    atEvent reference
  rcases List.mem_append.mp announced with initial | earlier
  · rw [State.initializeWithStartup_initialStreams] at initial
    have absent := generated.initialStream_producerNone known initial
    rw [hasProducer] at absent
    cases absent
  · obtain ⟨carrier, member, ref⟩ := List.mem_flatMap.mp earlier
    obtain ⟨position, atPrefix⟩ := List.mem_iff_getElem?.mp member
    have bound : position < index := by
      have size := (List.getElem?_eq_some_iff.mp atPrefix).choose
      simp only [List.length_take] at size
      omega
    have atCarrier := (List.getElem?_take_of_lt bound).symm.trans atPrefix
    obtain ⟨child, sameRef, owners, occurrence, located, published⟩ :=
      (notices position carrier atCarrier).of_ref ref
    have sameProducer := generated.streamProducer_unique known located sameRef.symm
    have same := Option.some.inj (hasProducer.symm.trans sameProducer)
    subst source
    exact published_take_mono published (by omega)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
