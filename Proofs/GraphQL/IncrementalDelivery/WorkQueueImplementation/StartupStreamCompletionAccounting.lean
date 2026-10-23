import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamSourceOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionAccounting

/-! Successful startup stream closure accounts for its exact source-item publications. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every contributing item is published strictly before actual successful stream closure.
Exact source completion supplies the finite item inventory; stream-action order places its
publications before the closure on the same matching. Failure cuts are arbitrary here.
-/
theorem ExecutedWork.startup_streamSuccess_accounted {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (matching : PublicationMatching)
    (exactValues
      : let atoms :=
          (((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (covered
      : ∀ occurrence ∈ (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
          Published matching
            ((((State.initialize (Work.fromExecution work) startup)).runNormalized
                batches).2.flatten.flatMap
              publicationAtoms) occurrence)
    {index stream}
    (atSuccess
      : ((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.streamSuccess stream))
    : ∀ failures,
        NodeAccounted work matching
          (((((State.initialize (Work.fromExecution work) startup)).runNormalized
              batches).2.flatten.flatMap
              publicationAtoms).take
            index) failures stream.ref := by
  have source := State.runNormalized_startup_streamCompletion_source
    (State.initialize (Work.fromExecution work) startup) batches
    (List.mem_of_getElem? atSuccess) rfl
  obtain ⟨⟨dependencies, producer, address, entries, located⟩, inventory⟩ :=
    valid.streamSuccess_itemInventory generated source
  intro failures occurrence owners known owner
  obtain ⟨ordinal, same, _⟩ := generated.streamContributor_ordinal located known owner
  subst occurrence
  exact Or.inr (published_item_before_streamSuccess exactValues
    (State.startup_runNormalized_atomicStreamActions_ordered startup valid) atSuccess known owner
    (covered _ (inventory _ owners known owner)))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
