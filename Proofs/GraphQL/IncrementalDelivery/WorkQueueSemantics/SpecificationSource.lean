import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.HistoryPrefixes

/-! The maximal relational source implements the proposed queue contract. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- Proof-only maximal queue for chosen initial notices. It retains every admitted
history and selects no future completion order. Invalid initialization is not repaired.
-/
def specificationSource (work : Work) (groups streams : List DeliveryNode) : WorkQueue :=
  {
    initialGroups := groups
    initialStreams := streams
    workEventStream :=
      {
        admissible := fun batches => ValidHistory work ⟨groups, streams, batches⟩
        finished := fun batches => AdmissibleRun work ⟨groups, streams, batches⟩
      }
  }

/-- Valid initial notices give a conforming maximal source. Witness: history prefix
closure, direct work admission, and the source's exact terminal-run predicate.
-/
theorem specificationSource_conforms {work groups streams}
    (initialized : Initializes work groups streams)
    : (specificationSource work groups streams).Conforms work := by
  refine ⟨⟨rfl, Or.inl initialized.emptyHistory⟩, ?_, fun _ h => h, ?_⟩
  · intro before after earlier admitted
    obtain ⟨suffix, rfl⟩ := earlier
    exact ValidHistory.prefix admitted
  · intro batches
    exact ⟨fun run => ⟨Or.inr run, run⟩, fun h => h.2⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
