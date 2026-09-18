import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.HistoryPrefixes

/-! The maximal relational source implements the proposed queue contract. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

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

/-- An explicit valid initialization choice yields scheduler conformance for the given
nonempty work; witness: specialize maximal-source conformance, without selecting a run.
-/
theorem specificationScheduler_conforms (initialNotices) (work : Work)
    (initialized
      : work.size ≠ 0 → Initializes work (initialNotices work).1 (initialNotices work).2)
    : (specificationScheduler initialNotices).Conforms work := by
  intro nonempty
  exact specificationSource_conforms (initialized nonempty)

end GraphQL.IncrementalDelivery.WorkScheduler
