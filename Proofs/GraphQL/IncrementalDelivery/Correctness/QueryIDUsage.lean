import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryIdentity
import Proofs.GraphQL.IncrementalDelivery.Correctness.WireReferenceSafety

/-! Public open-ID safety derived from histories, stable allocation, and response grouping. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- Every work observation uses only announced, still-open IDs. Witness: work-reference
admission, injective mapper allocation, and grouping preserve reference legality.
-/
theorem WorkObservation.idUsageValid {response work complete result}
    (observed : WorkObservation response work complete result)
    : result.idUsageValid := by
  have identities := observed.uniqueIDs
  cases observed with
  | single empty => trivial
  | incremental groups streams batches nonempty batchNonempty admitted finished =>
      have refs := admitted.elim WorkScheduler.AdmissiblePrefix.openReferences
        WorkScheduler.AdmissibleRun.openReferences
      have grouped := replayResponse_groups response groups streams batches
      cases allocated
            : (getPendingEntry (m := StateM IDState) groups streams ensureID).run {} with
      | mk pending ids =>
          rw [allocated] at grouped
          obtain ⟨updates, flatten, replay⟩ := grouped
          have initialKeys := (getPendingEntry_of_eq allocated).2
          have well : Allocated ids := by
            simpa only [allocated]
              using getPendingEntry_allocated groups streams {} .empty
          have mapped := mappedTrace_references well initialKeys
            (.nil : Encodes ids [] []) refs
          rw [replay] at identities ⊢
          exact incremental_idUsageValid_of_references _ _
            (batched_references (flatten.symm ▸ mapped)) identities.1 identities.2

/-- Every query prefix satisfies public ID safety, by the query/history bridge. -/
theorem deliveryIDUsageValid_holds (schema : Schema) (operation : Operation)
    : deliveryIDUsageValid schema operation := by
  intro ObjectRef resolvers variables fuel source result observed
  exact queryObservation_property QueryResult.idUsageValid
    (fun _ _ _ h => h.idUsageValid) observed

/-- Every query patch has an earlier or same-response announcement, by ID safety. -/
theorem deliveryPatchesAnnounced_holds (schema : Schema) (operation : Operation)
    : deliveryPatchesAnnounced schema operation := by
  intro ObjectRef resolvers variables fuel source result observed
  exact patchesAnnounced_of_idUsageValid result
    (deliveryIDUsageValid_holds schema operation resolvers variables fuel source result observed)

end GraphQL.IncrementalDelivery.Correctness
