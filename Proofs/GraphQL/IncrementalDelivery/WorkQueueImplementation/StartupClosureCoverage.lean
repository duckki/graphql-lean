import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationBlockOrder

/-! Object-free control suffixes preserve the source-handler closure ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue

/-- Object-free control suffixes impose no registration-order or ledger-offset constraint. -/
theorem BlocksFollowRegistrations.append_noObjectValues_iff {tasks published left right}
    (empty : right.flatMap Execution.WorkQueueEvent.objectValues = [])
    : BlocksFollowRegistrations tasks published (left ++ right)
      ↔ BlocksFollowRegistrations tasks published left := by
  rw [BlocksFollowRegistrations.append_iff]
  exact ⟨And.left, fun prior => ⟨prior, .of_noObjectValues _ _ empty⟩⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
