import GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Retained contributor metadata is not abstract ownership evidence
-----------------------------------------------------------------------------------------

/-- Replacing a normalized value's contributor annotation preserves admission.
Witness: the singleton rule checks payload projections and derives ownership from Work.
This does not apply before publisher normalization, which uses the contributor list.
-/
theorem eventAllowed_groupValues_metadata
    (work initial matching before failures owner value groups)
    : EventAllowed work initial matching before failures
        (.groupValues owner [{ value with deliveryGroups := groups }])
      ↔ EventAllowed work initial matching before failures
          (.groupValues owner [value]) := by
  simp [EventAllowed]

/-- Retaining contributor metadata does not change a normalized wire entry.
Witness: the draft mapper reads only path, data, errors, and the selected owner.
-/
theorem getIncrementalEntry_metadata {m : Type → Type} [Monad m]
    (owner value groups) (idFor : DeliveryNode → m String)
    : getIncrementalEntry owner { value with deliveryGroups := groups } idFor
      = getIncrementalEntry owner value idFor :=
  rfl

end GraphQL.IncrementalDelivery.WorkQueueSemantics
