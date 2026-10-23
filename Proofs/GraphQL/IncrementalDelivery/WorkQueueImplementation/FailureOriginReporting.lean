import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyFailureOwners

/-! Actual positive group reports propagate through canonical full defer ancestry. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A reported ref in a record's full chain reports that record as well.
Witness: equal refs have canonical equal dependency lists; strict ancestors use generated
transitivity. The record itself may be taskless or unannounced.
-/
theorem GroupFailureReported.inherit_chain {work events owner ancestors node dependencies}
    (reported : GroupFailureReported events owner ancestors)
    (generated : ExecutedWork work) (ownerKnown : GroupRecordAt work owner ancestors)
    (known : GroupRecordAt work node dependencies)
    (inChain : owner.ref ∈ node.ref :: dependencies)
    : GroupFailureReported events node dependencies := by
  rcases List.mem_cons.mp inChain with equal | above
  · obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
    have same : ancestors = dependencies := by
      rw [canonical owner ancestors ownerKnown, canonical node dependencies known, equal]
    obtain ⟨reporter, errors, positive, member, relation⟩ := reported
    exact ⟨reporter, errors, positive, member, by simpa only [equal, same] using relation⟩
  · exact reported.inherit generated known ownerKnown above

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
