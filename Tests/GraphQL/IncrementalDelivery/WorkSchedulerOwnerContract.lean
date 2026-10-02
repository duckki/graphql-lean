import GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Definition-level checks separating healthy support from effective wire ownership. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerOwnerContract
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

variable {work : Work} {initial owners : Keys} {matching : PublicationMatching}
  {before : List WorkQueueEvent} {failures : FailureCuts} {node supporter : DeliveryNode}

-----------------------------------------------------------------------------------------
-- Shared values may use a failed open ID, but still need healthy publication support
-----------------------------------------------------------------------------------------

/-- Healthy support retains exactly the earlier known/contributing/open/healthy conditions.
Witness: unfold the factored open-owner predicate and reassociate conjunctions.
-/
example
    : HealthyOpenOwner work initial matching before failures owners supporter
      ↔ (∃ kind dependencies producer, NodeAt work supporter kind dependencies producer)
        ∧ supporter.key ∈ owners
        ∧ Open initial before supporter.key
        ∧ ¬NodeFailed work matching before failures supporter.key := by
  simp only [HealthyOpenOwner, OpenOwner, and_assoc]

/-- A failed selected owner is permitted when another healthy contributor supplies support.
Witness: construct the revised owner certificate without requiring selected-owner health.
-/
example (selected : OpenOwner work initial before owners node)
    (healthy : HealthyOpenOwner work initial matching before failures owners supporter)
    (longest
      : ∀ other,
          OpenOwner work initial before owners other
          → other.path.length ≤ node.path.length)
    (failed : NodeFailed work matching before failures node.key)
    : PublicationOwner work initial matching before failures owners node
      ∧ NodeFailed work matching before failures node.key :=
  ⟨⟨selected, ⟨supporter, healthy⟩, longest⟩, failed⟩

/-- A wire owner cannot replace the requirement for some healthy publication supporter.
Witness: extract the existential healthy contributor from the owner certificate.
-/
example
    (unsupported
      : ¬∃ candidate,
          HealthyOpenOwner work initial matching before failures owners candidate)
    : ¬PublicationOwner work initial matching before failures owners node :=
  fun selected => unsupported selected.2.1

-----------------------------------------------------------------------------------------
-- Openness, longest-path selection, singleton health, and cancellation remain enforced
-----------------------------------------------------------------------------------------

/-- Selected IDs must still be announced and open, even when healthy support exists.
Witness: project openness from the selected contributor, not from the supporter.
-/
example (closed : ¬Open initial before node.key)
    : ¬PublicationOwner work initial matching before failures owners node :=
  fun selected => closed selected.1.2.2

/-- Longest-path selection considers all open contributors, without a health premise.
Witness: the selected owner's maximality compares directly with an open competitor.
-/
example (selected : PublicationOwner work initial matching before failures owners node)
    (other : DeliveryNode) (candidate : OpenOwner work initial before owners other)
    : other.path.length ≤ node.path.length :=
  selected.2.2 other candidate

/-- A singleton owner set still requires the selected key to be healthy.
Witness: any healthy supporter must have that sole key, as for a stream item.
-/
example
    (selected : PublicationOwner work initial matching before failures [node.key] node)
    : ¬NodeFailed work matching before failures node.key := by
  obtain ⟨candidate, available⟩ := selected.2.1
  have same := List.mem_singleton.mp available.1.2.1
  simpa only [same] using available.2

/-- Choosing a different effective owner does not authorize cancelled-task publication.
Witness: the unchanged publication predicate explicitly excludes cancellation.
-/
example {occurrence : Occurrence} {producer : Option Occurrence}
    (cancelled : TaskCancelled work matching before failures occurrence)
    : ¬CanPublish work matching before failures occurrence producer :=
  fun publish => publish.2.1 cancelled

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerOwnerContract
