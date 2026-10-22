import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.ReportingWitness

/-! Reporting availability can precede causal acceptance, but never follow it.
The same occurrence supplies both witnesses without adding a second reporting entry.
-/

namespace GraphQL.IncrementalDelivery.Tests.CausalFailureAvailability
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-- A cached rejection supports a causal cut after another output has been emitted.
example (task : Occurrence) : CausalFailuresAvailable [(1, task)] [(0, task)] := by
  simp [CausalFailuresAvailable]

-- Equal cuts retain the previous contract's ordinary case.
example (task : Occurrence) : CausalFailuresAvailable [(1, task)] [(1, task)] := by
  simp [CausalFailuresAvailable]

-- Future availability cannot justify an earlier cancellation.
example (task : Occurrence) : ¬CausalFailuresAvailable [(0, task)] [(1, task)] := by
  simp [CausalFailuresAvailable]

-- An available rejection from another task cannot stand in for the causal occurrence.
example (task other : Occurrence) (distinct : task ≠ other)
    : ¬CausalFailuresAvailable [(1, task)] [(0, other)] := by
  simp [CausalFailuresAvailable, distinct]

-- Recording a new causal cut reuses reporting evidence already present in the inventory.
example (first second : Occurrence)
    : CausalFailuresAvailable ([(0, first)] ++ [(1, second)])
        [(0, first), (0, second)] := by
  have available : CausalFailuresAvailable [(0, first)] [(0, first), (0, second)] := by
    simp [CausalFailuresAvailable]
  exact available.record (by simp) (by decide : 0 ≤ 1)

end GraphQL.IncrementalDelivery.Tests.CausalFailureAvailability
