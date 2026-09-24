import GraphQL.IncrementalDelivery.WorkScheduler

/-! Introduction lemmas package structural evidence for the small causal kernel. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- A failed contributing task fails its owner, by packing the task descriptor. -/
theorem NodeFailed.task {work failed occurrence owners producer payload key}
    (known : TaskAt work occurrence owners producer payload)
    (owner : key ∈ owners) (finished : occurrence ∈ failed)
    : NodeFailed work failed key :=
  Causality.NodeFailed.task ⟨producer, payload, known⟩ owner finished

/-- One failed group dependency fails the group, by packing its node descriptor. -/
theorem NodeFailed.groupDependency {work failed node dependencies birth key}
    (known : NodeAt work node .group dependencies birth)
    (dependency : key ∈ dependencies)
    (failure : NodeFailed work failed key)
    : NodeFailed work failed node.key :=
  Causality.NodeFailed.groupDependency ⟨node, birth, known, rfl⟩ dependency failure

/-- A stream loses all nonempty dependencies, by the stream-dependency causal rule. -/
theorem NodeFailed.streamDependencies {work failed node dependencies birth}
    (known : NodeAt work node .stream dependencies birth) (nonempty : dependencies ≠ [])
    (failures : ∀ key ∈ dependencies, NodeFailed work failed key)
    : NodeFailed work failed node.key :=
  Causality.NodeFailed.streamDependencies ⟨node, birth, known, rfl⟩ nonempty failures

/-- All descriptor producers must be unavailable, including repeated-key descriptors. -/
theorem NodeFailed.producers {work failed node kind dependencies birth}
    (known : NodeAt work node kind dependencies birth)
    (noRoot
      : ∀ other otherKind otherDependencies,
          NodeAt work other otherKind otherDependencies none → other.key ≠ node.key)
    (cancelled
      : ∀ other otherKind otherDependencies producer,
          NodeAt work other otherKind otherDependencies (some producer)
          → other.key = node.key
          → producer ∉ failed
          → TaskCancelled work failed producer)
    : NodeFailed work failed node.key := by
  refine Causality.NodeFailed.producers ⟨birth, node, kind, dependencies, known, rfl⟩ ?_ ?_
  · rintro ⟨other, otherKind, otherDependencies, located, same⟩
    exact noRoot other otherKind otherDependencies located same
  · rintro producer ⟨other, otherKind, otherDependencies, located, same⟩ notFailed
    exact cancelled other otherKind otherDependencies producer located same notFailed

/-- Losing every nonempty owner cancels a task, by packing its contributing keys. -/
theorem TaskCancelled.owners {work failed occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload) (nonempty : owners ≠ [])
    (failures : ∀ key ∈ owners, NodeFailed work failed key)
    : TaskCancelled work failed occurrence :=
  Causality.TaskCancelled.owners ⟨producer, payload, known⟩ nonempty failures

/-- A failed producer cancels its actual child, witnessed by its producer descriptor. -/
theorem TaskCancelled.producerFailed {work failed occurrence owners producer payload}
    (known : TaskAt work occurrence owners (some producer) payload)
    (failure : producer ∈ failed)
    : TaskCancelled work failed occurrence :=
  Causality.TaskCancelled.producerFailed ⟨owners, payload, known⟩ failure

/-- Producer cancellation propagates to a child, by the finite causal derivation. -/
theorem TaskCancelled.producerCancelled {work failed occurrence owners producer payload}
    (known : TaskAt work occurrence owners (some producer) payload)
    (cancelled : TaskCancelled work failed producer)
    : TaskCancelled work failed occurrence :=
  Causality.TaskCancelled.producerCancelled ⟨owners, payload, known⟩ cancelled

end GraphQL.IncrementalDelivery.WorkScheduler
