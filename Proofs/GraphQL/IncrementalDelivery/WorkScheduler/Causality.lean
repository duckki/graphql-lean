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
theorem NodeFailed.groupParent {work failed node parents birth key}
    (known : NodeAt work node .group parents birth) (parent : key ∈ parents)
    (failure : NodeFailed work failed key)
    : NodeFailed work failed node.key :=
  Causality.NodeFailed.groupParent ⟨node, birth, known, rfl⟩ parent failure

/-- A stream loses all nonempty dependencies, by the stream-parent causal rule. -/
theorem NodeFailed.streamParents {work failed node parents birth}
    (known : NodeAt work node .stream parents birth) (nonempty : parents ≠ [])
    (failures : ∀ key ∈ parents, NodeFailed work failed key)
    : NodeFailed work failed node.key :=
  Causality.NodeFailed.streamParents ⟨node, birth, known, rfl⟩ nonempty failures

/-- All descriptor producers must be unavailable, including repeated-key descriptors. -/
theorem NodeFailed.producers {work failed node kind parents birth}
    (known : NodeAt work node kind parents birth)
    (noRoot
      : ∀ other otherKind otherParents,
          NodeAt work other otherKind otherParents none → other.key ≠ node.key)
    (cancelled
      : ∀ other otherKind otherParents parent,
          NodeAt work other otherKind otherParents (some parent)
          → other.key = node.key
          → parent ∉ failed
          → TaskCancelled work failed parent)
    : NodeFailed work failed node.key := by
  refine Causality.NodeFailed.producers ⟨birth, node, kind, parents, known, rfl⟩ ?_ ?_
  · rintro ⟨other, otherKind, otherParents, located, same⟩
    exact noRoot other otherKind otherParents located same
  · rintro parent ⟨other, otherKind, otherParents, located, same⟩ notFailed
    exact cancelled other otherKind otherParents parent located same notFailed

/-- Losing every nonempty owner cancels a task, by packing its contributing keys. -/
theorem TaskCancelled.owners {work failed occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload) (nonempty : owners ≠ [])
    (failures : ∀ key ∈ owners, NodeFailed work failed key)
    : TaskCancelled work failed occurrence :=
  Causality.TaskCancelled.owners ⟨producer, payload, known⟩ nonempty failures

/-- A failed producer cancels its actual child, witnessed by its producer descriptor. -/
theorem TaskCancelled.producerFailed {work failed occurrence owners parent payload}
    (known : TaskAt work occurrence owners (some parent) payload)
    (failure : parent ∈ failed)
    : TaskCancelled work failed occurrence :=
  Causality.TaskCancelled.producerFailed ⟨owners, payload, known⟩ failure

/-- Producer cancellation propagates to a child, by the finite causal derivation. -/
theorem TaskCancelled.producerCancelled {work failed occurrence owners parent payload}
    (known : TaskAt work occurrence owners (some parent) payload)
    (cancelled : TaskCancelled work failed parent)
    : TaskCancelled work failed occurrence :=
  Causality.TaskCancelled.producerCancelled ⟨owners, payload, known⟩ cancelled

end GraphQL.IncrementalDelivery.WorkScheduler
