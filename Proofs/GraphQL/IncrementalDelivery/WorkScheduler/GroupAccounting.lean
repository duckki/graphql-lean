import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.TaskReadiness

/-! Healthy accounted groups have a published contributor, even in mixed work.
This avoids assuming that cancellation of each individual task fails all its owners.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Cancellation under a healthy owner must come from the producer
-----------------------------------------------------------------------------------------

/-- A cancelled task with a healthy contributing owner has an unavailable producer.
Witness: invert cancellation; the all-owners-failed case contradicts the healthy owner.
The conclusion retains either actual producer failure or causal producer cancellation.
-/
theorem TaskCancelled.healthy_producer_unavailable
    {work failed occurrence owners producer payload key}
    (cancelled : TaskCancelled work failed occurrence)
    (known : TaskAt work occurrence owners producer payload) (member : key ∈ owners)
    (healthy : ¬NodeFailed work failed key)
    : ∃ parent,
        producer = some parent
        ∧ (parent ∈ failed ∨ TaskCancelled work failed parent) := by
  cases cancelled with
  | owners projected _ failures =>
      obtain ⟨birth, result, task⟩ := projected
      exact False.elim (healthy (failures key ((TaskAt.unique task known).1.symm ▸ member)))
  | producerFailed projected failure =>
      obtain ⟨otherOwners, result, task⟩ := projected
      exact ⟨_, (TaskAt.unique known task).2.1, Or.inl failure⟩
  | producerCancelled projected cancellation =>
      obtain ⟨otherOwners, result, task⟩ := projected
      exact ⟨_, (TaskAt.unique known task).2.1, Or.inr cancellation⟩

/-- Each group descriptor comes from a contributing deferred task with the same producer.
Witness: its structural deferred boundary; repeated descriptors remain visible.
-/
theorem NodeAt.group_task {work node parents producer}
    (known : NodeAt work node .group parents producer)
    : ∃ occurrence owners payload,
        TaskAt work occurrence owners producer payload ∧ node.key ∈ owners := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      exact ⟨_, _, _, .deferred located.toCurrent,
        List.mem_map_of_mem (f := fun group : DeferredFragment => group.node.key) member⟩

/-- Every contributing owner of a deferred task has a group descriptor at its producer.
Witness: select the corresponding fragment from that task's owner map.
-/
theorem TaskAt.deferred_owner {work address owners producer payload key}
    (known : TaskAt work (.deferred address) owners producer payload)
    (member : key ∈ owners)
    : ∃ node parents, NodeAt work node .group parents producer ∧ node.key = key := by
  cases StructuralEquivalence.taskAt_of_current known with
  | deferred located =>
      obtain ⟨group, included, same⟩ := List.mem_map.mp member
      exact ⟨group.node, _, .group located.toCurrent included, same⟩

-----------------------------------------------------------------------------------------
-- Entire healthy groups cannot disappear through cancellation alone
-----------------------------------------------------------------------------------------

/-- A healthy accounted group has at least one published contributor.
Witness: if every contributor were cancelled, every descriptor's producer would be
unavailable, triggering group failure. Kind separation prevents an empty stream descriptor
with the same raw key from invalidating that argument; no uniqueness of producers is used.
-/
theorem NodeAccounted.group_published
    {work matching events failed node parents producer}
    (accounted : NodeAccounted work matching events failed node.key)
    (known : NodeAt work node .group parents producer)
    (groupsOnly
      : ∀ other kind dependencies birth,
          NodeAt work other kind dependencies birth
          → other.key = node.key
          → kind = .group)
    (healthy : ¬NodeFailed work failed node.key)
    : ∃ occurrence owners birth payload,
        TaskAt work occurrence owners birth payload
        ∧ node.key ∈ owners
        ∧ Published matching events occurrence := by
  classical
  apply Classical.byContradiction
  intro absent
  have unavailable {other dependencies birth}
      (descriptor : NodeAt work other .group dependencies birth) (same : other.key = node.key)
      : ∃ parent, birth = some parent
          ∧ (parent ∈ failed ∨ TaskCancelled work failed parent) := by
    obtain ⟨occurrence, owners, payload, task, member⟩ := descriptor.group_task
    have contributes : node.key ∈ owners := same ▸ member
    rcases accounted occurrence owners ⟨birth, payload, task⟩ contributes with cancelled | published
    · exact cancelled.healthy_producer_unavailable task contributes healthy
    · exact False.elim (absent ⟨occurrence, owners, birth, payload, task, contributes, published⟩)
  apply healthy
  apply NodeFailed.producers known
  · intro other kind dependencies descriptor same
    have group := groupsOnly other kind dependencies none descriptor same
    subst kind
    obtain ⟨parent, impossible, _⟩ := unavailable descriptor same
    cases impossible
  · intro other kind dependencies parent descriptor same notFailed
    have group := groupsOnly other kind dependencies (some parent) descriptor same
    subst kind
    obtain ⟨otherParent, equal, failed | cancelled⟩ := unavailable descriptor same
    · exact False.elim (notFailed (Option.some.inj equal ▸ failed))
    · exact Option.some.inj equal ▸ cancelled

/-- A published task's producer has published in the same observed history.
Witness: extract the strict earlier publication supplied by task readiness.
-/
theorem Explains.published_producer
    {work groups streams events matching failures occurrence owners producer payload}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer payload)
    (published : Published matching events occurrence)
    : ∀ parent, producer = some parent → Published matching events parent := by
  intro parent generated
  subst producer
  obtain ⟨index, event, selected, value, same⟩ := published
  obtain ⟨earlier, previous, _, atEarlier, publishes, matched⟩ :=
    explained.producer_before selected value (same ▸ known)
  exact ⟨earlier, previous, atEarlier, publishes, matched⟩

end GraphQL.IncrementalDelivery.WorkScheduler
