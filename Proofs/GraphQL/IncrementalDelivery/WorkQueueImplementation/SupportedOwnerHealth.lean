import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupInvalidation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCausalHealth

/-! Owner-health bridges usable while constructing, rather than assuming, admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Queue-local cleanup has a historical failure witness without Explains
-----------------------------------------------------------------------------------------

/-- Recorded queue-local invalidation implies historical failure on supported publications.
Witness: embed cleanup in the current causal snapshot, then recover a reached cut with
the support-based snapshot bridge. The original Explains-based interface is unchanged.
-/
theorem GroupInvalidated.toNodeFailed_of_support
    {work failed key events matching cuts}
    (failure : GroupInvalidated work failed key)
    (support : PublicationSupport work matching events cuts)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ cuts
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (included : failed.Subset (failedBefore cuts events.length))
    : NodeFailed work matching events cuts key :=
  support.snapshot_nodeFailed failedPayloads
    ((failure.mono included).toCausality (Published matching events))

-----------------------------------------------------------------------------------------
-- Published producers exclude producer cancellation without a fully admitted history
-----------------------------------------------------------------------------------------

/-- A supported generated group's failure comes from its contributors or defer ancestry.
Witness: move to the supported snapshot, where a published producer blocks the producer
rule. Root descriptors block that rule directly. Generated roles and canonical ancestry
identify the remaining cases; dependency failures are transported back to historical cuts.
-/
theorem PublicationSupport.groupFailure_causes
    {work events matching failures node dependencies producer}
    (support : PublicationSupport work matching events failures)
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node .group dependencies producer)
    (ready : ∀ source, producer = some source → Published matching events source)
    (failure : NodeFailed work matching events failures node.key)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners
        ∧ node.key ∈ owners
        ∧ occurrence ∈ failedBefore failures events.length)
      ∨ ∃ dependency ∈ dependencies,
          NodeFailed work matching events failures dependency := by
  have snapshot := support.nodeFailed_snapshot failedPayloads failure
  cases snapshot with
  | task task owner member => exact .inl ⟨_, _, task, owner, member⟩
  | @groupDependency key otherDependencies dependency descriptor member prior =>
      obtain ⟨other, birth, otherKnown, keyEq⟩ := descriptor
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have same : otherDependencies = dependencies := by
        rw [canonical _ _ _ otherKnown, canonical _ _ _ known, keyEq]
      exact .inr ⟨_, same ▸ member, support.snapshot_nodeFailed failedPayloads prior⟩
  | streamDependencies descriptor _ _ =>
      obtain ⟨stream, birth, located, same⟩ := descriptor
      exact False.elim (generated.groupStreamKeysDisjoint known located same.symm)
  | producers _ noRoot unpublished _ =>
      cases producer with
      | none => exact False.elim (noRoot ⟨node, .group, dependencies, known, rfl⟩)
      | some source =>
          exact False.elim (unpublished source ⟨node, .group, dependencies, known, rfl⟩
            (ready source rfl))

/-- A generated group with a ready producer and healthy contributors/ancestors is healthy.
Witness: the preceding failure decomposition. This can be applied to publication support
of a strict prefix while proving the next event; it does not assume that event's admission.
-/
theorem PublicationSupport.groupHealthy
    {work events matching failures node dependencies producer}
    (support : PublicationSupport work matching events failures)
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node .group dependencies producer)
    (ready : ∀ source, producer = some source → Published matching events source)
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → node.key ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    (ancestors : ∀ key ∈ dependencies, ¬NodeFailed work matching events failures key)
    : ¬NodeFailed work matching events failures node.key := by
  intro failure
  rcases support.groupFailure_causes generated failedPayloads known ready failure with
    ⟨occurrence, owners, task, owner, failed⟩ | ⟨key, member, failed⟩
  · exact contributors occurrence owners task owner failed
  · exact ancestors key member failed

/-- A supported generated stream fails through an item or failure of every defer owner.
Witness: unique stream metadata identifies dependencies, generated roles exclude group
rules, and an already-published producer excludes producer cancellation at the current
snapshot. These conclusions retain historical failure evidence, not only a live ledger.
-/
theorem PublicationSupport.streamFailure_causes
    {work events matching failures node dependencies producer}
    (support : PublicationSupport work matching events failures)
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node .stream dependencies producer)
    (ready : ∀ source, producer = some source → Published matching events source)
    (failure : NodeFailed work matching events failures node.key)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners
        ∧ node.key ∈ owners
        ∧ occurrence ∈ failedBefore failures events.length)
      ∨ dependencies ≠ []
        ∧ ∀ dependency ∈ dependencies,
            NodeFailed work matching events failures dependency := by
  have snapshot := support.nodeFailed_snapshot failedPayloads failure
  cases snapshot with
  | task task owner member => exact .inl ⟨_, _, task, owner, member⟩
  | groupDependency descriptor _ _ =>
      obtain ⟨group, birth, located, same⟩ := descriptor
      exact False.elim (generated.groupStreamKeysDisjoint located known same)
  | streamDependencies descriptor nonempty failed =>
      obtain ⟨stream, birth, located, same⟩ := descriptor
      have equal := generated.streamDependencies_unique located known same
      refine .inr ⟨equal ▸ nonempty, ?_⟩
      intro key member
      exact support.snapshot_nodeFailed failedPayloads (failed key (equal.symm ▸ member))
  | producers _ noRoot unpublished _ =>
      cases producer with
      | none => exact False.elim (noRoot ⟨node, .stream, dependencies, known, rfl⟩)
      | some source =>
          exact False.elim (unpublished source ⟨node, .stream, dependencies, known, rfl⟩
            (ready source rfl))

/-- A ready stream with no failed item and one healthy defer owner remains healthy.
Witness: exclude both cases of streamFailure_causes; empty dependency lists need no owner.
Publication support belongs to the earlier observed prefix, not an assumed next event.
-/
theorem PublicationSupport.streamHealthy
    {work events matching failures node dependencies producer}
    (support : PublicationSupport work matching events failures)
    (generated : ExecutedWork work)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (known : NodeAt work node .stream dependencies producer)
    (ready : ∀ source, producer = some source → Published matching events source)
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → node.key ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    (owners
      : dependencies = []
        ∨ ∃ key ∈ dependencies, ¬NodeFailed work matching events failures key)
    : ¬NodeFailed work matching events failures node.key := by
  intro failure
  rcases support.streamFailure_causes generated failedPayloads known ready failure with
    ⟨occurrence, owners, task, owner, failed⟩ | ⟨nonempty, failed⟩
  · exact contributors occurrence owners task owner failed
  · rcases owners with empty | ⟨key, member, healthy⟩
    · exact nonempty empty
    · exact healthy (failed key member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
