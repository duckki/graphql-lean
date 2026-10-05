import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingNoticeCoverage

/-! Healthy group accounting retains at least one available producer descriptor.
Repeated descriptors and shared owners are kept; no primary producer is selected.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Accounting cannot silently make every group producer unavailable
-----------------------------------------------------------------------------------------

/-- A healthy accounted group has a root descriptor or a published producer.
Witness: if every descriptor's producer were unavailable, each accounted contributing task
would be cancelled by that producer rather than its healthy owner. The all-producers causal
rule would then fail the group already. Ref roles exclude unrelated stream descriptors.
This uses actual accounting and causal explanations, not terminal reporting or notice laws.
-/
theorem Explains.healthy_group_accounted_producer_available
    {roles work groups streams events matching failures node dependencies producer}
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies producer)
    (healthy : ¬NodeFailed work matching events failures node.ref)
    (accounted : NodeAccounted work matching events failures node.ref)
    : ∃ birth,
        NodeHasProducer work node.ref birth
        ∧ ∀ source, birth = some source → Published matching events source := by
  classical
  apply Classical.byContradiction
  intro absent
  have noRoot : ¬NodeHasProducer work node.ref none := by
    intro root
    exact absent ⟨none, root, by intro source impossible; cases impossible⟩
  have unavailable : ∀ source, NodeHasProducer work node.ref (some source) →
      ¬Published matching events source := by
    intro source descriptor published
    apply absent
    refine ⟨some source, descriptor, ?_⟩
    intro other same
    cases Option.some.inj same
    exact published
  apply healthy
  apply explained.snapshot_nodeFailed
  refine Causality.NodeFailed.producers ⟨producer, node, .group, dependencies, known, rfl⟩
    noRoot unavailable ?_
  intro source descriptor notRecorded
  obtain ⟨owner, kind, parents, ownerKnown, same⟩ := descriptor
  cases kind with
  | stream =>
      exact False.elim (stream_group_refs_distinct roleCoherent ownerKnown known same)
  | group =>
      obtain ⟨address, fragments, path, result, children, enclosing, fragment, located,
        member, ownerEq, parentsEq⟩ := ownerKnown
      have task := TaskAt.executionGroup located
      have contributes : node.ref ∈ fragments.map (fun group => group.node.ref) :=
        List.mem_map.mpr ⟨fragment, member, (congrArg DeliveryNode.ref ownerEq.symm).trans same⟩
      have cancelled : TaskCancelled work matching events failures (.executionGroup address) := by
        apply (accounted _ _ ⟨some source, _, task⟩ contributes).resolve_right
        intro published
        exact unavailable source ⟨owner, .group, parents, by
          exact ⟨address, fragments, path, result, children, enclosing, fragment, located,
            member, ownerEq, parentsEq⟩, same⟩
          (explained.published_producer task published source rfl)
      have snapshot := explained.taskCancelled_snapshot cancelled
      cases snapshot with
      | owners projected _ _ failed =>
          obtain ⟨birth, payload, other⟩ := projected
          have membership := (task.unique other).1 ▸ contributes
          exact False.elim (healthy (explained.snapshot_nodeFailed (failed _ membership)))
      | producerFailed projected _ recorded =>
          obtain ⟨owners, payload, other⟩ := projected
          have sameSource := Option.some.inj (task.unique other).2.1
          exact False.elim (notRecorded (sameSource ▸ recorded))
      | producerCancelled projected _ failure =>
          obtain ⟨owners, payload, other⟩ := projected
          have sameSource := Option.some.inj (task.unique other).2.1
          exact sameSource.symm ▸ failure

/-- Every causally failed ref has a represented node descriptor.
Witness: direct failure uses its contributing task's owner; dependency and producer rules
already carry a descriptor. This is structural provenance, not an announcement premise.
-/
theorem Explains.failed_node_known
    {work groups streams events matching failures ref}
    (explained : Explains work groups streams events matching failures)
    (failed : NodeFailed work matching events failures ref)
    : ∃ node kind dependencies producer,
        NodeAt work node kind dependencies producer ∧ node.ref = ref := by
  have snapshot := explained.nodeFailed_snapshot failed
  cases snapshot with
  | task projected member _ =>
      obtain ⟨producer, payload, known⟩ := projected
      exact known.owner_known member
  | groupDependency known _ _ =>
      obtain ⟨node, producer, known, same⟩ := known
      exact ⟨node, .group, _, producer, known, same⟩
  | streamDependencies known _ _ =>
      obtain ⟨node, producer, known, same⟩ := known
      exact ⟨node, .stream, _, producer, known, same⟩
  | producers known _ _ _ =>
      obtain ⟨producer, node, kind, dependencies, known, same⟩ := known
      exact ⟨node, kind, dependencies, producer, known, same⟩

end GraphQL.IncrementalDelivery.Correctness
