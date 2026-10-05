import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeCoverage

/-! Least healthy owner support, independently of any terminal-progress construction. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Least outstanding owners have full support, including stream-dependency ancestry
-----------------------------------------------------------------------------------------

/-- A least outstanding healthy owner is supported once smaller healthy refs satisfy
dependencies. Witness: ordinary eligibility plus, for streams, the selected defer
dependency's strict, healthy ancestry. This excludes merely early silent-accounting
notices.
-/
theorem least_owner_supported
    {ancestry bound work groups streams initial matching events failed occurrence owners
      producer payload node kind dependencies}
    (explained : Explains work groups streams events matching failed)
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failed occurrence producer)
    (descriptor : NodeAt work node kind dependencies producer)
    (member : node.ref ∈ owners)
    (healthy : ¬NodeFailed work matching events failed node.ref)
    (fresh : node.ref ∉ announcedRefs initial events)
    (smaller
      : ∀ ref,
          ref < node.ref
          → ¬NodeFailed work matching events failed ref
          → DependencySatisfied work initial matching events failed ref)
    : SupportedNotice ancestry work initial matching events failed node kind dependencies
        producer := by
  have eligible := least_owner_announceable explained valid coherent ordered known ready descriptor
    member healthy fresh smaller
  refine ⟨eligible, healthy, ?_⟩
  intro stream
  subst kind
  rcases eligible.2.2.2 with empty | ⟨ref, contributes, dependency⟩
  · exact Or.inl empty
  · obtain ⟨group, parents, birth, groupKnown, same⟩ :=
      stream_dependency_group descriptor contributes
    refine Or.inr ⟨ref, contributes, dependency, ?_⟩
    intro ancestor included
    have full := DeferOnly.node_dependencies coherent groupKnown
    have dependencyMember : ancestor ∈ parents := by simpa only [full, same] using included
    apply smaller ancestor
    · have before := coherent_group_dependencies valid coherent groupKnown ancestor dependencyMember
      have below := coherent_stream_dependencies ordered descriptor ref contributes
      simpa only [same] using Nat.lt_trans before (same ▸ below)
    · intro failed
      exact dependency.1 (same ▸ NodeFailed.groupDependency groupKnown dependencyMember failed)

end GraphQL.IncrementalDelivery.Correctness
