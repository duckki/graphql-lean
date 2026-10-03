import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.Correctness.LeastRefProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.NoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.NoticeEligibility

/-! Proof-only notice support for mixed work. A stream may wait until one healthy defer
dependency and that dependency's full ancestry are satisfied. Public admission stays
unchanged.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A weaker coverage witness allows streams to wait for a later notice carrier
-----------------------------------------------------------------------------------------

/-- A healthy eligible group, or a healthy eligible stream supported by one dependency
and its full defer ancestry. This proof-construction opportunity need not announce
retained failures; public admission also permits them and earlier stream notices.
-/
def SupportedNotice (ancestry : Ancestry.Assignment) (work : Work) (initial : NodeRefs)
    (matching : PublicationMatching) (events : List WorkQueueEvent) (failed : FailureCuts)
    (node : DeliveryNode) (kind : NodeKind) (dependencies : NodeRefs)
    (producer : Option Occurrence)
    : Prop :=
  CanAnnounce work initial matching events failed node kind dependencies producer
  ∧ ¬NodeFailed work matching events failed node.ref
  ∧ (kind = .stream
      → dependencies = []
        ∨ ∃ ref ∈ dependencies,
            DependencySatisfied work initial matching events failed ref
            ∧ ∀ ancestor ∈ ancestry ref,
                DependencySatisfied work initial matching events failed ancestor)

/-- No unannounced node has the stronger support used by the progress construction.
This witness permits an eligible stream to wait on its dependency's still-open ancestry.
-/
def SupportedNoticesCovered (ancestry : Ancestry.Assignment) (work : Work)
    (initial : NodeRefs) (matching : PublicationMatching) (events : List WorkQueueEvent)
    (failed : FailureCuts)
    : Prop :=
  ∀ node kind dependencies producer,
    NodeAt work node kind dependencies producer
    → ¬SupportedNotice ancestry work initial matching events failed node kind
        dependencies
        producer

/-- Covering every eligible notice also covers the stronger supported opportunities.
Witness: forget the extra ancestry support. Existing initialization and both covering
carrier constructions therefore supply this weaker construction invariant unchanged.
-/
theorem supportedNoticesCovered_of_noticesCovered
    {ancestry work initial matching events failed}
    (covered : NoticesCovered work initial matching events failed)
    : SupportedNoticesCovered ancestry work initial matching events failed :=
  fun node kind dependencies producer known supported =>
    covered node kind dependencies producer known supported.1

-----------------------------------------------------------------------------------------
-- Transport supported group dependencies across non-carrier observations
-----------------------------------------------------------------------------------------

/-- A fully supported defer dependency was already satisfied before a non-carrier change.
Witness: ref induction. If a healthy unannounced group becomes accounted for, some actual
contributor published; its already-ready producer and transported ancestors would have
made the group announceable before. Kind roles include absent ancestor placeholders.
The publication premise allows a new ready object publication, not just control events.
-/
theorem supported_dependency_before
    {ancestry bound roles work groups streams initial before events oldMatching matching
      oldFailed failed ref}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (covered : SupportedNoticesCovered ancestry work initial oldMatching before oldFailed)
    (explained : Explains work groups streams events matching failed)
    (included
      : ∀ ref,
          NodeFailed work oldMatching before oldFailed ref
          → NodeFailed work matching events failed ref)
    (notices : (announcedRefs initial before).Subset (announcedRefs initial events))
    (completions
      : ∀ ref,
          roles ref = false
          → ¬NodeFailed work matching events failed ref
          → ref ∈ completedRefs events
          → ref ∈ completedRefs before)
    (producers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence
          → ∀ producerOccurrence,
              producer = some producerOccurrence
              → Published oldMatching before producerOccurrence)
    (role : roles ref = false)
    (ancestors
      : ∀ ancestor ∈ ancestry ref,
          DependencySatisfied work initial matching events failed ancestor)
    (satisfied : DependencySatisfied work initial matching events failed ref)
    : DependencySatisfied work initial oldMatching before oldFailed ref := by
  classical
  induction ref using Nat.strongRecOn with
  | ind ref ih =>
      have healthy : ¬NodeFailed work oldMatching before oldFailed ref :=
        fun failure => satisfied.1 (included _ failure)
      refine ⟨healthy, ?_⟩
      rcases satisfied.2 with absent | completed | ⟨fresh, accounted⟩
      · exact Or.inl absent
      · exact Or.inr (Or.inl (completions ref role satisfied.1 completed))
      · by_cases beforeAccounted : NodeAccounted work oldMatching before oldFailed ref
        · exact Or.inr (Or.inr ⟨fun member => fresh (notices member), beforeAccounted⟩)
        by_cases supported : ∃ birth, NodeHasProducer work ref birth
        · obtain ⟨birth, node, kind, dependencies, descriptor, same⟩ := supported
          have group := node_kind_of_defer_role roleCoherent descriptor (same ▸ role)
          subst kind
          obtain ⟨occurrence, owners, producer, payload, task, member, published⟩ :=
            NodeAccounted.group_published explained (same ▸ accounted) descriptor
              (by
                intro other kind dependencies birth known equal
                exact node_kind_of_defer_role roleCoherent known ((equal.trans same) ▸ role))
              (same ▸ satisfied.1)
          obtain ⟨owner, ownerKind, dependencies, known, ownerSame⟩ :=
            task.owner_at_producer member
          have refSame := ownerSame.trans same
          have group := node_kind_of_defer_role roleCoherent known (refSame ▸ role)
          subst ownerKind
          have full := DeferOnly.node_dependencies coherent known
          have bounded := (coherent_node_bounds coherent known).2
          apply False.elim
          apply covered owner .group dependencies producer known
          refine ⟨
            ⟨
              refSame ▸ (fun member => fresh (notices member)),
              Or.inl ⟨refSame ▸ healthy, Or.inr (refSame ▸ beforeAccounted)⟩,
              producers _ _ _ _ task published,
              ?_
            ⟩,
            refSame ▸ healthy,
            by intro impossible; cases impossible
          ⟩
          intro ancestor dependency
          have inDependencies : ancestor ∈ ancestry ref := by
            simpa only [full, refSame] using dependency
          have prior := valid ref (refSame ▸ bounded) ancestor inDependencies
          apply ih ancestor prior.1 (group_dependency_role roleCoherent known dependency)
          · exact fun dependency member => ancestors dependency (prior.2 member)
          · exact ancestors ancestor inDependencies
        · exact Or.inl supported

/-- The complete dependency support of a notice transports backwards across a change
whose publications already had ready producers and which closes no new healthy defer ref.
Witness: the preceding ref induction and transitivity of each selected dependency's
ancestry.
-/
theorem SupportedNotice.dependencies_before
    {ancestry bound roles work groups streams initial before events oldMatching matching
      oldFailed failed node kind dependencies producer}
    (supported
      : SupportedNotice ancestry work initial matching events failed
          node kind dependencies producer)
    (known : NodeAt work node kind dependencies producer)
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (covered : SupportedNoticesCovered ancestry work initial oldMatching before oldFailed)
    (explained : Explains work groups streams events matching failed)
    (included
      : ∀ ref,
          NodeFailed work oldMatching before oldFailed ref
          → NodeFailed work matching events failed ref)
    (notices : (announcedRefs initial before).Subset (announcedRefs initial events))
    (completions
      : ∀ ref,
          roles ref = false
          → ¬NodeFailed work matching events failed ref
          → ref ∈ completedRefs events
          → ref ∈ completedRefs before)
    (producers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence
          → ∀ producerOccurrence,
              producer = some producerOccurrence
              → Published oldMatching before producerOccurrence)
    : match kind with
      | .group =>
          ∀ ref ∈ dependencies,
            DependencySatisfied work initial oldMatching before oldFailed ref
      | .stream =>
          dependencies = []
          ∨ ∃ ref ∈ dependencies,
              DependencySatisfied work initial oldMatching before oldFailed ref
              ∧ ∀ ancestor ∈ ancestry ref,
                  DependencySatisfied work initial oldMatching before oldFailed
                    ancestor := by
  have transport {group dependencies birth}
      (descriptor : NodeAt work group .group dependencies birth)
      (current : ∀ ref ∈ ancestry group.ref,
        DependencySatisfied work initial matching events failed ref)
      : ∀ ref ∈ ancestry group.ref,
          DependencySatisfied work initial oldMatching before oldFailed ref := by
    intro ref member
    have full := DeferOnly.node_dependencies coherent descriptor
    have bounded := (coherent_node_bounds coherent descriptor).2
    have prior := valid group.ref bounded ref member
    apply supported_dependency_before valid coherent roleCoherent covered explained included notices
      completions producers (group_dependency_role roleCoherent descriptor (full ▸ member))
    · exact fun ancestor included => current ancestor (prior.2 included)
    · exact current ref member
  cases kind with
  | group =>
      have full := DeferOnly.node_dependencies coherent known
      have previous := transport known (by simpa only [full] using supported.1.2.2.2)
      simpa only [full] using previous
  | stream =>
      rcases supported.2.2 rfl with empty | ⟨ref, member, dependency, ancestors⟩
      · exact Or.inl empty
      · obtain ⟨group, dependencies, birth, descriptor, same⟩ :=
          stream_dependency_group known member
        have groupRole : roles group.ref = false := node_ref_role roleCoherent descriptor
        have role : roles ref = false := same ▸ groupRole
        exact Or.inr ⟨ref, member,
          supported_dependency_before valid coherent roleCoherent covered explained included notices
            completions producers role ancestors dependency,
          by simpa only [same] using transport descriptor (by simpa only [same] using ancestors)⟩

/-- Supported notice coverage survives a non-carrier change when ready node producers
were already available. Witness: transport dependencies, freshness, health, and
outstanding accounting backwards. The producer premise is discharged for object events.
-/
theorem supported_coverage_noncarrier
    {ancestry bound roles work groups streams initial before events oldMatching matching
      oldFailed failed}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (covered : SupportedNoticesCovered ancestry work initial oldMatching before oldFailed)
    (explained : Explains work groups streams events matching failed)
    (included
      : ∀ ref,
          NodeFailed work oldMatching before oldFailed ref
          → NodeFailed work matching events failed ref)
    (notices : (announcedRefs initial before).Subset (announcedRefs initial events))
    (completions
      : ∀ ref,
          roles ref = false
          → ¬NodeFailed work matching events failed ref
          → ref ∈ completedRefs events
          → ref ∈ completedRefs before)
    (producers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence
          → ∀ producerOccurrence,
              producer = some producerOccurrence
              → Published oldMatching before producerOccurrence)
    (accounting
      : ∀ ref,
          NodeAccounted work oldMatching before oldFailed ref
          → NodeAccounted work matching events failed ref)
    (nodeProducers
      : ∀ node kind dependencies producer,
          NodeAt work node kind dependencies producer
          → SupportedNotice ancestry work initial matching events failed node kind
              dependencies
              producer
          → ∀ producerOccurrence,
              producer = some producerOccurrence
              → Published oldMatching before producerOccurrence)
    : SupportedNoticesCovered ancestry work initial matching events failed := by
  intro node kind dependencies producer known supported
  have dependenciesBefore := supported.dependencies_before known valid coherent
    roleCoherent covered explained included notices completions producers
  apply covered node kind dependencies producer known
  have fresh := fun member => supported.1.1 (notices member)
  have healthy : ¬NodeFailed work oldMatching before oldFailed node.ref :=
    fun failure => supported.2.1 (included _ failure)
  have original := (canAnnounce_healthy_iff supported.2.1).mp supported.1
  have ready := nodeProducers node kind dependencies producer known supported
  cases kind with
  | group =>
      exact ⟨
        ⟨
          fresh,
          Or.inl
            ⟨
              healthy,
              Or.inr
                (fun accounted =>
                  original.2.1.resolve_left (by simp) (accounting node.ref accounted))
            ⟩,
          ready,
          dependenciesBefore
        ⟩,
        healthy,
        by intro impossible; cases impossible
      ⟩
  | stream =>
      refine ⟨⟨fresh, Or.inl ⟨healthy, Or.inl rfl⟩, ready, ?_⟩, healthy,
        fun _ => dependenciesBefore⟩
      exact dependenciesBefore.imp_right
        (by rintro ⟨ref, member, satisfied, _⟩; exact ⟨ref, member, satisfied⟩)

end GraphQL.IncrementalDelivery.Correctness
