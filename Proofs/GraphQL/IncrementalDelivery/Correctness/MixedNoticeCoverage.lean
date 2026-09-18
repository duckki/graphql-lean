import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.Correctness.LeastKeyProgress
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.NoticeCoverage

/-! Proof-only notice support for mixed work. A stream may wait until one healthy defer
parent and that parent's full ancestry are satisfied. Public admission stays unchanged.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- A weaker coverage witness allows streams to wait for a later notice carrier
-----------------------------------------------------------------------------------------

/-- An eligible group, or an eligible stream supported by one dependency and its full
defer ancestry. This is a sufficient proof-construction opportunity, not the public
stream-admission rule: streams may legally be announced earlier via silent accounting.
-/
def SupportedNotice (ancestry : Ancestry.Assignment) (work : Work) (initial : Keys)
    (matching : PublicationMatching) (events : List WorkEvent) (failed : List Occurrence)
    (node : DeliveryNode) (kind : NodeKind) (parents : Keys)
    (producer : Option Occurrence)
    : Prop :=
  CanAnnounce work initial matching events failed node kind parents producer
  ∧ (kind = .stream
      → parents = []
        ∨ ∃ key ∈ parents,
            DependencySatisfied work initial matching events failed key
            ∧ ∀ ancestor ∈ ancestry key,
                DependencySatisfied work initial matching events failed ancestor)

/-- No unannounced node has the stronger support used by the progress construction.
This witness permits an eligible stream to wait on its parent's still-open ancestry.
-/
def SupportedNoticesCovered (ancestry : Ancestry.Assignment) (work : Work)
    (initial : Keys) (matching : PublicationMatching) (events : List WorkEvent)
    (failed : List Occurrence)
    : Prop :=
  ∀ node kind parents producer,
    NodeAt work node kind parents producer
    → ¬SupportedNotice ancestry work initial matching events failed node kind parents
        producer

/-- Covering every eligible notice also covers the stronger supported opportunities.
Witness: forget the extra ancestry support. Existing initialization and both covering
carrier constructions therefore supply this weaker construction invariant unchanged.
-/
theorem supportedNoticesCovered_of_noticesCovered
    {ancestry work initial matching events failed}
    (covered : NoticesCovered work initial matching events failed)
    : SupportedNoticesCovered ancestry work initial matching events failed :=
  fun node kind parents producer known supported =>
    covered node kind parents producer known supported.1

-----------------------------------------------------------------------------------------
-- Transport supported group dependencies across non-carrier observations
-----------------------------------------------------------------------------------------

/-- A fully supported defer dependency was already satisfied before a non-carrier change.
Witness: key induction. If a healthy unannounced group becomes accounted for, some actual
contributor published; its already-ready producer and transported ancestors would have
made the group announceable before. Kind roles include absent ancestor placeholders.
The publication premise allows a new ready object publication, not just control events.
-/
theorem supported_dependency_before
    {ancestry bound roles work initial before events oldMatching matching oldFailed failed
      key}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (covered : SupportedNoticesCovered ancestry work initial oldMatching before oldFailed)
    (included : oldFailed ⊆ failed)
    (notices : (announcedKeys initial before).Subset (announcedKeys initial events))
    (completions
      : ∀ key,
          roles key = false
          → ¬NodeFailed work failed key
          → key ∈ completedKeys events
          → key ∈ completedKeys before)
    (producers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence
          → ∀ parent, producer = some parent → Published oldMatching before parent)
    (role : roles key = false)
    (ancestors
      : ∀ ancestor ∈ ancestry key,
          DependencySatisfied work initial matching events failed ancestor)
    (satisfied : DependencySatisfied work initial matching events failed key)
    : DependencySatisfied work initial oldMatching before oldFailed key := by
  classical
  induction key using Nat.strongRecOn with
  | ind key ih =>
      have healthy : ¬NodeFailed work oldFailed key :=
        fun failure => satisfied.1 (failure.mono included)
      refine ⟨healthy, ?_⟩
      rcases satisfied.2 with absent | completed | ⟨fresh, accounted⟩
      · exact Or.inl absent
      · exact Or.inr (Or.inl (completions key role satisfied.1 completed))
      · by_cases beforeAccounted : NodeAccounted work oldMatching before oldFailed key
        · exact Or.inr (Or.inr ⟨fun member => fresh (notices member), beforeAccounted⟩)
        by_cases supported : ∃ birth, NodeHasProducer work key birth
        · obtain ⟨birth, node, kind, parents, descriptor, same⟩ := supported
          have group := node_kind_of_defer_role roleCoherent descriptor (same ▸ role)
          subst kind
          obtain ⟨occurrence, owners, producer, payload, task, member, published⟩ :=
            NodeAccounted.group_published (same ▸ accounted) descriptor
              (by
                intro other kind dependencies birth known equal
                exact node_kind_of_defer_role roleCoherent known ((equal.trans same) ▸ role))
              (same ▸ satisfied.1)
          obtain ⟨owner, ownerKind, dependencies, known, ownerSame⟩ :=
            task.owner_at_producer member
          have keySame := ownerSame.trans same
          have group := node_kind_of_defer_role roleCoherent known (keySame ▸ role)
          subst ownerKind
          have full := DeferOnly.node_parents coherent known
          have bounded := (coherent_node_bounds coherent known).2
          apply False.elim
          apply covered owner .group dependencies producer known
          refine ⟨
            ⟨
              keySame ▸ (fun member => fresh (notices member)),
              keySame ▸ healthy,
              Or.inr (keySame ▸ beforeAccounted),
              producers _ _ _ _ task published,
              ?_
            ⟩,
            by intro impossible; cases impossible
          ⟩
          intro ancestor dependency
          have inParents : ancestor ∈ ancestry key := by
            simpa only [full, keySame] using dependency
          have prior := valid key (keySame ▸ bounded) ancestor inParents
          apply ih ancestor prior.1 (group_parent_role roleCoherent known dependency)
          · exact fun parent member => ancestors parent (prior.2 member)
          · exact ancestors ancestor inParents
        · exact Or.inl supported

/-- The complete dependency support of a notice transports backwards across a change
whose publications already had ready producers and which closes no new healthy defer key.
Witness: the preceding key induction and transitivity of each selected parent's ancestry.
-/
theorem SupportedNotice.dependencies_before
    {ancestry bound roles work initial before events oldMatching matching oldFailed failed
      node kind parents producer}
    (supported
      : SupportedNotice ancestry work initial matching events failed
          node kind parents producer)
    (known : NodeAt work node kind parents producer)
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (covered : SupportedNoticesCovered ancestry work initial oldMatching before oldFailed)
    (included : oldFailed ⊆ failed)
    (notices : (announcedKeys initial before).Subset (announcedKeys initial events))
    (completions
      : ∀ key,
          roles key = false
          → ¬NodeFailed work failed key
          → key ∈ completedKeys events
          → key ∈ completedKeys before)
    (producers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence
          → ∀ parent, producer = some parent → Published oldMatching before parent)
    : match kind with
      | .group =>
          ∀ key ∈ parents,
            DependencySatisfied work initial oldMatching before oldFailed key
      | .stream =>
          parents = []
          ∨ ∃ key ∈ parents,
              DependencySatisfied work initial oldMatching before oldFailed key
              ∧ ∀ ancestor ∈ ancestry key,
                  DependencySatisfied work initial oldMatching before oldFailed
                    ancestor := by
  have transport {group dependencies birth}
      (descriptor : NodeAt work group .group dependencies birth)
      (current : ∀ key ∈ ancestry group.key,
        DependencySatisfied work initial matching events failed key)
      : ∀ key ∈ ancestry group.key,
          DependencySatisfied work initial oldMatching before oldFailed key := by
    intro key member
    have full := DeferOnly.node_parents coherent descriptor
    have bounded := (coherent_node_bounds coherent descriptor).2
    have prior := valid group.key bounded key member
    apply supported_dependency_before valid coherent roleCoherent covered included notices
      completions producers (group_parent_role roleCoherent descriptor (full ▸ member))
    · exact fun ancestor included => current ancestor (prior.2 included)
    · exact current key member
  cases kind with
  | group =>
      have full := DeferOnly.node_parents coherent known
      have previous := transport known (by simpa only [full] using supported.1.2.2.2.2)
      simpa only [full] using previous
  | stream =>
      rcases supported.2 rfl with empty | ⟨key, member, dependency, ancestors⟩
      · exact Or.inl empty
      · obtain ⟨group, dependencies, birth, descriptor, same⟩ := stream_parent_group known member
        have groupRole : roles group.key = false := node_key_role roleCoherent descriptor
        have role : roles key = false := same ▸ groupRole
        exact Or.inr ⟨key, member,
          supported_dependency_before valid coherent roleCoherent covered included notices
            completions producers role ancestors dependency,
          by simpa only [same] using transport descriptor (by simpa only [same] using ancestors)⟩

/-- Supported notice coverage survives a non-carrier change when ready node producers
were already available. Witness: transport dependencies, freshness, health, and
outstanding accounting backwards. The producer premise is discharged for object events.
-/
theorem supported_coverage_noncarrier
    {ancestry bound roles work initial before events oldMatching matching oldFailed
      failed}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (covered : SupportedNoticesCovered ancestry work initial oldMatching before oldFailed)
    (included : oldFailed ⊆ failed)
    (notices : (announcedKeys initial before).Subset (announcedKeys initial events))
    (completions
      : ∀ key,
          roles key = false
          → ¬NodeFailed work failed key
          → key ∈ completedKeys events
          → key ∈ completedKeys before)
    (producers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence
          → ∀ parent, producer = some parent → Published oldMatching before parent)
    (accounting
      : ∀ key,
          NodeAccounted work oldMatching before oldFailed key
          → NodeAccounted work matching events failed key)
    (nodeProducers
      : ∀ node kind parents producer,
          NodeAt work node kind parents producer
          → SupportedNotice ancestry work initial matching events failed node kind parents
              producer
          → ∀ parent, producer = some parent → Published oldMatching before parent)
    : SupportedNoticesCovered ancestry work initial matching events failed := by
  intro node kind parents producer known supported
  have dependencies := supported.dependencies_before known valid coherent roleCoherent
    covered included notices completions producers
  apply covered node kind parents producer known
  have fresh := fun member => supported.1.1 (notices member)
  have healthy : ¬NodeFailed work oldFailed node.key :=
    fun failure => supported.1.2.1 (failure.mono included)
  have ready := nodeProducers node kind parents producer known supported
  cases kind with
  | group =>
      exact ⟨
        ⟨
          fresh,
          healthy,
          Or.inr
            (fun accounted =>
              supported.1.2.2.1.resolve_left (by simp) (accounting node.key accounted)),
          ready,
          dependencies
        ⟩,
        by intro impossible; cases impossible
      ⟩
  | stream =>
      refine ⟨⟨fresh, healthy, Or.inl rfl, ready, ?_⟩, fun _ => dependencies⟩
      exact dependencies.imp_right
        (by rintro ⟨key, member, satisfied, _⟩; exact ⟨key, member, satisfied⟩)

end GraphQL.IncrementalDelivery.Correctness
