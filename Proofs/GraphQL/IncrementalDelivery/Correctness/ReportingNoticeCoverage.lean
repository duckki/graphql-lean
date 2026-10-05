import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeCoverage

/-! Constructive notice coverage includes retained failed groups, not only healthy work.
These proof choices strengthen neither public admission nor the host source contract.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Preserve the reporting frontier as well as healthy notice support
-----------------------------------------------------------------------------------------

/-- No represented group has an eligible but still-unannounced notice. Unlike healthy
support coverage, this also covers the retained-failure announcement alternative.
-/
def GroupNoticesCovered (work : Work) (initial : NodeRefs)
    (matching : PublicationMatching) (events : List WorkQueueEvent)
    (failures : FailureCuts)
    : Prop :=
  ∀ node dependencies producer,
    NodeAt work node .group dependencies producer
    → ¬CanAnnounce work initial matching events failures node .group dependencies producer

/-- Cover healthy supported streams/groups and every eligible retained-failure group.
This is a constructive progress invariant; arbitrary admitted prefixes need not satisfy it.
-/
def ReportingNoticesCovered (ancestry : Ancestry.Assignment) (work : Work)
    (initial : NodeRefs) (matching : PublicationMatching) (events : List WorkQueueEvent)
    (failures : FailureCuts)
    : Prop :=
  SupportedNoticesCovered ancestry work initial matching events failures
  ∧ GroupNoticesCovered work initial matching events failures

/-- A full eligible frontier supplies both components of reporting-aware coverage.
Witness: restrict ordinary coverage to groups and forget extra healthy stream support.
-/
theorem reportingNoticesCovered_of_noticesCovered
    {ancestry work initial matching events failures}
    (covered : NoticesCovered work initial matching events failures)
    : ReportingNoticesCovered ancestry work initial matching events failures :=
  ⟨
    supportedNoticesCovered_of_noticesCovered covered,
    fun node dependencies producer known =>
      covered node .group dependencies producer known
  ⟩

-----------------------------------------------------------------------------------------
-- An eligible produced group without a recorded contributor failure is healthy
-----------------------------------------------------------------------------------------

/-- A group with a published producer and healthy ancestors has no other failure origin
when none of its contributors has a recorded failure. Witness: invert current causal
failure; coherent ancestry and ref roles exclude dependency/type mismatches, while its
published producer (or root descriptor) excludes the unavailable-producer rule.
-/
theorem Explains.group_healthy_of_no_recorded_failure
    {ancestry bound roles work groups streams events matching failures node dependencies
      producer}
    (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies producer)
    (noFailure : ¬HasRecordedFailure work failures events.length node.ref)
    (produced : ∀ source, producer = some source → Published matching events source)
    (healthyDependencies
      : ∀ ref ∈ dependencies, ¬NodeFailed work matching events failures ref)
    : ¬NodeFailed work matching events failures node.ref := by
  intro failed
  have snapshot := explained.nodeFailed_snapshot failed
  cases snapshot with
  | task projected member recorded =>
      exact noFailure ⟨_, _, recorded, projected, member⟩
  | groupDependency projected member failure =>
      obtain ⟨group, birth, descriptor, same⟩ := projected
      have full := DeferOnly.node_dependencies coherent known
      have other := DeferOnly.node_dependencies coherent descriptor
      have contributes := member
      rw [other, same, ← full] at contributes
      exact healthyDependencies _ contributes (explained.snapshot_nodeFailed failure)
  | streamDependencies projected _ _ =>
      obtain ⟨stream, birth, descriptor, same⟩ := projected
      exact stream_group_refs_distinct roleCoherent descriptor known same
  | producers _ noRoot unpublished _ =>
      cases producer with
      | none => exact noRoot ⟨node, .group, dependencies, known, rfl⟩
      | some source =>
          exact unpublished source ⟨node, .group, dependencies, known, rfl⟩
            (produced source rfl)

-----------------------------------------------------------------------------------------
-- Failed group notices retain the same full ancestry transport as healthy groups
-----------------------------------------------------------------------------------------

/-- Group announcement dependencies transport backwards without assuming group health.
Witness: strong ref induction on the healthy dependencies themselves. This retains the
failure-announcement alternative that the old SupportedNotice wrapper could not express.
-/
theorem CanAnnounce.group_dependencies_before
    {ancestry bound roles work groups streams initial before events oldMatching matching
      oldFailed failed node dependencies producer}
    (notice
      : CanAnnounce work initial matching events failed node .group dependencies producer)
    (known : NodeAt work node .group dependencies producer)
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
          → ∀ source, producer = some source → Published oldMatching before source)
    : ∀ ref ∈ dependencies,
        DependencySatisfied work initial oldMatching before oldFailed ref := by
  intro ref member
  have full := DeferOnly.node_dependencies coherent known
  have bounded := (coherent_node_bounds coherent known).2
  have contributes : ref ∈ ancestry node.ref := by simpa only [full] using member
  have prior := valid node.ref bounded ref contributes
  apply supported_dependency_before valid coherent roleCoherent covered explained included
    notices completions producers (group_dependency_role roleCoherent known member)
  · intro ancestor included
    apply notice.2.2.2 ancestor
    simpa only [full] using prior.2 included
  · exact notice.2.2.2 ref member

-----------------------------------------------------------------------------------------
-- Non-carrier changes with no newly recorded contributor failures
-----------------------------------------------------------------------------------------

/-- Retained group notices stay covered across a non-carrier change when their producer,
dependencies, and recorded failures were already available. Witness: transfer the actual
failure-announcement branch backwards; healthy notices use ordinary support coverage.
New failure settlements need the separate construction below this boundary.
-/
theorem group_notices_covered_noncarrier
    {ancestry bound roles work groups streams initial before events oldMatching matching
      oldFailed failed}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (covered : ReportingNoticesCovered ancestry work initial oldMatching before oldFailed)
    (healthyCovered
      : SupportedNoticesCovered ancestry work initial matching events failed)
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
          → ∀ source, producer = some source → Published oldMatching before source)
    (nodeProducers
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer
          → CanAnnounce work initial matching events failed node .group dependencies
              producer
          → ∀ source, producer = some source → Published oldMatching before source)
    (records
      : ∀ ref,
          HasRecordedFailure work failed events.length ref
          → HasRecordedFailure work oldFailed before.length ref)
    : ReportingNoticesCovered ancestry work initial matching events failed := by
  refine ⟨healthyCovered, ?_⟩
  intro node dependencies producer known notice
  rcases notice.2.1 with ⟨healthy, _⟩ | ⟨_, recorded⟩
  · exact healthyCovered node .group dependencies producer known
      ⟨notice, healthy, by intro impossible; cases impossible⟩
  · apply covered.2 node dependencies producer known
    exact ⟨fun announced => notice.1 (notices announced),
      Or.inr ⟨rfl, records node.ref recorded⟩,
      nodeProducers node dependencies producer known notice,
      CanAnnounce.group_dependencies_before notice known valid coherent roleCoherent covered.1
        explained included notices completions producers⟩

-----------------------------------------------------------------------------------------
-- A ready settlement cannot uncover an unannounced failed group
-----------------------------------------------------------------------------------------

/-- One ready task settlement preserves group notice coverage when no producer is newly
published. Witness: an old recorded failure transports directly; otherwise the newly
failing contributor was healthy and outstanding before settlement, so its eligible
notice was already covered. No terminal reporting or runtime queue invariant is assumed.
-/
theorem group_notices_covered_settlement
    {ancestry bound roles work groups streams initial before events oldMatching matching
      oldFailed failed occurrence owners producer payload}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (covered : ReportingNoticesCovered ancestry work initial oldMatching before oldFailed)
    (healthyCovered
      : SupportedNoticesCovered ancestry work initial matching events failed)
    (explained : Explains work groups streams events matching failed)
    (oldExplained : Explains work groups streams before oldMatching oldFailed)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work oldMatching before oldFailed occurrence producer)
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
    (publications
      : ∀ task, Published matching events task → Published oldMatching before task)
    (records
      : ∀ ref,
          HasRecordedFailure work failed events.length ref
          → HasRecordedFailure work oldFailed before.length ref ∨ ref ∈ owners)
    : ReportingNoticesCovered ancestry work initial matching events failed := by
  refine ⟨healthyCovered, ?_⟩
  intro node dependencies birth descriptor notice
  have produced : ∀ source, birth = some source → Published oldMatching before source := by
    intro source generated
    exact publications source (notice.2.2.1 source generated)
  have dependenciesBefore := CanAnnounce.group_dependencies_before notice descriptor valid
    coherent roleCoherent covered.1 explained included notices completions
    (fun _ _ _ _ task published =>
      oldExplained.published_producer task (publications _ published))
  have fresh : node.ref ∉ announcedRefs initial before :=
    fun announced => notice.1 (notices announced)
  rcases notice.2.1 with ⟨healthy, _⟩ | ⟨_, recorded⟩
  · exact healthyCovered node .group dependencies birth descriptor
      ⟨notice, healthy, by intro impossible; cases impossible⟩
  · by_cases oldRecord : HasRecordedFailure work oldFailed before.length node.ref
    · exact covered.2 node dependencies birth descriptor
        ⟨fresh, Or.inr ⟨rfl, oldRecord⟩, produced, dependenciesBefore⟩
    · have contributor : node.ref ∈ owners := (records node.ref recorded).resolve_left oldRecord
      have healthy := Explains.group_healthy_of_no_recorded_failure coherent roleCoherent
        oldExplained descriptor oldRecord produced
        (fun ref member => (dependenciesBefore ref member).1)
      apply covered.2 node dependencies birth descriptor
      refine ⟨fresh, Or.inl ⟨healthy, Or.inr ?_⟩, produced, dependenciesBefore⟩
      intro accounted
      rcases accounted occurrence owners ⟨producer, payload, known⟩ contributor
        with cancelled | published
      · exact ready.2.1 cancelled
      · exact ready.1 published

-----------------------------------------------------------------------------------------
-- Object publication retains eligible failed co-owners
-----------------------------------------------------------------------------------------

/-- A ready group's eligible healthy or retained-failure owner is already announced.
Witness: its descriptor and full satisfied ancestry contradict group notice coverage if
the owner is fresh. Shared ownership is not required to be healthy in this statement.
-/
theorem reporting_ready_owner_announced
    {ancestry bound work initial matching events failed address owners producer payload
      ref}
    (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (covered : GroupNoticesCovered work initial matching events failed)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (member : ref ∈ owners)
    (ready : CanPublish work matching events failed (.executionGroup address) producer)
    (available
      : ¬NodeFailed work matching events failed ref
        ∨ HasRecordedFailure work failed events.length ref)
    (dependencies
      : ∀ ancestor ∈ ancestry ref,
          DependencySatisfied work initial matching events failed ancestor)
    : ref ∈ announcedRefs initial events := by
  classical
  apply Classical.byContradiction
  intro fresh
  obtain ⟨node, nodeDependencies, descriptor, same⟩ := known.executionGroup_owner member
  apply covered node nodeDependencies producer descriptor
  refine ⟨same ▸ fresh, ?_, ready.2.2.1, ?_⟩
  · rcases available with healthy | recorded
    · refine Or.inl ⟨same ▸ healthy, Or.inr ?_⟩
      intro accounted
      rcases accounted (.executionGroup address) owners ⟨producer, payload, known⟩
        (same ▸ member) with cancelled | published
      · exact ready.2.1 cancelled
      · exact ready.1 published
    · exact Or.inr ⟨rfl, same ▸ recorded⟩
  · intro ancestor contributes
    apply dependencies ancestor
    simpa only [DeferOnly.node_dependencies coherent descriptor, same] using contributes

/-- A ready object publication preserves all eligible group notices, including failed
co-owners. Witness: full ancestry transports backwards; a newly produced group either
reuses an already-covered owner or depends on an outstanding producer owner. Failure
settlement evidence is unchanged by the publication.
-/
theorem group_notices_covered_publication
    {ancestry bound roles work groups streams initial before events oldMatching matching
      failed address owners producer payload}
    (valid : Valid ancestry bound) (coherent : MixedRefs.WorkAt ancestry 0 bound work)
    (roleCoherent : RefRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (covered : ReportingNoticesCovered ancestry work initial oldMatching before failed)
    (healthyCovered
      : SupportedNoticesCovered ancestry work initial matching events failed)
    (explained : Explains work groups streams events matching failed)
    (failureTransport
      : ∀ ref,
          NodeFailed work oldMatching before failed ref
          → NodeFailed work matching events failed ref)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ready : CanPublish work oldMatching before failed (.executionGroup address) producer)
    (unavailable
      : ∀ ref ∈ owners, ¬DependencySatisfied work initial oldMatching before failed ref)
    (oldProducers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published oldMatching before occurrence
          → ∀ source, producer = some source → Published oldMatching before source)
    (notices : (announcedRefs initial before).Subset (announcedRefs initial events))
    (completions : (completedRefs events).Subset (completedRefs before))
    (publications
      : ∀ task,
          Published matching events task
          → Published oldMatching before task ∨ task = .executionGroup address)
    (records
      : ∀ ref,
          HasRecordedFailure work failed events.length ref
          → HasRecordedFailure work failed before.length ref)
    : ReportingNoticesCovered ancestry work initial matching events failed := by
  have producers : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload → Published matching events occurrence →
      ∀ source, producer = some source → Published oldMatching before source := by
    intro occurrence otherOwners birth result task published source generated
    rcases publications occurrence published with earlier | rfl
    · exact oldProducers _ _ _ _ task earlier source generated
    · exact ready.2.2.1 source ((TaskAt.unique known task).2.1.trans generated)
  apply group_notices_covered_noncarrier valid coherent roleCoherent covered
    healthyCovered explained failureTransport notices
    (fun _ _ _ member => completions member) producers ?_ records
  intro node dependencies birth descriptor notice source generated
  rcases publications source (notice.2.2.1 source generated) with earlier | rfl
  · exact earlier
  subst birth
  have dependenciesBefore := CanAnnounce.group_dependencies_before notice descriptor valid
    coherent roleCoherent covered.1 explained failureTransport notices
    (fun _ _ _ member => completions member) producers
  obtain ⟨producerOwners, ancestor, value, ref, task, member, support⟩ :=
    deferred_producer_dependency coherent continuous ordered descriptor
  have contributes := (TaskAt.unique task known).1 ▸ member
  rcases support with reused | dependency
  · have available : ¬NodeFailed work oldMatching before failed ref
        ∨ HasRecordedFailure work failed before.length ref := by
      rcases notice.2.1 with ⟨healthy, _⟩ | ⟨_, recorded⟩
      · exact Or.inl (fun failure => healthy (failureTransport _ (reused ▸ failure)))
      · exact Or.inr (reused ▸ records node.ref recorded)
    have notified := reporting_ready_owner_announced coherent covered.2 known contributes
      ready available (by
        intro ancestor member
        apply dependenciesBefore ancestor
        simpa only [DeferOnly.node_dependencies coherent descriptor, ← reused] using member)
    exact False.elim (notice.1 (reused ▸ notices notified))
  · exact False.elim (unavailable ref contributes (dependenciesBefore ref dependency))

end GraphQL.IncrementalDelivery.Correctness
