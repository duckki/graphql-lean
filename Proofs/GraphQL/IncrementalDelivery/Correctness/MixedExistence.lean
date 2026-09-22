import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedProgressEvents

/-! Complete finite runs for arbitrary coherent generated mixed defer/stream work.
Supported notice coverage is a proof choice, not a restriction on admitted histories.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Least outstanding owners have full support, including stream-dependency ancestry
-----------------------------------------------------------------------------------------

/-- A least outstanding healthy owner is supported once smaller healthy keys satisfy
dependencies. Witness: ordinary eligibility plus, for streams, the selected defer
dependency's strict, healthy ancestry. This excludes merely early silent-accounting
notices.
-/
theorem least_owner_supported
    {ancestry bound work initial matching events failed occurrence owners producer payload
      node kind dependencies}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (ordered : StreamOwnersOrdered work)
    (known : TaskAt work occurrence owners producer payload)
    (ready : CanPublish work matching events failed occurrence producer)
    (descriptor : NodeAt work node kind dependencies producer)
    (member : node.key ∈ owners) (healthy : ¬NodeFailed work failed node.key)
    (fresh : node.key ∉ announcedKeys initial events)
    (smaller
      : ∀ key,
          key < node.key
          → ¬NodeFailed work failed key
          → DependencySatisfied work initial matching events failed key)
    : SupportedNotice ancestry work initial matching events failed node kind dependencies
        producer := by
  have eligible := least_owner_announceable valid coherent ordered known ready descriptor
    member healthy fresh smaller
  refine ⟨eligible, ?_⟩
  intro stream
  subst kind
  rcases eligible.2.2.2.2 with empty | ⟨key, contributes, dependency⟩
  · exact Or.inl empty
  · obtain ⟨group, parents, birth, groupKnown, same⟩ :=
      stream_dependency_group descriptor contributes
    refine Or.inr ⟨key, contributes, dependency, ?_⟩
    intro ancestor included
    have full := DeferOnly.node_dependencies coherent groupKnown
    have dependencyMember : ancestor ∈ parents := by simpa only [full, same] using included
    apply smaller ancestor
    · have before := coherent_group_dependencies valid coherent groupKnown ancestor dependencyMember
      have below := coherent_stream_dependencies ordered descriptor key contributes
      simpa only [same] using Nat.lt_trans before (same ▸ below)
    · intro failed
      exact dependency.1 (same ▸ NodeFailed.groupDependency groupKnown dependencyMember failed)

-----------------------------------------------------------------------------------------
-- A maximal supported history accounts for every task
-----------------------------------------------------------------------------------------

/-- A supported explained prefix extends to task accounting without changing its outputs.
Witness: maximize a finite extension preserving supported notice coverage. Healthy accounted
groups close with covering notices; stream completions preserve support. A least healthy
outstanding owner must then be announced and has a coverage-preserving success or failure
step, contradicting maximality. Matching and failure evidence remain existential.
-/
theorem mixed_supported_accounted_extension
    {ancestry bound roles paths pathBound work groups streams head matching failures}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (initial : Explains work groups streams head matching failures)
    (coverage
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
          matching head (failures.map Prod.snd))
    : ∃ tail next cuts,
        Explains work groups streams (head ++ tail) next cuts
        ∧ ∀ occurrence owners producer payload,
            TaskAt work occurrence owners producer payload
            → Accounted work next (head ++ tail)
                (failedBefore cuts (head ++ tail).length) occurrence := by
  classical
  obtain ⟨tail, matching, failures, explained, covered, maximal⟩ :=
    initial.maximal_extension_preserving
      (fun events matching failures => SupportedNoticesCovered ancestry work
        ((groups ++ streams).map DeliveryNode.key) matching events (failures.map Prod.snd))
      coverage
  generalize joined : head ++ tail = events at explained covered maximal
  have stable := explained.2.1.failedBefore_eq (Nat.le_refl _)
  have dependency {key}
      (healthy : ¬NodeFailed work (failedBefore failures events.length) key)
      (accounted : NodeAccounted work matching events (failedBefore failures events.length) key)
      : DependencySatisfied work ((groups ++ streams).map DeliveryNode.key) matching events
          (failedBefore failures events.length) key := by
    refine ⟨healthy, ?_⟩
    by_cases supported : ∃ birth, NodeHasProducer work key birth
    · by_cases announced :
        key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events
      · by_cases completed : key ∈ completedKeys events
        · exact Or.inr (Or.inl completed)
        · obtain ⟨birth, node, kind, parents, descriptor, same⟩ := supported
          cases kind with
          | group =>
              obtain ⟨newGroups, newStreams, extended, notices⟩ :=
                explained.complete_group_noticesCovered descriptor
                  (same ▸ ⟨announced, completed⟩) (same ▸ healthy) (same ▸ accounted)
              have impossible := maximal [.groupSuccess node newGroups newStreams]
                matching failures extended (supportedNoticesCovered_of_noticesCovered notices)
              cases impossible
          | stream =>
              obtain ⟨extended, retained⟩ := supported_complete_stream valid coherent
                roleCoherent explained covered descriptor (same ▸ ⟨announced, completed⟩)
                  (same ▸ healthy) (same ▸ accounted)
              have impossible := maximal [.streamSuccess node] matching failures extended retained
              cases impossible
      · exact Or.inr (Or.inr ⟨announced, accounted⟩)
    · exact Or.inl supported
  have accounted : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload →
      Accounted work matching events (failedBefore failures events.length) occurrence := by
    intro occurrence owners producer payload known
    apply Classical.byContradiction
    intro outstanding
    obtain ⟨next, nextOwners, nextProducer, result, key, task, ready, member, healthy, least⟩ :=
      least_ready_owner valid coherent continuous ordered explained known outstanding
    have notified : key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events := by
      apply Classical.byContradiction
      intro fresh
      obtain ⟨node, kind, dependencies, descriptor, same⟩ := task.owner_at_producer member
      have supported := least_owner_supported valid coherent ordered task ready descriptor
        (same ▸ member) (same ▸ healthy) (same ▸ fresh)
        (fun smaller before smallerHealthy => dependency smallerHealthy
          (least smaller (by simpa only [same] using before) smallerHealthy))
      exact covered node kind dependencies nextProducer descriptor
        (by simpa only [stable] using supported)
    obtain ⟨event, nextMatching, cuts, extended, retained⟩ :=
      extend_ready_supported valid coherent roleCoherent continuous ordered pathCoherent
        explained covered task ready ⟨key, member, notified, healthy⟩
    have impossible := maximal [event] nextMatching cuts extended retained
    cases impossible
  exact ⟨tail, matching, failures, joined.symm ▸ explained, joined.symm ▸ accounted⟩

/-- Every supported mixed-work prefix has a terminal continuation preserving its initial
notices and all supplied batches. Witness: reach task accounting, append only new batches,
then use the existing finalization theorem. No scheduler policy or host fairness is assumed.
-/
theorem mixed_supported_continuation
    {ancestry bound roles paths pathBound work groups streams events matching failures
      batches}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (explained : Explains work groups streams events matching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
          matching events (failures.map Prod.snd))
    (batched : WorkBatching events batches)
    : (History.mk groups streams batches).CanFinish work := by
  obtain ⟨tail, next, cuts, extended, accounted⟩ := mixed_supported_accounted_extension
    valid coherent roleCoherent continuous ordered pathCoherent explained covered
  obtain ⟨closures, run, _, _⟩ :=
    (batched.append (WorkBatching.singletons tail)).finish_accounted extended accounted
  refine ⟨tail.map (fun event => [event]) ++ closures.map (fun event => [event])
    ++ [[.workQueueTermination]], ?_⟩
  simpa only [List.append_assoc] using run

/-- Every nonempty coherent mixed work tree has a complete finite run. Witness: covering
initial notices establish support, then supported-prefix continuation supplies completion.
This does not assert completion of arbitrary admitted prefixes or host fairness.
-/
theorem mixed_completeRun_exists
    {ancestry bound roles paths pathBound work}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (pathCoherent : MixedOwnerPaths.WorkAt paths pathBound work)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history := by
  obtain ⟨groups, streams, initialized⟩ :=
    initialization_exists valid coherent continuous ordered nonempty
  obtain ⟨groups, streams, initialized, covers⟩ := initialized.covering_exists
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  obtain ⟨batches, run⟩ := mixed_supported_continuation valid coherent roleCoherent
    continuous ordered pathCoherent initial
    (supportedNoticesCovered_of_noticesCovered (NoticesCovered.initial covers _))
    WorkBatching.nil
  exact ⟨⟨groups, streams, batches⟩, run⟩

end GraphQL.IncrementalDelivery.Correctness
