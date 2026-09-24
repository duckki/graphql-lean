import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedNoticeCoverage

/-! Preservation of the weaker mixed-work coverage witness by non-carrier events.
Object publication uses full defer ancestry; control events retain old publications.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Object publication cannot create a newly supported notice without a carrier
-----------------------------------------------------------------------------------------

/-- A ready deferred owner with satisfied ancestors is already announced under supported
coverage. Witness: its group descriptor otherwise supplies a supported notice.
-/
theorem supported_ready_owner_announced
    {ancestry bound work initial matching events failed address owners producer payload
      key}
    (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (covered : SupportedNoticesCovered ancestry work initial matching events failed)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (member : key ∈ owners)
    (ready : CanPublish work matching events failed (.executionGroup address) producer)
    (healthy : ¬NodeFailed work failed key)
    (dependencies
      : ∀ ancestor ∈ ancestry key,
          DependencySatisfied work initial matching events failed ancestor)
    : key ∈ announcedKeys initial events := by
  classical
  apply Classical.byContradiction
  intro fresh
  obtain ⟨node, nodeDependencies, descriptor, same⟩ := known.executionGroup_owner member
  apply covered node .group nodeDependencies producer descriptor
  refine ⟨
    ⟨same ▸ fresh, same ▸ healthy, Or.inr ?_, ready.2.2.1, ?_⟩,
    by intro impossible; cases impossible
  ⟩
  · intro accounted
    rcases accounted (.executionGroup address) owners ⟨producer, payload, known⟩ (same ▸ member)
      with cancelled | published
    · exact ready.2.1 cancelled
    · exact ready.1 published
  · intro ancestor contributes
    apply dependencies ancestor
    simpa only [DeferOnly.node_dependencies coherent descriptor, same] using contributes

/-- A ready object publication preserves supported coverage in arbitrary mixed work.
Witness: transport full dependencies backwards. A newly produced group reuses a covered
owner or waits on an outstanding one; a stream's full supporting dependency is
outstanding.
-/
theorem supported_coverage_publication
    {ancestry bound roles work initial before events oldMatching matching failed address
      owners producer payload}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (continuous : DeferContinuous ancestry work) (ordered : StreamOwnersOrdered work)
    (covered : SupportedNoticesCovered ancestry work initial oldMatching before failed)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (ready : CanPublish work oldMatching before failed (.executionGroup address) producer)
    (unavailable
      : ∀ key ∈ owners, ¬DependencySatisfied work initial oldMatching before failed key)
    (oldProducers
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published oldMatching before occurrence
          → ∀ producerOccurrence,
              producer = some producerOccurrence
              → Published oldMatching before producerOccurrence)
    (notices : (announcedKeys initial before).Subset (announcedKeys initial events))
    (completions : (completedKeys events).Subset (completedKeys before))
    (publications
      : ∀ task,
          Published matching events task
          → Published oldMatching before task ∨ task = .executionGroup address)
    (accounting
      : ∀ key,
          NodeAccounted work oldMatching before failed key
          → NodeAccounted work matching events failed key)
    : SupportedNoticesCovered ancestry work initial matching events failed := by
  have producers : ∀ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload → Published matching events occurrence →
      ∀ producerOccurrence, producer = some producerOccurrence
        → Published oldMatching before producerOccurrence := by
    intro occurrence otherOwners birth result task published producerOccurrence generated
    rcases publications occurrence published with earlier | rfl
    · exact oldProducers _ _ _ _ task earlier producerOccurrence generated
    · exact ready.2.2.1 producerOccurrence
        ((TaskAt.unique known task).2.1.trans generated)
  apply supported_coverage_noncarrier valid coherent roleCoherent covered
    (List.Subset.refl _) notices (fun _ _ _ member => completions member) producers
    accounting
  intro node kind dependencies nodeProducer descriptor supported producerOccurrence generated
  rcases publications producerOccurrence
      (supported.1.2.2.2.1 producerOccurrence generated) with earlier | rfl
  · exact earlier
  subst nodeProducer
  have dependenciesBefore := supported.dependencies_before descriptor valid coherent
    roleCoherent covered (List.Subset.refl _) notices
      (fun _ _ _ member => completions member) producers
  cases kind with
  | group =>
      obtain ⟨producerOwners, ancestor, value, key, task, member, support⟩ :=
        deferred_producer_dependency coherent continuous ordered descriptor
      have contributes := (TaskAt.unique task known).1 ▸ member
      rcases support with reused | dependency
      · have notified := supported_ready_owner_announced coherent covered known contributes
          ready (reused ▸ supported.1.2.1) (by
            intro ancestor member
            apply dependenciesBefore ancestor
            simpa only [DeferOnly.node_dependencies coherent descriptor, ← reused] using member)
        exact False.elim (supported.1.1 (reused ▸ notices notified))
      · exact False.elim (unavailable key contributes (dependenciesBefore key dependency))
  | stream =>
      obtain ⟨streamAddress, items, located⟩ := descriptor
      obtain ⟨ancestor, path, result, task⟩ := located_producer_context located
      have same := (TaskAt.unique task known).1
      rcases dependenciesBefore with empty | ⟨key, member, dependency, _⟩
      · exact False.elim (coherent_task_owners_nonempty coherent known (same ▸ empty))
      · exact False.elim (unavailable key (same ▸ member) dependency)

-----------------------------------------------------------------------------------------
-- Failure and stream completion preserve the same witness without new publications
-----------------------------------------------------------------------------------------

/-- Nonpublishing changes preserve supported coverage if they close no healthy defer key.
Witness: old causal publication evidence supplies every task and node producer; full
dependency transport accounts for newly cancelled mixed work without assuming that
every cancelled task's owners fail.
-/
theorem supported_coverage_control
    {ancestry bound roles work groups streams before events oldMatching matching failures
      failed}
    (valid : Valid ancestry bound) (coherent : MixedKeys.WorkAt ancestry 0 bound work)
    (roleCoherent : KeyRoles.WorkRoles roles work)
    (explained : Explains work groups streams before oldMatching failures)
    (covered
      : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
          oldMatching before (failures.map Prod.snd))
    (included : failures.map Prod.snd ⊆ failed)
    (notices
      : (announcedKeys ((groups ++ streams).map DeliveryNode.key) before).Subset
          (announcedKeys ((groups ++ streams).map DeliveryNode.key) events))
    (completions
      : ∀ key,
          roles key = false
          → ¬NodeFailed work failed key
          → key ∈ completedKeys events
          → key ∈ completedKeys before)
    (publications
      : ∀ task, Published matching events task → Published oldMatching before task)
    (accounting
      : ∀ key,
          NodeAccounted work oldMatching before (failures.map Prod.snd) key
          → NodeAccounted work matching events failed key)
    : SupportedNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.key)
        matching events failed := by
  refine supported_coverage_noncarrier valid coherent roleCoherent covered included notices
    completions ?_ accounting ?_
  · intro occurrence owners producer payload known published
    exact explained.published_producer known (publications occurrence published)
  · intro node kind dependencies producer _ supported producerOccurrence generated
    exact publications producerOccurrence
      (supported.1.2.2.2.1 producerOccurrence generated)

end GraphQL.IncrementalDelivery.Correctness
