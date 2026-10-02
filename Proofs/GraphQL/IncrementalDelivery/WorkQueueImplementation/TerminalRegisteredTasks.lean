import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorCoverageReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.EndpointFailureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Concrete termination accounts for every permanently registered object task. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Concrete root exhaustion retires every healthy registered contributor
-----------------------------------------------------------------------------------------

/-- A healthy registered contributor has retired by actual terminal replay.
Witness: replay coverage and empty terminal roots rule out a live lookup, while permanent
task registration retains its group key. This includes groups that were never announced.
-/
theorem ExecutedWork.terminal_healthyContributor_retired {work inputs task key}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (member
      : task
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            inputs.flatten).tasks)
    (contributes : key ∈ task.groups.map Execution.DeliveryNode.key)
    (healthy
      : ¬GroupInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions
            inputs.flatten) key)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        inputs.flatten).RetiredGroup
        key := by
  have initial := createWorkQueue_registration work
  have registered := State.replayGraphEvents_registration initial.1 initial.2 inputs.flatten
    (fun _ included => valid.eachMatches included)
  have roots := (createWorkQueue_replayGraphEvents_terminalRoots started ended).1
  have accepts := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  apply State.RetiredGroup.of_lookup_none (registered.2.1 task member key contributes)
  cases found
        : ((State.initialize (Work.fromExecution work)).replayGraphEvents
            inputs.flatten).groupNode?
            key with
  | none => rfl
  | some node =>
      obtain ⟨root, active, _⟩ := generated.replayGraphEvents_healthyContributorsCovered
        inputs.flatten valid accepts task member key contributes healthy ⟨node, found⟩
      rw [roots] at active
      cases active

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Connect concrete retirement to the existing canonical matching and failure cuts
-----------------------------------------------------------------------------------------

/-- Every registered object task is published or cancelled on the explained terminal witness.
Witness: a healthy owner must retire and therefore publish the task; if all owners failed,
the same visible accepted-failure inventory supplies cancellation at a historical cut.
No completion notice is required for the healthy-owner publication argument.
-/
theorem terminal_registeredTask_accounted {work inputs task} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (member : task ∈ ((initialQueue work).replayGraphEvents inputs.flatten).tasks)
    : TaskAccounted work w.matching w.events w.failures task.occurrence := by
  classical
  by_cases published : Published w.matching w.events task.occurrence
  · exact .inr published
  have matched := (createWorkQueue_replay_regionInventory valid).matching task member
  obtain ⟨address, payload, producer, identity, known⟩ := matched.1
  by_cases healthyOwner :
    ∃ key ∈ task.groups.map Execution.DeliveryNode.key,
      ¬GroupInvalidated work
        ((initialQueue work).objectFailureContributions inputs.flatten) key
  · obtain ⟨key, contributes, healthy⟩ := healthyOwner
    have retired := generated.terminal_healthyContributor_retired valid started ended
      member contributes healthy
    have recordHealthy := matched.contributor_recordHealthy generated contributes healthy
    have delivered := retiredGroup_contributorPublished generated valid started history ledger
      (identity ▸ known) contributes retired recordHealthy
    exact .inr (identity.symm ▸ delivered)
  · apply Or.inl
    apply explained.snapshot_taskCancelled
    refine Causality.TaskCancelled.owners ⟨producer, payload, known⟩ published
      (generated.taskOwners_nonempty known) ?_
    intro key contributes
    have invalid : GroupInvalidated work
        ((initialQueue work).objectFailureContributions inputs.flatten) key := by
      apply Classical.byContradiction
      intro healthy
      exact healthyOwner ⟨key, contributes, healthy⟩
    exact (invalid.mono visible).toCausality (Published w.matching w.events)

/-- A structural group with a registered contributor is failed or fully accounted at termination.
Witness: an invalidated group has a historical failure cause; otherwise terminal coverage
forces retirement and the existing retirement theorem accounts for every structural owner.
Other contributors need not be separately assumed registered or already settled.
-/
theorem terminal_registeredContributor_groupAccounted
    {work inputs group dependencies producer task} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : NodeAt work group .group dependencies producer)
    (member : task ∈ ((initialQueue work).replayGraphEvents inputs.flatten).tasks)
    (contributes : group.key ∈ task.groups.map Execution.DeliveryNode.key)
    : NodeFailed work w.matching w.events w.failures group.key
      ∨ NodeAccounted work w.matching w.events w.failures group.key := by
  classical
  by_cases invalid : GroupInvalidated work
      ((initialQueue work).objectFailureContributions inputs.flatten) group.key
  · exact .inl (invalid.toNodeFailed explained visible)
  · have retired := generated.terminal_healthyContributor_retired valid started ended
      member contributes invalid
    exact .inr (retiredGroup_nodeAccounted generated valid started history ledger known retired
      (fun failure => invalid ((generated.groupRecordInvalidated_iff_groupInvalidated known).mp
        failure)))

/-- Every producer-free object task is accounted at actual termination.
Witness: inverse root lowering supplies permanent registration, then registered-task
accounting uses the canonical publication matching and historical cancellation cuts.
-/
theorem terminal_rootTask_accounted {work inputs address owners payload} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : TaskAt work (.executionGroup address) owners none payload)
    : TaskAccounted work w.matching w.events w.failures (.executionGroup address) := by
  obtain ⟨task, member, identity, _⟩ :=
    TaskAt.executionGroup_replay_registered known inputs.flatten
  exact identity ▸ terminal_registeredTask_accounted generated valid started history ledger
    explained visible ended member

/-- A producer-free structural group is failed or fully accounted at termination.
Witness: its own structural contributor is registered by root lowering; the terminal
registered-contributor theorem also covers all other contributors to that same group.
-/
theorem terminal_rootGroup_accounted {work inputs group dependencies} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : NodeAt work group .group dependencies none)
    : NodeFailed work w.matching w.events w.failures group.key
      ∨ NodeAccounted work w.matching w.events w.failures group.key := by
  obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
  cases occurrence with
  | executionGroup address =>
      obtain ⟨candidate, member, _, groups⟩ :=
        TaskAt.executionGroup_replay_registered task inputs.flatten
      exact terminal_registeredContributor_groupAccounted generated valid started history ledger
        explained visible ended known member (groups.symm ▸ contributes)
  | item address index =>
      obtain ⟨stream, entries, enclosing, result, children, located, entry, sameOwners,
        samePayload⟩ := task
      rw [sameOwners] at contributes
      exact False.elim (generated.groupStreamKeysDisjoint known (.stream located)
        (List.mem_singleton.mp contributes))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
