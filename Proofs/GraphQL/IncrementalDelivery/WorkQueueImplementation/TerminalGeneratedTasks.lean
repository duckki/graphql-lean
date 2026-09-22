import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectProducedStreamNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness

/-! Every generated structural task is accounted at concrete termination. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Root and published-producer tasks use complete registration and stream closure
-----------------------------------------------------------------------------------------

/-- Root tasks and tasks with published producers are accounted at termination.
Witness: object tasks are registered; items belong to root or published-producer streams,
whose completed keys exclude an outstanding item on the same explained history.
-/
theorem terminal_availableTask_accounted
    {work inputs w occurrence owners producer payload} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : TaskAt work occurrence owners producer payload)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    : TaskAccounted work w.matching w.events w.failures occurrence := by
  cases occurrence with
  | executionGroup address =>
      cases producer with
      | none =>
          exact terminal_rootTask_accounted generated valid started history ledger
            explained visible ended known
      | some parent =>
          cases parent with
          | executionGroup source =>
              exact terminal_objectProducedTask_accounted generated valid started history
                admitted ledger explained visible ended known (available _ rfl)
          | item source index =>
              exact terminal_itemProducedTask_accounted generated valid started history
                admitted ledger explained visible ended known (available _ rfl)
  | item address index =>
      have descriptor := known
      obtain ⟨stream, entries, enclosing, result, children, located, selected,
        sameOwners, samePayload⟩ := descriptor
      have streamKnown : NodeAt work stream .stream enclosing producer := .stream located
      have completed : stream.key ∈ completedKeys w.events := by
        cases producer with
        | none =>
            exact terminal_rootStream_completed valid started history ended streamKnown
        | some parent =>
            cases parent with
            | executionGroup source =>
                exact terminal_objectProducedStream_completed generated valid started history
                  admitted ledger ended streamKnown (available _ rfl)
            | item source ordinal =>
                exact terminal_itemProducedStream_of_publication generated valid started history
                  admitted ledger ended streamKnown (available _ rfl)
      apply Classical.byContradiction
      intro outstanding
      obtain ⟨key, contributes, _, notClosed⟩ := explained.outstanding_owner known
        (generated.taskOwners_nonempty known) outstanding
      rw [sameOwners] at contributes
      exact notClosed ((List.mem_singleton.mp contributes).symm ▸ completed)

-----------------------------------------------------------------------------------------
-- A finite structural rank propagates cancellation through all unpublished producers
-----------------------------------------------------------------------------------------

/-- All generated tasks are published or cancelled when the concrete queue terminates.
Witness: strong induction on structural producer rank. A cancelled producer cancels its
unpublished child; a published producer invokes complete registration or stream closure.
No fairness, recursive accounting assumption, or extra source premise is introduced.
-/
theorem terminal_generatedTasks_accounted {work inputs w} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (visible
      : ((initialQueue work).objectFailureContributions inputs.flatten).Subset
          (failedBefore w.failures w.events.length))
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    : TaskAccounting work w := by
  have all : ∀ rank occurrence owners producer payload,
      occurrence.dependencyRank = rank → TaskAt work occurrence owners producer payload
      → TaskAccounted work w.matching w.events w.failures occurrence := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
        intro occurrence owners producer payload same known
        classical
        by_cases published : Published w.matching w.events occurrence
        · exact .inr published
        · cases producer with
          | none =>
              exact terminal_availableTask_accounted generated valid started history admitted
                ledger explained visible ended known (fun _ impossible => by cases impossible)
          | some parent =>
              obtain ⟨lower, parents, ancestor, result, parentKnown⟩ := known.producer_dependency
              have parentAccounted := ih parent.dependencyRank (by omega) parent parents
                ancestor result rfl parentKnown
              rcases parentAccounted with cancelled | delivered
              · exact .inl (TaskCancelled.producerCancelled known published cancelled)
              · apply terminal_availableTask_accounted generated valid started history admitted
                  ledger explained visible ended known
                intro candidate sameParent
                cases sameParent
                exact delivered
  exact fun occurrence owners producer payload known =>
    all occurrence.dependencyRank occurrence owners producer payload rfl known

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
