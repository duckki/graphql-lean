import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupAvailableObjectTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupObjectProducedStreams
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemProducedStreams
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness

/-! Terminal startup replay accounts for all generated tasks by structural producer rank. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every root or published-producer stream actually completes at startup termination.
The object branch includes buffered children; the item branch uses the same publication
matching to recover the exact successful source item. No terminal accounting is assumed.
-/
theorem startup_terminal_availableStream_completed
    {work inputs w node dependencies producer} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .stream dependencies producer)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    : node.ref ∈ completedRefs w.events := by
  cases producer with
  | none =>
      exact startup_terminal_rootStream_completed startup valid started history ended known
  | some parent =>
      cases parent with
      | executionGroup source =>
          exact startup_terminal_objectProducedStream_completed generated startup matched valid
            started history admitted ledger ended known (available _ rfl)
      | item source ordinal =>
          exact startup_terminal_itemProducedStream_completed generated startup matched valid
            started history ended known
            (startup_published_item_success startup valid started history admitted ledger
              (available _ rfl))

/-- Roots and tasks with published producers are accounted on the actual startup history.
Registered objects use observed cancellation reports; items use actual stream closure and
the same explanation's outstanding-owner law. No raw-failure visibility premise is needed.
-/
theorem startup_terminal_availableTask_accounted
    {work inputs w occurrence owners producer payload} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (known : TaskAt work occurrence owners producer payload)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    : TaskAccounted work w.matching w.events w.failures occurrence := by
  cases occurrence with
  | executionGroup address =>
      exact startup_terminal_availableObjectTask_accounted generated startup matched valid
        started history admitted ledger explained ended known available
  | item address index =>
      have descriptor := known
      obtain ⟨stream, entries, enclosing, result, children, located, selected,
        sameOwners, samePayload⟩ := descriptor
      have streamKnown : NodeAt work stream .stream enclosing producer := .stream located
      have completed := startup_terminal_availableStream_completed generated startup matched valid
        started history admitted ledger ended streamKnown available
      apply Classical.byContradiction
      intro outstanding
      obtain ⟨ref, contributes, _, notClosed⟩ := explained.outstanding_owner known
        (generated.taskOwners_nonempty known) outstanding
      rw [sameOwners] at contributes
      exact notClosed ((List.mem_singleton.mp contributes).symm ▸ completed)

/-- All generated tasks are published or cancelled when the concrete queue terminates.
Witness: strong induction on structural producer rank. A cancelled producer cancels its
unpublished child; a published producer invokes complete registration or stream closure.
No fairness, recursive accounting assumption, or extra source premise is introduced.
-/
theorem startup_terminal_generatedTasks_accounted {work inputs w}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
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
              exact startup_terminal_availableTask_accounted generated startup matched valid
                  started history admitted
                ledger explained ended known (fun _ impossible => by cases impossible)
          | some parent =>
              obtain ⟨lower, parents, ancestor, result, parentKnown⟩ := known.producer_dependency
              have parentAccounted := ih parent.dependencyRank (by omega) parent parents
                ancestor result rfl parentKnown
              rcases parentAccounted with cancelled | delivered
              · exact .inl (TaskCancelled.producerCancelled known published cancelled)
              · apply startup_terminal_availableTask_accounted generated startup matched valid
                  started history admitted
                  ledger explained ended known
                intro candidate sameParent
                cases sameParent
                exact delivered
  exact fun occurrence owners producer payload known =>
    all occurrence.dependencyRank occurrence owners producer payload rfl known

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
