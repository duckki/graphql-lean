import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupProducedTaskRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemPublicationReflection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRegisteredTasks

/-! Root and published producers expose every available startup object task for terminal
  accounting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Roots and published producers permanently register all their structural object tasks.
Object publications recover their actual storing callback; item publications reflect an
actual successful item input. Neither task publication nor terminal accounting is assumed.
-/
theorem startup_availableObjectTask_registered
    {work inputs w address owners producer payload} (generated : ExecutedWork work)
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
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ task ∈ (initial.runNormalized inputs).1.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have registration := (generated.startup_runNormalized_frame canonical startup matched inputs
    valid started).producerRegistrations
  cases producer with
  | none => exact registration.root_registered known
  | some parent =>
      cases parent with
      | executionGroup source =>
          exact startup_published_object_child_registered generated startup matched valid started
            history admitted ledger known (available _ rfl)
      | item source ordinal =>
          exact registration.item_registered known
            (startup_published_item_success startup valid started history admitted ledger
              (available _ rfl))

/-- Every root or published-producer object task is accounted when actual startup replay ends. -/
theorem startup_terminal_availableObjectTask_accounted
    {work inputs w address owners producer payload} (generated : ExecutedWork work)
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
      : Explains work (initialQueue work).initialGroups (initialQueue work).initialStreams
          w.events w.matching w.failures)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    : TaskAccounted work w.matching w.events w.failures (.executionGroup address) := by
  obtain ⟨task, registered, identity, _⟩ := startup_availableObjectTask_registered generated
    startup matched valid started history admitted ledger known available
  exact identity ▸ startup_terminal_registeredTask_accounted generated startup matched valid started
    history ledger explained ended registered

/-- Every unpublished available object task has a covering positive completion at termination. -/
theorem startup_terminal_availableObjectTask_reported
    {work inputs w address owners producer payload} (generated : ExecutedWork work)
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
      : Explains work (initialQueue work).initialGroups (initialQueue work).initialStreams
          w.events w.matching w.failures)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    (unpublished : ¬Published w.matching w.events (.executionGroup address))
    : FailureReportedFor w.events payload.path := by
  obtain ⟨task, registered, identity, _⟩ := startup_availableObjectTask_registered generated
    startup matched valid started history admitted ledger known available
  exact startup_terminal_registeredTask_reported generated startup matched valid started history
    ledger explained ended registered known identity unpublished

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
