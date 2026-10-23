import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupTerminalTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamSourceOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalStreamReporting

/-! Actual startup terminal reports cover every unpublished generated attachment. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The unchanged common matching publishes every received source item
-----------------------------------------------------------------------------------------

/-- Every received item belongs to the common witness's actual publications.
Witness: source/output item-count equality and the closure ledger's complete prefix.
No fresh matching or response-value equality is used to identify the item.
-/
theorem startup_sourceItem_published {work inputs occurrence} {w : Witness}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (received
      : occurrence ∈ (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst)
    : Published w.matching w.events occurrence := by
  obtain ⟨_, _, _, _, prefixes⟩ := ledger
  have count : (w.events.flatMap normalizedItemValues).length
      = ((inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).length := by
    rw [Witness.startup_itemValues_eq_source startup valid started history]
    simp only [List.length_map]
  have member : occurrence
      ∈ ((inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
          (((w.events.take w.events.length).flatMap normalizedItemValues).length) := by
    rw [List.take_length, count, List.take_length]
    exact received
  simpa only [List.take_length] using prefixes w.events.length occurrence member

/-- A canonical nonterminal event remains in the full normalized atomic output.
Witness: the exact optional terminal suffix adds no replacements or discarded controls.
-/
theorem Witness.startup_event_mem_fullOutput {work inputs event} {w : Witness}
    (startup : InitialStartup)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (member : event ∈ w.events)
    : event
      ∈ (((State.initialize (Work.fromExecution work) startup)).runNormalized
          inputs).2.flatten.flatMap
          publicationAtoms := by
  rw [State.runNormalized_terminalShape _ inputs (State.initializeWithStartup_terminated _ startup)]
  exact List.mem_append_left _ (history ▸ member)

-----------------------------------------------------------------------------------------
-- A completed stream either published all its items or has a positive failure scope
-----------------------------------------------------------------------------------------

/-- An unpublished item of a concretely completed stream has a covering failure report.
Witness: successful source closure received every item and the common ledger published
them; a failure closure instead identifies a generated positive failing item. Generated
descriptor coherence keeps the reported list attachment exact.
No terminal reporting premise is used.
-/
theorem startup_completedStream_item_reported
    {work inputs w address ordinal owners producer payload stream dependencies birth}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (_matched : startup.MatchesWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ledger
      : BufferedClosureLedger work inputs w
          (State.initialize (Work.fromExecution work) startup))
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (known : TaskAt work (.item address ordinal) owners producer payload)
    (streamKnown : NodeAt work stream .stream dependencies birth)
    (contributes : stream.ref ∈ owners)
    (closed : stream.ref ∈ completedRefs w.events)
    (unpublished : ¬Published w.matching w.events (.item address ordinal))
    : FailureReportedFor w.events payload.path := by
  obtain ⟨event, member, completes⟩ := List.mem_flatMap.mp closed
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have allowed := explained.eventAllowed index event selected
  have full := Witness.startup_event_mem_fullOutput startup history member
  cases event <;> simp only [eventCompleted] at completes
  case groupValues | streamValues | workQueueTermination => cases completes
  case groupSuccess node groups streams | groupFailure node errors =>
    obtain ⟨parents, parent, descriptor⟩ := allowed.1
    exact False.elim (generated.groupStreamRefsDisjoint descriptor streamKnown
      (List.mem_singleton.mp completes).symm)
  case streamSuccess node =>
    have source := State.runNormalized_startup_streamCompletion_source
      (State.initialize (Work.fromExecution work) startup) inputs
      full rfl
    have inventory := valid.streamSuccess_itemInventory generated source
    exact False.elim (unpublished (startup_sourceItem_published startup valid started history ledger
      (inventory.2 _ owners ⟨producer, payload, known⟩
        ((List.mem_singleton.mp completes) ▸ contributes))))
  case streamFailure node errors =>
    have source := State.runNormalized_startup_streamCompletion_source
      (State.initialize (Work.fromExecution work) startup) inputs
      full rfl
    obtain ⟨_, _, _, failed, _, _⟩ := valid.streamFailure_itemInventory generated source
    have positive : 0 < errors := by
      simpa only [Payload.failure, Option.getD_some]
        using generated.taskFailure_positive failed rfl
    obtain ⟨parents, parent, descriptor⟩ := allowed.1
    have sameNode := generated.nodeRefCoherent _ _ _ _ _ _ _ _ descriptor streamKnown
      (List.mem_singleton.mp completes).symm
    have attachment : payload.path = stream.path := by
      obtain ⟨node, items, enclosing, result, children, located, entry,
        sameOwners, samePayload⟩ := known
      have sameRef : stream.ref = node.ref := by
        rw [sameOwners] at contributes
        exact List.mem_singleton.mp contributes
      have equal := generated.nodeRefCoherent _ _ _ _ _ _ _ _ streamKnown
        (.stream located) sameRef
      simp only [samePayload, Payload.path, equal]
    exact ⟨
      node,
      errors,
      positive,
      by rw [sameNode, attachment]; exact ⟨[], by simp⟩,
      Or.inr member
    ⟩

/-- Every unpublished released stream item is reported when concrete replay terminates.
Witness: root or published-producer stream coverage supplies a concrete closing event,
then source-success inventory or positive source failure supplies the covering scope.
This discharges the item branch of released-frontier reporting on the existing witness.
-/
theorem startup_terminal_availableItem_reported
    {work inputs w address ordinal owners producer payload}
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
    (known : TaskAt work (.item address ordinal) owners producer payload)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    (unpublished : ¬Published w.matching w.events (.item address ordinal))
    : FailureReportedFor w.events payload.path := by
  have descriptor := known
  obtain ⟨stream, entries, enclosing, result, children, located, selected,
    sameOwners, samePayload⟩ := descriptor
  have streamKnown : NodeAt work stream .stream enclosing producer := .stream located
  have completed := startup_terminal_availableStream_completed generated startup matched valid
    started history admitted ledger ended streamKnown available
  exact startup_completedStream_item_reported generated startup matched valid started
    history ledger explained known streamKnown (by simp [sameOwners]) completed
    unpublished

/-- Every unpublished generated task has a positive completion covering its attachment.
Actual registered-object reports and completed stream inventories supply the released
frontier. Structural producer inheritance extends those same report scopes to latent work.
-/
theorem startup_terminal_cancellationReporting {work inputs w}
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
    : CancellationReporting work w := by
  apply cancellationReporting_of_availableTaskReporting generated
  intro occurrence owners producer payload known available unpublished
  cases occurrence with
  | executionGroup address =>
      exact startup_terminal_availableObjectTask_reported generated startup matched valid started
        history admitted ledger explained ended known available unpublished
  | item address ordinal =>
      exact startup_terminal_availableItem_reported generated startup matched valid started
        history admitted ledger explained ended known available unpublished

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
