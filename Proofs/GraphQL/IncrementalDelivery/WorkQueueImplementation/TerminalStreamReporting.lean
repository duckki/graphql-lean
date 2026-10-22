import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalGeneratedTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalCancellationReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemPublicationReflection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors

/-! Completed released streams report every unpublished item attachment. -/

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
theorem sourceItem_published {work inputs occurrence} {w : Witness}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (received
      : occurrence ∈ (inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst)
    : Published w.matching w.events occurrence := by
  obtain ⟨_, _, _, _, prefixes⟩ := ledger
  have count : (w.events.flatMap normalizedItemValues).length
      = ((inputs.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).length := by
    rw [Witness.itemValues_eq_source valid started history]
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
theorem Witness.event_mem_fullOutput {work inputs event} {w : Witness}
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (member : event ∈ w.events)
    : event
      ∈ ((initialQueue work).runNormalized inputs).2.flatten.flatMap
          publicationAtoms := by
  rw [(initialQueue work).runNormalized_terminalShape inputs (createWorkQueue_terminated _)]
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
theorem completedStream_item_reported
    {work inputs w address ordinal owners producer payload stream dependencies birth}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
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
  have full := Witness.event_mem_fullOutput history member
  cases event <;> simp only [eventCompleted] at completes
  case groupValues | streamValues | workQueueTermination => cases completes
  case groupSuccess node groups streams | groupFailure node errors =>
    obtain ⟨parents, parent, descriptor⟩ := allowed.1
    exact False.elim (generated.groupStreamRefsDisjoint descriptor streamKnown
      (List.mem_singleton.mp completes).symm)
  case streamSuccess node =>
    have inventory := createWorkQueue_runNormalized_streamSuccess_itemInventory
      generated valid full
    exact False.elim (unpublished (sourceItem_published valid started history ledger
      (inventory.2 _ owners ⟨producer, payload, known⟩
        ((List.mem_singleton.mp completes) ▸ contributes))))
  case streamFailure node errors =>
    have source := createWorkQueue_runNormalized_streamCompletion_source
      (Work.fromExecution work) inputs full rfl
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
theorem terminal_availableItem_reported
    {work inputs w address ordinal owners producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : TaskAt work (.item address ordinal) owners producer payload)
    (available : ∀ parent, producer = some parent → Published w.matching w.events parent)
    (unpublished : ¬Published w.matching w.events (.item address ordinal))
    : FailureReportedFor w.events payload.path := by
  have descriptor := known
  obtain ⟨stream, entries, enclosing, result, children, located, selected,
    sameOwners, samePayload⟩ := descriptor
  have streamKnown : NodeAt work stream .stream enclosing producer := .stream located
  have completed : stream.ref ∈ completedRefs w.events := by
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
  exact completedStream_item_reported generated valid started history ledger explained
    known streamKnown (by simp [sameOwners]) completed unpublished

-----------------------------------------------------------------------------------------
-- The remaining frontier obligation concerns registered execution-group tasks only
-----------------------------------------------------------------------------------------

/-- Unpublished released execution-group tasks have a covering actual failure completion.
This proof-only construction target retains `w`'s events, matching, and cuts. It does not
assume cancellation reporting for streams, unreleased work, or the whole queue.
-/
def AvailableObjectTaskReporting (work : Execution.Work) (w : Witness) : Prop :=
  ∀ address owners producer payload,
    TaskAt work (.executionGroup address) owners producer payload
    → (∀ parent, producer = some parent → Published w.matching w.events parent)
    → ¬Published w.matching w.events (.executionGroup address)
    → FailureReportedFor w.events payload.path

/-- Registered-object frontier reporting suffices for the complete reporting leaf.
Witness: the proved stream-item branch and producer-rank inheritance supply every other
task. The object target remains to be constructed from concrete retained failures and
ancestor cancellations, not assumed by the public implementation-conformance statement.
-/
theorem cancellationReporting_of_availableObjectTaskReporting
    {work inputs w} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (admitted : PublicationAdmission work w)
    (ledger : BufferedClosureLedger work inputs w)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (objects : AvailableObjectTaskReporting work w)
    : CancellationReporting work w := by
  apply cancellationReporting_of_availableTaskReporting generated
  intro occurrence owners producer payload known available unpublished
  cases occurrence with
  | executionGroup address =>
      exact objects address owners producer payload known available unpublished
  | item address ordinal =>
      exact terminal_availableItem_reported generated valid started history admitted ledger
        explained ended known available unpublished

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
