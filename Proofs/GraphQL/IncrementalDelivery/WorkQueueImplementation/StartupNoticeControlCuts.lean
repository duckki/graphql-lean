import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalNoticeCompletion

/-! Actual startup carriers retain notice equality and all source-ledger group closures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Keep the same selected raw carrier for both control projections
-----------------------------------------------------------------------------------------

/-- A canonical group carrier retains exact raw strict notice and closure prefixes.
Witness: accepted batches flatten to publisher replay; legal source payloads make atomic
splitting preserve notices. Both projections use the same indexed raw carrier.
-/
theorem Witness.startup_groupNotice_rawControls {work inputs} {w : Witness}
    {index group groups streams}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : ∃ position,
        (((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2[position]?
          = some (.groupSuccess group groups streams)
        ∧ (w.events.take index).flatMap groupNoticeRefs
          = ((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
              position).flatMap
              rawGroupNoticeRefs
        ∧ (w.events.take index).flatMap groupClosureRefs
          = ((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
              position).flatMap
              rawGroupClosureRefs := by
  obtain ⟨atAtoms, exactPrefix⟩ := Witness.startup_rawBatches_canonical startup history selected
  have rawShape := ((State.initialize (Work.fromExecution work)
    startup)).rawBatches_nonemptyValues
      inputs valid.nonemptyItems
  obtain ⟨sourceIndex, sourceAt, notices, closures⟩ := publicationAtoms_groupSuccess_controls _
    (IncrementalPublisher.normalizeBatch_nonemptyValues _ _ rawShape).2 atAtoms
  obtain ⟨position, rawAt, rawNotices, rawClosures⟩ :=
    IncrementalPublisher.normalizeBatch_groupSuccess_controls _ _ sourceAt
  rw [exactPrefix] at notices closures
  exact ⟨position, rawAt, notices.trans rawNotices, closures.trans rawClosures⟩

/-- A canonical item notice retains exact raw strict notice and closure prefixes.
Witness: the selected notice is on its batch's last item atom; all earlier atoms of that
batch have no group controls. Normalization then recovers one common raw carrier index.
-/
theorem Witness.startup_itemNotice_rawControls {work inputs} {w : Witness}
    {index owner values groups streams child}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ position rawValues,
        (((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2[position]?
          = some (.streamValues owner rawValues groups streams)
        ∧ (w.events.take index).flatMap groupNoticeRefs
          = ((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
              position).flatMap
              rawGroupNoticeRefs
        ∧ (w.events.take index).flatMap groupClosureRefs
          = ((((State.initialize (Work.fromExecution work) startup)).rawBatches
                inputs).2.take
              position).flatMap
              rawGroupClosureRefs := by
  obtain ⟨atAtoms, exactPrefix⟩ := Witness.startup_rawBatches_canonical startup history selected
  have rawShape := ((State.initialize (Work.fromExecution work)
    startup)).rawBatches_nonemptyValues
      inputs valid.nonemptyItems
  obtain ⟨sourceIndex, sourceValues, sourceAt, notices, closures⟩ :=
    publicationAtoms_itemNotice_controls _
      (IncrementalPublisher.normalizeBatch_nonemptyValues _ _ rawShape).2 atAtoms noticed
  obtain ⟨position, rawValues, rawAt, rawNotices, rawClosures⟩ :=
    IncrementalPublisher.normalizeBatch_itemNotice_controls _ _ sourceAt
  rw [exactPrefix] at notices closures
  exact ⟨position, rawValues, rawAt, notices.trans rawNotices, closures.trans rawClosures⟩

/-- A group notice uses one source-handler cut for its notices and earlier completions.
Extra startup failure completions remain in the actual output prefix.
-/
theorem Witness.startup_groupNotice_sourceControls {work inputs} {w : Witness}
    {index group groups streams} (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : let initial := (State.initialize (Work.fromExecution work) startup)
      ∃ position,
        (initial.rawBatches inputs).2[position]?
          = some (.groupSuccess group groups streams)
        ∧ (w.events.take index).flatMap groupNoticeRefs
          = ((initial.rawBatches inputs).2.take position).flatMap rawGroupNoticeRefs
        ∧ (((initial.rawBatches inputs).2.take position).flatMap
            rawGroupClosureRefs).Subset
            ((w.events.take index).flatMap groupClosureRefs) := by
  obtain ⟨position, atRaw, notices, closures⟩ :=
    Witness.startup_groupNotice_rawControls startup valid started history selected
  exact ⟨position, atRaw, notices, fun _ member => closures.symm ▸ member⟩

/-- A item notice uses one source-handler cut for its notices and earlier completions.
Extra startup failure completions remain in the actual output prefix.
-/
theorem Witness.startup_itemNotice_sourceControls {work inputs} {w : Witness}
    {index owner values groups streams child} (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : let initial := (State.initialize (Work.fromExecution work) startup)
      ∃ position rawValues,
        (initial.rawBatches inputs).2[position]?
          = some (.streamValues owner rawValues groups streams)
        ∧ (w.events.take index).flatMap groupNoticeRefs
          = ((initial.rawBatches inputs).2.take position).flatMap rawGroupNoticeRefs
        ∧ (((initial.rawBatches inputs).2.take position).flatMap
            rawGroupClosureRefs).Subset
            ((w.events.take index).flatMap groupClosureRefs) := by
  obtain ⟨position, rawValues, atRaw, notices, closures⟩ :=
    Witness.startup_itemNotice_rawControls startup valid started history selected noticed
  exact ⟨position, rawValues, atRaw, notices, fun _ member => closures.symm ▸ member⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
