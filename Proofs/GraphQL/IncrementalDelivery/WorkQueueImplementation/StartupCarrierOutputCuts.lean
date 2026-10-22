import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProjectedOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches

/-! Startup carrier positions preserve the exact actual raw object-prefix ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A startup normalized atomic group carrier is interpreted by the same raw object-prefix
ledger as its actual source handlers. Its wire-owner mapping remains the actual publisher's.
-/
theorem State.startup_runNormalized_groupSuccess_rawPrefix {work : Execution.Work}
    (startup : InitialStartup) {inputs : List (List GraphEvent)}
    {index group groups streams}
    (selected
      : let initial := State.initialize (Work.fromExecution work) startup
        ((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms)[index]?
        = some (.groupSuccess group groups streams))
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ position,
        (initial.rawBatches inputs).2[position]?
          = some (.groupSuccess group groups streams)
        ∧ ((((initial.runNormalized inputs).2.flatten.flatMap publicationAtoms).take
              index).flatMap
            normalizedObjectValues).length
          = (((initial.rawBatches inputs).2.take position).flatMap
              WorkQueueEvent.objectValues).length := by
  dsimp only at selected ⊢
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  rw [initial.runNormalized_rawBatches inputs] at selected ⊢
  obtain ⟨normalizedIndex, atNormalized, atomCount⟩ :=
    publicationAtoms_groupSuccess_prefix _ selected
  obtain ⟨position, atRaw, rawCount⟩ := publisher.normalizeBatch_groupSuccess _ atNormalized
  exact ⟨position, atRaw, atomCount.trans rawCount⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
