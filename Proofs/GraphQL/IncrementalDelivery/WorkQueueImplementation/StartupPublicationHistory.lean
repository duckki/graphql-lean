import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRawBatches
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAdmission

/-! Startup publication positions agree with the actual raw output and publisher. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- Actual normalized startup raw output differs from the shared witness only by final
termination. The retained raw diagnostic controls stay in their executable positions.
-/
theorem Witness.startup_rawBatches_shape {work inputs} {w : Witness}
    (startup : InitialStartup)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    : let publisher : IncrementalPublisher :=
        {
          active :=
            ((State.initialize (Work.fromExecution work) startup)).initialGroups
            ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
        }
      (publisher.normalizeBatch
        (((State.initialize (Work.fromExecution work) startup)).rawBatches
          inputs).2).2.flatMap
        publicationAtoms
      = w.events
        ++ (if (((State.initialize (Work.fromExecution work) startup)).runNormalized
                  inputs).1.terminated then
              [.workQueueTermination]
            else
              []) := by
  dsimp only
  rw [← State.runNormalized_rawBatches
    (State.initialize (Work.fromExecution work) startup) inputs]
  rw [State.runNormalized_terminalShape _ _ (State.initializeWithStartup_terminated _ startup), history]

/-- A canonical publication retains its position and strict prefix in actual raw batches. -/
theorem Witness.startup_rawBatches_canonical {work inputs index event} {w : Witness}
    (startup : InitialStartup)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    : let publisher : IncrementalPublisher :=
        {
          active :=
            ((State.initialize (Work.fromExecution work) startup)).initialGroups
            ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
        }
      let atoms :=
        (publisher.normalizeBatch
          (((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2).2.flatMap
          publicationAtoms
      atoms[index]? = some event ∧ atoms.take index = w.events.take index := by
  dsimp only
  rw [Witness.startup_rawBatches_shape startup history]
  have within := (List.getElem?_eq_some_iff.mp selected).1
  exact ⟨
    by rwa [List.getElem?_append_left within],
    List.take_append_of_le_length (Nat.le_of_lt within)
  ⟩

/-- Every bounded canonical prefix is the same prefix of normalized actual raw batches. -/
theorem Witness.startup_rawBatches_prefix {work inputs} {w : Witness}
    (startup : InitialStartup)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (count : Nat) (within : count ≤ w.events.length)
    : ((({
            active :=
              ((State.initialize (Work.fromExecution work) startup)).initialGroups
              ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
          }
          : IncrementalPublisher).normalizeBatch
          (((State.initialize (Work.fromExecution work) startup)).rawBatches
            inputs).2).2.flatMap
        publicationAtoms).take
        count
      = w.events.take count := by
  rw [Witness.startup_rawBatches_shape startup history, List.take_append_of_le_length within]

/-- Every nonterminal raw-batch atom remains at that same canonical index and prefix. -/
theorem Witness.startup_rawBatches_nonterminal {work inputs index event} {w : Witness}
    (startup : InitialStartup)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    (selected
      : ((({
              active :=
                ((State.initialize (Work.fromExecution work) startup)).initialGroups
                ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
            }
            : IncrementalPublisher).normalizeBatch
            (((State.initialize (Work.fromExecution work) startup)).rawBatches
              inputs).2).2.flatMap
          publicationAtoms)[index]?
        = some event)
    (nonterminal : event ≠ .workQueueTermination)
    : w.events[index]? = some event
      ∧ ((({
              active :=
                ((State.initialize (Work.fromExecution work) startup)).initialGroups
                ++ ((State.initialize (Work.fromExecution work) startup)).initialStreams
            }
            : IncrementalPublisher).normalizeBatch
            (((State.initialize (Work.fromExecution work) startup)).rawBatches
              inputs).2).2.flatMap
          publicationAtoms).take
          index
        = w.events.take index := by
  rw [Witness.startup_rawBatches_shape startup history] at selected ⊢
  have within : index < w.events.length := by
    by_cases within : index < w.events.length
    · exact within
    rw [List.getElem?_append_right (Nat.le_of_not_gt within)] at selected
    have member := List.mem_of_getElem? selected
    split at member
    · exact False.elim (nonterminal (List.mem_singleton.mp member))
    · cases member
  exact ⟨
    by rwa [List.getElem?_append_left within] at selected,
    List.take_append_of_le_length (Nat.le_of_lt within)
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
