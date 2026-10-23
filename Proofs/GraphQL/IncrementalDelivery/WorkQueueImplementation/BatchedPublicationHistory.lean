import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureEventAdmission

/-! Canonical publication positions and prefixes agree with actual normalized raw batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- The actual normalized raw batches differ from the witness only by optional termination. -/
theorem Witness.rawBatches_shape {work inputs} {w : Witness}
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    : let publisher : IncrementalPublisher :=
        {
          active :=
            (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
        }
      (publisher.normalizeBatch ((initialQueue work).rawBatches inputs).2).2.flatMap
        publicationAtoms
      = w.events
        ++ (if ((initialQueue work).runNormalized inputs).1.terminated then
              [.workQueueTermination]
            else
              []) := by
  dsimp only
  rw [← createWorkQueue_runNormalized_rawBatches (work := work) inputs]
  rw [State.runNormalized_terminalShape _ _ (createWorkQueue_terminated _), history]

/-- A canonical publication retains its position and strict prefix in actual raw batches. -/
theorem Witness.rawBatches_canonical {work inputs index event} {w : Witness}
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    : let publisher : IncrementalPublisher :=
        {
          active :=
            (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
        }
      let atoms :=
        (publisher.normalizeBatch ((initialQueue work).rawBatches inputs).2).2.flatMap
          publicationAtoms
      atoms[index]? = some event ∧ atoms.take index = w.events.take index := by
  dsimp only
  rw [Witness.rawBatches_shape history]
  have within := (List.getElem?_eq_some_iff.mp selected).1
  exact ⟨
    by rwa [List.getElem?_append_left within],
    List.take_append_of_le_length (Nat.le_of_lt within)
  ⟩

/-- Every bounded canonical prefix is the same prefix of normalized actual raw batches. -/
theorem Witness.rawBatches_prefix {work inputs} {w : Witness}
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (count : Nat) (within : count ≤ w.events.length)
    : ((({
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          : IncrementalPublisher).normalizeBatch
          ((initialQueue work).rawBatches inputs).2).2.flatMap
        publicationAtoms).take
        count
      = w.events.take count := by
  rw [Witness.rawBatches_shape history, List.take_append_of_le_length within]

/-- Every nonterminal raw-batch atom remains at that same canonical index and prefix. -/
theorem Witness.rawBatches_nonterminal {work inputs index event} {w : Witness}
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected
      : ((({
              active :=
                (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
            }
            : IncrementalPublisher).normalizeBatch
            ((initialQueue work).rawBatches inputs).2).2.flatMap
          publicationAtoms)[index]?
        = some event)
    (nonterminal : event ≠ .workQueueTermination)
    : w.events[index]? = some event
      ∧ ((({
              active :=
                (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
            }
            : IncrementalPublisher).normalizeBatch
            ((initialQueue work).rawBatches inputs).2).2.flatMap
          publicationAtoms).take
          index
        = w.events.take index := by
  rw [Witness.rawBatches_shape history] at selected ⊢
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
