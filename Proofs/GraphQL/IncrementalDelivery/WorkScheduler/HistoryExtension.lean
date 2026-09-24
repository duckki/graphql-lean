import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.HistoryPrefixes

/-! Constructing longer history witnesses, without choosing a public scheduler. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Extending observations while retaining their evidence
-----------------------------------------------------------------------------------------

/-- A publication remains present after appending outputs. Witness: the same lookup
index and matching, independent of the new events.
-/
theorem Published.append {matching events occurrence}
    (published : Published matching events occurrence) (tail : List WorkEvent)
    : Published matching (events ++ tail) occurrence := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  exact ⟨index, event, (List.getElem?_append_left bound).trans selected, value, same⟩

/-- Fixed failure evidence and additional outputs preserve task accounting. Witness:
cancellation is unchanged, and existing publications retain their indices.
-/
theorem Accounted.append {work matching events failed occurrence}
    (accounted : Accounted work matching events failed occurrence) (tail : List WorkEvent)
    : Accounted work matching (events ++ tail) failed occurrence :=
  accounted.imp_right (fun published => published.append tail)

/-- Accounting for a node survives output extension with unchanged failure evidence.
Witness: apply task-accounting preservation to every contributing occurrence.
-/
theorem NodeAccounted.append {work matching events failed key}
    (accounted : NodeAccounted work matching events failed key) (tail : List WorkEvent)
    : NodeAccounted work matching (events ++ tail) failed key :=
  fun occurrence owners known member =>
    (accounted occurrence owners known member).append tail

/-- Every recorded failure cut is within the observed output history. Witness: split
the ordered witness at that failure and extract its bound.
-/
theorem FailureWitness.cut_le {work initial events failures entry}
    (witness : FailureWitness work initial events failures) (member : entry ∈ failures)
    : entry.1 ≤ events.length := by
  obtain ⟨before, after, same⟩ := List.mem_iff_append.mp member
  exact (witness before entry.1 entry.2 after same).1

/-- At the last output boundary every recorded failure is visible. Witness: all cuts
are bounded by the witness's original output length.
-/
theorem FailureWitness.failedBefore_eq {work initial events failures}
    (witness : FailureWitness work initial events failures) {cut : Nat}
    (after : events.length ≤ cut)
    : failedBefore failures cut = failures.map Prod.snd := by
  unfold failedBefore
  congr 1
  apply List.filter_eq_self.mpr
  intro entry member
  simpa using Nat.le_trans (witness.cut_le member) after

/-- Appending events preserves existing failure evidence and the open-owner facts at
its original cuts. Witness: every cut still selects exactly the same output prefix.
-/
theorem FailureWitness.append {work initial events failures}
    (witness : FailureWitness work initial events failures) (tail : List WorkEvent)
    : FailureWitness work initial (events ++ tail) failures := by
  intro before cut occurrence after same
  obtain ⟨bounded, ordered, known, active⟩ := witness before cut occurrence after same
  refine ⟨by simp only [List.length_append]; omega, ordered, ?_, active⟩
  simpa only [List.take_append_of_le_length bounded] using known

/-- One permitted event extends an explained history, retaining its publication
matching and failure cuts. Witness: preserve earlier indices and check the final one.
-/
theorem Explains.append_event {work groups streams events matching failures event}
    (explained : Explains work groups streams events matching failures)
    (allowed
      : EventAllowed work ((groups ++ streams).map DeliveryNode.key) matching
          events (failedBefore failures events.length) event)
    : Explains work groups streams (events ++ [event]) matching failures := by
  refine ⟨explained.1, explained.2.1.append [event], ?_⟩
  intro index next selected
  by_cases earlier : index < events.length
  · have original : events[index]? = some next := by
      simpa only [List.getElem?_append_left earlier] using selected
    simpa only [List.take_append_of_le_length (Nat.le_of_lt earlier)]
      using explained.2.2 index next original
  · have bound := (List.getElem?_eq_some_iff.mp selected).1
    have sameIndex : index = events.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst index
    have sameEvent : next = event := by simpa using selected.symm
    subst next
    simpa using allowed

-----------------------------------------------------------------------------------------
-- Finite error counts and output batches
-----------------------------------------------------------------------------------------

/-- Actual recorded task failures always have a finite node-error count. Witness: choose
each task's fixed descriptor and sum its contribution; no positive-count premise is used.
-/
theorem NodeErrors.exists {work failed}
    (known
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload) (key : Nat)
    : ∃ errors, NodeErrors work failed key errors := by
  classical
  let contribution := fun occurrence =>
    if member : occurrence ∈ failed then
      let owners := Classical.choose (known occurrence member)
      let payload := Classical.choose
        (Classical.choose_spec (Classical.choose_spec (known occurrence member)))
      if key ∈ owners then payload.failure.getD 0 else 0
    else 0
  refine ⟨(failed.map contribution).sum, contribution, ?_, rfl⟩
  intro occurrence member
  refine ⟨Classical.choose (known occurrence member),
    Classical.choose (Classical.choose_spec (known occurrence member)),
    Classical.choose (Classical.choose_spec (Classical.choose_spec (known occurrence member))),
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (known occurrence member))), ?_⟩
  simp only [contribution, dite_eq_left member]

/-- Every recorded failure supplies a structural task descriptor. Witness: its failure
cut evidence, ignoring only reachability and the open owner.
-/
theorem FailureWitness.known {work initial events failures}
    (witness : FailureWitness work initial events failures)
    : ∀ occurrence ∈ failures.map Prod.snd,
        ∃ owners producer payload, TaskAt work occurrence owners producer payload := by
  intro occurrence member
  obtain ⟨⟨cut, occurrence⟩, inFailures, rfl⟩ := List.mem_map.mp member
  obtain ⟨before, after, same⟩ := List.mem_iff_append.mp inFailures
  obtain ⟨owners, producer, payload, known, _⟩ :=
    (witness before cut occurrence after same).2.2.1
  exact ⟨owners, producer, payload, known⟩

/-- Work batching composes at an existing batch boundary. Witness: induction on the
first batching derivation; no value coalescing is required across the boundary.
-/
theorem WorkBatching.append {before after left right}
    (first : WorkBatching before left) (last : WorkBatching after right)
    : WorkBatching (before ++ after) (left ++ right) := by
  induction first with
  | nil => exact last
  | cons nonempty values subsequent ih =>
      simpa only [List.append_assoc, List.cons_append]
        using WorkBatching.cons nonempty values ih

/-- Singleton batches can represent any supplied finite raw output list. Witness:
one separate value-grouping constructor per event, preserving exact event order.
-/
theorem WorkBatching.singletons (events : List WorkEvent)
    : WorkBatching events (events.map (fun event => [event])) := by
  induction events with
  | nil => exact .nil
  | cons event rest ih => exact .cons (by simp) (.separate event .nil) ih

end GraphQL.IncrementalDelivery.WorkScheduler
