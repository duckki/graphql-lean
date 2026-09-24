import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureReporting

/-! Task publication is one-shot independently of owner choice and metadata equality. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- A value event's matched occurrence is fresh relative to its observed prefix;
witness: extract CanPublish from the corresponding value rule.
-/
theorem EventAllowed.freshPublication {work initial matching before failed event}
    (allowed : EventAllowed work initial matching before failed event)
    (value : IsValue event)
    : ¬Published matching before (matching before.length) := by
  cases event <;> try contradiction
  case groupValues node values =>
    obtain ⟨_, _, _, _, _, _, _, ready, _⟩ := allowed
    exact ready.1
  case streamValues node values groups streams =>
    obtain ⟨_, _, _, _, _, _, ready, _⟩ := allowed
    exact ready.1

/-- Every value atom comes from an actual successful task; witness: its event rule.
-/
theorem EventAllowed.publicationTask {work initial matching before failed event}
    (allowed : EventAllowed work initial matching before failed event)
    (value : IsValue event)
    : ∃ owners producer payload,
        TaskAt work (matching before.length) owners producer payload
        ∧ payload.failure = none := by
  cases event <;> try contradiction
  case groupValues node values =>
    obtain ⟨owners, producer, path, data, errors, _, known, _⟩ := allowed
    exact ⟨owners, producer, _, known, rfl⟩
  case streamValues node values groups streams =>
    obtain ⟨owners, producer, item, errors, _, known, _⟩ := allowed
    exact ⟨owners, producer, _, known, rfl⟩

/-- Distinct value atoms never match the same task occurrence. Witness: the earlier
publication would contradict freshness at the later output position.
-/
theorem Explains.publication_unique {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {left right first second}
    (firstAt : events[left]? = some first) (firstValue : IsValue first)
    (secondAt : events[right]? = some second) (secondValue : IsValue second)
    (same : matching left = matching right)
    : left = right := by
  have earlier {i j a b} (atI : events[i]? = some a) (valueI : IsValue a)
      (atJ : events[j]? = some b) (valueJ : IsValue b)
      (equal : matching i = matching j) (less : i < j) : False := by
    have bound := (List.getElem?_eq_some_iff.mp atJ).choose
    have length : (events.take j).length = j := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
    have fresh := (explained.2.2 j b atJ).freshPublication valueJ
    rw [length] at fresh
    apply fresh
    exact ⟨i, a, (List.getElem?_take_of_lt less).trans atI, valueI, equal⟩
  by_cases less : left < right
  · exact False.elim (earlier firstAt firstValue secondAt secondValue same less)
  · by_cases greater : right < left
    · exact False.elim (earlier secondAt secondValue firstAt firstValue same.symm greater)
    · omega

/-- Every matched publication has a uniquely located value atom; witness: uniqueness
of publication indices, without requiring different payload values or different owners.
-/
theorem Explains.published_once {work groups streams events matching failures occurrence}
    (explained : Explains work groups streams events matching failures)
    (published : Published matching events occurrence)
    : ∃ index,
        (∃ event,
          events[index]? = some event ∧ IsValue event ∧ matching index = occurrence)
        ∧ ∀ other event,
            events[other]? = some event
            → IsValue event
            → matching other = occurrence
            → other = index := by
  obtain ⟨index, event, selected, value, same⟩ := published
  exact ⟨index, ⟨event, selected, value, same⟩, fun other next atOther isValue equal =>
    explained.publication_unique atOther isValue selected value (equal.trans same.symm)⟩

/-- Publications cannot invent tasks; witness: the event rule at their output index. -/
theorem Explains.published_task {work groups streams events matching failures occurrence}
    (explained : Explains work groups streams events matching failures)
    (published : Published matching events occurrence)
    : ∃ owners producer payload,
        TaskAt work occurrence owners producer payload ∧ payload.failure = none := by
  obtain ⟨index, event, selected, value, same⟩ := published
  have bound := (List.getElem?_eq_some_iff.mp selected).choose
  have task := (explained.2.2 index event selected).publicationTask value
  simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound), same] using task

end GraphQL.IncrementalDelivery.WorkScheduler
