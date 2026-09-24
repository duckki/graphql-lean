import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.EventLifecycle
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureCauses

/-! Open-owner failure cuts cannot disappear from a terminal work history. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- One structural occurrence has one owner list, producer, and payload; witness:
uniqueness of the location lookup and, for stream items, the item lookup.
-/
theorem TaskAt.unique {work occurrence owners producer payload more otherProducer other}
    (left : TaskAt work occurrence owners producer payload)
    (right : TaskAt work occurrence more otherProducer other)
    : owners = more ∧ producer = otherProducer ∧ payload = other := by
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩ := left
      obtain ⟨groups', path', result', children', enclosing', located', rfl, rfl⟩ :=
        right
      have same := Option.some.inj (located.symm.trans located')
      simp only [WorkLocation.mk.injEq, Work.executionGroup.injEq] at same
      rcases same with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  | item address index =>
      obtain ⟨node, items, enclosing, result, children, located, item, rfl, rfl⟩ :=
        left
      obtain ⟨node', items', enclosing', result', children', located', item',
        rfl, rfl⟩ :=
        right
      have same := Option.some.inj (located.symm.trans located')
      simp only [WorkLocation.mk.injEq, Work.stream.injEq] at same
      rcases same with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (item.symm.trans item'))
      exact ⟨rfl, rfl, rfl⟩

/-- Every recorded failure has an open contributing owner at its cut; witness: split
the ordered evidence at the selected member and use structural task uniqueness.
-/
theorem FailureWitness.open_owner {work initial events failures cut occurrence}
    (h : FailureWitness work initial events failures)
    (member : (cut, occurrence) ∈ failures)
    {owners producer payload} (known : TaskAt work occurrence owners producer payload)
    : ∃ key ∈ owners, Open initial (events.take cut) key := by
  obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp member
  obtain ⟨more, otherProducer, other, task, _, _, key, owner, opened⟩ :=
    (h before cut occurrence after equal).2.2.1
  obtain ⟨rfl, _, _⟩ := known.unique task
  exact ⟨key, owner, opened⟩

/-- A failure at or before the observed cut remains in that cut's causal evidence. -/
theorem mem_failedBefore {failures cut occurrence index}
    (member : (cut, occurrence) ∈ failures) (before : cut ≤ index)
    : occurrence ∈ failedBefore failures index := by
  exact List.mem_map.mpr
    ⟨(cut, occurrence), List.mem_filter.mpr ⟨member, by simpa using before⟩, rfl⟩

/-- A member of a list of natural counts is bounded by their sum, by list induction. -/
theorem le_sum {values : List Nat} {value : Nat} (h : value ∈ values)
    : value ≤ values.sum := by
  induction values with
  | nil => simp at h
  | cons head rest ih =>
      rcases List.mem_cons.mp h with rfl | member
      · simp
      · simpa using Nat.le_trans (ih member) (Nat.le_add_left rest.sum head)

/-- A node's counted errors include each recorded contributing failure; witness:
the summand for that task and uniqueness of its payload.
-/
theorem NodeErrors.contribution_le
    {work failed key errors occurrence owners producer payload}
    (h : NodeErrors work failed key errors) (member : occurrence ∈ failed)
    (known : TaskAt work occurrence owners producer payload) (owner : key ∈ owners)
    : payload.failure.getD 0 ≤ errors := by
  obtain ⟨contribution, counts, rfl⟩ := h
  obtain ⟨more, otherProducer, other, task, counted⟩ := counts occurrence member
  obtain ⟨rfl, rfl, rfl⟩ := known.unique task
  have same : contribution occurrence = payload.failure.getD 0 := by
    simpa [owner] using counted
  rw [← same]
  exact le_sum (List.mem_map.mpr ⟨occurrence, member, rfl⟩)

/-- Count failure-completion errors only; successful payload errors are separate. This
proof observation does not constrain scheduler admission.
-/
def failureErrors : WorkEvent → Nat
  | .groupFailure _ errors | .streamFailure _ errors => errors
  | _ => 0

/-- Closing an owner of a known failed task reports at least that task's errors.
Witness: successful closure contradicts failure, and failure closure counts its tasks.
-/
theorem EventAllowed.failure_completion
    {work initial matching before failed event occurrence owners producer payload key}
    (h : EventAllowed work initial matching before failed event)
    (member : occurrence ∈ failed)
    (known : TaskAt work occurrence owners producer payload) (owner : key ∈ owners)
    (closed : key ∈ eventCompleted event)
    : ∃ node errors,
        node.key = key
        ∧ (event = .groupFailure node errors ∨ event = .streamFailure node errors)
        ∧ payload.failure.getD 0 ≤ errors := by
  have failure : NodeFailed work failed key := NodeFailed.task known owner member
  cases event <;> simp only [eventCompleted, List.mem_singleton] at closed
  case groupValues | streamValues | workQueueTermination => contradiction
  case groupSuccess node groups streams =>
    subst key
    exact False.elim (h.2.2.1 failure)
  case streamSuccess node =>
    subst key
    exact False.elim (h.2.2.1 failure)
  case groupFailure node errors =>
    subst key
    exact ⟨node, errors, rfl, Or.inl rfl, h.2.2.2.contribution_le member known owner⟩
  case streamFailure node errors =>
    subst key
    exact ⟨node, errors, rfl, Or.inr rfl, h.2.2.2.contribution_le member known owner⟩

/-- Every recorded failure in a terminal history has a later completion reporting at
least its error count. Witness: its open owner must close, and cannot close successfully.
-/
theorem Explains.failure_reported {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    (done
      : Terminal work ((groups ++ streams).map DeliveryNode.key) matching events
          (failedBefore failures events.length))
    {cut occurrence owners producer payload}
    (member : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    : ∃ index node errors,
        cut ≤ index
        ∧ node.key ∈ owners
        ∧ (events[index]? = some (.groupFailure node errors)
            ∨ events[index]? = some (.streamFailure node errors))
        ∧ payload.failure.getD 0 ≤ errors := by
  obtain ⟨key, owner, opened⟩ := h.2.1.open_owner member known
  have announced
      : key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events := by
    rcases List.mem_append.mp opened.1 with initial | later
    · exact List.mem_append_left _ initial
    · obtain ⟨event, selected, contains⟩ := List.mem_flatMap.mp later
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨event, List.mem_of_mem_take selected, contains⟩)
  obtain ⟨event, selected, closes⟩ :=
    List.mem_flatMap.mp (h.allCompleted done key announced)
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp selected
  have afterCut : cut ≤ index := by
    apply Nat.le_of_not_lt
    intro beforeCut
    apply opened.2
    apply List.mem_flatMap.mpr
    exact ⟨event, List.mem_iff_getElem?.mpr ⟨index, by
      simp [beforeCut, selected]⟩, closes⟩
  obtain ⟨node, errors, same, reports, bound⟩ :=
    (h.2.2 index event selected).failure_completion (mem_failedBefore member afterCut)
      known owner closes
  refine ⟨index, node, errors, afterCut, same ▸ owner, ?_, bound⟩
  exact reports.elim (fun equal => Or.inl (equal ▸ selected))
    (fun equal => Or.inr (equal ▸ selected))

/-- Each recorded failure is bounded by all reported failure errors in a terminal
history; witness: its later completion is one summand.
-/
theorem Explains.failure_le_total {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    (done
      : Terminal work ((groups ++ streams).map DeliveryNode.key) matching events
          (failedBefore failures events.length))
    {cut occurrence owners producer payload}
    (member : (cut, occurrence) ∈ failures)
    (known : TaskAt work occurrence owners producer payload)
    : payload.failure.getD 0 ≤ (events.map failureErrors).sum := by
  obtain ⟨index, node, errors, _, _, reports, bound⟩ :=
    h.failure_reported done member known
  apply Nat.le_trans bound
  apply le_sum
  rcases reports with group | stream
  · exact List.mem_map.mpr
      ⟨.groupFailure node errors, List.mem_iff_getElem?.mpr ⟨index, group⟩, rfl⟩
  · exact List.mem_map.mpr
      ⟨.streamFailure node errors, List.mem_iff_getElem?.mpr ⟨index, stream⟩, rfl⟩

/-- Compatible value coalescing cannot remove failure counts: both input events and
the combined event are value publications, not failure completions.
-/
private theorem combineValues_failureErrors {left right combined}
    (h : combineValues left right = some combined)
    : failureErrors combined = failureErrors left + failureErrors right := by
  cases left <;> cases right <;> simp only [combineValues] at h <;> try contradiction
  all_goals split at h <;> cases h <;> rfl

/-- Value grouping preserves every failure error count, by induction on grouping. -/
theorem ValueGrouping.failureErrors_eq {events grouped} (h : ValueGrouping events grouped)
    : (grouped.map failureErrors).sum = (events.map failureErrors).sum := by
  induction h with
  | nil => rfl
  | separate head _ ih => simpa using congrArg (failureErrors head + ·) ih
  | combine head _ compatible ih =>
      simpa [combineValues_failureErrors compatible, Nat.add_assoc]
        using congrArg (failureErrors head + ·) ih

/-- Work batching preserves every failure error count, by induction on its partition
and the value-grouping equality within each batch.
-/
theorem WorkBatching.failureErrors_eq {events batches} (h : WorkBatching events batches)
    : (batches.flatten.map failureErrors).sum = (events.map failureErrors).sum := by
  induction h with
  | nil => rfl
  | cons _ values _ ih =>
      simp only [List.flatten_cons, List.map_append, List.sum_append,
        values.failureErrors_eq, ih]

/-- Every admitted terminal run has explaining witnesses whose recorded failures are
bounded by emitted errors, even after arbitrary value grouping and work batching.
Witness: extract admission and transport each failure's completion count through batching.
-/
theorem AdmissibleRun.failure_accounting {work history} (run : AdmissibleRun work history)
    : ∃ events matching failures,
        Explains work history.initialGroups history.initialStreams events matching
          failures
        ∧ Terminal work
            ((history.initialGroups ++ history.initialStreams).map DeliveryNode.key)
            matching events (failedBefore failures events.length)
        ∧ WorkBatching (events ++ [.workQueueTermination]) history.batches
        ∧ ∀ cut occurrence owners producer payload,
            (cut, occurrence) ∈ failures
            → TaskAt work occurrence owners producer payload
            → payload.failure.getD 0
              ≤ (history.batches.flatten.map failureErrors).sum := by
  obtain ⟨events, matching, failures, explained, done, batching⟩ := run
  refine ⟨events, matching, failures, explained, done, batching, ?_⟩
  intro cut occurrence owners producer payload member known
  rw [batching.failureErrors_eq]
  simpa [failureErrors] using explained.failure_le_total done member known

/-- A published occurrence has a successful payload, by its event's provenance and
the uniqueness of the task descriptor.
-/
theorem Explains.published_succeeds {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (published : Published matching events occurrence)
    : payload.failure = none := by
  obtain ⟨index, event, selected, isValue, same⟩ := published
  have length : (events.take index).length = index := by
    have bound := (List.getElem?_eq_some_iff.mp selected).choose
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have allowed := h.2.2 index event selected
  cases event <;> try contradiction
  case groupValues node values =>
    obtain ⟨_, _, _, _, _, _, task, _⟩ := allowed
    rw [length, same] at task
    rw [(known.unique task).2.2]
    rfl
  case streamValues node values groups streams =>
    obtain ⟨_, _, _, _, _, task, _⟩ := allowed
    rw [length, same] at task
    rw [(known.unique task).2.2]
    rfl

/-- Zero reported failure errors imply every work task succeeds, provided actual failure
outcomes carry positive counts. Witness: failure accounting eliminates the failure cuts;
terminal accounting then forces publication, whose payload is successful. Positivity is
explicit because arbitrary raw Work can contain an artificial error with count zero.
-/
theorem AdmissibleRun.tasks_succeed_of_no_failure_errors {work history}
    (run : AdmissibleRun work history)
    (positive
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → payload.failure.isSome = true
          → 0 < payload.failure.getD 0)
    (zero : (history.batches.flatten.map failureErrors).sum = 0)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : payload.failure = none := by
  obtain ⟨events, matching, failures, explained, done, _, counts⟩ :=
    run.failure_accounting
  have empty : failures = [] := by
    cases failures with
    | nil => rfl
    | cons entry rest =>
        rcases entry with ⟨cut, task⟩
        obtain ⟨more, otherProducer, other, located, fails, _⟩ :=
          (explained.2.1 [] cut task rest rfl).2.2.1
        have nonzero := positive task more otherProducer other located fails
        have bound := counts cut task more otherProducer other (by simp) located
        omega
  subst failures
  rcases done.1 occurrence owners producer payload known with cancelled | published
  · exact False.elim (cancelled.nonempty rfl)
  · exact explained.published_succeeds known published

end GraphQL.IncrementalDelivery.WorkScheduler
