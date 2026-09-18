import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.ReferenceHistory
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.BatchLifecycle

/-! Every admitted work batch references only announced, not-previously-closed keys. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- Keys referenced by a payload or a completion, independently of its announcements. -/
def eventUsed : WorkEvent → Keys
  | .groupValues node _
  | .groupSuccess node _ _
  | .groupFailure node _
  | .streamValues node _ _ _
  | .streamSuccess node
  | .streamFailure node _ => [node.key]
  | .workQueueTermination => []

/-- All referenced key occurrences in the supplied outputs. -/
def usedKeys (events : List WorkEvent) : Keys := events.flatMap eventUsed

/-- A completion is a reference, by inspecting its containing event. -/
theorem completedKeys_used {events : List WorkEvent} {key : Nat}
    (h : key ∈ completedKeys events)
    : key ∈ usedKeys events := by
  obtain ⟨event, member, completed⟩ := List.mem_flatMap.mp h
  apply List.mem_flatMap.mpr
  refine ⟨event, member, ?_⟩
  cases event <;> simp_all [eventCompleted, eventUsed]

/-- Every permitted atomic reference is open before the event, by owner/closure rules. -/
theorem EventAllowed.reference {work initial matching before failed event}
    (h : EventAllowed work initial matching before failed event)
    : ∀ key ∈ eventUsed event, Open initial before key := by
  intro key member
  cases event <;> simp only [eventUsed, List.mem_singleton] at member
  case workQueueTermination => contradiction
  all_goals subst key
  case groupValues node values =>
    obtain ⟨_, _, _, _, _, _, _, _, owner⟩ := h
    exact owner.1.2.2.1
  case streamValues node values groups streams =>
    obtain ⟨_, _, _, _, _, _, _, owner, _⟩ := h
    exact owner.1.2.2.1
  all_goals exact h.2.1

/-- Pointwise event admission supplies ordered open-reference evidence, by suffix
induction over the observed history.
-/
theorem Explains.references {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    : ReferenceHistory eventPending eventCompleted eventUsed
        ((groups ++ streams).map DeliveryNode.key) [] events := by
  let initial := (groups ++ streams).map DeliveryNode.key
  have go (before rest : List WorkEvent) (equal : events = before ++ rest) :
      ReferenceHistory eventPending eventCompleted eventUsed
        (announcedKeys initial before) (completedKeys before) rest := by
    induction rest generalizing before with
    | nil => trivial
    | cons event rest ih =>
        constructor
        · have selected : events[before.length]? = some event := by simp [equal]
          have allowed := h.2.2 before.length event selected
          rw [equal] at allowed
          intro key member
          have opened := allowed.reference key member
          simp only [List.take_left] at opened
          exact ⟨List.mem_append_left _ opened.1, opened.2⟩
        · have tail := ih (before ++ [event]) (by simpa [List.append_assoc] using equal)
          simpa [announcedKeys, pendingKeys, completedKeys, List.append_assoc] using tail
  simpa [initial, announcedKeys, pendingKeys, completedKeys] using go [] events rfl

/-- Compatible value coalescing preserves reference membership, by event case analysis. -/
theorem combineValues_used {left right combined : WorkEvent}
    (h : combineValues left right = some combined)
    : ∀ key, key ∈ usedKeys [combined] ↔ key ∈ usedKeys [left, right] := by
  cases left <;> cases right <;> simp [combineValues] at h
  all_goals
    obtain ⟨keys, rfl⟩ := h
    intro key
    simp [usedKeys, eventUsed, keys]

/-- Value grouping preserves reference membership, by its separate/combine induction. -/
theorem ValueGrouping.used {events grouped : List WorkEvent}
    (h : ValueGrouping events grouped)
    : ∀ key, key ∈ usedKeys grouped ↔ key ∈ usedKeys events := by
  induction h with
  | nil => exact fun _ => Iff.rfl
  | separate head _ ih =>
      intro key
      simpa only [usedKeys, List.flatMap_cons, List.mem_append]
        using or_congr (Iff.rfl : key ∈ eventUsed head ↔ key ∈ eventUsed head) (ih key)
  | combine head _ compatible ih =>
      intro key
      have merged := combineValues_used compatible key
      simp only [usedKeys, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at merged ih ⊢
      exact (or_congr merged Iff.rfl).trans
        (or_assoc.trans (or_congr Iff.rfl (ih key)))

/-- Work batching preserves open references, by splitting atomic histories and
transporting membership through each batch's occurrence permutations.
-/
theorem WorkBatching.references {events batches} (h : WorkBatching events batches)
    {seen closed : Keys}
    (refs : ReferenceHistory eventPending eventCompleted eventUsed seen closed events)
    : ReferenceHistory pendingKeys completedKeys usedKeys seen closed batches := by
  induction h generalizing seen closed with
  | nil => trivial
  | cons _ values _ ih =>
      obtain ⟨head, tail⟩ := refs.split
      have keys := values.keyPermutation
      refine ⟨?_, (ih tail).congr ?_ ?_⟩
      · intro key member
        obtain ⟨known, fresh⟩ := head key ((values.used key).mp member)
        refine ⟨?_, fresh⟩
        rcases List.mem_append.mp known with old | new
        · exact List.mem_append_left _ old
        · exact List.mem_append_right _ (keys.pending.mem_iff.mpr new)
      · intro key; simp only [List.mem_append, keys.pending.mem_iff]; rfl
      · intro key; simp only [List.mem_append, keys.completed.mem_iff]; rfl

/-- Derived reference legality at batch boundaries, not an admission premise. -/
def History.OpenReferences (history : History) : Prop :=
  ReferenceHistory pendingKeys completedKeys usedKeys
    ((history.initialGroups ++ history.initialStreams).map DeliveryNode.key) []
    history.batches

/-- Admitted prefixes have legal references, by event admission and work batching. -/
theorem AdmissiblePrefix.openReferences {work history} (h : AdmissiblePrefix work history)
    : history.OpenReferences := by
  obtain ⟨events, matching, failures, explained, batching⟩ := h
  exact batching.references explained.references

/-- Terminal histories retain legal references; termination adds no referenced key. -/
theorem AdmissibleRun.openReferences {work history} (h : AdmissibleRun work history)
    : history.OpenReferences := by
  obtain ⟨events, matching, failures, explained, _, batching⟩ := h
  apply batching.references
  exact explained.references.append
    (tail := [.workQueueTermination]) (by simp [ReferenceHistory, eventUsed])

end GraphQL.IncrementalDelivery.WorkScheduler
