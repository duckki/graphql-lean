import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Nonblocking
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Causality
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.PublicationExtension

/-! Omitting a notice can strand finite successful work, independently of host fairness. -/

namespace GraphQL.IncrementalDelivery.Tests.Nonblocking
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler

/-- An empty root stream and an independent nonempty root stream have distinct IDs. -/
def node (key : Nat) : DeliveryNode := { key, path := [.field (toString key)] }

/-- Only the second stream has a publication that could carry a later notice. -/
def work : Work :=
  .combine (.stream (node 0) []) (.stream (node 1) [(.ok (.null, 0), .empty)])

/-- The only successful task belongs to the omitted stream. Witness: structural lookup.
-/
theorem task_shape {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = .item [1] 0
      ∧ owners = [1]
      ∧ producer = none
      ∧ payload = .item (node 1) (.ok (.null, 0)) := by
  have locations {address current birth enclosing}
      (located : Located work address current birth enclosing)
      : (address = [] ∧ current = work ∧ birth = none)
        ∨ (address = [0] ∧ current = .stream (node 0) [] ∧ birth = none)
        ∨ (address = [1]
          ∧ current = .stream (node 1) [(.ok (.null, 0), .empty)] ∧ birth = none)
        ∨ current = .empty := by
    replace located := StructuralEquivalence.located_of_current located
    induction located with
    | root => exact Or.inl ⟨rfl, rfl, rfl⟩
    | left _ ih | right _ ih | executionGroup _ ih | item _ _ ih =>
        rcases ih with h | h | h | h <;> simp_all [work, node]
        all_goals
          rename_i index result children located entry
          cases index <;> simp_all
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      rcases locations located.toCurrent with h | h | h | h <;> simp_all [work]
  | @item address stream items birth enclosing index result children located selected =>
      rcases locations located.toCurrent with h | h | h | h <;> simp_all [work]
      cases index <;> simp_all [node]

/-- No group-completion carrier exists in this work. Witness: lookup preserves stream
and combine constructors, so no deferred location can supply a group descriptor.
-/
theorem no_group {other parents birth} : ¬NodeAt work other .group parents birth := by
  rintro ⟨address, groups, path, result, children, enclosing, group, located, _, _, _⟩
  have task : TaskAt work (.executionGroup address) (groups.map (fun g => g.node.key)) birth
      (.object path result) := ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩
  have impossible := (task_shape task).1
  cases impossible

/-- The empty stream alone is a legal nonempty initialization. Witness: its root
descriptor is eligible even though it has no items.
-/
theorem initialized : Initializes work [] [node 0] := by
  refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
  intro other member
  have same := List.mem_singleton.mp member
  subst other
  refine ⟨[], none, .stream (.left .root), ?_⟩
  exact ⟨
    by simp [announcedKeys, pendingKeys],
    fun h => h.nonempty rfl,
    Or.inl rfl,
    by simp,
    Or.inl rfl
  ⟩

/-- Snoc induction reduces prefix reasoning to a previous history and its last event.
Witness: ordinary list induction on the reversed history.
-/
private theorem snoc_induction {α : Type} {motive : List α → Prop}
    (nil : motive [])
    (snoc : ∀ before event, motive before → motive (before ++ [event]))
    (events : List α)
    : motive events := by
  have reversed (items : List α) : motive items.reverse := by
    induction items with
    | nil => exact nil
    | cons event before ih => simpa using snoc before.reverse event ih
  simpa using reversed events.reverse

/-- No matching can publish through an ID which has no initial or later notice.
Witness: snoc induction using the absence of any other notice carrier.
-/
theorem no_publications {events matching failures}
    (explained : Explains work [] [node 0] events matching failures)
    : pendingKeys events = [] ∧ ∀ occurrence, ¬Published matching events occurrence := by
  induction events using snoc_induction generalizing failures with
  | nil => simp [pendingKeys, Published]
  | snoc before event ih =>
      have previous := explained.prefix (head := before) (tail := [event])
      obtain ⟨noNotices, noValues⟩ := ih previous
      have allowed := explained.2.2 before.length event (by simp)
      have inactive : ¬Open [0] before 1 := by
        simp [Open, announcedKeys, noNotices]
      have control : eventPending event = [] ∧ ¬IsValue event := by
        cases event with
        | groupValues owner values =>
            obtain ⟨_, _, _, _, _, _, known, _⟩ := allowed
            have impossible := (task_shape known).2.2.2
            cases impossible
        | streamValues owner values groups streams =>
            obtain ⟨owners, producer, _, _, _, known, _, selected, _⟩ := allowed
            have shape := task_shape known
            have same : owner = node 1 := by
              cases shape.2.2.2
              rfl
            subst owner
            exact False.elim (inactive (by simpa [node] using selected.1.2.2.1))
        | groupSuccess owner groups streams =>
            obtain ⟨parents, birth, known⟩ := allowed.1
            exact False.elim (no_group known)
        | groupFailure owner errors =>
            obtain ⟨parents, birth, known⟩ := allowed.1
            exact False.elim (no_group known)
        | streamSuccess | streamFailure => simp [eventPending, IsValue]
        | workQueueTermination => exact False.elim allowed
      constructor
      · simp [pendingKeys, List.flatMap_append, control.1,
          show before.flatMap eventPending = [] from noNotices]
      · intro occurrence published
        rcases published_append_singleton_iff.mp published with old | next
        · exact noValues occurrence old
        · exact control.2 next.1

/-- No terminal run has this initialization, regardless of output grouping. Witness:
all tasks succeed, so no failure cuts exist; the omitted task can neither publish nor
be cancelled. An empty stream completion cannot repair the lost initial notice.
-/
theorem no_complete_run (batches : List (List WorkEvent))
    : ¬AdmissibleRun work ⟨[], [node 0], batches⟩ := by
  rintro ⟨events, matching, failures, explained, terminal, _⟩
  have empty : failures = [] := by
    cases failures with
    | nil => rfl
    | cons first rest =>
        obtain ⟨cut, occurrence⟩ := first
        obtain ⟨owners, producer, payload, known, fails, _⟩ :=
          (explained.2.1 [] cut occurrence rest rfl).2.2.1
        simp [(task_shape known).2.2.2, Payload.failure] at fails
  subst failures
  have task : TaskAt work (.item [1] 0) [1] none (.item (node 1) (.ok (.null, 0))) :=
    .item (.right .root) rfl
  rcases terminal.1 _ _ _ _ task with cancelled | published
  · exact cancelled.nonempty rfl
  · exact (no_publications explained).2 _ published

/-- The maximal source conforms but is not nonblocking. Witness: its admitted empty
history has no finished extension. Conformance alone deliberately permits this source.
-/
example
    : (specificationSource work [] [node 0]).Conforms work
      ∧ ¬(specificationSource work [] [node 0]).Nonblocking := by
  refine ⟨specificationSource_conforms initialized, ?_⟩
  intro nonblocking
  obtain ⟨suffix, run⟩ := nonblocking [] (Or.inl initialized.emptyHistory)
  exact no_complete_run suffix run

end GraphQL.IncrementalDelivery.Tests.Nonblocking
