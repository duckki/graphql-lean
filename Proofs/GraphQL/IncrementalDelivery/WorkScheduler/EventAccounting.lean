import GraphQL.IncrementalDelivery.WorkScheduler

/-! Notice facts derived from output-history accounting, with no queue-state witness. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- The delivery-node key occurs in the original work. -/
def Supported (work : Work) (key : Nat) : Prop :=
  ∃ node kind dependencies birth,
    NodeAt work node kind dependencies birth ∧ node.key = key

/-- Projecting a producer retains exactly the supported keys, by repacking witnesses. -/
theorem supported_iff_hasProducer {work key}
    : Supported work key ↔ ∃ birth, NodeHasProducer work key birth := by
  constructor
  · rintro ⟨node, kind, dependencies, birth, known, same⟩
    exact ⟨birth, node, kind, dependencies, known, same⟩
  · rintro ⟨birth, node, kind, dependencies, known, same⟩
    exact ⟨node, kind, dependencies, birth, known, same⟩

/-- Owner-based accounting is the former full-task condition, by existential elimination.
-/
theorem nodeAccounted_iff_taskAt {work matching events failed key}
    : NodeAccounted work matching events failed key
      ↔ ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → key ∈ owners
          → Accounted work matching events failed occurrence := by
  constructor
  · intro accounted occurrence owners producer payload known member
    exact accounted occurrence owners ⟨producer, payload, known⟩ member
  · rintro accounted occurrence owners ⟨producer, payload, known⟩ member
    exact accounted occurrence owners producer payload known member

/-- Dependency satisfaction keeps its original support condition, by producer projection.
-/
theorem dependencySatisfied_iff_supported {work initial matching events failed key}
    : DependencySatisfied work initial matching events failed key
      ↔ ¬NodeFailed work failed key
        ∧ (¬Supported work key
            ∨ key ∈ completedKeys events
            ∨ key ∉ announcedKeys initial events
              ∧ NodeAccounted work matching events failed key) := by
  rw [DependencySatisfied, supported_iff_hasProducer]

/-- An announcement frontier is fresh and structurally supported, by eligibility and
NodeAt.
-/
theorem announcements_facts {work initial matching events failed groups streams}
    (h : Announcements work initial matching events failed groups streams)
    : ((groups ++ streams).map DeliveryNode.key).Nodup
      ∧ (∀ key ∈ (groups ++ streams).map DeliveryNode.key,
          key ∉ announcedKeys initial events)
      ∧ (∀ key ∈ (groups ++ streams).map DeliveryNode.key, Supported work key) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro key member
    obtain ⟨node, belongs, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp belongs with member | member
    · obtain ⟨dependencies, birth, _, eligible⟩ := h.2.1 node member
      exact eligible.1
    · obtain ⟨dependencies, birth, _, eligible⟩ := h.2.2 node member
      exact eligible.1
  · intro key member
    obtain ⟨node, belongs, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp belongs with member | member
    · obtain ⟨dependencies, birth, known, _⟩ := h.2.1 node member
      exact ⟨node, .group, dependencies, birth, known, rfl⟩
    · obtain ⟨dependencies, birth, known, _⟩ := h.2.2 node member
      exact ⟨node, .stream, dependencies, birth, known, rfl⟩

/-- Derived fresh-notice and open-key-closure facts for the next event after the observed
prefix.
-/
structure EventAccounting (work : Work) (initial : Keys)
    (before : List WorkEvent) (event : WorkEvent)
    : Prop where
  pendingUnique : (eventPending event).Nodup
  fresh : ∀ key ∈ eventPending event, key ∉ announcedKeys initial before
  supported : ∀ key ∈ eventPending event, Supported work key
  completedUnique : (eventCompleted event).Nodup
  completion : ∀ key ∈ eventCompleted event, Open initial before key

/-- Every permitted atom has fresh notices and open-key closures, by its event rule. -/
theorem EventAllowed.accounting {work initial matching before failed event}
    (h : EventAllowed work initial matching before failed event)
    : EventAccounting work initial before event := by
  cases event with
  | groupValues =>
      exact ⟨
        by simp [eventPending],
        by simp [eventPending],
        by simp [eventPending],
        by simp [eventCompleted],
        by simp [eventCompleted]
      ⟩
  | streamValues node values groups streams =>
      obtain ⟨owners, producer, item, errors, _, _, _, _, releases⟩ := h
      obtain ⟨unique, fresh, support⟩ := announcements_facts releases
      refine ⟨unique, ?_, support, by simp [eventCompleted], by simp [eventCompleted]⟩
      simpa [announcedKeys, pendingKeys, eventPending] using fresh
  | groupSuccess node groups streams =>
      obtain ⟨_, active, _, _, releases⟩ := h
      obtain ⟨unique, fresh, support⟩ := announcements_facts releases
      refine ⟨unique, ?_, support, by simp [eventCompleted], ?_⟩
      · simpa [announcedKeys, pendingKeys, eventPending] using fresh
      · simpa [eventCompleted] using active
  | streamSuccess node | groupFailure node _ | streamFailure node _ =>
      exact ⟨
        by simp [eventPending],
        by simp [eventPending],
        by simp [eventPending],
        by simp [eventCompleted],
        by simpa [eventCompleted] using h.2.1
      ⟩
  | workQueueTermination => exact False.elim h

/-- (NoticeHistory work initial before events) extends notice accounting from output
prefix before through suffix events, using work and initial notice keys; this is
proof-only, not scheduler state.
-/
def NoticeHistory (work : Work) (initial : Keys) : List WorkEvent → List WorkEvent → Prop
  | _, [] => True
  | before, event :: rest =>
      EventAccounting work initial before event
      ∧ NoticeHistory work initial (before ++ [event]) rest

/-- Pointwise history admission supplies the recursive notice witness, by suffix
induction.
-/
theorem Explains.notices {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    : NoticeHistory work ((groups ++ streams).map DeliveryNode.key) [] events := by
  have go (before rest : List WorkEvent) (equal : events = before ++ rest) :
      NoticeHistory work ((groups ++ streams).map DeliveryNode.key) before rest := by
    induction rest generalizing before with
    | nil => trivial
    | cons event rest ih =>
        constructor
        · have selected : events[before.length]? = some event := by simp [equal]
          have allowed := h.2.2 before.length event selected
          rw [equal] at allowed
          simpa using allowed.accounting
        · apply ih (before ++ [event])
          simpa [List.append_assoc] using equal
  exact go [] events rfl

/-- Initialization yields unique supported node keys, by its structural notice frontier.
-/
theorem initializes_notices {work groups streams} (h : Initializes work groups streams)
    : ((groups ++ streams).map DeliveryNode.key).Nodup
      ∧ ∀ key ∈ (groups ++ streams).map DeliveryNode.key, Supported work key :=
  ⟨(announcements_facts h.1).1, (announcements_facts h.1).2.2⟩

end GraphQL.IncrementalDelivery.WorkScheduler
