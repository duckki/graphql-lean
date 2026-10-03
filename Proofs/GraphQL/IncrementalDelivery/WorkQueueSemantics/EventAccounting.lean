import GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Notice facts derived from output-history accounting, with no queue-state witness. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- The delivery-node ref occurs in the original work. -/
def Supported (work : Work) (ref : NodeRef) : Prop :=
  ∃ node kind dependencies birth,
    NodeAt work node kind dependencies birth ∧ node.ref = ref

/-- Projecting a producer retains exactly the supported refs, by repacking witnesses. -/
theorem supported_iff_hasProducer {work ref}
    : Supported work ref ↔ ∃ birth, NodeHasProducer work ref birth := by
  constructor
  · rintro ⟨node, kind, dependencies, birth, known, same⟩
    exact ⟨birth, node, kind, dependencies, known, same⟩
  · rintro ⟨birth, node, kind, dependencies, known, same⟩
    exact ⟨node, kind, dependencies, birth, known, same⟩

/-- Owner-based accounting is the former full-task condition, by existential elimination.
-/
theorem nodeAccounted_iff_taskAt {work matching events failed ref}
    : NodeAccounted work matching events failed ref
      ↔ ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → ref ∈ owners
          → TaskAccounted work matching events failed occurrence := by
  constructor
  · intro accounted occurrence owners producer payload known member
    exact accounted occurrence owners ⟨producer, payload, known⟩ member
  · rintro accounted occurrence owners ⟨producer, payload, known⟩ member
    exact accounted occurrence owners producer payload known member

/-- Dependency satisfaction keeps its original support condition, by producer projection.
-/
theorem dependencySatisfied_iff_supported {work initial matching events failed ref}
    : DependencySatisfied work initial matching events failed ref
      ↔ ¬NodeFailed work matching events failed ref
        ∧ (¬Supported work ref
            ∨ ref ∈ completedRefs events
            ∨ ref ∉ announcedRefs initial events
              ∧ NodeAccounted work matching events failed ref) := by
  rw [DependencySatisfied, supported_iff_hasProducer]

/-- An announcement frontier is fresh and structurally supported, by eligibility and
NodeAt.
-/
theorem announcements_facts {work initial matching events failed groups streams}
    (h : Announcements work initial matching events failed groups streams)
    : ((groups ++ streams).map DeliveryNode.ref).Nodup
      ∧ (∀ ref ∈ (groups ++ streams).map DeliveryNode.ref,
          ref ∉ announcedRefs initial events)
      ∧ (∀ ref ∈ (groups ++ streams).map DeliveryNode.ref, Supported work ref) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro ref member
    obtain ⟨node, belongs, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp belongs with member | member
    · obtain ⟨dependencies, birth, _, eligible⟩ := h.2.1 node member
      exact eligible.1
    · obtain ⟨dependencies, birth, _, eligible⟩ := h.2.2 node member
      exact eligible.1
  · intro ref member
    obtain ⟨node, belongs, rfl⟩ := List.mem_map.mp member
    rcases List.mem_append.mp belongs with member | member
    · obtain ⟨dependencies, birth, known, _⟩ := h.2.1 node member
      exact ⟨node, .group, dependencies, birth, known, rfl⟩
    · obtain ⟨dependencies, birth, known, _⟩ := h.2.2 node member
      exact ⟨node, .stream, dependencies, birth, known, rfl⟩

/-- Derived fresh-notice and open-ref-closure facts for the next event after the observed
prefix.
-/
structure EventAccounting (work : Work) (initial : NodeRefs)
    (before : List WorkQueueEvent) (event : WorkQueueEvent)
    : Prop where
  pendingUnique : (eventPending event).Nodup
  fresh : ∀ ref ∈ eventPending event, ref ∉ announcedRefs initial before
  supported : ∀ ref ∈ eventPending event, Supported work ref
  completedUnique : (eventCompleted event).Nodup
  completion : ∀ ref ∈ eventCompleted event, Open initial before ref

/-- Every permitted atom has fresh notices and open-ref closures, by its event rule. -/
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
      obtain ⟨owners, producer, ⟨item, errors⟩, _, _, _, _, releases⟩ := h
      obtain ⟨unique, fresh, support⟩ := announcements_facts releases
      refine ⟨unique, ?_, support, by simp [eventCompleted], by simp [eventCompleted]⟩
      simpa [announcedRefs, pendingRefs, eventPending] using fresh
  | groupSuccess node groups streams =>
      obtain ⟨_, active, _, _, releases⟩ := h
      obtain ⟨unique, fresh, support⟩ := announcements_facts releases
      refine ⟨unique, ?_, support, by simp [eventCompleted], ?_⟩
      · simpa [announcedRefs, pendingRefs, eventPending] using fresh
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
prefix before through suffix events, using work and initial notice refs; this is
proof-only, not scheduler state.
-/
def NoticeHistory (work : Work) (initial : NodeRefs)
    : List WorkQueueEvent → List WorkQueueEvent → Prop
  | _, [] => True
  | before, event :: rest =>
      EventAccounting work initial before event
      ∧ NoticeHistory work initial (before ++ [event]) rest

/-- Pointwise history admission supplies the recursive notice witness, by suffix
induction.
-/
theorem Explains.notices {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    : NoticeHistory work ((groups ++ streams).map DeliveryNode.ref) [] events := by
  have go (before rest : List WorkQueueEvent) (equal : events = before ++ rest) :
      NoticeHistory work ((groups ++ streams).map DeliveryNode.ref) before rest := by
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

/-- Initialization yields unique supported node refs, by its structural notice frontier.
-/
theorem initializes_notices {work groups streams} (h : Initializes work groups streams)
    : ((groups ++ streams).map DeliveryNode.ref).Nodup
      ∧ ∀ ref ∈ (groups ++ streams).map DeliveryNode.ref, Supported work ref :=
  ⟨(announcements_facts h.1).1, (announcements_facts h.1).2.2⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
