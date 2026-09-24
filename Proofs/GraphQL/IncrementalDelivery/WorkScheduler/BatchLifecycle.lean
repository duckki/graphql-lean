import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.EventLifecycle

/-! Notice identity and causal completion survive all relational work batching choices.
Value grouping can reorder announcements inside a batch, so occurrences use permutation.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler

open GraphQL.IncrementalDelivery.Execution

/-- The two event lists have the same announcement and completion occurrences, up to order
but preserving multiplicity.
-/
structure KeyPermutation (left right : List WorkEvent) : Prop where
  pending : (pendingKeys left).Perm (pendingKeys right)
  completed : (completedKeys left).Perm (completedKeys right)

/-- An unchanged event list preserves its key occurrences, by reflexive permutations. -/
theorem KeyPermutation.refl (events : List WorkEvent) : KeyPermutation events events :=
  ⟨.rfl, .rfl⟩

/-- Key preservation composes, by transitivity of both occurrence permutations. -/
theorem KeyPermutation.trans {left middle right : List WorkEvent}
    (hl : KeyPermutation left middle) (hr : KeyPermutation middle right)
    : KeyPermutation left right :=
  ⟨hl.pending.trans hr.pending, hl.completed.trans hr.completed⟩

/-- Concatenating separately preserved event lists preserves all occurrences, by flatMap
and append.
-/
theorem KeyPermutation.append {left right more next : List WorkEvent}
    (hl : KeyPermutation left right) (hr : KeyPermutation more next)
    : KeyPermutation (left ++ more) (right ++ next) := by
  exact ⟨
    by simpa only [pendingKeys, List.flatMap_append] using hl.pending.append hr.pending,
    by
      simpa only [completedKeys, List.flatMap_append]
        using hl.completed.append hr.completed
  ⟩

/-- A compatible value merge preserves notice occurrences; stream notices may swap middle
blocks. Witness: event case analysis followed by append-permutation for the stream case.
-/
theorem combineValues_keyPermutation {left right combined : WorkEvent}
    (h : combineValues left right = some combined)
    : KeyPermutation [combined] [left, right] := by
  cases left <;> cases right <;> simp [combineValues] at h
  all_goals
    obtain ⟨_, rfl⟩ := h
    constructor <;>
      simp only [pendingKeys, completedKeys, eventPending, eventCompleted,
        List.flatMap_cons, List.flatMap_nil, List.map_append, List.append_nil]
  all_goals first | exact .rfl |
    simpa only [List.append_assoc] using
      (List.Perm.append_left _ ((List.perm_append_comm).append_right _))

/-- Every value-grouping witness preserves occurrences, by induction over separate/combine
choices.
-/
theorem ValueGrouping.keyPermutation {events grouped : List WorkEvent}
    (h : ValueGrouping events grouped)
    : KeyPermutation grouped events := by
  induction h with
  | nil => exact .refl []
  | separate head _ ih => exact (KeyPermutation.refl [head]).append ih
  | @combine head tail first rest merged _ compatible ih =>
      exact ((combineValues_keyPermutation compatible).append (.refl rest)).trans
        ((KeyPermutation.refl [head]).append ih)

/-- Every work-batching witness preserves occurrences across its flattened groups, by
batch induction.
-/
theorem WorkBatching.keyPermutation {events : List WorkEvent}
    {batches : List (List WorkEvent)} (h : WorkBatching events batches)
    : KeyPermutation batches.flatten events := by
  induction h with
  | nil => exact .refl []
  | cons _ values _ ih => exact values.keyPermutation.append ih

/-- (liveBatches batches) requires each notice in the supplied output batches to complete
in its own batch or a later one.
-/
def liveBatches : List (List WorkEvent) → Prop
  | [] => True
  | batch :: rest =>
      (∀ key ∈ pendingKeys batch, key ∈ completedKeys (batch ++ rest.flatten))
      ∧ liveBatches rest

/-- A live event history splits into prefix closure and a live suffix, by prefix
induction.
-/
theorem liveEvents_split {head tail : List WorkEvent} (h : liveEvents (head ++ tail))
    : (∀ key ∈ pendingKeys head, key ∈ completedKeys (head ++ tail))
      ∧ liveEvents tail := by
  induction head with
  | nil => exact ⟨by simp [pendingKeys], h⟩
  | cons event rest ih =>
      obtain ⟨hp, ht⟩ := h
      obtain ⟨hr, hf⟩ := ih ht
      refine ⟨?_, hf⟩
      intro key hk
      rcases List.mem_append.mp hk with hk | hk
      · exact hp key hk
      · exact List.mem_append_right _ (hr key hk)

/-- Work batching preserves causal closure, by splitting the raw history and transporting
occurrences.
-/
theorem WorkBatching.live {events : List WorkEvent} {batches : List (List WorkEvent)}
    (h : WorkBatching events batches) (live : liveEvents events)
    : liveBatches batches := by
  induction h with
  | nil => trivial
  | cons _ values tail ih =>
      obtain ⟨headLive, tailLive⟩ := liveEvents_split live
      refine ⟨?_, ih tailLive⟩
      intro key hk
      exact (values.keyPermutation.append tail.keyPermutation).completed.mem_iff.mpr
        (headLive key (values.keyPermutation.pending.mem_iff.mp hk))

/-- Joining two causally live histories retains liveness, by embedding prefix completions
in the append.
-/
theorem liveEvents_append_of_live {head tail : List WorkEvent}
    (hl : liveEvents head) (hr : liveEvents tail)
    : liveEvents (head ++ tail) := by
  induction head with
  | nil => exact hr
  | cons event rest ih =>
      refine ⟨?_, ih hl.2⟩
      intro key hk
      obtain ⟨later, hm, hc⟩ := List.mem_flatMap.mp (hl.1 key hk)
      exact List.mem_flatMap.mpr ⟨later, List.mem_append_left _ hm, hc⟩

/-- Announcements across initial notices and batches are unique, as are completions across
batches.
-/
def History.UniqueKeys (history : History) : Prop :=
  ((history.initialGroups ++ history.initialStreams).map DeliveryNode.key
    ++ pendingKeys history.batches.flatten).Nodup
  ∧ (completedKeys history.batches.flatten).Nodup

/-- Every admitted prefix has one-shot announcements and completions, using initialization
and batching.
-/
theorem AdmissiblePrefix.uniqueKeys {work : Work} {history : History}
    (h : AdmissiblePrefix work history)
    : history.UniqueKeys := by
  obtain ⟨events, matching, failures, explained, batching⟩ := h
  have keys := batching.keyPermutation
  constructor
  · apply (keys.pending.append_left _).nodup_iff.mpr
    exact explained.noticeFacts.announcedUnique
  · exact keys.completed.nodup_iff.mpr explained.noticeFacts.completedUnique

/-- Complete runs retain one-shot keys; their extra termination event contributes no
notice keys.
-/
theorem AdmissibleRun.uniqueKeys {work : Work} {history : History}
    (h : AdmissibleRun work history)
    : history.UniqueKeys := by
  obtain ⟨events, matching, failures, explained, _, batching⟩ := h
  have keys := batching.keyPermutation
  constructor
  · apply (keys.pending.append_left _).nodup_iff.mpr
    simp only [pendingKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      eventPending, List.append_nil]
    exact explained.noticeFacts.announcedUnique
  · apply keys.completed.nodup_iff.mpr
    simpa [completedKeys, eventCompleted] using explained.noticeFacts.completedUnique

/-- Every initially or later announced node completes causally in a terminal history.
Witness: terminal history liveness plus occurrence-preserving work batching; no fairness
is asserted.
-/
theorem AdmissibleRun.liveKeys {work : Work} {history : History}
    (h : AdmissibleRun work history)
    : (∀ key ∈ (history.initialGroups ++ history.initialStreams).map DeliveryNode.key,
        key ∈ completedKeys history.batches.flatten)
      ∧ liveBatches history.batches := by
  obtain ⟨events, matching, failures, explained, done, batching⟩ := h
  refine ⟨?_, batching.live (liveEvents_append_of_live (explained.liveEvents done) ?_)⟩
  · intro key hk
    have completes := explained.allCompleted done key (List.mem_append_left _ hk)
    apply batching.keyPermutation.completed.mem_iff.mpr
    obtain ⟨event, member, completed⟩ := List.mem_flatMap.mp completes
    exact List.mem_flatMap.mpr ⟨event, List.mem_append_left _ member, completed⟩
  · simp [liveEvents, eventPending]

/-- Causal batch liveness implies total completion membership, by induction over batches.
-/
theorem liveBatches_pendingKeys {batches : List (List WorkEvent)}
    (h : liveBatches batches) {key : Nat} (member : key ∈ pendingKeys batches.flatten)
    : key ∈ completedKeys batches.flatten := by
  induction batches with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      simp only [List.flatten_cons, pendingKeys, List.flatMap_append] at member
      rcases List.mem_append.mp member with first | later
      · exact h.1 key first
      · simpa only [List.flatten_cons, completedKeys, List.flatMap_append]
          using List.mem_append_right (completedKeys head) (ih h.2 later)

/-- Every announced node key completes exactly once in a terminal history: liveness plus
Nodup counts.
-/
theorem AdmissibleRun.keysCompleteExactlyOnce {work : Work} {history : History}
    (h : AdmissibleRun work history)
    : ∀ key ∈
        (history.initialGroups ++ history.initialStreams).map DeliveryNode.key
        ++ pendingKeys history.batches.flatten,
        (completedKeys history.batches.flatten).count key = 1 := by
  intro key member
  have completed : key ∈ completedKeys history.batches.flatten := by
    rcases List.mem_append.mp member with initial | later
    · exact h.liveKeys.1 key initial
    · exact liveBatches_pendingKeys h.liveKeys.2 later
  simp [h.uniqueKeys.2.count, completed]

end GraphQL.IncrementalDelivery.WorkScheduler
