import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.EventLifecycle

/-! Notice identity and causal completion survive all relational work batching choices.
Value grouping can reorder announcements inside a batch, so occurrences use permutation.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics

open GraphQL.IncrementalDelivery.Execution

/-- The two event lists have the same announcement and completion occurrences, up to order
but preserving multiplicity.
-/
structure RefPermutation (left right : List WorkQueueEvent) : Prop where
  pending : (pendingRefs left).Perm (pendingRefs right)
  completed : (completedRefs left).Perm (completedRefs right)

/-- An unchanged event list preserves its ref occurrences, by reflexive permutations. -/
theorem RefPermutation.refl (events : List WorkQueueEvent)
    : RefPermutation events events :=
  ⟨.rfl, .rfl⟩

/-- Ref preservation composes, by transitivity of both occurrence permutations. -/
theorem RefPermutation.trans {left middle right : List WorkQueueEvent}
    (hl : RefPermutation left middle) (hr : RefPermutation middle right)
    : RefPermutation left right :=
  ⟨hl.pending.trans hr.pending, hl.completed.trans hr.completed⟩

/-- Concatenating separately preserved event lists preserves all occurrences, by flatMap
and append.
-/
theorem RefPermutation.append {left right more next : List WorkQueueEvent}
    (hl : RefPermutation left right) (hr : RefPermutation more next)
    : RefPermutation (left ++ more) (right ++ next) := by
  exact ⟨
    by simpa only [pendingRefs, List.flatMap_append] using hl.pending.append hr.pending,
    by
      simpa only [completedRefs, List.flatMap_append]
        using hl.completed.append hr.completed
  ⟩

/-- A compatible value merge preserves notice occurrences; stream notices may swap middle
blocks. Witness: event case analysis followed by append-permutation for the stream case.
-/
theorem combineValues_refPermutation {left right combined : WorkQueueEvent}
    (h : combineValues left right = some combined)
    : RefPermutation [combined] [left, right] := by
  cases left <;> cases right <;> simp [combineValues] at h
  all_goals
    obtain ⟨_, rfl⟩ := h
    constructor <;>
      simp only [pendingRefs, completedRefs, eventPending, eventCompleted,
        List.flatMap_cons, List.flatMap_nil, List.map_append, List.append_nil]
  all_goals first | exact .rfl |
    simpa only [List.append_assoc] using
      (List.Perm.append_left _ ((List.perm_append_comm).append_right _))

/-- Every value-grouping witness preserves occurrences, by induction over separate/combine
choices.
-/
theorem ValueGrouping.refPermutation {events grouped : List WorkQueueEvent}
    (h : ValueGrouping events grouped)
    : RefPermutation grouped events := by
  induction h with
  | nil => exact .refl []
  | separate head _ ih => exact (RefPermutation.refl [head]).append ih
  | @combine head tail first rest merged _ compatible ih =>
      exact ((combineValues_refPermutation compatible).append (.refl rest)).trans
        ((RefPermutation.refl [head]).append ih)

/-- Every work-batching witness preserves occurrences across its flattened groups, by
batch induction.
-/
theorem WorkBatching.refPermutation {events : List WorkQueueEvent}
    {batches : List (List WorkQueueEvent)} (h : WorkBatching events batches)
    : RefPermutation batches.flatten events := by
  induction h with
  | nil => exact .refl []
  | cons _ values _ ih => exact values.refPermutation.append ih

/-- (liveBatches batches) requires each notice in the supplied output batches to complete
in its own batch or a later one.
-/
def liveBatches : List (List WorkQueueEvent) → Prop
  | [] => True
  | batch :: rest =>
      (∀ ref ∈ pendingRefs batch, ref ∈ completedRefs (batch ++ rest.flatten))
      ∧ liveBatches rest

/-- A live event history splits into prefix closure and a live suffix, by prefix
induction.
-/
theorem liveEvents_split {head tail : List WorkQueueEvent} (h : liveEvents (head ++ tail))
    : (∀ ref ∈ pendingRefs head, ref ∈ completedRefs (head ++ tail))
      ∧ liveEvents tail := by
  induction head with
  | nil => exact ⟨by simp [pendingRefs], h⟩
  | cons event rest ih =>
      obtain ⟨hp, ht⟩ := h
      obtain ⟨hr, hf⟩ := ih ht
      refine ⟨?_, hf⟩
      intro ref hk
      rcases List.mem_append.mp hk with hk | hk
      · exact hp ref hk
      · exact List.mem_append_right _ (hr ref hk)

/-- Work batching preserves causal closure, by splitting the raw history and transporting
occurrences.
-/
theorem WorkBatching.live {events : List WorkQueueEvent}
    {batches : List (List WorkQueueEvent)} (h : WorkBatching events batches)
    (live : liveEvents events)
    : liveBatches batches := by
  induction h with
  | nil => trivial
  | cons _ values tail ih =>
      obtain ⟨headLive, tailLive⟩ := liveEvents_split live
      refine ⟨?_, ih tailLive⟩
      intro ref hk
      exact (values.refPermutation.append tail.refPermutation).completed.mem_iff.mpr
        (headLive ref (values.refPermutation.pending.mem_iff.mp hk))

/-- Joining two causally live histories retains liveness, by embedding prefix completions
in the append.
-/
theorem liveEvents_append_of_live {head tail : List WorkQueueEvent}
    (hl : liveEvents head) (hr : liveEvents tail)
    : liveEvents (head ++ tail) := by
  induction head with
  | nil => exact hr
  | cons event rest ih =>
      refine ⟨?_, ih hl.2⟩
      intro ref hk
      obtain ⟨later, hm, hc⟩ := List.mem_flatMap.mp (hl.1 ref hk)
      exact List.mem_flatMap.mpr ⟨later, List.mem_append_left _ hm, hc⟩

/-- Announcements across initial notices and batches are unique, as are completions across
batches.
-/
def History.UniqueRefs (history : History) : Prop :=
  ((history.initialGroups ++ history.initialStreams).map DeliveryNode.ref
    ++ pendingRefs history.batches.flatten).Nodup
  ∧ (completedRefs history.batches.flatten).Nodup

/-- Every admitted prefix has one-shot announcements and completions, using initialization
and batching.
-/
theorem AdmissiblePrefix.uniqueRefs {work : Work} {history : History}
    (h : AdmissiblePrefix work history)
    : history.UniqueRefs := by
  obtain ⟨events, matching, failures, explained, batching⟩ := h
  have refs := batching.refPermutation
  constructor
  · apply (refs.pending.append_left _).nodup_iff.mpr
    exact explained.noticeFacts.announcedUnique
  · exact refs.completed.nodup_iff.mpr explained.noticeFacts.completedUnique

/-- Complete runs retain one-shot refs; their extra termination event contributes no
notice refs.
-/
theorem AdmissibleRun.uniqueRefs {work : Work} {history : History}
    (h : AdmissibleRun work history)
    : history.UniqueRefs := by
  obtain ⟨events, matching, failures, explained, _, batching⟩ := h
  have refs := batching.refPermutation
  constructor
  · apply (refs.pending.append_left _).nodup_iff.mpr
    simp only [pendingRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      eventPending, List.append_nil]
    exact explained.noticeFacts.announcedUnique
  · apply refs.completed.nodup_iff.mpr
    simpa [completedRefs, eventCompleted] using explained.noticeFacts.completedUnique

/-- Every initially or later announced node completes causally in a terminal history.
Witness: terminal history liveness plus occurrence-preserving work batching; no fairness
is asserted.
-/
theorem AdmissibleRun.liveRefs {work : Work} {history : History}
    (h : AdmissibleRun work history)
    : (∀ ref ∈ (history.initialGroups ++ history.initialStreams).map DeliveryNode.ref,
        ref ∈ completedRefs history.batches.flatten)
      ∧ liveBatches history.batches := by
  obtain ⟨events, matching, failures, explained, done, batching⟩ := h
  refine ⟨?_, batching.live (liveEvents_append_of_live (explained.liveEvents done) ?_)⟩
  · intro ref hk
    have completes := explained.allCompleted done ref (List.mem_append_left _ hk)
    apply batching.refPermutation.completed.mem_iff.mpr
    obtain ⟨event, member, completed⟩ := List.mem_flatMap.mp completes
    exact List.mem_flatMap.mpr ⟨event, List.mem_append_left _ member, completed⟩
  · simp [liveEvents, eventPending]

/-- Causal batch liveness implies total completion membership, by induction over batches.
-/
theorem liveBatches_pendingRefs {batches : List (List WorkQueueEvent)}
    (h : liveBatches batches) {ref : NodeRef} (member : ref ∈ pendingRefs batches.flatten)
    : ref ∈ completedRefs batches.flatten := by
  induction batches with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      simp only [List.flatten_cons, pendingRefs, List.flatMap_append] at member
      rcases List.mem_append.mp member with first | later
      · exact h.1 ref first
      · simpa only [List.flatten_cons, completedRefs, List.flatMap_append]
          using List.mem_append_right (completedRefs head) (ih h.2 later)

/-- Every announced node ref completes exactly once in a terminal history: liveness plus
Nodup counts.
-/
theorem AdmissibleRun.refsCompleteExactlyOnce {work : Work} {history : History}
    (h : AdmissibleRun work history)
    : ∀ ref ∈
        (history.initialGroups ++ history.initialStreams).map DeliveryNode.ref
        ++ pendingRefs history.batches.flatten,
        (completedRefs history.batches.flatten).count ref = 1 := by
  intro ref member
  have completed : ref ∈ completedRefs history.batches.flatten := by
    rcases List.mem_append.mp member with initial | later
    · exact h.liveRefs.1 ref initial
    · exact liveBatches_pendingRefs h.liveRefs.2 later
  simp [h.uniqueRefs.2.count, completed]

end GraphQL.IncrementalDelivery.WorkQueueSemantics
