import GraphQL.IncrementalDelivery.Correctness
import Proofs.GraphQL.IncrementalDelivery.Correctness.Observation

/-! Wire ID safety forbids repeated completion, independently of hasNext.
Combining this safety with eventual completion gives exactly one completion per ID.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- One Boolean safety step is exactly freshness, uniqueness, open references, and safe
continuation. Witness: Boolean/list reflection; this is a proof view, not a second safety
definition.
-/
theorem idUsageValid_cons_iff (seen active : List String)
    (update : IncrementalStreamUpdateResult) (rest : List IncrementalStreamUpdateResult)
    : DeliveryTrace.idUsageValid seen active (update :: rest) = true
      ↔ (∀ id ∈ update.pending.map IncrementalPendingNotice.id, id ∉ seen)
        ∧ (update.pending.map IncrementalPendingNotice.id).Nodup
        ∧ (update.completed.map IncrementalCompletionNotice.id).Nodup
        ∧ (∀ id ∈ update.completed.map IncrementalCompletionNotice.id,
            id ∈ active ++ update.pending.map IncrementalPendingNotice.id)
        ∧ (∀ patch ∈ update.incremental,
            patch.id ∈ active ++ update.pending.map IncrementalPendingNotice.id)
        ∧ DeliveryTrace.idUsageValid
            (seen ++ update.pending.map IncrementalPendingNotice.id)
            ((active ++ update.pending.map IncrementalPendingNotice.id).filter
              (fun id =>
                !(update.completed.map IncrementalCompletionNotice.id).contains id))
            rest
          = true := by
  simp [DeliveryTrace.idUsageValid, List.all_eq_true, and_assoc]

/-- A known closed ID cannot complete again; induction uses freshness to prevent
reannouncement.
-/
theorem idUsageValid_neverCompletesClosed (seen active : List String)
    (updates : List IncrementalStreamUpdateResult)
    (h : DeliveryTrace.idUsageValid seen active updates = true) (id : String)
    (hs : id ∈ seen) (ha : id ∉ active)
    : id ∉ DeliveryTrace.completedIDs updates := by
  induction updates generalizing seen active with
  | nil => simp [DeliveryTrace.completedIDs]
  | cons update rest ih =>
      rw [idUsageValid_cons_iff] at h
      obtain ⟨hf, _, _, hc, _, ht⟩ := h
      have unavailable : id ∉ active ++ update.pending.map IncrementalPendingNotice.id := by
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact ha hm
        · exact hf id hm hs
      have htail := ih _ _ ht (List.mem_append_left _ hs)
        (fun hm => unavailable (List.mem_filter.mp hm).1)
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact unavailable (hc id hm)
      · exact htail hm

/-- Completion notices are unique, by one-step uniqueness and the closed-ID exclusion
witness.
-/
theorem idUsageValid_completedIDs_nodup (seen active : List String)
    (updates : List IncrementalStreamUpdateResult)
    (h : DeliveryTrace.idUsageValid seen active updates = true)
    (ha : ∀ id ∈ active, id ∈ seen)
    : (DeliveryTrace.completedIDs updates).Nodup := by
  induction updates generalizing seen active with
  | nil => simp [DeliveryTrace.completedIDs]
  | cons update rest ih =>
      rw [idUsageValid_cons_iff] at h
      obtain ⟨_, _, hc, hav, _, ht⟩ := h
      have available : ∀ id ∈ active ++ update.pending.map IncrementalPendingNotice.id,
          id ∈ seen ++ update.pending.map IncrementalPendingNotice.id := by
        intro id hm
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ (ha id hm)
        · exact List.mem_append_right _ hm
      have htail := ih _ _ ht (fun id hm => available id (List.mem_filter.mp hm).1)
      change (_ ++ DeliveryTrace.completedIDs rest).Nodup
      rw [List.nodup_append]
      refine ⟨hc, htail, ?_⟩
      intro id hm later hl he
      subst later
      apply idUsageValid_neverCompletesClosed _ _ rest ht id (available id (hav id hm)) _
        hl
      intro hfiltered
      have hb := (List.mem_filter.mp hfiltered).2
      have hm' := List.contains_iff_mem.mpr hm
      simp only [hm', Bool.not_true, Bool.false_eq_true] at hb

/-- Announcements stay unique across updates; induction appends only fresh, unique IDs. -/
theorem idUsageValid_idsUnique (seen active : List String)
    (updates : List IncrementalStreamUpdateResult)
    (h : DeliveryTrace.idUsageValid seen active updates = true) (hs : seen.Nodup)
    : (seen ++ DeliveryTrace.pendingIDs updates).Nodup := by
  induction updates generalizing seen active with
  | nil => simpa [DeliveryTrace.pendingIDs] using hs
  | cons update rest ih =>
      rw [idUsageValid_cons_iff] at h
      obtain ⟨hf, hn, _, _, _, ht⟩ := h
      have hnext : (seen ++ update.pending.map IncrementalPendingNotice.id).Nodup := by
        rw [List.nodup_append]
        refine ⟨hs, hn, ?_⟩
        intro old ho fresh hm he
        subst fresh
        exact hf old hm ho
      simpa [DeliveryTrace.pendingIDs, List.append_assoc] using ih _ _ ht hnext

/-- Open-ID references imply causal announcements; induction preserves active IDs' history
support.
-/
theorem idUsageValid_patchesAnnounced (seen active : List String)
    (updates : List IncrementalStreamUpdateResult)
    (h : DeliveryTrace.idUsageValid seen active updates = true)
    (ha : ∀ id ∈ active, id ∈ seen)
    : DeliveryTrace.patchesAnnounced seen updates := by
  induction updates generalizing seen active with
  | nil => trivial
  | cons update rest ih =>
      rw [idUsageValid_cons_iff] at h
      obtain ⟨_, _, _, _, hp, ht⟩ := h
      have available : ∀ id ∈ active ++ update.pending.map IncrementalPendingNotice.id,
          id ∈ seen ++ update.pending.map IncrementalPendingNotice.id := by
        intro id hm
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ (ha id hm)
        · exact List.mem_append_right _ hm
      exact ⟨fun patch hm => available patch.id (hp patch hm),
        ih _ _ ht (fun id hm => available id (List.mem_filter.mp hm).1)⟩

/-- Query-level uniqueness follows from the initial uniqueness and the update induction
witness.
-/
theorem idsUnique_of_idUsageValid (result : QueryResult) (h : result.idUsageValid)
    : result.idsUnique := by
  cases result with
  | single response => trivial
  | incremental initial subsequent => exact idUsageValid_idsUnique _ _ _ h.2 h.1

/-- Query-level causal references follow from initially announced IDs and safe updates. -/
theorem patchesAnnounced_of_idUsageValid (result : QueryResult) (h : result.idUsageValid)
    : result.patchesAnnounced := by
  cases result with
  | single response => trivial
  | incremental initial subsequent =>
      exact idUsageValid_patchesAnnounced _ _ _ h.2 (by intros; assumption)

/-- Causal liveness implies membership in the total completion list, by update-list
induction.
-/
theorem announcementsEventuallyComplete_pendingIDs
    (updates : List IncrementalStreamUpdateResult)
    (h : DeliveryTrace.announcementsEventuallyComplete updates)
    (id : String) (hi : id ∈ DeliveryTrace.pendingIDs updates)
    : id ∈ DeliveryTrace.completedIDs updates := by
  induction updates with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons update rest ih =>
      rcases List.mem_append.mp hi with hi | hi
      · exact h.1 id hi
      · exact List.mem_append_right _ (ih h.2 hi)

/-- Safety plus liveness gives exactly-once completion: a present element of a Nodup list
counts once.
-/
theorem idsCompleteExactlyOnce_of_idUsageValid_of_liveness (result : QueryResult)
    (hs : result.idUsageValid) (hl : result.idsEventuallyComplete)
    : result.idsCompleteExactlyOnce := by
  cases result with
  | single response => trivial
  | incremental initial subsequent =>
      have hn := idUsageValid_completedIDs_nodup _ _ subsequent hs.2 (by intros; assumption)
      intro id hi
      have hm : id ∈ DeliveryTrace.completedIDs subsequent := by
        rcases List.mem_append.mp hi with hi | hi
        · exact hl.1 id hi
        · exact announcementsEventuallyComplete_pendingIDs subsequent hl.2 id hi
      simp [hn.count, hm]

/-- The public exactly-once claim follows from separate safety/liveness witnesses for all
outcomes. This composition theorem does not itself prove either scheduler-to-wire premise.
-/
theorem deliveryIDsCompleteExactlyOnce_of_idUsageValid_of_liveness (schema : Schema)
    (operation : Operation) (hs : deliveryIDUsageValid schema operation)
    (hl : deliveryIDsEventuallyComplete schema operation)
    : deliveryIDsCompleteExactlyOnce schema operation := by
  intro ObjectRef resolvers variables fuel source result observed
  exact idsCompleteExactlyOnce_of_idUsageValid_of_liveness _
    (hs resolvers variables fuel source result (queryOutcome_observation observed))
    (hl resolvers variables fuel source result observed)

end GraphQL.IncrementalDelivery.Correctness
