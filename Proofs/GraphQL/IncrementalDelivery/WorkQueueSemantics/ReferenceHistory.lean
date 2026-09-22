import GraphQL.IncrementalDelivery.Execution

/-! Proof-only causal reference accounting, shared by work events and wire updates.
Completed keys remain in history. Coalescing allows a reference and its completion
in the same update, but cannot legalize a reference after an earlier update closed it.
-/

namespace GraphQL.IncrementalDelivery

def ReferenceHistory (pending completed used : α → List κ) (seen closed : List κ)
    : List α → Prop
  | [] => True
  | event :: rest =>
      (∀ key ∈ used event, key ∈ seen ++ pending event ∧ key ∉ closed)
      ∧ ReferenceHistory pending completed used (seen ++ pending event)
          (closed ++ completed event) rest

namespace ReferenceHistory

variable {pending completed used : α → List κ}

/-- Membership-equivalent histories preserve reference legality, by list induction. -/
theorem congr {seen closed more done : List κ} {events : List α}
    (h : ReferenceHistory pending completed used seen closed events)
    (hs : ∀ key, key ∈ more ↔ key ∈ seen) (hc : ∀ key, key ∈ done ↔ key ∈ closed)
    : ReferenceHistory pending completed used more done events := by
  induction events generalizing seen closed more done with
  | nil => trivial
  | cons event rest ih =>
      refine ⟨?_, ih h.2 ?_ ?_⟩
      · intro key hk
        obtain ⟨known, fresh⟩ := h.1 key hk
        exact ⟨by simpa only [List.mem_append, hs] using known, fun hd => fresh ((hc key).mp hd)⟩
      · intro key; simp only [List.mem_append, hs]
      · intro key; simp only [List.mem_append, hc]

/-- Reference-valid histories concatenate with their accumulated seen/closed keys. -/
theorem append {seen closed : List κ} {head tail : List α}
    (h : ReferenceHistory pending completed used seen closed head)
    (t
      : ReferenceHistory pending completed used (seen ++ head.flatMap pending)
          (closed ++ head.flatMap completed) tail)
    : ReferenceHistory pending completed used seen closed (head ++ tail) := by
  induction head generalizing seen closed with
  | nil => simpa using t
  | cons event rest ih =>
      exact ⟨h.1, ih h.2 (by simpa only [List.flatMap_cons, List.append_assoc] using t)⟩

/-- A valid concatenation gives prefix references and a valid suffix, by induction. -/
theorem split {seen closed : List κ} {head tail : List α}
    (h : ReferenceHistory pending completed used seen closed (head ++ tail))
    : (∀ key ∈ head.flatMap used, key ∈ seen ++ head.flatMap pending ∧ key ∉ closed)
      ∧ ReferenceHistory pending completed used (seen ++ head.flatMap pending)
          (closed ++ head.flatMap completed) tail := by
  induction head generalizing seen closed with
  | nil => exact ⟨by simp, by simpa using h⟩
  | cons event rest ih =>
      obtain ⟨refs, future⟩ := ih h.2
      refine ⟨?_, by simpa only [List.flatMap_cons, List.append_assoc] using future⟩
      intro key hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨known, fresh⟩ := h.1 key hk
        exact ⟨by simpa only [List.flatMap_cons, ← List.append_assoc]
          using List.mem_append_left (rest.flatMap pending) known, fresh⟩
      · obtain ⟨known, fresh⟩ := refs key hk
        exact ⟨by simpa only [List.flatMap_cons, List.append_assoc] using known,
          fun hc => fresh (List.mem_append_left _ hc)⟩

/-- Grouping adjacent outputs preserves open references, by prefix splitting. -/
theorem batches {seen closed : List κ} {parts : List (List α)}
    (h : ReferenceHistory pending completed used seen closed parts.flatten)
    : ReferenceHistory (List.flatMap pending) (List.flatMap completed) (List.flatMap used)
        seen closed parts := by
  induction parts generalizing seen closed with
  | nil => trivial
  | cons head tail ih =>
      obtain ⟨refs, future⟩ := split h
      exact ⟨refs, ih future⟩

/-- A mapping preserving notices and references preserves validity, by list induction. -/
theorem map {pending' completed' used' : β → List κ} (f : α → β)
    (hp : ∀ event, pending' (f event) = pending event)
    (hc : ∀ event, completed' (f event) = completed event)
    (hu : ∀ event key, key ∈ used' (f event) ↔ key ∈ used event)
    {seen closed : List κ} {events : List α}
    (h : ReferenceHistory pending completed used seen closed events)
    : ReferenceHistory pending' completed' used' seen closed (events.map f) := by
  induction events generalizing seen closed with
  | nil => trivial
  | cons event rest ih =>
      simp only [List.map_cons, ReferenceHistory, hp, hc]
      exact ⟨fun key hk => h.1 key ((hu event key).mp hk), ih h.2⟩

end ReferenceHistory
end GraphQL.IncrementalDelivery
