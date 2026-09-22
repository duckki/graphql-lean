import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness

/-! Logical redundancy checks without changing permissive raw-work admission. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Failure uniqueness follows from licensing and admitted publication provenance
-----------------------------------------------------------------------------------------

/-- Earlier-occurrence freshness implies mapped-list uniqueness. Witness: list induction;
a second occurrence contradicts freshness at the split immediately preceding it.
-/
private theorem nodup_of_fresh {failures : FailureCuts}
    (fresh
      : ∀ before cut occurrence after,
          failures = before ++ (cut, occurrence) :: after
          → occurrence ∉ before.map Prod.snd)
    : (failures.map Prod.snd).Nodup := by
  induction failures with
  | nil => simp
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · rintro member
        obtain ⟨⟨cut, occurrence⟩, included, same⟩ := List.mem_map.mp member
        obtain ⟨before, after, equal⟩ := List.mem_iff_append.mp included
        apply fresh (first :: before) cut occurrence after
          (by simp only [equal, List.cons_append])
        exact List.mem_cons.mpr (Or.inl same)
      · apply ih
        intro before cut occurrence after equal member
        exact fresh (first :: before) cut occurrence after
          (by simp only [equal, List.cons_append]) (by simpa using Or.inr member)

/-- Failure uniqueness follows when recorded failures have no successful publication.
Witness: an earlier copy cancels its unpublished, nonempty-owned task at a reached cut.
The publication exclusion follows from event provenance in an explained history.
-/
theorem FailureWitness.nodup {work initial matching events failures}
    (witness : FailureWitness work initial matching events failures)
    (unpublished
      : ∀ occurrence ∈ failures.map Prod.snd, ¬Published matching events occurrence)
    : (failures.map Prod.snd).Nodup := by
  apply nodup_of_fresh
  intro before cut occurrence after equal member
  have facts := witness before cut occurrence after equal
  obtain ⟨owners, producer, payload, known, _, _, key, contributes, _⟩ := facts.2.2.1
  apply facts.2.2.2
  apply TaskCancelled.of_recorded known (fun empty => by simp [empty] at contributes)
  · intro published
    apply unpublished occurrence (by simp only [equal, List.map_append,
      List.map_cons, List.mem_append, List.mem_cons]; exact Or.inr (Or.inl trivial))
    simpa only [List.take_append_drop] using published.append (events.drop cut)
  · have filtered
        : before.filter (fun entry => decide (entry.1 ≤ (events.take cut).length))
          = before :=
      List.filter_eq_self.mpr
        (fun entry included => by
          simpa only [List.length_take, Nat.min_eq_left facts.1, decide_eq_true_eq]
            using facts.2.1 entry included)
    simpa only [failedBefore, filtered] using member

/-- Every explained history has unique actual failure occurrences.
Witness: successful event provenance excludes publications of failing tasks, then the
ordered failure licensing theorem applies. No generated-work premise is required.
-/
theorem Explains.failures_nodup {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : (failures.map Prod.snd).Nodup := by
  apply explained.2.1.nodup
  intro occurrence member
  apply explained.failed_unpublished (cut := events.length)
  simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)] using member

/-- On histories excluding failed publications, explicit failure uniqueness is redundant.
Witness: derive uniqueness from licensing, or discard the redundant conjunct.
-/
theorem failureWitness_iff_nodup_and {work initial matching events failures}
    (unpublished
      : ∀ occurrence ∈ failures.map Prod.snd, ¬Published matching events occurrence)
    : FailureWitness work initial matching events failures
      ↔ (failures.map Prod.snd).Nodup
        ∧ FailureWitness work initial matching events failures :=
  ⟨fun witness => ⟨witness.nodup unpublished, witness⟩, And.right⟩

-----------------------------------------------------------------------------------------
-- Terminal node accounting suffices when every task has an owner
-----------------------------------------------------------------------------------------

/-- The node clause of Terminal, separated only for this redundancy experiment.
The other arguments are the same work, initial keys, and history explanation as Terminal.
-/
def NodesTerminal (work : Work) (initial : Keys) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failed : FailureCuts)
    : Prop :=
  ∀ node kind dependencies birth,
    NodeAt work node kind dependencies birth
    → node.key ∈ completedKeys events
      ∨ node.key ∉ announcedKeys initial events
        ∧ (NodeFailed work matching events failed node.key
            ∨ NodeAccounted work matching events failed node.key)

/-- Explained terminal nodes account for every nonempty-owned task. Witness: an
outstanding task has a healthy unclosed owner, contradicting that owner's terminal clause.
-/
theorem terminal_iff_nodes {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (owned
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload → owners ≠ [])
    : Terminal work ((groups ++ streams).map DeliveryNode.key) matching events failures
      ↔ NodesTerminal work ((groups ++ streams).map DeliveryNode.key) matching events
          failures := by
  refine ⟨fun terminal => terminal.2, fun nodes => ⟨?_, nodes⟩⟩
  intro occurrence owners producer payload known
  apply Classical.byContradiction
  intro outstanding
  obtain ⟨key, member, healthy, openKey⟩ :=
    explained.outstanding_owner known (owned _ _ _ _ known) outstanding
  obtain ⟨node, kind, dependencies, birth, descriptor, same⟩ := known.owner_known member
  rcases nodes node kind dependencies birth descriptor with closed | ⟨_, failed | accounted⟩
  · exact openKey (same ▸ closed)
  · exact healthy (same ▸ failed)
  · exact outstanding (accounted occurrence owners ⟨producer, payload, known⟩ (same.symm ▸ member))

end GraphQL.IncrementalDelivery.WorkQueueSemantics
