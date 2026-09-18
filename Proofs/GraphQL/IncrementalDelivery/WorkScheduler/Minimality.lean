import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.TaskReadiness

/-! Logical redundancy checks without changing permissive raw-work admission. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Failure uniqueness follows from licensing and earlier cancellation
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

/-- Explicit failure uniqueness is redundant even for raw work. Witness: the open-owner
clause gives nonempty ownership for every recorded task; an earlier copy already cancels
that task and contradicts its later licensing. No generated-work premise is needed.
-/
theorem FailureWitness.nodup {work initial events failures}
    (witness : FailureWitness work initial events failures)
    : (failures.map Prod.snd).Nodup := by
  apply nodup_of_fresh
  intro before cut occurrence after equal member
  have facts := witness before cut occurrence after equal
  obtain ⟨owners, producer, payload, known, _, _, key, contributes, _⟩ := facts.2.2.1
  exact facts.2.2.2 (TaskCancelled.of_recorded known
    (fun empty => by simp [empty] at contributes) member)

/-- Adding the former explicit uniqueness clause leaves failure admission unchanged.
Witness: derive uniqueness from licensing, or discard the redundant conjunct.
-/
theorem failureWitness_iff_nodup_and {work initial events failures}
    : FailureWitness work initial events failures
      ↔ (failures.map Prod.snd).Nodup ∧ FailureWitness work initial events failures :=
  ⟨fun witness => ⟨witness.nodup, witness⟩, And.right⟩

-----------------------------------------------------------------------------------------
-- Terminal node accounting suffices when every task has an owner
-----------------------------------------------------------------------------------------

/-- The node clause of Terminal, separated only for this redundancy experiment.
The other arguments are the same work, initial keys, and history explanation as Terminal.
-/
def NodesTerminal (work : Work) (initial : Keys) (matching : PublicationMatching)
    (events : List WorkEvent) (failed : List Occurrence)
    : Prop :=
  ∀ node kind parents birth,
    NodeAt work node kind parents birth
    → node.key ∈ completedKeys events
      ∨ node.key ∉ announcedKeys initial events
        ∧ (NodeFailed work failed node.key
            ∨ NodeAccounted work matching events failed node.key)

/-- Explained terminal nodes account for every nonempty-owned task. Witness: an
outstanding task has a healthy unclosed owner, contradicting that owner's terminal clause.
-/
theorem terminal_iff_nodes {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (owned
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload → owners ≠ [])
    : Terminal work ((groups ++ streams).map DeliveryNode.key) matching events
        (failedBefore failures events.length)
      ↔ NodesTerminal work ((groups ++ streams).map DeliveryNode.key) matching events
          (failedBefore failures events.length) := by
  refine ⟨fun terminal => terminal.2, fun nodes => ⟨?_, nodes⟩⟩
  intro occurrence owners producer payload known
  apply Classical.byContradiction
  intro outstanding
  obtain ⟨key, member, healthy, openKey⟩ :=
    explained.outstanding_owner known (owned _ _ _ _ known) outstanding
  obtain ⟨node, kind, parents, birth, descriptor, same⟩ := known.owner_known member
  rcases nodes node kind parents birth descriptor with closed | ⟨_, failed | accounted⟩
  · exact openKey (same ▸ closed)
  · exact healthy (same ▸ failed)
  · exact outstanding (accounted occurrence owners ⟨producer, payload, known⟩ (same.symm ▸ member))

end GraphQL.IncrementalDelivery.WorkScheduler
