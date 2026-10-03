import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureSource

/-! Exact source-contribution lists bridge to the scheduler's node-error accounting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A distinct contribution list supplies the existential NodeErrors function
-----------------------------------------------------------------------------------------

/-- Distinct owning-task failure pairs have exactly their listed sum in `NodeErrors`.
Witness: extend the contribution function at one fresh occurrence per list entry;
uniqueness ensures that earlier assignments and the remaining sum stay unchanged.
-/
theorem failureContributions_nodeErrors {work : Execution.Work} {ref : NodeRef}
    (parts : List (Occurrence × Nat)) (unique : (parts.map Prod.fst).Nodup)
    (known
      : ∀ occurrence errors,
          (occurrence, errors) ∈ parts
          → ∃ owners producer path,
              TaskAt work occurrence owners producer (.object path (.error errors))
              ∧ ref ∈ owners)
    : NodeErrors work (parts.map Prod.fst) ref (parts.map Prod.snd).sum := by
  classical
  induction parts with
  | nil => exact ⟨fun _ => 0, by simp, rfl⟩
  | cons head rest ih =>
      obtain ⟨occurrence, errors⟩ := head
      obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
      obtain ⟨owners, producer, path, task, owner⟩ := known occurrence errors List.mem_cons_self
      obtain ⟨contribution, counts, sum⟩ := ih tailUnique
        (fun task errors member => known task errors (List.mem_cons_of_mem _ member))
      let extended := fun other => if other = occurrence then errors else contribution other
      have tailSame : (rest.map Prod.fst).map extended
          = (rest.map Prod.fst).map contribution := by
        apply List.map_congr_left
        intro other member
        have different : other ≠ occurrence := fun same => fresh (same ▸ member)
        simp [extended, different]
      refine ⟨extended, ?_, ?_⟩
      · intro other member
        rcases List.mem_cons.mp member with same | earlier
        · subst other
          exact ⟨owners, producer, _, task, by simp [extended, owner, Payload.failure]⟩
        · obtain ⟨otherOwners, parent, payload, descriptor, count⟩ := counts other earlier
          have different : other ≠ occurrence := fun same => fresh (same ▸ earlier)
          exact ⟨otherOwners, parent, payload, descriptor, by
            simpa [extended, different] using count⟩
      · simpa only [List.map_cons, List.sum_cons, tailSame, extended, ↓reduceIte]
          using congrArg (errors + ·) sum

/-- A certified source total has a nonempty distinct `NodeErrors` contributor inventory.
Witness: retain the source certificate's task identities and construct their contribution
function. This list is per completion, not yet one shared ordered failure-cut witness.
-/
theorem GroupFailureTotal.nodeErrors {work inputs ref errors}
    (total : GroupFailureTotal work inputs ref errors)
    : ∃ failed : List Occurrence,
        failed ≠ []
        ∧ failed.Nodup
        ∧ NodeErrors work failed ref errors
        ∧ ∀ occurrence ∈ failed,
            ∃ count owners producer path,
              GraphEvent.taskFailure occurrence count ∈ inputs
              ∧ TaskAt work occurrence owners producer (.object path (.error count))
              ∧ ref ∈ owners := by
  obtain ⟨parts, nonempty, unique, sum, sources⟩ := total
  refine ⟨parts.map Prod.fst, ?_, unique, ?_, ?_⟩
  · intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  · rw [← sum]
    exact failureContributions_nodeErrors parts unique
      (fun occurrence errors member => (sources occurrence errors member).2)
  · intro occurrence member
    obtain ⟨⟨task, count⟩, member, same⟩ := List.mem_map.mp member
    dsimp only at same
    subst task
    obtain ⟨received, owners, producer, path, known, owner⟩ := sources occurrence count member
    exact ⟨count, owners, producer, path, received, known, owner⟩

-----------------------------------------------------------------------------------------
-- Contributor completeness is the remaining bridge to a shared cut inventory
-----------------------------------------------------------------------------------------

/-- A distinct complete superset of a node's contributors has the same error total.
Witness: keep counted occurrences, assign zero to other known tasks, and partition the
larger list into the original contributors (up to permutation) and noncontributors.
The coverage premise is explicit; this theorem does not assert it for actual queue cuts.
-/
theorem nodeErrors_of_complete_contributors {work selected failed ref errors}
    (counts : NodeErrors work selected ref errors) (selectedUnique : selected.Nodup)
    (failedUnique : failed.Nodup) (included : selected.Subset failed)
    (known
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload, TaskAt work occurrence owners producer payload)
    (complete
      : ∀ occurrence ∈ failed,
          ∀ owners,
            TaskHasOwners work occurrence owners → ref ∈ owners → occurrence ∈ selected)
    : NodeErrors work failed ref errors := by
  classical
  obtain ⟨contribution, assigned, total⟩ := counts
  let kept := fun occurrence => decide (occurrence ∈ selected)
  let extended := fun occurrence => if occurrence ∈ selected then contribution occurrence else 0
  have same : (failed.filter kept).Perm selected := by
    apply (List.perm_ext_iff_of_nodup (failedUnique.filter _) selectedUnique).mpr
    intro occurrence
    simp only [List.mem_filter, kept, decide_eq_true_eq]
    exact ⟨And.right, fun member => ⟨included member, member⟩⟩
  have oldSame : selected.map extended = selected.map contribution := by
    apply List.map_congr_left
    intro occurrence member
    simp [extended, member]
  have zero : ((failed.filter (fun occurrence => !kept occurrence)).map extended).sum = 0 := by
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro count member
    obtain ⟨occurrence, present, rfl⟩ := List.mem_map.mp member
    have absent : occurrence ∉ selected := by
      simpa [kept] using (List.mem_filter.mp present).2
    simp [extended, absent]
  refine ⟨extended, ?_, ?_⟩
  · intro occurrence member
    by_cases present : occurrence ∈ selected
    · obtain ⟨owners, producer, payload, descriptor, count⟩ := assigned occurrence present
      exact ⟨owners, producer, payload, descriptor, by simpa [extended, present] using count⟩
    · obtain ⟨owners, producer, payload, descriptor⟩ := known occurrence member
      have nonowner : ref ∉ owners := fun owner =>
        present (complete occurrence member owners ⟨producer, payload, descriptor⟩ owner)
      exact ⟨owners, producer, payload, descriptor, by simp [extended, present, nonowner]⟩
  · have partition := ((List.filter_append_perm kept failed).map extended).sum_nat
    rw [List.map_append, List.sum_append, zero, Nat.add_zero,
      (same.map extended).sum_nat, oldSame] at partition
    exact total.trans partition

/-- Every actual atomic failed-group total admits an exact per-completion inventory.
Witness: normalized source provenance and the generic contribution-function construction.
Only the complete-contributor bridge above can transport it to a larger shared cut list;
cut visibility, cancellation safety, and open-owner licensing are separate obligations.
-/
theorem createWorkQueue_runNormalized_groupFailure_nodeErrorsWitness
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms)
    : ∃ failed : List Occurrence,
        failed ≠ []
        ∧ failed.Nodup
        ∧ NodeErrors work failed group.ref errors
        ∧ ∀ occurrence ∈ failed,
            ∃ count owners producer path,
              GraphEvent.taskFailure occurrence count ∈ batches.flatten
              ∧ TaskAt work occurrence owners producer (.object path (.error count))
              ∧ group.ref ∈ owners :=
  (createWorkQueue_runNormalized_atomicGroupFailure_source generated valid
    emitted).nodeErrors

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
