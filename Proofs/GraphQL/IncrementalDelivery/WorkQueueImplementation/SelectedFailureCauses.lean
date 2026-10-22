import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedFailureCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupAncestorHealth

/-! Selected proof cuts preserve the cause of an observable group completion.
Ancestor health separates a direct reported failure from an inherited cancellation.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Selection preserves a group's positive output cause when its ancestors are healthy.
Witness: boundary-wise invalidation preservation recovers a selected cause; healthy
ancestry makes it direct. Generated delivery failures select one primitive error, so the
replacement contributor has exactly the reported count without summing diagnostics.
-/
theorem ExecutedWork.selectObjectFailureCuts_nodeFailureCause
    {work cuts bound node dependencies producer errors}
    (generated : ExecutedWork work)
    (ordered : cuts.Pairwise (fun left right => left.1 ≤ right.1))
    (known : NodeAt work node .group dependencies producer)
    (failedKnown
      : ∀ entry ∈ cuts,
          ∃ owners producer payload,
            TaskAt work entry.2 owners producer payload ∧ payload.failure.isSome = true)
    (ancestors : GroupAncestorsHealthy work (failedBefore cuts bound) node.ref)
    (cause : NodeFailureCause work (failedBefore cuts bound) node.ref errors)
    : NodeFailureCause work
        (failedBefore (selectObjectFailureCuts work [] cuts) bound) node.ref errors := by
  have count := generated.nodeFailureCause_count cause
  subst errors
  have rawInvalid : GroupRecordInvalidated work (failedBefore cuts bound) node.ref := by
    obtain ⟨occurrence, recorded, owners, birth, payload, task, owner, _, _⟩ := cause
    exact .task ⟨birth, payload, task⟩ owner recorded
  have selectedInvalid := (selectObjectFailureCuts_failedBefore_groupRecordInvalidated
    work [] cuts bound node.ref ordered).mp rawInvalid
  simp only [List.nil_append] at selectedInvalid
  rcases generated.groupRecordInvalidated_causes (groupRecordAt_of_nodeAt known) selectedInvalid with
    ⟨occurrence, owners, ⟨birth, payload, task⟩, owner, recorded⟩
    | ⟨ancestor, member, invalid⟩
  · obtain ⟨entry, selected, same⟩ := List.mem_map.mp recorded
    have selectedEntry := (List.mem_filter.mp selected).1
    have rawEntry := (selectObjectFailureCuts_sublist work [] cuts).subset selectedEntry
    obtain ⟨otherOwners, otherBirth, otherPayload, otherTask, failed⟩ := failedKnown entry rawEntry
    rw [same] at otherTask
    have equal := task.unique otherTask
    have fails : payload.failure.isSome = true := equal.2.2.symm ▸ failed
    have unit := generated.taskFailure_count task fails
    have failure : payload.failure = some 1 := by
      cases result : payload.failure with
      | none => simp [result] at fails
      | some errors =>
          have one : errors = 1 := by simpa only [result, Option.getD_some] using unit
          exact congrArg Option.some one
    exact ⟨occurrence, recorded, owners, birth, payload, task, owner, failure, by decide⟩
  · have rawAncestor := (selectObjectFailureCuts_failedBefore_groupRecordInvalidated
      work [] cuts bound ancestor ordered).mpr invalid
    exact False.elim (ancestors node dependencies (groupRecordAt_of_nodeAt known)
      rfl ancestor member rawAncestor)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
