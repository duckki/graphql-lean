import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordInvalidation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Permanent cancellation history includes ancestor-only registration records
-----------------------------------------------------------------------------------------

/-- Each cancellation ref has a failed-task cause through registration ancestry.
`failed` is the accepted task-failure inventory. Taskless records need no `NodeAt` witness;
the contributor bridge recovers ordinary causal invalidation wherever it is relevant.
-/
def State.CancelledRecordsSupported (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  ∀ ref ∈ queue.cancelledGroups, GroupRecordInvalidated work failed ref

/-- Contributor-only cancellation support implies the record-aware invariant.
Witness: embed each contributing-node cause into record invalidation.
-/
theorem State.CancelledGroupsSupported.toRecords {queue work failed}
    (supported : State.CancelledGroupsSupported queue work failed)
    : queue.CancelledRecordsSupported work failed :=
  fun ref member => (supported ref member).toRecordInvalidated

/-- A record with no cleanup cause is absent from supported cancellation history.
Witness: membership would supply the contradictory record-invalidation witness.
-/
theorem State.CancelledRecordsSupported.healthy_not_mem {queue work failed ref}
    (supported : State.CancelledRecordsSupported queue work failed)
    (healthy : ¬GroupRecordInvalidated work failed ref)
    : ref ∉ queue.cancelledGroups :=
  fun member => healthy (supported ref member)

/-- An actual healthy generated contributor cannot be recorded as cancelled.
Witness: record cleanup and the original group invalidation agree on that contributor.
-/
theorem State.CancelledRecordsSupported.contributor_healthy_not_mem
    {queue work failed node dependencies producer}
    (supported : State.CancelledRecordsSupported queue work failed)
    (generated : ExecutedWork work)
    (known : NodeAt work node .group dependencies producer)
    (healthy : ¬GroupInvalidated work failed node.ref)
    : node.ref ∉ queue.cancelledGroups :=
  supported.healthy_not_mem
    (fun failure =>
      healthy ((generated.groupRecordInvalidated_iff_groupInvalidated known).mp failure))

/-- Enlarging the settled-failure inventory preserves record cancellation support.
Witness: monotonicity of each retained record's cleanup derivation.
-/
theorem State.CancelledRecordsSupported.weaken {queue work before after}
    (supported : State.CancelledRecordsSupported queue work before)
    (included : before.Subset after)
    : queue.CancelledRecordsSupported work after :=
  fun ref member => (supported ref member).mono included

-----------------------------------------------------------------------------------------
-- Refused children inherit cancellation from their actual registration parent
-----------------------------------------------------------------------------------------

/-- Registration preserves record-aware cancellation support, including taskless groups.
Witness: the refused child's immediate parent belongs to its full registration ancestry.
-/
theorem State.CancelledRecordsSupported.addGroup {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (group : Group)
    (matching
      : ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head?)
    : (queue.addGroup group).CancelledRecordsSupported work failed := by
  unfold State.addGroup
  split
  · exact supported
  · split
    · rename_i blocked
      intro ref member
      rcases List.mem_append.mp member with old | new
      · exact supported ref old
      · obtain rfl := List.mem_singleton.mp new
        obtain ⟨dependencies, known, canonical⟩ := matching
        cases parentEq : group.parent with
        | none => simp [parentEq] at blocked
        | some parent =>
            have cancelled : parent ∈ queue.cancelledGroups := by
              simpa [parentEq] using blocked
            exact .ancestor known (List.mem_of_head? (canonical.symm.trans parentEq))
              (supported _ cancelled)
    · exact supported

/-- Every candidate order preserves record-aware cancellation support during registration.
Witness: induction threads the state through refused children; linking changes no refs.
-/
theorem State.CancelledRecordsSupported.addGroups {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (groups : List Group)
    (matching
      : ∀ group ∈ groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    : (queue.addGroups groups).1.CancelledRecordsSupported work failed := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.ref
      && (queue.groupNode? group.node.ref).isNone)
  have fold (more : List Group) (current : State)
      (prior : current.CancelledRecordsSupported work failed)
      (subset : more.Subset groups)
      : (more.foldl State.addGroup current).CancelledRecordsSupported work failed := by
    induction more generalizing current with
    | nil => exact prior
    | cons group rest ih =>
        exact ih _ (prior.addGroup group (matching group (subset List.mem_cons_self)))
          (fun _ member => subset (List.mem_cons_of_mem _ member))
  have registered := fold fresh queue supported
    (fun _ member => (List.mem_filter.mp member).1)
  intro ref member
  rw [State.addGroups_cancelledGroups] at member
  exact registered ref member

/-- Integration preserves record-aware cancellation support using lowering metadata only.
Witness: supported registration followed by unchanged cancellation refs in later stages.
-/
theorem State.CancelledRecordsSupported.maybeIntegrateWork {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (newWork : Work)
    (parentTask : Option Occurrence)
    (matching
      : ∀ group ∈ newWork.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    : (queue.maybeIntegrateWork newWork parentTask).1.CancelledRecordsSupported work
        failed := by
  intro ref member
  rw [State.maybeIntegrateWork_cancelledGroups queue newWork parentTask] at member
  exact supported.addGroups newWork.groups matching ref member

/-- Initial record cancellation support needs no source or generated-work assumption.
Witness: queue creation records no cancellations, even on raw work chunks.
-/
theorem createWorkQueue_cancelledRecordsSupported (initialWork : Work)
    (work : Execution.Work) (failed : List Occurrence)
    : (State.initialize initialWork).CancelledRecordsSupported work failed :=
  (createWorkQueue_cancelledGroupsSupported initialWork work failed).toRecords

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
