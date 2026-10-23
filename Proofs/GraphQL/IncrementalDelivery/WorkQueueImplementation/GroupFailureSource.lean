import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchFailureSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureAccounting

/-! Failed group closures retain aggregate contributing source causes through actual batching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Raw source replay retains selected source causes
-----------------------------------------------------------------------------------------

/-- A failed group closure reports distinct matching contributing source rejections.
-/
abbrev GroupFailureOrigin (work : Execution.Work) (inputs : List GraphEvent)
    (group : Execution.DeliveryNode) (errors : Nat)
    : Prop :=
  GroupFailureSources work inputs group.ref errors

/-- A successful flush itself emits no failed group closure.
Witness: its exact output is optional values followed by successful completion.
The enclosing handler can still emit failed closures during its later drain.
-/
theorem State.finishGroupSuccess_no_groupFailure (queue : State) (node : GroupNode)
    (group : Execution.DeliveryNode) (errors : Nat)
    : Execution.WorkQueueEvent.groupFailure group errors
      ∉ (queue.finishGroupSuccess node).2.1 :=
  queue.finishGroupSuccess_groupFailure_absent node group errors

/-- A task-failure handler emits its current count for one of the task's contributors.
Witness: its actual owner fold; this does not cover cached failures from other handlers.
-/
theorem State.taskFailure_groupFailure_source (queue : State) (occurrence : Occurrence)
    (errors : Nat) {group count}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group count
        ∈ (queue.taskFailure occurrence errors).2)
    : ∃ node,
        queue.taskNode? occurrence = some node
        ∧ group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
        ∧ count = errors :=
  queue.taskFailure_groupFailure_current occurrence errors emitted

/-- Every normalized failed group closure retains its exact aggregate source inventory.
Witness: actual cache-aware FIFO batches and startup forwarding, followed by publisher
normalization. Task-local caches remain distinct from the aggregate notice inventory.
-/
theorem createWorkQueue_runNormalized_groupFailure_source {work : Execution.Work}
    (_generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    : GroupFailureOrigin work batches.flatten group errors :=
  createWorkQueue_runNormalized_groupFailure_sources valid emitted

/-- Atomic value splitting neither creates nor changes a failed group closure.
Witness: only the failed group constructor has such a control atom.
-/
theorem publicationAtoms_groupFailure_mem (event : Execution.WorkQueueEvent)
    {group errors}
    : Execution.WorkQueueEvent.groupFailure group errors ∈ publicationAtoms event
      ↔ event = .groupFailure group errors := by
  cases event with
  | groupValues => simp [publicationAtoms]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms]
      | case2 => simp [publicationAtoms, streamPublicationAtoms]
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms] using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms, eq_comm]

/-- Atomic group failures retain the exact aggregate source causes of their wire event.
Witness: atomic value expansion leaves group-failure controls and error counts intact.
-/
theorem createWorkQueue_runNormalized_atomicGroupFailure_source {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms)
    : GroupFailureOrigin work batches.flatten group errors := by
  obtain ⟨event, member, within⟩ := List.mem_flatMap.mp emitted
  have same := (publicationAtoms_groupFailure_mem event).mp within
  subst event
  exact createWorkQueue_runNormalized_groupFailure_source generated valid member

-----------------------------------------------------------------------------------------
-- Source readiness and payload matching constrain every contributor, not just one
-----------------------------------------------------------------------------------------

/-- A valid failed task settlement is structurally reachable through successful producers.
Witness: its valid source prefix and readiness, not a queue-history or cut premise.
-/
theorem ValidGraphEvents.taskFailure_reachable {work events}
    (valid : ValidGraphEvents work events) (generated : ExecutedWork work)
    {occurrence errors} (received : GraphEvent.taskFailure occurrence errors ∈ events)
    : Reachable work occurrence := by
  obtain ⟨before, _, _, validBefore, ready⟩ := valid.event_ready_context received
  obtain ⟨owners, producer, payload, known, supported⟩ := ready
  exact task_reachable_of_source_support validBefore (validBefore.successes_reachable generated)
    known supported

/-- Each atomic group report has distinct reachable unpublished contributing rejections.
Witness: the actual aggregate inventory, source readiness and successful-only publication
matching. Its summed count is retained without reducing the report to one selected cause.
This does not yet place or license their reporting or causal failure cuts.
-/
theorem createWorkQueue_runNormalized_groupFailure_accounting {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) (matching : PublicationMatching)
    (exactValues
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atFailure
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : ∃ contributions : List (Occurrence × Nat),
        contributions ≠ []
        ∧ (contributions.map Prod.fst).Nodup
        ∧ (contributions.map Prod.snd).sum = errors
        ∧ ∀ occurrence count,
            (occurrence, count) ∈ contributions
            → GraphEvent.taskFailure occurrence count ∈ batches.flatten
              ∧ (∃ owners producer path,
                  TaskAt work occurrence owners producer (.object path (.error count))
                  ∧ group.ref ∈ owners)
              ∧ Reachable work occurrence
              ∧ ¬Published matching
                  (((State.initialize (Work.fromExecution work)).runNormalized
                      batches).2.flatten.flatMap
                    publicationAtoms) occurrence := by
  obtain ⟨causes, nonempty, distinct, total, sources⟩ :=
    createWorkQueue_runNormalized_atomicGroupFailure_source generated valid
      (List.mem_of_getElem? atFailure)
  refine ⟨causes, nonempty, distinct, total, ?_⟩
  intro occurrence count member
  obtain ⟨received, owners, producer, path, known, owner⟩ := sources occurrence count member
  exact ⟨received, ⟨owners, producer, path, known, owner⟩,
    valid.taskFailure_reachable generated received,
    failedTask_unpublished_of_exactValues exactValues known rfl⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
