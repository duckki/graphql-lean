import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupSupportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureOutput

/-! Actual generated-work closures retain exact contributor descriptors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A raw group completion closes a structurally known contributor; other events are
unchecked. This concerns the closing node, not its announced children or health.
-/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.GroupClosureLocated
    (work : Execution.Work) : WorkQueueEvent → Prop
  | .groupSuccess group _ _ | .groupFailure group _ =>
      ∃ dependencies producer, NodeAt work group .group dependencies producer
  | _ => True

/-- The normalized counterpart checks successful and failed group-closing descriptors. -/
def GroupClosureLocated (work : Execution.Work) : Execution.WorkQueueEvent → Prop
  | .groupSuccess group _ _ | .groupFailure group _ =>
      ∃ dependencies producer, NodeAt work group .group dependencies producer
  | _ => True

-----------------------------------------------------------------------------------------
-- Record metadata plus contributor support recover exact closing-node provenance
-----------------------------------------------------------------------------------------

/-- A group flush closes precisely its supplied group, retaining that node's provenance.
Witness: the exact flush output has only object values followed by this group completion.
-/
theorem State.finishGroupSuccess_groupClosureLocated {work : Execution.Work}
    (queue : State) (group : GroupNode)
    (known
      : ∃ dependencies producer,
          NodeAt work group.group.node .group dependencies producer)
    : ∀ event ∈ (queue.finishGroupSuccess group).2.1, event.GroupClosureLocated work := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  intro event member
  rw [output] at member
  rcases List.mem_append.mp member with value | closure
  · split at value
    · cases value
    · have same := List.mem_singleton.mp value
      subst event
      trivial
  · have same := List.mem_singleton.mp closure
    subst event
    exact known

/-- An immediate task-failure closure has the exact descriptor of a real contributor.
Witness: the handler's closing record and actual task-owner key agree under generated
descriptor allocation. Neither output admission nor a cache-support assumption is needed.
-/
theorem State.taskFailure_groupFailure_located {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (groups : queue.GroupNodesMatchWork work)
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    {occurrence errors group count}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group count
        ∈ (queue.taskFailure occurrence errors).2)
    : ∃ dependencies producer, NodeAt work group .group dependencies producer := by
  obtain ⟨node, found, owner, _⟩ :=
    queue.taskFailure_groupFailure_current occurrence errors emitted
  have matching := tasks node.task (registered node (List.mem_of_find?_eq_some found))
  obtain ⟨dependencies, record⟩ :=
    groups.taskFailure_groupClosureRecords occurrence errors _ emitted
  exact generated.record_contributor record (matching.contributorKnown owner)

/-- Every normalized group closure in generated work has its exact structural descriptor.
Witness: raw-work replay supplies record provenance and contributor-key support separately;
the generated descriptor assignment identifies the record with that actual contributor.
This proof-only generated-work premise does not strengthen the public source contract.
-/
theorem createWorkQueue_runNormalized_groupClosuresLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
        GroupClosureLocated work event := by
  intro event member
  have record := createWorkQueue_runNormalized_groupClosureRecordsLocated valid event member
  have supported := createWorkQueue_runNormalized_groupClosureKeys valid event member
  cases event <;> try trivial
  all_goals
    obtain ⟨dependencies, record⟩ := record
    exact generated.record_contributor record supported

-----------------------------------------------------------------------------------------
-- Atomic expansion preserves exact closure descriptors without creating completions
-----------------------------------------------------------------------------------------

/-- Splitting values preserves closing-node provenance because it introduces no closures.
Witness: object/item expansion has only value atoms; control events stay unchanged.
-/
theorem GroupClosureLocated.atoms {work event} (known : GroupClosureLocated work event)
    : ∀ atom ∈ publicationAtoms event, GroupClosureLocated work atom := by
  cases event with
  | groupValues => simp [publicationAtoms, GroupClosureLocated]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms]
      | case2 => simp [publicationAtoms, streamPublicationAtoms, GroupClosureLocated]
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, GroupClosureLocated] using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simpa only [publicationAtoms, List.mem_singleton, forall_eq] using known

/-- Every actual atomic group closure has an exact contributor descriptor in generated work.
Witness: preserve normalized closure provenance through the unchanged atomic value split.
-/
theorem createWorkQueue_runNormalized_atomicGroupClosuresLocated {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms,
        GroupClosureLocated work event := by
  intro event member
  obtain ⟨carrier, emitted, within⟩ := List.mem_flatMap.mp member
  have known := createWorkQueue_runNormalized_groupClosuresLocated generated valid carrier emitted
  exact known.atoms event within

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
