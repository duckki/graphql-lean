import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureContributions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupStartup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskMemberships

/-! Aggregate startup reports retain distinct exact contributing source failures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A group report sums distinct contributing task rejections from the supplied source.
The occurrence labels are proof evidence for the local startup collection, not group state.
-/
def GroupFailureSources (work : Execution.Work) (inputs : List GraphEvent)
    (ref : NodeRef) (errors : Nat)
    : Prop :=
  ∃ causes : List (Occurrence × Nat),
    causes ≠ []
    ∧ (causes.map Prod.fst).Nodup
    ∧ (causes.map Prod.snd).sum = errors
    ∧ ∀ occurrence count,
        (occurrence, count) ∈ causes
        → GraphEvent.taskFailure occurrence count ∈ inputs
          ∧ ∃ owners producer path,
              TaskAt work occurrence owners producer (.object path (.error count))
              ∧ ref ∈ owners

/-- Extending source history preserves the same distinct aggregate cause inventory. -/
theorem GroupFailureSources.weaken {work before after ref errors}
    (sources : GroupFailureSources work before ref errors)
    (included : before.Subset after)
    : GroupFailureSources work after ref errors := by
  obtain ⟨causes, nonempty, unique, total, known⟩ := sources
  exact ⟨causes, nonempty, unique, total, fun occurrence count member =>
    ⟨included (known occurrence count member).1, (known occurrence count member).2⟩⟩

/-- One immediate source cause is a singleton instance of aggregate group reporting. -/
theorem GroupFailureSourceCause.sources {work inputs ref errors}
    (cause : GroupFailureSourceCause work inputs ref errors)
    : GroupFailureSources work inputs ref errors := by
  obtain ⟨occurrence, member, known⟩ := cause
  refine ⟨[(occurrence, errors)], by simp, by simp, by simp, ?_⟩
  intro task count selected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp selected)
  exact ⟨member, known⟩

/-- A startup aggregate contains exact source failures of distinct member tasks.
Witness: the existing local error collection supplies occurrence labels and distinctness;
sound registered memberships identify each task's contribution to this group.
-/
theorem State.startGroup_failure_sources {queue : State} {work inputs}
    (prior
      : queue.TaskRejectionsSatisfy
          (fun occurrence errors =>
            GraphEvent.taskFailure occurrence errors ∈ inputs))
    (unique : queue.TaskMembershipsUnique) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (sources : ∀ event ∈ inputs, event.MatchesWork work) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    {failure : GroupFailureEvent}
    (reported : failure ∈ (queue.startGroup ref available).2)
    : GroupFailureSources work inputs failure.group.ref failure.errors := by
  obtain ⟨node, live, same, causes, nonempty, members, distinct, total, rejected⟩ :=
    queue.startGroup_failure_causes prior unique ref available licensed reported
  refine ⟨causes, nonempty, distinct, total.symm, ?_⟩
  intro occurrence count member
  have received := rejected (occurrence, count) member
  have listed : occurrence ∈ node.tasks :=
    members.subset (List.mem_map.mpr ⟨(occurrence, count), member, rfl⟩)
  obtain ⟨task, registered, identity, owner⟩ := sound node live occurrence listed
  obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ := matching task registered
  rw [identity] at known
  obtain ⟨owners, birth, path, failed⟩ := sources _ received
  have contributes := (known.unique failed).1 ▸ owner
  rw [same]
  exact ⟨received, owners, birth, path, failed, contributes⟩

/-- Released groups report only distinct exact source failures under the batch snapshot.
Witness: thread rejection provenance and sound memberships through the real group-start
fold. Each failed startup removes its group before the next startup is inspected.
-/
theorem State.startNewWork_failure_sources {queue : State} {work inputs}
    (prior
      : queue.TaskRejectionsSatisfy
          (fun occurrence errors =>
            GraphEvent.taskFailure occurrence errors ∈ inputs))
    (unique : queue.TaskMembershipsUnique) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (released : NewWork) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : ∀ failure ∈ (queue.startNewWork released available).2,
        GroupFailureSources work inputs failure.group.ref failure.errors := by
  let invariant (current : State) :=
    current.TaskRejectionsSatisfy (fun occurrence errors =>
      GraphEvent.taskFailure occurrence errors ∈ inputs)
    ∧ current.TaskMembershipsUnique ∧ current.GroupMembershipSound
    ∧ current.RegisteredTasksMatch work
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let next := acc.1.startGroup ref available
    (next.1, acc.2 ++ next.2)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (frame : invariant acc.1)
      (reported : ∀ failure ∈ acc.2,
        GroupFailureSources work inputs failure.group.ref failure.errors)
      : ∀ failure ∈ (refs.foldl step acc).2,
          GroupFailureSources work inputs failure.group.ref failure.errors := by
    induction refs generalizing acc with
    | nil => exact reported
    | cons ref rest ih =>
        apply ih (acc := step acc ref)
        · exact ⟨frame.1.startGroup ref available licensed,
            (fun node member => frame.2.1 node
              ((acc.1.startGroup_groupNodes_sublist ref available).subset member)),
            frame.2.2.1.startGroup ref available,
            frame.2.2.2.startGroup ref available⟩
        · intro failure member
          rcases List.mem_append.mp member with old | new
          · exact reported failure old
          · exact acc.1.startGroup_failure_sources frame.1 frame.2.1 frame.2.2.1
              frame.2.2.2 sources ref available licensed new
  exact loop (released.newGroups.map Execution.DeliveryNode.ref)
    (
      {
        queue with
          rootGroups :=
            queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref
      },
      []
    )
    ⟨prior, unique, sound, matching⟩ (by simp)

/-- Recursive successful draining retains the sources of every queued startup failure.
Witness: each successful closure preserves rejection provenance and memberships; the next
startup supplies its own aggregate before recursion follows the resulting actual state.
-/
theorem State.drainReadyGroups_go_failure_sources {queue : State} {work inputs}
    (prior
      : queue.TaskRejectionsSatisfy
          (fun occurrence errors =>
            GraphEvent.taskFailure occurrence errors ∈ inputs))
    (unique : queue.TaskMembershipsUnique) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (sources : ∀ event ∈ inputs, event.MatchesWork work)
    (fuel : Nat) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → GraphEvent.taskFailure occurrence errors ∈ inputs)
    : ∀ failure ∈ (State.drainReadyGroups.go available fuel queue).2.2,
        GroupFailureSources work inputs failure.group.ref failure.errors := by
  induction fuel generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simp
      · rename_i node selected
        let closed := queue.finishGroupSuccess node
        have rejected := prior.finishGroupSuccess node
        have distinct := unique.finishGroupSuccess node
        have members := sound.finishGroupSuccess node
        have tasks := matching.finishGroupSuccess node
        have first := closed.1.startNewWork_failure_sources rejected distinct members tasks
          sources closed.2.2 available licensed
        have later := ih (rejected.startNewWork closed.2.2 available licensed)
          (distinct.startNewWork closed.2.2 available)
          (members.startNewWork closed.2.2 available)
          (tasks.startNewWork closed.2.2 available)
        intro failure member
        exact (List.mem_append.mp member).elim (first failure) (later failure)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
