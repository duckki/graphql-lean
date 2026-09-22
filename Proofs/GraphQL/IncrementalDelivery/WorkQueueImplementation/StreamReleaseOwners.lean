import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectStreamSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting

/-! Successful stream release supplies a contributing owner, not an arbitrary ancestor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The actual flush selection identifies a supporting defer dependency
-----------------------------------------------------------------------------------------

/-- Every stream released by a live group names that group among its defer dependencies.
Witness: the flush selects a linked producer from the group's task memberships. Sound
membership and task provenance identify its owners; stream provenance identifies the
same producer, whose owners are exactly the stream dependencies.
-/
theorem State.finishGroupSuccess_streamDependency {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) {group : GroupNode}
    (live : group ∈ queue.groupNodes) {stream dependencies producer}
    (known : NodeAt work stream .stream dependencies producer)
    (released : stream ∈ (queue.finishGroupSuccess group).2.2.newStreams)
    : group.group.node.key ∈ dependencies := by
  obtain ⟨selected, _, selectedKnown, _, _, _, children⟩ :=
    queue.finishGroupSuccess_selection group
  obtain ⟨node, selectedNode, linked⟩ := children stream released
  obtain ⟨stored, member⟩ := selectedKnown node selectedNode
  have sameProducer := links.producer generated stored known linked
  obtain ⟨task, registered, sameTask, contributes⟩ :=
    sound group live node.task.occurrence member
  obtain ⟨⟨address, payload, ancestor, occurrence, structural⟩, _⟩ :=
    matching task registered
  have exactProducer : producer = some (.executionGroup address) := by
    rw [sameProducer, ← sameTask, occurrence]
  obtain ⟨parent, path, result, ownerList⟩ :=
    NodeAt.stream_objectProducer_owners (exactProducer ▸ known)
  rw [occurrence] at structural
  exact (structural.unique ownerList).1 ▸ contributes

/-- Successful release retires a contributing stream dependency without cancelling it.
Witness: derive the dependency from the actual flush selection, use registered-key
retirement, and retain the unchanged cancellation history. These are local queue facts;
no observable-history admission or stream-safety premise is used.
-/
theorem State.finishGroupSuccess_streamRetiredDependency {queue : State}
    {work : Execution.Work} (generated : ExecutedWork work)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) (registered : queue.LiveGroupsRegistered)
    {group : GroupNode} (live : group ∈ queue.groupNodes)
    (uncancelled : group.group.node.key ∉ queue.cancelledGroups)
    {stream dependencies producer}
    (known : NodeAt work stream .stream dependencies producer)
    (released : stream ∈ (queue.finishGroupSuccess group).2.2.newStreams)
    : group.group.node.key ∈ dependencies
      ∧ (queue.finishGroupSuccess group).1.RetiredGroup group.group.node.key
      ∧ group.group.node.key ∉ (queue.finishGroupSuccess group).1.cancelledGroups := by
  refine ⟨queue.finishGroupSuccess_streamDependency generated sound matching links live known
    released, queue.finishGroupSuccess_retires group (registered group live), ?_⟩
  rwa [State.finishGroupSuccess_cancelledGroups]

-----------------------------------------------------------------------------------------
-- Every successful carrier in a recursive drain retains the same dependency fact
-----------------------------------------------------------------------------------------

/-- Each group-success carrier in `events` is a defer dependency of its released streams.
This property records only structural ownership, not health, publication, or admission.
-/
def StreamReleaseDependencies (work : Execution.Work) (events : List WorkQueueEvent)
    : Prop :=
  ∀ group groups streams,
    Execution.WorkQueueEvent.groupSuccess group groups streams ∈ events
    → ∀ stream ∈ streams,
        ∀ dependencies producer,
          NodeAt work stream .stream dependencies producer → group.key ∈ dependencies

/-- Empty output has no carrier requiring a dependency witness.
Witness: the carrier membership premise is impossible. -/
theorem StreamReleaseDependencies.nil (work : Execution.Work)
    : StreamReleaseDependencies work [] := by
  intro group groups streams impossible
  cases impossible

/-- Concatenating output retains every carrier's dependency witness.
Witness: split membership into the two output segments. -/
theorem StreamReleaseDependencies.append {work left right}
    (before : StreamReleaseDependencies work left)
    (after : StreamReleaseDependencies work right)
    : StreamReleaseDependencies work (left ++ right) := by
  intro group groups streams member
  rcases List.mem_append.mp member with earlier | later
  · exact before group groups streams earlier
  · exact after group groups streams later

/-- A flush's only successful carrier releases streams supported by its own group.
Witness: its exact output is optional values followed by the one checked carrier. -/
theorem State.finishGroupSuccess_streamDependencies {queue : State}
    {work : Execution.Work} (generated : ExecutedWork work)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) {group : GroupNode}
    (live : group ∈ queue.groupNodes)
    : StreamReleaseDependencies work (queue.finishGroupSuccess group).2.1 := by
  intro trigger groups streams member
  obtain ⟨_, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [output] at member
  have same : trigger = group.group.node
      ∧ groups = (queue.finishGroupSuccess group).2.2.newGroups
      ∧ streams = (queue.finishGroupSuccess group).2.2.newStreams := by
    split at member <;> simpa using member
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro stream released dependencies producer known
  exact queue.finishGroupSuccess_streamDependency generated sound matching links live
    known released

/-- Every stream released anywhere in a recursive drain has its carrier as a dependency.
Witness: the ready lookup supplies a live group; success preserves the three structural
invariants and appends its carrier, while failed closure contributes no stream notices.
-/
theorem State.drainReadyGroups_streamDependencies {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work)
    : StreamReleaseDependencies work queue.drainReadyGroups.2 := by
  have loop (fuel : Nat) (current : State)
      (sound : current.GroupMembershipSound) (matching : current.RegisteredTasksMatch work)
      (links : current.ChildStreamsMatchWork work)
      : StreamReleaseDependencies work (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current with
    | zero => exact .nil work
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact .nil work
        · rename_i node selected
          have live : node ∈ current.groupNodes := by
            obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
            cases found : current.groupNode? key with
            | none => simp [found] at choice
            | some candidate =>
                simp only [found] at choice
                change (if candidate.failure.isSome || candidate.pending == 0 then
                  some candidate else none) = some node at choice
                split at choice
                · cases Option.some.inj choice
                  exact List.mem_of_find?_eq_some found
                · contradiction
          cases cached : node.failure with
          | none =>
              exact (current.finishGroupSuccess_streamDependencies generated sound matching
                links live).append (ih _ ((sound.finishGroupSuccess node).startNewWork _)
                  ((matching.finishGroupSuccess node).startNewWork _)
                  ((links.finishGroupSuccess node).startNewWork _))
          | some errors =>
              have noRelease : StreamReleaseDependencies work
                  [(current.finishGroupFailure node errors).2] := by
                intro group groups streams impossible
                simp [State.finishGroupFailure] at impossible
              exact noRelease.append (ih _ (sound.removeGroup _)
                (matching.removeGroup _) (links.removeGroup _))
  exact loop _ queue sound matching links

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
