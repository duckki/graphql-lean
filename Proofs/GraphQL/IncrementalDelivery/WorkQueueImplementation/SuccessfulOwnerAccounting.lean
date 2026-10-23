import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StructuralRegistrationFromRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayOwnerConservation

/-! Successful source values remain published or buffered for each uncancelled owner. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each consumed task success is already published or retains its exact buffered value
and live contributor. The shared publication list labels actual object-value output. -/
def State.SuccessfulOwnersAccounted (queue : State) (work : Execution.Work)
    (before : List GraphEvent) (published : List ObjectPublication)
    : Prop :=
  ∀ occurrence result,
    GraphEvent.taskSuccess occurrence result ∈ before
    → ∀ owners producer payload,
        TaskAt work occurrence owners producer payload
        → ∀ ref ∈ owners,
            ref ∉ queue.cancelledGroups
            → (occurrence, result.value) ∈ published
              ∨ ∃ node,
                  queue.taskNode? occurrence = some node
                  ∧ node.value = some result.value
                  ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
                  ∧ ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref)

/-- An empty source history has no successful value to account for. -/
theorem State.SuccessfulOwnersAccounted.empty (queue : State) (work : Execution.Work)
    : queue.SuccessfulOwnersAccounted work [] [] := by
  intro occurrence result impossible
  cases impossible

/-- Actual handler ledger certificates preserve earlier values and account for new success.
Fresh source accounting makes every uncancelled contributor live before the storing branch;
the existing prepared-owner certificate then follows that exact value through this handler. -/
theorem State.SuccessfulOwnersAccounted.handleGraphEvent_ofDisposition
    {queue : State} {work parents before published localPublications}
    (prior : queue.SuccessfulOwnersAccounted work before published)
    (frame : UncancelledReplayFrame queue work parents before)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (covered : queue.ReplayClosuresCovered [event] localPublications available)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    : (queue.handleGraphEvent event available).1.SuccessfulOwnersAccounted work
        (before ++ [event])
        (published
          ++ localPublications.take
              ((queue.handleGraphEvent event available).2.1.flatMap
                WorkQueueEvent.objectValues).length) := by
  intro occurrence result received owners producer payload known ref contributes uncancelled
  have beforeUncancelled : ref ∉ queue.cancelledGroups :=
    fun member => uncancelled (queue.handleGraphEvent_cancelledGroups_subset event available member)
  rcases List.mem_append.mp received with earlier | current
  · rcases prior occurrence result earlier owners producer payload known ref contributes
        beforeUncancelled with emitted | ⟨node, found, stored, owns, live⟩
    · exact .inl (List.mem_append_left _ emitted)
    · have conserved :=
        covered.conservesOwners occurrence node result.value found stored ref owns live
          (by
            simpa only [State.replayGraphEvents, List.foldl_cons, List.foldl_nil,
              State.dispatchGraphEvent, State.enqueueGroupFailures]
              using uncancelled)
      rcases conserved with emitted | retained
      · apply Or.inl
        apply List.mem_append_right
        simpa only [State.rawEventReplay, List.foldl_cons, List.foldl_nil, rawEventStep,
          List.nil_append, State.dispatchGraphEvent, State.enqueueGroupFailures] using emitted
      · exact .inr ⟨node, retained.1, stored, owns, retained.2⟩
  · have same : event = .taskSuccess occurrence result := (List.mem_singleton.mp current).symm
    subst event
    obtain ⟨_, fresh, _⟩ := valid.atPrefix (List.prefix_refl _)
    have cached := frame.pending.cacheTaskFailures available
    obtain ⟨liveNode, liveLookup⟩ := frame.taskNode_of_uncancelledOwner
      (tracked occurrence result rfl) known (by
        intro settled
        exact fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.groupSettlements_subsetIdentities before settled)) contributes
      beforeUncancelled
    have cachedAccepted : (queue.cacheTaskFailures available).acceptsGraphEvent
        (.taskSuccess occurrence result) = true := by
      rw [State.cacheTaskFailures_acceptsGraphEvent]
      simp only [State.acceptsGraphEvent, liveLookup, Option.isSome_some]
    obtain ⟨node, found⟩ : ∃ node,
        (queue.cacheTaskFailures available).taskNode? occurrence = some node := by
      cases found : (queue.cacheTaskFailures available).taskNode? occurrence with
      | none => simp only [State.acceptsGraphEvent, found, Option.isSome_none,
          Bool.false_eq_true] at cachedAccepted
      | some node => exact ⟨node, rfl⟩
    have lookup := State.taskNode?_some found
    have registered := cached.started node lookup.1
    obtain ⟨_, _, _, _, descriptor⟩ := (cached.matching node.task registered).1
    have sameOwners := (TaskAt.unique (lookup.2 ▸ descriptor) known).1
    have nodeContributes := sameOwners.symm ▸ contributes
    have unsettled : node.task.occurrence ∉ GraphEvent.groupSettlements before := by
      rw [lookup.2]
      exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
        (GraphEvent.groupSettlements_subsetIdentities before member)
    have cachedUncancelled : ref ∉ (queue.cacheTaskFailures available).cancelledGroups := by
      rwa [State.cacheTaskFailures_cancelledGroups]
    obtain ⟨owner, live, sameRef, _⟩ := (frame.owners.cacheTaskFailures available)
      node.task registered unsettled ref nodeContributes cachedUncancelled
    have present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref) := by
      rw [State.cacheTaskFailures_groupNodes] at live
      exact List.mem_map.mpr ⟨owner, live, sameRef⟩
    have accounted :=
      covered.success_published_or_buffered found nodeContributes present
        (by
          simpa only [State.replayGraphEvents, List.foldl_cons, List.foldl_nil,
            State.dispatchGraphEvent, State.enqueueGroupFailures]
            using uncancelled)
    rcases accounted with emitted | retained
    · apply Or.inl
      apply List.mem_append_right
      simpa only [State.rawEventReplay, List.foldl_cons, List.foldl_nil, rawEventStep,
        List.nil_append, State.dispatchGraphEvent, State.enqueueGroupFailures] using emitted
    · exact .inr retained

/-- Live event eligibility supplies the callback evidence for successful-value accounting. -/
theorem State.SuccessfulOwnersAccounted.handleGraphEvent
    {queue : State} {work parents before published localPublications}
    (prior : queue.SuccessfulOwnersAccounted work before published)
    (frame : UncancelledReplayFrame queue work parents before)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (covered : queue.ReplayClosuresCovered [event] localPublications available)
    : (queue.handleGraphEvent event available).1.SuccessfulOwnersAccounted work
        (before ++ [event])
        (published
          ++ localPublications.take
              ((queue.handleGraphEvent event available).2.1.flatMap
                WorkQueueEvent.objectValues).length) := by
  apply prior.handleGraphEvent_ofDisposition frame event valid available covered
  intro occurrence result same
  subst event
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some node =>
      exact ⟨.inl ⟨node, found⟩, node.task,
        frame.pending.started node (List.mem_of_find?_eq_some found),
        (State.taskNode?_some found).2⟩

/-- A terminal control flag leaves the publication/buffer accounting unchanged. -/
theorem State.SuccessfulOwnersAccounted.withTerminated
    {queue : State} {work before published}
    (prior : queue.SuccessfulOwnersAccounted work before published) (terminated : Bool)
    : ({ queue with terminated } : State).SuccessfulOwnersAccounted work before
        published :=
  prior

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
