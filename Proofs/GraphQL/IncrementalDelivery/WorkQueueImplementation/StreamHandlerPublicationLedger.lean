import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemPreparationLedger

/-! Cancellation-aware publication coverage through actual stream-item handlers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open WorkQueueSemantics

/-- Entry buffers are conserved at each actual item-handler drain prefix. -/
def State.StreamDrainOwners (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (published : List ObjectPublication)
    (available : List (Occurrence × Nat) := [])
    : Prop :=
  queue.rootStreams.contains stream.ref = true
  → let prepared := queue.preparedStreamItems items available
    ∀ steps,
      steps ≤ prepared.groupNodes.length
      → queue.StoredOwnersConserved
          (published.take
            ((State.drainReadyGroups.go available steps prepared).2.1.flatMap
              WorkQueueEvent.objectValues).length)
          (State.drainReadyGroups.go available steps prepared).1

/-- Earlier published memberships are absent at each actual item-handler drain prefix. -/
structure State.StreamDrainMembershipsCleared (queue : State)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (published : List ObjectPublication) (available : List (Occurrence × Nat) := [])
    : Prop where
  drain
    : queue.rootStreams.contains stream.ref = true
      → let prepared := queue.preparedStreamItems items available
        ∀ steps,
          steps ≤ prepared.groupNodes.length
          → ∀ publication ∈
              published.take
                ((State.drainReadyGroups.go available steps prepared).2.1.flatMap
                  WorkQueueEvent.objectValues).length,
              (State.drainReadyGroups.go available steps prepared).1.TaskMembershipAbsent
                publication.1

  startup
    : queue.rootStreams.contains stream.ref = true
      → let prepared := queue.preparedStreamItems items available
        prepared.DrainStartupMembershipsCleared prepared.groupNodes.length published
          available

/-- The item handler has one ledger covering successful carriers, surviving endpoint
values, streams and every owner-processing prefix. Preparation may cancel buffers; only
contributors able to carry later success or survive at the endpoint require retention.
-/
theorem State.PublicationInventory.streamItems_bufferedCoverage {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (live : queue.LiveGroupsRegistered) (registered : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered) (links : queue.StoredTaskLinks)
    (settled : queue.ChildStreamsSettled) (children : queue.ChildStreamsMatchWork work)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (allCovered
      : ∀ item ∈ items,
        ∀ task ∈ item.work.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          ∃ group ∈ item.work.groups, group.node.ref = ref)
    (memberships : queue.GroupMembershipOrder) (cancelled : queue.CancellationsRetired)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value allowed errors impossible; cases impossible)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.streamItems stream items available).2.1.flatMap
              WorkQueueEvent.objectValues
        ∧ (queue.streamItems stream items available).1.PublicationInventory property
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added
            (queue.streamItems stream items available).2.1
        ∧ StreamReleasePublications work added
            (queue.streamItems stream items available).2.1
        ∧ queue.StoredValuesConserved added (queue.streamItems stream items available).1
        ∧ BlocksFollowRegistrations (queue.streamItems stream items available).1.tasks
            added (queue.streamItems stream items available).2.1
        ∧ queue.StoredOwnersConserved added (queue.streamItems stream items available).1
        ∧ queue.StreamDrainOwners stream items added available
        ∧ queue.StreamDrainMembershipsCleared stream items added available := by
  rw [queue.streamItems_eq stream items available]
  split
  · rename_i inactive
    refine ⟨[], rfl, by simpa using inventory, .nil queue, .nil work,
      (fun _ _ _ found _ _ => Or.inr found), .nil _ _, .refl queue, ?_, ⟨?_, ?_⟩⟩
    all_goals
      intro active
      simp only [active, Bool.not_true, Bool.false_eq_true] at inactive
  · let prepared := queue.preparedStreamItems items available
    obtain ⟨ledger, linked, ready, provenance, order, cancellations, _, _, owners⟩ :=
      inventory.preparedStreamItems_ledger refs live registered started links settled children
        memberships cancelled items allCovered available clean
    obtain ⟨added, values, final, covered, conserved, streams, ordered, prefixes,
      cleared, startup⟩ :=
      ledger.drainReadyGroups_go_prefixCoverage_withStartup linked prepared.groupNodes.length
        available clean
    have coverage := covered.of_preparationOwners owners started registered cancellations
      (fun _ retired => retired.preparedStreamItems items available)
    let folded := items.foldl (fun acc item => streamItemStep acc item available)
      (queue, [], [], [], [])
    have firstCoverage : queue.BufferedClosuresCovered []
        [.streamValues stream folded.2.2.2.1 folded.2.1 folded.2.2.1] :=
      .of_noGroupSuccess (by intros; simp)
    have firstStreams : StreamReleasePublications work []
        [.streamValues stream folded.2.2.2.1 folded.2.1 folded.2.2.1] :=
      .of_noGroupSuccess (by intros; simp)
    have valueConservation := (show prepared.StoredValuesConserved added
      (prepared.drainReadyGroups available).1 from conserved).of_preparationOwners
        owners started registered cancellations
        (fun _ retired => retired.preparedStreamItems items available)
        (fun _ retired => retired.drainReadyGroups available)
    refine ⟨added, ?_, final, ?_, ?_, valueConservation, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
    · simpa only [List.flatMap_cons, WorkQueueEvent.objectValues, List.nil_append,
        State.drainReadyGroups, prepared, State.preparedStreamItems] using values
    · exact firstCoverage.append coverage rfl (fun _ _ _ found _ => Or.inr found)
    · exact firstStreams.append (streams work generated ready provenance) rfl
    · have blocks := ordered order
      change BlocksFollowRegistrations (prepared.drainReadyGroups available).1.tasks added
        (.streamValues stream folded.2.2.2.1 folded.2.1 folded.2.2.1
          :: (prepared.drainReadyGroups available).2.1)
      rw [State.drainReadyGroups_tasks prepared available]
      exact blocks.control rfl
    · have complete := owners.append (prefixes _ (Nat.le_refl _))
        (State.drainReadyGroups_go_cancelledGroups_subset _ _ available)
      intro occurrence node value found stored ref contributes present uncancelled
      exact (complete occurrence node value found stored ref contributes present uncancelled)
        |>.imp_left
        (by intro member; exact List.mem_of_mem_take (by simpa only [List.nil_append] using member))
    · intro _
      dsimp only
      intro steps bounded
      simpa only [List.nil_append] using owners.append (prefixes steps bounded)
        (State.drainReadyGroups_go_cancelledGroups_subset steps prepared available)
    · intro _
      exact cleared
    · intro _
      exact startup

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
