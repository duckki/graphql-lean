import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionIntegration

/-! Single-pass owner processing and recursive draining share one coverage/release ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Extend all publication certificates with the same labels at each owner step
-----------------------------------------------------------------------------------------

/-- One owner step preserves both queue facts and the joint publication certificate.
Witness: counter-only updates change no stored task; a flush uses the common complete
selection for conservation, strict closure coverage, and child-stream producer labels.
-/
private theorem successGroupStep_jointCoverage {work property published}
    (generated : ExecutedWork work) (original : State)
    (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
    (refs : acc.1.GroupRefsUnique) (links : acc.1.StoredTaskLinks)
    (settled : acc.1.ChildStreamsSettled) (children : acc.1.ChildStreamsMatchWork work)
    {added : List ObjectPublication}
    (values : added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues)
    (inventory : acc.1.PublicationInventory property (published ++ added))
    (covered : original.BufferedClosuresCovered added acc.2.1)
    (conserved
      : ∀ occurrence node value,
          original.taskNode? occurrence = some node
          → node.value = some value
          → (occurrence, value) ∈ added ∨ acc.1.taskNode? occurrence = some node)
    (streams : StreamReleasePublications work added acc.2.1)
    (memberships : acc.1.GroupMembershipOrder) (same : acc.1.tasks = original.tasks)
    (ordered : BlocksFollowRegistrations original.tasks added acc.2.1)
    (owners : original.StoredOwnersConserved added acc.1)
    (cleared : ∀ publication ∈ added, acc.1.TaskMembershipAbsent publication.1)
    : let next := successGroupStep acc group
      next.1.GroupRefsUnique
      ∧ next.1.StoredTaskLinks
      ∧ next.1.ChildStreamsSettled
      ∧ next.1.ChildStreamsMatchWork work
      ∧ ∃ labels : List ObjectPublication,
          labels.map Prod.snd = next.2.1.flatMap WorkQueueEvent.objectValues
          ∧ next.1.PublicationInventory property (published ++ labels)
          ∧ original.BufferedClosuresCovered labels next.2.1
          ∧ (∀ occurrence node value,
              original.taskNode? occurrence = some node
              → node.value = some value
              → (occurrence, value) ∈ labels ∨ next.1.taskNode? occurrence = some node)
          ∧ StreamReleasePublications work labels next.2.1
          ∧ BlocksFollowRegistrations original.tasks labels next.2.1
          ∧ original.StoredOwnersConserved labels next.1
          ∧ (∀ publication ∈ labels, next.1.TaskMembershipAbsent publication.1)
          ∧ added.IsPrefix labels := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨refs, links, settled, children, added, values, inventory, covered, conserved,
      streams, ordered, owners, cleared, List.prefix_refl _⟩
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    have live := List.mem_of_find?_eq_some found
    have nextRefs := refs.putGroupNode updated
    have nextLinks := links.putGroupNodeSameTasks refs node live updated rfl rfl
    have nextSettled := settled.putGroupNode updated
    have nextChildren := children.putGroupNode updated
    have nextInventory := inventory.putGroupNode updated
    have nextCleared (publication) (member : publication ∈ added) :=
      (cleared publication member).putGroupNode updated (cleared publication member node live)
    have nextOwners : original.StoredOwnersConserved added (current.putGroupNode updated) := by
      simpa only [List.append_nil]
        using owners.append
          (current.putGroupNode_storedOwnersConserved updated) (List.Subset.refl _)
    split
    · have updatedLive : updated ∈ (current.putGroupNode updated).groupNodes := by
        apply List.mem_map.mpr
        exact ⟨node, live, by simp [updated]⟩
      obtain ⟨extra, extraValues, final, extraCoverage, extraConserved, extraStreams,
        extraOrder, extraOwners, extraCleared⟩ :=
        nextInventory.finishGroupSuccess_bufferedCoverage nextLinks updated updatedLive
      refine ⟨nextRefs.finishGroupSuccess _, nextLinks.finishGroupSuccess _,
        nextSettled.finishGroupSuccess _, nextChildren.finishGroupSuccess _, added ++ extra,
        ?_, ?_, covered.append extraCoverage values conserved, ?_,
        streams.append (extraStreams work generated nextSettled nextChildren) values, ?_, ?_,
        ?_, List.prefix_append _ _⟩
      · simp only [List.map_append, List.flatMap_append, values, extraValues]
        rfl
      · simpa only [List.append_assoc] using final
      · intro occurrence task value lookup stored
        rcases conserved occurrence task value lookup stored with earlier | retained
        · exact Or.inl (List.mem_append_left _ earlier)
        · exact (extraConserved occurrence task value retained stored).imp_left
            (List.mem_append_right _)
      · have addedOrder := extraOrder
          (memberships.putGroupNode updated (memberships node live))
        change BlocksFollowRegistrations current.tasks extra _ at addedOrder
        rw [same] at addedOrder
        exact ordered.append addedOrder
          (by simpa only [List.length_map] using congrArg List.length values)
      · exact nextOwners.append extraOwners
          (by rw [State.finishGroupSuccess_cancelledGroups]; exact List.Subset.refl _)
      · intro publication member
        exact (List.mem_append.mp member).elim
          (fun old => (nextCleared publication old).finishGroupSuccess updated)
          (extraCleared publication)
    · exact ⟨nextRefs, nextLinks, nextSettled, nextChildren,
        added, values, nextInventory, covered, conserved, streams, ordered, nextOwners,
        nextCleared, List.prefix_refl _⟩

-----------------------------------------------------------------------------------------
-- The entire single-pass contributor fold keeps its initially buffered contributions
-----------------------------------------------------------------------------------------

/-- One ledger covers every owner-fold carrier and every released stream producer.
Witness: fold the joint one-step certificate, retaining exact payload order and buffered
publish-or-retain conservation throughout the actual single-pass implementation.
-/
theorem State.PublicationInventory.successGroupFold_prefixCoverage {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (groups : List Execution.DeliveryNode)
    (memberships : queue.GroupMembershipOrder)
    : let result := groups.foldl successGroupStep (queue, [], {})
      result.1.GroupRefsUnique
      ∧ result.1.StoredTaskLinks
      ∧ result.1.ChildStreamsSettled
      ∧ result.1.ChildStreamsMatchWork work
      ∧ ∃ added : List ObjectPublication,
          added.map Prod.snd = result.2.1.flatMap WorkQueueEvent.objectValues
          ∧ result.1.PublicationInventory property (published ++ added)
          ∧ queue.BufferedClosuresCovered added result.2.1
          ∧ (∀ occurrence node value,
              queue.taskNode? occurrence = some node
              → node.value = some value
              → (occurrence, value) ∈ added ∨ result.1.taskNode? occurrence = some node)
          ∧ StreamReleasePublications work added result.2.1
          ∧ BlocksFollowRegistrations queue.tasks added result.2.1
          ∧ queue.StoredOwnersConserved added result.1
          ∧ (∀ publication ∈ added, result.1.TaskMembershipAbsent publication.1)
          ∧ (∀ steps,
              steps ≤ groups.length
              → let boundary := (groups.take steps).foldl successGroupStep (queue, [], {})
                ∀ publication ∈
                  added.take (boundary.2.1.flatMap WorkQueueEvent.objectValues).length,
                  boundary.1.TaskMembershipAbsent publication.1)
          ∧ ∀ steps,
              steps ≤ groups.length
              → let boundary := (groups.take steps).foldl successGroupStep (queue, [], {})
                queue.StoredOwnersConserved
                  (added.take (boundary.2.1.flatMap WorkQueueEvent.objectValues).length)
                  boundary.1 := by
  let invariant (acc : State × List WorkQueueEvent × NewWork)
      (added : List ObjectPublication) :=
    acc.1.GroupRefsUnique ∧ acc.1.StoredTaskLinks
    ∧ acc.1.ChildStreamsSettled ∧ acc.1.ChildStreamsMatchWork work
    ∧ added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues
        ∧ acc.1.PublicationInventory property (published ++ added)
        ∧ queue.BufferedClosuresCovered added acc.2.1
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node → node.value = some value
            → (occurrence, value) ∈ added ∨ acc.1.taskNode? occurrence = some node)
        ∧ StreamReleasePublications work added acc.2.1
        ∧ BlocksFollowRegistrations queue.tasks added acc.2.1
        ∧ queue.StoredOwnersConserved added acc.1
        ∧ ∀ publication ∈ added, acc.1.TaskMembershipAbsent publication.1
  have loop (more : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (added : List ObjectPublication) (prior : invariant acc added)
      (order : acc.1.GroupMembershipOrder) (same : acc.1.tasks = queue.tasks)
      : ∃ labels,
          invariant (more.foldl successGroupStep acc) labels
          ∧ added.IsPrefix labels
          ∧ ∀ steps, steps ≤ more.length →
              let boundary := (more.take steps).foldl successGroupStep acc
              (∀ publication ∈ labels.take
                  (boundary.2.1.flatMap WorkQueueEvent.objectValues).length,
                boundary.1.TaskMembershipAbsent publication.1)
              ∧ queue.StoredOwnersConserved
                  (labels.take (boundary.2.1.flatMap WorkQueueEvent.objectValues).length)
                  boundary.1 := by
    induction more generalizing acc added with
    | nil =>
        refine ⟨added, prior, List.prefix_refl _, ?_⟩
        intro steps bounded boundary
        have zero : steps = 0 := by simpa using bounded
        subst steps
        have size : added.length = (acc.2.1.flatMap WorkQueueEvent.objectValues).length := by
          simpa only [List.length_map] using congrArg List.length prior.2.2.2.2.1
        simpa only [boundary, List.take_zero, List.foldl_nil, ← size, List.take_length]
          using And.intro prior.2.2.2.2.2.2.2.2.2.2.2 prior.2.2.2.2.2.2.2.2.2.2.1
    | cons group rest ih =>
        obtain ⟨currentRefs, currentLinks, currentSettled, currentChildren,
          values, ledger, covered, conserved, streams, ordered, owners, cleared⟩ := prior
        obtain ⟨nextRefs, nextLinks, nextSettled, nextChildren, nextLabels,
          nextValues, nextInventory, nextCoverage, nextConserved, nextStreams, nextOrder,
          nextOwners, nextCleared, extended⟩ :=
          successGroupStep_jointCoverage generated queue acc group currentRefs
          currentLinks currentSettled currentChildren values ledger covered conserved streams
          order same ordered owners cleared
        obtain ⟨labels, final, extendsFurther, boundaries⟩ := ih _ nextLabels
          ⟨nextRefs, nextLinks, nextSettled, nextChildren, nextValues, nextInventory,
            nextCoverage, nextConserved, nextStreams, nextOrder, nextOwners, nextCleared⟩
          (successGroupStep_groupMembershipOrder acc group order)
          ((successGroupStep_tasks acc group).trans same)
        refine ⟨labels, final, extended.trans extendsFurther, ?_⟩
        intro steps bounded boundary
        cases steps with
        | zero =>
            have size : added.length = (acc.2.1.flatMap WorkQueueEvent.objectValues).length := by
              simpa only [List.length_map] using congrArg List.length values
            obtain ⟨suffix, exactLabels⟩ := extended.trans extendsFurther
            simpa only [boundary, List.take_zero, List.foldl_nil, ← size, ← exactLabels,
              List.take_left]
              using And.intro cleared owners
        | succ steps =>
            exact boundaries steps (by simpa using bounded)
  obtain ⟨added, final, _, boundaries⟩ := loop groups (queue, [], {}) []
    ⟨
      refs,
      links,
      settled,
      children,
      rfl,
      by simpa only [List.append_nil] using inventory,
      .nil queue,
      (fun _ _ _ found _ => Or.inr found),
      .nil work,
      .nil _ _,
      .refl queue,
      by simp
    ⟩ memberships rfl
  obtain ⟨finalRefs, finalLinks, finalSettled, finalChildren, values, ledger, covered,
    conserved, streams, order, owners, cleared⟩ := final
  exact ⟨finalRefs, finalLinks, finalSettled, finalChildren, added, values, ledger,
    covered, conserved, streams, order, owners, cleared,
    fun steps bound => (boundaries steps bound).1,
    fun steps bound => (boundaries steps bound).2⟩

/-- The existing owner-fold interface projects the common prefix-aware certificate.
Witness: discard only intermediate owner conservation, keeping the original labels and
every closure, stream, membership and endpoint conservation result unchanged.
-/
theorem State.PublicationInventory.successGroupFold_bufferedCoverage {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (groups : List Execution.DeliveryNode)
    (memberships : queue.GroupMembershipOrder)
    : let result := groups.foldl successGroupStep (queue, [], {})
      result.1.GroupRefsUnique
      ∧ result.1.StoredTaskLinks
      ∧ result.1.ChildStreamsSettled
      ∧ result.1.ChildStreamsMatchWork work
      ∧ ∃ added : List ObjectPublication,
          added.map Prod.snd = result.2.1.flatMap WorkQueueEvent.objectValues
          ∧ result.1.PublicationInventory property (published ++ added)
          ∧ queue.BufferedClosuresCovered added result.2.1
          ∧ (∀ occurrence node value,
              queue.taskNode? occurrence = some node
              → node.value = some value
              → (occurrence, value) ∈ added ∨ result.1.taskNode? occurrence = some node)
          ∧ StreamReleasePublications work added result.2.1
          ∧ BlocksFollowRegistrations queue.tasks added result.2.1
          ∧ queue.StoredOwnersConserved added result.1
          ∧ (∀ publication ∈ added, result.1.TaskMembershipAbsent publication.1)
          ∧ ∀ steps,
              steps ≤ groups.length
              → let boundary := (groups.take steps).foldl successGroupStep (queue, [], {})
                ∀ publication ∈
                  added.take (boundary.2.1.flatMap WorkQueueEvent.objectValues).length,
                  boundary.1.TaskMembershipAbsent publication.1 := by
  obtain ⟨finalRefs, finalLinks, finalSettled, finalChildren, added, values, ledger,
    covered, conserved, streams, order, owners, cleared, boundaries, _⟩ :=
    inventory.successGroupFold_prefixCoverage generated refs links settled children groups
      memberships
  exact ⟨finalRefs, finalLinks, finalSettled, finalChildren, added, values, ledger,
    covered, conserved, streams, order, owners, cleared, boundaries⟩

-----------------------------------------------------------------------------------------
-- Release and drain compose without changing the owner-fold publication witness
-----------------------------------------------------------------------------------------

/-- The single-pass owner fold only appends raw output events.
Witness: a skipped or counter-only owner keeps the prefix; a successful closure appends
its value/carrier block before the remaining owners are processed.
-/
theorem successGroupFold_outputPrefix (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × NewWork)
    : acc.2.1.IsPrefix (groups.foldl successGroupStep acc).2.1 := by
  induction groups generalizing acc with
  | nil => exact List.prefix_refl _
  | cons group rest ih =>
      have step : acc.2.1.IsPrefix (successGroupStep acc group).2.1 := by
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact List.prefix_refl _
        · split
          · exact List.prefix_append _ _
          · exact List.prefix_refl _
      exact step.trans (ih _)

/-- An owner-fold prefix has no more object values than the complete fold.
Witness: split the actual owner list into its processed prefix and remaining suffix.
-/
theorem successGroupFold_objectCount_take_le (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × NewWork) (steps : Nat)
    : (((groups.take steps).foldl successGroupStep acc).2.1.flatMap
        WorkQueueEvent.objectValues).length
      ≤ ((groups.foldl successGroupStep acc).2.1.flatMap
          WorkQueueEvent.objectValues).length := by
  have extended := successGroupFold_outputPrefix (groups.drop steps)
    ((groups.take steps).foldl successGroupStep acc)
  rw [← List.foldl_append, List.take_append_drop] at extended
  obtain ⟨later, same⟩ := extended
  have size := congrArg (fun events => (events.flatMap WorkQueueEvent.objectValues).length) same
  simp only [List.flatMap_append, List.length_append] at size
  omega

/-- Every internal drain prefix conserves the owner fold's initial buffered contributors.
`groups` fixes the actual single-pass owner fold. Its object count offsets each prefix
inside the one `published` ledger for that fold followed by the complete ready drain.
-/
def State.ReleaseDrainOwners (queue : State) (groups : List Execution.DeliveryNode)
    (published : List ObjectPublication)
    : Prop :=
  let released := groups.foldl successGroupStep (queue, [], {})
  let activated := released.1.startNewWork released.2.2
  ∀ steps,
    steps ≤ activated.groupNodes.length
    → queue.StoredOwnersConserved
        (published.take
          ((released.2.1 ++ (State.drainReadyGroups.go steps activated).2).flatMap
            WorkQueueEvent.objectValues).length)
        (State.drainReadyGroups.go steps activated).1

/-- Every processed-owner and drain boundary conserves the same initial buffered owners.
`published` labels the complete owner-fold/drain output; each boundary selects its exact
object-count prefix, including retirement that emits no completion for the removed ref.
-/
structure State.ReleaseOwners (queue : State) (groups : List Execution.DeliveryNode)
    (published : List ObjectPublication)
    : Prop where
  ownerFold
    : ∀ steps,
        steps ≤ groups.length
        → let boundary := (groups.take steps).foldl successGroupStep (queue, [], {})
          queue.StoredOwnersConserved
            (published.take (boundary.2.1.flatMap WorkQueueEvent.objectValues).length)
            boundary.1
  drain : queue.ReleaseDrainOwners groups published

/-- Exact prefixes of the same ledger clear memberships in both release phases.
`published` labels the whole owner-fold/drain output; raw object counts select the prefix
at each owner-fold boundary and at each subsequent drain boundary.
-/
structure State.ReleaseMembershipsCleared (queue : State)
    (groups : List Execution.DeliveryNode) (published : List ObjectPublication)
    : Prop where
  ownerFold
    : ∀ steps,
        steps ≤ groups.length
        → let boundary := (groups.take steps).foldl successGroupStep (queue, [], {})
          ∀ publication ∈
            published.take (boundary.2.1.flatMap WorkQueueEvent.objectValues).length,
            boundary.1.TaskMembershipAbsent publication.1
  drain
    : let released := groups.foldl successGroupStep (queue, [], {})
      let activated := released.1.startNewWork released.2.2
      ∀ steps,
        steps ≤ activated.groupNodes.length
        → ∀ publication ∈
            published.take
              ((released.2.1 ++ (State.drainReadyGroups.go steps activated).2).flatMap
                WorkQueueEvent.objectValues).length,
            (State.drainReadyGroups.go steps activated).1.TaskMembershipAbsent
              publication.1

/-- The complete owner-fold/release/drain phase has one common publication ledger.
Witness: combine owner-fold conservation with simultaneous mixed-drain coverage; activation
preserves each retained lookup and all stream/link invariants. The same labels justify
every successful carrier and its stream producers across both parts of the phase.
-/
theorem State.PublicationInventory.successGroupFold_drain_bufferedCoverage {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (groups : List Execution.DeliveryNode)
    (memberships : queue.GroupMembershipOrder)
    : let released := groups.foldl successGroupStep (queue, [], {})
      let drained := (released.1.startNewWork released.2.2).drainReadyGroups
      ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (released.2.1 ++ drained.2).flatMap WorkQueueEvent.objectValues
        ∧ drained.1.PublicationInventory property (published ++ added)
        ∧ queue.BufferedClosuresCovered added (released.2.1 ++ drained.2)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner, drained.1.groupNode? contributor.ref = some owner)
            → (occurrence, value) ∈ added ∨ drained.1.taskNode? occurrence = some node)
        ∧ StreamReleasePublications work added (released.2.1 ++ drained.2)
        ∧ BlocksFollowRegistrations queue.tasks added (released.2.1 ++ drained.2)
        ∧ queue.StoredOwnersConserved added drained.1
        ∧ queue.ReleaseOwners groups added
        ∧ queue.ReleaseMembershipsCleared groups added := by
  dsimp only
  let released := groups.foldl successGroupStep (queue, [], {})
  obtain ⟨_, currentLinks, currentSettled, currentChildren, first, firstValues,
    flushed, firstCoverage, firstConserved, firstStreams, firstOrder,
    firstOwners, firstCleared, foldCleared, foldOwners⟩ :=
    inventory.successGroupFold_prefixCoverage generated refs links settled children groups
      memberships
  have activated := State.PublicationInventory.mk flushed.unique flushed.provenance
    (flushed.stored.startNewWork released.2.2)
  obtain ⟨later, laterValues, final, laterCoverage, laterConserved, laterStreams, laterOrder,
    laterOwners, laterCleared⟩ :=
    activated.drainReadyGroups_go_prefixCoverage (currentLinks.startNewWork _)
      (released.1.startNewWork released.2.2).groupNodes.length
  have kept : ∀ occurrence node value,
      queue.taskNode? occurrence = some node → node.value = some value
      → (occurrence, value) ∈ first
        ∨ (released.1.startNewWork released.2.2).taskNode? occurrence = some node := by
    intro occurrence node value found stored
    exact (firstConserved occurrence node value found stored).imp_right
      (fun retained => State.startNewWork_lookup_existing retained _)
  refine ⟨first ++ later, ?_, ?_, firstCoverage.append laterCoverage firstValues kept, ?_,
    firstStreams.append (laterStreams work generated (currentSettled.startNewWork _)
      (currentChildren.startNewWork _)) firstValues, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [List.map_append, List.flatMap_append, firstValues, laterValues]
    rfl
  · simpa only [List.append_assoc, State.drainReadyGroups, released] using final
  · intro occurrence node value found stored live
    rcases kept occurrence node value found stored with earlier | retained
    · exact Or.inl (List.mem_append_left _ earlier)
    · exact (laterConserved occurrence node value retained stored live).imp_left
        (List.mem_append_right _)
  · have ordered := laterOrder ((memberships.successGroupFold groups).startNewWork _)
    rw [(State.startNewWork_groupCore _ _).2.1] at ordered
    change BlocksFollowRegistrations (groups.foldl successGroupStep (queue, [], {})).1.tasks
      later _ at ordered
    rw [successGroupFold_tasks] at ordered
    exact firstOrder.append ordered
      (by simpa only [List.length_map] using congrArg List.length firstValues)
  · have activatedOwners := firstOwners.append
      (State.startNewWork_storedOwnersConserved _ released.2.2)
      (by rw [State.startNewWork_cancelledGroups]; exact List.Subset.refl _)
    have size : later.length = ((released.1.startNewWork released.2.2).drainReadyGroups.2.flatMap
        WorkQueueEvent.objectValues).length := by
      simpa only [List.length_map, State.drainReadyGroups, released]
        using congrArg List.length laterValues
    have fullOwners := laterOwners _ (Nat.le_refl _)
    change State.StoredOwnersConserved _
      (later.take ((released.1.startNewWork released.2.2).drainReadyGroups.2.flatMap
        WorkQueueEvent.objectValues).length) _ at fullOwners
    rw [← size, List.take_length] at fullOwners
    simpa only [List.append_nil, State.drainReadyGroups, released]
      using activatedOwners.append fullOwners
        (State.drainReadyGroups_go_cancelledGroups_subset _ _)
  · intro steps bounded boundary
    have size : first.length = (released.2.1.flatMap WorkQueueEvent.objectValues).length := by
      simpa only [List.length_map] using congrArg List.length firstValues
    have count : (boundary.2.1.flatMap WorkQueueEvent.objectValues).length ≤ first.length := by
      rw [size]
      exact successGroupFold_objectCount_take_le groups (queue, [], {}) steps
    rw [List.take_append_of_le_length count]
    exact foldOwners steps bounded
  · intro steps bounded
    have activatedOwners := firstOwners.append
      (State.startNewWork_storedOwnersConserved _ released.2.2)
      (by rw [State.startNewWork_cancelledGroups]; exact List.Subset.refl _)
    have prefixOwners := activatedOwners.append (laterOwners steps bounded)
      (State.drainReadyGroups_go_cancelledGroups_subset steps _)
    have size : first.length = (released.2.1.flatMap WorkQueueEvent.objectValues).length := by
      simpa only [List.length_map] using congrArg List.length firstValues
    change queue.StoredOwnersConserved
      ((first ++ later).take ((released.2.1 ++ (State.drainReadyGroups.go steps
        (released.1.startNewWork released.2.2)).2).flatMap WorkQueueEvent.objectValues).length) _
    simpa only [List.flatMap_append, List.length_append, ← size, List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.append_nil]
      using prefixOwners
  · intro steps bounded boundary publication member
    have size : first.length = (released.2.1.flatMap WorkQueueEvent.objectValues).length := by
      simpa only [List.length_map] using congrArg List.length firstValues
    have count : (boundary.2.1.flatMap WorkQueueEvent.objectValues).length ≤ first.length := by
      rw [size]
      exact successGroupFold_objectCount_take_le groups (queue, [], {}) steps
    rw [List.take_append_of_le_length count] at member
    exact foldCleared steps bounded publication member
  · dsimp only
    intro steps bounded publication member
    have size : first.length = (released.2.1.flatMap WorkQueueEvent.objectValues).length := by
      simpa only [List.length_map] using congrArg List.length firstValues
    change publication ∈ (first ++ later).take
      ((released.2.1 ++ (State.drainReadyGroups.go steps
        (released.1.startNewWork released.2.2)).2).flatMap WorkQueueEvent.objectValues).length
      at member
    simp only [List.flatMap_append, List.length_append, ← size, List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at member
    rcases List.mem_append.mp member with old | new
    · exact ((firstCleared publication old).startNewWork released.2.2).drainReadyGroups_go steps
    · exact laterCleared steps bounded publication new

-----------------------------------------------------------------------------------------
-- Fresh task settlement supplies the prepared state used by the joint release proof
-----------------------------------------------------------------------------------------

/-- A healthy task-success handler has one coverage/release ledger after installing input.
Witness: fresh unsettled links justify the new stored node, source matching supplies child
stream provenance, and the joint owner-fold/drain theorem preserves the same labels.
Coverage includes both earlier buffered values and this input in the prepared state; the
healthy guard identifies the actual executing branch, not an added host-source law.
-/
theorem State.PublicationInventory.taskSuccess_preparedCoverage {queue : State}
    {work property published settledTasks}
    (inventory : queue.PublicationInventory property published)
    (generated : ExecutedWork work)
    (accounted : queue.PendingAccounting work settledTasks)
    (links : queue.StoredTaskLinks) (settled : queue.ChildStreamsSettled)
    (children : queue.ChildStreamsMatchWork work) (occurrence : Occurrence)
    (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (node : TaskNode) (found : queue.taskNode? occurrence = some node)
    (healthy : queue.taskHasHealthyOwner node.task = true)
    (fresh : occurrence ∉ settledTasks) (allowed : property occurrence result.value)
    (unpublished : occurrence ∉ published.map Prod.fst)
    (memberships : queue.GroupMembershipOrder)
    : let stored := queue.putTaskNode { node with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.taskSuccess occurrence result).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.taskSuccess occurrence result).1.PublicationInventory property
            (published ++ added)
        ∧ prepared.BufferedClosuresCovered added (queue.taskSuccess occurrence result).2
        ∧ (∀ task buffered value,
            prepared.taskNode? task = some buffered
            → buffered.value = some value
            → (∃ contributor ∈ buffered.task.groups,
                ∃ owner,
                  (queue.taskSuccess occurrence result).1.groupNode? contributor.ref
                  = some owner)
            → (task, value) ∈ added
              ∨ (queue.taskSuccess occurrence result).1.taskNode? task = some buffered)
        ∧ StreamReleasePublications work added (queue.taskSuccess occurrence result).2
        ∧ BlocksFollowRegistrations prepared.tasks added
            (queue.taskSuccess occurrence result).2
        ∧ prepared.StoredOwnersConserved added (queue.taskSuccess occurrence result).1
        ∧ prepared.ReleaseOwners node.task.groups added
        ∧ prepared.ReleaseMembershipsCleared node.task.groups added := by
  have known := State.taskNode?_some found
  have registered := accounted.started node known.1
  have installedLinks := links.putTaskNode { node with value := some result.value }
    (fun _ => accounted.links node.task registered (known.2.symm ▸ fresh))
  have installedStarted := accounted.started.putTaskNode
    { node with value := some result.value } registered
  have preparedLinks := installedLinks.maybeIntegrateWork accounted.refs accounted.taskGroups
    installedStarted result.work (some occurrence)
  have storedRefs : (queue.putTaskNode { node with value := some result.value }).GroupRefsUnique :=
    accounted.refs
  have preparedRefs := storedRefs.maybeIntegrateWork result.work (some occurrence)
  have installed := inventory.stored.putTaskNode { node with value := some result.value } (by
    intro value same
    cases same
    simpa only [known.2] using And.intro allowed unpublished)
  have preparedInventory := State.PublicationInventory.mk inventory.unique inventory.provenance
    (installed.maybeIntegrateWork result.work (some occurrence))
  have preparedSettled := settled.integrateSuccess found result
  have preparedChildren := (children.putTaskNode { node with value := some result.value }
    (children node known.1)).maybeIntegrateWork result.work (some occurrence) (by
      intro producer same stream member
      cases same
      exact matching.childStream_producer member)
  have joint := preparedInventory.successGroupFold_drain_bufferedCoverage generated preparedRefs
    preparedLinks preparedSettled preparedChildren node.task.groups
    (State.GroupMembershipOrder.maybeIntegrateWork
      (queue := queue.putTaskNode { node with value := some result.value }) memberships
      result.work (some occurrence))
  rw [queue.taskSuccess_eq occurrence result node found]
  simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact joint

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
