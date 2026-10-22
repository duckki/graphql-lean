import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskCatalogue
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegisteredTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTasks

/-! Queue registration never reaches a still-hidden stream-item ref region. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.RefRegions

-----------------------------------------------------------------------------------------
-- Exact permanent-task registry equations avoid repeating invariant traversals
-----------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Task regions remain inside the exposed ref inventory
-----------------------------------------------------------------------------------------

/-- Every permanent task's complete defer region is covered by the observed item regions.
This is proof evidence over existing fields; no inventory is stored by the implementation. -/
def State.RegisteredRegions (queue : State) (work : Execution.Work)
    (seen : List Occurrence)
    : Prop :=
  ∀ task ∈ queue.tasks, TaskRegionCovered work seen task

/-- A larger observed-item set preserves all task-region certificates.
Witness: exposed-ref monotonicity for each unchanged permanent task. -/
theorem State.RegisteredRegions.mono {queue : State} {work before after}
    (covered : queue.RegisteredRegions work before) (included : before.Subset after)
    : queue.RegisteredRegions work after :=
  fun task member => (covered task member).mono included

/-- Initial tasks use only the root region, not any hidden stream-item region.
Witness: the exact initialization registry and immediate-lowering coverage. -/
theorem createWorkQueue_registeredRegions (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).RegisteredRegions work [] := by
  intro task member
  rw [createWorkQueue_tasks] at member
  exact workFromSpec_tasks_regionCovered Located.root
    (fun _ contains => .inl contains) task member

/-- A matched task success introduces no new stream-item ref region.
Witness: its started parent task already covers the whole defer region, including the
new child work. The permanent registry append equation handles old and new tasks. -/
theorem State.RegisteredRegions.taskSuccess {queue : State} {work seen occurrence result}
    (covered : queue.RegisteredRegions work seen)
    (started : queue.StartedTasksRegistered)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.RegisteredRegions work seen := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using covered
  | some node =>
      have registered := started node (List.mem_of_find?_eq_some found)
      have same : node.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : TaskNode =>
          candidate.task.occurrence == occurrence) found)
      obtain ⟨owners, producer, known, _, childrenWork⟩ := matching
      cases occurrence with
      | item => cases childrenWork
      | executionGroup address =>
          obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
          change locateWork work address = some
            ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
          have lowering : result.work = Work.fromExecution children (address ++ [0]) := by
            simpa [taskChildWork?_eq_lookup, located] using childrenWork.symm
          have childCovered : ∀ ref ∈ rootRefs children, ExposedRef work seen ref := by
            intro ref member
            exact covered node.task registered address _ same located ref
              (List.mem_append_right _ member)
          intro task member
          rw [State.taskSuccess_tasks found available] at member
          rcases List.mem_append.mp member with old | new
          · exact covered task old
          · rw [lowering] at new
            exact workFromSpec_tasks_regionCovered (Located.executionGroup located)
              childCovered task new

/-- Task failure cannot expose a new ref region.
Witness: the permanent registry is unchanged by failure cleanup. -/
theorem State.RegisteredRegions.taskFailure {queue : State} {work seen}
    (covered : queue.RegisteredRegions work seen) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.RegisteredRegions work seen := by
  intro task member
  rw [State.taskFailure_tasks] at member
  exact covered task member

/-- Recursive release cannot expose a hidden item region.
Witness: region coverage depends only on the unchanged permanent task registry.
-/
theorem State.RegisteredRegions.drainReadyGroups {queue : State} {work seen}
    (covered : queue.RegisteredRegions work seen)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.RegisteredRegions work seen := by
  intro task member
  rw [State.drainReadyGroups_tasks _ available] at member
  exact covered task member

/-- Integrating one matched stream item exposes its region and no other region.
Witness: the matched lowering's located region supplies every newly registered task. -/
theorem State.RegisteredRegions.integrateStreamItem {queue : State}
    {work seen stream items} (covered : queue.RegisteredRegions work seen)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).RegisteredRegions work
        (item.occurrence :: seen) := by
  obtain ⟨children, address, producer, owners, located, lowering, region⟩ :=
    matching.streamItem_region member
  intro task registered
  rw [State.integrateStreamItem_tasks _ _ available] at registered
  rcases List.mem_append.mp registered with old | new
  · exact (covered task old).mono (by intro occurrence recorded; exact .tail _ recorded)
  · rw [lowering] at new
    exact workFromSpec_tasks_regionCovered located
      (fun ref contains => .inr ⟨item.occurrence, List.mem_cons_self, _, region, contains⟩)
      task new

/-- A stream batch exposes only the regions of its supplied items.
Witness: fold one-item coverage; every intermediate certificate can be weakened to the
whole batch's observed-item set without asserting earlier registration availability. -/
theorem State.RegisteredRegions.streamItems {queue : State} {work seen stream items}
    (covered : queue.RegisteredRegions work seen)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.RegisteredRegions work
        (seen ++ items.map StreamItem.occurrence) := by
  let after := seen ++ items.map StreamItem.occurrence
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) :=
      pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (prior : acc.1.RegisteredRegions work after)
      : (more.foldl step acc).1.RegisteredRegions work after := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        have member := included List.mem_cons_self
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) (step acc item)
        apply (prior.integrateStreamItem matching member available).mono
        intro occurrence recorded
        rcases List.mem_cons.mp recorded with same | old
        · exact List.mem_append_right _ (same ▸ List.mem_map_of_mem member)
        · exact old
  have initial : queue.RegisteredRegions work after :=
    covered.mono (List.subset_append_left seen _)
  unfold State.streamItems
  split
  · exact initial
  · exact (loop items (fun _ member => member)
      (queue, [], [], [], []) initial).drainReadyGroups available

/-- Matching events preserve region coverage using exactly their supplied identities.
Witness: task/closure handlers expose no new region; stream batches add their item regions.
-/
theorem State.RegisteredRegions.handleGraphEvent {queue : State} {work seen}
    (covered : queue.RegisteredRegions work seen) (started : queue.StartedTasksRegistered)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.RegisteredRegions work
        (seen ++ event.identities.1) := by
  have cached : (queue.cacheTaskFailures available).RegisteredRegions work seen := by
    intro task member
    rw [State.cacheTaskFailures_tasks] at member
    exact covered task member
  have registered := started.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      exact (cached.taskSuccess registered matching available).mono (List.subset_append_left _ _)
  | taskFailure occurrence errors =>
      exact (cached.taskFailure occurrence errors).mono (List.subset_append_left _ _)
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.RegisteredRegions _ _
      unfold State.groupFailure
      split
      · exact cached.mono (List.subset_append_left _ _)
      · split <;> exact cached.mono (List.subset_append_left _ _)
  | streamItems stream items => exact cached.streamItems matching available
  | streamSuccess stream =>
      change ((queue.cacheTaskFailures available).streamSuccess stream).1.RegisteredRegions
        work (seen ++ [])
      unfold State.streamSuccess
      split <;> exact cached.mono (List.subset_append_left _ _)
  | streamFailure stream errors =>
      change ((queue.cacheTaskFailures available).streamFailure stream errors).1.RegisteredRegions
        work (seen ++ [])
      unfold State.streamFailure
      split <;> exact cached.mono (List.subset_append_left _ _)

-----------------------------------------------------------------------------------------
-- Permanent registration refs remain in exposed source regions
-----------------------------------------------------------------------------------------

/-- Every registered ref belongs to an already exposed root or stream-item region. -/
abbrev State.RegisteredRefsCovered (queue : State) (work : Execution.Work)
    (seen : List Occurrence)
    : Prop :=
  queue.RegistrationsSatisfy (ExposedRef work seen)

/-- Recording more source identities retains every registration's exposed region. -/
theorem State.RegisteredRefsCovered.mono {queue : State} {work before after}
    (covered : queue.RegisteredRefsCovered work before) (included : before.Subset after)
    : queue.RegisteredRefsCovered work after :=
  State.RegistrationsSatisfy.mono covered (fun _ known => known.mono included)

/-- Initial candidate refs, including empty declarations, lie in the root region. -/
theorem createWorkQueue_registeredRefsCovered (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).RegisteredRefsCovered work [] := by
  have empty : ({} : State).RegisteredRefsCovered work [] := by
    intro ref member; cases member
  exact ((empty.maybeIntegrateWork (Work.fromExecution work)
    (fun _ member => .inl (workFromSpec_group_rootRef work [] member))).pruneEmptyGroups
      _).startNewWork _

/-- A successful task registers only refs in its permanent task's covered defer region. -/
theorem State.RegisteredRefsCovered.taskSuccess {queue : State}
    {work seen occurrence result} (covered : queue.RegisteredRefsCovered work seen)
    (regions : queue.RegisteredRegions work seen) (started : queue.StartedTasksRegistered)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.RegisteredRefsCovered work
        seen := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using covered
  | some node =>
      have registered := started node (List.mem_of_find?_eq_some found)
      have same : node.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : TaskNode =>
          candidate.task.occurrence == occurrence) found)
      apply State.RegistrationsSatisfy.taskSuccess covered occurrence result ?_ available
      obtain ⟨owners, producer, known, _, childrenWork⟩ := matching
      cases occurrence with
      | item => cases childrenWork
      | executionGroup address =>
          obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
          change locateWork work address = some
            ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
          have lowering : result.work = Work.fromExecution children (address ++ [0]) := by
            simpa [taskChildWork?_eq_lookup, located] using childrenWork.symm
          intro group member
          rw [lowering] at member
          exact regions node.task registered address _ same located group.node.ref
            (List.mem_append_right _ (workFromSpec_group_rootRef children _ member))

/-- One matched item registers refs only in its newly exposed finite region. -/
theorem State.RegisteredRefsCovered.integrateStreamItem {queue : State}
    {work seen stream items} (covered : queue.RegisteredRefsCovered work seen)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).RegisteredRefsCovered work
        (item.occurrence :: seen) := by
  obtain ⟨children, address, producer, owners, located, lowering, region⟩ :=
    matching.streamItem_region member
  have prior : queue.RegisteredRefsCovered work (item.occurrence :: seen) :=
    covered.mono (by intro occurrence included; exact .tail _ included)
  unfold State.integrateStreamItem
  apply State.RegistrationsSatisfy.startNewWork
  apply State.RegistrationsSatisfy.pruneEmptyGroups
  apply State.RegistrationsSatisfy.maybeIntegrateWork prior
  intro group included
  rw [lowering] at included
  exact .inr ⟨item.occurrence, List.mem_cons_self, _, region,
    workFromSpec_group_rootRef children address included⟩

/-- A stream batch exposes only the regions of its supplied items.
Witness: fold one-item coverage; every intermediate certificate can be weakened to the
whole batch's observed-item set without asserting earlier registration availability. -/
theorem State.RegisteredRefsCovered.streamItems {queue : State} {work seen stream items}
    (covered : queue.RegisteredRefsCovered work seen)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.RegisteredRefsCovered work
        (seen ++ items.map StreamItem.occurrence) := by
  let after := seen ++ items.map StreamItem.occurrence
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) :=
      pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (prior : acc.1.RegisteredRefsCovered work after)
      : (more.foldl step acc).1.RegisteredRefsCovered work after := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        have member := included List.mem_cons_self
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) (step acc item)
        apply (prior.integrateStreamItem matching member available).mono
        intro occurrence recorded
        rcases List.mem_cons.mp recorded with same | old
        · exact List.mem_append_right _ (same ▸ List.mem_map_of_mem member)
        · exact old
  have initial : queue.RegisteredRefsCovered work after :=
    covered.mono (List.subset_append_left seen _)
  unfold State.streamItems
  split
  · exact initial
  · exact (loop items (fun _ member => member)
      (queue, [], [], [], []) initial).drainReadyGroups available

/-- A matching dispatch registers refs only in the enlarged source prefix. -/
theorem State.RegisteredRefsCovered.handleGraphEvent {queue : State} {work seen}
    (covered : queue.RegisteredRefsCovered work seen)
    (regions : queue.RegisteredRegions work seen) (started : queue.StartedTasksRegistered)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.RegisteredRefsCovered work
        (seen ++ event.identities.1) := by
  have cached := State.RegistrationsSatisfy.cacheTaskFailures covered available
  have taskRegions : (queue.cacheTaskFailures available).RegisteredRegions work seen := by
    intro task member
    rw [State.cacheTaskFailures_tasks] at member
    exact regions task member
  have registered := started.cacheTaskFailures available
  have prior : (queue.cacheTaskFailures available).RegisteredRefsCovered work
      (seen ++ event.identities.1) :=
    State.RegisteredRefsCovered.mono cached (List.subset_append_left _ _)
  cases event with
  | taskSuccess occurrence result =>
      exact (State.RegisteredRefsCovered.taskSuccess cached taskRegions registered matching
        available).mono (List.subset_append_left _ _)
  | taskFailure occurrence errors => exact prior.taskFailure occurrence errors
  | streamItems stream items =>
      exact State.RegisteredRefsCovered.streamItems cached matching available
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.RegisteredRefsCovered _ _
      unfold State.groupFailure
      split
      · exact prior
      · split <;> exact prior
  | streamSuccess stream =>
      change ((queue.cacheTaskFailures available).streamSuccess stream).1.RegisteredRefsCovered _ _
      unfold State.streamSuccess
      split <;> exact prior
  | streamFailure stream errors =>
      change ((queue.cacheTaskFailures available).streamFailure stream errors).1.RegisteredRefsCovered _ _
      unfold State.streamFailure
      split <;> exact prior

-----------------------------------------------------------------------------------------
-- Registered refs inherit their permanent tasks' exposed-region certificates
-----------------------------------------------------------------------------------------

/-- Proof-only region inventory over the queue's permanent task and group registries.
The observed identities may include task settlements; only stream items expose regions. -/
structure State.RegionInventory (queue : State) (work : Execution.Work)
    (seen : List Occurrence)
    : Prop where
  regions : queue.RegisteredRegions work seen
  matching : queue.RegisteredTasksMatch work
  registrations : queue.RegisteredRefsCovered work seen
  started : queue.StartedTasksRegistered

/-- Every permanent registration has already been exposed by the source history. -/
theorem State.RegionInventory.registered_exposed {queue : State} {work seen}
    (inventory : queue.RegionInventory work seen) {ref : NodeRef}
    (registered : ref ∈ queue.registeredGroups)
    : ExposedRef work seen ref :=
  inventory.registrations ref registered

/-- One matched item updates the inventory at its actual integration boundary.
Witness: region coverage and the existing task-provenance/registry preservation lemmas. -/
theorem State.RegionInventory.integrateStreamItem {queue : State} {work seen stream items}
    (inventory : queue.RegionInventory work seen)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).RegionInventory work
        (item.occurrence :: seen) := by
  have childTasks : ∀ task ∈ item.work.tasks, TaskMatches work task := by
    intro task taskMember
    obtain ⟨address, payload, same, known⟩ :=
      matching.streamItem_childTask_producer member taskMember
    exact ⟨⟨address, payload, _, same, known⟩,
      matching.streamItem_childTask_groupsExact member taskMember⟩
  exact ⟨
    inventory.regions.integrateStreamItem matching member available,
    ((inventory.matching.maybeIntegrateWork item.work childTasks).pruneEmptyGroups
      _).startNewWork
      _ available,
    inventory.registrations.integrateStreamItem matching member available,
    ((inventory.started.maybeIntegrateWork item.work none).pruneEmptyGroups
      _).startNewWork
      _ available
  ⟩

/-- Initial registration cannot use any stream item's hidden region.
Witness: root-only task-region coverage and the existing initial registry invariants. -/
theorem createWorkQueue_regionInventory (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).RegionInventory work [] :=
  ⟨
    createWorkQueue_registeredRegions work,
    createWorkQueue_fromSpec_registeredTasksMatch work,
    createWorkQueue_registeredRefsCovered work,
    createWorkQueue_startedTasksRegistered _
  ⟩

/-- Every matching graph event preserves the inventory for the enlarged identity prefix.
Witness: region coverage plus unchanged provenance, registration, and start invariants. -/
theorem State.RegionInventory.handleGraphEvent {queue : State} {work seen}
    (inventory : queue.RegionInventory work seen)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.RegionInventory work
        (seen ++ event.identities.1) :=
  ⟨
    inventory.regions.handleGraphEvent inventory.started event matching available,
    inventory.matching.handleGraphEvent event matching available,
    inventory.registrations.handleGraphEvent inventory.regions inventory.started event
      matching available,
    inventory.started.handleGraphEvent event available
  ⟩

/-- Realizing FIFO enqueue effects preserves the permanent region inventory. -/
theorem State.RegionInventory.dispatchGraphEvent {queue : State} {work seen}
    (inventory : queue.RegionInventory work seen)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.RegionInventory work
        (seen ++ event.identities.1) := by
  have next := inventory.handleGraphEvent event matching available
  exact ⟨next.regions, next.matching, next.registrations, next.started⟩

/-- A larger observed region inventory retains all existing certificates. -/
theorem State.RegionInventory.mono {queue : State} {work before after}
    (prior : queue.RegionInventory work before) (included : before.Subset after)
    : queue.RegionInventory work after :=
  ⟨
    prior.regions.mono included,
    prior.matching,
    prior.registrations.mono included,
    prior.started
  ⟩

/-- Cache exposure leaves the permanent region inventory unchanged. -/
theorem State.RegionInventory.cacheTaskFailures {queue : State} {work seen}
    (prior : queue.RegionInventory work seen) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).RegionInventory work seen := by
  refine ⟨?_, prior.matching.cacheTaskFailures available,
    prior.registrations.cacheTaskFailures available, prior.started.cacheTaskFailures available⟩
  intro task member
  rw [State.cacheTaskFailures_tasks] at member
  exact prior.regions task member

/-- The batch-control flag does not affect registration or source-region evidence. -/
theorem State.RegionInventory.withTerminated {queue : State} {work seen}
    (prior : queue.RegionInventory work seen) (terminated : Bool)
    : ({queue with terminated := terminated}).RegionInventory work seen :=
  ⟨prior.regions, prior.matching, prior.registrations, prior.started⟩

/-- A fixed-snapshot event fold exposes only the supplied source identities. -/
theorem State.RegionInventory.replayGraphEvents {queue : State} {work seen}
    (prior : queue.RegionInventory work seen) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).RegionInventory work
        (seen ++ events.flatMap (fun event => event.identities.1)) := by
  induction events generalizing queue seen with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have next := prior.dispatchGraphEvent event (matching event List.mem_cons_self) available
      have result := ih next
        (fun next member => matching next (List.mem_cons_of_mem _ member))
      simpa only [State.replayGraphEvents, List.foldl_cons, List.flatMap_cons,
        List.append_assoc] using result

/-- Complete host batches preserve region provenance even after termination. -/
theorem State.RegionInventory.handleGraphEvents {queue : State} {work seen}
    (prior : queue.RegionInventory work seen) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.RegionInventory work
        (seen ++ events.flatMap (fun event => event.identities.1)) := by
  cases running : queue.terminated with
  | true =>
      simpa only [State.handleGraphEvents, running, ↓reduceIte]
        using prior.mono (List.subset_append_left _ _)
  | false =>
      have replayed := prior.replayGraphEvents events matching (GraphEvent.availableFailures events)
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact replayed.withTerminated terminal

/-- Region provenance follows actual batches without selecting a flattened cache history. -/
theorem State.RegionInventory.runNormalized {queue : State} {work seen}
    (prior : queue.RegionInventory work seen) (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    : (queue.runNormalized batches).1.RegionInventory work
        (seen ++ batches.flatten.flatMap (fun event => event.identities.1)) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue seen with
  | nil => simpa [State.replayBatches] using prior
  | cons batch rest ih =>
      have next := prior.handleGraphEvents batch (matching batch List.mem_cons_self)
      have result := ih next (fun next member => matching next (List.mem_cons_of_mem _ member))
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.flatMap_append, List.append_assoc] using result

/-- Every registered region at the actual normalized endpoint has an observed source. -/
theorem createWorkQueue_runNormalized_regionInventory {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RegionInventory
        work (batches.flatten.flatMap (fun event => event.identities.1)) :=
  (createWorkQueue_regionInventory work).runNormalized batches
    (fun _ batchMember _ eventMember =>
      valid.eachMatches (List.mem_flatten.mpr ⟨_, batchMember, eventMember⟩))

/-- Arbitrary matching source replay registers only already-exposed ref regions.
Witness: induction through the actual event handlers, including both failures and
successful releases. Neither pending ledgers nor registration availability is assumed. -/
theorem createWorkQueue_replay_regionInventory {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (available : List (Occurrence × Nat) := [])
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events available).RegionInventory
        work (events.flatMap (fun event => event.identities.1)) := by
  induction valid with
  | nil => exact createWorkQueue_regionInventory work
  | @append before event validBefore matching fresh ready ih =>
      rw [State.replayGraphEvents_append _ _ _ available, List.flatMap_append,
        List.flatMap_singleton]
      simpa only [State.replayGraphEvents, List.foldl_cons, List.foldl_nil]
        using ih.dispatchGraphEvent event matching available

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
