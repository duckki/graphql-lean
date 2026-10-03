import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerAccounting

/-! Queue registration never reaches a still-hidden stream-item ref region. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.RefRegions

-----------------------------------------------------------------------------------------
-- Exact permanent-task registry equations avoid repeating invariant traversals
-----------------------------------------------------------------------------------------

/-- Recursive release preserves the permanent task registry.
Witness: each successful flush, activation, and cached-failure removal leaves it unchanged.
-/
theorem State.drainReadyGroups_tasks (queue : State)
    : queue.drainReadyGroups.1.tasks = queue.tasks := by
  apply State.drainReadyGroups_preserves (fun current => current.tasks = queue.tasks)
  · intro current node prior _ _ _ _
    rw [(State.startNewWork_groupCore _ _).2.1, State.finishGroupSuccess_tasks, prior]
  · intro current node errors prior _ _ _
    exact prior
  · rfl

/-- A contributor step changes pending/live bookkeeping but not registered tasks.
Witness: ref-preserving updates and the successful-cleanup registry equation. -/
theorem successGroupStep_tasks (acc : State × List WorkQueueEvent × NewWork)
    (group : Execution.DeliveryNode)
    : (successGroupStep acc group).1.tasks = acc.1.tasks := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · rfl
  · split
    · exact State.finishGroupSuccess_tasks _ _
    · rfl

/-- An eligible successful task appends exactly the supplied child tasks.
Witness: the accepting guard selects integration; release preserves the appended registry.
-/
theorem State.taskSuccess_tasks {queue : State} {occurrence result node}
    (found : queue.taskNode? occurrence = some node)
    (eligible : queue.taskHasHealthyOwner node.task = true)
    : (queue.taskSuccess occurrence result).1.tasks
      = queue.tasks ++ result.work.tasks := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      : (groups.foldl successGroupStep acc).1.tasks = acc.1.tasks := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih, successGroupStep_tasks]
  rw [queue.taskSuccess_eq occurrence result node found]
  simp only [eligible, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [State.drainReadyGroups_tasks, (State.startNewWork_groupCore _ _).2.1, loop,
    State.maybeIntegrateWork_tasks_append]
  rfl

/-- Task failure retains permanent registrations even when removing live descendants.
Witness: every owner-handler branch leaves the task registry unchanged. -/
theorem State.taskFailure_tasks (queue : State) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.tasks = queue.tasks := by
  let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
    match acc.1.groupNode? group.ref with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains group.ref then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      : (groups.foldl step acc).1.tasks = acc.1.tasks := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih]
        unfold step
        split
        · rfl
        · split <;> rfl
  unfold State.taskFailure
  split
  · rfl
  · split
    · rfl
    · exact loop _ _

/-- One stream-item integration appends exactly its immediate child tasks.
Witness: pruning and activation preserve the integration append equation. -/
theorem State.integrateStreamItem_tasks (queue : State) (item : StreamItem)
    : (queue.integrateStreamItem item).tasks = queue.tasks ++ item.work.tasks := by
  unfold State.integrateStreamItem
  rw [(State.startNewWork_groupCore _ _).2.1, State.pruneEmptyGroups_tasks,
    State.maybeIntegrateWork_tasks_append]

/-- Initialization registers exactly the immediate input tasks.
Witness: empty-queue integration, followed by registry-preserving pruning and activation. -/
theorem createWorkQueue_tasks (work : Work)
    : (State.initialize work).tasks = work.tasks := by
  unfold State.initialize
  dsimp only
  rw [(State.startNewWork_groupCore _ _).2.1, State.pruneEmptyGroups_tasks,
    State.maybeIntegrateWork_tasks_append]
  rfl

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
    : (queue.taskSuccess occurrence result).1.RegisteredRegions work seen := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using covered
  | some node =>
      cases eligible : queue.taskHasHealthyOwner node.task with
      | false =>
          rw [State.taskSuccess_of_noHealthyOwner found eligible result]
          exact covered
      | true =>
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
                simpa [taskChildWork?, located] using childrenWork.symm
              have childCovered : ∀ ref ∈ rootRefs children, ExposedRef work seen ref := by
                intro ref member
                exact covered node.task registered address _ same located ref
                  (List.mem_append_right _ member)
              intro task member
              rw [State.taskSuccess_tasks found eligible] at member
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
    : queue.drainReadyGroups.1.RegisteredRegions work seen := by
  intro task member
  rw [State.drainReadyGroups_tasks] at member
  exact covered task member

/-- Integrating one matched stream item exposes its region and no other region.
Witness: the matched lowering's located region supplies every newly registered task. -/
theorem State.RegisteredRegions.integrateStreamItem {queue : State}
    {work seen stream items} (covered : queue.RegisteredRegions work seen)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : (queue.integrateStreamItem item).RegisteredRegions work
        (item.occurrence :: seen) := by
  obtain ⟨children, address, producer, owners, located, lowering, region⟩ :=
    matching.streamItem_region member
  intro task registered
  rw [State.integrateStreamItem_tasks] at registered
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
    : (queue.streamItems stream items).1.RegisteredRegions work
        (seen ++ items.map StreamItem.occurrence) := by
  let after := seen ++ items.map StreamItem.occurrence
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.RegisteredRegions work after)
      : (more.foldl step acc).1.RegisteredRegions work after := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        have member := included List.mem_cons_self
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) (step acc item)
        apply (prior.integrateStreamItem matching member).mono
        intro occurrence recorded
        rcases List.mem_cons.mp recorded with same | old
        · exact List.mem_append_right _ (same ▸ List.mem_map_of_mem member)
        · exact old
  have initial : queue.RegisteredRegions work after :=
    covered.mono (List.subset_append_left seen _)
  unfold State.streamItems
  split
  · exact initial
  · exact (loop items (fun _ member => member) (queue, [], [], []) initial).drainReadyGroups

/-- Matching events preserve region coverage using exactly their supplied identities.
Witness: task/closure handlers expose no new region; stream batches add their item regions.
-/
theorem State.RegisteredRegions.handleGraphEvent {queue : State} {work seen}
    (covered : queue.RegisteredRegions work seen) (started : queue.StartedTasksRegistered)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.RegisteredRegions work
        (seen ++ event.identities.1) := by
  cases event with
  | taskSuccess occurrence result =>
      exact (covered.taskSuccess started matching).mono (List.subset_append_left _ _)
  | taskFailure occurrence errors =>
      exact (covered.taskFailure occurrence errors).mono (List.subset_append_left _ _)
  | streamItems stream items => exact covered.streamItems matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact covered.mono (List.subset_append_left _ _)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact covered.mono (List.subset_append_left _ _)

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
  registrations : queue.RegistrationsSupportedBy (Task.SupportsGroup work)
  started : queue.StartedTasksRegistered

/-- Every registered contributor or ancestor ref belongs to an exposed task region.
Witness: full-chain task support supplies the ref inside its covered source region,
without inferring direct ownership from registration.
-/
theorem State.RegionInventory.registered_exposed {queue : State} {work seen}
    (inventory : queue.RegionInventory work seen) {ref : NodeRef}
    (registered : ref ∈ queue.registeredGroups)
    : ExposedRef work seen ref := by
  obtain ⟨task, member, address, groups, path, result, children, producer, owners,
    fragment, same, located, included, inChain⟩ := inventory.registrations ref registered
  apply inventory.regions task member address _ same located ref
  exact List.mem_append_left _ (List.mem_flatMap.mpr
    ⟨fragment, included, inChain⟩)

/-- One matched item updates the inventory at its actual integration boundary.
Witness: region coverage and the existing task-provenance/registry preservation lemmas. -/
theorem State.RegionInventory.integrateStreamItem {queue : State} {work seen stream items}
    (inventory : queue.RegionInventory work seen)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : (queue.integrateStreamItem item).RegionInventory work
        (item.occurrence :: seen) := by
  have childTasks : ∀ task ∈ item.work.tasks, TaskMatches work task := by
    intro task taskMember
    obtain ⟨address, payload, same, known⟩ :=
      matching.streamItem_childTask_producer member taskMember
    exact ⟨⟨address, payload, _, same, known⟩,
      matching.streamItem_childTask_groupsExact member taskMember⟩
  exact ⟨
    inventory.regions.integrateStreamItem matching member,
    ((inventory.matching.maybeIntegrateWork item.work childTasks).pruneEmptyGroups
      _).startNewWork
      _,
    ((inventory.registrations.maybeIntegrateWork item.work
        (fun _ groupMember => matching.streamItem_groupsSupported member groupMember)
        ).pruneEmptyGroups
      _).startNewWork
      _,
    ((inventory.started.maybeIntegrateWork item.work none).pruneEmptyGroups
      _).startNewWork
      _
  ⟩

/-- Initial registration cannot use any stream item's hidden region.
Witness: root-only task-region coverage and the existing initial registry invariants. -/
theorem createWorkQueue_regionInventory (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).RegionInventory work [] :=
  ⟨
    createWorkQueue_registeredRegions work,
    createWorkQueue_fromSpec_registeredTasksMatch work,
    createWorkQueue_fromSpec_registrationsSupported work,
    createWorkQueue_startedTasksRegistered _
  ⟩

/-- Every matching graph event preserves the inventory for the enlarged identity prefix.
Witness: region coverage plus unchanged provenance, registration, and start invariants. -/
theorem State.RegionInventory.handleGraphEvent {queue : State} {work seen}
    (inventory : queue.RegionInventory work seen)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : (queue.handleGraphEvent event).1.RegionInventory work
        (seen ++ event.identities.1) :=
  ⟨
    inventory.regions.handleGraphEvent inventory.started event matching,
    inventory.matching.handleGraphEvent event matching,
    inventory.registrations.handleGraphEvent event matching,
    inventory.started.handleGraphEvent event
  ⟩

/-- Arbitrary matching source replay registers only already-exposed ref regions.
Witness: induction through the actual event handlers, including both failures and
successful releases. Neither pending ledgers nor registration availability is assumed. -/
theorem createWorkQueue_replay_regionInventory {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).RegionInventory
        work (events.flatMap (fun event => event.identities.1)) := by
  induction valid with
  | nil => exact createWorkQueue_regionInventory work
  | @append before event validBefore matching fresh ready ih =>
      rw [State.replayGraphEvents_append, List.flatMap_append, List.flatMap_singleton]
      exact ih.handleGraphEvent event matching

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
