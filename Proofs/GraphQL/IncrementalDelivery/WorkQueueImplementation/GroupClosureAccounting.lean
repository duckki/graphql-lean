import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalBasics

/-! Group closures retire their keys and cannot repeat in subsequent actual output. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Closure segments carry concrete retirement, not assumed lifecycle validity
-----------------------------------------------------------------------------------------

/-- Group keys closed by raw success/failure events, excluding stream completions. -/
def rawGroupClosureKeys : WorkQueueEvent → Keys
  | .groupSuccess group _ _ | .groupFailure group _ => [group.key]
  | _ => []

/-- A segment closes distinct keys, retires each one, and cannot close an old retired key.
The before/result states are the actual executable states; no history admission is assumed.
-/
structure GroupClosureAccounting (before : State) (result : State × List WorkQueueEvent)
    : Prop where
  unique : (result.2.flatMap rawGroupClosureKeys).Nodup
  closed : ∀ key ∈ result.2.flatMap rawGroupClosureKeys, result.1.RetiredGroup key
  preserves : ∀ key, before.RetiredGroup key → result.1.RetiredGroup key
  excludes : ∀ key, before.RetiredGroup key → key ∉ result.2.flatMap rawGroupClosureKeys

/-- A silent transition only needs to retain earlier retirement certificates.
Witness: its empty output has no new closure or duplicate.
-/
theorem GroupClosureAccounting.silent {before after : State}
    (preserves : ∀ key, before.RetiredGroup key → after.RetiredGroup key)
    : GroupClosureAccounting before (after, []) :=
  ⟨by simp, by simp, preserves, by simp⟩

/-- Sequential segments cannot repeat a closure from an earlier segment.
Witness: every earlier closure supplies the retirement certificate excluded by the next.
-/
theorem GroupClosureAccounting.append {before first second}
    (left : GroupClosureAccounting before first)
    (right : GroupClosureAccounting first.1 second)
    : GroupClosureAccounting before (second.1, first.2 ++ second.2) := by
  refine ⟨?_, ?_, fun key retired => right.preserves key (left.preserves key retired), ?_⟩
  · rw [List.flatMap_append]
    exact List.nodup_append.mpr ⟨left.unique, right.unique, by
      intro key earlier other later same
      subst other
      exact right.excludes key (left.closed key earlier) later⟩
  · intro key member
    rw [List.flatMap_append] at member
    rcases List.mem_append.mp member with earlier | later
    · exact right.preserves key (left.closed key earlier)
    · exact right.closed key later
  · intro key retired member
    rw [List.flatMap_append] at member
    rcases List.mem_append.mp member with earlier | later
    · exact left.excludes key retired earlier
    · exact right.excludes key (left.preserves key retired) later

/-- A final silent state change preserves closure accounting if it preserves retirement.
Witness: transport every newly or previously retired key through that state change.
-/
theorem GroupClosureAccounting.post {before result after}
    (accounted : GroupClosureAccounting before result)
    (preserves : ∀ key, result.1.RetiredGroup key → after.RetiredGroup key)
    : GroupClosureAccounting before (after, result.2) :=
  ⟨
    accounted.unique,
    fun key member => preserves key (accounted.closed key member),
    fun key retired => preserves key (accounted.preserves key retired),
    accounted.excludes
  ⟩

-----------------------------------------------------------------------------------------
-- Each concrete group completion establishes permanent retirement
-----------------------------------------------------------------------------------------

/-- A successful flush closes exactly its supplied group, irrespective of value count.
Witness: the output is optional group values followed by one success control event.
-/
theorem State.finishGroupSuccess_groupClosureKeys (queue : State) (node : GroupNode)
    : (queue.finishGroupSuccess node).2.1.flatMap rawGroupClosureKeys
      = [node.group.node.key] := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output]
  split <;> simp [rawGroupClosureKeys]

/-- Successful closure retires the supplied registered key, including through child pruning.
Witness: task flushing preserves the registry; the own-key filter removes every live copy,
and pruning preserves the resulting retirement certificate.
-/
theorem State.finishGroupSuccess_retires (queue : State) (node : GroupNode)
    (registered : node.group.node.key ∈ queue.registeredGroups)
    : (queue.finishGroupSuccess node).1.RetiredGroup node.group.node.key := by
  let flushed := (node.tasks.foldl flushGroupTask (queue, [], [])).1
  have same : flushed.registeredGroups = queue.registeredGroups := by
    apply fold_projection (fun acc : State × List ExecutionGroupValue × Keys =>
      acc.1.registeredGroups) flushGroupTask
    intro acc occurrence
    unfold flushGroupTask
    split <;> rfl
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun entry => entry.group.node.key != node.group.node.key)
    rootGroups := flushed.rootGroups.filter (· != node.group.node.key) }
  have retired : current.RetiredGroup node.group.node.key := by
    refine ⟨same ▸ registered, ?_⟩
    intro member
    obtain ⟨other, kept, equal⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp kept).2
    simp [equal] at different
  exact retired.pruneEmptyGroups _

/-- Failed closure retires its registered root without a descendant-coverage premise.
Witness: the removal traversal always removes its own key and preserves registrations.
-/
theorem State.finishGroupFailure_retires (queue : State) (node : GroupNode) (errors : Nat)
    (registered : node.group.node.key ∈ queue.registeredGroups)
    : (queue.finishGroupFailure node errors).1.RetiredGroup node.group.node.key :=
  State.RetiredGroup.of_lookup_none registered (queue.removeGroup_ownGroupAbsent _)

/-- A live successful closure supplies one fresh retirement certificate.
Witness: its sole closing key is live before the flush and permanently absent afterward.
-/
theorem State.finishGroupSuccess_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (node : GroupNode)
    (member : node ∈ queue.groupNodes)
    : GroupClosureAccounting queue
        ((queue.finishGroupSuccess node).1, (queue.finishGroupSuccess node).2.1) := by
  refine ⟨?_, ?_, fun _ retired => retired.finishGroupSuccess node, ?_⟩
  · rw [queue.finishGroupSuccess_groupClosureKeys]; simp
  · intro key closed
    rw [queue.finishGroupSuccess_groupClosureKeys] at closed
    cases List.mem_singleton.mp closed
    exact queue.finishGroupSuccess_retires node (live node member)
  · intro key retired closed
    rw [queue.finishGroupSuccess_groupClosureKeys] at closed
    exact retired.2 (List.mem_map.mpr ⟨node, member, (List.mem_singleton.mp closed).symm⟩)

/-- A live failed closure supplies one fresh retirement certificate.
Witness: its closing node was live and registered; own-root removal excludes later reuse.
-/
theorem State.finishGroupFailure_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (node : GroupNode)
    (member : node ∈ queue.groupNodes) (errors : Nat)
    : GroupClosureAccounting queue
        (
          (queue.finishGroupFailure node errors).1,
          [(queue.finishGroupFailure node errors).2]
        ) := by
  refine ⟨
    by simp [State.finishGroupFailure, rawGroupClosureKeys],
    ?_,
    fun _ retired => retired.removeGroup node.group.node.key,
    ?_
  ⟩
  · intro key closed
    have same : key = node.group.node.key := List.mem_singleton.mp closed
    subst key
    exact queue.finishGroupFailure_retires node errors (live node member)
  · intro key retired closed
    have same : key = node.group.node.key := List.mem_singleton.mp closed
    exact retired.2 (List.mem_map.mpr ⟨node, member, same.symm⟩)

-----------------------------------------------------------------------------------------
-- Recursive drains and contributor folds retain every earlier closure certificate
-----------------------------------------------------------------------------------------

/-- Ready-group draining closes each group at most once and permanently retires its key.
Witness: selected nodes are live and registered; every recursive step preserves old
retirements, including activation after a successful carrier.
-/
theorem State.drainReadyGroups_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    : GroupClosureAccounting queue queue.drainReadyGroups := by
  have loop (fuel : Nat) (current : State)
      (live : current.LiveGroupsRegistered) (tasks : current.TaskGroupsRegistered)
      : GroupClosureAccounting current (State.drainReadyGroups.go fuel current) := by
    induction fuel generalizing current with
    | zero => exact GroupClosureAccounting.silent (fun _ retired => retired)
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact GroupClosureAccounting.silent (fun _ retired => retired)
        · rename_i node selected
          have member : node ∈ current.groupNodes := by
            obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
            cases found : current.groupNode? key with
            | none => simp [found] at choice
            | some candidate =>
                simp only [found] at choice
                change (if _ then some candidate else none) = some node at choice
                split at choice
                · cases Option.some.inj choice
                  exact List.mem_of_find?_eq_some found
                · contradiction
          cases failed : node.failure with
          | none =>
              have registered := current.finishGroupSuccess_registration live tasks node
              have activated := State.startNewWork_registration registered.1 registered.2.1
                (current.finishGroupSuccess node).2.2
              exact ((State.finishGroupSuccess_closureAccounting live node member).post
                (fun _ retired => retired.startNewWork _)).append
                  (ih _ activated.1 activated.2)
          | some errors =>
              exact (State.finishGroupFailure_closureAccounting live node member errors).append
                (ih _ (fun other kept => live other (List.mem_filter.mp kept).1) tasks)
  exact loop _ queue live tasks

/-- Removing task memberships retains registration of every live group.
Witness: the mapped group keeps exactly its previous key and registration entry.
-/
private theorem live_removeTask {queue : State} (live : queue.LiveGroupsRegistered)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).LiveGroupsRegistered := by
  intro node member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact live old oldMember

/-- A failed-task owner fold retires every emitted closure without repetition.
Witness: each active owner is looked up before closing; latent caches and ignored
settlements produce no closure, and retirement survives every subsequent owner step.
-/
theorem State.taskFailure_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (occurrence : Occurrence) (errors : Nat)
    : GroupClosureAccounting queue (queue.taskFailure occurrence errors) := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (registered : acc.1.LiveGroupsRegistered)
      (prior : GroupClosureAccounting queue acc)
      : GroupClosureAccounting queue (groups.foldl (failureGroupStep errors) acc) := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        obtain ⟨current, events⟩ := acc
        dsimp only [List.foldl_cons, failureGroupStep]
        split
        · exact ih _ registered prior
        · rename_i node found
          have member := List.mem_of_find?_eq_some found
          split
          · exact ih _ (fun other kept => registered other (List.mem_filter.mp kept).1)
              (prior.append (State.finishGroupFailure_closureAccounting registered node
                member errors))
          · exact ih _ (registered.putGroupNode _ (registered node member))
              (prior.post (fun _ retired => retired.putGroupNode _))
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskFailure, found]
        using GroupClosureAccounting.silent (before := queue) (fun _ retired => retired)
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      split
      · exact GroupClosureAccounting.silent (fun _ retired => retired.removeTask occurrence)
      · exact loop _ (_, []) (live_removeTask live occurrence)
          (GroupClosureAccounting.silent (fun _ retired => retired.removeTask occurrence))

/-- A successful task preserves closure uniqueness across integration, owners, and draining.
Witness: child integration cannot revive retired keys; each live owner closes once, and
the exact single-pass output carries its retirement evidence into the final drain.
-/
theorem State.taskSuccess_closureAccounting {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : GroupClosureAccounting queue (queue.taskSuccess occurrence result) := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (live : acc.1.LiveGroupsRegistered) (tasks : acc.1.TaskGroupsRegistered)
      (prior : GroupClosureAccounting queue (acc.1, acc.2.1))
      : let final := groups.foldl successGroupStep acc
        final.1.LiveGroupsRegistered ∧ final.1.TaskGroupsRegistered
        ∧ GroupClosureAccounting queue (final.1, final.2.1) := by
    induction groups generalizing acc with
    | nil => exact ⟨live, tasks, prior⟩
    | cons group rest ih =>
        obtain ⟨current, events, released⟩ := acc
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ live tasks prior
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have member := List.mem_of_find?_eq_some found
          have updatedLive := live.putGroupNode updated (live node member)
          have present : updated ∈ (current.putGroupNode updated).groupNodes := by
            apply List.mem_map.mpr ⟨node, member, ?_⟩
            simp [updated]
          have prepared := prior.post (fun _ retired => retired.putGroupNode updated)
          split
          · have registered := State.finishGroupSuccess_registration updatedLive tasks updated
            exact ih _ registered.1 registered.2.1
              (prepared.append (State.finishGroupSuccess_closureAccounting updatedLive
                updated present))
          · exact ih _ updatedLive tasks prepared
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found]
        using GroupClosureAccounting.silent (before := queue) (fun _ retired => retired)
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact GroupClosureAccounting.silent (fun _ retired => retired.removeTask occurrence)
      · let stored := queue.putTaskNode { node with value := some result.value }
        have registered := stored.maybeIntegrateWork_registration live tasks result.work
          matching.childTasksCovered (some occurrence)
        have start : GroupClosureAccounting queue
            ((stored.maybeIntegrateWork result.work (some occurrence)).1, []) :=
          GroupClosureAccounting.silent (fun key retired =>
            State.RetiredGroup.maybeIntegrateWork (queue := stored) retired _ _)
        obtain ⟨finalLive, finalTasks, closures⟩ := loop node.task.groups (_, [], {})
          registered.1 registered.2.1 start
        let folded := node.task.groups.foldl successGroupStep
          ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
        have activated := State.startNewWork_registration finalLive finalTasks folded.2.2
        exact (closures.post (fun _ retired => retired.startNewWork _)).append
          (State.drainReadyGroups_closureAccounting activated.1 activated.2)

/-- Stream-item integration preserves old retirements before its group-closure drain.
Witness: matched child work retains registration; integration, pruning, and activation
cannot recreate an old group, and the stream carrier itself closes no group.
-/
theorem State.streamItems_closureAccounting {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : GroupClosureAccounting queue (queue.streamItems stream items) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let integrated := acc.1.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 },
      acc.2.1 ++ pruned.2, acc.2.2.1 ++ integrated.2.newStreams,
      acc.2.2.2 ++ [item.value])
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (live : acc.1.LiveGroupsRegistered) (tasks : acc.1.TaskGroupsRegistered)
      (retains : ∀ key, queue.RetiredGroup key → acc.1.RetiredGroup key)
      : let final := more.foldl step acc
        final.1.LiveGroupsRegistered ∧ final.1.TaskGroupsRegistered
        ∧ ∀ key, queue.RetiredGroup key → final.1.RetiredGroup key := by
    induction more generalizing acc with
    | nil => exact ⟨live, tasks, retains⟩
    | cons item rest ih =>
        have registered := State.integrateStreamItem_registration live tasks matching
          (included List.mem_cons_self)
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          registered.1 registered.2.1 (fun key old =>
            (((retains key old).maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
  unfold State.streamItems
  split
  · exact GroupClosureAccounting.silent (fun _ retired => retired)
  · let final := items.foldl step (queue, [], [], [])
    obtain ⟨finalLive, finalTasks, retains⟩ := loop items (List.Subset.refl _)
      (queue, [], [], []) live tasks (fun _ retired => retired)
    have carrier : GroupClosureAccounting queue
        (final.1, [.streamValues stream final.2.2.2 final.2.1 final.2.2.1]) :=
      ⟨by simp [rawGroupClosureKeys], by simp [rawGroupClosureKeys], retains,
        by simp [rawGroupClosureKeys]⟩
    exact carrier.append (State.drainReadyGroups_closureAccounting finalLive finalTasks)

/-- Matching graph events emit nonrepeating, permanently retired group closures.
Witness: task and item proofs include all drains; stream-only closures leave groups alone.
-/
theorem State.handleGraphEvent_closureAccounting {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (event : GraphEvent) (matching : event.MatchesWork work)
    : GroupClosureAccounting queue (queue.handleGraphEvent event) := by
  cases event with
  | taskSuccess occurrence result =>
      exact State.taskSuccess_closureAccounting live tasks matching
  | taskFailure occurrence errors =>
      exact State.taskFailure_closureAccounting live occurrence errors
  | streamItems stream items =>
      exact State.streamItems_closureAccounting live tasks matching
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact ⟨by simp [rawGroupClosureKeys], by simp [rawGroupClosureKeys],
        fun _ retired => retired, by simp [rawGroupClosureKeys]⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨by simp [rawGroupClosureKeys], by simp [rawGroupClosureKeys],
        fun _ retired => retired, by simp [rawGroupClosureKeys]⟩

-----------------------------------------------------------------------------------------
-- Replay and publisher projections retain nonrepeating group closures
-----------------------------------------------------------------------------------------

/-- Raw replay preserves closure accounting across every matching event.
Witness: registration coverage supplies each handler, and segment composition rules out
closures already retired by an earlier handler, even within the same host batch.
-/
theorem State.rawEventReplay_closureAccounting {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : GroupClosureAccounting queue (queue.rawEventReplay events) := by
  induction events generalizing queue with
  | nil => exact GroupClosureAccounting.silent (fun _ retired => retired)
  | cons event rest ih =>
      have matched := matching event List.mem_cons_self
      have next := State.handleGraphEvent_registration live tasks event matched
      rw [State.rawEventReplay_cons]
      exact (State.handleGraphEvent_closureAccounting live tasks event matched).append
        (ih next.1 next.2.1 (fun later member => matching later (List.mem_cons_of_mem _ member)))

/-- The batch wrapper preserves group closure accounting through termination.
Witness: the optional terminal marker has no group key and changes no retirement field.
-/
theorem State.handleGraphEvents_closureAccounting {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : GroupClosureAccounting queue (queue.handleGraphEvents events) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact GroupClosureAccounting.silent (fun _ retired => retired)
  · have prior := State.rawEventReplay_closureAccounting live tasks events matching
    dsimp only
    split
    · refine ⟨?_, ?_, prior.preserves, ?_⟩
      · simpa only [List.flatMap_append, List.flatMap_singleton,
          rawGroupClosureKeys, List.append_nil] using prior.unique
      · simpa only [List.flatMap_append, List.flatMap_singleton,
          rawGroupClosureKeys, List.append_nil, State.RetiredGroup] using prior.closed
      · simpa only [List.flatMap_append, List.flatMap_singleton,
          rawGroupClosureKeys, List.append_nil] using prior.excludes
    · exact prior

/-- Group keys closed by normalized success/failure events, excluding streams. -/
def groupClosureKeys : Execution.WorkQueueEvent → Keys
  | .groupSuccess group _ _ | .groupFailure group _ => [group.key]
  | _ => []

/-- Normalizing a raw event retains exactly its closing group keys.
Witness: group controls are copied, while value remapping cannot introduce a closure.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupClosureKeys
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap groupClosureKeys
      = rawGroupClosureKeys event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawGroupClosureKeys,
    groupClosureKeys, List.flatMap_map]

/-- Stateful normalization retains every group closure in its original order.
Witness: the per-event projection and concatenation through the publisher's real fold.
-/
theorem IncrementalPublisher.normalizeBatch_groupClosureKeys
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap groupClosureKeys
      = events.flatMap rawGroupClosureKeys := by
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.flatMap_append, IncrementalPublisher.handleWorkQueueEvent_groupClosureKeys,
        ih, List.flatMap_cons]

/-- Actual normalized replay closes each group at most once and retires every closed key.
Witness: joint registry and closure-certificate replay; old output keys are retired before
each batch, so the next batch excludes them without any output-admission premise.
-/
theorem State.runNormalized_groupClosures {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ((queue.runNormalized batches).2.flatten.flatMap groupClosureKeys).Nodup
      ∧ ∀ key ∈ (queue.runNormalized batches).2.flatten.flatMap groupClosureKeys,
          (queue.runNormalized batches).1.RetiredGroup key := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (live : acc.1.LiveGroupsRegistered) (tasks : acc.1.TaskGroupsRegistered)
      (matching : ∀ event ∈ more.flatten, event.MatchesWork work)
      (unique : (acc.2.2.flatten.flatMap groupClosureKeys).Nodup)
      (retired : ∀ key ∈ acc.2.2.flatten.flatMap groupClosureKeys, acc.1.RetiredGroup key)
      : let final := more.foldl normalizedStep acc
        (final.2.2.flatten.flatMap groupClosureKeys).Nodup
        ∧ ∀ key ∈ final.2.2.flatten.flatMap groupClosureKeys, final.1.RetiredGroup key := by
    induction more generalizing acc with
    | nil => exact ⟨unique, retired⟩
    | cons batch rest ih =>
        have matched : ∀ event ∈ batch, event.MatchesWork work :=
          fun event member => matching event (List.mem_append_left _ member)
        have next := State.handleGraphEvents_registration live tasks batch matched
        have accounted := State.handleGraphEvents_closureAccounting live tasks batch matched
        apply ih
          (normalizedStep acc batch)
          (by rw [normalizedStep_queue]; exact next.1)
          (by rw [normalizedStep_queue]; exact next.2.1)
          (fun event member => matching event (List.mem_append_right _ member))
        · rw [normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupClosureKeys]
          exact List.nodup_append.mpr ⟨unique, accounted.unique, by
            intro key old other later equal
            subst other
            exact accounted.excludes key (retired key old) later⟩
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupClosureKeys]
          intro key member
          exact (List.mem_append.mp member).elim
            (fun old => accounted.preserves key (retired key old))
            (fun added => accounted.closed key added)
  exact loop batches
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, []) live tasks
    matching (by simp) (by simp)

/-- Matched source payloads suffice for nonrepeating actual group closures.
Witness: initial registry coverage and the complete normalized replay theorem; source
freshness, start discipline, and generated-work metadata are unnecessary for this fact.
-/
theorem createWorkQueue_runNormalized_groupClosuresUnique {work : Execution.Work}
    {batches : List (List GraphEvent)}
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : (((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
        groupClosureKeys).Nodup :=
  (State.runNormalized_groupClosures (createWorkQueue_registration work).1
    (createWorkQueue_registration work).2 batches matching).1

-----------------------------------------------------------------------------------------
-- Atomic positions exclude every earlier group closure with the same key
-----------------------------------------------------------------------------------------

/-- Atomic value expansion preserves the group-closure list exactly.
Witness: all value atoms are nonclosing; group control events remain singletons.
-/
theorem publicationAtoms_groupClosureKeys (event : Execution.WorkQueueEvent)
    : (publicationAtoms event).flatMap groupClosureKeys = groupClosureKeys event := by
  cases event with
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => rfl
      | case2 => rfl
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, groupClosureKeys] using ih
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => simp [publicationAtoms, groupClosureKeys, List.flatMap_map]

/-- Atomic output has exactly the same nonrepeating group closures as normalized output.
Witness: the exact atomization projection preserves the normalized uniqueness theorem.
-/
theorem createWorkQueue_runNormalized_atomicGroupClosuresUnique {work : Execution.Work}
    {batches : List (List GraphEvent)}
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ((((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms).flatMap
        groupClosureKeys).Nodup := by
  simpa only [List.flatMap_assoc, publicationAtoms_groupClosureKeys]
    using createWorkQueue_runNormalized_groupClosuresUnique matching

/-- A unique closure-key list excludes the current key from its strict output prefix.
Witness: index induction through the event list and disjointness of each head and tail.
-/
theorem groupClosuresUnique_atEvent {events : List Execution.WorkQueueEvent}
    {index event key} (unique : (events.flatMap groupClosureKeys).Nodup)
    (atEvent : events[index]? = some event) (closes : key ∈ groupClosureKeys event)
    : key ∉ (events.take index).flatMap groupClosureKeys := by
  induction events generalizing index with
  | nil => simp at atEvent
  | cons head tail ih =>
      have parts := List.nodup_append.mp unique
      cases index with
      | zero => simp
      | succ index =>
          intro earlier
          rcases List.mem_append.mp earlier with atHead | inTail
          · exact parts.2.2 key atHead key
              (List.mem_flatMap.mpr ⟨event, List.mem_of_getElem? atEvent, closes⟩) rfl
          · exact ih parts.2.1 atEvent inTail

/-- Every actual group closure excludes an earlier group closure with the same key.
Witness: concrete permanent retirement survives matching replay, normalization, and
atomic expansion. Same-key stream closures require generated role separation separately.
-/
theorem createWorkQueue_runNormalized_groupUnclosedAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index event key}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (closes : key ∈ groupClosureKeys event)
    : key
      ∉ (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
          |>.take index).flatMap
          groupClosureKeys :=
  groupClosuresUnique_atEvent
    (createWorkQueue_runNormalized_atomicGroupClosuresUnique
      (fun _ member => valid.eachMatches member)) atEvent closes

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
