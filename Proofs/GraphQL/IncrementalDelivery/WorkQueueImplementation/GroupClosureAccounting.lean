import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalBasics

/-! Group closures retire their refs and cannot repeat in subsequent actual output. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Closure segments carry concrete retirement, not assumed lifecycle validity
-----------------------------------------------------------------------------------------

/-- Group refs closed by raw success/failure events, excluding stream completions. -/
def rawGroupClosureRefs : WorkQueueEvent → NodeRefs
  | .groupSuccess group _ _ | .groupFailure group _ => [group.ref]
  | _ => []

/-- A segment closes distinct refs, retires each one, and cannot close an old retired ref.
The before/result states are the actual executable states; no history admission is assumed.
-/
structure GroupClosureAccounting (before : State) (result : State × List WorkQueueEvent)
    : Prop where
  unique : (result.2.flatMap rawGroupClosureRefs).Nodup
  closed : ∀ ref ∈ result.2.flatMap rawGroupClosureRefs, result.1.RetiredGroup ref
  preserves : ∀ ref, before.RetiredGroup ref → result.1.RetiredGroup ref
  excludes : ∀ ref, before.RetiredGroup ref → ref ∉ result.2.flatMap rawGroupClosureRefs

/-- A silent transition only needs to retain earlier retirement certificates.
Witness: its empty output has no new closure or duplicate.
-/
theorem GroupClosureAccounting.silent {before after : State}
    (preserves : ∀ ref, before.RetiredGroup ref → after.RetiredGroup ref)
    : GroupClosureAccounting before (after, []) :=
  ⟨by simp, by simp, preserves, by simp⟩

/-- Sequential segments cannot repeat a closure from an earlier segment.
Witness: every earlier closure supplies the retirement certificate excluded by the next.
-/
theorem GroupClosureAccounting.append {before first second}
    (left : GroupClosureAccounting before first)
    (right : GroupClosureAccounting first.1 second)
    : GroupClosureAccounting before (second.1, first.2 ++ second.2) := by
  refine ⟨?_, ?_, fun ref retired => right.preserves ref (left.preserves ref retired), ?_⟩
  · rw [List.flatMap_append]
    exact List.nodup_append.mpr ⟨left.unique, right.unique, by
      intro ref earlier other later same
      subst other
      exact right.excludes ref (left.closed ref earlier) later⟩
  · intro ref member
    rw [List.flatMap_append] at member
    rcases List.mem_append.mp member with earlier | later
    · exact right.preserves ref (left.closed ref earlier)
    · exact right.closed ref later
  · intro ref retired member
    rw [List.flatMap_append] at member
    rcases List.mem_append.mp member with earlier | later
    · exact left.excludes ref retired earlier
    · exact right.excludes ref (left.preserves ref retired) later

/-- A final silent state change preserves closure accounting if it preserves retirement.
Witness: transport every newly or previously retired ref through that state change.
-/
theorem GroupClosureAccounting.post {before result after}
    (accounted : GroupClosureAccounting before result)
    (preserves : ∀ ref, result.1.RetiredGroup ref → after.RetiredGroup ref)
    : GroupClosureAccounting before (after, result.2) :=
  ⟨
    accounted.unique,
    fun ref member => preserves ref (accounted.closed ref member),
    fun ref retired => preserves ref (accounted.preserves ref retired),
    accounted.excludes
  ⟩

-----------------------------------------------------------------------------------------
-- Each concrete group completion establishes permanent retirement
-----------------------------------------------------------------------------------------

/-- A successful flush closes exactly its supplied group, irrespective of value count.
Witness: the output is optional group values followed by one success control event.
-/
theorem State.finishGroupSuccess_groupClosureRefs (queue : State) (node : GroupNode)
    : (queue.finishGroupSuccess node).2.1.flatMap rawGroupClosureRefs
      = [node.group.node.ref] := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output]
  split <;> simp [rawGroupClosureRefs]

/-- Successful closure retires the supplied registered ref, including through child pruning.
Witness: task flushing preserves the registry; the own-ref filter removes every live copy,
and pruning preserves the resulting retirement certificate.
-/
theorem State.finishGroupSuccess_retires (queue : State) (node : GroupNode)
    (registered : node.group.node.ref ∈ queue.registeredGroups)
    : (queue.finishGroupSuccess node).1.RetiredGroup node.group.node.ref := by
  let flushed := (node.tasks.foldl flushGroupTask (queue, [], [])).1
  have same : flushed.registeredGroups = queue.registeredGroups := by
    apply fold_projection (fun acc : State × List ExecutionGroupValue × NodeRefs =>
      acc.1.registeredGroups) flushGroupTask
    intro acc occurrence
    unfold flushGroupTask
    split <;> rfl
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun entry => entry.group.node.ref != node.group.node.ref)
    rootGroups := flushed.rootGroups.filter (· != node.group.node.ref) }
  have retired : current.RetiredGroup node.group.node.ref := by
    refine ⟨same ▸ registered, ?_⟩
    intro member
    obtain ⟨other, kept, equal⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp kept).2
    simp [equal] at different
  exact retired.pruneEmptyGroups _

/-- Failed closure retires its registered root without a descendant-coverage premise.
Witness: the removal traversal always removes its own ref and preserves registrations.
-/
theorem State.finishGroupFailure_retires (queue : State) (node : GroupNode) (errors : Nat)
    (registered : node.group.node.ref ∈ queue.registeredGroups)
    : (queue.finishGroupFailure node errors).1.RetiredGroup node.group.node.ref :=
  State.RetiredGroup.of_lookup_none registered (queue.removeGroup_ownGroupAbsent _)

/-- A live successful closure supplies one fresh retirement certificate.
Witness: its sole closing ref is live before the flush and permanently absent afterward.
-/
theorem State.finishGroupSuccess_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (node : GroupNode)
    (member : node ∈ queue.groupNodes)
    : GroupClosureAccounting queue
        ((queue.finishGroupSuccess node).1, (queue.finishGroupSuccess node).2.1) := by
  refine ⟨?_, ?_, fun _ retired => retired.finishGroupSuccess node, ?_⟩
  · rw [queue.finishGroupSuccess_groupClosureRefs]; simp
  · intro ref closed
    rw [queue.finishGroupSuccess_groupClosureRefs] at closed
    cases List.mem_singleton.mp closed
    exact queue.finishGroupSuccess_retires node (live node member)
  · intro ref retired closed
    rw [queue.finishGroupSuccess_groupClosureRefs] at closed
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
    by simp [State.finishGroupFailure, rawGroupClosureRefs],
    ?_,
    fun _ retired => retired.removeGroup node.group.node.ref,
    ?_
  ⟩
  · intro ref closed
    have same : ref = node.group.node.ref := List.mem_singleton.mp closed
    subst ref
    exact queue.finishGroupFailure_retires node errors (live node member)
  · intro ref retired closed
    have same : ref = node.group.node.ref := List.mem_singleton.mp closed
    exact retired.2 (List.mem_map.mpr ⟨node, member, same.symm⟩)

-----------------------------------------------------------------------------------------
-- Recursive drains and contributor folds retain every earlier closure certificate
-----------------------------------------------------------------------------------------

/-- Ready-group draining closes each group at most once and permanently retires its ref.
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
            obtain ⟨ref, _, choice⟩ := List.exists_of_findSome?_eq_some selected
            cases found : current.groupNode? ref with
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
Witness: the mapped group keeps exactly its previous ref and registration entry.
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
Witness: child integration cannot revive retired refs; each live owner closes once, and
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
          GroupClosureAccounting.silent (fun ref retired =>
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
      (retains : ∀ ref, queue.RetiredGroup ref → acc.1.RetiredGroup ref)
      : let final := more.foldl step acc
        final.1.LiveGroupsRegistered ∧ final.1.TaskGroupsRegistered
        ∧ ∀ ref, queue.RetiredGroup ref → final.1.RetiredGroup ref := by
    induction more generalizing acc with
    | nil => exact ⟨live, tasks, retains⟩
    | cons item rest ih =>
        have registered := State.integrateStreamItem_registration live tasks matching
          (included List.mem_cons_self)
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          registered.1 registered.2.1 (fun ref old =>
            (((retains ref old).maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
  unfold State.streamItems
  split
  · exact GroupClosureAccounting.silent (fun _ retired => retired)
  · let final := items.foldl step (queue, [], [], [])
    obtain ⟨finalLive, finalTasks, retains⟩ := loop items (List.Subset.refl _)
      (queue, [], [], []) live tasks (fun _ retired => retired)
    have carrier : GroupClosureAccounting queue
        (final.1, [.streamValues stream final.2.2.2 final.2.1 final.2.2.1]) :=
      ⟨by simp [rawGroupClosureRefs], by simp [rawGroupClosureRefs], retains,
        by simp [rawGroupClosureRefs]⟩
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
      split <;> exact ⟨by simp [rawGroupClosureRefs], by simp [rawGroupClosureRefs],
        fun _ retired => retired, by simp [rawGroupClosureRefs]⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact ⟨by simp [rawGroupClosureRefs], by simp [rawGroupClosureRefs],
        fun _ retired => retired, by simp [rawGroupClosureRefs]⟩

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
Witness: the optional terminal marker has no group ref and changes no retirement field.
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
          rawGroupClosureRefs, List.append_nil] using prior.unique
      · simpa only [List.flatMap_append, List.flatMap_singleton,
          rawGroupClosureRefs, List.append_nil, State.RetiredGroup] using prior.closed
      · simpa only [List.flatMap_append, List.flatMap_singleton,
          rawGroupClosureRefs, List.append_nil] using prior.excludes
    · exact prior

/-- Group refs closed by normalized success/failure events, excluding streams. -/
def groupClosureRefs : Execution.WorkQueueEvent → NodeRefs
  | .groupSuccess group _ _ | .groupFailure group _ => [group.ref]
  | _ => []

/-- Normalizing a raw event retains exactly its closing group refs.
Witness: group controls are copied, while value remapping cannot introduce a closure.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_groupClosureRefs
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.flatMap groupClosureRefs
      = rawGroupClosureRefs event := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, rawGroupClosureRefs,
    groupClosureRefs, List.flatMap_map]

/-- Stateful normalization retains every group closure in its original order.
Witness: the per-event projection and concatenation through the publisher's real fold.
-/
theorem IncrementalPublisher.normalizeBatch_groupClosureRefs
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.flatMap groupClosureRefs
      = events.flatMap rawGroupClosureRefs := by
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.flatMap_append, IncrementalPublisher.handleWorkQueueEvent_groupClosureRefs,
        ih, List.flatMap_cons]

/-- Actual normalized replay closes each group at most once and retires every closed ref.
Witness: joint registry and closure-certificate replay; old output refs are retired before
each batch, so the next batch excludes them without any output-admission premise.
-/
theorem State.runNormalized_groupClosures {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ((queue.runNormalized batches).2.flatten.flatMap groupClosureRefs).Nodup
      ∧ ∀ ref ∈ (queue.runNormalized batches).2.flatten.flatMap groupClosureRefs,
          (queue.runNormalized batches).1.RetiredGroup ref := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (live : acc.1.LiveGroupsRegistered) (tasks : acc.1.TaskGroupsRegistered)
      (matching : ∀ event ∈ more.flatten, event.MatchesWork work)
      (unique : (acc.2.2.flatten.flatMap groupClosureRefs).Nodup)
      (retired : ∀ ref ∈ acc.2.2.flatten.flatMap groupClosureRefs, acc.1.RetiredGroup ref)
      : let final := more.foldl normalizedStep acc
        (final.2.2.flatten.flatMap groupClosureRefs).Nodup
        ∧ ∀ ref ∈ final.2.2.flatten.flatMap groupClosureRefs, final.1.RetiredGroup ref := by
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
            IncrementalPublisher.normalizeBatch_groupClosureRefs]
          exact List.nodup_append.mpr ⟨unique, accounted.unique, by
            intro ref old other later equal
            subst other
            exact accounted.excludes ref (retired ref old) later⟩
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupClosureRefs]
          intro ref member
          exact (List.mem_append.mp member).elim
            (fun old => accounted.preserves ref (retired ref old))
            (fun added => accounted.closed ref added)
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
        groupClosureRefs).Nodup :=
  (State.runNormalized_groupClosures (createWorkQueue_registration work).1
    (createWorkQueue_registration work).2 batches matching).1

-----------------------------------------------------------------------------------------
-- Atomic positions exclude every earlier group closure with the same ref
-----------------------------------------------------------------------------------------

/-- Atomic value expansion preserves the group-closure list exactly.
Witness: all value atoms are nonclosing; group control events remain singletons.
-/
theorem publicationAtoms_groupClosureRefs (event : Execution.WorkQueueEvent)
    : (publicationAtoms event).flatMap groupClosureRefs = groupClosureRefs event := by
  cases event with
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => rfl
      | case2 => rfl
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, groupClosureRefs] using ih
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => simp [publicationAtoms, groupClosureRefs, List.flatMap_map]

/-- Atomic output has exactly the same nonrepeating group closures as normalized output.
Witness: the exact atomization projection preserves the normalized uniqueness theorem.
-/
theorem createWorkQueue_runNormalized_atomicGroupClosuresUnique {work : Execution.Work}
    {batches : List (List GraphEvent)}
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ((((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
          publicationAtoms).flatMap
        groupClosureRefs).Nodup := by
  simpa only [List.flatMap_assoc, publicationAtoms_groupClosureRefs]
    using createWorkQueue_runNormalized_groupClosuresUnique matching

/-- A unique closure-ref list excludes the current ref from its strict output prefix.
Witness: index induction through the event list and disjointness of each head and tail.
-/
theorem groupClosuresUnique_atEvent {events : List Execution.WorkQueueEvent}
    {index event ref} (unique : (events.flatMap groupClosureRefs).Nodup)
    (atEvent : events[index]? = some event) (closes : ref ∈ groupClosureRefs event)
    : ref ∉ (events.take index).flatMap groupClosureRefs := by
  induction events generalizing index with
  | nil => simp at atEvent
  | cons head tail ih =>
      have parts := List.nodup_append.mp unique
      cases index with
      | zero => simp
      | succ index =>
          intro earlier
          rcases List.mem_append.mp earlier with atHead | inTail
          · exact parts.2.2 ref atHead ref
              (List.mem_flatMap.mpr ⟨event, List.mem_of_getElem? atEvent, closes⟩) rfl
          · exact ih parts.2.1 atEvent inTail

/-- Every actual group closure excludes an earlier group closure with the same ref.
Witness: concrete permanent retirement survives matching replay, normalization, and
atomic expansion. Same-ref stream closures require generated role separation separately.
-/
theorem createWorkQueue_runNormalized_groupUnclosedAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index event ref}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (closes : ref ∈ groupClosureRefs event)
    : ref
      ∉ (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
          |>.take index).flatMap
          groupClosureRefs :=
  groupClosuresUnique_atEvent
    (createWorkQueue_runNormalized_atomicGroupClosuresUnique
      (fun _ member => valid.eachMatches member)) atEvent closes

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
