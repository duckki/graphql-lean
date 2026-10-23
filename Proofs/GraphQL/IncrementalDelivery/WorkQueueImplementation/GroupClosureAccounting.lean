import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalBasics
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.LiveRegistration

/-! Group removal and FIFO notification completion have distinct retirement ledgers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Closure segments carry concrete retirement, not assumed lifecycle validity
-----------------------------------------------------------------------------------------

/-- Control-shaped ref counters for local startup removals, separate from replay output. -/
private def startupClosures (failures : List GroupFailureEvent) : List WorkQueueEvent :=
  failures.map (fun failure => .groupFailure failure.group failure.errors)

/-- Immediate closures and enqueue effects record distinct removals at this transition. -/
private abbrev StartupClosureAccounting (before : State)
    (result : State × List WorkQueueEvent × List GroupFailureEvent)
    : Prop :=
  GroupClosureAccounting before (result.1, result.2.1 ++ startupClosures result.2.2)

/-- Compose the two completion channels while preserving their separate output order.
Witness: retirement excludes duplicates across the chronological transition sequence;
collecting the two local effect channels preserves their removal refs. This proof
permutation does not reorder emitted FIFO output.
-/
private theorem StartupClosureAccounting.append {before first second}
    (left : StartupClosureAccounting before first)
    (right : StartupClosureAccounting first.1 second)
    : StartupClosureAccounting before
        (second.1, first.2.1 ++ second.2.1, first.2.2 ++ second.2.2) := by
  have combined := GroupClosureAccounting.append left right
  apply combined.permute
  simpa only [startupClosures, List.map_append, List.append_assoc]
    using (List.perm_append_comm_assoc (startupClosures first.2.2)
            second.2.1 (startupClosures second.2.2)).append_left
      first.2.1

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
          [.groupFailure (queue.finishGroupFailure node errors).2.group
            (queue.finishGroupFailure node errors).2.errors]
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
          · exact ih _ registered prior
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskFailure, found]
        using GroupClosureAccounting.silent (before := queue) (fun _ retired => retired)
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact loop _ (_, []) live (GroupClosureAccounting.silent (fun _ retired => retired))

/-- Starting one group retires its queued failure and preserves earlier retirement.
Witness: cache exposure changes no group ref; the failing branch closes its live lookup,
and the successful task-start fold is silent for group retirement.
-/
private theorem startGroup_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    : GroupClosureAccounting queue
        (
          (queue.startGroup ref available).1,
          startupClosures (queue.startGroup ref available).2
        ) := by
  have cached : (queue.cacheTaskFailures available).LiveGroupsRegistered := by
    intro node member
    rw [State.cacheTaskFailures_registeredGroups]
    rw [State.cacheTaskFailures_groupNodes] at member
    exact live node member
  have initial : GroupClosureAccounting queue (queue.cacheTaskFailures available, []) :=
    .silent (fun _ retired => retired.cacheTaskFailures available)
  unfold State.startGroup
  dsimp only
  split
  · exact initial
  · rename_i node found
    split
    · apply initial.post
      intro target retired
      have nodes := fold_projection State.groupNodes
        (fun current task => current.startTask task available)
        (fun current task => current.startTask_groupNodes task available)
        node.tasks (queue.cacheTaskFailures available)
      have registry := fold_projection State.registeredGroups
        (fun current task => current.startTask task available)
        (fun current task => by
          unfold State.startTask
          split
          · rfl
          · split <;> rfl)
        node.tasks (queue.cacheTaskFailures available)
      simpa only [State.RetiredGroup, nodes, registry] using retired
    · exact initial.append (State.finishGroupFailure_closureAccounting cached node
        (List.mem_of_find?_eq_some found) _)

/-- Startup's separate failure inventory has distinct permanently retired refs.
Witness: compose each actual group start before activating streams, which change no group
retirement field. The local inventory needs no runtime group-cause cache.
-/
private theorem startNewWork_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (released : NewWork)
    (available : List (Occurrence × Nat))
    : GroupClosureAccounting queue
        (
          (queue.startNewWork released available).1,
          startupClosures (queue.startNewWork released available).2
        ) := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (registered : acc.1.LiveGroupsRegistered)
      (prior : GroupClosureAccounting queue (acc.1, startupClosures acc.2))
      : GroupClosureAccounting queue
          ((refs.foldl step acc).1, startupClosures (refs.foldl step acc).2) := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        · intro node member
          rw [State.startGroup_registeredGroups]
          exact registered node
            ((acc.1.startGroup_groupNodes_sublist ref available).subset member)
        · simpa only [step, startupClosures, List.map_append]
            using prior.append (startGroup_closureAccounting registered ref available)
  unfold State.startNewWork
  let initial : State := { queue with rootGroups :=
    queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref }
  have groups := loop (released.newGroups.map Execution.DeliveryNode.ref)
    (initial, []) live (.silent (fun _ retired => retired))
  apply groups.post
  intro ref retired
  let folded := (released.newGroups.map Execution.DeliveryNode.ref).foldl step (initial, [])
  change (released.newStreams.map Execution.DeliveryNode.ref).foldl State.startStream
    folded.1 |>.RetiredGroup ref
  have nodes := fold_projection State.groupNodes State.startStream
    State.startStream_groupNodes (released.newStreams.map Execution.DeliveryNode.ref) folded.1
  have registry := fold_projection State.registeredGroups State.startStream
    (fun current ref => by unfold State.startStream; split <;> rfl)
    (released.newStreams.map Execution.DeliveryNode.ref) folded.1
  simpa only [State.RetiredGroup, nodes, registry] using retired

/-- Local startup failures name distinct refs, each permanently retired by activation.
This exposes the existing transition accounting without adding runtime notification state.
-/
theorem State.startNewWork_failureRetirements {queue : State}
    (live : queue.LiveGroupsRegistered) (released : NewWork)
    (available : List (Occurrence × Nat))
    : (((queue.startNewWork released available).2).map
        (fun failure => failure.group.ref)).Nodup
      ∧ ∀ failure ∈ (queue.startNewWork released available).2,
          (queue.startNewWork released available).1.RetiredGroup failure.group.ref := by
  have accounted := startNewWork_closureAccounting live released available
  have projection (failures : List GroupFailureEvent)
      : (startupClosures failures).flatMap rawGroupClosureRefs
        = failures.map (fun failure => failure.group.ref) := by
    simp [startupClosures, List.flatMap_map, rawGroupClosureRefs, ← List.map_eq_flatMap]
  refine ⟨by simpa only [projection] using accounted.unique, ?_⟩
  intro failure member
  apply accounted.closed failure.group.ref
  rw [projection]
  exact List.mem_map_of_mem member

/-- Ready draining closes each immediate or queued group ref at most once.
Witness: compose each successful flush, its actual startup failures, and recursion. Enqueue
effects remain separate from immediate output while recording each removal once.
-/
theorem State.drainReadyGroups_go_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered)
    (fuel : Nat) (available : List (Occurrence × Nat) := [])
    : StartupClosureAccounting queue
        (State.drainReadyGroups.go available fuel queue) := by
  have loop (fuel : Nat) (current : State)
      (live : current.LiveGroupsRegistered)
      : StartupClosureAccounting current (State.drainReadyGroups.go available fuel current) := by
    induction fuel generalizing current with
    | zero => exact .silent (fun _ retired => retired)
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact .silent (fun _ retired => retired)
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
          have registered := live.finishGroupSuccess node
          have activated := registered.startNewWork
            (current.finishGroupSuccess node).2.2 available
          have first : StartupClosureAccounting current
              ((current.finishGroupSuccess node).1, (current.finishGroupSuccess node).2.1, []) := by
            simpa only [StartupClosureAccounting, startupClosures, List.map_nil,
              List.append_nil]
              using State.finishGroupSuccess_closureAccounting live node member
          have startup : StartupClosureAccounting (current.finishGroupSuccess node).1
              (((current.finishGroupSuccess node).1.startNewWork
                (current.finishGroupSuccess node).2.2 available).1, [],
                ((current.finishGroupSuccess node).1.startNewWork
                  (current.finishGroupSuccess node).2.2 available).2) :=
            startNewWork_closureAccounting registered _ available
          simpa only [List.append_nil, List.nil_append]
            using StartupClosureAccounting.append
              (StartupClosureAccounting.append first startup)
              (ih _ activated)
  exact loop fuel queue live

/-- The full drain inherits the same two-channel retirement evidence. -/
theorem State.drainReadyGroups_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered)
    (available : List (Occurrence × Nat) := [])
    : StartupClosureAccounting queue (queue.drainReadyGroups available) :=
  State.drainReadyGroups_go_closureAccounting live queue.groupNodes.length available

/-- Removing task memberships retains registration of every live group.
Witness: the mapped group keeps exactly its previous ref and registration entry.
-/
private theorem live_removeTask {queue : State} (live : queue.LiveGroupsRegistered)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).LiveGroupsRegistered := by
  intro node member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact live old oldMember

/-- A successful task preserves closure uniqueness across integration, owners, and draining.
Witness: child integration cannot revive retired refs; each live owner closes once, and
the exact single-pass output carries its retirement evidence into the final drain.
-/
theorem State.taskSuccess_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (occurrence : Occurrence) (result : TaskResult)
    (available : List (Occurrence × Nat) := [])
    : StartupClosureAccounting queue (queue.taskSuccess occurrence result available) := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (live : acc.1.LiveGroupsRegistered)
      (prior : GroupClosureAccounting queue (acc.1, acc.2.1))
      : let final := groups.foldl successGroupStep acc
        final.1.LiveGroupsRegistered ∧ GroupClosureAccounting queue (final.1, final.2.1) := by
    induction groups generalizing acc with
    | nil => exact ⟨live, prior⟩
    | cons group rest ih =>
        obtain ⟨current, events, released⟩ := acc
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ live prior
        · rename_i node found
          let updated := { node with pending := node.pending - 1 }
          have member := List.mem_of_find?_eq_some found
          have updatedLive := live.putGroupNode updated (live node member)
          have present : updated ∈ (current.putGroupNode updated).groupNodes := by
            apply List.mem_map.mpr ⟨node, member, ?_⟩
            simp [updated]
          have prepared := prior.post (fun _ retired => retired.putGroupNode updated)
          split
          · have registered := updatedLive.finishGroupSuccess updated
            exact ih _ registered
              (prepared.append (State.finishGroupSuccess_closureAccounting updatedLive
                updated present))
          · exact ih _ updatedLive prepared
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found, StartupClosureAccounting, startupClosures,
        List.map_nil, List.append_nil]
        using GroupClosureAccounting.silent (before := queue) (fun _ retired => retired)
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedLive : stored.LiveGroupsRegistered := live
      have registered := storedLive.maybeIntegrateWork result.work (some occurrence)
      have start : GroupClosureAccounting queue
          ((stored.maybeIntegrateWork result.work (some occurrence)).1, []) :=
        GroupClosureAccounting.silent (fun ref retired =>
          State.RetiredGroup.maybeIntegrateWork (queue := stored) retired _ _)
      obtain ⟨finalLive, closures⟩ := loop node.task.groups (_, [], {})
        registered start
      let folded := node.task.groups.foldl successGroupStep
        ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
      have activated := finalLive.startNewWork folded.2.2 available
      have first : StartupClosureAccounting queue (folded.1, folded.2.1, []) := by
        simpa only [StartupClosureAccounting, startupClosures, List.map_nil,
          List.append_nil]
          using closures
      have startup : StartupClosureAccounting folded.1
          ((folded.1.startNewWork folded.2.2 available).1, [],
            (folded.1.startNewWork folded.2.2 available).2) :=
        startNewWork_closureAccounting finalLive folded.2.2 available
      simpa only [List.append_nil, List.nil_append]
        using StartupClosureAccounting.append
          (StartupClosureAccounting.append first startup)
          (State.drainReadyGroups_closureAccounting activated available)

/-- Stream-item integration preserves old retirements before its group-closure drain.
Witness: matched child work retains registration; integration, pruning, and activation
cannot recreate an old group, and the stream carrier itself closes no group.
-/
theorem State.streamItems_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : StartupClosureAccounting queue (queue.streamItems stream items available) := by
  have loop (more : List StreamItem)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue × List GroupFailureEvent)
      (live : acc.1.LiveGroupsRegistered)
      (prior : GroupClosureAccounting queue (acc.1, startupClosures acc.2.2.2.2))
      : let final := more.foldl (fun acc item => streamItemStep acc item available) acc
        final.1.LiveGroupsRegistered ∧ GroupClosureAccounting queue (final.1, startupClosures final.2.2.2.2) := by
    induction more generalizing acc with
    | nil => exact ⟨live, prior⟩
    | cons item rest ih =>
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released : NewWork := { integrated.2 with newGroups := pruned.2 }
        have registered := live.integrateStreamItem item available
        have integratedReg := live.maybeIntegrateWork item.work
        have prunedReg := integratedReg.pruneEmptyGroups integrated.2.newGroups
        have prepared := prior.post (fun _ retired =>
          (retired.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups)
        apply ih _ registered
        simpa only [streamItemStep, startupClosures, List.map_append] using prepared.append
          (startNewWork_closureAccounting prunedReg released available)
  rw [queue.streamItems_eq stream items available]
  split
  · exact .silent (fun _ retired => retired)
  · let final := items.foldl (fun acc item => streamItemStep acc item available)
      (queue, [], [], [], [])
    obtain ⟨finalLive, closures⟩ := loop items
      (queue, [], [], [], []) live (.silent (fun _ retired => retired))
    have carrier : StartupClosureAccounting queue
        (final.1, [.streamValues stream final.2.2.2.1 final.2.1 final.2.2.1],
          final.2.2.2.2) := by
      exact ⟨by simpa only [List.singleton_append, List.flatMap_cons,
            rawGroupClosureRefs, List.nil_append]
          using closures.unique,
        by simpa only [List.singleton_append, List.flatMap_cons,
            rawGroupClosureRefs, List.nil_append]
          using closures.closed,
        closures.preserves,
        by simpa only [List.singleton_append, List.flatMap_cons,
            rawGroupClosureRefs, List.nil_append]
          using closures.excludes⟩
    exact StartupClosureAccounting.append carrier
      (State.drainReadyGroups_closureAccounting finalLive available)

/-- Ordinary handlers retire each newly closed or newly queued group once.
Forwarding an earlier pending control is handled separately as notification completion. -/
theorem State.handleGraphEvent_removalAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    (ordinary : ∀ failure, event ≠ .groupFailure failure)
    : StartupClosureAccounting queue (queue.handleGraphEvent event available) := by
  have cached := live.cacheTaskFailures available
  have initial : GroupClosureAccounting queue (queue.cacheTaskFailures available, []) :=
    .silent (fun _ retired => retired.cacheTaskFailures available)
  have after : StartupClosureAccounting (queue.cacheTaskFailures available)
      (queue.handleGraphEvent event available) := by
    cases event with
    | taskSuccess occurrence result =>
        exact State.taskSuccess_closureAccounting cached occurrence result available
    | taskFailure occurrence errors =>
        simpa only [State.handleGraphEvent, StartupClosureAccounting, startupClosures,
          List.map_nil, List.append_nil]
          using State.taskFailure_closureAccounting cached occurrence errors
    | streamItems stream items =>
        exact State.streamItems_closureAccounting cached stream items available
    | streamSuccess stream =>
        simp only [State.handleGraphEvent, State.streamSuccess]
        split <;> exact ⟨by simp [startupClosures, rawGroupClosureRefs],
          by simp [startupClosures, rawGroupClosureRefs], fun _ retired => retired,
          by simp [startupClosures, rawGroupClosureRefs]⟩
    | streamFailure stream errors =>
        simp only [State.handleGraphEvent, State.streamFailure]
        split <;> exact ⟨by simp [startupClosures, rawGroupClosureRefs],
          by simp [startupClosures, rawGroupClosureRefs], fun _ retired => retired,
          by simp [startupClosures, rawGroupClosureRefs]⟩
    | groupFailure notice => exact (ordinary notice rfl).elim
  exact initial.append after

/-- Actual dispatch distinguishes newly retired refs from consumed pending notices. -/
theorem State.dispatchGraphEvent_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (pending : queue.PendingGroupFailures)
    (event : GraphEvent) (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.PendingGroupFailures
      ∧ NotificationClosureAccounting queue
          (queue.dispatchGraphEvent event available) := by
  by_cases control : ∃ failure, event = .groupFailure failure
  · obtain ⟨failure, rfl⟩ := control
    have initial : NotificationClosureAccounting queue (queue.cacheTaskFailures available, []) :=
      .silent (fun _ closed => closed.cacheTaskFailures available)
    have next := (pending.cacheTaskFailures available).groupFailure failure
    have accounted := initial.append next.2
    simpa only [State.dispatchGraphEvent, State.handleGraphEvent, State.enqueueGroupFailures,
      List.append_nil, List.nil_append] using And.intro next.1 accounted
  · have ordinary : ∀ failure, event ≠ .groupFailure failure := by
      intro failure same; exact control ⟨failure, same⟩
    exact pending.enqueue_closureAccounting
      (queue.handleGraphEvent event available).2.1
      (queue.handleGraphEvent event available).2.2
      (State.handleGraphEvent_removalAccounting live event available ordinary)
      (queue.handleGraphEvent_groupFailureEvents_eq event available ordinary)

/-- FIFO replay retains the distinct pending inventory and closes each notification once. -/
theorem State.rawEventReplay_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (pending : queue.PendingGroupFailures)
    (events : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : (queue.rawEventReplay events available).1.PendingGroupFailures
      ∧ NotificationClosureAccounting queue (queue.rawEventReplay events available) := by
  induction events generalizing queue with
  | nil => exact ⟨pending, .silent (fun _ closed => closed)⟩
  | cons event rest ih =>
      have first := State.dispatchGraphEvent_closureAccounting live pending event available
      have later := ih (live.dispatchGraphEvent event available) first.1
      rw [State.rawEventReplay_cons queue event rest available]
      exact ⟨later.1, first.2.append later.2⟩

/-- The state-only FIFO view retains the same derived pending-notice invariant. -/
theorem State.PendingGroupFailures.replayGraphEvents {queue : State}
    (pending : queue.PendingGroupFailures) (live : queue.LiveGroupsRegistered)
    (events : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).PendingGroupFailures := by
  have next := (State.rawEventReplay_closureAccounting live pending events available).1
  rwa [State.rawEventReplay_state queue events available] at next

/-- Batch termination preserves pending identities and notification completion accounting. -/
theorem State.handleGraphEvents_closureAccounting {queue : State}
    (live : queue.LiveGroupsRegistered) (pending : queue.PendingGroupFailures)
    (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.PendingGroupFailures
      ∧ NotificationClosureAccounting queue (queue.handleGraphEvents events) := by
  have prior := State.rawEventReplay_closureAccounting live pending events
    (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact ⟨pending, .silent (fun _ closed => closed)⟩
  · dsimp only
    split
    · refine ⟨⟨prior.1.unique, prior.1.retired⟩, ⟨?_, ?_, ?_, ?_⟩⟩
      · simpa only [List.flatMap_append, List.flatMap_singleton, rawGroupClosureRefs,
          List.append_nil] using prior.2.unique
      · intro ref member
        apply prior.2.closed ref
        simpa only [List.flatMap_append, List.flatMap_singleton, rawGroupClosureRefs,
          List.append_nil] using member
      · intro ref closed; exact prior.2.preserves ref closed
      · intro ref closed member
        apply prior.2.excludes ref closed
        simpa only [List.flatMap_append, List.flatMap_singleton, rawGroupClosureRefs,
          List.append_nil] using member
    · exact prior

/-- Arbitrary finite host batches retain the pending-notice invariant. -/
theorem State.PendingGroupFailures.runNormalized {queue : State}
    (pending : queue.PendingGroupFailures) (live : queue.LiveGroupsRegistered)
    (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1.PendingGroupFailures := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue with
  | nil => exact pending
  | cons batch rest ih =>
      exact ih (State.handleGraphEvents_closureAccounting live pending batch).1
        (live.handleGraphEvents batch)

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
theorem State.runNormalized_groupClosures {queue : State}
    (live : queue.LiveGroupsRegistered) (pending : queue.PendingGroupFailures)
    (batches : List (List GraphEvent))
    : ((queue.runNormalized batches).2.flatten.flatMap groupClosureRefs).Nodup
      ∧ ∀ ref ∈ (queue.runNormalized batches).2.flatten.flatMap groupClosureRefs,
          (queue.runNormalized batches).1.RetiredGroup ref := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (live : acc.1.LiveGroupsRegistered) (pending : acc.1.PendingGroupFailures)
      (unique : (acc.2.2.flatten.flatMap groupClosureRefs).Nodup)
      (closed : ∀ ref ∈ acc.2.2.flatten.flatMap groupClosureRefs, acc.1.GroupClosed ref)
      : let final := more.foldl normalizedStep acc
        (final.2.2.flatten.flatMap groupClosureRefs).Nodup
        ∧ ∀ ref ∈ final.2.2.flatten.flatMap groupClosureRefs, final.1.GroupClosed ref := by
    induction more generalizing acc with
    | nil => exact ⟨unique, closed⟩
    | cons batch rest ih =>
        obtain ⟨next, accounted⟩ := State.handleGraphEvents_closureAccounting live pending batch
        apply ih
          (normalizedStep acc batch)
          (by rw [normalizedStep_queue]; exact live.handleGraphEvents batch)
          (by rw [normalizedStep_queue]; exact next)
        · rw [normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupClosureRefs]
          exact List.nodup_append.mpr ⟨unique, accounted.unique, by
            intro ref old other later equal
            subst other
            exact accounted.excludes ref (closed ref old) later⟩
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupClosureRefs]
          intro ref member
          exact (List.mem_append.mp member).elim
            (fun old => accounted.preserves ref (closed ref old))
            (fun added => accounted.closed ref added)
  have final := loop batches
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, []) live pending
    (by simp) (by simp)
  exact ⟨final.1, fun ref member => (final.2 ref member).1⟩

/-- Actual initialization and dispatch close each group ref at most once.
The result holds even without source matching or accepted-start premises. -/
theorem createWorkQueue_runNormalized_groupClosuresUnique {work : Execution.Work}
    {batches : List (List GraphEvent)}
    (_matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : (((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten.flatMap
        groupClosureRefs).Nodup :=
  (State.runNormalized_groupClosures (createWorkQueue_liveGroupsRegistered _)
    (createWorkQueue_pendingGroupFailures _) batches).1

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
