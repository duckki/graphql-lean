import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.WorkDeclarations
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Concrete group notices cannot reintroduce refs closed earlier in the output. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Output-local freshness, composed using permanent concrete retirement
-----------------------------------------------------------------------------------------

/-- Group notices avoid `retired` refs and every closure at or before their carrier.
The predicate tracks outputs only; `retired` is supplied by concrete queue bookkeeping.
-/
def GroupNoticesFresh (retired : Nat → Prop) : List WorkQueueEvent → Prop
  | [] => True
  | event :: rest =>
      (∀ ref ∈ rawGroupNoticeRefs event, ¬retired ref ∧ ref ∉ rawGroupClosureRefs event)
      ∧ GroupNoticesFresh (fun ref => retired ref ∨ ref ∈ rawGroupClosureRefs event) rest

/-- Freshness against more excluded refs implies freshness against fewer refs.
Witness: list induction transports the old exclusion and retains each new closure.
-/
theorem GroupNoticesFresh.mono {first second : Nat → Prop} {events}
    (fresh : GroupNoticesFresh first events) (included : ∀ ref, second ref → first ref)
    : GroupNoticesFresh second events := by
  induction events generalizing first second with
  | nil => trivial
  | cons event rest ih =>
      exact ⟨fun ref member => ⟨fun old => (fresh.1 ref member).1 (included ref old),
        (fresh.1 ref member).2⟩,
        ih fresh.2 (fun ref => Or.imp (included ref) id)⟩

/-- Two fresh segments compose when the second excludes the first segment's closures.
Witness: list induction reassociates the accumulated closure-ref disjunction.
-/
theorem GroupNoticesFresh.append {retired : Nat → Prop} {first second}
    (left : GroupNoticesFresh retired first)
    (right
      : GroupNoticesFresh
          (fun ref => retired ref ∨ ref ∈ first.flatMap rawGroupClosureRefs) second)
    : GroupNoticesFresh retired (first ++ second) := by
  induction first generalizing retired with
  | nil => exact right.mono (fun _ old => .inl old)
  | cons event rest ih =>
      refine ⟨left.1, ih left.2 (right.mono ?_)⟩
      intro ref old
      simpa only [List.flatMap_cons, List.mem_append, or_assoc] using old

/-- Concrete retirement makes a later fresh segment exclude every earlier closure.
Witness: previous closures retire their refs, and the transition retains old retirements.
-/
theorem GroupNoticesFresh.then {before first second}
    (left : GroupNoticesFresh before.RetiredGroup first.2)
    (accounted : GroupClosureAccounting before first)
    (right : GroupNoticesFresh first.1.RetiredGroup second)
    : GroupNoticesFresh before.RetiredGroup (first.2 ++ second) := by
  exact left.append (right.mono (fun ref old => old.elim
    (accounted.preserves ref) (accounted.closed ref)))

/-- A segment without group notices is fresh for every prior exclusion set.
Witness: each recursive notice check has an empty domain, irrespective of closures.
-/
theorem GroupNoticesFresh.of_noNotices {retired : Nat → Prop} {events}
    (empty : ∀ event ∈ events, rawGroupNoticeRefs event = [])
    : GroupNoticesFresh retired events := by
  induction events generalizing retired with
  | nil => trivial
  | cons event rest ih =>
      exact ⟨
        by simp [empty event List.mem_cons_self],
        ih (fun next member => empty next (List.mem_cons_of_mem _ member))
      ⟩

-----------------------------------------------------------------------------------------
-- Pruning and successful release do not announce retired nodes
-----------------------------------------------------------------------------------------

/-- Pruning never returns a descriptor for a previously retired group.
Witness: the traversal skips absent refs; retained descriptors have a successful lookup,
and filtering empty shells preserves retirement. No tree or unique-ref premise is needed.
-/
theorem State.RetiredGroup.pruneEmptyGroups_not_announced {queue : State} {ref}
    (retired : queue.RetiredGroup ref) (groups : List Execution.DeliveryNode)
    : ref ∉ (queue.pruneEmptyGroups groups).2.map Execution.DeliveryNode.ref := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (old : current.RetiredGroup ref) (absent : ref ∉ kept.map Execution.DeliveryNode.ref)
      : ref ∉ (State.pruneEmptyGroups.go fuel current remaining kept).2.map
          Execution.DeliveryNode.ref := by
    induction fuel generalizing current remaining kept with
    | zero => exact absent
    | succ fuel ih =>
        cases remaining with
        | nil => exact absent
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ old absent
            · rename_i node found
              have different : ref ≠ group.ref := by
                intro same
                have impossible := same ▸ old.lookup_none
                rw [found] at impossible
                contradiction
              split
              · dsimp only
                refine ih _ _ _ ⟨old.1, ?_⟩ absent
                intro member
                obtain ⟨entry, kept, same⟩ := List.mem_map.mp member
                exact old.2 (List.mem_map.mpr ⟨entry, (List.mem_filter.mp kept).1, same⟩)
              · exact ih _ _ _ old (by simpa using And.intro absent different)
  have result := loop (queue.groupNodes.length + groups.length + 1) queue groups [] retired
    (by simp)
  intro member
  apply result
  simpa only [State.pruneEmptyGroups, List.mem_map] using member

/-- Successful release announces no previously retired group and never its closing ref.
Witness: task flushing preserves refs, own-group filtering removes the closing ref, and
pruning cannot reintroduce either kind of retired node.
-/
theorem State.finishGroupSuccess_groupNoticesFresh (queue : State) (node : GroupNode)
    (registered : node.group.node.ref ∈ queue.registeredGroups)
    : GroupNoticesFresh queue.RetiredGroup (queue.finishGroupSuccess node).2.1 := by
  let flushed := (node.tasks.foldl flushGroupTask (queue, [], [])).1
  have refs : flushed.groupNodes.map (fun entry => entry.group.node.ref)
      = queue.groupNodes.map (fun entry => entry.group.node.ref) := by
    apply fold_projection (fun acc : State × List ExecutionGroupValue × NodeRefs =>
      acc.1.groupNodes.map (fun entry => entry.group.node.ref)) flushGroupTask
    intro acc occurrence
    unfold flushGroupTask
    split <;> simp [State.removeTask, List.map_map, Function.comp_def]
  have registrations : flushed.registeredGroups = queue.registeredGroups := by
    apply fold_projection (fun acc : State × List ExecutionGroupValue × NodeRefs =>
      acc.1.registeredGroups) flushGroupTask
    intro acc occurrence
    unfold flushGroupTask
    split <;> rfl
  let current : State := { flushed with
    groupNodes := flushed.groupNodes.filter
      (fun entry => entry.group.node.ref != node.group.node.ref)
    rootGroups := flushed.rootGroups.filter (· != node.group.node.ref) }
  have oldRetired ref (old : queue.RetiredGroup ref) : current.RetiredGroup ref := by
    refine ⟨registrations.symm ▸ old.1, ?_⟩
    intro member
    obtain ⟨entry, kept, same⟩ := List.mem_map.mp member
    exact old.2 (refs ▸ List.mem_map.mpr ⟨entry, (List.mem_filter.mp kept).1, same⟩)
  have ownRetired : current.RetiredGroup node.group.node.ref := by
    refine ⟨registrations.symm ▸ registered, ?_⟩
    rintro member
    obtain ⟨entry, kept, same⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp kept).2
    simp [same] at different
  let children := node.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun child => child.group.node))
  have newRefs ref (member : ref ∈ (current.pruneEmptyGroups children).2.map
      Execution.DeliveryNode.ref)
      : ¬queue.RetiredGroup ref ∧ ref ≠ node.group.node.ref := by
    exact ⟨fun old => (oldRetired ref old).pruneEmptyGroups_not_announced children member,
      fun same => ownRetired.pruneEmptyGroups_not_announced children (same ▸ member)⟩
  change GroupNoticesFresh queue.RetiredGroup
    ((if _ then [] else [.groupValues _ _]) ++ [.groupSuccess _ _ _])
  split
  · exact ⟨fun ref member => by
      simpa only [rawGroupClosureRefs, List.mem_singleton] using newRefs ref member,
      trivial⟩
  · refine ⟨by simp [rawGroupNoticeRefs], ?_⟩
    exact ⟨fun ref member => ⟨fun old => (newRefs ref member).1
      (old.elim id (by simp [rawGroupClosureRefs])), by
        simpa only [rawGroupClosureRefs, List.mem_singleton] using
          (newRefs ref member).2⟩, trivial⟩

-----------------------------------------------------------------------------------------
-- Handler folds retain every earlier closure before emitting new notices
-----------------------------------------------------------------------------------------

/-- Recursive draining avoids notices for previously retired or completed groups.
Witness: each successful flush has fresh notices; startup preserves its retirement
certificate even when it removes cached-failed children before the next drain iteration.
-/
theorem State.drainReadyGroups_groupNoticesFresh {queue : State}
    (live : queue.LiveGroupsRegistered)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticesFresh queue.RetiredGroup (queue.drainReadyGroups available).2.1 := by
  have loop (fuel : Nat) (current : State)
      (live : current.LiveGroupsRegistered)
      : GroupNoticesFresh current.RetiredGroup
          (State.drainReadyGroups.go available fuel current).2.1 := by
    induction fuel generalizing current with
    | zero => trivial
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · trivial
        · rename_i node selected
          have member : node ∈ current.groupNodes := by
            obtain ⟨ref, _, choice⟩ := List.exists_of_findSome?_eq_some selected
            cases found : current.groupNode? ref with
            | none => simp [found] at choice
            | some candidate =>
                simp only [found] at choice
                change (if candidate.pending == 0 then some candidate else none) = some node
                  at choice
                split at choice
                · cases Option.some.inj choice
                  exact List.mem_of_find?_eq_some found
                · contradiction
          have activated := (live.finishGroupSuccess node).startNewWork
            (current.finishGroupSuccess node).2.2 available
          exact (current.finishGroupSuccess_groupNoticesFresh node
                  (live node member)).then
            ((State.finishGroupSuccess_closureAccounting live node member).post
              (fun _ retired => retired.startNewWork _ available))
            (ih _ activated)
  exact loop _ queue live

/-- A successful task's single-pass owner fold cannot reannounce an earlier closed group.
Witness: the same retirement certificates used for closure uniqueness thread each flush,
child activation, and the final drain. No output-admission premise is used.
-/
theorem State.taskSuccess_groupNoticesFresh {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered)
    {occurrence result}
    (_matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticesFresh queue.RetiredGroup
        (queue.taskSuccess occurrence result available).2.1 := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (live : acc.1.LiveGroupsRegistered)
      (prior : GroupClosureAccounting queue (acc.1, acc.2.1))
      (fresh : GroupNoticesFresh queue.RetiredGroup acc.2.1)
      : let final := groups.foldl successGroupStep acc
        final.1.LiveGroupsRegistered
        ∧ GroupClosureAccounting queue (final.1, final.2.1)
        ∧ GroupNoticesFresh queue.RetiredGroup final.2.1 := by
    induction groups generalizing acc with
    | nil => exact ⟨live, prior, fresh⟩
    | cons group rest ih =>
        obtain ⟨current, events, released⟩ := acc
        dsimp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ live prior fresh
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
              (fresh.then prepared (State.finishGroupSuccess_groupNoticesFresh _ updated
                (updatedLive updated present)))
          · exact ih _ updatedLive prepared fresh
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found, GroupNoticesFresh]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      have registered : (stored.maybeIntegrateWork result.work (some occurrence)).1.LiveGroupsRegistered :=
        (show stored.LiveGroupsRegistered from live).maybeIntegrateWork result.work (some occurrence)
      have start : GroupClosureAccounting queue
          ((stored.maybeIntegrateWork result.work (some occurrence)).1, []) :=
        GroupClosureAccounting.silent (fun ref retired =>
          State.RetiredGroup.maybeIntegrateWork (queue := stored) retired _ _)
      obtain ⟨finalLive, closures, fresh⟩ := loop node.task.groups (_, [], {})
        registered start trivial
      let folded := node.task.groups.foldl successGroupStep
        ((stored.maybeIntegrateWork result.work (some occurrence)).1, [], {})
      have activated := finalLive.startNewWork folded.2.2 available
      exact fresh.then (closures.post (fun _ retired => retired.startNewWork _ available))
        (State.drainReadyGroups_groupNoticesFresh activated available)

/-- Stream-item integration announces only groups not retired before the item batch.
Witness: each pruning result avoids old retirement, integration preserves retirement,
and the following group drain composes with the notice-only item carrier.
-/
theorem State.streamItems_groupNoticesFresh {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered)
    {stream items} (_matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticesFresh queue.RetiredGroup
        (queue.streamItems stream items available).2.1 := by
  let step := fun acc item => streamItemStep acc item available
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (live : acc.1.LiveGroupsRegistered)
      (retains : ∀ ref, queue.RetiredGroup ref → acc.1.RetiredGroup ref)
      (fresh : ∀ ref ∈ acc.2.1.map Execution.DeliveryNode.ref, ¬queue.RetiredGroup ref)
      : let final := more.foldl step acc
        final.1.LiveGroupsRegistered
        ∧ (∀ ref, queue.RetiredGroup ref → final.1.RetiredGroup ref)
        ∧ ∀ ref ∈ final.2.1.map Execution.DeliveryNode.ref, ¬queue.RetiredGroup ref := by
    induction more generalizing acc with
    | nil => exact ⟨live, retains, fresh⟩
    | cons item rest ih =>
        have registered := live.integrateStreamItem item available
        refine ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          registered (fun ref old =>
            State.RetiredGroup.startNewWork
              (((retains ref old).maybeIntegrateWork item.work).pruneEmptyGroups _) _ available)
          ?_
        intro ref member old
        change ref ∈ (acc.2.1 ++ _).map Execution.DeliveryNode.ref at member
        rw [List.map_append] at member
        rcases List.mem_append.mp member with earlier | added
        · exact fresh ref earlier old
        · exact ((retains ref old).maybeIntegrateWork item.work).pruneEmptyGroups_not_announced
            _ added
  unfold State.streamItems
  split
  · trivial
  · let final := items.foldl step (queue, [], [], [], [])
    obtain ⟨finalLive, retains, fresh⟩ := loop items (List.Subset.refl _)
      (queue, [], [], [], []) live (fun _ retired => retired) (by simp)
    have carrier : GroupClosureAccounting queue
        (final.1, [.streamValues stream final.2.2.2.1 final.2.1 final.2.2.1]) :=
      ⟨by simp [rawGroupClosureRefs], by simp [rawGroupClosureRefs], retains,
        by simp [rawGroupClosureRefs]⟩
    have notices : GroupNoticesFresh queue.RetiredGroup
        [.streamValues stream final.2.2.2.1 final.2.1 final.2.2.1] :=
      ⟨fun ref member => ⟨fresh ref member, by simp [rawGroupClosureRefs]⟩, trivial⟩
    exact notices.then carrier
      (State.drainReadyGroups_groupNoticesFresh finalLive available)

/-- Task failures cannot reannounce a group because they emit only failure completions.
Witness: the checked output-shape projections exclude both notice-bearing event kinds.
-/
theorem State.taskFailure_groupNoticesFresh (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : GroupNoticesFresh queue.RetiredGroup (queue.taskFailure occurrence errors).2 := by
  apply GroupNoticesFresh.of_noNotices
  intro event member
  cases event with
  | groupSuccess group groups streams =>
      exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups streams
        member)
  | streamValues stream values groups streams =>
      have impossible : stream.ref ∈
          (queue.taskFailure occurrence errors).2.flatMap rawStreamReferenceRefs :=
        List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩
      rw [State.taskFailure_streamReferences] at impossible
      cases impossible
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      rfl

/-- Every matching input handler preserves notice freshness against earlier group closures.
Witness: compose task and item release results; stream completions introduce no group notice.
-/
theorem State.handleGraphEvent_groupNoticesFresh {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticesFresh queue.RetiredGroup
        (queue.handleGraphEvent event available).2.1 := by
  have cached := live.cacheTaskFailures available
  have prior : ∀ ref, queue.RetiredGroup ref
      → (queue.cacheTaskFailures available).RetiredGroup ref :=
    fun _ retired => retired.cacheTaskFailures available
  cases event with
  | taskSuccess =>
      exact (State.taskSuccess_groupNoticesFresh cached matching available).mono prior
  | taskFailure occurrence errors =>
      exact ((queue.cacheTaskFailures available).taskFailure_groupNoticesFresh
        occurrence errors).mono prior
  | streamItems =>
      exact (State.streamItems_groupNoticesFresh cached matching available).mono prior
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [GroupNoticesFresh, rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [GroupNoticesFresh, rawGroupNoticeRefs]

  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · trivial
      · split <;> simp [GroupNoticesFresh, rawGroupNoticeRefs]

-----------------------------------------------------------------------------------------
-- Actual replay excludes reannouncement, independently of source timing or ownership
-----------------------------------------------------------------------------------------

/-- Raw replay never announces a group at or after a closure of the same ref.
Witness: actual registration coverage and permanent closure accounting compose each
handler's local freshness. Settlements need only match the supplied finite work.
-/
theorem State.rawEventReplay_groupNoticesFresh {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (pending : queue.PendingGroupFailures)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticesFresh queue.RetiredGroup (queue.rawEventReplay events available).2 := by
  induction events generalizing queue with
  | nil => trivial
  | cons event rest ih =>
      have matched := matching event List.mem_cons_self
      have step := queue.dispatchGraphEvent_closureAccounting live pending event available
      have fresh : GroupNoticesFresh queue.RetiredGroup
          (queue.dispatchGraphEvent event available).2 :=
        State.handleGraphEvent_groupNoticesFresh live event matched available
      have later := ih (live.dispatchGraphEvent event available) step.1
        (fun next member => matching next (List.mem_cons_of_mem _ member))
      rw [State.rawEventReplay_cons queue event rest available]
      exact fresh.append (later.mono (fun ref old => old.elim
        (fun retired => show (queue.dispatchGraphEvent event available).1.RetiredGroup ref from
          retired.handleGraphEvent event available)
        (fun member => (step.2.closed ref member).1)))

/-- Actual batching preserves notice freshness at every consumed FIFO control. -/
theorem State.handleGraphEvents_groupNoticesFresh {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (pending : queue.PendingGroupFailures)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : GroupNoticesFresh queue.RetiredGroup (queue.handleGraphEvents events).2 := by
  have prior := State.rawEventReplay_groupNoticesFresh live pending events matching
    (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · trivial
  · dsimp only
    split
    · exact prior.append (GroupNoticesFresh.of_noNotices (by simp [rawGroupNoticeRefs]))
    · exact prior

/-- Initial replay has no group reannouncement after completion.
The live and pending invariants follow from initialization for arbitrary internal work. -/
theorem createWorkQueue_rawEventReplay_groupNoticesFresh {work events}
    (valid : ValidGraphEvents work events)
    : GroupNoticesFresh (State.initialize (Work.fromExecution work)).RetiredGroup
        ((State.initialize (Work.fromExecution work)).rawEventReplay events).2 :=
  State.rawEventReplay_groupNoticesFresh (createWorkQueue_liveGroupsRegistered _)
    (createWorkQueue_pendingGroupFailures _) events
    (fun _ member => valid.event_matches member)

/-- Freshness yields no previous or same-event group closure at an indexed notice carrier.
Witness: list induction retains exactly the refs closed by the strict output prefix.
-/
theorem GroupNoticesFresh.atEvent {retired : Nat → Prop} {events index event}
    (fresh : GroupNoticesFresh retired events) (selected : events[index]? = some event)
    {ref} (notice : ref ∈ rawGroupNoticeRefs event)
    : ¬retired ref
      ∧ ref ∉ (events.take index).flatMap rawGroupClosureRefs
      ∧ ref ∉ rawGroupClosureRefs event := by
  induction events generalizing retired index with
  | nil => simp at selected
  | cons head rest ih =>
      cases index with
      | zero =>
          cases Option.some.inj selected
          exact ⟨(fresh.1 ref notice).1, by simp, (fresh.1 ref notice).2⟩
      | succ index =>
          obtain ⟨old, earlier, current⟩ := ih fresh.2 selected
          exact ⟨
            fun previous => old (.inl previous),
            by
              simpa only [List.take_succ_cons, List.flatMap_cons, List.mem_append, not_or]
                using And.intro (fun member => old (.inr member)) earlier,
            current
          ⟩

/-- Every output prefix inherits freshness with the same initial retirement predicate.
Witness: list induction discards only the unobserved suffix, retaining earlier closures.
-/
theorem GroupNoticesFresh.prefix {retired : Nat → Prop} {events before}
    (fresh : GroupNoticesFresh retired events) (isPrefix : before.IsPrefix events)
    : GroupNoticesFresh retired before := by
  obtain ⟨after, rfl⟩ := isPrefix
  induction before generalizing retired with
  | nil => trivial
  | cons event rest ih => exact ⟨fresh.1, ih fresh.2⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
