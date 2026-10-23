import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrors

/-! Rejection provenance under a fixed finite host-batch availability snapshot. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Fold induction threads a state invariant through the actual transition sequence. -/
private theorem fold_preserves {α β : Type} (property : β → Prop)
    (step : β → α → β) (items : List α)
    (preserved : ∀ state item, property state → property (step state item))
    (state : β) (valid : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact valid
  | cons item rest ih => exact ih _ (preserved state item valid)

/-- Exposing a batch's rejection caches retains a licensed task contributor. -/
theorem State.CachedErrorsSatisfy.cacheTaskFailures {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.cacheTaskFailures available).CachedErrorsSatisfy property := by
  induction available generalizing queue with
  | nil => exact supported
  | cons entry rest ih =>
      have tailLicensed : ∀ task, TaskMatches work task → ∀ errors,
          (task.occurrence, errors) ∈ rest → ∀ group ∈ task.groups, property group.ref errors :=
        fun task known errors member => licensed task known errors (List.mem_cons_of_mem _ member)
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih supported registered matching tailLicensed
      · rename_i node found
        have live := List.mem_of_find?_eq_some found
        have same : node.task.occurrence = entry.1 :=
          (occurrence_beq_iff_eq _ _).mp (List.find?_some
            (p := fun candidate : TaskNode => candidate.task.occurrence == entry.1) found)
        have updated := supported.putTaskNode { node with rejection := some entry.2 }
          (by
            intro errors rejected
            cases Option.some.inj rejected
            exact licensed node.task (matching node.task (registered node live)) entry.2
              (same ▸ List.mem_cons_self))
        exact ih updated (registered.putTaskNode _ (registered node live)) matching tailLicensed

/-- A newly started computation may immediately expose its available rejection. -/
theorem State.CachedErrorsSatisfy.startTask_available {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.startTask occurrence available).CachedErrorsSatisfy property := by
  unfold State.startTask
  split
  · exact supported
  · split
    · exact supported
    · rename_i task found
      intro node member errors rejected group contributes
      rcases List.mem_append.mp member with old | added
      · exact supported node old errors rejected group contributes
      · cases List.mem_singleton.mp added
        obtain ⟨⟨other, count⟩, inAvailable, selected⟩ :=
          List.exists_of_findSome?_eq_some rejected
        change (if other == occurrence then some count else none) = some errors at selected
        split at selected
        · rename_i equal
          have same : other = occurrence := (occurrence_beq_iff_eq _ _).mp equal
          have taskSame : task.occurrence = occurrence :=
            (occurrence_beq_iff_eq _ _).mp (List.find?_some
              (p := fun candidate : Task => candidate.occurrence == occurrence) found)
          cases Option.some.inj selected
          exact licensed task (matching task (List.mem_of_find?_eq_some found)) errors
            (taskSame.symm ▸ same ▸ inAvailable) group contributes
        · cases selected

/-- Startup preserves cache provenance even when it removes a rejected group. -/
theorem State.CachedErrorsSatisfy.startGroup_available {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.startGroup ref available).1.CachedErrorsSatisfy property := by
  have cached := supported.cacheTaskFailures registered matching available licensed
  have cachedMatch := matching.cacheTaskFailures available
  have tasks (items : List Occurrence) (current : State)
      (valid : current.CachedErrorsSatisfy property)
      (currentMatch : current.RegisteredTasksMatch work)
      : (items.foldl (fun current task => current.startTask task available)
          current).CachedErrorsSatisfy property := by
    induction items generalizing current with
    | nil => exact valid
    | cons task rest ih =>
        exact ih _ (valid.startTask_available currentMatch task available licensed)
          (currentMatch.startTask task available)
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact tasks _ _ cached cachedMatch
    · exact cached.removeGroup _

/-- Activation threads the batch's availability through every newly released group. -/
theorem State.CachedErrorsSatisfy.startNewWork_available {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (more : NewWork)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.startNewWork more available).1.CachedErrorsSatisfy property := by
  let invariant (current : State) := current.CachedErrorsSatisfy property
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (valid : invariant acc.1)
      : invariant (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1 := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih =>
        exact ih _ ⟨valid.1.startGroup_available valid.2.1 valid.2.2 ref available licensed,
          valid.2.1.startGroup ref available, valid.2.2.startGroup ref available⟩
  have streams (refs : NodeRefs) (current : State)
      (valid : current.CachedErrorsSatisfy property)
      : (refs.foldl State.startStream current).CachedErrorsSatisfy property := by
    induction refs generalizing current with
    | nil => exact valid
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact valid
  unfold State.startNewWork
  exact streams _ _ (groups _ _ ⟨supported, registered, matching⟩).1

/-- Ready-group draining preserves supported caches under a fixed batch snapshot. -/
theorem State.CachedErrorsSatisfy.drainReadyGroups_available {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.drainReadyGroups available).1.CachedErrorsSatisfy property := by
  let invariant (current : State) := current.CachedErrorsSatisfy property
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  have result := State.drainReadyGroups_preserves invariant
    (available := available) (fun _ node valid _ _ _ =>
      ⟨(valid.1.finishGroupSuccess node).startNewWork_available
          (valid.2.1.finishGroupSuccess node) (valid.2.2.finishGroupSuccess node)
          _ available licensed,
        (valid.2.1.finishGroupSuccess node).startNewWork _ available,
        (valid.2.2.finishGroupSuccess node).startNewWork _ available⟩)
    ⟨supported, registered, matching⟩
  exact result.1

/-- Successful task integration retains supported caches under batch availability. -/
theorem State.CachedErrorsSatisfy.taskSuccess_available {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence)
    (result : TaskResult) (childTasks : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.taskSuccess occurrence result available).1.CachedErrorsSatisfy property := by
  let invariant (current : State) := current.CachedErrorsSatisfy property
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  let step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode) :=
    let (current, outputs, released) := acc
    match current.groupNode? group.ref with
    | none => (current, outputs, released)
    | some old =>
        let node := { old with pending := old.pending - 1 }
        let current := current.putGroupNode node
        if current.rootGroups.contains group.ref && node.pending == 0 then
          let (next, finished, more) := current.finishGroupSuccess node
          (next, outputs ++ finished,
            ⟨released.newGroups ++ more.newGroups, released.newStreams ++ more.newStreams⟩)
        else (current, outputs, released)
  have stable (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (valid : invariant acc.1) : invariant (step acc group).1 := by
    obtain ⟨current, outputs, released⟩ := acc
    dsimp only [step]
    split
    · exact valid
    · rename_i node found
      have updated : invariant (current.putGroupNode { node with pending := node.pending - 1 }) :=
        ⟨valid.1.putGroupNode _, valid.2.1.putGroupNode _, valid.2.2.putGroupNode _⟩
      split
      · exact ⟨updated.1.finishGroupSuccess _, updated.2.1.finishGroupSuccess _,
          updated.2.2.finishGroupSuccess _⟩
      · exact updated
  unfold State.taskSuccess
  split
  · exact supported
  · rename_i taskNode found
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have before : invariant withValue :=
      ⟨supported.putTaskNode _ (supported taskNode (List.mem_of_find?_eq_some found)),
        registered.putTaskNode _ (registered taskNode (List.mem_of_find?_eq_some found)),
        matching⟩
    have integrated : invariant (withValue.maybeIntegrateWork result.work (some occurrence)).1 :=
      ⟨before.1.maybeIntegrateWork _ _, before.2.1.maybeIntegrateWork _ _,
        before.2.2.maybeIntegrateWork _ childTasks _⟩
    have released := fold_preserves (fun acc : State × List WorkQueueEvent × NewWork =>
      invariant acc.1) step taskNode.task.groups stable
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {}) integrated
    let finished := taskNode.task.groups.foldl step
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {})
    have started := released.1.startNewWork_available released.2.1 released.2.2
      finished.2.2 available licensed
    exact started.drainReadyGroups_available (released.2.1.startNewWork _ available)
      (released.2.2.startNewWork _ available) available licensed

/-- Stream children may start computations with already available rejections. -/
theorem State.CachedErrorsSatisfy.streamItems_available {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (childTasks : ∀ item ∈ items, ∀ task ∈ item.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.streamItems stream items available).1.CachedErrorsSatisfy property := by
  let invariant (current : State) := current.CachedErrorsSatisfy property
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List Execution.StreamItemValue × List GroupFailureEvent) (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    let (started, queued) := pruned.startNewWork { more with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ more.newStreams,
      values ++ [item.value], failures ++ queued)
  have stable (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List Execution.StreamItemValue × List GroupFailureEvent) (item : StreamItem)
      (member : item ∈ items) (valid : invariant acc.1) : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values, failures⟩ := acc
    have integrated : invariant (current.maybeIntegrateWork item.work).1 :=
      ⟨valid.1.maybeIntegrateWork _, valid.2.1.maybeIntegrateWork _,
        valid.2.2.maybeIntegrateWork _ (childTasks item member)⟩
    have pruned : invariant
        ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups
          (current.maybeIntegrateWork item.work).2.newGroups).1 :=
      ⟨integrated.1.pruneEmptyGroups _, integrated.2.1.pruneEmptyGroups _,
        integrated.2.2.pruneEmptyGroups _⟩
    exact ⟨pruned.1.startNewWork_available pruned.2.1 pruned.2.2 _ available licensed,
      pruned.2.1.startNewWork _ available, pruned.2.2.startNewWork _ available⟩
  have fold (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List Execution.StreamItemValue × List GroupFailureEvent)
      (valid : invariant acc.1) : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact valid
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (stable acc item (included List.mem_cons_self) valid)
  dsimp only [State.streamItems]
  split
  · exact supported
  · have final := fold items (List.Subset.refl _) (queue, [], [], [], [])
        ⟨supported, registered, matching⟩
    exact final.1.drainReadyGroups_available final.2.1 final.2.2 available licensed

/-- Dispatch preserves certified rejection facts from the batch's complete snapshot. -/
theorem State.CachedErrorsSatisfy.handleGraphEvent_available
    {queue : State} {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (eventMatch : event.MatchesWork work) (available : List (Occurrence × Nat))
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ available
              → ∀ group ∈ task.groups, property group.ref errors)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    : (queue.handleGraphEvent event available).1.CachedErrorsSatisfy property := by
  have cached := supported.cacheTaskFailures registered matching available licensed
  have cachedRegistered := registered.cacheTaskFailures available
  have cachedMatch := matching.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      apply cached.taskSuccess_available cachedRegistered cachedMatch occurrence result
        (available := available) (licensed := licensed)
      intro task member
      obtain ⟨address, payload, occurrenceEq, known⟩ := eventMatch.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, occurrenceEq, known⟩,
        eventMatch.childTask_groupsExact member⟩
  | groupFailure failure =>
      change ((queue.cacheTaskFailures available).groupFailure failure).1.CachedErrorsSatisfy property
      unfold State.groupFailure
      split
      · exact cached
      · split <;> exact cached
  | taskFailure occurrence errors =>
      apply cached.taskFailure occurrence errors
      intro node found
      have same : node.task.occurrence = occurrence :=
        (occurrence_beq_iff_eq _ _).mp (List.find?_some
          (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
      exact licensed node.task (cachedMatch node.task
        (cachedRegistered node (List.mem_of_find?_eq_some found))) errors
          (same.symm ▸ notified _ _ rfl)
  | streamItems stream items =>
      apply cached.streamItems_available cachedRegistered cachedMatch stream items
        (available := available) (licensed := licensed)
      intro item itemMember task taskMember
      obtain ⟨address, payload, occurrenceEq, known⟩ :=
        eventMatch.streamItem_childTask_producer itemMember taskMember
      exact ⟨⟨address, payload, some item.occurrence, occurrenceEq, known⟩,
        eventMatch.streamItem_childTask_groupsExact itemMember taskMember⟩
  | streamSuccess stream =>
      change ((queue.cacheTaskFailures available).streamSuccess
        stream).1.CachedErrorsSatisfy property
      unfold State.streamSuccess
      split <;> exact cached
  | streamFailure stream errors =>
      change ((queue.cacheTaskFailures available).streamFailure
        stream errors).1.CachedErrorsSatisfy property
      unfold State.streamFailure
      split <;> exact cached

/-- Batch cache exposure and FIFO dispatch preserve certified task rejections. -/
theorem State.CachedErrorsSatisfy.handleGraphEvents_available
    {queue : State} {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (batch : List GraphEvent)
    (allMatch : ∀ event ∈ batch, event.MatchesWork work)
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              (task.occurrence, errors) ∈ GraphEvent.availableFailures batch
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.handleGraphEvents batch).1.CachedErrorsSatisfy property := by
  let invariant (current : State) := current.CachedErrorsSatisfy property
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  let available := GraphEvent.availableFailures batch
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (next, produced) := acc.1.dispatchGraphEvent event available
    (next, acc.2 ++ produced)
  have fold (events : List GraphEvent) (included : events.Subset batch)
      (acc : State × List WorkQueueEvent) (valid : invariant acc.1)
      : invariant (events.foldl step acc).1 := by
    induction events generalizing acc with
    | nil => exact valid
    | cons event rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        have eventMember := included List.mem_cons_self
        refine ⟨valid.1.handleGraphEvent_available valid.2.1 valid.2.2 event
            (allMatch event eventMember) available licensed ?_,
          valid.2.1.handleGraphEvent event available,
          valid.2.2.handleGraphEvent event (allMatch event eventMember) available⟩
        intro occurrence errors same
        exact List.mem_filterMap.mpr ⟨event, eventMember, by simp [same]⟩
  unfold State.handleGraphEvents
  split
  · exact supported
  · let folded := batch.foldl step (queue, [])
    have final : folded.1.CachedErrorsSatisfy property :=
      (fold batch (List.Subset.refl _) (queue, []) ⟨supported, registered, matching⟩).1
    cases folded with
    | mk current outputs =>
        dsimp only at final ⊢
        split <;> exact final

/-- Normalized batch replay preserves exact rejection facts licensed by its inputs. -/
theorem State.CachedErrorsSatisfy.runNormalized_available {queue : State}
    {work : Execution.Work} {property : Nat → Nat → Prop}
    (supported : State.CachedErrorsSatisfy queue property)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (batches : List (List GraphEvent))
    (allMatch : ∀ event ∈ batches.flatten, event.MatchesWork work)
    (licensed
      : ∀ task,
          TaskMatches work task
          → ∀ errors,
              GraphEvent.taskFailure task.occurrence errors ∈ batches.flatten
              → ∀ group ∈ task.groups, property group.ref errors)
    : (queue.runNormalized batches).1.CachedErrorsSatisfy property := by
  let invariant (current : State) := current.CachedErrorsSatisfy property
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  have stable (acc : NormalizedAcc) (batch : List GraphEvent) (member : batch ∈ batches)
      (valid : invariant acc.1) : invariant (normalizedStep acc batch).1 := by
    have batchMatch : ∀ event ∈ batch, event.MatchesWork work := by
      intro event eventMember
      exact allMatch event (List.mem_flatten.mpr ⟨batch, member, eventMember⟩)
    have batchLicensed : ∀ task, TaskMatches work task → ∀ errors,
        (task.occurrence, errors) ∈ GraphEvent.availableFailures batch →
          ∀ group ∈ task.groups, property group.ref errors := by
      intro task known errors available
      obtain ⟨event, eventMember, same⟩ := List.mem_filterMap.mp available
      cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact licensed task known _ (List.mem_flatten.mpr ⟨batch, member, eventMember⟩)
    obtain ⟨current, publisher, outputs⟩ := acc
    have next : invariant (current.handleGraphEvents batch).1 :=
      ⟨valid.1.handleGraphEvents_available valid.2.1 valid.2.2 batch batchMatch batchLicensed,
        valid.2.1.handleGraphEvents batch, valid.2.2.handleGraphEvents batch batchMatch⟩
    dsimp only [normalizedStep]
    split <;> exact next
  have fold (more : List (List GraphEvent)) (included : more.Subset batches)
      (acc : NormalizedAcc) (valid : invariant acc.1)
      : invariant (more.foldl normalizedStep acc).1 := by
    induction more generalizing acc with
    | nil => exact valid
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (stable acc batch (included List.mem_cons_self) valid)
  exact (fold batches (List.Subset.refl _)
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, [])
    ⟨supported, registered, matching⟩).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
