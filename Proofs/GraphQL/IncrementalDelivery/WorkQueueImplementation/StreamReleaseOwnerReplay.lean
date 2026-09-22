import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedStreamRelease

/-! Source handlers retain the contributing dependency of every group-carried stream. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The shared contributor fold keeps structural support through immediate flushes
-----------------------------------------------------------------------------------------

/-- One contributor step retains structural state evidence and all release dependencies.
Witness: a counter update changes no membership; its optional flush selects a live group
and appends only carriers with the proved contributing-owner witness.
-/
theorem successGroupStep_streamDependencies {work : Execution.Work}
    (generated : ExecutedWork work) (acc : State × List WorkQueueEvent × NewWork)
    (group : Execution.DeliveryNode) (sound : acc.1.GroupMembershipSound)
    (matching : acc.1.RegisteredTasksMatch work)
    (links : acc.1.ChildStreamsMatchWork work)
    (prior : StreamReleaseDependencies work acc.2.1)
    : (successGroupStep acc group).1.GroupMembershipSound
      ∧ (successGroupStep acc group).1.RegisteredTasksMatch work
      ∧ (successGroupStep acc group).1.ChildStreamsMatchWork work
      ∧ StreamReleaseDependencies work (successGroupStep acc group).2.1 := by
  obtain ⟨queue, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨sound, matching, links, prior⟩
  · rename_i node found
    have live := List.mem_of_find?_eq_some found
    let updated := { node with pending := node.pending - 1 }
    have currentSound := sound.putGroupNode updated (sound node live)
    have currentMatching := matching.putGroupNode updated
    have currentLinks := links.putGroupNode updated
    have currentLive : updated ∈ (queue.putGroupNode updated).groupNodes := by
      apply List.mem_map.mpr
      exact ⟨node, live, by simp [updated]⟩
    split
    · exact ⟨currentSound.finishGroupSuccess updated,
        currentMatching.finishGroupSuccess updated, currentLinks.finishGroupSuccess updated,
        prior.append ((queue.putGroupNode updated).finishGroupSuccess_streamDependencies
          generated currentSound currentMatching currentLinks currentLive)⟩
    · exact ⟨currentSound, currentMatching, currentLinks, prior⟩

/-- Task success supplies a contributing stream dependency across both release stages.
Witness: matched child integration installs structural provenance, the contributor fold
retains it through immediate flushes, and recursive draining proves the remaining carriers.
-/
theorem State.taskSuccess_streamDependencies {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) {occurrence result}
    (source : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : StreamReleaseDependencies work (queue.taskSuccess occurrence result).2 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      exact (by
        simpa only [State.taskSuccess, found] using StreamReleaseDependencies.nil work)
  | some node =>
      obtain ⟨member, _⟩ := State.taskNode?_some found
      let stored := queue.putTaskNode { node with value := some result.value }
      have storedSound : stored.GroupMembershipSound := sound
      have storedMatching : stored.RegisteredTasksMatch work := matching
      have storedLinks := links.putTaskNode { node with value := some result.value }
        (links node member)
      have integratedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
      have integratedMatching := storedMatching.maybeIntegrateWork result.work (by
        intro task supplied
        obtain ⟨address, payload, equal, known⟩ := source.childTask_producer supplied
        exact ⟨⟨address, payload, some occurrence, equal, known⟩,
          source.childTask_groupsExact supplied⟩) (some occurrence)
      have integratedLinks := storedLinks.maybeIntegrateWork result.work (some occurrence) (by
        intro producer equal stream supplied
        cases equal
        exact source.childStream_producer supplied)
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent × NewWork)
          (sound : acc.1.GroupMembershipSound) (matching : acc.1.RegisteredTasksMatch work)
          (links : acc.1.ChildStreamsMatchWork work)
          (prior : StreamReleaseDependencies work acc.2.1)
          : (groups.foldl successGroupStep acc).1.GroupMembershipSound
            ∧ (groups.foldl successGroupStep acc).1.RegisteredTasksMatch work
            ∧ (groups.foldl successGroupStep acc).1.ChildStreamsMatchWork work
            ∧ StreamReleaseDependencies work (groups.foldl successGroupStep acc).2.1 := by
        induction groups generalizing acc with
        | nil => exact ⟨sound, matching, links, prior⟩
        | cons group rest ih =>
            obtain ⟨nextSound, nextMatching, nextLinks, output⟩ :=
              successGroupStep_streamDependencies generated acc group sound matching links prior
            exact ih _ nextSound nextMatching nextLinks output
      obtain ⟨nextSound, nextMatching, nextLinks, output⟩ := loop node.task.groups (_, [], {})
        integratedSound integratedMatching integratedLinks (.nil work)
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact .nil work
      · exact output.append (State.drainReadyGroups_streamDependencies generated
          (nextSound.startNewWork _) (nextMatching.startNewWork _) (nextLinks.startNewWork _))

-----------------------------------------------------------------------------------------
-- Item integration may expose stored groups; only its final drain releases their streams
-----------------------------------------------------------------------------------------

/-- Item batches retain support for every group-produced stream released by their drain.
Witness: matched item-child tasks preserve membership provenance; parentless integration
preserves existing stream links, and the leading item event is not a group carrier.
-/
theorem State.streamItems_streamDependencies {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) {stream items}
    (source : (GraphEvent.streamItems stream items).MatchesWork work)
    : StreamReleaseDependencies work (queue.streamItems stream items).2 := by
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
      (sound : acc.1.GroupMembershipSound) (matching : acc.1.RegisteredTasksMatch work)
      (links : acc.1.ChildStreamsMatchWork work)
      : (more.foldl step acc).1.GroupMembershipSound
        ∧ (more.foldl step acc).1.RegisteredTasksMatch work
        ∧ (more.foldl step acc).1.ChildStreamsMatchWork work := by
    induction more generalizing acc with
    | nil => exact ⟨sound, matching, links⟩
    | cons item rest ih =>
        have tasks : ∀ task ∈ item.work.tasks, TaskMatches work task := by
          intro task member
          obtain ⟨address, payload, equal, known⟩ :=
            source.streamItem_childTask_producer (included List.mem_cons_self) member
          exact ⟨⟨address, payload, some item.occurrence, equal, known⟩,
            source.streamItem_childTask_groupsExact (included List.mem_cons_self) member⟩
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (((sound.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
          (((matching.maybeIntegrateWork item.work tasks).pruneEmptyGroups _).startNewWork
            _)
          (((links.integrateRoots item.work).pruneEmptyGroups _).startNewWork _)
  obtain ⟨nextSound, nextMatching, nextLinks⟩ :=
    loop items (fun _ member => member) (queue, [], [], []) sound matching links
  unfold State.streamItems
  split
  · exact .nil work
  · intro group groups streams member
    have later := (List.mem_cons.mp member).resolve_left (by intro impossible; cases impossible)
    exact State.drainReadyGroups_streamDependencies generated nextSound nextMatching nextLinks
      group groups streams later

/-- Every matched source handler emits structurally supported group-carried stream notices.
Witness: task/item successes use their release theorems; errors and stream closure emit
no successful group carrier. This result does not assume source freshness or health.
-/
theorem State.handleGraphEvent_streamDependencies {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) (event : GraphEvent)
    (source : event.MatchesWork work)
    : StreamReleaseDependencies work (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess =>
      exact queue.taskSuccess_streamDependencies generated sound matching links source
  | streamItems =>
      exact queue.streamItems_streamDependencies generated sound matching links source
  | taskFailure occurrence errors =>
      intro group groups streams member
      exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors group groups streams
        member)
  | streamSuccess stream =>
      intro group groups streams member
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      intro group groups streams member
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member

-----------------------------------------------------------------------------------------
-- Actual batching and publisher normalization preserve the unmodified success carrier
-----------------------------------------------------------------------------------------

/-- Raw replay preserves structural dependency witnesses for every successful carrier.
Witness: induct through source handlers, preserving the independently proved membership,
task-provenance, and child-link invariants at each next-handler boundary.
-/
theorem State.rawEventReplay_streamDependencies {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) (received : List GraphEvent)
    (sources : ∀ event ∈ received, event.MatchesWork work)
    : StreamReleaseDependencies work (queue.rawEventReplay received).2 := by
  induction received generalizing queue with
  | nil => exact .nil work
  | cons event rest ih =>
      have source := sources event List.mem_cons_self
      rw [State.rawEventReplay_cons]
      exact (queue.handleGraphEvent_streamDependencies generated sound matching links event
        source).append (ih (sound.handleGraphEvent event)
          (matching.handleGraphEvent event source) (links.handleGraphEvent source)
          (fun next member => sources next (List.mem_cons_of_mem _ member)))

/-- The executable batch wrapper adds no group-success carrier of its own.
Witness: apply raw replay; terminal bookkeeping only appends termination or emits nothing.
-/
theorem State.handleGraphEvents_streamDependencies {queue : State} {work : Execution.Work}
    (generated : ExecutedWork work) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    (links : queue.ChildStreamsMatchWork work) (received : List GraphEvent)
    (sources : ∀ event ∈ received, event.MatchesWork work)
    : StreamReleaseDependencies work (queue.handleGraphEvents received).2 := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact .nil work
  · have raw := queue.rawEventReplay_streamDependencies generated sound matching links
      received sources
    dsimp only
    split
    · exact raw.append (by intro group groups streams impossible; simp at impossible)
    · exact raw

/-- Normalized group-success carriers retain their streams' contributing dependencies.
The publisher may remap value owners, but not these success-carrier descriptors.
-/
def NormalizedStreamReleaseDependencies (work : Execution.Work)
    (events : List Execution.WorkQueueEvent)
    : Prop :=
  ∀ group groups streams,
    Execution.WorkQueueEvent.groupSuccess group groups streams ∈ events
    → ∀ stream ∈ streams,
        ∀ dependencies producer,
          NodeAt work stream .stream dependencies producer → group.key ∈ dependencies

/-- Publisher normalization preserves every successful carrier's dependency witness.
Witness: the normalized carrier has an identical raw predecessor; value-owner remapping
cannot introduce, remove, or change a group-success carrier.
-/
theorem StreamReleaseDependencies.normalizeBatch {work events}
    (supported : StreamReleaseDependencies work events) (publisher : IncrementalPublisher)
    : NormalizedStreamReleaseDependencies work (publisher.normalizeBatch events).2 := by
  intro group groups streams member
  obtain ⟨index, atEvent⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨rawIndex, rawEvent, _⟩ := publisher.normalizeBatch_groupSuccess events atEvent
  exact supported group groups streams (List.mem_of_getElem? rawEvent)

/-- Concatenated normalized output retains each carrier's dependency witness.
Witness: split event membership between the two unchanged output segments.
-/
theorem NormalizedStreamReleaseDependencies.append {work left right}
    (before : NormalizedStreamReleaseDependencies work left)
    (after : NormalizedStreamReleaseDependencies work right)
    : NormalizedStreamReleaseDependencies work (left ++ right) := by
  intro group groups streams member
  rcases List.mem_append.mp member with earlier | later
  · exact before group groups streams earlier
  · exact after group groups streams later

/-- Every actual normalized group-carried stream has its carrier among its dependencies.
Witness: initialization supplies all structural state premises; matched source replay
preserves them through both flush paths and publisher normalization. This theorem needs
no output admission, health hypothesis, start discipline, or source freshness assumption.
-/
theorem createWorkQueue_runNormalized_streamReleaseDependencies {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (sources : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : NormalizedStreamReleaseDependencies work
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).2.flatten := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (sound : acc.1.GroupMembershipSound) (matching : acc.1.RegisteredTasksMatch work)
      (links : acc.1.ChildStreamsMatchWork work)
      (prior : NormalizedStreamReleaseDependencies work acc.2.2.flatten)
      (sources : ∀ event ∈ more.flatten, event.MatchesWork work)
      : NormalizedStreamReleaseDependencies work
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc with
    | nil => exact prior
    | cons batch rest ih =>
        have first : ∀ event ∈ batch, event.MatchesWork work :=
          fun event member => sources event (List.mem_append_left _ member)
        have nextSound : (normalizedStep acc batch).1.GroupMembershipSound := by
          rw [normalizedStep_queue]
          exact sound.handleGraphEvents batch
        have nextMatching : (normalizedStep acc batch).1.RegisteredTasksMatch work := by
          rw [normalizedStep_queue]
          exact matching.handleGraphEvents batch first
        have nextLinks : (normalizedStep acc batch).1.ChildStreamsMatchWork work := by
          rw [normalizedStep_queue]
          exact links.handleGraphEvents batch first
        have output : NormalizedStreamReleaseDependencies work
            (normalizedStep acc batch).2.2.flatten := by
          rw [normalizedStep_flatten]
          exact prior.append ((acc.1.handleGraphEvents_streamDependencies generated sound
            matching links batch first).normalizeBatch acc.2.1)
        exact ih _ nextSound nextMatching nextLinks output
          (fun event member => sources event (List.mem_append_right _ member))
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  exact loop batches (queue, publisher, []) (createWorkQueue_groupMembershipSound _)
    (createWorkQueue_fromSpec_registeredTasksMatch _)
    (createWorkQueue_childStreamsMatchWork _ _)
    (by
      intro group groups streams impossible
      cases impossible)
    sources

/-- Every actual group-carried stream has a contributing dependency retired by replay.
Witness: combine structural carrier preservation with independent closure accounting;
retirement persists through all later batches. Uncancelledness and failure-cut health
are deliberately not inferred from this structural certificate alone.
-/
theorem createWorkQueue_runNormalized_streamRetiredDependency {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (sources : ∀ event ∈ batches.flatten, event.MatchesWork work)
    {group groups streams stream dependencies producer}
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    (released : stream ∈ streams)
    (known : NodeAt work stream .stream dependencies producer)
    : group.key ∈ dependencies
      ∧ ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.RetiredGroup
          group.key := by
  refine ⟨createWorkQueue_runNormalized_streamReleaseDependencies generated batches sources
    group groups streams carrier stream released dependencies producer known, ?_⟩
  exact (State.runNormalized_groupClosures (createWorkQueue_registration work).1
    (createWorkQueue_registration work).2 batches sources).2 group.key
      (List.mem_flatMap.mpr ⟨_, carrier, List.mem_cons_self⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
