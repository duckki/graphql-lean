import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementStability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulCarrierOrigins

/-! Successful carriers retain known uncancelled retirements independently of failure counts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each successful carrier names a known group that is retired without cancellation. -/
def SuccessfulGroupRetirements (queue : State) (work : Execution.Work)
    (events : List Execution.WorkQueueEvent)
    : Prop :=
  ∀ group groups streams,
    .groupSuccess group groups streams ∈ events
    → ∃ dependencies,
        GroupRecordAt work group dependencies ∧ UncancelledRetirement queue group.ref

private theorem SuccessfulGroupRetirements.post {before after work events}
    (prior : SuccessfulGroupRetirements before work events)
    (preserved
      : ∀ ref, UncancelledRetirement before ref → UncancelledRetirement after ref)
    : SuccessfulGroupRetirements after work events := by
  intro group groups streams member
  obtain ⟨dependencies, known, retired⟩ := prior group groups streams member
  exact ⟨dependencies, known, preserved _ retired⟩

private theorem SuccessfulGroupRetirements.append {queue work first second}
    (left : SuccessfulGroupRetirements queue work first)
    (right : SuccessfulGroupRetirements queue work second)
    : SuccessfulGroupRetirements queue work (first ++ second) := by
  intro group groups streams member
  exact (List.mem_append.mp member).elim (left group groups streams) (right group groups streams)

private structure CarrierFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs)
    : Prop where
  parent : ParentCutFrame queue work parents
  cancelled : queue.CancellationsRetired

private theorem CarrierFrame.finishGroupSuccess {queue work parents}
    (frame : CarrierFrame queue work parents) (node : GroupNode)
    (member : node ∈ queue.groupNodes)
    : CarrierFrame (queue.finishGroupSuccess node).1 work parents
      ∧ SuccessfulGroupRetirements (queue.finishGroupSuccess node).1 work
          (queue.finishGroupSuccess node).2.1 := by
  refine ⟨
    ⟨frame.parent.finishGroupSuccess node, frame.cancelled.finishGroupSuccess node⟩,
    ?_
  ⟩
  have safeRetirement : UncancelledRetirement (queue.finishGroupSuccess node).1
      node.group.node.ref := by
    refine ⟨queue.finishGroupSuccess_retires node (frame.parent.live node member), ?_⟩
    rw [State.finishGroupSuccess_cancelledGroups]
    exact frame.cancelled.live_uncancelled member
  intro group groups streams included
  obtain ⟨dependencies, known⟩ := frame.parent.records node member
  obtain ⟨_, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output] at included
  have same : group = node.group.node := by
    split at included <;> simp_all
  exact ⟨dependencies, same ▸ known, same ▸ safeRetirement⟩

private theorem CarrierFrame.startNewWork {queue work parents}
    (frame : CarrierFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (released : NewWork) (available : List (Occurrence × Nat))
    : CarrierFrame (queue.startNewWork released available).1 work parents :=
  ⟨
    frame.parent.startNewWork generated canonical released available,
    frame.cancelled.startNewWork frame.parent.live released available
  ⟩

private theorem CarrierFrame.drainReadyGroups_go {queue work parents}
    (frame : CarrierFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (fuel : Nat) (available : List (Occurrence × Nat))
    : CarrierFrame (State.drainReadyGroups.go available fuel queue).1 work parents
      ∧ SuccessfulGroupRetirements (State.drainReadyGroups.go available fuel queue).1 work
          (State.drainReadyGroups.go available fuel queue).2.1 := by
  induction fuel generalizing queue with
  | zero => exact ⟨frame, by intro group groups streams impossible; cases impossible⟩
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact ⟨frame, by intro group groups streams impossible; cases impossible⟩
      · rename_i node selected
        have member : node ∈ queue.groupNodes := by
          obtain ⟨ref, _, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : queue.groupNode? ref with
          | none => simp [found] at choice
          | some chosen =>
              simp only [found] at choice
              change (if chosen.pending == 0 then some chosen else none) = some node at choice
              split at choice
              · cases Option.some.inj choice
                exact List.mem_of_find?_eq_some found
              · cases choice
        have closed := frame.finishGroupSuccess node member
        have started := closed.1.startNewWork generated canonical
          (queue.finishGroupSuccess node).2.2 available
        have later := ih started
        refine ⟨later.1, (closed.2.post (fun ref prior => ?_)).append later.2⟩
        have active := prior.startNewWork (queue.finishGroupSuccess node).2.2 available
        exact State.drainReadyGroups_go_preserves
          (fun current => UncancelledRetirement current ref)
          (fun _ group prior _ _ _ =>
            (prior.finishGroupSuccess group).startNewWork _ available)
          active fuel (available := available)

private theorem CarrierFrame.successGroupFold {queue work parents}
    (frame : CarrierFrame queue work parents) (groups : List Execution.DeliveryNode)
    : let released := groups.foldl successGroupStep (queue, [], {})
      CarrierFrame released.1 work parents
      ∧ SuccessfulGroupRetirements released.1 work released.2.1 := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List Execution.WorkQueueEvent × NewWork)
      (frame : CarrierFrame acc.1 work parents)
      (output : SuccessfulGroupRetirements acc.1 work acc.2.1)
      : let released := groups.foldl successGroupStep acc
        CarrierFrame released.1 work parents
          ∧ SuccessfulGroupRetirements released.1 work released.2.1 := by
    induction groups generalizing acc with
    | nil => exact ⟨frame, output⟩
    | cons group rest ih =>
        rw [List.foldl_cons]
        apply ih
        all_goals
          unfold successGroupStep
          dsimp only
          split
          · assumption
          · rename_i node found
            let updated := { node with pending := node.pending - 1 }
            have parent := frame.parent.putGroupNode found updated rfl rfl
            have changed : CarrierFrame (acc.1.putGroupNode updated) work parents :=
              ⟨parent, frame.cancelled.putGroupNode updated⟩
            have prior := output.post (fun _ prior => prior.putGroupNode updated)
            split
            · have member : updated ∈ (acc.1.putGroupNode updated).groupNodes :=
                List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, by simp [updated]⟩
              first
              | exact (changed.finishGroupSuccess updated member).1
              | exact (prior.post (fun _ prior => prior.finishGroupSuccess updated)).append
                  (changed.finishGroupSuccess updated member).2
            · assumption
  exact loop groups (queue, [], {}) frame
    (by intro group groups streams impossible; cases impossible)

private theorem CarrierFrame.taskSuccess {queue work parents}
    (frame : CarrierFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {occurrence result}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat))
    : SuccessfulGroupRetirements (queue.taskSuccess occurrence result available).1 work
        (queue.taskSuccess occurrence result available).2.1 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]; intro group groups streams impossible; cases impossible
  | some node =>
      let stored := queue.putTaskNode { node with value := some result.value }
      have parent : ParentCutFrame stored work parents :=
        ⟨frame.parent.safe, frame.parent.keys, frame.parent.records, frame.parent.links,
          frame.parent.children, frame.parent.live, frame.parent.tasks, frame.parent.closed,
          frame.parent.fields, frame.parent.complete, frame.parent.cancelled,
          frame.parent.registration.putTaskNode _ (frame.parent.registration.started node
            (List.mem_of_find?_eq_some found))⟩
      have certificate := (frame.parent.registration.children node.task
        (frame.parent.registration.started node (List.mem_of_find?_eq_some found))).sourceChild
          (State.taskNode?_some found).2 matching
      have integrated : CarrierFrame (stored.maybeIntegrateWork result.work
          (some occurrence)).1 work parents :=
        ⟨parent.maybeIntegrateWork result.work
          (fun _ member => matching.taskChildGroups_recordAt member)
          (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
          certificate (some occurrence) generated canonical, (frame.cancelled.putTaskNode
            { node with value := some result.value }).maybeIntegrateWork result.work
              (some occurrence)⟩
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := node.task.groups.foldl successGroupStep (prepared, [], {})
      have folded := integrated.successGroupFold node.task.groups
      have started := folded.1.startNewWork generated canonical released.2.2 available
      have drained := started.drainReadyGroups_go generated canonical
        (released.1.startNewWork released.2.2 available).1.groupNodes.length available
      rw [queue.taskSuccess_eq occurrence result node found available]
      exact (folded.2.post (fun _ prior => (prior.startNewWork released.2.2 available
        ).drainReadyGroups available)).append drained.2

private theorem CarrierFrame.integrateStreamItem {queue work parents stream items item}
    (frame : CarrierFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (available : List (Occurrence × Nat))
    : CarrierFrame (queue.integrateStreamItem item available) work parents := by
  have singleton : (GraphEvent.streamItems stream [item]).MatchesWork work := by
    intro next listed
    cases List.mem_singleton.mp listed
    exact matching item member
  exact ⟨
    frame.parent.integrateStreamItem generated canonical matching member available,
    frame.cancelled.preparedStreamItems frame.parent.live frame.parent.tasks singleton
      available
  ⟩

private theorem CarrierFrame.streamItems {queue work parents stream items}
    (frame : CarrierFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : SuccessfulGroupRetirements (queue.streamItems stream items available).1 work
        (queue.streamItems stream items available).2.1 := by
  have prepared := State.preparedStreamItems_preserves
    (fun current => CarrierFrame current work parents) frame items available
    (fun _ item member prior =>
      prior.integrateStreamItem generated canonical matching member available)
  have drained := prepared.drainReadyGroups_go generated canonical
    (queue.preparedStreamItems items available).groupNodes.length available
  rw [queue.streamItems_eq stream items available]
  split
  · intro group groups streams impossible; cases impossible
  · intro group groups streams member
    exact drained.2 group groups streams
      ((List.mem_cons.mp member).resolve_left (by intro same; cases same))

/-- Actual immediate successful carriers leave known uncancelled retirements.
Witness: every closing node is live and hence not previously cancelled. Its successful
flush retires it without a marker, and structural persistence covers all later work in
that same handler, including cached startup and recursive draining.
-/
theorem State.handleGraphEvent_successfulRetirements {queue work parents}
    (parent : ParentCutFrame queue work parents) (cancelled : queue.CancellationsRetired)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : SuccessfulGroupRetirements (queue.handleGraphEvent event available).1 work
        (queue.handleGraphEvent event available).2.1 := by
  have frame : CarrierFrame (queue.cacheTaskFailures available) work parents :=
    ⟨parent.cacheTaskFailures available, cancelled.cacheTaskFailures available⟩
  cases event with
  | taskSuccess occurrence result =>
      exact frame.taskSuccess generated canonical matching available
  | streamItems stream items =>
      exact frame.streamItems generated canonical matching available
  | taskFailure occurrence errors =>
      intro group groups streams member
      exact False.elim ((queue.cacheTaskFailures available).taskFailure_noGroupSuccess
        occurrence errors group groups streams member)
  | streamSuccess stream =>
      intro group groups streams member
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      intro group groups streams member
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member
  | groupFailure notice =>
      intro group groups streams member
      change .groupSuccess group groups streams ∈
        ((queue.cacheTaskFailures available).groupFailure notice).2 at member
      unfold State.groupFailure at member
      split at member
      · cases member
      · split at member <;> simp at member

private theorem CarrierFrame.replayGraphEvents {queue work parents}
    (frame : CarrierFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : CarrierFrame (queue.replayGraphEvents events available) work parents := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      have source := matching event List.mem_cons_self
      exact ih ⟨frame.parent.dispatchGraphEvent generated canonical event source available,
        frame.cancelled.handleGraphEvent frame.parent.live frame.parent.tasks event source
          available⟩
        (fun next member => matching next (List.mem_cons_of_mem _ member))

private theorem CarrierFrame.replayBatches {queue work parents}
    (frame : CarrierFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : CarrierFrame (queue.replayBatches batches) work parents := by
  induction batches generalizing queue with
  | nil => exact frame
  | cons batch rest ih =>
      have source : ∀ event ∈ batch, event.MatchesWork work :=
        fun event member => matching event (List.mem_append_left _ member)
      exact ih ⟨frame.parent.handleGraphEvents generated canonical batch source,
        frame.cancelled.handleGraphEvents frame.parent.live frame.parent.tasks batch source⟩
        (fun event member => matching event (List.mem_append_right _ member))

/-- Every actual normalized successful carrier has a durable uncancelled retirement.
Witness: recover its batch/FIFO origin, certify the actual successful handler, then carry
that retirement through the remainder of the same snapshot and all later host batches.
No flattened state bridge or desired response-lifecycle property is assumed.
-/
theorem ExecutedWork.runNormalized_successfulGroupRetirements
    {work batches group groups streams} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    : ∃ dependencies,
        GroupRecordAt work group dependencies
        ∧ UncancelledRetirement
            ((State.initialize (Work.fromExecution work)).runNormalized batches).1
            group.ref := by
  obtain ⟨earlier, batch, later, fifo, event, after, splitBatches, within, emitted⟩ :=
    createWorkQueue_runNormalized_groupSuccess_origin batches started carrier
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  let initial := State.initialize (Work.fromExecution work)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  have earlierMatches : ∀ event ∈ earlier.flatten, event.MatchesWork work := by
    intro event member
    apply valid.eachMatches
    rw [splitBatches, List.flatten_append]
    exact List.mem_append_left _ member
  have batchMatches : ∀ event ∈ batch, event.MatchesWork work := by
    intro event member
    apply valid.eachMatches
    rw [splitBatches, List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ member)
  have initialFrame : CarrierFrame initial work parents :=
    ⟨initial_parentCutFrame generated canonical, createWorkQueue_cancellationsRetired _⟩
  have before := (initialFrame.replayBatches generated canonical earlier earlierMatches
    ).replayGraphEvents generated canonical fifo (by
      intro event member
      apply batchMatches
      rw [within]
      exact List.mem_append_left _ member) available
  have source := batchMatches event (by
    rw [within]; exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨dependencies, known, protectedRef⟩ :=
    State.handleGraphEvent_successfulRetirements before.parent before.cancelled generated
      canonical event source available group groups streams emitted
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← splitBatches, ← inputsStarted_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  obtain ⟨running, _, _⟩ := boundary.batchesStarted_cons batch later checked.2
  obtain ⟨terminal, core⟩ := boundary.handleGraphEvents_stateCore batch running
  have realized : UncancelledRetirement (current.dispatchGraphEvent event available).1 group.ref :=
    protectedRef
  have continued := realized.replayGraphEvents after available
  have batchEnd : UncancelledRetirement (boundary.handleGraphEvents batch).1 group.ref := by
    rw [core]
    change UncancelledRetirement
      { boundary.replayGraphEvents batch available with terminated := terminal } group.ref
    rw [within, State.replayGraphEvents_append _ _ _ available]
    exact continued.withTerminated terminal
  refine ⟨dependencies, known, ?_⟩
  simpa only [boundary, initial, State.runNormalized_replayBatches, splitBatches,
    State.replayBatches, List.foldl_append, List.foldl_cons]
    using batchEnd.replayBatches later

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
