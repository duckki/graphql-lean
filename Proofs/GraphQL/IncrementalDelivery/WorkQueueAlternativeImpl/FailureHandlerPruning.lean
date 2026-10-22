import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureResources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureValueRetention

/-! Generated failed-task disposal uses the real owner fold and its inline effects.
Reference topology lemmas remain reusable, but no reconstructed failure-effect view supplies
the resource witness.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode GroupNode failureGroupStep)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State

/-- The actual failed-group output frontier, without choosing a removal order separately. -/
def failureRoots (events : List WorkQueueEvent) : NodeRefs :=
  events.filterMap
    (fun
      | .groupFailure group _ => some group.ref
      | _ => none)

private def publishedRoots (events : List WorkQueueEvent) : NodeRefs :=
  events.filterMap
    (fun
      | .groupSuccess group _ _ => some group.ref
      | _ => none)

-----------------------------------------------------------------------------------------
-- Sequential failure output preserves every owner outside its emitted subtrees
-----------------------------------------------------------------------------------------

private theorem failureFold_eventsSubset (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : Kernel × List WorkQueueEvent)
    : acc.2.Subset (groups.foldl (failureGroupStep errors) acc).2 := by
  induction groups generalizing acc with
  | nil => exact List.Subset.refl _
  | cons group rest ih =>
      apply List.Subset.trans (l₂ := (failureGroupStep errors acc group).2) _ (ih _)
      obtain ⟨queue, events⟩ := acc
      unfold failureGroupStep
      dsimp only
      split
      · exact List.Subset.refl _
      · split
        · exact List.subset_append_left _ _
        · exact List.Subset.refl _

/-- The full failure fold retains a key outside every actually emitted failed subtree.
The endpoint output, not cancellation-history guesses, licenses each skipped subtree.
-/
theorem failureFold_outside_survives {parents key} (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : Kernel × List WorkQueueEvent)
    (unique : acc.1.GroupRefsUnique) (forest : acc.1.RemovalForest parents)
    (live : ∃ node, acc.1.groupNode? key = some node)
    (outside
      : ∀ root ∈ failureRoots (groups.foldl (failureGroupStep errors) acc).2,
          ¬acc.1.LiveDescendant root key)
    : ∃ node,
        (groups.foldl (failureGroupStep errors) acc).1.groupNode? key = some node := by
  induction groups generalizing acc with
  | nil => exact live
  | cons group rest ih =>
      obtain ⟨queue, events⟩ := acc
      obtain ⟨node, lookup⟩ := live
      rw [List.foldl_cons] at outside ⊢
      unfold failureGroupStep at outside ⊢
      dsimp only at outside ⊢
      cases found : queue.groupNode? group.ref with
      | none =>
          simp only [found] at outside ⊢
          exact ih (queue, events) unique forest ⟨node, lookup⟩ outside
      | some owner =>
          simp only [found] at outside ⊢
          cases active : queue.rootGroups.contains group.ref with
          | false =>
              simp only [active, Bool.false_eq_true, ↓reduceIte] at outside ⊢
              exact ih (queue, events) unique forest ⟨node, lookup⟩ outside
          | true =>
              simp only [active, ↓reduceIte] at outside ⊢
              have emitted : .groupFailure owner.group.node errors ∈
                  (rest.foldl (failureGroupStep errors)
                    (queue.removeGroup owner.group.node.ref, events ++ [.groupFailure owner.group.node errors])).2 :=
                failureFold_eventsSubset errors rest _ (List.mem_append_right _ List.mem_cons_self)
              have notBelow := outside owner.group.node.ref
                (List.mem_filterMap.mpr ⟨_, emitted, rfl⟩)
              have kept := (ReferenceWorkQueue.State.removeGroup_groupNodeRetained forest notBelow).trans lookup
              let removed := ReferenceWorkQueue.State.removeGroup.collect
                (queue.groupNodes.length + 1) queue [owner.group.node.ref] []
              have edges : (queue.removeGroup owner.group.node.ref).GroupEdgesFrom queue :=
                queue.filterRefs_groupEdgesFrom (fun key => !removed.contains key)
              apply ih _ (unique.removeGroup _) (forest.removeGroup _) ⟨node, kept⟩
              intro root member below
              exact outside root member (edges.liveDescendant below)

/-- Task failure retains each old owner outside all failure notices from that handler. -/
theorem taskFailure_outside_survives {queue : Kernel} {parents key}
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (failed : Occurrence) (errors : Nat) (live : ∃ node, queue.groupNode? key = some node)
    (outside
      : ∀ root ∈ failureRoots (queue.taskFailure failed errors).2,
          ¬queue.LiveDescendant root key)
    : ∃ node, (queue.taskFailure failed errors).1.groupNode? key = some node := by
  cases found : queue.taskNode? failed with
  | none => simpa only [ReferenceWorkQueue.State.taskFailure, found] using live
  | some task =>
      rw [queue.taskFailure_eq failed errors task found] at outside ⊢
      apply failureFold_outside_survives errors _ _ unique
        ⟨forest.uniqueChildren, forest.canonical, forest.increasing⟩ live
      intro root member path
      exact outside root member
        (ReferenceWorkQueue.State.LiveDescendant.of_groupNodes_eq
          (queue := queue.putTaskNode { task with rejection := some errors })
          (next := queue) rfl path)

-----------------------------------------------------------------------------------------
-- Exact actual-handler disposal, without a publication-filtered observer
-----------------------------------------------------------------------------------------

/-- Losing a nonsettling held-source record implies cancellation in this actual reduction.
Unlike the old output-scan route, this needs neither contributor links nor a forest premise.
-/
theorem taskFailure_lostBufferedSource (state : State) (failed : Occurrence)
    (errors : Nat) {occurrence node key} (different : occurrence ≠ failed)
    (found : state.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    (changed : (state.taskFailure failed errors).1.queue.taskNode? occurrence ≠ some node)
    : .cancelSource key ∈ (state.handleGraphEvent (.taskFailure failed errors)).2.2 := by
  have target := (state.taskFailure_heldSource failed errors different found held).resolve_left changed
  exact List.mem_flatMap.mpr ⟨.stream key, target, List.mem_cons_self⟩

/-- Complete disappearance specializes exact-record loss at the actual endpoint. -/
theorem taskFailure_droppedBufferedSource (state : State) (failed : Occurrence)
    (errors : Nat) {occurrence node key} (different : occurrence ≠ failed)
    (found : state.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    (dropped : (state.taskFailure failed errors).1.queue.taskNode? occurrence = none)
    : .cancelSource key ∈ (state.handleGraphEvent (.taskFailure failed errors)).2.2 := by
  apply taskFailure_lostBufferedSource state failed errors different found held
  rw [dropped]
  intro impossible
  cases impossible

-----------------------------------------------------------------------------------------
-- Generated freshness connects buffered records to the nonsettling safety domain
-----------------------------------------------------------------------------------------

/-- Alternative terminal retirement preserves key uniqueness, vacuously when cleared. -/
theorem generatedReplay_groupKeysUnique (work : Work) (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((State.initialize work).runNormalized inputs).1.queue.GroupRefsUnique := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · simp [ReferenceWorkQueue.State.GroupRefsUnique, State.clearRecords]
  · exact ReferenceWorkQueue.createWorkQueue_runNormalized_groupRefsUnique _ _

/-- An actual buffered value still identifies its earlier success input after projection. -/
theorem generatedReplay_bufferedSource {work : Work} {inputs : List (List GraphEvent)}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    {occurrence node value}
    (found
      : ((State.initialize work).runNormalized inputs).1.queue.taskNode? occurrence
        = some node)
    (stored : node.value = some value)
    : ReferenceWorkQueue.ObjectValueFrom inputs.flatten occurrence value := by
  rw [State.runNormalized_initialize work inputs generated valid started] at found
  simp only [State.fromReference] at found
  split at found
  · cases found
  · obtain ⟨published, _, inventory⟩ := ReferenceWorkQueue.createWorkQueue_runNormalized_publications valid
    have known := ReferenceWorkQueue.State.taskNode?_some found
    have source := (inventory.stored node known.1 value stored).1
    rwa [known.2] at source

/-- Fresh task inputs cannot settle an occurrence with an earlier stored success value. -/
theorem generatedReplay_buffered_ne_taskInput {work inputs event occurrence node incoming}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    (found
      : ((State.initialize work).runNormalized inputs).1.queue.taskNode? occurrence
        = some node)
    (stored : node.value.isSome = true) (current : incoming ∈ event.identities.1)
    : occurrence ≠ incoming := by
  obtain ⟨earlier, _, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases value : node.value with
  | none => simp [value] at stored
  | some payload =>
      have source := generatedReplay_bufferedSource generated earlier started found value
      intro same
      exact fresh.2.2.1 incoming current (same ▸ source.identity)

/-- Generated full task-failure dispatch covers each dropped initially owned buffer.
The independently supplied resource inventory is observed through this same handler's
actual effects. Cleanup requests are not async settlement or full stop coverage.
-/
def GeneratedTaskFailureDisposal : Prop :=
  ∀ work inputs failed errors,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work
        (inputs.flatten ++ [.taskFailure failed errors])
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ resources : ResourceState,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced :=
          ({ state := before } : GraphBatchResult).handleGraphEvent
            (.taskFailure failed errors)
        let observed :=
          resources.observeHandlerCleanup before (.taskFailure failed errors)
        ResourceReplay resources observed.2 observed.1
        ∧ ∀ occurrence node key,
            before.queue.taskNode? occurrence = some node
            → node.value.isSome = true
            → (∃ owner ∈ node.task.groups,
                ∃ group, before.queue.groupNode? owner.ref = some group)
            → key ∈ node.childStreams
            → reduced.state.queue.taskNode? occurrence = none
            → .cancelSource key ∈ reduced.effects
              ∧ (resources (.stream key) = .owned .queue
                  → observed.1 (.stream key) = .cleanupRequested .queue)

/-- Derive actual effects and requests using generated input freshness and raw safety.
No caller supplies disposal, topology, owner-link or resource-history premises.
-/
theorem GeneratedTaskFailureDisposal_holds : GeneratedTaskFailureDisposal := by
  intro work inputs failed errors generated valid started resources
  let before := ((State.initialize work).runNormalized inputs).1
  refine ⟨resources.observeHandlerCleanup_replay _ _, ?_⟩
  intro occurrence node key found stored _owned held dropped
  have different : occurrence ≠ failed :=
    generatedReplay_buffered_ne_taskInput generated valid started found stored List.mem_cons_self
  have requested := taskFailure_droppedBufferedSource before failed errors different found held dropped
  refine ⟨requested, fun owned => resources.requestQueueCleanup_owned _ _ ?_ owned⟩
  exact List.mem_filterMap.mpr ⟨.cancelSource key, requested, rfl⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
