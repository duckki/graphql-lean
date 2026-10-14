import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTasks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention

/-! Link last-owner disposal to buffered task removal, rather than merely group presence.
The permanent task catalogue and buffered memberships are derived from generated replay.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task TaskNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Pruning removes nodes without changing the permanent task catalogue
-----------------------------------------------------------------------------------------

/-- Every task selected by the fold has the same permanent descriptor before and after it. -/
theorem PruningTasks.taskLookup {queue occurrences final targets}
    (trace : PruningTasks queue occurrences final targets) (occurrence : Occurrence)
    : final.task? occurrence = queue.task? occurrence := by
  induction trace with
  | nil => rfl
  | missing _ _ ih | shared _ _ _ ih => exact ih
  | dispose _ _ _ ih => exact ih

/-- Group pruning also leaves the permanent task catalogue unchanged. -/
theorem PruningGroups.taskLookup {queue pending final targets}
    (trace : PruningGroups queue pending final targets) (occurrence : Occurrence)
    : final.task? occurrence = queue.task? occurrence := by
  induction trace with
  | nil => rfl
  | missing _ _ ih => exact ih
  | visit _ tasks _ ih => exact ih.trans (tasks.taskLookup occurrence)

/-- A retained exact lookup existed before the task fold; pruning never recreates nodes. -/
theorem PruningTasks.lookupBefore {queue occurrences final targets occurrence node}
    (trace : PruningTasks queue occurrences final targets)
    (retained : final.taskNode? occurrence = some node)
    : queue.taskNode? occurrence = some node := by
  induction trace with
  | nil => exact retained
  | missing _ _ ih | shared _ _ _ ih => exact ih retained
  | @dispose task rest final targets queue selected lookup owners trace ih =>
      have current := ih retained
      by_cases same : occurrence = selected
      · subst selected
        rw [ReferenceWorkQueue.State.removeTask_node_absent] at current
        contradiction
      · rwa [queue.removeTask_lookup_other same] at current

/-- Filtering groups and unlinking tasks cannot introduce an exact task lookup. -/
theorem PruningGroups.lookupBefore {queue pending final targets occurrence node}
    (trace : PruningGroups queue pending final targets)
    (retained : final.taskNode? occurrence = some node)
    : queue.taskNode? occurrence = some node := by
  induction trace with
  | nil => exact retained
  | missing _ _ ih => exact ih retained
  | visit _ tasks _ ih => exact tasks.lookupBefore (ih retained)

/-- The task fold preserves buffered membership links. -/
theorem PruningTasks.storedTaskLinks {queue occurrences final targets}
    (trace : PruningTasks queue occurrences final targets) (links : queue.StoredTaskLinks)
    : final.StoredTaskLinks := by
  induction trace with
  | nil => exact links
  | missing _ _ ih | shared _ _ _ ih => exact ih links
  | dispose _ _ _ ih => exact ih (links.removeTask _)

private abbrev withoutGroup (queue : Kernel) (key : Nat) : Kernel :=
  {
    queue with
      groupNodes := queue.groupNodes.filter (fun node => node.group.node.ref != key)
      rootGroups := queue.rootGroups.filter (· != key)
  }

-----------------------------------------------------------------------------------------
-- A linked buffered task cannot survive removal of its last live contributor
-----------------------------------------------------------------------------------------

/-- Any selected ownerless occurrence is absent after the actual task fold.
Catalogue lookup, not the started-node map, supplies the executable last-owner test.
-/
theorem PruningTasks.ownerlessSelected {queue occurrences final targets occurrence task}
    (trace : PruningTasks queue occurrences final targets)
    (selected : occurrence ∈ occurrences) (catalogue : queue.task? occurrence = some task)
    (ownerless : ∀ owner ∈ task.groups, queue.groupNode? owner.ref = none)
    : final.taskNode? occurrence = none := by
  induction trace with
  | nil => cases selected
  | @missing queue rest final targets chosen absent trace ih =>
      rcases List.mem_cons.mp selected with same | later
      · subst chosen
        rw [absent] at catalogue
        contradiction
      · exact ih later catalogue ownerless
  | @shared found queue rest final targets chosen lookup retained trace ih =>
      rcases List.mem_cons.mp selected with same | later
      · subst chosen
        have sameTask : found = task := Option.some.inj (lookup.symm.trans catalogue)
        subst found
        have all : task.groups.all (fun owner => (queue.groupNode? owner.ref).isNone) = true :=
          List.all_eq_true.mpr (fun owner member => by simp [ownerless owner member])
        rw [all] at retained
        contradiction
      · exact ih later catalogue ownerless
  | @dispose found rest final targets queue chosen lookup owners trace ih =>
      rcases List.mem_cons.mp selected with same | later
      · subst chosen
        cases kept : final.taskNode? occurrence with
        | none => rfl
        | some node =>
            have impossible := trace.lookupBefore kept
            rw [ReferenceWorkQueue.State.removeTask_node_absent] at impossible
            contradiction
      · apply ih later catalogue
        intro owner member
        cases live : (queue.removeTask chosen).groupNode? owner.ref with
        | none => rfl
        | some node =>
            obtain ⟨old, earlier, _⟩ := queue.removeTask_groupEdgesFrom chosen owner.ref node live
            rw [ownerless owner member] at earlier
            contradiction

/-- The task fold retains one occurrence's links whenever its exact node survives. -/
theorem PruningTasks.linkedOnRetained
    {queue occurrences final targets occurrence keys node}
    (trace : PruningTasks queue occurrences final targets)
    (links : queue.TaskLinkedOn occurrence keys)
    (retained : final.taskNode? occurrence = some node)
    : final.TaskLinkedOn occurrence keys := by
  induction trace with
  | nil => exact links
  | missing _ _ ih | shared _ _ _ ih => exact ih links retained
  | @dispose task rest final targets queue chosen lookup owners trace ih =>
      by_cases same : occurrence = chosen
      · subst chosen
        have impossible := trace.lookupBefore retained
        rw [ReferenceWorkQueue.State.removeTask_node_absent] at impossible
        contradiction
      · exact ih (links.removeOtherTask chosen same) retained

/-- A retained linked task with an original live contributor has one afterward.
Membership links force the last owner's occurrence into the disposal fold; canonical
catalogue groups make that fold test the same contributors as the retained record.
Only this occurrence needs links, so an already finished settler may be excluded.
-/
theorem PruningGroups.retainedHasOwnerOn
    {queue pending final targets occurrence node task}
    (trace : PruningGroups queue pending final targets)
    (links
      : queue.TaskLinkedOn occurrence (node.task.groups.map Execution.DeliveryNode.ref))
    (catalogue : queue.task? occurrence = some task)
    (groups : task.groups = node.task.groups)
    (owned : ∃ owner ∈ node.task.groups, ∃ group, queue.groupNode? owner.ref = some group)
    (retained : final.taskNode? occurrence = some node)
    : ∃ owner ∈ node.task.groups, ∃ group, final.groupNode? owner.ref = some group := by
  induction trace with
  | nil => exact owned
  | missing _ _ ih => exact ih links catalogue owned retained
  | @visit group queue key current first keys final later lookup tasks rest ih =>
      have currentFound := rest.lookupBefore retained
      have currentCatalogue : current.task? occurrence = some task :=
        (tasks.taskLookup occurrence).trans catalogue
      by_cases currentOwned : ∃ owner ∈ node.task.groups,
          ∃ group, current.groupNode? owner.ref = some group
      · have filteredLinks : (withoutGroup queue key).TaskLinkedOn occurrence
            (node.task.groups.map Execution.DeliveryNode.ref) :=
          fun owner member contributes => links owner (List.mem_filter.mp member).1 contributes
        exact ih (tasks.linkedOnRetained filteredLinks currentFound)
          currentCatalogue currentOwned retained
      · have ownerless : ∀ owner ∈ task.groups,
            (withoutGroup queue key).groupNode? owner.ref = none := by
          intro owner member
          rw [groups] at member
          cases live : (withoutGroup queue key).groupNode? owner.ref with
          | none => rfl
          | some old =>
              obtain ⟨new, kept⟩ := tasks.groupPresent ⟨old, live⟩
              exact False.elim (currentOwned ⟨owner, member, new, kept⟩)
        obtain ⟨owner, contributes, old, live⟩ := owned
        have same : owner.ref = key := by
          by_cases equal : owner.ref = key
          · exact equal
          apply False.elim
          have filtered : (withoutGroup queue key).groupNode? owner.ref = some old := by
            change (queue.groupNodes.filter (fun node => node.group.node.ref != key)).find?
              (fun node => node.group.node.ref == owner.ref) = some old
            rw [ReferenceWorkQueue.State.groupNode?_filterRefs queue (fun other => other != key)]
            simpa [equal] using live
          rw [ownerless owner (groups ▸ contributes)] at filtered
          contradiction
        have linked : occurrence ∈ group.tasks := by
          apply links group (List.mem_of_find?_eq_some lookup)
          exact List.mem_map.mpr ⟨owner, contributes,
            same.trans (ReferenceWorkQueue.State.groupNode?_ref lookup).symm⟩
        have removed := tasks.ownerlessSelected linked catalogue ownerless
        rw [removed] at currentFound
        contradiction

/-- Buffered membership evidence specializes the occurrence-local ownership theorem. -/
theorem PruningGroups.retainedHasOwner {queue pending final targets occurrence node task}
    (trace : PruningGroups queue pending final targets) (links : queue.StoredTaskLinks)
    (found : queue.taskNode? occurrence = some node) (stored : node.value.isSome = true)
    (catalogue : queue.task? occurrence = some task)
    (groups : task.groups = node.task.groups)
    (owned : ∃ owner ∈ node.task.groups, ∃ group, queue.groupNode? owner.ref = some group)
    (retained : final.taskNode? occurrence = some node)
    : ∃ owner ∈ node.task.groups, ∃ group, final.groupNode? owner.ref = some group := by
  have facts := ReferenceWorkQueue.State.taskNode?_some found
  have linked := links node facts.1 stored
  rw [facts.2] at linked
  exact trace.retainedHasOwnerOn linked catalogue groups owned retained

-----------------------------------------------------------------------------------------
-- Project buffered disposal to the actual reference task filter
-----------------------------------------------------------------------------------------

/-- A buffered task dropped by reference removal cannot retain its held sources silently.
The initial live-contributor premise identifies an owned buffer, rather than an arbitrary
raw orphan node. The resulting cleanup identity comes from the actual disposal trace.
-/
theorem PruningGroups.removedBufferedSource
    {queue final targets parents root occurrence node task key}
    (trace : PruningGroups queue [root] final targets)
    (forest : queue.RemovalForest parents) (links : queue.StoredTaskLinks)
    (found : queue.taskNode? occurrence = some node) (stored : node.value.isSome = true)
    (catalogue : queue.task? occurrence = some task)
    (groups : task.groups = node.task.groups)
    (owned : ∃ owner ∈ node.task.groups, ∃ group, queue.groupNode? owner.ref = some group)
    (held : key ∈ node.childStreams)
    (removed : (queue.removeGroup root).taskNode? occurrence = none)
    : .stream key ∈ targets := by
  rcases trace.heldSource found held with retained | requested
  · obtain ⟨owner, contributes, live⟩ := trace.retainedHasOwner links found stored catalogue
      groups owned retained
    obtain ⟨group, lookup⟩ := (trace.groupPresent_iff_removeGroup forest).mp live
    have impossible := ReferenceWorkQueue.State.removeGroup_lookup_survivingOwner found root
      contributes (List.mem_of_find?_eq_some lookup)
      (ReferenceWorkQueue.State.groupNode?_ref lookup)
    rw [removed] at impossible
    contradiction
  · exact requested

/-- Registered started nodes and matched Work give the exact catalogue contributor list.
This uses structural occurrence identity, not an assumed unique native task map.
-/
theorem canonicalTaskCatalogue {queue : Kernel} {work occurrence node}
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (found : queue.taskNode? occurrence = some node)
    : ∃ task, queue.task? occurrence = some task ∧ task.groups = node.task.groups := by
  have nodeFacts := ReferenceWorkQueue.State.taskNode?_some found
  have member := registered node nodeFacts.1
  cases selected : queue.task? occurrence with
  | none =>
      have excluded := List.find?_eq_none.mp selected node.task member
      have reflexive := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr nodeFacts.2
      rw [reflexive] at excluded
      contradiction
  | some task =>
      have sameOccurrence := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : Task => candidate.occurrence == occurrence) selected)
      have taskMatch := (matching task (List.mem_of_find?_eq_some selected)).2
      have nodeMatch := (matching node.task member).2
      rw [sameOccurrence] at taskMatch
      rw [nodeFacts.2] at nodeMatch
      exact ⟨task, rfl, Option.some.inj (taskMatch.symm.trans nodeMatch)⟩

/-- Generated replay supplies registration, exact catalogue matching, and buffered links.
Terminal retirement is handled explicitly; an empty retired task map is vacuous.
-/
theorem generatedReplay_taskInvariants {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : let queue := ((State.initialize work).runNormalized inputs).1.queue
      queue.StartedTasksRegistered
      ∧ queue.RegisteredTasksMatch work
      ∧ queue.StoredTaskLinks := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · refine ⟨?_, ?_, ?_⟩
    · intro node impossible; cases impossible
    · intro task impossible; cases impossible
    · intro node impossible; cases impossible
  · exact ⟨ReferenceWorkQueue.State.runNormalized_startedTasksRegistered
      (ReferenceWorkQueue.createWorkQueue_startedTasksRegistered _) inputs,
      ReferenceWorkQueue.createWorkQueue_runNormalized_registeredTasksMatch valid,
      generated.runNormalized_storedTaskLinks inputs valid started⟩

/-- At each generated started boundary, one exact pruning witness covers every buffered
held source dropped by reference single-root removal. A live initial contributor identifies
the buffer; inventory completeness and full handler/adoption projection remain separate.
-/
def GeneratedPruningBufferedCoverage : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ root,
        let queue := ((State.initialize work).runNormalized inputs).1.queue
        ∃ final targets,
          PruningGroups queue [root] final targets
          ∧ (({ queue } : State).removeGroup root).2 = uniqueCleanupTargets targets
          ∧ ∀ occurrence node key,
              queue.taskNode? occurrence = some node
              → node.value.isSome = true
              → (∃ owner ∈ node.task.groups,
                  ∃ group, queue.groupNode? owner.ref = some group)
              → key ∈ node.childStreams
              → (queue.removeGroup root).taskNode? occurrence = none
              → .stream key ∈ targets

/-- Derive buffered cleanup from the same actual trace and the existing source contract. -/
theorem GeneratedPruningBufferedCoverage_holds : GeneratedPruningBufferedCoverage := by
  intro work inputs generated valid started root
  let queue := ((State.initialize work).runNormalized inputs).1.queue
  obtain ⟨parents, forest⟩ := generatedReplay_removalForest generated inputs valid started
  obtain ⟨registered, matching, links⟩ := generatedReplay_taskInvariants generated inputs valid started
  obtain ⟨final, targets, trace, same, _records⟩ :=
    pruningRemoval_witness { queue } root
  refine ⟨final, targets, trace, same, ?_⟩
  intro occurrence node key found stored owned held removed
  obtain ⟨task, catalogue, groups⟩ := canonicalTaskCatalogue registered matching found
  exact trace.removedBufferedSource forest links found stored catalogue groups owned held
    removed

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
