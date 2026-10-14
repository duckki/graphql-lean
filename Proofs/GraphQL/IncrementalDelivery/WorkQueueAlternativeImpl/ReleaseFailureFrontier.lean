import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningTaskOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedBufferDisposal

/-! Proof-only failure-frontier topology for optional path and owner-cut lemmas.
The trace theorem below concerns a mathematical filtered view, not actual handler cleanup.
Actual disposal is constructed independently by PreparedSourceProgress/GeneratedBufferDisposal.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task TaskNode GroupNode)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Memberships retained by the actual publication/settlement exclusion
-----------------------------------------------------------------------------------------

/-- Successful contributor keys from this handler, not historical batch notices. -/
def publicationRoots (events : List WorkQueueEvent) : NodeRefs :=
  events.filterMap
    (fun
      | .groupSuccess group _ _ => some group.ref
      | _ => none)

/-- The actual effect-view predicate: published tasks transfer; a failed settler finishes. -/
def pruningPending (snapshot : Kernel) (event : GraphEvent)
    (events : List WorkQueueEvent) (occurrence : Occurrence)
    : Bool :=
  let settling :=
    match event with
    | .taskFailure task _ => task == occurrence
    | _ => false
  match snapshot.task? occurrence with
  | none => false
  | some task =>
      !settling
      && !task.groups.any (fun owner => (publicationRoots events).contains owner.ref)

private def pruningGroup (snapshot : Kernel) (event : GraphEvent)
    (events : List WorkQueueEvent) (group : GroupNode)
    : Option GroupNode :=
  if (publicationRoots events).contains group.group.node.ref then
    none
  else
    some { group with tasks := group.tasks.filter (pruningPending snapshot event events) }

/-- Name the proof-only topology filtering boundary, never a runtime cleanup pass. -/
theorem failurePruningView_eq (before : Kernel) (event : GraphEvent)
    (events : List WorkQueueEvent)
    : failurePruningView before event events
      = {
        registrationSnapshot before event with
          groupNodes :=
            (registrationSnapshot before event).groupNodes.filterMap
              (pruningGroup (registrationSnapshot before event) event events)
      } :=
  rfl

/-- Filtering successful keys preserves the exact lookup and child links of every other
group. The tasks list is deliberately filtered; counters and topology are not projected away.
-/
theorem failurePruningView_lookup {before : Kernel} {event events key node}
    (found : (registrationSnapshot before event).groupNode? key = some node)
    (unpublished : key ∉ publicationRoots events)
    : (failurePruningView before event events).groupNode? key
      = some
          {
            node with
              tasks :=
                node.tasks.filter
                  (pruningPending (registrationSnapshot before event) event events)
          } := by
  rw [failurePruningView_eq]
  change ((registrationSnapshot before event).groupNodes.filterMap
    (pruningGroup (registrationSnapshot before event) event events)).find?
      (fun group => group.group.node.ref == key) = _
  rw [List.find?_filterMap]
  have predicate : (fun group : GroupNode =>
      (pruningGroup (registrationSnapshot before event) event events group).any
        (fun group => group.group.node.ref == key)) = (fun group => group.group.node.ref == key) := by
    funext group
    by_cases same : group.group.node.ref = key
    · simp [pruningGroup, same, unpublished]
    · unfold pruningGroup
      split <;> simp [same]
  rw [predicate]
  change ((registrationSnapshot before event).groupNode? key).bind _ = _
  rw [found]
  simp only [Option.bind_some, pruningGroup, ReferenceWorkQueue.State.groupNode?_ref found,
    List.contains_iff_mem, unpublished, ↓reduceIte]

/-- A pending occurrence retains links to all of its still-live contributors in the view.
Only this occurrence is tracked: transferred tasks need not satisfy a global link invariant.
-/
theorem failurePruningView_pendingLinks {before : Kernel} {event events occurrence}
    {node : TaskNode}
    (links
      : (registrationSnapshot before event).TaskLinkedOn occurrence
          (node.task.groups.map Execution.DeliveryNode.ref))
    (pending
      : pruningPending (registrationSnapshot before event) event events occurrence = true)
    : (failurePruningView before event events).TaskLinkedOn occurrence
        (node.task.groups.map Execution.DeliveryNode.ref) := by
  rw [failurePruningView_eq]
  intro group member contributes
  obtain ⟨old, earlier, selected⟩ := List.mem_filterMap.mp member
  unfold pruningGroup at selected
  split at selected
  · contradiction
  · cases Option.some.inj selected
    exact List.mem_filter.mpr ⟨links old earlier contributes, pending⟩

/-- A pending task has no contributor among this dispatch's successful keys. -/
theorem pruningPending_unpublished {snapshot : Kernel} {event events occurrence task}
    (catalogue : snapshot.task? occurrence = some task)
    (pending : pruningPending snapshot event events occurrence = true)
    {owner : Execution.DeliveryNode} (contributes : owner ∈ task.groups)
    : owner.ref ∉ publicationRoots events := by
  simp only [pruningPending, catalogue, Bool.and_eq_true] at pending
  have absent : task.groups.any
      (fun owner => (publicationRoots events).contains owner.ref) = false := by
    simpa only [Bool.not_eq_true'] using pending.2
  intro published
  have selected : task.groups.any
      (fun owner => (publicationRoots events).contains owner.ref) = true :=
    List.any_eq_true.mpr ⟨owner, contributes, List.contains_iff_mem.mpr published⟩
  rw [absent] at selected
  contradiction

/-- Successful-group filtering preserves every initially live owner of a pending task.
Membership filtering changes the tasks list, but cannot silently erase this owner's key.
Only the actual catalogue/filter and a lookup are needed; no uniqueness premise is used.
-/
theorem failurePruningView_pendingOwner {before : Kernel} {event events occurrence task}
    (catalogue : (registrationSnapshot before event).task? occurrence = some task)
    (pending
      : pruningPending (registrationSnapshot before event) event events occurrence = true)
    {owner : Execution.DeliveryNode} (contributes : owner ∈ task.groups)
    {group : GroupNode}
    (live : (registrationSnapshot before event).groupNode? owner.ref = some group)
    : ∃ retained,
        (failurePruningView before event events).groupNode? owner.ref
        = some retained := by
  have unpublished := pruningPending_unpublished catalogue pending contributes
  have same := ReferenceWorkQueue.State.groupNode?_ref live
  let retained := { group with tasks := group.tasks.filter (pruningPending
    (registrationSnapshot before event) event events) }
  have present : retained ∈ (failurePruningView before event events).groupNodes := by
    rw [failurePruningView_eq]
    apply List.mem_filterMap.mpr
    refine ⟨group, List.mem_of_find?_eq_some live, ?_⟩
    simp only [pruningGroup, same, List.contains_iff_mem, unpublished, ↓reduceIte, retained]
  cases found : (failurePruningView before event events).groupNode? owner.ref with
  | none =>
      have absent := List.find?_eq_none.mp found retained present
      exact False.elim (absent (by simp only [retained, same, beq_self_eq_true]))
  | some selected => exact ⟨selected, rfl⟩

/-- Effect filtering retains each surviving group's identity and child edges exactly. -/
theorem failurePruningView_groupOrigin {before : Kernel} {event events group}
    (member : group ∈ (failurePruningView before event events).groupNodes)
    : ∃ old ∈ (registrationSnapshot before event).groupNodes,
        group.group = old.group ∧ group.childGroups = old.childGroups := by
  rw [failurePruningView_eq] at member
  obtain ⟨old, earlier, selected⟩ := List.mem_filterMap.mp member
  unfold pruningGroup at selected
  split at selected
  · contradiction
  · cases Option.some.inj selected
    exact ⟨old, earlier, rfl, rfl⟩

/-- The public effect view inherits its finite forest from the registration snapshot.
Successful-group exclusion changes membership lists, not any surviving identity or edge.
-/
theorem failurePruningView_removalForest {before : Kernel} {event events parents}
    (forest : (registrationSnapshot before event).RemovalForest parents)
    : (failurePruningView before event events).RemovalForest parents := by
  refine ⟨?_, ?_, ?_⟩
  · intro group member
    obtain ⟨old, earlier, _, children⟩ := failurePruningView_groupOrigin member
    rw [children]
    exact forest.uniqueChildren old earlier
  · intro group member child linked
    obtain ⟨old, earlier, same, children⟩ := failurePruningView_groupOrigin member
    rw [same]
    exact forest.canonical old earlier child (children ▸ linked)
  · intro parent child member present linked
    obtain ⟨oldParent, earlier, sameParent, children⟩ := failurePruningView_groupOrigin member
    obtain ⟨oldChild, oldPresent, sameChild, _⟩ := failurePruningView_groupOrigin present
    rw [sameParent, sameChild]
    exact forest.increasing earlier oldPresent (sameChild ▸ children ▸ linked)

-----------------------------------------------------------------------------------------
-- All remaining contributors below the same emitted frontier imply actual disposal
-----------------------------------------------------------------------------------------

/-- Checked frontier reduction for any handler. All still-live contributing owners must
lie below actual failure notices, and the task must not have transferred or finished.
These are proof obligations, not strengthened source laws or a residual-state assumption.
-/
theorem failureFrontier_heldSource {before : Kernel} {event events parents occurrence}
    {node : TaskNode} {task : Task} {key : Nat} {final targets}
    (trace
      : PruningGroups (failurePruningView before event events) (failureRoots events) final
          targets)
    (forest : (failurePruningView before event events).RemovalForest parents)
    (links
      : (registrationSnapshot before event).TaskLinkedOn occurrence
          (node.task.groups.map Execution.DeliveryNode.ref))
    (pending
      : pruningPending (registrationSnapshot before event) event events occurrence = true)
    (found : (registrationSnapshot before event).taskNode? occurrence = some node)
    (catalogue : (registrationSnapshot before event).task? occurrence = some task)
    (groups : task.groups = node.task.groups)
    (owned
      : ∃ owner ∈ node.task.groups,
          ∃ group,
            (failurePruningView before event events).groupNode? owner.ref = some group)
    (cut
      : ∀ owner ∈ node.task.groups,
          ∀ group,
            (failurePruningView before event events).groupNode? owner.ref = some group
            → ∃ root ∈ failureRoots events,
                (failurePruningView before event events).LiveDescendant root owner.ref)
    (held : key ∈ node.childStreams)
    : .stream key ∈ targets := by
  have viewFound : (failurePruningView before event events).taskNode? occurrence = some node := found
  have viewCatalogue : (failurePruningView before event events).task? occurrence = some task := catalogue
  have requested : .stream key ∈ targets := by
    rcases trace.heldSource viewFound held with retained | requested
    · obtain ⟨owner, member, group, lookup⟩ := trace.retainedHasOwnerOn
        (failurePruningView_pendingLinks links pending) viewCatalogue groups owned retained
      obtain ⟨old, earlier, _⟩ := trace.groupEdgesFrom owner.ref group lookup
      obtain ⟨root, emitted, path⟩ := cut owner member old earlier
      rw [trace.coversDescendants forest root emitted owner.ref path] at lookup
      contradiction
    · exact requested
  exact requested

-----------------------------------------------------------------------------------------
-- Generated-dispatch resource disposal statement
-----------------------------------------------------------------------------------------

/-- Generated construction target, proved in GeneratedFailureCut, not a source assumption.
A successful task or item input must transfer each dropped prepared buffer's source to an
active root or emit
its cleanup request. The snapshot includes newly adopted sources. The frontier theorem
above checks the disposal edge. PendingFailureCut checks composition from the generated cut
leaf; publication exclusion and view ownership are constructed there.
-/
def GeneratedReleaseFailureDisposal : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ resources : ResourceState,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        let snapshot := registrationSnapshot before.queue event
        let observed := resources.observeCompletionAndCleanup before event
        ResourceReplay resources observed.2 observed.1
        ∧ ∀ occurrence node key,
            snapshot.taskNode? occurrence = some node
            → node.value.isSome = true
            → (∃ owner ∈ node.task.groups,
                ∃ group, snapshot.groupNode? owner.ref = some group)
            → key ∈ node.childStreams
            → reduced.state.queue.taskNode? occurrence = none
            → key ∈ reduced.state.queue.rootStreams
              ∨ (.cancelSource key ∈ reduced.effects
                  ∧ (resources (.stream key) = .owned .queue
                      → observed.1 (.stream key) = .cleanupRequested .queue))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
