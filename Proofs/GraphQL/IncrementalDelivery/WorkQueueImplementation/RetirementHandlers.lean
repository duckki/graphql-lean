import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementIntegration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorRelease

/-! Ancestor certificates through complete handlers, including retained failure drains. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failure settlement changes no healthy retirement boundary
-----------------------------------------------------------------------------------------

/-- A matching task failure preserves closure relative to any list containing it.
Witness: the stored task's contributors are invalidated, and sequential cleanup retains
every healthy node. Future failures may be included in this proof-only failure list. -/
theorem State.HealthyRetiredAncestors.taskFailure {queue : State} {work failed parents}
    (prior : queue.HealthyRetiredAncestors work failed)
    (links : queue.ChildLinksCanonical parents) (groups : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence) (errors : Nat)
    (recorded : occurrence ∈ failed)
    : (queue.taskFailure occurrence errors).1.HealthyRetiredAncestors work failed := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using prior
  | some taskNode =>
      have taskMember := registered taskNode (List.mem_of_find?_eq_some found)
      obtain ⟨⟨address, payload, producer, _, known⟩, _⟩ := matching taskNode.task taskMember
      have same : taskNode.task.occurrence = occurrence := by
        have selected := List.find?_some
          (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence)
          (by simpa [State.taskNode?] using found)
        exact (occurrence_beq_iff_eq _ _).mp selected
      let step (acc : State × List WorkQueueEvent) (group : Execution.DeliveryNode) :=
        match acc.1.groupNode? group.ref with
        | none => acc
        | some node =>
            if acc.1.rootGroups.contains group.ref then
              let (next, failure) := acc.1.finishGroupFailure node errors
              (next, acc.2 ++ [failure])
            else (acc.1.putGroupNode
              { node with pending := node.pending - 1
                          failure := some (node.failure.getD 0 + errors) }, acc.2)
      let property (acc : State × List WorkQueueEvent) :=
        acc.1.ChildLinksCanonical parents ∧ acc.1.GroupNodesMatchWork work
        ∧ acc.1.HealthyRetiredAncestors work failed
      have loop (more : List Execution.DeliveryNode) (included : more.Subset taskNode.task.groups)
          (acc : State × List WorkQueueEvent) (valid : property acc)
          : property (more.foldl step acc) := by
        induction more generalizing acc with
        | nil => exact valid
        | cons group rest ih =>
            apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
            have invalid : GroupInvalidated work failed group.ref :=
              .task ⟨producer, payload, known⟩
                (List.mem_map_of_mem (included List.mem_cons_self)) (same.symm ▸ recorded)
            unfold step
            split
            · exact valid
            · rename_i node selected
              split
              · have refEq := State.groupNode?_ref selected
                exact ⟨valid.1.removeGroup _, valid.2.1.removeGroup _,
                  valid.2.2.removeGroup valid.1 valid.2.1 canonical _
                    (refEq.symm ▸ invalid.toRecordInvalidated)⟩
              · have member := List.mem_of_find?_eq_some selected
                exact ⟨valid.1.putGroupNode _ (valid.1 node member),
                  valid.2.1.putGroupNode _ (valid.2.1 node member),
                  valid.2.2.putGroupNode _⟩
      let current := queue.removeTask occurrence
      simp only [State.taskFailure, found]
      split
      · exact prior.removeTask occurrence
      · exact (loop taskNode.task.groups (fun _ member => member)
          (current, []) ⟨links.removeTask occurrence, groups.removeTask occurrence,
            prior.removeTask occurrence⟩).2.2

/-- A task failure retains ancestor certificates for surviving roots.
Witness: roots only shrink, and every previously retired ancestor remains retired.
-/
theorem State.RootAncestorsRetired.taskFailure {queue : State} {work}
    (roots : queue.RootAncestorsRetired work) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.RootAncestorsRetired work :=
  roots.mono (queue.taskFailure_rootsSubset occurrence errors)
    (fun _ retired => retired.taskFailure occurrence errors)

-----------------------------------------------------------------------------------------
-- The successful contributor fold carries the metadata needed by its final drain
-----------------------------------------------------------------------------------------

/-- Internal metadata retained through contributor updates and release-time draining.
This bundle abbreviates independently proved bookkeeping facts; it adds no queue state.
-/
private structure RetirementMetadata (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (failed : List Occurrence)
    : Prop where
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  live : queue.LiveGroupsRegistered
  tasks : queue.TaskGroupsRegistered
  caches : queue.CachedFailuresSupported work failed
  cancelled : queue.CancelledRecordsSupported work failed

/-- Activation retains every metadata field needed for retirement preservation.
Witness: existing node, link, registry, and cache preservation theorems.
-/
private theorem RetirementMetadata.startNewWork {queue : State} {work parents failed}
    (prior : RetirementMetadata queue work parents failed) (released : NewWork)
    : RetirementMetadata (queue.startNewWork released) work parents failed := by
  have registered := State.startNewWork_registration prior.live prior.tasks released
  exact ⟨prior.groups.startNewWork _, prior.links.startNewWork _,
    registered.1, registered.2, prior.caches.startNewWork _, prior.cancelled.startNewWork _⟩

/-- A contributor decrement and any resulting successful closure retain metadata.
Witness: lookup identifies the updated descriptor; closure changes neither provenance
nor canonical ancestry, and preserves registry coverage and cache support.
-/
private theorem RetirementMetadata.contributor
    {acc : State × List WorkQueueEvent × NewWork} {work parents failed}
    (prior : RetirementMetadata acc.1 work parents failed)
    (group : Execution.DeliveryNode)
    : RetirementMetadata (successGroupStep acc group).1 work parents failed := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact prior
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    have member := List.mem_of_find?_eq_some found
    have next : RetirementMetadata (current.putGroupNode updated) work parents failed :=
      ⟨prior.groups.putGroupNode _ (prior.groups node member),
        prior.links.putGroupNode _ (prior.links node member),
        prior.live.putGroupNode _ (prior.live node member), prior.tasks,
        prior.caches.putGroupNode _ (prior.caches node member), prior.cancelled⟩
    split
    · have registered := State.finishGroupSuccess_registration next.live next.tasks updated
      exact ⟨next.groups.finishGroupSuccess _, next.links.finishGroupSuccess _,
        registered.1, registered.2.1, next.caches.finishGroupSuccess _,
        next.cancelled.finishGroupSuccess _⟩
    · exact next

/-- The actual single-pass contributor fold retains retirement metadata.
Witness: list induction through each executable decrement/closure state.
-/
private theorem RetirementMetadata.contributors
    {acc : State × List WorkQueueEvent × NewWork} {work parents failed}
    (prior : RetirementMetadata acc.1 work parents failed)
    (groups : List Execution.DeliveryNode)
    : RetirementMetadata (groups.foldl successGroupStep acc).1 work parents failed := by
  induction groups generalizing acc with
  | nil => exact prior
  | cons group rest ih => exact ih (prior.contributor group)

/-- Task success preserves both retired-ancestor certificates through its complete handler.
Witness: integration introduces no healthy retired ref, the contributor fold protects roots,
and supported caches justify the final recursive drain. No root-health or child-owner
availability premise is needed for this retirement step.
-/
theorem State.taskSuccess_retirement {queue : State} {work failed parents}
    (roots : queue.RootAncestorsRetired work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    {occurrence result}
    (eventMatches : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : (queue.taskSuccess occurrence result).1.RootAncestorsRetired work
      ∧ (queue.taskSuccess occurrence result).1.HealthyRetiredAncestors work failed := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using And.intro roots retirement
  | some taskNode =>
      let stored := queue.putTaskNode { taskNode with value := some result.value }
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have storedMatching : stored.GroupNodesMatchWork work := matching
      have storedLinks : stored.ChildLinksCanonical parents := links
      have storedLive : stored.LiveGroupsRegistered := registered
      have storedTasks : stored.TaskGroupsRegistered := tasks
      have storedRoots : stored.RootAncestorsRetired work := roots
      have storedClosure : stored.HealthyRetiredAncestors work failed := retirement
      have storedCaches : stored.CachedFailuresSupported work failed := supported
      have nextMatching : integrated.GroupNodesMatchWork work :=
        storedMatching.maybeIntegrateWork result.work
          (fun _ member => eventMatches.taskChildGroups_recordAt member) (some occurrence)
      have nextLinks : integrated.ChildLinksCanonical parents :=
        storedLinks.maybeIntegrateWork result.work
          (fun _ member => eventMatches.taskChildGroups_parentCanonical canonical member)
          (some occurrence)
      have coverage := State.maybeIntegrateWork_registration storedLive storedTasks
        result.work eventMatches.childTasksCovered (some occurrence)
      have nextRoots : integrated.RootAncestorsRetired work :=
        storedRoots.mono
          (by rw [stored.maybeIntegrateWork_rootGroups]; exact fun _ member => member)
          (fun _ retired => retired.maybeIntegrateWork result.work (some occurrence))
      have storedCancelled : stored.CancelledRecordsSupported work failed := cancelled
      have nextCancelled := storedCancelled.maybeIntegrateWork result.work (some occurrence)
        (by
          intro group member
          obtain ⟨dependencies, known⟩ := eventMatches.taskChildGroups_recordAt member
          exact ⟨dependencies, known,
            (eventMatches.taskChildGroups_parentCanonical canonical member).trans
              (congrArg List.head? (canonical _ _ known)).symm⟩)
      have nextClosure := storedClosure.maybeIntegrateWork result.work (some occurrence)
        nextCancelled
      have nextMeta : RetirementMetadata integrated work parents failed :=
        ⟨nextMatching, nextLinks, coverage.1, coverage.2.1,
          storedCaches.maybeIntegrateWork result.work (some occurrence), nextCancelled⟩
      have folded := successGroupFold_retirement (failed := failed) generated nextMatching
        nextLinks canonical coverage.1 coverage.2.1 nextRoots taskNode.task.groups
      let final := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
      have finalMeta : RetirementMetadata final.1 work parents failed :=
        nextMeta.contributors (acc := (integrated, [], {})) taskNode.task.groups
      have startedMeta := finalMeta.startNewWork final.2.2
      rw [queue.taskSuccess_eq occurrence result taskNode found]
      split
      · exact ⟨roots.mono (fun _ member => member)
          (fun _ retired => retired.removeTask occurrence), retirement.removeTask occurrence⟩
      · exact State.drainReadyGroups_retirement (folded.1.startNewWork _ folded.2.1)
          ((folded.2.2 nextClosure).startNewWork _) generated startedMeta.groups
          startedMeta.links canonical startedMeta.live startedMeta.tasks startedMeta.caches

-----------------------------------------------------------------------------------------
-- Sequential stream integration retains certificates before the final drain
-----------------------------------------------------------------------------------------

/-- A matched item integration retains the metadata used by release-time draining.
Witness: matched lowered descriptors, registry coverage, and unchanged cache provenance.
-/
private theorem RetirementMetadata.item {queue : State} {work parents failed stream items}
    (prior : RetirementMetadata queue work parents failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : RetirementMetadata (queue.integrateStreamItem item) work parents failed := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  have coverage := queue.integrateStreamItem_registration prior.live prior.tasks matching member
  have cancellations := prior.cancelled.maybeIntegrateWork item.work none (by
    intro group groupMember
    obtain ⟨dependencies, known⟩ :=
      matching.streamItem_childGroups_recordAt member groupMember
    exact ⟨dependencies, known,
      (matching.streamItem_childGroups_parentCanonical canonical member groupMember).trans
        (congrArg List.head? (canonical _ _ known)).symm⟩)
  have prunedCancellations : pruned.1.CancelledRecordsSupported work failed := by
    simpa only [pruned, integrated, State.CancelledRecordsSupported,
      State.pruneEmptyGroups_cancelledGroups]
      using cancellations
  exact ⟨
    ((prior.groups.maybeIntegrateWork item.work
        (fun _ included =>
          matching.streamItem_childGroups_recordAt member included)).pruneEmptyGroups
      integrated.2.newGroups).startNewWork
      released,
    ((prior.links.maybeIntegrateWork item.work
        (fun _ included =>
          matching.streamItem_childGroups_parentCanonical canonical member
            included)).pruneEmptyGroups
      integrated.2.newGroups).startNewWork
      released,
    coverage.1,
    coverage.2.1,
    ((prior.caches.maybeIntegrateWork item.work).pruneEmptyGroups
      integrated.2.newGroups).startNewWork
      released,
    prunedCancellations.startNewWork released
  ⟩

/-- A complete stream-item handler retains protected roots and healthy retirement closure.
Witness: matched items introduce only ancestor-free roots, sequential integration cannot
prune those supported candidates, and the final drain preserves the resulting certificates.
No stream-availability or active-root health assumption is used.
-/
theorem State.streamItems_retirement {queue : State} {work failed parents}
    (roots : queue.RootAncestorsRetired work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    (unique : queue.GroupRefsUnique) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.RootAncestorsRetired work
      ∧ (queue.streamItems stream items).1.HealthyRetiredAncestors work failed := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  let invariant (current : State) := current.GroupRefsUnique
    ∧ current.RootAncestorsRetired work ∧ current.HealthyRetiredAncestors work failed
    ∧ RetirementMetadata current work parents failed
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : invariant acc.1) : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        have member := included (List.mem_cons_self : item ∈ item :: rest)
        have nextRefs := ((prior.1.maybeIntegrateWork item.work).pruneEmptyGroups
          (acc.1.maybeIntegrateWork item.work).2.newGroups).startNewWork
          { (acc.1.maybeIntegrateWork item.work).2 with newGroups :=
            ((acc.1.maybeIntegrateWork item.work).1.pruneEmptyGroups
              (acc.1.maybeIntegrateWork item.work).2.newGroups).2 }
        have integratedCancelled := prior.2.2.2.cancelled.maybeIntegrateWork item.work none
          (by
            intro group groupMember
            obtain ⟨dependencies, known⟩ :=
              eventMatches.streamItem_childGroups_recordAt member groupMember
            exact ⟨dependencies, known,
              (eventMatches.streamItem_childGroups_parentCanonical canonical member
                groupMember).trans (congrArg List.head? (canonical _ _ known)).symm⟩)
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released := { integrated.2 with newGroups := pruned.2 }
        have certificates := acc.1.maybeIntegrateWork_prune_retirement generated
          prior.2.2.2.groups prior.2.2.2.links canonical prior.2.2.2.live
          prior.2.2.2.tasks item.work
          (fun _ included => eventMatches.streamItem_childGroups_recordAt member included)
          (fun _ included =>
            eventMatches.streamItem_childGroups_parentCanonical canonical member included)
          (eventMatches.streamItem_childTasksCovered member) integratedCancelled
        have oldRoots : pruned.1.RootAncestorsRetired work :=
          prior.2.1.mono
            (by
              intro ref active
              change ref ∈ (integrated.1.pruneEmptyGroups integrated.2.newGroups).1.rootGroups
                at active
              rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups]
                at active
              exact active)
            (fun _ retired =>
              (retired.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups)
        exact ih (fun _ later => included (List.mem_cons_of_mem _ later)) (step acc item)
          ⟨nextRefs, oldRoots.startNewWork released certificates.1,
            (certificates.2 prior.2.2.1).startNewWork released,
            prior.2.2.2.item canonical eventMatches member⟩
  unfold State.streamItems
  split
  · exact ⟨roots, retirement⟩
  · have folded := loop items (fun _ member => member) (queue, [], [], [])
      ⟨unique, roots, retirement, matching, links, registered, tasks, supported, cancelled⟩
    exact State.drainReadyGroups_retirement folded.2.1 folded.2.2.1 generated
      folded.2.2.2.groups folded.2.2.2.links canonical folded.2.2.2.live
      folded.2.2.2.tasks folded.2.2.2.caches

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
