import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementIntegration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationFrames

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
      let property (current : State) := current.ChildLinksCanonical parents
        ∧ current.GroupNodesMatchWork work ∧ current.HealthyRetiredAncestors work failed
      rw [queue.taskFailure_eq occurrence errors taskNode found]
      refine (failureGroupFold_preserves_on property
                (fun ref => GroupRecordInvalidated work failed ref) ?_ errors
                taskNode.task.groups ?_
                (queue.putTaskNode { taskNode with rejection := some errors }, []) ?_).2.2
      · intro current ref valid invalid
        exact ⟨valid.1.removeGroup _, valid.2.1.removeGroup _,
          valid.2.2.removeGroup valid.1 valid.2.1 canonical ref invalid⟩
      · intro group member
        exact (GroupInvalidated.task ⟨producer, payload, known⟩
          (List.mem_map_of_mem member) (same.symm ▸ recorded)).toRecordInvalidated
      · exact ⟨links, groups, prior⟩

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
  started : queue.StartedTasksRegistered
  taskMatching : queue.RegisteredTasksMatch work
  sound : queue.GroupMembershipSound
  registration : queue.RegistrationFrame work

/-- Activation retains every metadata field needed for retirement preservation.
Witness: existing node, link, registry, and cache preservation theorems.
-/
private theorem RetirementMetadata.startNewWork {queue : State} {work parents failed}
    (prior : RetirementMetadata queue work parents failed) (released : NewWork)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : RetirementMetadata (queue.startNewWork released).1 work parents failed := by
  have registered := State.startNewWork_registration prior.live prior.tasks released
  exact ⟨prior.groups.startNewWork _, prior.links.startNewWork _,
    registered.1, registered.2, prior.caches.startNewWork _,
    prior.cancelled.startNewWork prior.caches prior.started prior.taskMatching prior.sound
      prior.groups prior.links canonical released,
    prior.started.startNewWork _, prior.taskMatching.startNewWork _, prior.sound.startNewWork _,
    prior.registration.startNewWork _⟩

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
        prior.caches.putGroupNode _, prior.cancelled, prior.started.putGroupNode _,
        prior.taskMatching.putGroupNode _,
        prior.sound.putGroupNode _ (prior.sound node member),
        prior.registration.putGroupNode _ (prior.live node member)⟩
    split
    · have registered := State.finishGroupSuccess_registration next.live next.tasks updated
      exact ⟨next.groups.finishGroupSuccess _, next.links.finishGroupSuccess _,
        registered.1, registered.2.1, next.caches.finishGroupSuccess _,
        next.cancelled.finishGroupSuccess _, next.started.finishGroupSuccess _,
        next.taskMatching.finishGroupSuccess _, next.sound.finishGroupSuccess _,
        next.registration.finishGroupSuccess _⟩
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
    (generated : ExecutedWork work) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (started : queue.StartedTasksRegistered)
    (taskMatching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (context : queue.RegistrationFrame work)
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
      have storedCaches : stored.CachedFailuresSupported work failed :=
        supported.putTaskNode _ (supported taskNode (List.mem_of_find?_eq_some found))
      have nextMatching : integrated.GroupNodesMatchWork work :=
        storedMatching.maybeIntegrateWork result.work
          (fun _ member => eventMatches.taskChildGroups_recordAt member) (some occurrence)
      have nextLinks : integrated.ChildLinksCanonical parents :=
        storedLinks.maybeIntegrateWork result.work
          (fun _ member => eventMatches.taskChildGroups_parentCanonical canonical member)
          (some occurrence)
      have producerRegistered := started taskNode (List.mem_of_find?_eq_some found)
      have storedContext := context.putTaskNode { taskNode with value := some result.value }
        producerRegistered
      have certificate := (context.children taskNode.task producerRegistered).sourceChild
        (State.taskNode?_some found).2 eventMatches
      have descriptors : ∀ group ∈ result.work.groups, ∃ dependencies,
          GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head? := by
        intro group member
        obtain ⟨dependencies, known⟩ := eventMatches.taskChildGroups_recordAt member
        exact ⟨dependencies, known,
          (eventMatches.taskChildGroups_parentCanonical canonical member).trans
            (congrArg List.head? (canonical _ _ known)).symm⟩
      have coverage := State.maybeIntegrateWork_registration storedLive storedTasks
        result.work certificate.contributors (some occurrence)
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
        generated storedLive descriptors certificate.parentRefs
      have storedStarted : stored.StartedTasksRegistered :=
        started.putTaskNode _ (started taskNode (List.mem_of_find?_eq_some found))
      have childTasks : ∀ task ∈ result.work.tasks, TaskMatches work task := by
        intro task member
        obtain ⟨address, payload, same, known⟩ := eventMatches.childTask_producer member
        exact ⟨⟨address, payload, some occurrence, same, known⟩,
          eventMatches.childTask_groupsExact member⟩
      have storedTasksMatch : stored.RegisteredTasksMatch work := taskMatching
      have storedSound : stored.GroupMembershipSound := sound
      have nextMeta : RetirementMetadata integrated work parents failed :=
        ⟨nextMatching, nextLinks, coverage.1, coverage.2.1,
          storedCaches.maybeIntegrateWork result.work (some occurrence), nextCancelled,
          storedStarted.maybeIntegrateWork result.work (some occurrence),
          storedTasksMatch.maybeIntegrateWork result.work childTasks (some occurrence),
          storedSound.maybeIntegrateWork result.work (some occurrence),
          (storedContext.maybeIntegrateWork result.work certificate (some occurrence)).1⟩
      have folded := successGroupFold_retirement (failed := failed) generated nextMatching
        nextLinks canonical coverage.1 coverage.2.1 nextRoots taskNode.task.groups
      let final := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
      have finalMeta : RetirementMetadata final.1 work parents failed :=
        nextMeta.contributors (acc := (integrated, [], {})) taskNode.task.groups
      have startedMeta := finalMeta.startNewWork final.2.2 canonical
      rw [queue.taskSuccess_eq occurrence result taskNode found]
      exact State.drainReadyGroups_retirement (folded.1.startNewWork _ folded.2.1)
        ((folded.2.2 nextClosure).startNewWork finalMeta.caches finalMeta.started
          finalMeta.taskMatching finalMeta.sound finalMeta.links finalMeta.groups
          canonical _)
        generated startedMeta.groups
        startedMeta.links canonical startedMeta.live startedMeta.tasks startedMeta.caches
        startedMeta.started startedMeta.taskMatching startedMeta.sound

-----------------------------------------------------------------------------------------
-- Sequential stream integration retains certificates before the final drain
-----------------------------------------------------------------------------------------

/-- A matched item integration retains the metadata used by release-time draining.
Witness: matched lowered descriptors, registry coverage, and unchanged cache provenance.
-/
private theorem RetirementMetadata.prunedItem {queue : State}
    {work parents failed stream items}
    (prior : RetirementMetadata queue work parents failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    : let integrated := queue.maybeIntegrateWork item.work
      RetirementMetadata (integrated.1.pruneEmptyGroups integrated.2.newGroups).1 work
        parents failed := by
  let integrated := queue.maybeIntegrateWork item.work
  have descriptors : ∀ group ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work group.node dependencies :=
    fun _ included => matching.streamItem_childGroups_recordAt member included
  have fields : ∀ group ∈ item.work.groups,
      group.parent = (parents group.node.ref).head? :=
    fun _ included => matching.streamItem_childGroups_parentCanonical canonical member included
  have knownTasks : ∀ task ∈ item.work.tasks, TaskMatches work task := by
    intro task included
    obtain ⟨address, payload, same, known⟩ := matching.streamItem_childTask_producer member included
    exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
      matching.streamItem_childTask_groupsExact member included⟩
  have certificate := prior.registration.source.sourceStreamItem matching member queue.registeredGroups
  have registered := queue.maybeIntegrateWork_registration prior.live prior.tasks item.work
    certificate.contributors
  have coverage := integrated.1.pruneEmptyGroups_registration registered.1 registered.2.1
    integrated.2.newGroups
  have cancelled := prior.cancelled.maybeIntegrateWork item.work none (by
    intro group included
    obtain ⟨dependencies, known⟩ := descriptors group included
    exact ⟨dependencies, known, by rw [canonical _ _ known]; exact fields group included⟩)
  refine ⟨((prior.groups.maybeIntegrateWork item.work descriptors).pruneEmptyGroups _),
    ((prior.links.maybeIntegrateWork item.work fields).pruneEmptyGroups _),
    coverage.1, coverage.2.1,
    ((prior.caches.maybeIntegrateWork item.work).pruneEmptyGroups _), ?_,
    ((prior.started.maybeIntegrateWork item.work).pruneEmptyGroups _),
    ((prior.taskMatching.maybeIntegrateWork item.work knownTasks).pruneEmptyGroups _),
    ((prior.sound.maybeIntegrateWork item.work).pruneEmptyGroups _),
    (prior.registration.maybeIntegrateWork item.work certificate).1.pruneEmptyGroups _⟩
  intro ref included
  apply cancelled ref
  simpa only [State.pruneEmptyGroups_cancelledGroups] using included

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
    (started : queue.StartedTasksRegistered)
    (taskMatching : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (context : queue.RegistrationFrame work)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    : (queue.streamItems stream items).1.RootAncestorsRetired work
      ∧ (queue.streamItems stream items).1.HealthyRetiredAncestors work failed := by
  let invariant (current : State) := current.GroupRefsUnique
    ∧ current.RootAncestorsRetired work ∧ current.HealthyRetiredAncestors work failed
    ∧ RetirementMetadata current work parents failed
  have loop (more : List StreamItem) (included : more.Subset items)
      (current : State) (prior : invariant current)
      : invariant (current.preparedStreamItems more) := by
    induction more generalizing current with
    | nil => exact prior
    | cons item rest ih =>
        have member := included List.mem_cons_self
        let integrated := current.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released := { integrated.2 with newGroups := pruned.2 }
        have prunedMeta := prior.2.2.2.prunedItem canonical eventMatches member
        have descriptors : ∀ group ∈ item.work.groups,
            ∃ dependencies, GroupRecordAt work group.node dependencies :=
          fun _ included => eventMatches.streamItem_childGroups_recordAt member included
        have fields : ∀ group ∈ item.work.groups,
            group.parent = (parents group.node.ref).head? :=
          fun _ included => eventMatches.streamItem_childGroups_parentCanonical canonical
            member included
        have certificates := current.maybeIntegrateWork_prune_retirement (failed := failed) generated
          prior.2.2.2.groups prior.2.2.2.links canonical prior.2.2.2.live
          prior.2.2.2.tasks item.work descriptors fields
          (eventMatches.streamItem_childTasksCovered generated.declarations member)
          (prior.2.2.2.registration.source.sourceStreamItem eventMatches member
            current.registeredGroups).parentRefs
        have oldRoots : pruned.1.RootAncestorsRetired work :=
          prior.2.1.mono
            (by
              intro ref active
              change ref ∈ pruned.1.rootGroups at active
              rw [State.pruneEmptyGroups_rootGroups, State.maybeIntegrateWork_rootGroups]
                at active
              exact active)
            (fun _ retired =>
              (retired.maybeIntegrateWork item.work).pruneEmptyGroups integrated.2.newGroups)
        have nextRefs := ((prior.1.maybeIntegrateWork item.work).pruneEmptyGroups
          integrated.2.newGroups).startNewWork released
        have next := ih (fun _ later => included (List.mem_cons_of_mem _ later))
          (current.integrateStreamItem item)
          ⟨nextRefs, oldRoots.startNewWork released certificates.1,
            (certificates.2 prior.2.2.1).startNewWork prunedMeta.caches prunedMeta.started
              prunedMeta.taskMatching prunedMeta.sound prunedMeta.links prunedMeta.groups
              canonical released,
            prunedMeta.startNewWork released canonical⟩
        rwa [current.preparedStreamItems_cons]
  rw [queue.streamItems_eq stream items]
  split
  · exact ⟨roots, retirement⟩
  · have folded := loop items (List.Subset.refl _) queue
      ⟨unique, roots, retirement, matching, links, registered, tasks, supported, cancelled,
        started, taskMatching, sound, context⟩
    exact State.drainReadyGroups_retirement folded.2.1 folded.2.2.1 generated
      folded.2.2.2.groups folded.2.2.2.links canonical folded.2.2.2.live
      folded.2.2.2.tasks folded.2.2.2.caches folded.2.2.2.started
      folded.2.2.2.taskMatching folded.2.2.2.sound

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
