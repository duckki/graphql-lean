import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentCutsHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedGroupCoverage

/-! Live ancestry coverage uses actual cancellation markers and consumed successes.
Cached failed latent contributors retain their structural support before notification.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Follow live parent links, or recover a successful retirement at the first missing parent
-----------------------------------------------------------------------------------------

/-- A task-bearing ancestor of any live record is linked or retired uncancelled.
Witness: follow canonical live parents. At a missing parent, structural retirement closes
the ancestor chain and its marker certificate excludes cancellation. The child may have
a cached failure, and no root coverage or output admission is assumed.
-/
theorem State.ParentLinksComplete.supported_ancestor_or_retired
    {queue : State} {work parents child dependencies ancestor occurrence owners}
    (links : queue.ParentLinksComplete parents) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (retirement : queue.UncancelledRetiredAncestors work)
    (markers : queue.UncancelledRetiredMarkers work)
    (safe : queue.LiveParentsUncancelled) (fields : queue.GroupParentsCanonical parents)
    (registered : queue.LiveGroupsRegistered)
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (found : queue.groupNode? child.group.node.ref = some child)
    (known : GroupRecordAt work child.group.node dependencies)
    (member : ancestor ∈ dependencies) (task : TaskHasOwners work occurrence owners)
    (contributes : ancestor ∈ owners)
    : queue.LiveDescendant ancestor child.group.node.ref
      ∨ (queue.RetiredGroup ancestor ∧ ancestor ∉ queue.cancelledGroups) := by
  induction dependencies generalizing child with
  | nil => cases member
  | cons parent rest ih =>
      have childMember := List.mem_of_find?_eq_some found
      have parentEq : child.group.parent = some parent := by
        rw [fields child childMember, ← canonical _ _ known]
        rfl
      have uncancelled := safe child childMember parent parentEq
      cases parentFound : queue.groupNode? parent with
      | none =>
          have retired : queue.RetiredGroup parent := .of_lookup_none
            (registry child.group.node.ref (registered child childMember) parent
              (by rw [← canonical _ _ known]; rfl)) parentFound
          obtain ⟨parentNode, parentKey, parentKnown⟩ := known.parent
          apply Or.inr
          rcases List.mem_cons.mp member with same | above
          · exact ⟨same ▸ retired, same ▸ uncancelled⟩
          · exact ⟨retirement parent retired uncancelled parentNode rest parentKnown
              parentKey ancestor above occurrence owners task contributes,
              markers parent retired uncancelled parentNode rest parentKnown parentKey
                ancestor above occurrence owners task contributes⟩
      | some parentNode =>
          have parentKey := State.groupNode?_ref parentFound
          have head : (parent :: rest).head? = some parentNode.group.node.ref := by
            simp [parentKey]
          have linked := links child childMember parentNode
            (List.mem_of_find?_eq_some parentFound) (by rw [← canonical _ _ known]; exact head)
          have edge : queue.LiveDescendant parentNode.group.node.ref child.group.node.ref :=
            .child (parentKey.symm ▸ parentFound) linked (.self found)
          rcases List.mem_cons.mp member with same | above
          · exact Or.inl (by simpa only [parentKey, same] using edge)
          · obtain ⟨parentDependencies, parentKnown⟩ := records parentNode
              (List.mem_of_find?_eq_some parentFound)
            have tail : rest = parentDependencies :=
              (List.cons.inj (generated.groupRecordAncestryChain known parentKnown head)).2
            rcases ih (parentKey.symm ▸ parentFound) (tail.symm ▸ parentKnown) above with
              path | retired
            · exact Or.inl (path.trans edge)
            · exact Or.inr retired

-----------------------------------------------------------------------------------------
-- A fresh producer prevents successful retirement of its supporting contributor
-----------------------------------------------------------------------------------------

/-- Every live task-produced contributor connects to a live producer owner, even if failed.
Witness: generated producer support, permanent registration, and the live-or-retired
dichotomy. An uncancelled retired supporting owner would make the producer already settled.
The supplied coverage concerns only earlier contributors, never the new target.
-/
theorem State.UncancelledTaskAccounting.live_childGroup_integrated_root_coverage
    {queue : State} {work : Execution.Work} {parents settled}
    (accounted : queue.UncancelledTaskAccounting settled)
    (taskMatching : queue.RegisteredTasksMatch work) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (retirement : queue.UncancelledRetiredAncestors work)
    (markers : queue.UncancelledRetiredMarkers work)
    (safe : queue.LiveParentsUncancelled) (fields : queue.GroupParentsCanonical parents)
    (links : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents)
    (context : queue.RegistrationFrame work) (cancelled : queue.CancellationsRetired)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {producer : Task} (producerMember : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    {task : Task} {ref : NodeRef} (member : task ∈ result.work.tasks)
    (contributing : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (covered
      : ∀ key ∈ producer.groups.map Execution.DeliveryNode.ref,
          (∃ node, queue.groupNode? key = some node)
          → ∃ root ∈ queue.rootGroups, queue.LiveDescendant root key)
    : let integrated :=
        (queue.maybeIntegrateWork result.work (some producer.occurrence)).1
      (∃ node, integrated.groupNode? ref = some node)
      → ∃ root ∈ integrated.rootGroups, integrated.LiveDescendant root ref := by
  intro integrated survives
  obtain ⟨childDescriptor, dependencies, childKnown, refEq, owner, contributes, support⟩ :=
    matching.childContributor_producer_support generated member contributing
  have ⟨_, _, _, exactGroups, _⟩ := matching
  have sameGroups : producer.groups = result.value.deliveryGroups :=
    Option.some.inj ((taskMatching producer producerMember).2.symm.trans exactGroups)
  have producerContributes : owner ∈ producer.groups.map Execution.DeliveryNode.ref := by
    rwa [sameGroups]
  have groupCanonical : ∀ candidate ∈ result.work.groups,
      candidate.parent = (parents candidate.node.ref).head? :=
    fun _ included => matching.taskChildGroups_parentCanonical canonical included
  have newRecords : ∀ candidate ∈ result.work.groups,
      ∃ ancestors, GroupRecordAt work candidate.node ancestors :=
    fun _ included => matching.taskChildGroups_recordAt included
  have newMatching := records.maybeIntegrateWork result.work newRecords
    (some producer.occurrence)
  have newLinks := links.maybeIntegrateWork unique registered closed result.work
    groupCanonical (some producer.occurrence)
  have certificate := (context.children producer producerMember).sourceChild rfl matching
  have descriptors : ∀ candidate ∈ result.work.groups, ∃ ancestors,
      GroupRecordAt work candidate.node ancestors ∧ candidate.parent = ancestors.head? := by
    intro candidate member
    obtain ⟨ancestors, known⟩ := newRecords candidate member
    exact ⟨ancestors, known, by rw [canonical _ _ known]; exact groupCanonical candidate member⟩
  have newRegistered := queue.maybeIntegrateWork_registration registered tasks result.work
    certificate.contributors (some producer.occurrence)
  have newRegistry := closed.maybeIntegrateWork registered result.work groupCanonical
    certificate.parents (some producer.occurrence)
  have newSafe := safe.maybeIntegrateWork registered closed fields result.work groupCanonical
    cancelled generated newRecords canonical certificate.parents (some producer.occurrence)
  obtain ⟨child, childFound⟩ := survives
  obtain ⟨childDependencies, childRecord⟩ := newMatching child
    (List.mem_of_find?_eq_some childFound)
  have descriptor := generated.record_eq_node childRecord childKnown
    ((State.groupNode?_ref childFound).trans refEq.symm)
  have childPath : integrated.LiveDescendant owner ref := by
    rcases support with same | ancestor
    · rw [same]
      exact .self childFound
    · obtain ⟨⟨_, payload, taskProducer, _, knownTask⟩, _⟩ := taskMatching producer producerMember
      have boundary := newLinks.supported_ancestor_or_retired generated newMatching
        (retirement.maybeIntegrateWork result.work (some producer.occurrence)
          generated registered descriptors certificate.parentRefs)
        (markers.maybeIntegrateWork closed canonical result.work (some producer.occurrence)
          generated registered descriptors certificate.parentRefs) newSafe
        (fields.maybeIntegrateWork result.work groupCanonical (some producer.occurrence))
        newRegistered.1 newRegistry canonical
        ((State.groupNode?_ref childFound).symm ▸ childFound) childRecord
        (by simpa only [canonical _ _ childRecord,
          canonical _ _ (groupRecordAt_of_nodeAt childKnown), descriptor] using ancestor)
        (show TaskHasOwners work producer.occurrence
          (producer.groups.map Execution.DeliveryNode.ref) from ⟨taskProducer, payload, knownTask⟩)
        producerContributes
      rcases boundary with path | ⟨retired, ownerUncancelled⟩
      · simpa only [descriptor, refEq] using path
      · have oldRetired : queue.RetiredGroup owner := by
          cases found : queue.groupNode? owner with
          | none =>
              exact .of_lookup_none (tasks producer producerMember owner producerContributes) found
          | some node =>
              have present := queue.maybeIntegrateWork_includesRefs result.work
                (some producer.occurrence) owner (List.mem_map.mpr
                  ⟨node, List.mem_of_find?_eq_some found, State.groupNode?_ref found⟩)
              exact False.elim (retired.2 present)
        exact False.elim
          (fresh
            (accounted.retired_contributor_settled producerMember producerContributes
              (by
                intro marked
                apply ownerUncancelled
                rw [State.maybeIntegrateWork_cancelledGroups _ _
                      (some producer.occurrence)]
                exact queue.addGroups_cancelledGroups_subset result.work.groups marked)
              oldRetired))
  have oldLive : ∃ node, queue.groupNode? owner = some node := by
    cases found : queue.groupNode? owner with
    | some node => exact ⟨node, rfl⟩
    | none =>
        have retired := (State.RetiredGroup.of_lookup_none
          (tasks producer producerMember owner producerContributes) found).maybeIntegrateWork
            result.work (some producer.occurrence)
        obtain ⟨node, live⟩ := childPath.found
        rw [retired.lookup_none] at live
        contradiction
  obtain ⟨root, active, path⟩ := covered owner producerContributes oldLive
  exact ⟨
    root,
    by rwa [State.maybeIntegrateWork_rootGroups],
    (path.maybeIntegrateWork unique result.work (some producer.occurrence)).trans
      childPath
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
