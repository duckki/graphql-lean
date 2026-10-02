import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupAccounting

/-! Generated producer support for healthy child-group registration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.Ancestry Semantics.GeneralScheduling

-----------------------------------------------------------------------------------------
-- Structural lowering retains generated defer support
-----------------------------------------------------------------------------------------

/-- Generated work retains the executor's key bounds and defer-continuity certificate.
Witness: instantiate root execution's metadata theorem at the generating execution. -/
private theorem ExecutedWork.deferMetadata {work : Execution.Work}
    (generated : ExecutedWork work)
    : ∃ parents bound,
        Valid parents bound
        ∧ Semantics.MixedKeys.WorkAt parents 0 bound work
        ∧ DeferContinuous parents work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, equal⟩ := generated
  obtain ⟨_, parents, valid, coherent, continuous⟩ :=
    executeRoot_continuity schema resolvers variables fuel parentType source selections 0
  exact ⟨parents, _, valid, equal ▸ coherent, equal ▸ continuous⟩

/-- A located subtree retains defer continuity, including below stream items.
Witness: navigation induction through the executor's recursive certificate. -/
private theorem deferContinuous_located
    {parents work address current producer enclosing}
    (continuous : DeferContinuous parents work)
    (located : Located work address current producer enclosing)
    : DeferContinuous parents current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact continuous
  | left _ ih => rw [DeferContinuous] at ih; exact ih.1
  | right _ ih => rw [DeferContinuous] at ih; exact ih.2
  | executionGroup _ ih => rw [DeferContinuous] at ih; exact ih.2
  | item _ entry ih => rw [DeferContinuous] at ih; exact ih _ (List.mem_of_getElem? entry)

/-- Each immediate task contributor belongs to the current defer region.
Witness: lowering descends through combines but stops at group and stream boundaries. -/
private theorem workFromSpec_contributor_in_deferRegion
    (work : Execution.Work) (address : Address) {task : Task} {key : Nat}
    (member : task ∈ (Work.fromExecution work address).tasks)
    (contributor : key ∈ task.groups.map Execution.DeliveryNode.key)
    : key ∈ deferRegionKeys work := by
  cases work with
  | empty => cases member
  | combine left right =>
      rcases List.mem_append.mp member with inLeft | inRight
      · exact List.mem_append_left _
          (workFromSpec_contributor_in_deferRegion left _ inLeft contributor)
      · exact List.mem_append_right _
          (workFromSpec_contributor_in_deferRegion right _ inRight contributor)
  | executionGroup groups path result children =>
      obtain rfl := List.mem_singleton.mp member
      exact List.mem_append_left _ (by simpa [mapKeys, List.map_map] using contributor)
  | stream => cases member
termination_by sizeOf work

/-- A concrete group descriptor uses the coherent work's full ancestor assignment.
Witness: inspect its located execution group and the fragment metadata certificate. -/
private theorem coherent_group_dependencies_eq
    {parents lower bound work node dependencies producer}
    (coherent : Semantics.MixedKeys.WorkAt parents lower bound work)
    (known : NodeAt work node .group dependencies producer)
    : dependencies = parents node.key := by
  obtain ⟨address, groups, path, result, children, enclosing, fragment,
    located, member, sameNode, sameDependencies⟩ := known
  have localWork := coherent_located coherent located
  rw [Semantics.MixedKeys.WorkAt] at localWork
  rw [sameDependencies, sameNode]
  exact (localWork.2.1 fragment member).2.2

/-- Every task-owning child group reuses a producer contributor or descends from one.
Witness: source matching identifies the child lowering; execution's defer continuity
supplies support, and coherent metadata identifies the child's actual ancestors.
Ancestor-only registration candidates do not satisfy the task-ownership premise. -/
theorem GraphEvent.MatchesWork.childGroup_producer_support
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (generated : ExecutedWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    (contributing
      : ∃ task ∈ result.work.tasks,
          group.node.key ∈ task.groups.map Execution.DeliveryNode.key)
    : ∃ dependencies,
        NodeAt work group.node .group dependencies (some occurrence)
        ∧ ∃ owner ∈ result.value.deliveryGroups.map Execution.DeliveryNode.key,
            owner = group.node.key ∨ owner ∈ dependencies := by
  obtain ⟨task, taskMember, contributor⟩ := contributing
  obtain ⟨taskAddress, payload, taskEq, taskAt⟩ := matching.childTask_producer taskMember
  obtain ⟨node, dependencies, descriptor, sameKey⟩ :=
    TaskAt.executionGroup_owner (taskEq ▸ taskAt) contributor
  obtain ⟨recordDependencies, record⟩ := matching.taskChildGroups_recordAt member
  have sameNode := generated.record_eq_node record descriptor sameKey.symm
  have childKnown : NodeAt work group.node .group dependencies (some occurrence) :=
    sameNode.symm ▸ descriptor
  obtain ⟨parents, bound, _, coherent, continuous⟩ := generated.deferMetadata
  obtain ⟨owners, producer, known, exactGroups, childrenWork⟩ := matching
  cases occurrence with
  | item => cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
      have lowering : result.work = Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      have sameGroups : groups.map Execution.DeferredFragment.node
          = result.value.deliveryGroups := by
        simpa [taskGroups?, located] using exactGroups
      rw [lowering] at taskMember
      have localContinuity := deferContinuous_located continuous located
      obtain ⟨owner, contributes, support⟩ := localContinuity.child_key_supported
        (workFromSpec_contributor_in_deferRegion children _ taskMember contributor)
      refine ⟨dependencies, childKnown, owner, ?_, ?_⟩
      · rw [← sameGroups]
        simpa [mapKeys, List.map_map] using contributes
      · rw [coherent_group_dependencies_eq coherent childKnown]
        exact support

/-- A parentless task-owning child cannot introduce an independent defer root.
Witness: its canonical ancestor list is empty, so producer support must be direct reuse.
This explains the structural side of task success ignoring new group-root candidates. -/
theorem GraphEvent.MatchesWork.childGroup_parentless_reused
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (generated : ExecutedWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    (contributing
      : ∃ task ∈ result.work.tasks,
          group.node.key ∈ task.groups.map Execution.DeliveryNode.key)
    (parentless : group.parent = none)
    : group.node.key ∈ result.value.deliveryGroups.map Execution.DeliveryNode.key := by
  obtain ⟨dependencies, known, owner, contributes, support⟩ :=
    matching.childGroup_producer_support generated member contributing
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have sameParent := matching.taskChildGroups_parentCanonical canonical member
  rw [← canonical _ _ (groupRecordAt_of_nodeAt known), parentless] at sameParent
  have empty : dependencies = [] := by
    cases dependencies with
    | nil => rfl
    | cons head tail => simp at sameParent
  rcases support with same | ancestor
  · exact same ▸ contributes
  · simp [empty] at ancestor

/-- Immediate task contributors preserve a subtree's lower key bound.
Witness: combine descent and the located execution group's fragment certificate. -/
private theorem workFromSpec_contributors_lower
    {parents lower bound} (work : Execution.Work) (address : Address)
    (coherent : Semantics.MixedKeys.WorkAt parents lower bound work)
    {task : Task} {key : Nat} (member : task ∈ (Work.fromExecution work address).tasks)
    (contributor : key ∈ task.groups.map Execution.DeliveryNode.key)
    : lower ≤ key := by
  cases work with
  | empty => cases member
  | combine left right =>
      rw [Semantics.MixedKeys.WorkAt] at coherent
      rcases List.mem_append.mp member with inLeft | inRight
      · exact workFromSpec_contributors_lower left _ coherent.1 inLeft contributor
      · exact workFromSpec_contributors_lower right _ coherent.2 inRight contributor
  | executionGroup groups path result children =>
      rw [Semantics.MixedKeys.WorkAt] at coherent
      obtain rfl := List.mem_singleton.mp member
      have owner : key ∈ mapKeys groups := by simpa [mapKeys, List.map_map] using contributor
      obtain ⟨fragment, fragmentMember, same⟩ := List.mem_map.mp owner
      exact same ▸ (coherent.2.1 fragment fragmentMember).1
  | stream => cases member
termination_by sizeOf work

/-- A stream item's task-owning child groups follow the producing stream's key.
Witness: item completion starts a fresh defer-key region. This ordering alone does not
prove that another already-integrated item cannot reference the same key. -/
theorem GraphEvent.MatchesWork.streamItem_childGroup_key_gt
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items)
    {group : Group}
    (contributing
      : ∃ task ∈ item.work.tasks,
          group.node.key ∈ task.groups.map Execution.DeliveryNode.key)
    : stream.key < group.node.key := by
  obtain ⟨parents, bound, _, coherent, _⟩ := generated.deferMetadata
  obtain ⟨task, taskMember, contributor⟩ := contributing
  obtain ⟨owners, producer, known, childrenWork⟩ := matching item itemMember
  cases occurrence : item.occurrence with
  | executionGroup => simp [streamItemWork?, occurrence] at childrenWork
  | item address index =>
      rw [occurrence] at known
      obtain ⟨node, entries, enclosing, result, children, located, entry, _, samePayload⟩ :=
        known
      have sameNode : node = stream := by cases samePayload; rfl
      subst node
      change locateWork work address = some ⟨.stream stream entries, producer, enclosing⟩
        at located
      have lowering : item.work = Work.fromExecution children (address ++ [index]) := by
        simpa [streamItemWork?, occurrence, located, entry] using childrenWork.symm
      have localWork := coherent_located coherent located
      rw [Semantics.MixedKeys.WorkAt] at localWork
      have childBound := localWork.2.2 _ (List.mem_of_getElem? entry)
      rw [lowering] at taskMember
      exact workFromSpec_contributors_lower children _ childBound taskMember contributor

-----------------------------------------------------------------------------------------
-- The unsettled producer protects reused keys and supports new descendants
-----------------------------------------------------------------------------------------

/-- Before a producer settles, each healthy child group has a live, nonempty supporting
producer group: the child itself or one of its defer ancestors. Witness: generated
support, contrapositive failure propagation, and the healthy task/pending ledgers. -/
theorem State.HealthyRegisteredTaskAccounting.childGroup_live_support
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    {producer : Task} (producerMember : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    (contributing
      : ∃ task ∈ result.work.tasks,
          group.node.key ∈ task.groups.map Execution.DeliveryNode.key)
    (healthy : ¬GroupInvalidated work failed group.node.key)
    : ∃ dependencies,
        NodeAt work group.node .group dependencies (some producer.occurrence)
        ∧ ∃ node ∈ queue.groupNodes,
            ¬GroupInvalidated work failed node.group.node.key
            ∧ node.group.node.key ∈ producer.groups.map Execution.DeliveryNode.key
            ∧ producer.occurrence ∈ node.tasks
            ∧ node.pending ≠ 0
            ∧ (node.group.node.key = group.node.key
                ∨ node.group.node.key ∈ dependencies) := by
  obtain ⟨dependencies, known, owner, contributes, support⟩ :=
    matching.childGroup_producer_support generated member contributing
  obtain ⟨_, _, _, exactGroups, _⟩ := matching
  have sameGroups : producer.groups = result.value.deliveryGroups :=
    Option.some.inj ((taskMatching producer producerMember).2.symm.trans exactGroups)
  have ownerHealthy : ¬GroupInvalidated work failed owner := by
    intro failure
    apply healthy
    rcases support with same | ancestor
    · exact same ▸ failure
    · exact .groupDependency ⟨group.node, _, known, rfl⟩ ancestor failure
  have producerContributes : owner ∈ producer.groups.map Execution.DeliveryNode.key := by
    rw [sameGroups]
    exact contributes
  obtain ⟨node, nodeMember, sameKey, linked⟩ :=
    accounted producer producerMember fresh owner producerContributes ownerHealthy
  have nodeHealthy : ¬GroupInvalidated work failed node.group.node.key :=
    sameKey.symm ▸ ownerHealthy
  have nonzero : node.pending ≠ 0 := by
    intro zero
    exact fresh (GroupNode.PendingTracks.allSettled node settled
      (tracks node nodeMember nodeHealthy) zero producer.occurrence linked)
  exact ⟨dependencies, known, node, nodeMember, nodeHealthy,
    sameKey.symm ▸ producerContributes, linked, nonzero,
    sameKey.symm ▸ support⟩

/-- Directly reused producer keys are already available for healthy child integration.
Witness: the producer's existing task membership keeps the contributor group live. -/
theorem State.HealthyRegisteredTaskAccounting.childGroup_available_of_reused
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work) {producer : Task}
    (producerMember : producer ∈ queue.tasks) (fresh : producer.occurrence ∉ settled)
    {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    {key : Nat}
    (reused : key ∈ result.value.deliveryGroups.map Execution.DeliveryNode.key)
    (healthy : ¬GroupInvalidated work failed key)
    : queue.GroupAvailable key := by
  obtain ⟨_, _, _, exactGroups, _⟩ := matching
  have sameGroups : producer.groups = result.value.deliveryGroups :=
    Option.some.inj ((taskMatching producer producerMember).2.symm.trans exactGroups)
  apply accounted.groupAvailable producerMember fresh _ healthy
  simpa [sameGroups] using reused

/-- If child tasks only reuse producer contributor keys, registration availability is
fully discharged. Witness: each healthy reused key has the unsettled producer's live
membership. This is a structural condition on child work, not an output-admission law. -/
theorem State.HealthyRegisteredTaskAccounting.childGroupsAvailable_of_reused
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    {producer : Task} (producerMember : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    (reused
      : ∀ task ∈ result.work.tasks,
          (task.groups.map Execution.DeliveryNode.key).Subset
            (result.value.deliveryGroups.map Execution.DeliveryNode.key))
    : queue.ChildGroupsAvailable work failed result.work := by
  intro task member key contributor healthy
  exact accounted.childGroup_available_of_reused taskMatching producerMember fresh matching
    (reused task member contributor) healthy

/-- Parentless child work needs no separate registration-availability assumption.
Witness: every task key has an immediate group candidate, and each parentless generated
candidate reuses a producer key protected by the producer's pending membership. -/
theorem State.HealthyRegisteredTaskAccounting.childGroupsAvailable_of_parentless
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    {producer : Task} (producerMember : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    (parentless : ∀ group ∈ result.work.groups, group.parent = none)
    : queue.ChildGroupsAvailable work failed result.work := by
  apply accounted.childGroupsAvailable_of_reused taskMatching producerMember fresh matching
  intro task member key contributor
  obtain ⟨group, groupMember, sameKey⟩ := matching.childTasksCovered task member key contributor
  exact sameKey ▸ matching.childGroup_parentless_reused generated groupMember
    ⟨task, member, sameKey.symm ▸ contributor⟩ (parentless group groupMember)

/-- Any unavailable healthy child of a task success has a strictly earlier live ancestor
with the producer still pending. Witness: eliminate direct reuse from live support;
generated ancestor ordering supplies the strict key inequality. -/
theorem State.HealthyRegisteredTaskAccounting.unavailable_child_live_ancestor
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (tracks : queue.HealthyPendingTracks work settled failed)
    (taskMatching : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    {producer : Task} (producerMember : producer ∈ queue.tasks)
    (fresh : producer.occurrence ∉ settled) {result : TaskResult}
    (matching : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    (contributing
      : ∃ task ∈ result.work.tasks,
          group.node.key ∈ task.groups.map Execution.DeliveryNode.key)
    (healthy : ¬GroupInvalidated work failed group.node.key)
    (unavailable : ¬queue.GroupAvailable group.node.key)
    : ∃ dependencies,
        NodeAt work group.node .group dependencies (some producer.occurrence)
        ∧ ∃ node ∈ queue.groupNodes,
            ¬GroupInvalidated work failed node.group.node.key
            ∧ node.group.node.key ∈ producer.groups.map Execution.DeliveryNode.key
            ∧ producer.occurrence ∈ node.tasks
            ∧ node.pending ≠ 0
            ∧ node.group.node.key ∈ dependencies
            ∧ node.group.node.key < group.node.key := by
  obtain ⟨dependencies, known, node, nodeMember, nodeHealthy, contributes,
    linked, nonzero, support⟩ :=
    accounted.childGroup_live_support tracks taskMatching generated producerMember fresh
      matching member contributing healthy
  rcases support with same | ancestor
  · exact False.elim (unavailable (.inl (List.mem_map.mpr ⟨node, nodeMember, same⟩)))
  · exact ⟨dependencies, known, node, nodeMember, nodeHealthy, contributes,
      linked, nonzero, ancestor,
      generated.groupAncestorSmaller known ancestor⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
