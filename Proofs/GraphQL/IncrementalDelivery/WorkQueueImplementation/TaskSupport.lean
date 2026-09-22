import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A task supports registration of its contributors and their full ancestor chains
-----------------------------------------------------------------------------------------

/-- A task's structural occurrence supports `key` through a contributor or its ancestors.
This does not assert that the key contributes to the task or that the task has started.
-/
def Task.SupportsGroup (work : Execution.Work) (task : Task) (key : Nat) : Prop :=
  ∃ address groups path result children producer owners fragment,
    task.occurrence = .executionGroup address
    ∧ Located work address (.executionGroup groups path result children) producer owners
    ∧ fragment ∈ groups
    ∧ key ∈ fragment.node.key :: fragment.ancestors.map Execution.DeliveryNode.key

/-- A supporting task supplies an actual contributor-or-ancestor registration descriptor.
Witness: split its full chain at the supported key and retain the remaining suffix.
-/
theorem Task.SupportsGroup.recordAt {work : Execution.Work} {task : Task} {key : Nat}
    (supported : task.SupportsGroup work key)
    : ∃ node dependencies, GroupRecordAt work node dependencies ∧ node.key = key := by
  obtain ⟨address, groups, path, result, children, producer, owners, fragment,
    _, located, member, contains⟩ := supported
  have mapped : key ∈ (fragment.node :: fragment.ancestors).map Execution.DeliveryNode.key :=
    contains
  obtain ⟨node, inChain, sameKey⟩ := List.mem_map.mp mapped
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp inChain
  refine ⟨node, after.map Execution.DeliveryNode.key,
    ⟨address, groups, path, result, children, producer, owners, fragment,
      after, located, member, ?_, rfl⟩, sameKey⟩
  exact ⟨before, split.symm⟩

/-- Every lowered group candidate has an immediate task supporting its full-chain key.
Witness: choose the contributing fragment used by lowering; combine preserves witnesses.
-/
theorem workFromSpec_groups_taskSupport
    {root current : Execution.Work} {address producer owners}
    (located : Located root address current producer owners)
    {group : Group} (member : group ∈ (Work.fromExecution current address).groups)
    : ∃ task ∈ (Work.fromExecution current address).tasks,
        task.SupportsGroup root group.node.key := by
  cases current with
  | empty => cases member
  | combine left right =>
      rcases List.mem_append.mp member with inLeft | inRight
      · obtain ⟨task, taskMember, support⟩ := workFromSpec_groups_taskSupport located.left inLeft
        exact ⟨task, List.mem_append_left _ taskMember, support⟩
      · obtain ⟨task, taskMember, support⟩ := workFromSpec_groups_taskSupport located.right inRight
        exact ⟨task, List.mem_append_right _ taskMember, support⟩
  | executionGroup groups path result children =>
      obtain ⟨fragment, fragmentMember, chainMember⟩ := List.mem_flatMap.mp member
      obtain ⟨ancestors, suffix, _⟩ := workFromSpec_groupChain_member chainMember
      refine ⟨⟨.executionGroup address, groups.map Execution.DeferredFragment.node⟩,
        List.mem_cons_self, address, groups, path, result, children, producer, owners,
        fragment, rfl, located, fragmentMember, ?_⟩
      exact List.mem_map.mpr ⟨group.node, suffix.sublist.subset List.mem_cons_self, rfl⟩
  | stream => cases member
termination_by sizeOf current

/-- Matched task results carry a supporting child task for every registration candidate.
Witness: exact source child lowering, located under the successful producer.
-/
theorem GraphEvent.MatchesWork.childGroupsSupported
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    : ∃ task ∈ result.work.tasks, task.SupportsGroup work group.node.key := by
  obtain ⟨_, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item => cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
      have lowering : result.work = Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [lowering] at member ⊢
      exact workFromSpec_groups_taskSupport (Located.executionGroup located) member

/-- Matched stream items likewise carry task support for every new registration candidate.
Witness: exact item-child lowering at its structural item address.
-/
theorem GraphEvent.MatchesWork.streamItem_groupsSupported
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items)
    {group : Group} (member : group ∈ item.work.groups)
    : ∃ task ∈ item.work.tasks, task.SupportsGroup work group.node.key := by
  obtain ⟨_, producer, known, childrenWork⟩ := matching item itemMember
  cases occurrence : item.occurrence with
  | executionGroup => simp [streamItemWork?, occurrence] at childrenWork
  | item address index =>
      rw [occurrence] at known
      obtain ⟨node, entries, enclosing, result, children, located, entry, _, _⟩ := known
      change locateWork work address = some ⟨.stream node entries, producer, enclosing⟩ at located
      have lowering : item.work = Work.fromExecution children (address ++ [index]) := by
        simpa [streamItemWork?, occurrence, located, entry] using childrenWork.symm
      rw [lowering] at member ⊢
      exact workFromSpec_groups_taskSupport (Located.item located entry) member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
