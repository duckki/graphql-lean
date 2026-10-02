import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork

/-! Host-event freshness, successful outcomes, and child-work provenance. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The host settles each task and stream at most once
-----------------------------------------------------------------------------------------

/-- Every prefix of a legal host-event history is legal. Witness: remove final events
from the source's append derivation; no queue or output-accounting facts are needed.
-/
theorem ValidGraphEvents.prefix {work events before}
    (valid : ValidGraphEvents work events) (earlier : before.IsPrefix events)
    : ValidGraphEvents work before := by
  induction valid with
  | nil =>
      have empty := List.eq_nil_of_prefix_nil earlier
      subst before
      exact .nil
  | @append prior event validPrior matching fresh ready ih =>
      rcases List.prefix_concat_iff.mp earlier with same | shorter
      · rw [same]
        exact .append validPrior matching fresh ready
      · exact ih shorter

/-- A valid graph-event prefix contains no repeated task/item settlement or stream
closure. Witness: induct over the source's one-event-at-a-time freshness rule.
-/
theorem ValidGraphEvents.identities_nodup {work events}
    (valid : ValidGraphEvents work events)
    : (events.flatMap (fun event => event.identities.1)).Nodup
      ∧ (events.flatMap (fun event => event.identities.2)).Nodup := by
  induction valid with
  | nil => simp
  | @append before event _ matching fresh ready ih =>
      simp only [List.flatMap_append, List.flatMap_singleton]
      constructor
      · apply List.nodup_append.mpr
        exact ⟨ih.1, fresh.1, by
          intro task earlier sameTask later equal
          subst sameTask
          exact (fresh.2.2.1 task later) earlier⟩
      · apply List.nodup_append.mpr
        exact ⟨ih.2, fresh.2.1, by
          intro stream earlier sameStream later equal
          subst sameStream
          exact (fresh.2.2.2 stream later) earlier⟩

/-- Every successful host settlement identifies a task whose fixed Work outcome is
successful. Witness: the event's exact-outcome matching clause.
-/
theorem GraphEvent.MatchesWork.successes_succeed {work} {event : GraphEvent}
    (matching : event.MatchesWork work)
    {occurrence} (member : occurrence ∈ event.successes)
    : TaskSucceeds work occurrence := by
  cases event with
  | taskSuccess task result =>
      simp only [GraphEvent.successes, List.mem_singleton] at member
      subst occurrence
      obtain ⟨owners, producer, known, _, _⟩ := matching
      exact ⟨owners, producer, _, known, rfl⟩
  | streamItems stream items =>
      simp only [GraphEvent.successes] at member
      obtain ⟨item, inItems, same⟩ := List.mem_map.mp member
      subst occurrence
      obtain ⟨owners, producer, known, _⟩ := matching item inItems
      exact ⟨owners, producer, _, known, rfl⟩
  | taskFailure task errors =>
      simp [GraphEvent.successes] at member
  | streamSuccess stream =>
      simp [GraphEvent.successes] at member
  | streamFailure stream errors =>
      simp [GraphEvent.successes] at member

/-- Every success in a valid input prefix is a genuine successful Work task. Witness:
induction over the host events, using their exact-outcome matches.
-/
theorem ValidGraphEvents.successes_succeed {work events}
    (valid : ValidGraphEvents work events)
    {occurrence} (member : occurrence ∈ events.flatMap GraphEvent.successes)
    : TaskSucceeds work occurrence := by
  induction valid with
  | nil => simp at member
  | @append before event _ matching fresh ready ih =>
      simp only [List.flatMap_append, List.flatMap_singleton, List.mem_append] at member
      rcases member with earlier | latest
      · exact ih earlier
      · exact GraphEvent.MatchesWork.successes_succeed matching latest

/-- A successful task's declared contributors are genuine group nodes in the
spec Work. Witness: exact group-list matching and the task's located group.
-/
theorem GraphEvent.MatchesWork.success_contributorsLocated
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (group : Execution.DeliveryNode)
    (member : group ∈ result.value.deliveryGroups)
    : ∃ dependencies producer, NodeAt work group .group dependencies producer := by
  obtain ⟨owners, producer, known, exactGroups, _⟩ := matching
  cases occurrence with
  | item address index =>
      simp only [taskGroups?] at exactGroups
      cases exactGroups
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing,
        located, _, _⟩ := known
      have mapped : groups.map Execution.DeferredFragment.node
          = result.value.deliveryGroups := by
        change locateWork work address = some
          ⟨.executionGroup groups path outcome children, producer, enclosing⟩
          at located
        simpa [taskGroups?, located] using exactGroups
      rw [← mapped] at member
      obtain ⟨fragment, inGroups, same⟩ := List.mem_map.mp member
      refine ⟨fragment.ancestors.map Execution.DeliveryNode.key,
        producer, ?_⟩
      exact ⟨address, groups, path, outcome, children, enclosing,
        fragment, located, inGroups, same.symm, rfl⟩

/-- A matched successful task reports distinct contributor keys. Witness:
exact group-list matching transports the generated task's structural owner
uniqueness into the host's execution-group value.
-/
theorem GraphEvent.MatchesWork.success_contributorsNodup
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (generated : ExecutedWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : (result.value.deliveryGroups.map Execution.DeliveryNode.key).Nodup := by
  obtain ⟨owners, producer, known, exactGroups, _⟩ := matching
  cases occurrence with
  | item address index =>
      simp only [taskGroups?] at exactGroups
      cases exactGroups
  | executionGroup address =>
      have unique := generated.taskOwners_nodup known
      obtain ⟨groups, path, outcome, children, enclosing,
        located, ownerEq, _⟩ := known
      have mapped : groups.map Execution.DeferredFragment.node
          = result.value.deliveryGroups := by
        change locateWork work address = some
          ⟨.executionGroup groups path outcome children, producer, enclosing⟩
          at located
        simpa [taskGroups?, located] using exactGroups
      rw [← mapped]
      rw [ownerEq] at unique
      simpa only [List.map_map, Function.comp_def] using unique

/-- Every task lowered from immediate work is a structural execution-group
task. Its producer is inherited from the located subwork, so it cannot be
observed before the parent settlement that releases it.
-/
theorem workFromSpec_tasks_taskAt
    {root current : Execution.Work} {address : Address}
    {producer : Option Occurrence} {enclosing : Keys}
    (located : Located root address current producer enclosing)
    {task : Task} (member : task ∈ (Work.fromExecution current address).tasks)
    : ∃ taskAddress payload,
        task.occurrence = .executionGroup taskAddress
        ∧ TaskAt root task.occurrence
            (task.groups.map Execution.DeliveryNode.key) producer payload := by
  cases current with
  | empty => simp [Work.fromExecution] at member
  | combine left right =>
      simp only [Work.fromExecution, Work.combine, List.mem_append] at member
      rcases member with inLeft | inRight
      · exact workFromSpec_tasks_taskAt located.left inLeft
      · exact workFromSpec_tasks_taskAt located.right inRight
  | executionGroup groups path result children =>
      simp only [Work.fromExecution, List.mem_singleton] at member
      subst task
      refine ⟨address, .object path result, rfl, ?_⟩
      simpa only [List.map_map, Function.comp_def] using TaskAt.executionGroup located
  | stream node items => simp [Work.fromExecution] at member
termination_by sizeOf current
decreasing_by
  all_goals simp_wf
  all_goals subst current
  all_goals simp [sizeOf, Execution.Work._sizeOf_1]
  all_goals omega

/-- Lowering preserves the complete contributor descriptors, not just their
keys. The exact list matters when comparing queued tasks with host values.
-/
theorem workFromSpec_tasks_groupsExact
    {root current : Execution.Work} {address : Address}
    {producer : Option Occurrence} {enclosing : Keys}
    (located : Located root address current producer enclosing)
    {task : Task} (member : task ∈ (Work.fromExecution current address).tasks)
    : taskGroups? root task.occurrence = some task.groups := by
  cases current with
  | empty => simp [Work.fromExecution] at member
  | combine left right =>
      simp only [Work.fromExecution, Work.combine, List.mem_append] at member
      rcases member with inLeft | inRight
      · exact workFromSpec_tasks_groupsExact located.left inLeft
      · exact workFromSpec_tasks_groupsExact located.right inRight
  | executionGroup groups path result children =>
      simp only [Work.fromExecution, List.mem_singleton] at member
      subst task
      change locateWork root address = some
        ⟨.executionGroup groups path result children, producer, enclosing⟩ at located
      simp [taskGroups?, located]
  | stream node items => simp [Work.fromExecution] at member
termination_by sizeOf current
decreasing_by
  all_goals simp_wf
  all_goals subst current
  all_goals simp [sizeOf, Execution.Work._sizeOf_1]
  all_goals omega

/-- Every task immediately lowered from a located subtree of generated Work
has distinct contributor keys, regardless of the subtree's producer.
-/
private theorem workFromSpec_tasks_contributorsNodup
    {root current : Execution.Work} {address : Address}
    {producer : Option Occurrence} {enclosing : Keys}
    (generated : ExecutedWork root)
    (located : Located root address current producer enclosing)
    {task : Task} (member : task ∈ (Work.fromExecution current address).tasks)
    : (task.groups.map Execution.DeliveryNode.key).Nodup := by
  obtain ⟨taskAddress, payload, _, known⟩ :=
    workFromSpec_tasks_taskAt located member
  exact generated.taskOwners_nodup known

/-- Every task released by a successful execution group names that success
as its structural producer, independent of queue state or host timing.
-/
theorem GraphEvent.MatchesWork.childTask_producer
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {task : Task} (member : task ∈ result.work.tasks)
    : ∃ taskAddress payload,
        task.occurrence = .executionGroup taskAddress
        ∧ TaskAt work task.occurrence
            (task.groups.map Execution.DeliveryNode.key)
            (some occurrence) payload := by
  obtain ⟨owners, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item address index =>
      simp only [taskChildWork?] at childrenWork
      cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing,
        located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩
        at located
      have childLowering : result.work =
          Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [childLowering] at member
      have childLocated : Located work (address ++ [0]) children
          (some (.executionGroup address))
          (groups.map (fun group => group.node.key)) :=
        WorkQueueSemantics.Located.executionGroup located
      exact workFromSpec_tasks_taskAt childLocated member

/-- A matched successful task may release only groups whose primary parent
agrees with the generated work's global ancestor assignment. -/
theorem GraphEvent.MatchesWork.taskChildGroups_parentCanonical
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    {parents : Nat → Keys}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {group : Group} (member : group ∈ result.work.groups)
    : group.parent = (parents group.node.key).head? := by
  obtain ⟨owners, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item address index =>
      simp only [taskChildWork?] at childrenWork
      cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing,
        located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩
        at located
      have childLowering : result.work =
          Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [childLowering] at member
      have childLocated : Located work (address ++ [0]) children
          (some (.executionGroup address))
          (groups.map (fun group => group.node.key)) :=
        WorkQueueSemantics.Located.executionGroup located
      exact workFromSpec_groups_parentCanonical childLocated canonical member

/-- Child tasks released by a successful group retain the spec's exact
contributor-node list in the queue lowering.
-/
theorem GraphEvent.MatchesWork.childTask_groupsExact
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {task : Task} (member : task ∈ result.work.tasks)
    : taskGroups? work task.occurrence = some task.groups := by
  obtain ⟨owners, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item address index =>
      simp only [taskChildWork?] at childrenWork
      cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing,
        located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩
        at located
      have childLowering : result.work =
          Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [childLowering] at member
      have childLocated : Located work (address ++ [0]) children
          (some (.executionGroup address))
          (groups.map (fun group => group.node.key)) :=
        WorkQueueSemantics.Located.executionGroup located
      exact workFromSpec_tasks_groupsExact childLocated member

/-- A batch's item-result child work has the corresponding item settlement as
its structural producer. Witness: the host's exact child-work match and the
stream entry's location in spec Work.
-/
theorem GraphEvent.MatchesWork.streamItem_childTask_producer
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items)
    {task : Task} (taskMember : task ∈ item.work.tasks)
    : ∃ taskAddress payload,
        task.occurrence = .executionGroup taskAddress
        ∧ TaskAt work task.occurrence
            (task.groups.map Execution.DeliveryNode.key)
            (some item.occurrence) payload := by
  cases item with
  | mk itemOccurrence itemValue itemWork =>
      obtain ⟨owners, producer, known, childrenWork⟩ := matching _ itemMember
      cases itemOccurrence with
      | executionGroup address =>
          simp only [streamItemWork?] at childrenWork
          cases childrenWork
      | item address index =>
          obtain ⟨node, entries, enclosing, result, children, located, entry,
            _, _⟩ := known
          change locateWork work address = some
            ⟨.stream node entries, producer, enclosing⟩ at located
          have childLowering : itemWork =
              Work.fromExecution children (address ++ [index]) := by
            simpa [streamItemWork?, located, entry] using childrenWork.symm
          rw [childLowering] at taskMember
          have childLocated : Located work (address ++ [index]) children
              (some (.item address index)) [] :=
            WorkQueueSemantics.Located.item located entry
          exact workFromSpec_tasks_taskAt childLocated taskMember

/-- Stream-item child tasks likewise retain their exact contributor nodes. -/
theorem GraphEvent.MatchesWork.streamItem_childTask_groupsExact
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items)
    {task : Task} (taskMember : task ∈ item.work.tasks)
    : taskGroups? work task.occurrence = some task.groups := by
  cases item with
  | mk itemOccurrence itemValue itemWork =>
      obtain ⟨owners, producer, known, childrenWork⟩ := matching _ itemMember
      cases itemOccurrence with
      | executionGroup address =>
          simp only [streamItemWork?] at childrenWork
          cases childrenWork
      | item address index =>
          obtain ⟨node, entries, enclosing, result, children, located, entry,
            _, _⟩ := known
          change locateWork work address = some
            ⟨.stream node entries, producer, enclosing⟩ at located
          have childLowering : itemWork =
              Work.fromExecution children (address ++ [index]) := by
            simpa [streamItemWork?, located, entry] using childrenWork.symm
          rw [childLowering] at taskMember
          have childLocated : Located work (address ++ [index]) children
              (some (.item address index)) [] :=
            WorkQueueSemantics.Located.item located entry
          exact workFromSpec_tasks_groupsExact childLocated taskMember

/-- A matched stream-item settlement may release only groups with the
generated work's globally assigned primary parent. -/
theorem GraphEvent.MatchesWork.streamItem_childGroups_parentCanonical
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    {parents : Nat → Keys}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    {item : StreamItem} (itemMember : item ∈ items)
    {group : Group} (groupMember : group ∈ item.work.groups)
    : group.parent = (parents group.node.key).head? := by
  cases item with
  | mk itemOccurrence itemValue itemWork =>
      obtain ⟨owners, producer, known, childrenWork⟩ := matching _ itemMember
      cases itemOccurrence with
      | executionGroup address =>
          simp only [streamItemWork?] at childrenWork
          cases childrenWork
      | item address index =>
          obtain ⟨node, entries, enclosing, result, children, located, entry,
            _, _⟩ := known
          change locateWork work address = some
            ⟨.stream node entries, producer, enclosing⟩ at located
          have childLowering : itemWork =
              Work.fromExecution children (address ++ [index]) := by
            simpa [streamItemWork?, located, entry] using childrenWork.symm
          rw [childLowering] at groupMember
          have childLocated : Located work (address ++ [index]) children
              (some (.item address index)) [] :=
            WorkQueueSemantics.Located.item located entry
          exact workFromSpec_groups_parentCanonical childLocated canonical groupMember

/-- Successful task settlement releases only child tasks with distinct
contributor keys. Witness: exact child-work matching and generated structure.
-/
private theorem GraphEvent.MatchesWork.childTasksContributorsNodup
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (generated : ExecutedWork work)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {task : Task} (member : task ∈ result.work.tasks)
    : (task.groups.map Execution.DeliveryNode.key).Nodup := by
  obtain ⟨taskAddress, payload, _, known⟩ := matching.childTask_producer member
  exact generated.taskOwners_nodup known

/-- Stream-item publication likewise releases only child tasks with distinct
contributor keys, independently of item batching and observation order.
-/
private theorem GraphEvent.MatchesWork.streamItem_childTasksContributorsNodup
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items)
    {task : Task} (taskMember : task ∈ item.work.tasks)
    : (task.groups.map Execution.DeliveryNode.key).Nodup := by
  obtain ⟨taskAddress, payload, _, known⟩ :=
    matching.streamItem_childTask_producer itemMember taskMember
  exact generated.taskOwners_nodup known

/-- A settled execution-group task with a structural producer could only have
entered a valid event prefix after that producer succeeded. Witness: the
event's readiness premise and the uniqueness of structural task metadata.
-/
theorem ValidGraphEvents.groupSettlement_producerBefore
    {work : Execution.Work} {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    {address : Address} {owners : Keys} {producer : Occurrence} {payload : Payload}
    (known : TaskAt work (.executionGroup address) owners (some producer) payload)
    (settled
      : (.executionGroup address) ∈ events.flatMap (fun event => event.identities.1))
    : producer ∈ events.flatMap GraphEvent.successes := by
  induction valid with
  | nil => simp at settled
  | @append before event _ matching fresh ready ih =>
      simp only [List.flatMap_append, List.flatMap_singleton, List.mem_append] at settled ⊢
      rcases settled with earlier | latest
      · exact Or.inl (ih earlier)
      · left
        cases event with
        | taskSuccess occurrence result =>
            simp only [GraphEvent.identities, List.mem_singleton] at latest
            subst occurrence
            obtain ⟨otherOwners, otherProducer, otherPayload, otherKnown, readyBefore⟩ :=
              ready
            have same := TaskAt.unique known otherKnown
            exact readyBefore producer same.2.1.symm
        | taskFailure occurrence errors =>
            simp only [GraphEvent.identities, List.mem_singleton] at latest
            subst occurrence
            obtain ⟨otherOwners, otherProducer, otherPayload, otherKnown, readyBefore⟩ :=
              ready
            have same := TaskAt.unique known otherKnown
            exact readyBefore producer same.2.1.symm
        | streamItems stream items =>
            simp only [GraphEvent.identities] at latest
            obtain ⟨item, itemMember, same⟩ := List.mem_map.mp latest
            obtain ⟨otherOwners, otherProducer, otherKnown, _⟩ := matching item itemMember
            rw [same] at otherKnown
            have payloadSame := (TaskAt.unique known otherKnown).2.2
            rcases known with ⟨groups, path, result, children, enclosing,
              located, _, payloadEqual⟩
            simp [payloadEqual] at payloadSame
        | streamSuccess stream => simp [GraphEvent.identities] at latest
        | streamFailure stream errors => simp [GraphEvent.identities] at latest

/-- A success occurrence is necessarily among that event's settled identities.
Witness: inspect the two event constructors with successful tasks.
-/
private theorem GraphEvent.success_mem_identities {event : GraphEvent}
    {occurrence : Occurrence} (success : occurrence ∈ event.successes)
    : occurrence ∈ event.identities.1 := by
  cases event with
  | taskSuccess _ _ | streamItems _ _ => exact success
  | taskFailure _ _ | streamSuccess _ | streamFailure _ _ =>
      simp [GraphEvent.successes] at success

/-- Successful producer occurrences in an event prefix have already been
settled there. Witness: choose their event and apply the one-event fact.
-/
theorem GraphEvent.successes_mem_settled {events : List GraphEvent}
    {occurrence : Occurrence}
    (success : occurrence ∈ events.flatMap GraphEvent.successes)
    : occurrence ∈ events.flatMap (fun event => event.identities.1) := by
  obtain ⟨event, member, success⟩ := List.mem_flatMap.mp success
  exact List.mem_flatMap.mpr ⟨event, member, GraphEvent.success_mem_identities success⟩

/-- A successful group may only register new child tasks. Witness: any earlier
settlement of a child would require its producer to have succeeded earlier,
contradicting the current event's fresh identity.
-/
theorem GraphEvent.MatchesWork.childTasksFresh
    {work : Execution.Work} {before : List GraphEvent}
    {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (valid : ValidGraphEvents work before)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    {task : Task} (member : task ∈ result.work.tasks)
    : task.occurrence ∉ before.flatMap (fun event => event.identities.1) := by
  obtain ⟨address, payload, taskAddress, known⟩ := matching.childTask_producer member
  intro settled
  have producerBefore : occurrence ∈ before.flatMap GraphEvent.successes :=
    valid.groupSettlement_producerBefore
      (by simpa [taskAddress] using known)
      (by simpa [taskAddress] using settled)
  have producerSettled := GraphEvent.successes_mem_settled producerBefore
  exact (fresh.2.2.1 occurrence (by simp [GraphEvent.identities])) producerSettled

/-- The children of a published stream item have not settled in any earlier
event. Witness: the item is a fresh producer identity in this very batch.
-/
theorem GraphEvent.MatchesWork.streamItem_childTasksFresh
    {work : Execution.Work} {before : List GraphEvent}
    {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (valid : ValidGraphEvents work before)
    (fresh : (GraphEvent.streamItems stream items).Fresh before)
    {item : StreamItem} (itemMember : item ∈ items)
    {task : Task} (taskMember : task ∈ item.work.tasks)
    : task.occurrence ∉ before.flatMap (fun event => event.identities.1) := by
  obtain ⟨address, payload, taskAddress, known⟩ :=
    matching.streamItem_childTask_producer itemMember taskMember
  intro settled
  have producerBefore : item.occurrence ∈ before.flatMap GraphEvent.successes :=
    valid.groupSettlement_producerBefore
      (by simpa [taskAddress] using known)
      (by simpa [taskAddress] using settled)
  have producerSettled := GraphEvent.successes_mem_settled producerBefore
  have current : item.occurrence ∈
      (GraphEvent.streamItems stream items).identities.1 := by
    exact List.mem_map.mpr ⟨item, itemMember, rfl⟩
  exact (fresh.2.2.1 item.occurrence current) producerSettled

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
