import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedCarrierReplay

/-! A processed success is published before any later successful contributing carrier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The incoming value uses the same prepared and later replay occurrence labels
-----------------------------------------------------------------------------------------

/-- A processed success publishes before a successful contributor's later carrier.
Witness: exact storage supplies the prepared node. Permanent registration keeps a
contributor live across the first handler; prepared conservation either publishes there
or leaves a buffer covered by the later-carrier theorem. Both use the same ledger.
-/
theorem State.ReplayClosuresCovered.success_before_carrier {queue : State}
    {available : List (Occurrence × Nat)} {work occurrence result before event published}
    (covered
      : queue.ReplayClosuresCovered
          (.taskSuccess occurrence result :: before ++ [event]) published available)
    (live : queue.LiveGroupsRegistered) (registered : queue.TaskGroupsRegistered)
    (frame : queue.RegistrationFrame work)
    (matching
      : ∀ input ∈ .taskSuccess occurrence result :: before ++ [event],
          input.MatchesWork work)
    {node} (found : (queue.cacheTaskFailures available).taskNode? occurrence = some node)
    {index group groups streams}
    (carrier
      : (((queue.dispatchGraphEvent (.taskSuccess occurrence result)
            available).1.replayGraphEvents
            before available).handleGraphEvent
          event available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (contributes : group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    : (occurrence, result.value)
      ∈ published.take
          ((((queue.cacheTaskFailures available).taskSuccess occurrence result
              available).2.1.flatMap
              WorkQueueEvent.objectValues).length
            + (((queue.dispatchGraphEvent (.taskSuccess occurrence result)
                  available).1.rawEventReplay
                  before available).2.flatMap
                WorkQueueEvent.objectValues).length
            + (((((queue.dispatchGraphEvent (.taskSuccess occurrence result)
                    available).1.replayGraphEvents
                    before available).handleGraphEvent
                  event available).2.1.take
                  index).flatMap
                WorkQueueEvent.objectValues).length) := by
  have first := frame.dispatchGraphEvent
    (.taskSuccess occurrence result) (matching _ List.mem_cons_self) available
  have laterMatching : ∀ input ∈ before ++ [event], input.MatchesWork work :=
    fun input member => matching input (List.mem_cons_of_mem _ member)
  have boundary := first.1.replayGraphEvents before
    (fun input member => laterMatching input (List.mem_append_left _ member)) available
  have known := State.taskNode?_some found
  have cached := queue.cacheTaskFailures_registration live registered available
  have recorded : group.ref ∈ queue.registeredGroups := by
    simpa only [State.cacheTaskFailures_registeredGroups]
      using cached.2 node.task
        ((frame.started.cacheTaskFailures available) node known.1) group.ref contributes
  obtain ⟨owner, boundaryLive⟩ := State.handleGraphEvent_success_live_registered
    boundary.1.live boundary.1.tasks
    (laterMatching event (List.mem_append_right _ List.mem_cons_self))
    (boundary.2 (first.2 recorded)) (List.mem_of_getElem? carrier)
  obtain ⟨earlierOwner, earlierLive⟩ := State.replayGraphEvents_live_registered
    (first.2 recorded) before boundaryLive
  obtain ⟨buffered, installed, sameTask, stored⟩ := State.taskSuccess_prepared_value found result
  have survives : ∃ contributor ∈ buffered.task.groups, ∃ owner,
      ((queue.cacheTaskFailures available).taskSuccess occurrence result available).1.groupNode?
          contributor.ref = some owner := by
    obtain ⟨contributor, member, same⟩ := List.mem_map.mp contributes
    exact ⟨contributor, sameTask.symm ▸ member, earlierOwner, same ▸ earlierLive⟩
  have conserved := covered.2.2.2.1 node found
  rw [Nat.add_assoc, List.take_add]
  rcases conserved occurrence buffered result.value installed stored survives with now | retained
  · exact List.mem_append_left _ now
  · apply List.mem_append_right
    exact covered.tail.buffered_carrier first.1.live first.1.tasks
      (frame.dispatchGraphEvent (.taskSuccess occurrence result)
        (matching _ List.mem_cons_self) available).1 laterMatching
      carrier retained stored (sameTask.symm ▸ contributes)

/-- If the success handler itself closes a contributor, its new value is already emitted.
Witness: exact prepared storage and the handler's prepared coverage certificate. Taking
only the strict carrier prefix excludes any later output in the same handler.
-/
theorem State.ReplayClosuresCovered.success_at_carrier {queue : State}
    {available : List (Occurrence × Nat)} {occurrence result published rest}
    (covered
      : queue.ReplayClosuresCovered (.taskSuccess occurrence result :: rest) published
          available)
    {node} (found : (queue.cacheTaskFailures available).taskNode? occurrence = some node)
    {index group groups streams}
    (carrier
      : ((queue.cacheTaskFailures available).taskSuccess occurrence result
          available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (contributes : group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    : (occurrence, result.value)
      ∈ published.take
          ((((queue.cacheTaskFailures available).taskSuccess occurrence result
              available).2.1.take
              index).flatMap
            WorkQueueEvent.objectValues).length := by
  obtain ⟨buffered, installed, sameTask, stored⟩ := State.taskSuccess_prepared_value found result
  have coverage := covered.2.1 node found
  have delivered := coverage index group groups streams carrier occurrence buffered
    result.value installed stored (sameTask.symm ▸ contributes)
  have bounded
      : ((((queue.cacheTaskFailures available).taskSuccess occurrence result available).2.1.take
          index).flatMap
      WorkQueueEvent.objectValues).length
      ≤ (((queue.cacheTaskFailures available).taskSuccess occurrence result available).2.1.flatMap
          WorkQueueEvent.objectValues).length := by
    have split := congrArg (fun events : List WorkQueueEvent =>
      (events.flatMap WorkQueueEvent.objectValues).length)
      (List.take_append_drop index
        ((queue.cacheTaskFailures available).taskSuccess occurrence result available).2.1)
    simp only [List.flatMap_append, List.length_append] at split
    omega
  simpa only [State.dispatchGraphEvent, State.handleGraphEvent, List.take_take,
    Nat.min_eq_left bounded]
    using delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
