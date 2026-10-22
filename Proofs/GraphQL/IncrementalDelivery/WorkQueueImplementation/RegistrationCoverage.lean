import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationParentTraversal
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationFrames

/-! Derived declaration contexts discharge registry coverage through matched replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics

/-- Registration coverage follows from the derived declaration frame. -/
theorem State.taskSuccess_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (frame : queue.RegistrationFrame work)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.LiveGroupsRegistered
      ∧ (queue.taskSuccess occurrence result available).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.taskSuccess occurrence result available).1.registeredGroups := by
  let current : queue.RegistrationFrame work := { frame with live := live, tasks := tasks }
  have next := current.taskSuccess occurrence result matching available
  exact ⟨next.1.live, next.1.tasks, next.2⟩

/-- Registration coverage follows from the derived declaration frame. -/
theorem State.streamItems_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (frame : queue.RegistrationFrame work)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.LiveGroupsRegistered
      ∧ (queue.streamItems stream items available).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.streamItems stream items available).1.registeredGroups := by
  let current : queue.RegistrationFrame work := { frame with live := live, tasks := tasks }
  have next := current.streamItems matching available
  exact ⟨next.1.live, next.1.tasks, next.2⟩

/-- Registration coverage follows from the derived declaration frame. -/
theorem State.handleGraphEvent_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (frame : queue.RegistrationFrame work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.LiveGroupsRegistered
      ∧ (queue.handleGraphEvent event available).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.handleGraphEvent event available).1.registeredGroups := by
  let current : queue.RegistrationFrame work := { frame with live := live, tasks := tasks }
  have next := current.handleGraphEvent event matching available
  exact ⟨next.1.live, next.1.tasks, next.2⟩

/-- Registration coverage follows from the derived declaration frame. -/
theorem State.handleGraphEvents_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (frame : queue.RegistrationFrame work)
    : (queue.handleGraphEvents events).1.LiveGroupsRegistered
      ∧ (queue.handleGraphEvents events).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.handleGraphEvents events).1.registeredGroups := by
  let current : queue.RegistrationFrame work := { frame with live := live, tasks := tasks }
  have next := current.handleGraphEvents events matching
  exact ⟨next.1.live, next.1.tasks, next.2⟩

/-- Registration coverage follows from the derived declaration frame. -/
theorem State.runNormalized_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (batches : List (List GraphEvent))
    (matching : ∀ batch ∈ batches, ∀ event ∈ batch, event.MatchesWork work)
    (frame : queue.RegistrationFrame work)
    : (queue.runNormalized batches).1.LiveGroupsRegistered
      ∧ (queue.runNormalized batches).1.TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.runNormalized batches).1.registeredGroups := by
  let current : queue.RegistrationFrame work := { frame with live := live, tasks := tasks }
  have next := current.runNormalized batches matching
  exact ⟨next.1.live, next.1.tasks, next.2⟩

/-- Registration coverage follows from the derived declaration frame. -/
theorem State.replayGraphEvents_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (frame : queue.RegistrationFrame work)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).LiveGroupsRegistered
      ∧ (queue.replayGraphEvents events available).TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.replayGraphEvents events available).registeredGroups := by
  let current : queue.RegistrationFrame work := { frame with live := live, tasks := tasks }
  have next := current.replayGraphEvents events matching available
  exact ⟨next.1.live, next.1.tasks, next.2⟩

/-- A matching item uses its independently certified stream-child context. -/
theorem State.integrateStreamItem_registration {queue : State} {work : Execution.Work}
    (live : queue.LiveGroupsRegistered) (tasks : queue.TaskGroupsRegistered)
    {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (frame : queue.RegistrationFrame work) (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).LiveGroupsRegistered
      ∧ (queue.integrateStreamItem item available).TaskGroupsRegistered
      ∧ queue.registeredGroups.Subset
          (queue.integrateStreamItem item available).registeredGroups := by
  let current : queue.RegistrationFrame work := { frame with live := live, tasks := tasks }
  have next := current.integrateStreamItem matching member available
  exact ⟨next.1.live, next.1.tasks, next.2⟩

/-- Executed work supplies all registration contexts before matching batches are replayed. -/
theorem createWorkQueue_runNormalized_registration
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (certified : DeclarationCoverage.Certified [] work)
    : let queue := (State.initialize (Work.fromExecution work)).runNormalized batches
      queue.1.LiveGroupsRegistered
      ∧ queue.1.TaskGroupsRegistered
      ∧ (State.initialize (Work.fromExecution work)).registeredGroups.Subset
          queue.1.registeredGroups := by
  have next := (State.initialize_registrationFrame certified).runNormalized batches
    (fun _ batchMember _ eventMember => valid.eachMatches
      (List.mem_flatten.mpr ⟨_, batchMember, eventMember⟩))
  exact ⟨next.1.live, next.1.tasks, next.2⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
