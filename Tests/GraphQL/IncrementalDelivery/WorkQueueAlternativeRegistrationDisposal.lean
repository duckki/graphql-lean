import Tests.GraphQL.IncrementalDelivery.Fixtures.RejectedTaskCleanup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskRegistration

open GraphQL.IncrementalDelivery.Tests

/-! Generated rejection disposal and local registration guards. -/

namespace AlternativeRegistrationDisposalChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedAdoptedTaskRegistrationProgress :=
  GeneratedAdoptedTaskRegistrationProgress_holds

example : ReferenceWorkQueue.ExecutedWork SharedOwnerFailure.work :=
  SharedOwnerFailure.executed

example : RejectedTaskCleanup.schedule.ValidFor SharedOwnerFailure.work :=
  RejectedTaskCleanup.sourceValid

example
    : Execution.WorkQueue.Conforms
        (createWorkQueueForSchedule SharedOwnerFailure.work RejectedTaskCleanup.schedule)
        SharedOwnerFailure.work :=
  RejectedTaskCleanup.conforms

example : RejectedTaskCleanup.schedule.admissible RejectedTaskCleanup.inputs :=
  List.prefix_refl _

example
    : CompleteAdoptionInventories RejectedTaskCleanup.acquired
        RejectedTaskCleanup.inventories
        (graphEffects RejectedTaskCleanup.before.queue
          SharedOwnerFailure.parentSuccess) :=
  RejectedTaskCleanup.complete

example
    : ResourcesRepresented RejectedTaskCleanup.before.queue
        RejectedTaskCleanup.acquired :=
  RejectedTaskCleanup.beforeRepresented

example
    : RejectedTaskCleanup.observed.1 (.task RejectedTaskCleanup.child)
      = .cleanupRequested .queue :=
  RejectedTaskCleanup.requested

example
    : RejectedTaskCleanup.reduced.effects
      = [.adopt RejectedTaskCleanup.producer, .abortTask RejectedTaskCleanup.child] :=
  RejectedTaskCleanup.effects

example
    : RejectedTaskCleanup.reduced.state.queue.taskNode? RejectedTaskCleanup.child
      = none := by
  dsimp only [RejectedTaskCleanup.reduced, RejectedTaskCleanup.before]
  rw [SharedOwnerFailure.work_shape]
  cbv

example
    : ¬RecordTargetRepresented RejectedTaskCleanup.reduced.state.queue
        (.task RejectedTaskCleanup.child) :=
  RejectedTaskCleanup.unrepresented

example
    : ResourcesRepresented RejectedTaskCleanup.reduced.state.queue
        RejectedTaskCleanup.observed.1 :=
  RejectedTaskCleanup.represented

example : StopCoverage RejectedTaskCleanup.reduced.state RejectedTaskCleanup.observed.1 :=
  RejectedTaskCleanup.covered

example
    : (RejectedTaskCleanup.observed.1.observeStop RejectedTaskCleanup.reduced.state).1
        (.task RejectedTaskCleanup.child)
      = .cleanupRequested .queue :=
  RejectedTaskCleanup.stoppedRequested

example
    : (ResourceState.empty.observeDispatch RejectedTaskCleanup.inventories
        RejectedTaskCleanup.before SharedOwnerFailure.parentSuccess).1
        (.task RejectedTaskCleanup.child)
      = .unacquired :=
  ResourceState.observeDispatch_unacquired _ _ _ _ _ rfl

-----------------------------------------------------------------------------------------
-- Local raw-state guards: use registration-time ownership, not final-state absence
-----------------------------------------------------------------------------------------

private def node (key : Nat) : Execution.DeliveryNode := { ref := key, path := [] }
private def parent : WorkQueueSemantics.Occurrence := .executionGroup [0]
private def child : WorkQueueSemantics.Occurrence := .executionGroup [1]

private def task (owners : List Nat) : ReferenceWorkQueue.Task :=
  { occurrence := child, groups := owners.map node }

private def queue : ReferenceWorkQueue.State :=
  {
    rootGroups := [1]
    rootStreams := [4]
    registeredGroups := [0, 1, 3]
    groupNodes :=
      [
        { group := { node := node 1 }, tasks := [parent], pending := 1 },
        { group := { node := node 3 }, tasks := [.executionGroup [99]], pending := 1 }
      ]
    taskNodes :=
      [
        { task := { occurrence := parent, groups := [node 1] } },
        {
          task := { occurrence := .executionGroup [99], groups := [node 3] },
          rejection := some 1
        }
      ]
  }

private def success (work : ReferenceWorkQueue.Work) : GraphEvent :=
  .taskSuccess parent { value := { path := [], data := [] }, work }

private def item (work : ReferenceWorkQueue.Work) : ReferenceWorkQueue.StreamItem :=
  { occurrence := .item [] 0, value := { item := .scalar "item" }, work }

-- Inspect the actual handler trace, including handoff and acknowledgement placement.
private def handlerEffects (before : ReferenceWorkQueue.State) (event : GraphEvent) :=
  (({ queue := before } : State).handleGraphEvent event).2.2

-- Removed owner, including duplicate references, contributes one abort.
example
    : handlerEffects queue (success { tasks := [task [0]] })
      = [.adopt parent, .abortTask child] := by cbv

example
    : handlerEffects queue (success { tasks := [task [0], task [0]] })
      = [.adopt parent, .abortTask child] := by cbv

example
    : handlerEffects queue (success { tasks := [task []] })
      = [.adopt parent, .abortTask child] := by cbv

-- A shared surviving owner or a retained latent failed owner prevents rejection.
example
    : handlerEffects queue (success { tasks := [task [0, 1]] }) = [.adopt parent] := by
  cbv

example : handlerEffects queue (success { tasks := [task [3]] }) = [.adopt parent] := by
  cbv

-- Newly installed owners count too; checking only the pre-state would incorrectly abort.
example
    : handlerEffects queue
        (success { groups := [{ node := node 2 }], tasks := [task [2]] })
      = [.adopt parent] := by cbv

-- Active item work uses the same rejection rule; inactive receipts adopt no work.
example
    : handlerEffects queue (.streamItems (node 4) [item { tasks := [task [0]] }])
      = [.adopt (.item [] 0), .abortTask child, .acknowledge 4] := by cbv

-- Disposal is interleaved after the first handoff and deduplicated across the receipt.
example
    : handlerEffects queue
        (.streamItems (node 4)
          [
            item { tasks := [task [0]] },
            { item { tasks := [task [0]] } with occurrence := .item [] 1 }
          ])
      = [.adopt (.item [] 0), .abortTask child, .adopt (.item [] 1), .acknowledge 4] := by
  cbv

example
    : handlerEffects queue (.streamItems (node 5) [item { tasks := [task [0]] }])
      = [.acknowledge 5] := by cbv

example
    : handlerEffects queue (.streamItems (node 4) [item { tasks := [task [0, 1]] }])
      = [.adopt (.item [] 0), .acknowledge 4] := by cbv

example
    : handlerEffects queue
        (.streamItems (node 4)
          [item { groups := [{ node := node 2 }], tasks := [task [2]] }])
      = [.adopt (.item [] 0), .acknowledge 4] := by cbv

-- Unaccepted success and nonregistration inputs do not take producer-owned work.
example
    : handlerEffects queue
        (.taskSuccess child
          { value := { path := [], data := [] }, work := { tasks := [task [0]] } })
      = [] := by cbv

example
    : handlerEffects
        {
          queue with
            taskNodes :=
              (queue.taskNodes.filter
                (fun taskNode => taskNode.task.occurrence != parent))
        }
        (success { tasks := [task [0]] })
      = [] := by cbv

example : handlerEffects queue (.taskFailure parent 1) = [] := by cbv
example : handlerEffects queue (.streamSuccess (node 4)) = [] := by cbv
example : handlerEffects queue (.streamFailure (node 4) 1) = [.cancelSource 4] := by cbv

-- Rejection reuses cancelTask's held-source operations without recursively evaluating Work.
example
    : handlerEffects
        {
          queue with
            taskNodes := queue.taskNodes ++ [{ task := task [0], childStreams := [7] }]
        }
        (success { tasks := [task [0]] })
      = [.adopt parent, .abortTask child, .cancelSource 7, .abortStreamQueue 7] := by cbv

example
    : ∀ before event,
        ((handlerEffects before event).filterMap HostEffect.cleanupStart?).Nodup := by
  intro before event
  cases event with
  | taskSuccess occurrence result =>
      exact State.taskSuccess_cleanupStarts_nodup _ occurrence result
  | streamItems stream items => exact State.streamItems_cleanupStarts_nodup _ stream items
  | taskFailure occurrence errors =>
      exact State.taskFailure_cleanupStarts_nodup _ occurrence errors
  | streamSuccess => exact List.nodup_nil
  | streamFailure stream errors =>
      simp only [handlerEffects, State.handleGraphEvent]
      split <;> simp [HostEffect.cleanupStart?]

#print axioms RejectedTaskCleanup.valid
#print axioms RejectedTaskCleanup.started
#print axioms RejectedTaskCleanup.sourceValid
#print axioms RejectedTaskCleanup.conforms
#print axioms RejectedTaskCleanup.childKnown
#print axioms RejectedTaskCleanup.complete
#print axioms RejectedTaskCleanup.handoff
#print axioms RejectedTaskCleanup.targets
#print axioms RejectedTaskCleanup.requested
#print axioms RejectedTaskCleanup.stoppedRequested
#print axioms RejectedTaskCleanup.represented
#print axioms RejectedTaskCleanup.covered
#print axioms State.taskSuccess_cleanupStarts_nodup
#print axioms State.streamItems_cleanupStarts_nodup
#print axioms streamRegistrationFold_ownerless_target
#print axioms registration_rejectedTask_aborted
#print axioms generatedSnapshot_unsettledLinks
#print axioms GeneratedAdoptedTaskRegistrationProgress_holds

end AlternativeRegistrationDisposalChecks
