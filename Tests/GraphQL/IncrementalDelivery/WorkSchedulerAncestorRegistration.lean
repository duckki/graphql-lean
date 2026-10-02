import GraphQL.IncrementalDelivery.WorkQueueImplementation

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerAncestorRegistration
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Parent-first lowering and silent release through taskless wrappers
-----------------------------------------------------------------------------------------

private def p : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def q : DeliveryNode := ⟨1, [], some (.string "Q")⟩
private def r : DeliveryNode := ⟨2, [], some (.string "R")⟩
private def s : DeliveryNode := ⟨3, [], some (.string "S")⟩
private def e : DeliveryNode := ⟨4, [.field "user"], some (.string "E")⟩
private def c : DeliveryNode := ⟨5, [.field "user"], some (.string "C")⟩
private def d : DeliveryNode := ⟨6, [.field "user"], some (.string "D")⟩

private def wrapped : Execution.Work :=
  .executionGroup [⟨c, [e, p]⟩] [.field "user"] (.ok ([], 0)) .empty

/-- The conversion maps empty execution work to empty queue collections. -/
example : Work.fromExecution .empty = ({} : ReferenceWorkQueue.Work) := rfl

/-- Combining work preserves each task's structural address below the supplied route. -/
example (route : Address)
    : (Work.fromExecution (.combine wrapped wrapped) route).tasks.map Task.occurrence
      = [.executionGroup (route ++ [0]), .executionGroup (route ++ [1])] :=
  rfl

/-- Ancestors precede their children and retain every immediate-parent link. -/
example
    : (Work.fromExecution wrapped).groups.map
        (fun group => (group.node.key, group.parent))
      = [(p.key, none), (e.key, some p.key), (c.key, some e.key)] := by cbv

/-- Ancestor-only groups are not added to the task's contributing owners. -/
example
    : (Work.fromExecution wrapped).tasks.map
        (fun task => (task.occurrence, task.groups.map DeliveryNode.key))
      = [(.executionGroup [], [c.key])] := by cbv

/-- Initialization silently prunes taskless ancestors, announcing only C. -/
example : (State.initialize (Work.fromExecution wrapped)).initialGroups = [c] := by cbv

/-- Pruning does not cancel the surviving task or retain empty ancestor records. -/
example
    : let queue := State.initialize (Work.fromExecution wrapped)
      queue.registeredGroups = [p.key, e.key, c.key]
      ∧ queue.groupNodes.map (fun node => node.group.node.key) = [c.key]
      ∧ queue.cancelledGroups = []
      ∧ queue.groupIsHealthy c.key = true := by cbv

private def nested : Execution.Work :=
  .executionGroup [⟨p, []⟩] [] (.ok ([], 0)) wrapped

private def parentSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [])
    {
      value := { path := [], data := [], errors := 0, deliveryGroups := [p] },
      work := Work.fromExecution wrapped [0]
    }

private def childSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [0])
    {
      value := { path := [.field "user"], data := [], errors := 0, deliveryGroups := [c] }
    }

/-- Repeated ancestor candidates register once; E retains C until P releases it. -/
example
    : let queue := State.initialize (Work.fromExecution nested)
      let integrated := (queue.maybeIntegrateWork (Work.fromExecution wrapped [0])).1
      integrated.registeredGroups = [p.key, e.key, c.key]
      ∧ (integrated.groupNode? p.key).map GroupNode.childGroups = some [e.key]
      ∧ (integrated.groupNode? e.key).map GroupNode.childGroups = some [c.key] := by cbv

/-- Success promotes C through E without publishing any notice or completion for E. -/
example
    : ((State.initialize (Work.fromExecution nested)).runNormalized
        [[parentSuccess], [childSuccess]]).2
      = [
        [
          .groupValues p [{ path := [], data := [], errors := 0, deliveryGroups := [p] }],
          .groupSuccess p [c] []
        ],
        [
          .groupValues c
            [{ path := [.field "user"], data := [], errors := 0, deliveryGroups := [c] }],
          .groupSuccess c [] [],
          .workQueueTermination
        ]
      ] := by cbv

/-- Normal release starts the child task despite its taskless intermediate parent. -/
example : inputsStarted nested [[parentSuccess], [childSuccess]] = true := by cbv

-----------------------------------------------------------------------------------------
-- Cancellation through the taskless parent in the exact counterexample replay
-----------------------------------------------------------------------------------------

private def pTask : Occurrence := .executionGroup [1, 0]
private def uTask : Occurrence := .executionGroup [1, 1, 0]
private def xTask : Occurrence := .executionGroup [1, 1, 0, 0, 0, 1, 0]
private def yTask : Occurrence := .executionGroup [1, 1, 0, 0, 0, 1, 1, 0]
private def qTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def rTask : Occurrence := .executionGroup [1, 1, 1, 1, 0]
private def userData : List (Name × ResponseValue) := [("user", .object [])]
private def keepData : List (Name × ResponseValue) := [("keepQ", .scalar "a")]

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [⟨c, [e, p]⟩, ⟨d, [q]⟩, ⟨r, []⟩] [.field "user"] (.error 1)
          .empty)
        (.combine
          (.executionGroup [⟨d, [q]⟩, ⟨s, []⟩] [.field "user"] (.error 1) .empty)
          .empty)))
    .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨p, []⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨p, []⟩, ⟨q, []⟩, ⟨r, []⟩, ⟨s, []⟩] []
          (.ok (userData, 0)) children)
        (.combine
          (.executionGroup [⟨q, []⟩] [] (.ok (keepData, 0)) (.combine .empty .empty))
          (.combine (.executionGroup [⟨r, []⟩] [] (.error 2) .empty) .empty))))

private def expand : GraphEvent :=
  .taskSuccess uTask
    {
      value :=
        { path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s] },
      work := Work.fromExecution children [1, 1, 0, 0]
    }

private def finish : GraphEvent :=
  .taskSuccess qTask
    {
      value := { path := [], data := keepData, errors := 0, deliveryGroups := [q] },
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def beforeX : List (List GraphEvent) :=
  [[.taskFailure pTask 1], [expand], [.taskFailure yTask 1], [.taskFailure rTask 2]]

private def inputs : List (List GraphEvent) :=
  beforeX ++ [[.taskFailure xTask 1], [finish]]

/-- Parent-first registration propagates P's cancellation through E to C. -/
example
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized beforeX).1
      queue.registeredGroups = [0, 1, 2, 3, 4, 5, 6]
      ∧ queue.cancelledGroups = [0, 4, 5, 3, 2]
      ∧ queue.groupNode? e.key = none
      ∧ queue.groupNode? c.key = none
      ∧ queue.groupIsHealthy c.key = false := by cbv

/-- The same host prefix still obeys the executable start discipline. -/
example : inputsStarted work inputs = true := by cbv

/-- X adds no error after cancellation; D reports only its earlier Y failure. -/
example
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      = [
        [.groupFailure p 1],
        [.groupFailure s 1],
        [.groupFailure r 2],
        [
          .groupValues q
            [{
              path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s]
            }],
          .groupValues q
            [{ path := [], data := keepData, errors := 0, deliveryGroups := [q] }],
          .groupSuccess q [d] [],
          .groupFailure d 1,
          .workQueueTermination
        ]
      ] := by cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerAncestorRegistration
