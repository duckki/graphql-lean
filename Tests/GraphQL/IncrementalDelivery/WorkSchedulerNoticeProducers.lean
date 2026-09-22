import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeProducers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyClosureAccounting
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Shared group descriptors can be ready while another structural producer is buffered. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerNoticeProducers
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def first : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def second : DeliveryNode := ⟨1, [], some (.string "R")⟩
private def parentTask : Occurrence := .executionGroup [1, 0]
private def childTask : Occurrence := .executionGroup [1, 0, 0, 0, 1, 0]

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [⟨first, []⟩] [.field "user"]
          (.ok ([("name", .scalar "name1")], 0)) (.combine .empty .empty))
        (.combine
          (.executionGroup [⟨second, []⟩] [.field "user"]
            (.ok ([("age", .scalar "1")], 0)) (.combine .empty .empty))
          .empty)))
    .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨first, []⟩, ⟨second, []⟩] []
        (.ok ([("user", .object [])], 0)) children)
      .empty)

private def result : TaskResult :=
  {
    value :=
      {
        path := [],
        data := [("user", .object [])],
        errors := 0,
        deliveryGroups := [first, second]
      },
    work := Work.fromExecution children [1, 0, 0]
  }

private def received : List GraphEvent := [.taskSuccess parentTask result]

private theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "user" [field "name"]] (some "P"),
      defer [field "user" [field "age"]] (some "R")], ?_⟩
  cbv

private theorem child_known
    : TaskAt work childTask [first.key] (some parentTask)
        (.object [.field "user"] (.ok ([("name", .scalar "name1")], 0))) :=
  .executionGroup (groups := [⟨first, []⟩]) (children := .combine .empty .empty)
    (owners := [first.key, second.key]) (by cbv)

private theorem valid : ValidGraphEvents work received := by
  have known : TaskAt work parentTask [first.key, second.key] none
      (.object [] (.ok ([("user", .object [])], 0))) :=
    .executionGroup (groups := [⟨first, []⟩, ⟨second, []⟩])
      (children := children) (owners := []) (by cbv)
  exact .append .nil ⟨_, _, known, by cbv, by cbv⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, known, by intro source impossible; cases impossible⟩

/-- A real shared object settles, but its value waits for its newly registered children.
Witness: the actual source-start check and queue output; there is no parent publication.
-/
theorem producer_reuses_pending_groups
    : inputsStarted work [received] = true
      ∧ ((State.initialize (Work.fromExecution work)).rawEventReplay received).2
        = [] := by exact ⟨by cbv, by cbv⟩

/-- Readiness selects P's root descriptor rather than its buffered child descriptor.
Witness: apply the rank-descending theorem to the real child task. The empty output
rules out every published producer, so the resulting descriptor must be root-produced.
This is descriptor readiness, not a second announcement of the already-open group P.
-/
theorem buffered_reuse_selects_rootDescriptor
    : ¬Published (fun _ => parentTask) [] parentTask
      ∧ ∃ birth,
          NodeAt work first .group [] birth
          ∧ (∀ source, birth = some source → Published (fun _ => parentTask) [] source)
          ∧ birth = none := by
  have descriptor : NodeAt work first .group [] (some parentTask) :=
    .group (address := [1, 0, 0, 0, 1, 0]) (groups := [⟨first, []⟩])
      (path := [.field "user"]) (result := .ok ([("name", .scalar "name1")], 0))
      (children := .combine .empty .empty) (owners := [first.key, second.key])
      (by cbv) List.mem_cons_self
  obtain ⟨birth, known, ready⟩ := generated.groupNotice_readyDescriptor
    (initial := [first.key, second.key]) (matching := fun _ => parentTask)
    (events := []) (failures := []) valid
    (by intro cut occurrence member; cases member)
    (by simp [TaskCancelled])
    (by simp [received, GraphEvent.successes, parentTask])
    (by simp) (by simp) child_known List.mem_cons_self descriptor
    (by intro source same; cases same; exact List.mem_cons_self)
  refine ⟨by simp [Published], birth, known, ready, ?_⟩
  cases birth with
  | none => rfl
  | some source => simpa [Published] using ready source rfl

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerNoticeProducers
