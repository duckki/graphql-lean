import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProducerOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationProducerOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! A shared group buffers its producer and child until a third task settles. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducerOrder
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def owner : DeliveryNode := { ref := 0, path := [] }

private def childWork : Execution.Work :=
  .executionGroup [⟨owner, []⟩] [.field "obj"] (.ok ([("x", .scalar "X")], 0)) .empty

private def work : Execution.Work :=
  .combine
    (.executionGroup [⟨owner, []⟩] [] (.ok ([("obj", .object [])], 0)) childWork)
    (.executionGroup [⟨owner, []⟩] [] (.ok ([("blocker", .scalar "B")], 0)) .empty)

private def parentTask : Occurrence := .executionGroup [0]
private def blockerTask : Occurrence := .executionGroup [1]
private def childTask : Occurrence := .executionGroup [0, 0]

private def parentResult : TaskResult :=
  {
    value :=
      {
        path := [], data := [("obj", .object [])], errors := 0, deliveryGroups := [owner]
      },
    work := Work.fromExecution childWork [0, 0]
  }

private def childResult : TaskResult :=
  {
    value :=
      {
        path := [.field "obj"],
        data := [("x", .scalar "X")],
        errors := 0,
        deliveryGroups := [owner]
      }
  }

private def blockerResult : TaskResult :=
  {
    value :=
      {
        path := [],
        data := [("blocker", .scalar "B")],
        errors := 0,
        deliveryGroups := [owner]
      }
  }

private def before : List GraphEvent :=
  [.taskSuccess parentTask parentResult, .taskSuccess childTask childResult]

private def initial : State := State.initialize (Work.fromExecution work)
private def waiting : State := initial.replayGraphEvents before

private theorem child_known
    : TaskAt work childTask [owner.ref] (some parentTask)
        (.object childResult.value.path (.ok (childResult.value.data, 0))) := by
  refine ⟨[⟨owner, []⟩], [.field "obj"], _, .empty, [owner.ref], ?_, rfl, rfl⟩
  cbv

private theorem valid : ValidGraphEvents work before := by
  have parentKnown : TaskAt work parentTask [owner.ref] none
      (.object [] (.ok (parentResult.value.data, 0))) := by
    refine ⟨[⟨owner, []⟩], [], _, childWork, [], ?_, rfl, rfl⟩
    cbv
  have first : ValidGraphEvents work [.taskSuccess parentTask parentResult] :=
    .append .nil ⟨_, _, parentKnown, by cbv, by cbv⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩
  refine .append first ⟨_, _, child_known, by cbv, by cbv⟩ ?_ ?_
  · simp [GraphEvent.Fresh, GraphEvent.identities, parentTask, childTask]
  · refine ⟨_, _, _, child_known, ?_⟩
    intro source same
    cases same
    simp [GraphEvent.successes]

private def group : GroupNode :=
  { group := ⟨owner, none⟩, tasks := [parentTask, blockerTask, childTask], pending := 0 }

private def prepared : State :=
  (waiting.putTaskNode
    ⟨⟨blockerTask, [owner]⟩, some blockerResult.value, []⟩).putGroupNode
    group

/-- The child settles while its parent remains buffered; the blocker releases them together.
Witness: reduction of the three actual handlers. Output order follows registration rather
than settlement order, putting the blocker before the already-settled child.
-/
theorem shared_release_output
    : (initial.rawEventReplay before).2 = []
      ∧ (waiting.taskSuccess blockerTask blockerResult).2
        = [
          .groupValues owner [parentResult.value, blockerResult.value, childResult.value],
          .groupSuccess owner [] []
        ] := by
  constructor <;> cbv

/-- The actual shared flush admits one fresh labelled ledger with producer-before-child order.
Witness: source-valid registration order and membership preservation supply the generic
flush theorem. Complete selection places both stored occurrences in that same ledger;
the generic strict-prefix lemma then orders them, without inspecting payload equality.
This fixture tests queue ordering only; it does not assert generated-work conformance.
-/
theorem shared_release_producer_before
    : ∃ added : List ObjectPublication,
        added.map Prod.snd = [parentResult.value, blockerResult.value, childResult.value]
        ∧ (parentTask, parentResult.value) ∈ added
        ∧ (childTask, childResult.value) ∈ added
        ∧ ∀ index,
            added[index]? = some (childTask, childResult.value)
            → ∃ value, (parentTask, value) ∈ added.take index := by
  have inventory : prepared.PublicationInventory (fun _ _ => True) [] := by
    refine ⟨by simp, by simp, ?_⟩
    intro node member value stored
    exact ⟨trivial, by simp⟩
  have memberships : prepared.GroupMembershipOrder := by
    have prior := (createWorkQueue_groupMembershipOrder (Work.fromExecution work)).replayGraphEvents
      before
    apply State.GroupMembershipOrder.putGroupNode (queue := waiting.putTaskNode _)
      prior group
    change [parentTask, blockerTask, childTask].Sublist [parentTask, blockerTask, childTask]
    exact .refl _
  have order : ProducerOrder work (prepared.tasks.map Task.occurrence) :=
    (createWorkQueue_replayGraphEvents_producerOrder valid).2
  obtain ⟨added, values, _, ordered, covered⟩ :=
    inventory.finishGroupSuccess_producerOrder memberships order group List.mem_cons_self
  have parent := covered parentTask (by simp [group])
    ⟨⟨parentTask, [owner]⟩, some parentResult.value, []⟩ parentResult.value (by cbv) rfl
  have child := covered childTask (by simp [group])
    ⟨⟨childTask, [owner]⟩, some childResult.value, []⟩ childResult.value (by cbv) rfl
  refine ⟨added, ?_, parent, child, ?_⟩
  · exact values
  · intro index selected
    exact ordered.publication_before selected ⟨_, _, child_known⟩
      (List.mem_map.mpr ⟨_, parent, rfl⟩)

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducerOrder
