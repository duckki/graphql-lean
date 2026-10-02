import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementReplay
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Generated nested defer work is supported by a live, unsettled producer group. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducerSupport
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The root defer that produces an object containing a nested defer. -/
def parent : DeliveryNode :=
  { key := 0, path := [], label := some (.string "P") }

/-- The nested defer at the produced object's response path. -/
def child : DeliveryNode :=
  { key := 1, path := [.field "user"], label := some (.string "C") }

/-- The address of the object-producing root task. -/
def parentTask : Occurrence := .executionGroup [1, 0]

/-- The lowered task owned by the root defer. -/
def producer : Task := ⟨parentTask, [parent]⟩

/-- The child's immediate dependency is the producing parent defer. -/
def childGroup : Group := ⟨child, some parent.key⟩

/-- The finite deferred work returned by the parent task. -/
def children : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [⟨child, [parent]⟩] [.field "user"]
          (.ok ([("name", .scalar "name1")], 0)) (.combine .empty .empty))
        .empty))
    .empty

/-- The exact generated work for the nested-object fixture. -/
def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨parent, []⟩] [] (.ok ([("user", .object [])], 0)) children)
      .empty)

/-- The parent's matched value and nonempty lowered child work. -/
def result : TaskResult :=
  {
    value := { deliveryGroups := [parent], path := [], data := [("user", .object [])] },
    work := Work.fromExecution children [1, 0, 0]
  }

/-- The queue before the parent result arrives. -/
def queue : State := State.initialize (Work.fromExecution work)

/-- The fixture comes from a query with a defer nested inside an object-producing defer.
Witness: evaluate the actual executor, retaining its exact combine and producer paths. -/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "user" [defer [field "name"] (some "C")]] (some "P")], ?_⟩
  cbv

/-- The host result matches both the producer value and its immediate child work.
Witness: locate the generated parent task and check exact lowering. -/
theorem matching
    : (GraphEvent.taskSuccess producer.occurrence result).MatchesWork work := by
  refine ⟨[parent.key], none, ?_, ?_, ?_⟩
  · refine ⟨[⟨parent, []⟩], [], _, children, [], ?_, rfl, rfl⟩
    cbv
  · cbv
  · cbv

/-- The child's group candidate is supplied by the matched producer success.
Witness: its immediate lowering, not compilation of future work at initialization. -/
theorem child_candidate : childGroup ∈ result.work.groups := by
  have groups : result.work.groups = [⟨parent, none⟩, childGroup] := by cbv
  rw [groups]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- This is genuine descendant support, not reuse of an already-live child group.
Witness: initialization contains only P; C is supplied later by the producer. -/
theorem child_not_yet_live
    : child.key ∉ queue.groupNodes.map (fun node => node.group.node.key) := by
  have keys : queue.groupNodes.map (fun node => node.group.node.key) = [parent.key] := by cbv
  rw [keys]
  decide

/-- The generated child has a live defer ancestor with its producer still pending.
Witness: the general producer-support theorem and initial healthy ledgers; the absent
child node rules out the direct-reuse branch. No availability premise is assumed. -/
theorem child_supported_by_pending_ancestor
    : ∃ dependencies,
        NodeAt work child .group dependencies (some parentTask)
        ∧ ∃ node ∈ queue.groupNodes,
            node.group.node.key ∈ dependencies
            ∧ parentTask ∈ node.tasks
            ∧ node.pending ≠ 0 := by
  have tasks : queue.tasks = [producer] := by cbv
  have producerMember : producer ∈ queue.tasks := by
    rw [tasks]
    exact List.mem_cons_self
  obtain ⟨dependencies, known, node, nodeMember, _, _, linked, nonzero, support⟩ :=
    (createWorkQueue_healthyRegisteredTaskAccounting work).childGroup_live_support
      (createWorkQueue_healthyPendingTracks work)
      (createWorkQueue_fromSpec_registeredTasksMatch work)
      generated producerMember (by simp) matching child_candidate
      (by
        refine ⟨⟨.executionGroup [1, 0, 0, 0, 1, 0], [child]⟩, ?_, by simp [childGroup]⟩
        cbv
        exact List.mem_cons_self)
      (fun failure => failure.nonempty rfl)
  rcases support with same | ancestor
  · exact False.elim (child_not_yet_live (List.mem_map.mpr ⟨node, nodeMember, same⟩))
  · exact ⟨dependencies, known, node, nodeMember, ancestor, linked, nonzero⟩

/-- Completed-ancestor closure supplies registration availability for produced work.
Witness: initial closure and the checked healthy ledgers discharge the general reuse
lemma, including the descendant-support case rather than direct producer-key reuse. -/
theorem child_registration_available
    : queue.ChildGroupsAvailable work [] result.work := by
  have tasks : queue.tasks = [producer] := by cbv
  have producerMember : producer ∈ queue.tasks := by rw [tasks]; simp
  exact (createWorkQueue_healthyRetiredAncestors generated).childGroupsAvailable
    (createWorkQueue_healthyRegisteredTaskAccounting work)
    (createWorkQueue_healthyPendingTracks work)
    (createWorkQueue_fromSpec_registeredTasksMatch work)
    generated producerMember (by simp) matching

/-- Generated replay derives owner existence for a genuinely new child task.
Witness: the parent has nonempty child work; the unconditional joint replay theorem
needs only matched/fresh/ready inputs and the real start check. The child remains pending.
-/
theorem produced_child_ownerAncestry
    : ∃ parents : Nat → Keys,
        (queue.runNormalized [[.taskSuccess parentTask result]]).1.OwnerAncestry
          work parents [.taskSuccess parentTask result] := by
  have known : TaskAt work parentTask [parent.key] none
      (.object [] (.ok ([("user", .object [])], 0))) := by
    refine ⟨[⟨parent, []⟩], [], _, children, [], ?_, rfl, rfl⟩
    cbv
  have valid : ValidGraphEvents work [.taskSuccess parentTask result] :=
    .append .nil matching (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, known, by intro source impossible; cases impossible⟩
  obtain ⟨parents, _, replayed⟩ := generated.runNormalized_ownerAncestry
    [[.taskSuccess parentTask result]] valid (by cbv)
  exact ⟨parents, replayed⟩

/-- The newly registered child survives with its own pending occurrence.
Witness: direct evaluation verifies that the nonempty owner-accounting regression is
not an already-complete or empty-work case.
-/
theorem produced_child_still_pending
    : ((queue.runNormalized [[.taskSuccess parentTask result]]).1.groupNode?
        child.key).map
        GroupNode.pending
      = some 1 := by
  cbv

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducerSupport
