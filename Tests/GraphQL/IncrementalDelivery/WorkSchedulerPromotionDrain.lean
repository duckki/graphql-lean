import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PromotionPaths
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A cached successful child drains on release and promotes its unfinished descendant. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerPromotionDrain
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def child : DeliveryNode := ⟨1, [], some (.string "C")⟩
private def descendant : DeliveryNode := ⟨2, [], some (.string "D")⟩
private def other : DeliveryNode := ⟨3, [], some (.string "R")⟩
private def parentTask : Occurrence := .executionGroup [1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 0]
private def parentData : List (Name × ResponseValue) := [("p", .scalar "a")]
private def sharedData : List (Name × ResponseValue) := [("x", .scalar "b")]
private def noChildren : Execution.Work := .combine .empty .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨parent, []⟩] [] (.ok (parentData, 0)) noChildren)
      (.combine
        (.executionGroup [⟨child, [parent]⟩, ⟨other, []⟩] [] (.ok (sharedData, 0))
          noChildren)
        (.combine
          (.executionGroup [⟨descendant, [child, parent]⟩] []
            (.ok ([("z", .scalar "c")], 0)) noChildren)
          (.combine
            (.executionGroup [⟨other, []⟩] []
              (.ok ([("keep", .scalar "a")], 0)) noChildren)
            .empty))))

private def sharedResult : TaskResult :=
  {
    value :=
      { path := [], data := sharedData, errors := 0, deliveryGroups := [child, other] },
    work := Work.fromExecution noChildren [1, 1, 0, 0]
  }

private def parentResult : TaskResult :=
  {
    value := { path := [], data := parentData, errors := 0, deliveryGroups := [parent] },
    work := Work.fromExecution noChildren [1, 0, 0]
  }

private def first : GraphEvent := .taskSuccess sharedTask sharedResult
private def finish : GraphEvent := .taskSuccess parentTask parentResult
private def initial : State := State.initialize (Work.fromExecution work)
private def before : State := (initial.runNormalized [[first]]).1

/-- Pure execution generates the parent, shared child, grandchild, and other-root work.
Witness: the extra R-only field prevents early publication of the shared C/R value. -/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "a" [] [] (some "p"),
      defer [field "b" [] [] (some "x"),
        defer [field "c" [] [] (some "z")] (some "D")] (some "C")] (some "P"),
      defer [field "b" [] [] (some "x"), field "a" [] [] (some "keep")] (some "R")], ?_⟩
  cbv

/-- Both successful settlements satisfy fixed-outcome, freshness, producer, and start laws.
Witness: structural descriptors at root addresses and executable start discipline. -/
theorem source_valid
    : ValidGraphEvents work [first, finish]
      ∧ inputsStarted work [[first], [finish]] = true := by
  have sharedKnown : TaskAt work sharedTask [child.ref, other.ref] none
      (.object [] (.ok (sharedData, 0))) :=
    ⟨_, [], .ok (sharedData, 0), noChildren, [], rfl, rfl, rfl⟩
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok (parentData, 0))) :=
    ⟨_, [], .ok (parentData, 0), noChildren, [], rfl, rfl, rfl⟩
  have one : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, sharedKnown, rfl, rfl⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, sharedKnown, by intro source impossible; cases impossible⟩
  exact ⟨
    .append one ⟨_, _, parentKnown, rfl, rfl⟩
      (by
        simp [first, finish, GraphEvent.Fresh, GraphEvent.identities, parentTask, sharedTask])
      ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩,
    by cbv
  ⟩

/-- The first success is silent; parent completion then drains C and announces D.
Witness: exact replay includes C's stored value and closure after its notice carrier,
while R and D remain active with unfinished work. -/
theorem output
    : (initial.runNormalized [[first]]).2 = []
      ∧ before.rootGroups = [parent.ref, other.ref]
      ∧ (before.taskSuccess parentTask parentResult).1.rootGroups
        = [other.ref, descendant.ref]
      ∧ (initial.runNormalized [[first], [finish]]).2
        = [[
            .groupValues parent
              [{
                path := [], data := parentData, errors := 0, deliveryGroups := [parent]
              }],
            .groupSuccess parent [child] [],
            .groupValues child
              [{
                path := [],
                data := sharedData,
                errors := 0,
                deliveryGroups := [child, other]
              }],
            .groupSuccess child [descendant] []
          ]] := by
  cbv

/-- The new root reached through the drain belongs to an earlier active subtree.
Witness: the general task-success origin theorem covers the fold and final drain;
the computed old frontier excludes D itself. No specific path is supplied as a premise. -/
theorem drained_root_has_original_path
    : let taskNode : TaskNode :=
        { task := { occurrence := parentTask, groups := [parent] } }
      let integrated :=
        ((before.putTaskNode
            { taskNode with value := some parentResult.value }).maybeIntegrateWork
          parentResult.work (some parentTask)).1
      ∃ root ∈ before.rootGroups, integrated.LiveDescendant root descendant.ref := by
  let taskNode : TaskNode := { task := { occurrence := parentTask, groups := [parent] } }
  have found : before.taskNode? parentTask = some taskNode := by cbv
  have active : descendant.ref ∈ (before.taskSuccess parentTask parentResult).1.rootGroups := by
    rw [output.2.2.1]
    simp
  have origin := before.taskSuccess_rootOrigins
    (createWorkQueue_runNormalized_groupRefsUnique _ _) parentTask parentResult taskNode
    found descendant.ref active
  exact origin.resolve_left (by rw [output.2.1]; decide)

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerPromotionDrain
