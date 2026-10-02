import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Accepted failures remove announced owners while retaining latent error outcomes. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerAnnouncedRemoval
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def selections : List Selection :=
  [
    defer
      [
        field "required" [] [] (some "parent"),
        defer [field "required" [] [] (some "shared")] (some "C")
      ]
      (some "P"),
    defer [field "required" [] [] (some "shared")] (some "R")
  ]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def parent : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def child : DeliveryNode := ⟨1, [], some (.string "C")⟩
private def other : DeliveryNode := ⟨2, [], some (.string "R")⟩
private def parentTask : Occurrence := .executionGroup [1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 0]
private def initial : State := State.initialize (Work.fromExecution work)
private def sharedFailure : GraphEvent := .taskFailure sharedTask 1
private def before : State := (initial.runNormalized [[sharedFailure]]).1

/-- Pure execution generates the parent and shared latent/root failure tasks.
Witness: a non-null field selected under the three defer usages above. -/
theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0, selections, rfl⟩

/-- The first settlement is a valid fixed failure with no producer dependency.
Witness: the shared task's generated descriptor and the source append rule. -/
theorem prefix_valid : ValidGraphEvents work [sharedFailure] := by
  have known : TaskAt work sharedTask [child.key, other.key] none
      (.object [] (.error 1)) := by
    refine ⟨[{ node := child, ancestors := [parent] }, { node := other }],
      [], .error 1, .empty, [], ?_, rfl, rfl⟩
    cbv
  exact .append .nil ⟨_, _, _, known⟩
    (by simp [sharedFailure, GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, known, by intro source impossible; cases impossible⟩

/-- Both settlements were actually requested by queue initialization.
Witness: the shared task starts through R and the parent's task starts through P. -/
theorem inputs_started
    : inputsStarted work [[sharedFailure], [.taskFailure parentTask 1]] = true := by
  cbv

/-- The latent owner remains cached while only its announced co-owner emits failure.
Witness: concrete replay retains C's error and its link from P, without announcing C. -/
theorem latent_failure_retained
    : (before.groupNode? child.key).map GroupNode.failure = some (some 1)
      ∧ child.key ∉ before.rootGroups
      ∧ (before.groupNode? parent.key).map GroupNode.childGroups = some [child.key]
      ∧ (initial.runNormalized [[sharedFailure]]).2 = [[.groupFailure other 1]] := by
  refine ⟨by cbv, ?_, by cbv, by cbv⟩
  have roots : before.rootGroups = [parent.key] := by cbv
  rw [roots]
  decide

/-- An unannounced owner need not disappear when its accepted shared task fails.
Witness: C is already a live descendant of itself and survives with a cached error.
This refutes the former proof-only helper without its announced-owner qualification. -/
theorem unannounced_owner_not_removed
    : initial.LiveDescendant child.key child.key
      ∧ (initial.taskFailure sharedTask 1).1.groupNode? child.key ≠ none := by
  constructor
  · exact .self (node := (initial.groupNode? child.key).getD { group := { node := child } })
      (by cbv)
  · cbv
    simp

/-- The later accepted parent failure removes the cached child and its active key.
Witness: generated replay supplies the forest; the general announced-owner traversal
theorem consumes the concrete parent-to-child path. The conclusion is not evaluated. -/
theorem parent_failure_removes_cached_child
    : (before.taskFailure parentTask 1).1.groupNode? child.key = none
      ∧ child.key ∉ (before.taskFailure parentTask 1).1.rootGroups := by
  let taskNode : TaskNode := { task := { occurrence := parentTask, groups := [parent] } }
  have found : before.taskNode? parentTask = some taskNode := by cbv
  have path : before.LiveDescendant parent.key child.key := by
    apply State.LiveDescendant.child
      (node := (before.groupNode? parent.key).getD { group := { node := parent } })
      (child := child.key)
    · cbv
    · have links : ((before.groupNode? parent.key).getD
          { group := { node := parent } }).childGroups = [child.key] := by cbv
      rw [links]
      simp
    · exact .self (node := (before.groupNode? child.key).getD { group := { node := child } })
        (by cbv)
  exact generated.runNormalized_taskFailure_covers [[sharedFailure]] prefix_valid found
    (by cbv)
    (owner := parent)
    (by simp [taskNode])
    (by
      have roots : before.rootGroups = [parent.key] := by cbv
      change parent.key ∈ before.rootGroups
      rw [roots]
      simp)
    path

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerAnnouncedRemoval
