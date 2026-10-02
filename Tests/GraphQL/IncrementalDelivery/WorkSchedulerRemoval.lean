import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Generated failure cleanup and raw stale-link removal regressions. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRemoval
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def required (alias : Name) : Selection := field "required" [] [] (some alias)

private def selections : List Selection :=
  [
    defer
      [
        required "badP",
        defer [required "bad1"] (some "C1"),
        defer [required "bad2"] (some "C2"),
        defer [field "a"] (some "C3")
      ]
      (some "P"),
    defer [required "bad1"] (some "R1"),
    defer [required "bad2"] (some "R2")
  ]

private def work : Execution.Work :=
  ((executeRootSelectionSetCore schema resolvers [] 40 "Query" (.object "Query" 0)
      selections).run
    0).1.work

private def node (key : Nat) (label : String) : DeliveryNode :=
  { key, path := [], label := some (.string label) }

private def parent : DeliveryNode := node 0 "P"
private def child : DeliveryNode := node 3 "C3"
private def parentTask : Occurrence := .executionGroup [1, 0]
private def firstTask : Occurrence := .executionGroup [1, 1, 0]
private def secondTask : Occurrence := .executionGroup [1, 1, 1, 0]

private def firstFailure : GraphEvent := .taskFailure firstTask 1
private def secondFailure : GraphEvent := .taskFailure secondTask 1
private def parentFailure : GraphEvent := .taskFailure parentTask 1

private def batches : List (List GraphEvent) :=
  [[firstFailure], [secondFailure], [parentFailure]]

private def initial : State := State.initialize (Work.fromExecution work)

private def before : State :=
  ((initial.handleGraphEvent firstFailure).1.handleGraphEvent secondFailure).1

/-- The work is produced by ordinary pure query execution, not hand-written raw Work.
Witness: the schema, resolver environment, source object, and selection set above.
-/
theorem generated : ExecutedWork work :=
  ⟨Nat, schema, resolvers, [], 40, "Query", .object "Query" 0, selections, rfl⟩

/-- The parent task has the fixed non-null-field failure used by the host input.
Witness: reduce its structural location in the generated work.
-/
private theorem parent_known
    : TaskAt work parentTask [0] none (.object [] (.error 1)) := by
  refine ⟨[{ node := parent }], [], .error 1, .empty, [], ?_, rfl, rfl⟩
  cbv

/-- The first failure is shared by a latent child and an independent root group.
Witness: reduce its generated contributor descriptors and fixed error outcome.
-/
private theorem first_known
    : TaskAt work firstTask [1, 4] none (.object [] (.error 1)) := by
  refine ⟨[{ node := node 1 "C1", ancestors := [parent] },
    { node := node 4 "R1" }], [], .error 1, .empty, [], ?_, rfl, rfl⟩
  cbv

/-- The second failure likewise reaches a latent child through another root owner.
Witness: reduce its generated contributor descriptors and fixed error outcome.
-/
private theorem second_known
    : TaskAt work secondTask [2, 5] none (.object [] (.error 1)) := by
  refine ⟨[{ node := node 2 "C2", ancestors := [parent] },
    { node := node 5 "R2" }], [], .error 1, .empty, [], ?_, rfl, rfl⟩
  cbv

/-- A fresh root-produced failure satisfies the smaller host-event semantics.
Witness: its known fixed result supplies both outcome matching and producer readiness.
-/
private theorem append_failure {events occurrence owners}
    (valid : ValidGraphEvents work events)
    (known : TaskAt work occurrence owners none (.object [] (.error 1)))
    (fresh : (GraphEvent.taskFailure occurrence 1).Fresh events)
    : ValidGraphEvents work (events ++ [.taskFailure occurrence 1]) :=
  .append valid ⟨owners, none, [], known⟩ fresh
    ⟨owners, none, _, known, by intro source impossible; cases impossible⟩

/-- All three failures form a legal source history: outcomes match, identities are
fresh, and there are no unsettled producers. Witness: three source append rules.
-/
theorem inputs_valid : ValidGraphEvents work batches.flatten := by
  have first := append_failure .nil first_known (by
    simp [GraphEvent.Fresh, GraphEvent.identities])
  have second := append_failure first second_known (by
    simp [GraphEvent.Fresh, GraphEvent.identities, firstTask, secondTask])
  exact append_failure second parent_known
    (by simp [GraphEvent.Fresh, GraphEvent.identities, firstTask, secondTask, parentTask])

/-- The queue actually requested every task at its settlement boundary.
Witness: evaluation of the public start-discipline checker, including batching.
-/
theorem inputs_started : inputsStarted work batches = true := by cbv

/-- The concrete queue's three initial notices satisfy the unchanged initialization
contract. Witness: their generated descriptors have no defer dependencies or producers.
-/
theorem initialized : Initializes work initial.initialGroups initial.initialStreams := by
  have parentKnown : NodeAt work parent .group [] none := by
    refine ⟨[1, 0], [{ node := parent }], [], .error 1, .empty, [],
      { node := parent }, ?_, by simp, rfl, rfl⟩
    cbv
  have firstKnown : NodeAt work (node 4 "R1") .group [] none := by
    refine ⟨[1, 1, 0], [{ node := node 1 "C1", ancestors := [parent] },
      { node := node 4 "R1" }], [], .error 1, .empty, [],
      { node := node 4 "R1" }, ?_, by simp, rfl, rfl⟩
    cbv
  have secondKnown : NodeAt work (node 5 "R2") .group [] none := by
    refine ⟨[1, 1, 1, 0], [{ node := node 2 "C2", ancestors := [parent] },
      { node := node 5 "R2" }], [], .error 1, .empty, [],
      { node := node 5 "R2" }, ?_, by simp, rfl, rfl⟩
    cbv
  have eligible (group : DeliveryNode) (known : NodeAt work group .group [] none)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] group .group [] none := by
    exact ⟨by simp [announcedKeys, pendingKeys], Or.inl ⟨fun failure => failure.nonempty rfl,
        Or.inr (group_not_initially_accounted known)⟩, by simp, by simp⟩
  have notices : initial.initialGroups = [parent, node 4 "R1", node 5 "R2"]
      ∧ initial.initialStreams = [] := by cbv
  rw [notices.1, notices.2]
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro group member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨[], none, parentKnown, eligible _ parentKnown⟩
  · exact ⟨[], none, firstKnown, eligible _ firstKnown⟩
  · exact ⟨[], none, secondKnown, eligible _ secondKnown⟩

/-- The failure prefix retains healthy accounting and retired-ancestor certificates.
Witness: the current joint replay theorem, including cached unannounced child failures.
-/
theorem failure_prefix_accounted
    : ∃ parents,
        (initial.runNormalized [[firstFailure], [secondFailure]]).1.OwnerAncestry
          work parents [firstFailure, secondFailure] := by
  obtain ⟨parents, _, ledger⟩ := generated.runNormalized_ownerAncestry
    [[firstFailure], [secondFailure]] (inputs_valid.prefix ⟨[parentFailure], rfl⟩) (by cbv)
  exact ⟨parents, ledger⟩

/-- Failed latent children remain cached while the healthy sibling is still live.
Witness: concrete pre-parent-failure metadata; these are retained links, not stale links.
-/
theorem retained_links
    : before.groupNodes.map (fun group => group.group.node.key) = [0, 1, 2, 3]
      ∧ (before.groupNode? parent.key).map GroupNode.childGroups = some [1, 2, 3]
      ∧ (before.groupNode? child.key).map (fun group => group.group.parent)
        = some (some parent.key) := by
  cbv

/-- Each latent child preserves its own error while awaiting the parent's outcome.
Witness: actual cache lookup, guarding against prematurely deleting an unannounced failure.
-/
theorem failures_retained
    : (before.groupNode? 1).map GroupNode.failure = some (some 1)
      ∧ (before.groupNode? 2).map GroupNode.failure = some (some 1) := by
  constructor <;> cbv

/-- The healthy child remains connected beside the two retained failed siblings.
Witness: extract the actual parent/child lookups from the checked queue-state projection.
-/
theorem surviving_child_path : before.LiveDescendant parent.key child.key := by
  obtain ⟨parentNode, parentFound, children⟩ := Option.map_eq_some_iff.mp retained_links.2.1
  obtain ⟨childNode, childFound, _⟩ := Option.map_eq_some_iff.mp retained_links.2.2
  exact .child parentFound (by simp [children, child, node]) (.self childFound)

/-- The general coverage theorem removes this generated descendant.
Witness: valid input-prefix replay supplies the forest automatically; only the actual
stored live path is supplied, not an evaluated removal result or an added queue premise.
-/
theorem removal_covers_surviving_child
    : (before.removeGroup parent.key).groupNode? child.key = none
      ∧ child.key ∉ (before.removeGroup parent.key).rootGroups := by
  have valid : ValidGraphEvents work [[firstFailure], [secondFailure]].flatten :=
    inputs_valid.prefix ⟨[parentFailure], rfl⟩
  have same : (initial.runNormalized [[firstFailure], [secondFailure]]).1 = before := by
    cbv
  have path : (initial.runNormalized [[firstFailure], [secondFailure]]).1.LiveDescendant
      parent.key child.key := same.symm ▸ surviving_child_path
  have absent := generated.runNormalized_removeGroup_covers
    [[firstFailure], [secondFailure]] valid path
  rw [← same]
  exact absent

/-- The complete failure handler, not just direct group removal, covers the child.
Witness: the generated replay theorem follows the actual stored task's owner loop;
evaluation is used only to identify that task and the pre-handler state.
-/
theorem taskFailure_covers_surviving_child
    : (before.taskFailure parentTask 1).1.groupNode? child.key = none
      ∧ child.key ∉ (before.taskFailure parentTask 1).1.rootGroups := by
  have valid : ValidGraphEvents work [[firstFailure], [secondFailure]].flatten :=
    inputs_valid.prefix ⟨[parentFailure], rfl⟩
  have same : (initial.runNormalized [[firstFailure], [secondFailure]]).1 = before := by
    cbv
  have stored : (before.taskNode? parentTask).map (fun task => task.task.groups)
      = some [parent] := by cbv
  obtain ⟨task, found, groups⟩ := Option.map_eq_some_iff.mp stored
  have replayFound : (initial.runNormalized [[firstFailure], [secondFailure]]).1.taskNode?
      parentTask = some task := by simpa only [same] using found
  have path : (initial.runNormalized [[firstFailure], [secondFailure]]).1.LiveDescendant
      parent.key child.key := same.symm ▸ surviving_child_path
  have absent := generated.runNormalized_taskFailure_covers
    [[firstFailure], [secondFailure]] valid (errors := 1) replayFound
    (by
      unfold State.taskHasHealthyOwner
      rw [groups]
      cbv)
    (show parent ∈ task.task.groups by simp [groups])
    (by cbv; exact List.mem_cons_self) path
  rw [← same]
  exact absent

/-- The live child is invalidated when its parent fails even though it has no failed
contributor of its own. Witness: the genuine generated defer-ancestor relation.
-/
theorem child_invalidated : GroupInvalidated work [parentTask] child.key := by
  have childKnown : NodeAt work child .group [parent.key] none := by
    refine ⟨[1, 1, 1, 1, 0], [{ node := child, ancestors := [parent] }], [],
      .ok ([("a", .scalar "a")], 0), .combine .empty .empty, [],
      { node := child, ancestors := [parent] }, ?_, by simp, rfl, rfl⟩
    cbv
  exact .groupDependency (ancestor := parent.key) ⟨child, none, childKnown, rfl⟩ (by simp)
    (.task ⟨none, _, parent_known⟩ (by simp [parent, node]) (by simp))

/-- Cleanup handles the retained failed siblings and removes
the remaining descendant. Witness: reduce direct removal and the actual failure handler.
The previous traversal left the child behind in both cases.
-/
theorem removal_clears_descendant
    : (before.removeGroup parent.key).groupNodes.map (fun group => group.group.node.key)
        = []
      ∧ (before.handleGraphEvent parentFailure).1.groupNodes.map
          (fun group => group.group.node.key)
        = [] := by
  cbv

-----------------------------------------------------------------------------------------
-- Sequential removals cannot hide another owner's surviving descendant
-----------------------------------------------------------------------------------------

private def removalTask : TaskNode :=
  { task := ⟨.executionGroup [], [node 1 "first", node 0 "outer"]⟩ }

/-- A raw bookkeeping fixture isolates overlapping removal roots. It is not claimed
to be generated query work or a conforming source history.
-/
private def sequentialQueue : State :=
  {
    groupNodes :=
      [
        { group := ⟨node 0 "outer", none⟩, childGroups := [1, 2] },
        { group := ⟨node 1 "first", some 0⟩ },
        { group := ⟨node 2 "last", some 0⟩ }
      ]
    rootGroups := [0]
    taskNodes := [removalTask]
  }

private def removalParents (key : Nat) : Keys := if key = 0 then [] else [0]

/-- The raw fixture is a finite canonical removal forest.
Witness: its only stored edges are distinct increasing edges from key zero.
-/
private theorem sequential_forest : sequentialQueue.RemovalForest removalParents := by
  constructor
  · intro group member
    simp only [sequentialQueue, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro group member key linked
    simp only [sequentialQueue, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at linked
      rcases linked with rfl | rfl <;> rfl
    · cases linked
    · cases linked
  · intro parent child parentMember childMember linked
    simp only [sequentialQueue, List.mem_cons, List.not_mem_nil, or_false] at parentMember
    rcases parentMember with rfl | rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at linked
      rcases linked with same | same <;> simp [node, same]
    · cases linked
    · cases linked

/-- Removing the first owner leaves a stale child link before the second owner runs.
Witness: evaluate only this intermediate group-map projection.
-/
theorem sequential_removal_stale_link
    : (sequentialQueue.removeGroup 1).groupNode? 1 = none
      ∧ ((sequentialQueue.removeGroup 1).groupNode? 0).map GroupNode.childGroups
        = some [1, 2] := by cbv

/-- The second owner still removes its other descendant after the first removal.
Witness: the general failure-fold theorem, not evaluation of the terminal state.
-/
theorem sequential_removal_covers_last
    : (sequentialQueue.taskFailure (.executionGroup []) 1).1.groupNode? 2 = none
      ∧ 2 ∉ (sequentialQueue.taskFailure (.executionGroup []) 1).1.rootGroups := by
  have found : sequentialQueue.taskNode? (.executionGroup []) = some removalTask := by
    cbv
  have parentFound : sequentialQueue.groupNode? 0
      = some { group := ⟨node 0 "outer", none⟩, childGroups := [1, 2] } := by cbv
  have childFound : sequentialQueue.groupNode? 2
      = some { group := ⟨node 2 "last", some 0⟩ } := by cbv
  have path : sequentialQueue.LiveDescendant 0 2 :=
    .child parentFound (by simp) (.self childFound)
  exact State.taskFailure_liveDescendant_absent sequential_forest
    (by
      change ([0, 1, 2] : List Nat).Nodup
      decide)
    found
    (by cbv)
    (show node 0 "outer" ∈ removalTask.task.groups by simp [removalTask])
    (by change 0 ∈ ([0] : List Nat); decide)
    path

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRemoval
