import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredClosureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainRootCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A generated release drains a cached failure and success before closing a shared owner. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : DeliveryNode := ⟨0, [], some (.string "R")⟩
private def parent : DeliveryNode := ⟨1, [], some (.string "P")⟩
private def failed : DeliveryNode := ⟨2, [], some (.string "F")⟩
private def firstOwner : DeliveryNode := ⟨3, [], some (.string "B")⟩
private def lastOwner : DeliveryNode := ⟨4, [], some (.string "C")⟩
private def failedTask : Occurrence := .executionGroup [1, 0]
private def firstTask : Occurrence := .executionGroup [1, 1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 1, 0]

private def firstValue : ExecutionGroupValue :=
  {
    path := [],
    data := [("a", .scalar "a")],
    errors := 0,
    deliveryGroups := [root, firstOwner]
  }

private def sharedValue : ExecutionGroupValue :=
  {
    path := [],
    data := [("b", .scalar "b")],
    errors := 0,
    deliveryGroups := [root, failed, lastOwner]
  }

private def parentValue : ExecutionGroupValue :=
  { path := [], data := [("c", .scalar "c")], errors := 0, deliveryGroups := [parent] }

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩, ⟨failed, [parent]⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨firstOwner, [parent]⟩] []
          (.ok (firstValue.data, 0)) (.combine .empty .empty))
        (.combine
          (.executionGroup [⟨root, []⟩, ⟨failed, [parent]⟩, ⟨lastOwner, [parent]⟩] []
            (.ok (sharedValue.data, 0)) (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨parent, []⟩] [] (.ok (parentValue.data, 0))
              (.combine .empty .empty))
            .empty))))

private def failure : GraphEvent := .taskFailure failedTask 1
private def first : GraphEvent := .taskSuccess firstTask ⟨firstValue, {}⟩
private def shared : GraphEvent := .taskSuccess sharedTask ⟨sharedValue, {}⟩
private def finish : GraphEvent := .taskSuccess parentTask ⟨parentValue, {}⟩
private def received : List GraphEvent := [failure, first, shared, finish]
private def initial : State := State.initialize (Work.fromExecution work)
private def waiting : State := initial.replayGraphEvents [failure, first, shared]

/-- A cached failure and two buffered successes arise from overlapping generated defers.
Witness: R starts the shared tasks; P delays notices for F, B, and C until its own success.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "required", field "a", field "b"] (some "R"),
      defer [field "c", defer [field "required", field "b"] (some "F"),
        defer [field "a"] (some "B"), defer [field "b"] (some "C")] (some "P")], ?_⟩
  cbv

/-- The source settlements have fixed generated payloads, fresh identities, and real starts.
Witness: each task is producer-free and started through R or P; later values survive R's
failure through their unannounced child owners.
-/
theorem source_valid
    : ValidGraphEvents work received ∧ inputsStarted work [received] = true := by
  have failedKnown : TaskAt work failedTask [root.ref, failed.ref] none (.object [] (.error 1)) :=
    ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩
  have firstKnown : TaskAt work firstTask [root.ref, firstOwner.ref] none
      (.object [] (.ok (firstValue.data, 0))) :=
    ⟨_, [], .ok (firstValue.data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩
  have sharedKnown : TaskAt work sharedTask [root.ref, failed.ref, lastOwner.ref] none
      (.object [] (.ok (sharedValue.data, 0))) :=
    ⟨_, [], .ok (sharedValue.data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok (parentValue.data, 0))) :=
    ⟨_, [], .ok (parentValue.data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩
  have one : ValidGraphEvents work [failure] :=
    .append .nil ⟨_, _, _, failedKnown⟩
      (by simp [failure, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, failedKnown, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [failure, first] :=
    .append one ⟨_, _, firstKnown, rfl, rfl⟩
      (by simp [failure, first, GraphEvent.Fresh, GraphEvent.identities, failedTask, firstTask])
      ⟨_, _, _, firstKnown, by intro source impossible; cases impossible⟩
  have three : ValidGraphEvents work [failure, first, shared] :=
    .append two ⟨_, _, sharedKnown, rfl, rfl⟩
      (by simp [failure, first, shared, GraphEvent.Fresh, GraphEvent.identities,
        failedTask, firstTask, sharedTask])
      ⟨_, _, _, sharedKnown, by intro source impossible; cases impossible⟩
  refine ⟨
    .append three ⟨_, _, parentKnown, rfl, rfl⟩ ?_
      ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩,
    by cbv
  ⟩
  simp [failure, first, shared, finish, GraphEvent.Fresh, GraphEvent.identities,
    failedTask, firstTask, sharedTask, parentTask]

-----------------------------------------------------------------------------------------
-- The actual parent-success handler activates the three retained outcomes
-----------------------------------------------------------------------------------------

private def parentNode : GroupNode :=
  {
    group := ⟨parent, none⟩,
    childGroups := [failed.ref, firstOwner.ref, lastOwner.ref],
    tasks := [parentTask]
  }

private def ready : State :=
  let stored :=
    waiting.putTaskNode { task := ⟨parentTask, [parent]⟩, value := some parentValue }
  let closed := (stored.putGroupNode parentNode).finishGroupSuccess parentNode
  closed.1.startNewWork closed.2.2

private def firstNode : TaskNode :=
  { task := ⟨firstTask, firstValue.deliveryGroups⟩, value := some firstValue }

private def sharedNode : TaskNode :=
  { task := ⟨sharedTask, sharedValue.deliveryGroups⟩, value := some sharedValue }

private def middle := State.drainReadyGroups.go 2 ready

/-- The analyzed drain is the actual suffix of the generated parent-success handler.
Witness: exact handler reduction, including P's value and the notice carrier before drain.
-/
theorem actual_release_boundary
    : (waiting.handleGraphEvent finish).1 = ready.drainReadyGroups.1
      ∧ (waiting.handleGraphEvent finish).2
        = [
            .groupValues parent [parentValue],
            .groupSuccess parent [failed, firstOwner, lastOwner] []
          ]
          ++ ready.drainReadyGroups.2 := by
  constructor <;> cbv

/-- The drain first emits F's cached failure, then B's stored value and successful closure.
Witness: the first two iterations leave C and its exact shared value live; the full drain
then publishes that value and closes C. F's cleanup must not discard C's contribution.
-/
theorem mixed_drain_output
    : middle.2
        = [
          .groupFailure failed 1,
          .groupValues firstOwner [firstValue],
          .groupSuccess firstOwner [] []
        ]
      ∧ middle.1.taskNode? sharedTask = some sharedNode
      ∧ ready.drainReadyGroups.2
        = middle.2
          ++ [.groupValues lastOwner [sharedValue], .groupSuccess lastOwner [] []] := by
  constructor
  · cbv
  constructor <;> cbv

/-- The actual mixed drain cannot leave any of its three covered roots stranded.
Witness: generic success/failure root-coverage preservation plus the empty final root list;
the conclusion is not obtained by evaluating the three final group lookups directly.
-/
theorem mixed_drain_no_stranded_roots
    : ∀ ref ∈ [failed.ref, firstOwner.ref, lastOwner.ref],
        ready.drainReadyGroups.1.groupNode? ref = none := by
  have noChildren : ∀ node ∈ ready.groupNodes, node.childGroups = [] := by
    have checked : ready.groupNodes.all (fun node => node.childGroups.isEmpty) = true := by cbv
    intro node member
    simpa using (List.all_eq_true.mp checked node member)
  have forest : ready.RemovalForest (fun _ => []) := by
    refine ⟨?_, ?_, ?_⟩
    · intro node member
      rw [noChildren node member]
      simp
    · intro node member child linked
      rw [noChildren node member] at linked
      cases linked
    · intro first second firstMember secondMember linked
      rw [noChildren first firstMember] at linked
      cases linked
  intro ref member
  apply State.drainReadyGroups_no_stranded_group
    (by unfold State.GroupRefsUnique; cbv; decide)
    forest
    (by cbv)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨failed.ref, by cbv; exact List.mem_cons_self, .self (by cbv)⟩
  · exact ⟨firstOwner.ref, by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self,
      .self (by cbv)⟩
  · exact ⟨lastOwner.ref,
      by cbv; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      .self (by cbv)⟩

/-- The two buffered values are fresh against the already emitted parent publication.
Witness: exact live nodes and their distinct occurrences; no output admission is assumed.
-/
private theorem ready_inventory
    : ready.PublicationInventory (fun _ _ => True) [(parentTask, parentValue)] := by
  refine ⟨by simp, by simp, ?_⟩
  intro node member value stored
  have nodes : ready.taskNodes = [firstNode, sharedNode] := by cbv
  rw [nodes] at member
  rcases List.mem_cons.mp member with same | later
  · subst node
    exact ⟨trivial, by simp [firstNode, firstTask, parentTask]⟩
  · have same := List.mem_singleton.mp later
    subst node
    exact ⟨trivial, by simp [sharedNode, sharedTask, parentTask]⟩

/-- Actual generated replay supplies buffered links, including values with failed co-owners.
Witness: the general normalized-replay theorem applied to the validated started source.
-/
theorem replay_buffered_links : (initial.runNormalized [received]).1.StoredTaskLinks :=
  generated.runNormalized_storedTaskLinks [received] source_valid.1 source_valid.2

/-- The real parent-success release supplies all links needed by the subsequent drain.
Witness: generated replay establishes the input links and pending ledger, then local
preservation carries them through fresh storage, flushing, and activation. No live-map
enumeration or output-admission premise supplies buffered memberships.
-/
private theorem ready_links : ready.StoredTaskLinks := by
  have valid : ValidGraphEvents work [failure, first, shared] :=
    source_valid.1.prefix ⟨[finish], rfl⟩
  have accepted : initial.acceptsBatch [failure, first, shared] = true := by cbv
  have linked := generated.replayGraphEvents_storedTaskLinks _ valid accepted
  have accounted := (createWorkQueue_pendingAccounting work).replayGraphEvents (before := [])
    generated [failure, first, shared] valid accepted
  have found : waiting.taskNode? parentTask
      = some { task := ⟨parentTask, [parent]⟩ } := by cbv
  have known := State.taskNode?_some found
  have installed := linked.putTaskNode
    { task := ⟨parentTask, [parent]⟩, value := some parentValue }
    (fun _ => accounted.links _
      (accounted.started { task := ⟨parentTask, [parent]⟩ } known.1) (by
      simp [GraphEvent.taskSettlements, GraphEvent.groupSuccesses, GraphEvent.groupFailures,
        failure, first, shared, failedTask, firstTask, sharedTask, parentTask]))
  have oldGroup : waiting.groupNode? parent.ref = some { parentNode with pending := 1 } := by
    cbv
  have updated := installed.putGroupNodeSameTasks accounted.refs
    { parentNode with pending := 1 } (List.mem_of_find?_eq_some oldGroup) parentNode rfl rfl
  exact (updated.finishGroupSuccess parentNode).startNewWork _

/-- The two-iteration boundary is an exact prefix of the complete three-iteration drain.
Witness: the general budget-splitting equation preserves both the intermediate state and
the output concatenation, including the cached failure.
-/
theorem actual_drain_split
    : ready.drainReadyGroups
      = let later := State.drainReadyGroups.go 1 middle.1
        (later.1, middle.2 ++ later.2) := by
  have budget : ready.groupNodes.length = 3 := by cbv
  rw [State.drainReadyGroups, budget]
  exact State.drainReadyGroups_go_add 2 1 ready

/-- The earlier successful carrier is covered without including C's later publication.
Witness: select B's actual output position in the full drain; its strict prefix contains
exactly the first value, despite the remaining drain iterations.
-/
theorem mixed_drain_first_coverage
    : ∃ added : List ObjectPublication,
        added.map Prod.snd = [firstValue]
        ∧ (([(parentTask, parentValue)] ++ added).map Prod.fst).Nodup
        ∧ (firstTask, firstValue) ∈ added := by
  obtain ⟨_, _, added, _, _, _, values, inventory, covered⟩ :=
    ready_inventory.drainReadyGroups_go_success_coverage ready_links ready.groupNodes.length
      (index := 2) (group := firstOwner) (groups := []) (streams := []) (by cbv)
  refine ⟨added, values.trans (by cbv), inventory.unique, ?_⟩
  exact covered firstTask firstNode firstValue (by cbv) rfl
    (by simp [firstNode, firstValue])

/-- The shared value is in an occurrence-unique ledger before C closes, across F's error.
Witness: select C's actual output position; the general theorem recovers its queue boundary
and buffered links internally. The shared occurrence is covered before C's closure.
-/
theorem mixed_drain_strict_coverage
    : ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        ready.drainReadyGroups.2 = before ++ [.groupSuccess lastOwner [] []]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ (([(parentTask, parentValue)] ++ added).map Prod.fst).Nodup
        ∧ (sharedTask, sharedValue) ∈ added := by
  obtain ⟨_, _, added, _, _, _, values, inventory, covered⟩ :=
    ready_inventory.drainReadyGroups_go_success_coverage ready_links ready.groupNodes.length
      (index := 4) (group := lastOwner) (groups := []) (streams := []) (by cbv)
  refine ⟨added, ready.drainReadyGroups.2.take 4, ?_, values, inventory.unique, ?_⟩
  · cbv
  · exact covered sharedTask sharedNode sharedValue (by cbv) rfl
      (by simp [sharedNode, sharedValue])

/-- One shared ledger covers both successful carriers, with their exact strict prefixes.
Witness: the simultaneous drain theorem, not two per-carrier existential choices. The
second value is excluded from the first prefix even though both belong to the final drain.
-/
theorem mixed_drain_shared_ledger
    : ∃ added : List ObjectPublication,
        added.map Prod.snd = [firstValue, sharedValue]
        ∧ (([(parentTask, parentValue)] ++ added).map Prod.fst).Nodup
        ∧ ready.BufferedClosuresCovered added ready.drainReadyGroups.2
        ∧ (firstTask, firstValue) ∈ added.take 1
        ∧ (sharedTask, sharedValue) ∈ added.take 2
        ∧ (sharedTask, sharedValue) ∉ added.take 1 := by
  obtain ⟨added, values, inventory, covered, _⟩ :=
    ready_inventory.drainReadyGroups_go_bufferedCoverage ready_links ready.groupNodes.length
  have exactValues : added.map Prod.snd = [firstValue, sharedValue] := values.trans (by cbv)
  have firstCovered := covered 2 firstOwner [] [] (by cbv)
    firstTask firstNode firstValue (by cbv) rfl (by simp [firstNode, firstValue])
  have lastCovered := covered 4 lastOwner [] [] (by cbv)
    sharedTask sharedNode sharedValue (by cbv) rfl (by simp [sharedNode, sharedValue])
  have firstCount : ((ready.drainReadyGroups.2.take 2).flatMap WorkQueueEvent.objectValues).length
      = 1 := by cbv
  have lastCount : ((ready.drainReadyGroups.2.take 4).flatMap WorkQueueEvent.objectValues).length
      = 2 := by cbv
  rw [show State.drainReadyGroups.go ready.groupNodes.length ready = ready.drainReadyGroups
    from rfl, firstCount] at firstCovered
  rw [show State.drainReadyGroups.go ready.groupNodes.length ready = ready.drainReadyGroups
    from rfl, lastCount] at lastCovered
  refine ⟨added, exactValues, inventory.unique, covered, firstCovered, lastCovered, ?_⟩
  intro tooEarly
  have inValues : sharedValue ∈ (added.take 1).map Prod.snd :=
    List.mem_map.mpr ⟨_, tooEarly, rfl⟩
  rw [List.map_take, exactValues] at inValues
  have same : sharedValue = firstValue := by simpa only [List.take_succ_cons,
    List.take_zero, List.mem_singleton] using inValues
  have data := congrArg ExecutionGroupValue.data same
  have names := congrArg (fun fields => fields.map Prod.fst) data
  simp [sharedValue, firstValue] at names

/-- The internal drain boundary excludes its published task but keeps the later shared one.
Witness: coverage and membership exclusion use one full-drain ledger. Its exact prefix
contains B's value after the cached failure; C's still-buffered membership is checked in
the actual intermediate queue, so future removal cannot justify an earlier notice.
-/
theorem mixed_drain_membership_boundary
    : middle.1.TaskMembershipAbsent firstTask
      ∧ ∃ node ∈ middle.1.groupNodes, sharedTask ∈ node.tasks := by
  obtain ⟨added, _, _, covered, _, _, _, _, cleared⟩ :=
    ready_inventory.drainReadyGroups_go_prefixCoverage ready_links ready.groupNodes.length
  have firstCovered := covered 2 firstOwner [] [] (by cbv)
    firstTask firstNode firstValue (by cbv) rfl (by simp [firstNode, firstValue])
  have size : ((ready.drainReadyGroups.2.take 2).flatMap WorkQueueEvent.objectValues).length
      = (middle.2.flatMap WorkQueueEvent.objectValues).length := by cbv
  rw [show State.drainReadyGroups.go ready.groupNodes.length ready = ready.drainReadyGroups
    from rfl, size] at firstCovered
  refine ⟨cleared 2 (by cbv) (firstTask, firstValue) firstCovered, ?_⟩
  refine ⟨{ group := ⟨lastOwner, some parent.ref⟩, tasks := [sharedTask] }, ?_, by simp⟩
  cbv
  exact .head _

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerDrainCoverage
