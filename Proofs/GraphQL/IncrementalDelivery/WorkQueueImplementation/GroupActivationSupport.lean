import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegisteredTasks

/-! Taskless registration records cannot acquire contents or become active roots. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Separate registered ancestor shells from groups supported by actual contributors
-----------------------------------------------------------------------------------------

/-- Groups outside `supported` have no task memberships or cached error, and every
active root is supported. Registration alone supplies neither fact about a group key.
-/
structure State.GroupKeySupport (queue : State) (supported : Nat → Prop) : Prop where
  contents
    : ∀ node ∈ queue.groupNodes,
        ¬supported node.group.node.key → node.tasks = [] ∧ node.failure = none
  roots : ∀ key ∈ queue.rootGroups, supported key

/-- An empty queue has no unsupported contents or active roots.
Witness: both lists are empty.
-/
theorem State.GroupKeySupport.empty (supported : Nat → Prop)
    : ({} : State).GroupKeySupport supported := by
  constructor <;> simp

/-- Replacing a group preserves support when its replacement has no unsupported contents.
Witness: split the node-map membership; root keys do not change.
-/
theorem State.GroupKeySupport.putGroupNode {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (updated : GroupNode)
    (contents
      : ¬supported updated.group.node.key → updated.tasks = [] ∧ updated.failure = none)
    : (queue.putGroupNode updated).GroupKeySupport supported := by
  refine ⟨?_, valid.roots⟩
  intro node member absent
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node; exact contents absent
  · subst node; exact valid.contents old oldMember absent

/-- Fresh registration adds an empty shell, even when its key is not a contributor.
Witness: existing records survive; the only new record has no task or error.
-/
theorem State.GroupKeySupport.addGroup {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (group : Group)
    : (queue.addGroup group).GroupKeySupport supported := by
  unfold State.addGroup
  split
  · exact valid
  · split
    · exact ⟨valid.contents, valid.roots⟩
    · refine ⟨?_, valid.roots⟩
      intro node member absent
      rcases List.mem_append.mp member with old | new
      · exact valid.contents node old absent
      · have same := List.mem_singleton.mp new
        subst node
        exact ⟨rfl, rfl⟩

/-- Installing ancestor links does not activate or populate their records.
Witness: registration and child-link folds preserve the same support predicate.
-/
theorem State.GroupKeySupport.addGroups {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (groups : List Group)
    : (queue.addGroups groups).1.GroupKeySupport supported := by
  let link (current : State) (group : Group) :=
    match group.parent with
    | none => current
    | some parent =>
        match current.groupNode? parent with
        | none => current
        | some node =>
            let children := if node.childGroups.contains group.node.key then
              node.childGroups else node.childGroups ++ [group.node.key]
            current.putGroupNode { node with childGroups := children }
  have registered (more : List Group) (current : State)
      (known : current.GroupKeySupport supported)
      : (more.foldl State.addGroup current).GroupKeySupport supported := by
    induction more generalizing current with
    | nil => exact known
    | cons group rest ih => exact ih _ (known.addGroup group)
  have linked (more : List Group) (current : State)
      (known : current.GroupKeySupport supported)
      : (more.foldl link current).GroupKeySupport supported := by
    induction more generalizing current with
    | nil => exact known
    | cons group rest ih =>
        apply ih
        unfold link
        split
        · exact known
        · split
          · exact known
          · rename_i node found
            exact known.putGroupNode _
              (known.contents node (List.mem_of_find?_eq_some found))
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  change (fresh.foldl link (fresh.foldl State.addGroup queue)).GroupKeySupport supported
  exact linked fresh _ (registered fresh queue valid)

/-- Task registration populates only its actual contributing keys.
Witness: each successful lookup is at a supported task-owner key; other records stay empty.
-/
theorem State.GroupKeySupport.addTask {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (task : Task)
    (owners : ∀ group ∈ task.groups, supported group.key)
    : (queue.addTask task).GroupKeySupport supported := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have loop (more : List Execution.DeliveryNode) (subset : more.Subset task.groups)
      (current : State) (known : current.GroupKeySupport supported)
      : (more.foldl step current).GroupKeySupport supported := by
    induction more generalizing current with
    | nil => exact known
    | cons group rest ih =>
        apply ih (fun _ member => subset (List.mem_cons_of_mem _ member))
        unfold step
        split
        · exact known
        · rename_i node found
          split
          · exact known
          · apply known.putGroupNode
            intro absent
            have same := State.groupNode?_key found
            exact (absent (same ▸ owners group (subset List.mem_cons_self))).elim
  let current := task.groups.foldl step registered
  have known : current.GroupKeySupport supported :=
    loop _ (fun _ h => h) registered ⟨valid.contents, valid.roots⟩
  change (if _ then { current with taskNodes := _ } else current).GroupKeySupport supported
  split <;> exact ⟨known.contents, known.roots⟩

/-- Stream registration does not alter group contents or active group keys.
Witness: only streams and a task's child-stream list change.
-/
theorem State.GroupKeySupport.addStreams {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.GroupKeySupport supported := by
  unfold State.addStreams
  split
  · exact ⟨valid.contents, valid.roots⟩
  · dsimp only
    split <;> exact ⟨valid.contents, valid.roots⟩

/-- Integration may add arbitrary ancestor shells but populates only supported owners.
Witness: compose group registration, the actual task fold, and stream registration.
-/
theorem State.GroupKeySupport.maybeIntegrateWork {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (work : Work)
    (owners : ∀ task ∈ work.tasks, ∀ group ∈ task.groups, supported group.key)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.GroupKeySupport supported := by
  have loop (more : List Task) (subset : more.Subset work.tasks) (current : State)
      (known : current.GroupKeySupport supported)
      : (more.foldl State.addTask current).GroupKeySupport supported := by
    induction more generalizing current with
    | nil => exact known
    | cons task rest ih =>
        exact ih (fun _ h => subset (List.mem_cons_of_mem _ h)) _
          (known.addTask task (owners task (subset List.mem_cons_self)))
  exact (loop _ (fun _ h => h) _ (valid.addGroups work.groups)).addStreams _ parentTask

-----------------------------------------------------------------------------------------
-- Pruning is the gate between internal records and observable activation
-----------------------------------------------------------------------------------------

/-- Every retained pruning candidate has actual supported contents, not just a record.
Witness: fuel induction removes unsupported empty shells and follows their children;
each kept candidate has a nonempty task list or cached failure at its own lookup.
-/
theorem State.GroupKeySupport.pruneEmptyGroups {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.GroupKeySupport supported
      ∧ ∀ group ∈ (queue.pruneEmptyGroups groups).2, supported group.key := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (known : current.GroupKeySupport supported)
      (keptKnown : ∀ group ∈ kept, supported group.key)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.GroupKeySupport supported
        ∧ ∀ group ∈ (State.pruneEmptyGroups.go fuel current remaining kept).2,
            supported group.key := by
    induction fuel generalizing current remaining kept with
    | zero => exact ⟨known, keptKnown⟩
    | succ fuel ih =>
        cases remaining with
        | nil => exact ⟨known, keptKnown⟩
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ known keptKnown
            · rename_i node found
              split
              · apply ih _ _ _ _ keptKnown
                exact ⟨fun other member =>
                  known.contents other (List.mem_filter.mp member).1, known.roots⟩
              · rename_i nonempty
                have supportedGroup : supported group.key := by
                  apply Classical.byContradiction
                  intro absent
                  have same := State.groupNode?_key found
                  obtain ⟨tasks, failure⟩ := known.contents node
                    (List.mem_of_find?_eq_some found) (same ▸ absent)
                  simp [tasks, failure] at nonempty
                apply ih _ _ _ known
                intro candidate member
                rcases List.mem_append.mp member with old | new
                · exact keptKnown candidate old
                · have same := List.mem_singleton.mp new
                  subst candidate
                  exact supportedGroup
  exact loop _ queue groups [] valid (by simp)

/-- Activating already-supported notices preserves support for every active root.
Witness: activation leaves group contents unchanged and appends exactly these keys.
-/
theorem State.GroupKeySupport.startNewWork {queue : State} {supported}
    (valid : queue.GroupKeySupport supported) (newWork : NewWork)
    (groups : ∀ group ∈ newWork.newGroups, supported group.key)
    : (queue.startNewWork newWork).GroupKeySupport supported := by
  constructor
  · intro node member absent
    rw [(queue.startNewWork_groupCore newWork).1] at member
    exact valid.contents node member absent
  · intro key member
    rw [(queue.startNewWork_groupCore newWork).2.2] at member
    rcases List.mem_append.mp member with old | new
    · exact valid.roots key old
    · obtain ⟨group, within, same⟩ := List.mem_map.mp new
      exact same ▸ groups group within

/-- Initial activation cannot announce a taskless ancestor merely because it was lowered.
Witness: integrate actual task owners, prune empty shells, then start the retained roots.
-/
theorem createWorkQueue_groupKeySupport (work : Work) (supported : Nat → Prop)
    (owners : ∀ task ∈ work.tasks, ∀ group ∈ task.groups, supported group.key)
    : (State.initialize work).GroupKeySupport supported := by
  have integrated := (State.GroupKeySupport.empty supported).maybeIntegrateWork work owners
  obtain ⟨pruned, groups⟩ := integrated.pruneEmptyGroups
    (({} : State).maybeIntegrateWork work).2.newGroups
  have started := pruned.startNewWork
    { (({} : State).maybeIntegrateWork work).2 with newGroups :=
        ((({} : State).maybeIntegrateWork work).1.pruneEmptyGroups
          (({} : State).maybeIntegrateWork work).2.newGroups).2 } groups
  exact ⟨started.contents, started.roots⟩

/-- Every populated or activated initial group key denotes a real contributing group.
Witness: exact task lowering supplies `NodeAt` owners; ancestor registration and pruning
preserve key support. This holds for raw work, without generated-work assumptions.
-/
theorem createWorkQueue_fromSpec_groupKeySupport (work : Execution.Work)
    : (State.initialize (Work.fromExecution work)).GroupKeySupport
        (fun key =>
          ∃ dependencies, NodeHasDependencies work key .group dependencies) := by
  apply createWorkQueue_groupKeySupport
  intro task member group owner
  obtain ⟨address, payload, occurrenceEq, known⟩ :=
    workFromSpec_tasks_taskAt WorkQueueSemantics.Located.root member
  have matching : TaskMatches work task :=
    ⟨⟨address, payload, none, occurrenceEq, known⟩,
      workFromSpec_tasks_groupsExact WorkQueueSemantics.Located.root member⟩
  exact matching.contributorKnown (List.mem_map.mpr ⟨group, owner, rfl⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
