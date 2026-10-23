import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RetiredTaskReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNodeKeys

/-! Exact rejection slots after a task failure has been consumed. Missing computation
nodes satisfy this observation without claiming that the task remains live.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

/-- Every existing computation for this occurrence contains its fixed rejection count. -/
def State.FailureCached (queue : State) (occurrence : Occurrence) (errors : Nat) : Prop :=
  ∀ node ∈ queue.taskNodes,
    node.task.occurrence = occurrence → node.rejection = some errors

/-- A host snapshot supplies the tracked failure and has no conflicting count for it. -/
structure FailureInSnapshot (available : List (Occurrence × Nat))
    (occurrence : Occurrence) (errors : Nat)
    : Prop where
  lookup
    : available.findSome?
        (fun entry => if entry.1 == occurrence then some entry.2 else none)
      = some errors
  consistent : ∀ entry ∈ available, entry.1 = occurrence → entry.2 = errors

/-- Matching fixed task outcomes determine a unique task-local failure count. -/
theorem GraphEvent.MatchesWork.taskFailure_count_unique {work occurrence left right}
    (first : (GraphEvent.taskFailure occurrence left).MatchesWork work)
    (second : (GraphEvent.taskFailure occurrence right).MatchesWork work)
    : left = right := by
  obtain ⟨owners, producer, path, known⟩ := first
  obtain ⟨otherOwners, birth, otherPath, other⟩ := second
  have same := (known.unique other).2.2
  cases same
  rfl

/-- A present snapshot entry fixes lookup when all counts for that occurrence agree. -/
theorem FailureInSnapshot.of_mem {available occurrence errors}
    (member : (occurrence, errors) ∈ available)
    (consistent : ∀ entry ∈ available, entry.1 = occurrence → entry.2 = errors)
    : FailureInSnapshot available occurrence errors := by
  refine ⟨?_, consistent⟩
  induction available with
  | nil => cases member
  | cons entry rest ih =>
      by_cases same : entry.1 = occurrence
      · simp only [List.findSome?_cons, occurrence_beq_iff_eq, same, ↓reduceIte,
          consistent entry List.mem_cons_self same]
      · have later : (occurrence, errors) ∈ rest := by
          rcases List.mem_cons.mp member with first | later
          · exact False.elim (same (congrArg Prod.fst first).symm)
          · exact later
        simpa only [List.findSome?_cons, occurrence_beq_iff_eq, same, ↓reduceIte,
          Option.or]
          using ih later
            (fun next listed => consistent next (List.mem_cons_of_mem _ listed))

/-- A missing computation has no rejection slot left to update. -/
theorem State.FailureCached.of_missing {queue : State} {occurrence errors}
    (missing : queue.taskNode? occurrence = none)
    : queue.FailureCached occurrence errors := by
  intro node member same
  exact False.elim (List.find?_eq_none.mp missing node member
    ((occurrence_beq_iff_eq _ _).mpr same))

/-- Replacing a slot preserves its tracked rejection when the replacement agrees. -/
theorem State.FailureCached.putTaskNode {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (updated : TaskNode)
    (agrees : updated.task.occurrence = occurrence → updated.rejection = some errors)
    : (queue.putTaskNode updated).FailureCached occurrence errors := by
  intro node member same
  obtain ⟨old, prior, selected⟩ := List.mem_map.mp member
  split at selected
  · subst node; exact agrees same
  · subst node; exact cached old prior same

/-- Subtree removal only filters the computation map. -/
theorem State.FailureCached.removeGroup {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (ref : Nat)
    : (queue.removeGroup ref).FailureCached occurrence errors :=
  fun node member => cached node (List.mem_filter.mp member).1

/-- Publication removal only filters the computation map. -/
theorem State.FailureCached.removeTask {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (removed : Occurrence)
    : (queue.removeTask removed).FailureCached occurrence errors :=
  fun node member => cached node (List.mem_filter.mp member).1

/-- Cache exposure retains the fixed count even if the tracked entry is absent. -/
theorem State.FailureCached.cacheTaskFailures {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors)
    (available : List (Occurrence × Nat))
    (consistent : ∀ entry ∈ available, entry.1 = occurrence → entry.2 = errors)
    : (queue.cacheTaskFailures available).FailureCached occurrence errors := by
  unfold State.cacheTaskFailures
  induction available generalizing queue with
  | nil => exact cached
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      apply ih _ (fun next member => consistent next (List.mem_cons_of_mem _ member))
      split
      · exact cached
      · rename_i node found
        apply cached.putTaskNode
        intro same
        have identity := (State.taskNode?_some found).2
        exact congrArg some (consistent entry List.mem_cons_self (identity.symm.trans same))

private theorem State.FailureCached.putExistingTaskNode {queue occurrence errors node}
    (cached : State.FailureCached queue occurrence errors)
    (member : node ∈ queue.taskNodes) (updated : TaskNode)
    (sameTask : updated.task = node.task) (rejection : updated.rejection = node.rejection)
    : (queue.putTaskNode updated).FailureCached occurrence errors := by
  apply cached.putTaskNode
  intro same
  rw [rejection]
  exact cached node member (sameTask ▸ same)

/-- Starting a computation initializes its rejection from the same supplied failure. -/
theorem State.FailureCached.startTask {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (started : Occurrence)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.startTask started available).FailureCached occurrence errors := by
  unfold State.startTask
  split
  · exact cached
  · split
    · exact cached
    · rename_i task found
      intro node member same
      rcases List.mem_append.mp member with old | new
      · exact cached node old same
      · obtain rfl := List.mem_singleton.mp new
        have identity := (occurrence_beq_iff_eq _ _).mp
          (List.find?_some (p := fun task : Task => task.occurrence == started) found)
        have tracked : started = occurrence := identity.symm.trans same
        simpa only [tracked] using known.lookup

/-- Registration of another task cannot introduce an empty slot for the tracked occurrence. -/
theorem State.FailureCached.addTask {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (task : Task)
    (different : occurrence ≠ task.occurrence)
    : (queue.addTask task).FailureCached occurrence errors := by
  intro node member same
  rcases queue.addTask_startedOldOrNew task member with old | new
  · exact cached node old same
  · subst node; exact False.elim (different same.symm)

/-- Stream registration changes child-stream metadata, preserving rejection slots. -/
theorem State.FailureCached.addStreams {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (streams producer)
    : (queue.addStreams streams producer).1.FailureCached occurrence errors := by
  unfold State.addStreams
  dsimp only
  split
  · exact cached
  · split
    · exact cached
    · rename_i node found
      exact cached.putExistingTaskNode (List.mem_of_find?_eq_some found) _ rfl rfl

/-- Fresh child registration preserves every already completed failure slot. -/
theorem State.FailureCached.maybeIntegrateWork {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (incoming : Work)
    (fresh : ∀ task ∈ incoming.tasks, occurrence ≠ task.occurrence)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork incoming producer).1.FailureCached occurrence errors := by
  have groups : (queue.addGroups incoming.groups).1.FailureCached occurrence errors := by
    simpa only [State.FailureCached, State.addGroups_taskNodes] using cached
  have loop (tasks : List Task) (current : State)
      (prior : current.FailureCached occurrence errors)
      (fresh : ∀ task ∈ tasks, occurrence ≠ task.occurrence)
      : (tasks.foldl State.addTask current).FailureCached occurrence errors := by
    induction tasks generalizing current with
    | nil => exact prior
    | cons task rest ih =>
        exact ih _ (prior.addTask task (fresh task List.mem_cons_self))
          (fun next member => fresh next (List.mem_cons_of_mem _ member))
  exact (loop incoming.tasks _ groups fresh).addStreams incoming.streams producer

/-- Empty-shell pruning changes no rejection slots. -/
theorem State.FailureCached.pruneEmptyGroups {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (groups)
    : (queue.pruneEmptyGroups groups).1.FailureCached occurrence errors := by
  simpa only [State.FailureCached, State.pruneEmptyGroups_taskNodes] using cached

/-- Group startup preserves the count through both cache inspection and private starts. -/
theorem State.FailureCached.startGroup {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (ref : Nat)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.startGroup ref available).1.FailureCached occurrence errors := by
  have exposed := cached.cacheTaskFailures available known.consistent
  unfold State.startGroup
  dsimp only
  split
  · exact exposed
  · rename_i group found
    split
    · have loop (tasks : List Occurrence) (current : State)
          (prior : current.FailureCached occurrence errors)
          : (tasks.foldl (fun q task => q.startTask task available) current).FailureCached
              occurrence errors := by
        induction tasks generalizing current with
        | nil => exact prior
        | cons task rest ih => exact ih _ (prior.startTask task known)
      exact loop group.tasks _ exposed
    · change ((queue.cacheTaskFailures available).removeGroup group.group.node.ref).FailureCached
        occurrence errors
      exact exposed.removeGroup _

/-- The complete released-work startup retains exact completed rejection slots. -/
theorem State.FailureCached.startNewWork {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (released : NewWork)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (queue.startNewWork released available).1.FailureCached occurrence errors := by
  let step (acc : State × List GroupFailureEvent) (ref : Nat) :=
    let next := acc.1.startGroup ref available
    (next.1, acc.2 ++ next.2)
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.FailureCached occurrence errors)
      : (refs.foldl step acc).1.FailureCached occurrence errors := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih => exact ih _ (prior.startGroup ref known)
  have streams (refs : NodeRefs) (current : State)
      (prior : current.FailureCached occurrence errors)
      : (refs.foldl State.startStream current).FailureCached occurrence errors := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  exact streams _ _ (groups _ _ cached)

/-- Publication flushing never rewrites a retained rejection. -/
theorem State.FailureCached.flushGroupTasks {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (tasks : List Occurrence)
    (values : List Execution.ExecutionGroupValue) (streams : NodeRefs)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.FailureCached occurrence
        errors := by
  induction tasks generalizing queue values streams with
  | nil => exact cached
  | cons task rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih cached _ _
      · exact ih (cached.removeTask task) _ _

/-- Successful group completion only filters or retains existing rejection slots. -/
theorem State.FailureCached.finishGroupSuccess {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.FailureCached occurrence errors := by
  have flushed := cached.flushGroupTasks group.tasks [] []
  let values := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State := { values.1 with
    groupNodes := values.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := values.1.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.FailureCached occurrence errors := flushed
  exact filtered.pruneEmptyGroups _

/-- Ready draining preserves exact cached failures across release and startup. -/
theorem State.FailureCached.drainReadyGroups_go {queue occurrence errors}
    (cached : State.FailureCached queue occurrence errors) (fuel : Nat)
    {available : List (Occurrence × Nat)}
    (known : FailureInSnapshot available occurrence errors)
    : (State.drainReadyGroups.go available fuel queue).1.FailureCached occurrence
        errors := by
  induction fuel generalizing queue with
  | zero => exact cached
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact cached
      · rename_i node selected
        exact ih ((cached.finishGroupSuccess node).startNewWork _ known)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
