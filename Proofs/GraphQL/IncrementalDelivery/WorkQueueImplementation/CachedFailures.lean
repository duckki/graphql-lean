import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupInvalidation

/-! Provenance of retained failures, independent of output-history admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Cached failures have a recorded contributing task
-----------------------------------------------------------------------------------------

/-- Retained task rejections have recorded contributors for each of their owners.
This proof-only predicate observes task outcomes, not a per-group cache.
-/
def State.CachedFailuresSupported (queue : State) (work : Execution.Work)
    (failed : List Occurrence)
    : Prop :=
  queue.CachedErrorsSatisfy
    (fun ref _ =>
      ∃ occurrence ∈ failed,
        ∃ owners, TaskHasOwners work occurrence owners ∧ ref ∈ owners)

/-- Failure provenance is the count-independent instance of task-rejection facts. -/
theorem State.cachedFailuresSupported_iff {queue work failed}
    : State.CachedFailuresSupported queue work failed
      ↔ queue.CachedErrorsSatisfy
          (fun ref _ =>
            ∃ occurrence ∈ failed,
              ∃ owners, TaskHasOwners work occurrence owners ∧ ref ∈ owners) :=
  Iff.rfl

/-- A retained rejection invalidates every contributor named by its task. -/
theorem State.CachedFailuresSupported.invalidated {queue work failed node group}
    (supported : State.CachedFailuresSupported queue work failed)
    (member : node ∈ queue.taskNodes) (cached : node.rejection.isSome = true)
    (owner : group ∈ node.task.groups)
    : GroupInvalidated work failed group.ref := by
  cases rejected : node.rejection with
  | none => simp [rejected] at cached
  | some errors =>
      obtain ⟨occurrence, recorded, owners, known, contributes⟩ :=
        supported node member errors rejected group owner
      exact .task known contributes recorded

/-- A task with a healthy contributor cannot retain a supported rejection. -/
theorem State.CachedFailuresSupported.healthy_none {queue work failed node group}
    (supported : State.CachedFailuresSupported queue work failed)
    (member : node ∈ queue.taskNodes) (owner : group ∈ node.task.groups)
    (healthy : ¬GroupInvalidated work failed group.ref)
    : node.rejection = none := by
  cases rejected : node.rejection with
  | none => rfl
  | some errors =>
      exact (healthy (supported.invalidated member (by simp [rejected]) owner)).elim

/-- Enlarging the failure inventory preserves every retained contributor witness. -/
theorem State.CachedFailuresSupported.weaken {queue work before after}
    (supported : State.CachedFailuresSupported queue work before)
    (included : before.Subset after)
    : queue.CachedFailuresSupported work after :=
  supported.mono
    (by
      rintro ref errors ⟨occurrence, recorded, owners, known, contributes⟩
      exact ⟨occurrence, included recorded, owners, known, contributes⟩)

/-- A pointwise invariant is preserved by folding individually preserving steps.
Witness: list induction threads the actual state, without queue-admission assumptions.
-/
private theorem fold_preserves {α β : Type} (property : β → Prop)
    (step : β → α → β) (items : List α)
    (preserved : ∀ state item, property state → property (step state item))
    (state : β) (valid : property state)
    : property (items.foldl step state) := by
  induction items generalizing state with
  | nil => exact valid
  | cons item rest ih => exact ih _ (preserved state item valid)

/-- Group metadata changes leave task-rejection provenance unchanged. -/
theorem State.CachedFailuresSupported.putGroupNode {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (updated : GroupNode)
    : (queue.putGroupNode updated).CachedFailuresSupported work failed :=
  supported

/-- Fresh group registration starts with no error cache.
Witness: existing nodes retain their witnesses and the appended node has `none`.
-/
theorem State.CachedFailuresSupported.addGroup {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (group : Group)
    : (queue.addGroup group).CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.addGroup group

/-- Parent-link installation leaves every cache and delivery ref unchanged.
Witness: the two actual folds register empty nodes and replace only child links.
-/
theorem State.CachedFailuresSupported.addGroups {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (groups : List Group)
    : (queue.addGroups groups).1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.addGroups groups

/-- Adding a task changes membership and counters, never the group's cached errors.
Witness: induction through contributing groups and the unchanged cache projection.
-/
theorem State.CachedFailuresSupported.addTask {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (task : Task)
    : (queue.addTask task).CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.addTask task

/-- Stream registration leaves group caches untouched.
Witness: only stream and producer-task registries are updated.
-/
theorem State.CachedFailuresSupported.addStreams {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.addStreams streams producer

/-- Immediate work integration preserves cache provenance.
Witness: group, task, and stream integration preserve it individually.
-/
theorem State.CachedFailuresSupported.maybeIntegrateWork {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (more : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork more producer).1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.maybeIntegrateWork more producer

/-- Pruning preserves caches on surviving groups.
Witness: each iteration retains or filters nodes, and creates no new cache.
-/
theorem State.CachedFailuresSupported.pruneEmptyGroups {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.pruneEmptyGroups groups

/-- Activation starts host work without changing group caches.
Witness: task, group, and stream start folds preserve the group-node projection.
-/
theorem State.CachedFailuresSupported.startNewWork {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (more : NewWork)
    : (queue.startNewWork more).CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.startNewWork more

/-- Queue creation contains no unsupported cached failure.
Witness: the empty state, immediate integration, pruning, and activation.
-/
theorem createWorkQueue_cachedFailuresSupported (input : Work) (work : Execution.Work)
    (failed : List Occurrence)
    : (State.initialize input).CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff]
  exact createWorkQueue_cachedErrors input _

-----------------------------------------------------------------------------------------
-- Publication, cleanup, and recursive release retain cache provenance
-----------------------------------------------------------------------------------------

/-- Task retirement changes only memberships, retaining every cache witness.
Witness: the group map leaves each delivery ref and cached error unchanged.
-/
theorem State.CachedFailuresSupported.removeTask {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.removeTask occurrence

/-- Group cancellation filters nodes without modifying retained caches.
Witness: every surviving node and witness belonged to the original queue.
-/
theorem State.CachedFailuresSupported.removeGroup {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (ref : NodeRef)
    : (queue.removeGroup ref).CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.removeGroup ref

/-- A successful flush retires tasks and prunes shells without creating failures.
Witness: the task fold preserves caches, and subsequent node filters retain provenance.
-/
theorem State.CachedFailuresSupported.finishGroupSuccess {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.finishGroupSuccess group

/-- Recursive release preserves cache support through both kinds of closure.
Witness: the actual bounded drain alternates supported success flushes and failure removal.
-/
theorem State.CachedFailuresSupported.drainReadyGroups {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    : queue.drainReadyGroups.1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.drainReadyGroups

/-- Successful settlement never introduces a new retained failure.
Witness: child integration, each contributor decrement/flush, activation, and full drain.
-/
theorem State.CachedFailuresSupported.taskSuccess {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (occurrence : Occurrence) (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.taskSuccess occurrence result

/-- Stream-item integration and its final drain preserve cached-failure support.
Witness: each item integrates fresh work, prunes, and activates without inventing caches.
-/
theorem State.CachedFailuresSupported.streamItems {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    : (queue.streamItems stream items).1.CachedFailuresSupported work failed := by
  rw [State.cachedFailuresSupported_iff] at supported ⊢
  exact supported.streamItems stream items

-----------------------------------------------------------------------------------------
-- Failed settlement installs only a recorded contributor's cache
-----------------------------------------------------------------------------------------

/-- Failure accumulation is supported by the task actually removed from the started map.
Witness: registered source provenance identifies all its owners; other caches are retained.
-/
theorem State.CachedFailuresSupported.taskFailure {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence) (errors : Nat)
    (recorded : occurrence ∈ failed)
    : (queue.taskFailure occurrence errors).1.CachedFailuresSupported work failed := by
  apply State.CachedErrorsSatisfy.taskFailure supported occurrence errors
  intro node found group member
  have live := List.mem_of_find?_eq_some found
  have same : node.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp
      (List.find?_some (p := fun candidate : TaskNode =>
        candidate.task.occurrence == occurrence) found)
  obtain ⟨address, payload, producer, _, known⟩ :=
    (matching node.task (registered node live)).1
  exact ⟨occurrence, recorded, _, ⟨producer, payload, same ▸ known⟩,
    List.mem_map.mpr ⟨group, member, rfl⟩⟩

/-- One host event preserves support when any failed task is included in `failed`.
Witness: unchanged caches on nonfailure handlers and task provenance on failure.
-/
theorem State.CachedFailuresSupported.handleGraphEvent {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (event : GraphEvent)
    (recorded
      : ∀ occurrence errors, event = .taskFailure occurrence errors → occurrence ∈ failed)
    : (queue.handleGraphEvent event).1.CachedFailuresSupported work failed := by
  cases event with
  | taskSuccess occurrence result => exact supported.taskSuccess occurrence result
  | taskFailure occurrence errors =>
      exact supported.taskFailure registered matching occurrence errors (recorded _ _ rfl)
  | streamItems stream items => exact supported.streamItems stream items
  | streamSuccess stream =>
      change (queue.streamSuccess stream).1.CachedFailuresSupported work failed
      unfold State.streamSuccess
      split <;> exact supported
  | streamFailure stream errors =>
      change (queue.streamFailure stream errors).1.CachedFailuresSupported work failed
      unfold State.streamFailure
      split <;> exact supported

-----------------------------------------------------------------------------------------
-- Provenance through finite host replay
-----------------------------------------------------------------------------------------

/-- A host batch preserves cache support and the task-registration witnesses it uses.
Witness: sequential event handling maintains all three internal facts together.
-/
theorem State.CachedFailuresSupported.handleGraphEvents {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (batch : List GraphEvent)
    (allMatch : ∀ event ∈ batch, event.MatchesWork work)
    (recorded
      : ∀ occurrence errors, .taskFailure occurrence errors ∈ batch → occurrence ∈ failed)
    : (queue.handleGraphEvents batch).1.CachedFailuresSupported work failed := by
  let invariant (current : State) := current.CachedFailuresSupported work failed
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (current, outputs) := acc
    let (next, produced) := current.handleGraphEvent event
    (next, outputs ++ produced)
  have fold (events : List GraphEvent) (included : events.Subset batch)
      (acc : State × List WorkQueueEvent) (valid : invariant acc.1)
      : invariant (events.foldl step acc).1 := by
    induction events generalizing acc with
    | nil => exact valid
    | cons event rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        have eventMember := included List.mem_cons_self
        refine ⟨valid.1.handleGraphEvent valid.2.1 valid.2.2 event ?_,
          valid.2.1.handleGraphEvent event, valid.2.2.handleGraphEvent event
            (allMatch event eventMember)⟩
        intro occurrence errors same
        exact recorded occurrence errors (same ▸ eventMember)
  unfold State.handleGraphEvents
  split
  · exact supported
  · let folded := batch.foldl step (queue, [])
    have final : folded.1.CachedFailuresSupported work failed :=
      (fold batch (List.Subset.refl _) (queue, []) ⟨supported, registered, matching⟩).1
    cases folded with
    | mk current outputs =>
        dsimp only at final ⊢
        split <;> exact final

/-- Normalized replay preserves support by input failures, independently of wire output.
Witness: batch induction carries registration alongside cache support; normalization
changes only publisher state and the collected outputs.
-/
theorem State.CachedFailuresSupported.runNormalized {queue work failed}
    (supported : State.CachedFailuresSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (batches : List (List GraphEvent))
    (allMatch : ∀ event ∈ batches.flatten, event.MatchesWork work)
    (recorded
      : ∀ occurrence errors,
          .taskFailure occurrence errors ∈ batches.flatten → occurrence ∈ failed)
    : (queue.runNormalized batches).1.CachedFailuresSupported work failed := by
  let invariant (current : State) := current.CachedFailuresSupported work failed
    ∧ current.StartedTasksRegistered ∧ current.RegisteredTasksMatch work
  have stable (acc : NormalizedAcc) (batch : List GraphEvent) (member : batch ∈ batches)
      (valid : invariant acc.1) : invariant (normalizedStep acc batch).1 := by
    have batchMatch : ∀ event ∈ batch, event.MatchesWork work := by
      intro event eventMember
      exact allMatch event (List.mem_flatten.mpr ⟨batch, member, eventMember⟩)
    have batchRecorded : ∀ occurrence errors,
        .taskFailure occurrence errors ∈ batch → occurrence ∈ failed := by
      intro occurrence errors eventMember
      exact recorded occurrence errors (List.mem_flatten.mpr ⟨batch, member, eventMember⟩)
    obtain ⟨current, publisher, outputs⟩ := acc
    have next : invariant (current.handleGraphEvents batch).1 :=
      ⟨valid.1.handleGraphEvents valid.2.1 valid.2.2 batch batchMatch batchRecorded,
        valid.2.1.handleGraphEvents batch, valid.2.2.handleGraphEvents batch batchMatch⟩
    dsimp only [normalizedStep]
    split <;> exact next
  have fold (more : List (List GraphEvent)) (included : more.Subset batches)
      (acc : NormalizedAcc) (valid : invariant acc.1)
      : invariant (more.foldl normalizedStep acc).1 := by
    induction more generalizing acc with
    | nil => exact valid
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (stable acc batch (included List.mem_cons_self) valid)
  exact (fold batches (List.Subset.refl _)
    (queue, { active := queue.initialGroups ++ queue.initialStreams }, [])
    ⟨supported, registered, matching⟩).1

/-- Every final cached failure has an actual contributing failure in the supplied input.
Witness: replay support with exactly the failed-task identities extracted from the input.
No explained output history, fairness, or queue-conformance premise is used.
-/
theorem createWorkQueue_runNormalized_cachedFailure_hasSource {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {node : TaskNode} {group : Execution.DeliveryNode} {errors : Nat}
    (member
      : node
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.taskNodes)
    (cached : node.rejection = some errors) (contributes : group ∈ node.task.groups)
    : ∃ occurrence errors owners,
        .taskFailure occurrence errors ∈ batches.flatten
        ∧ TaskHasOwners work occurrence owners
        ∧ group.ref ∈ owners := by
  let failed := batches.flatten.filterMap (fun event => match event with
    | .taskFailure occurrence _ => some occurrence
    | _ => none)
  have recorded : ∀ occurrence errors,
      .taskFailure occurrence errors ∈ batches.flatten → occurrence ∈ failed := by
    intro occurrence errors inInputs
    exact List.mem_filterMap.mpr ⟨.taskFailure occurrence errors, inInputs, rfl⟩
  have initialized := createWorkQueue_cachedFailuresSupported (Work.fromExecution work) work failed
  have supported := initialized.runNormalized (createWorkQueue_startedTasksRegistered _)
      (createWorkQueue_fromSpec_registeredTasksMatch work) batches
      (fun _ member => valid.eachMatches member) recorded
  obtain ⟨occurrence, inFailed, owners, known, owner⟩ := supported node member errors cached group contributes
  obtain ⟨event, inInputs, same⟩ := List.mem_filterMap.mp inFailed
  cases event <;> simp only [Option.some.injEq, reduceCtorEq] at same
  rename_i actual errors
  subst actual
  exact ⟨occurrence, errors, owners, inInputs, known, owner⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
