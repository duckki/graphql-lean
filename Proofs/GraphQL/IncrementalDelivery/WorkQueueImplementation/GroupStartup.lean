import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipSoundness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegisteredTasks

/-! Exact reference startup reporting, separately from the broader queue contract.
The failure branch reports all cached task rejections and acquires no new task nodes.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem State.putTaskNode_occurrences (queue : State) (updated : TaskNode)
    : (queue.putTaskNode updated).taskNodes.map (fun node => node.task.occurrence)
      = queue.taskNodes.map (fun node => node.task.occurrence) := by
  simp only [State.putTaskNode, List.map_map]
  apply List.map_congr_left
  intro node _
  dsimp only [Function.comp_apply]
  split
  · rename_i same
    have equal : node.task.occurrence = updated.task.occurrence := by
      cases left : node.task.occurrence <;> cases right : updated.task.occurrence <;>
        simp_all [BEq.beq, WorkQueueSemantics.instBEqOccurrence.beq]
      all_goals
        apply (beq_iff_eq (a := _) (b := _)).mp
        first | exact same | exact same.1
    exact equal.symm
  · rfl

private theorem State.cacheTaskFailures_occurrences (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).taskNodes.map (fun node => node.task.occurrence)
      = queue.taskNodes.map (fun node => node.task.occurrence) := by
  induction available generalizing queue with
  | nil => rfl
  | cons failure rest ih =>
      simp only [State.cacheTaskFailures, List.foldl_cons]
      split
      · exact ih queue
      · exact (ih _).trans (State.putTaskNode_occurrences queue _)

/-- A failed startup returns exactly one notice whose count sums every retained task's
cached rejection in membership order. Its state is immediate removal of that group.
The computation-availability snapshot is explicit; collected diagnostics are not read.
-/
theorem State.startGroup_reportsAllCachedFailures (queue : State)
    (available : List (Occurrence × Nat)) (ref : NodeRef) (group : GroupNode)
    (found : (queue.cacheTaskFailures available).groupNode? ref = some group)
    (failed
      : (group.tasks.filterMap
          (fun task =>
            ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection)))
        ≠ [])
    : queue.startGroup ref available
      = (
        (queue.cacheTaskFailures available).removeGroup group.group.node.ref,
        [⟨
          group.group.node,
          (group.tasks.filterMap
            (fun task =>
              ((queue.cacheTaskFailures available).taskNode? task).bind
                (·.rejection))).sum
        ⟩]
      ) := by
  have nonempty : List.isEmpty (group.tasks.filterMap
      (fun task => ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection)))
      = false := by
    cases errors
          : group.tasks.filterMap
              (fun task =>
                ((queue.cacheTaskFailures available).taskNode? task).bind
                  (·.rejection)) with
    | nil => exact (failed errors).elim
    | cons _ _ => rfl
  simp only [State.startGroup, found, nonempty, Bool.false_eq_true, ↓reduceIte,
    State.finishGroupFailure]

/-- Startup failure can only remove started task identities. In particular it starts
none of the group's previously unstarted private tasks, even if its notice is deferred.
-/
theorem State.startGroup_failure_noNewTasks (queue : State)
    (available : List (Occurrence × Nat)) (ref : NodeRef) (group : GroupNode)
    (found : (queue.cacheTaskFailures available).groupNode? ref = some group)
    (failed
      : (group.tasks.filterMap
          (fun task =>
            ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection)))
        ≠ [])
    : List.Sublist
        ((queue.startGroup ref available).1.taskNodes.map
          (fun node => node.task.occurrence))
        (queue.taskNodes.map (fun node => node.task.occurrence)) := by
  rw [queue.startGroup_reportsAllCachedFailures available ref group found failed]
  have retained :
      (((queue.cacheTaskFailures available).removeGroup group.group.node.ref).taskNodes.map
        (fun node => node.task.occurrence)).Sublist
        ((queue.cacheTaskFailures available).taskNodes.map (fun node => node.task.occurrence)) :=
    (List.filter_sublist).map (fun (node : TaskNode) => node.task.occurrence)
  simpa only [State.cacheTaskFailures_occurrences] using retained

/-- Proof-only occurrence labels for the existing local startup error collection.
The runtime stores only task rejections and returns the aggregate notice count.
-/
def State.cachedTaskCauses (queue : State) (tasks : List Occurrence)
    : List (Occurrence × Nat) :=
  tasks.filterMap
    fun occurrence =>
      (queue.taskNode? occurrence).bind fun node => node.rejection.map (occurrence, ·)

/-- Erasing proof labels recovers exactly the local error collection used by startup. -/
theorem State.cachedTaskCauses_errors (queue : State) (tasks : List Occurrence)
    : (queue.cachedTaskCauses tasks).map Prod.snd
      = tasks.filterMap
          (fun occurrence => (queue.taskNode? occurrence).bind (·.rejection)) := by
  induction tasks with
  | nil => rfl
  | cons occurrence rest ih =>
      cases found : queue.taskNode? occurrence with
      | none => simpa [State.cachedTaskCauses, found] using ih
      | some node =>
          cases rejected : node.rejection with
          | none => simpa [State.cachedTaskCauses, found, rejected] using ih
          | some errors =>
              simpa [State.cachedTaskCauses, found, rejected] using congrArg (errors :: ·) ih

/-- Startup cause labels retain the task-membership order and introduce no new occurrence. -/
theorem State.cachedTaskCauses_tasks (queue : State) (tasks : List Occurrence)
    : ((queue.cachedTaskCauses tasks).map Prod.fst).Sublist tasks := by
  induction tasks with
  | nil => exact List.Sublist.refl _
  | cons occurrence rest ih =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simpa [State.cachedTaskCauses, found] using List.Sublist.cons occurrence ih
      | some node =>
          cases rejected : node.rejection with
          | none =>
              simpa [State.cachedTaskCauses, found, rejected]
                using List.Sublist.cons occurrence ih
          | some errors =>
              simpa [State.cachedTaskCauses, found, rejected]
                using List.Sublist.cons_cons occurrence ih

/-- Every proof-labelled cause retains the exact provenance of its own task rejection. -/
theorem State.TaskRejectionsSatisfy.cachedTaskCauses {queue : State} {property}
    (prior : queue.TaskRejectionsSatisfy property) (tasks : List Occurrence)
    : ∀ cause ∈ queue.cachedTaskCauses tasks, property cause.1 cause.2 := by
  intro cause member
  obtain ⟨occurrence, _, selected⟩ := List.mem_filterMap.mp member
  cases found : queue.taskNode? occurrence with
  | none => simp [found] at selected
  | some node =>
      cases rejected : node.rejection with
      | none => simp [found, rejected] at selected
      | some errors =>
          have same : (occurrence, errors) = cause := by simpa [found, rejected] using selected
          subst cause
          have identity : node.task.occurrence = occurrence :=
            (occurrence_beq_iff_eq _ _).mp (List.find?_some
              (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
          simpa only [identity]
            using prior node (List.mem_of_find?_eq_some found) errors rejected

/-- A startup failure sums a nonempty list of distinct member-task rejections.
Occurrence labels are existential proof evidence for the runtime's local `errors` list;
neither the notice nor the group node gains a cause cache.
-/
theorem State.startGroup_failure_causes {queue : State} {property}
    (prior : queue.TaskRejectionsSatisfy property) (unique : queue.TaskMembershipsUnique)
    (ref : NodeRef) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors)
    {failure : GroupFailureEvent}
    (reported : failure ∈ (queue.startGroup ref available).2)
    : ∃ node ∈ queue.groupNodes,
        failure.group = node.group.node
        ∧ ∃ causes : List (Occurrence × Nat),
            causes ≠ []
            ∧ (causes.map Prod.fst).Sublist node.tasks
            ∧ (causes.map Prod.fst).Nodup
            ∧ failure.errors = (causes.map Prod.snd).sum
            ∧ ∀ cause ∈ causes, property cause.1 cause.2 := by
  have cached := prior.cacheTaskFailures available licensed
  unfold State.startGroup at reported
  dsimp only at reported
  split at reported
  · cases reported
  · rename_i node found
    split at reported
    · cases reported
    · rename_i rejected
      have same := List.mem_singleton.mp reported
      subst failure
      have member : node ∈ queue.groupNodes := by
        have live := List.mem_of_find?_eq_some found
        rwa [State.cacheTaskFailures_groupNodes] at live
      let causes := (queue.cacheTaskFailures available).cachedTaskCauses node.tasks
      have errors := (queue.cacheTaskFailures available).cachedTaskCauses_errors node.tasks
      have tasks := (queue.cacheTaskFailures available).cachedTaskCauses_tasks node.tasks
      refine ⟨node, member, rfl, causes, ?_, tasks, tasks.nodup (unique node member), ?_,
        cached.cachedTaskCauses node.tasks⟩
      · intro empty
        have emptyErrors : node.tasks.filterMap
            (fun task => ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection))
            = [] := by
          rw [← errors]
          exact congrArg (List.map Prod.snd) empty
        exact rejected (by simp [emptyErrors])
      · exact congrArg List.sum errors.symm

/-- A startup notice has positive aggregate errors when each cached computation does.
Witness: the failure branch's local error collection is nonempty, and every collected count
comes from an exact retained task rejection. No ownership or distinctness premise is needed
for this positivity fact; distinct-cause accounting remains a separate theorem.
-/
theorem State.startGroup_failure_positive {queue : State}
    (positive : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors)) (ref : NodeRef)
    (available : List (Occurrence × Nat))
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors)
    {failure : GroupFailureEvent}
    (reported : failure ∈ (queue.startGroup ref available).2)
    : 0 < failure.errors := by
  have cached := positive.cacheTaskFailures available licensed
  unfold State.startGroup at reported
  dsimp only at reported
  split at reported
  · cases reported
  · rename_i group found
    split at reported
    · cases reported
    · rename_i rejected
      have same := List.mem_singleton.mp reported
      subst failure
      apply List.sum_pos_iff_exists_pos_nat.mpr
      cases counts
            : group.tasks.filterMap
                (fun task =>
                  ((queue.cacheTaskFailures available).taskNode? task).bind
                    (·.rejection)) with
      | nil => simp [counts] at rejected
      | cons errors rest =>
          have member : errors ∈ group.tasks.filterMap
              (fun task =>
                ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection)) := by
            rw [counts]
            exact List.mem_cons_self
          refine ⟨errors, List.mem_cons_self, ?_⟩
          obtain ⟨occurrence, _, selected⟩ := List.mem_filterMap.mp member
          cases lookup : (queue.cacheTaskFailures available).taskNode? occurrence with
          | none => simp [lookup] at selected
          | some node =>
              exact cached node (List.mem_of_find?_eq_some lookup) errors
                (by simpa only [lookup, Option.bind_some] using selected)

/-- Every startup-fold failure retains a positive count under positive available rejections.
Witness: thread task-local positivity through each actual group start and concatenate the
unchanged local notice lists. Stream activation leaves those notices unchanged.
-/
theorem State.startNewWork_failure_positive {queue : State}
    (positive : queue.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
    (released : NewWork) (available : List (Occurrence × Nat))
    (licensed : ∀ occurrence errors, (occurrence, errors) ∈ available → 0 < errors)
    : ∀ failure ∈ (queue.startNewWork released available).2, 0 < failure.errors := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (valid : acc.1.TaskRejectionsSatisfy (fun _ errors => 0 < errors))
      (prior : ∀ failure ∈ acc.2, 0 < failure.errors)
      : ∀ failure ∈ (refs.foldl step acc).2, 0 < failure.errors := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih (step acc ref) (valid.startGroup ref available licensed)
        intro failure member
        exact (List.mem_append.mp member).elim (prior failure)
          (acc.1.startGroup_failure_positive valid ref available licensed)
  exact loop _ (_, []) positive (by simp)

/-- Startup's exact aggregate satisfies the public distinct-cause reporting relation.
Sound memberships identify contributors in the fixed Work; occurrence-indexed provenance
supplies each count and its availability. No runtime failure-cause list is introduced.
-/
theorem State.startGroup_failure_nodeCauses {queue : State} {work failed property}
    (prior : queue.TaskRejectionsSatisfy property) (unique : queue.TaskMembershipsUnique)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (ref : NodeRef) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors)
    (explains
      : ∀ occurrence errors,
          property occurrence errors
          → occurrence ∈ failed
            ∧ ∃ owners producer payload,
                TaskAt work occurrence owners producer payload
                ∧ payload.failure = some errors
                ∧ 0 < errors)
    {failure : GroupFailureEvent}
    (reported : failure ∈ (queue.startGroup ref available).2)
    : NodeFailureCauses work failed failure.group.ref failure.errors := by
  obtain ⟨node, member, groupEq, causes, nonempty, sublist, distinct, total, properties⟩ :=
    queue.startGroup_failure_causes prior unique ref available licensed reported
  refine ⟨causes, nonempty, distinct, ?_, total⟩
  intro occurrence errors cause
  obtain ⟨recorded, owners, producer, payload, known, count, positive⟩ :=
    explains occurrence errors (properties (occurrence, errors) cause)
  have listed : occurrence ∈ node.tasks :=
    sublist.subset (List.mem_map.mpr ⟨(occurrence, errors), cause, rfl⟩)
  obtain ⟨task, registered, identity, contributes⟩ := sound node member occurrence listed
  obtain ⟨⟨_, _, _, _, taskKnown⟩, _⟩ := matching task registered
  rw [identity] at taskKnown
  refine ⟨recorded, owners, producer, payload, known, ?_, count, positive⟩
  rw [groupEq]
  exact (taskKnown.unique known).1 ▸ contributes

/-- Every notice accumulated during root activation has distinct supported task causes.
The fold retains source provenance and sound, unique memberships at each group start.
-/
theorem State.startNewWork_failure_nodeCauses {queue : State} {work failed property}
    (prior : queue.TaskRejectionsSatisfy property) (unique : queue.TaskMembershipsUnique)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (more : NewWork) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → property occurrence errors)
    (explains
      : ∀ occurrence errors,
          property occurrence errors
          → occurrence ∈ failed
            ∧ ∃ owners producer payload,
                TaskAt work occurrence owners producer payload
                ∧ payload.failure = some errors
                ∧ 0 < errors)
    : ∀ failure ∈ (queue.startNewWork more available).2,
        NodeFailureCauses work failed failure.group.ref failure.errors := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (current, failures) := acc
    let (next, queued) := current.startGroup ref available
    (next, failures ++ queued)
  let invariant (acc : State × List GroupFailureEvent) :=
    acc.1.TaskRejectionsSatisfy property ∧ acc.1.TaskMembershipsUnique
      ∧ acc.1.GroupMembershipSound ∧ acc.1.RegisteredTasksMatch work
      ∧ ∀ failure ∈ acc.2, NodeFailureCauses work failed failure.group.ref failure.errors
  have groupStable (acc : State × List GroupFailureEvent) (ref : NodeRef)
      (valid : invariant acc) : invariant (step acc ref) := by
    refine ⟨valid.1.startGroup ref available licensed, ?_, valid.2.2.1.startGroup ref available,
      valid.2.2.2.1.startGroup ref available, ?_⟩
    · intro node member
      exact valid.2.1 node ((acc.1.startGroup_groupNodes_sublist ref available).subset member)
    · intro failure member
      rcases List.mem_append.mp member with earlier | new
      · exact valid.2.2.2.2 failure earlier
      · exact acc.1.startGroup_failure_nodeCauses valid.1 valid.2.1 valid.2.2.1
          valid.2.2.2.1 ref available licensed explains new
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent) (valid : invariant acc)
      : invariant (refs.foldl step acc) := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih => exact ih _ (groupStable acc ref valid)
  unfold State.startNewWork
  exact (loop _ _
          ⟨
            prior,
            unique,
            sound,
            matching,
            by
              intro failure member; cases member
          ⟩).2.2.2.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
