import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeferFailureSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.GroupAccounting

/-! The defer-only queue health guard reflects the full historical scheduler relation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Producer cancellation adds no new failure mechanism in generated defer-only work
-----------------------------------------------------------------------------------------

/-- Invalidating every producer owner invalidates each defer-only child owner.
Witness: generated producer support either reuses an owner or names it as an ancestor.
This is the queue-local counterpart of the historical producer-failure theorem.
-/
private theorem ExecutedWork.defer_producerOwners_invalidated
    {work failed occurrence owners producer payload ref parentOwners ancestor result}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    (known : TaskAt work occurrence owners (some producer) payload) (owner : ref ∈ owners)
    (parent : TaskAt work producer parentOwners ancestor result)
    (invalid : ∀ parentRef ∈ parentOwners, GroupInvalidated work failed parentRef)
    : GroupInvalidated work failed ref := by
  obtain ⟨parents, bound, coherent, continuous, ordered⟩ := generated.producerMetadata
  obtain ⟨node, kind, dependencies, descriptor, same⟩ := known.owner_at_producer owner
  obtain ⟨supportOwners, birth, value, parentRef, task, contributes, support⟩ :=
    shape.producer_parent coherent continuous ordered descriptor
  have failedOwner := invalid parentRef ((task.unique parent).1 ▸ contributes)
  rcases support with reused | dependency
  · exact (reused.trans same) ▸ failedOwner
  · have group := shape _ _ _ _ descriptor
    subst kind
    exact same ▸ .groupDependency ⟨node, some producer, descriptor, rfl⟩ dependency failedOwner

/-- Snapshot failure in generated defer-only work has a direct or ancestor cleanup cause.
Witness: mutual induction over failure and cancellation; producer cases reduce through
defer continuity, while stream-dependency cases are excluded by the work's shape.
No consistency assumption on the publication predicate is required.
-/
theorem ExecutedWork.defer_snapshotFailure_invalidated
    {work failed published ref} (generated : ExecutedWork work)
    (shape : Correctness.DeferOnly work)
    (failure : Causality.NodeFailed work failed published ref)
    : GroupInvalidated work failed ref := by
  induction failure
    using Causality.NodeFailed.rec
      (motive_2 :=
        fun occurrence _ =>
          ∀ owners producer payload ref,
            TaskAt work occurrence owners producer payload
            → ref ∈ owners
            → GroupInvalidated work failed ref) with
  | task task owner member => exact .task task owner member
  | groupDependency known member _ ih => exact .groupDependency known member ih
  | streamDependencies known _ _ _ =>
      obtain ⟨node, producer, descriptor, _⟩ := known
      have impossible := shape _ _ _ _ descriptor
      cases impossible
  | producers known noRoot _ _ ih =>
      obtain ⟨birth, node, kind, dependencies, descriptor, same⟩ := known
      have group := shape _ _ _ _ descriptor
      subst kind
      cases birth with
      | none => exact False.elim (noRoot ⟨node, .group, dependencies, descriptor, same⟩)
      | some producer =>
          obtain ⟨occurrence, owners, payload, task, member⟩ := descriptor.group_task
          obtain ⟨_, parentOwners, ancestor, result, parent⟩ := task.producer_dependency
          apply same ▸ generated.defer_producerOwners_invalidated shape task member parent
          intro ref owner
          by_cases recorded : producer ∈ failed
          · exact .task ⟨ancestor, result, parent⟩ owner recorded
          · exact ih producer ⟨node, .group, dependencies, descriptor, same⟩ recorded
              parentOwners ancestor result ref parent owner
  | owners known _ _ _ ih =>
      rename_i owners producer payload ref task member
      obtain ⟨birth, result, descriptor⟩ := known
      exact ih ref ((task.unique descriptor).1 ▸ member)
  | producerFailed projected _ recorded =>
      rename_i owners producer payload ref task member
      obtain ⟨otherOwners, result, descriptor⟩ := projected
      have same := (task.unique descriptor).2.1
      subst producer
      obtain ⟨_, parentOwners, ancestor, value, parent⟩ := task.producer_dependency
      exact generated.defer_producerOwners_invalidated shape task member parent
        (fun ref owner => .task ⟨ancestor, value, parent⟩ owner recorded)
  | producerCancelled projected _ _ ih =>
      rename_i owners producer payload ref task member
      obtain ⟨otherOwners, result, descriptor⟩ := projected
      have same := (task.unique descriptor).2.1
      subst producer
      obtain ⟨_, parentOwners, ancestor, value, parent⟩ := task.producer_dependency
      exact generated.defer_producerOwners_invalidated shape task member parent
        (fun ref owner => ih parentOwners ancestor value ref parent owner)

/-- Historical defer-only failure is supported by the failures visible at this prefix.
Witness: retain the original cut, apply snapshot reflection, then extend its failure list.
Later publications cannot erase the historical cause, so no replay admission is assumed.
-/
theorem ExecutedWork.defer_nodeFailed_invalidated
    {work matching events failures ref} (generated : ExecutedWork work)
    (shape : Correctness.DeferOnly work)
    (failure : NodeFailed work matching events failures ref)
    : GroupInvalidated work (failedBefore failures events.length) ref := by
  obtain ⟨cut, _, reached, cause⟩ := failure
  exact (generated.defer_snapshotFailure_invalidated shape cause).mono
    (failedBefore_subset failures reached)

/-- Queue-local invalidation embeds directly into historical failure on any work.
Witness: each direct cause retains its own reached cut; ancestor rules transport that
cause without needing a whole-history explanation or a snapshot-to-history assumption.
-/
theorem GroupInvalidated.historical
    {work failed matching events failures ref}
    (invalid : GroupInvalidated work failed ref)
    (included : failed.Subset (failedBefore failures events.length))
    : NodeFailed work matching events failures ref := by
  induction invalid with
  | task known owner recorded =>
      obtain ⟨producer, payload, task⟩ := known
      exact NodeFailed.task task owner (included recorded)
  | groupDependency known member _ ih =>
      obtain ⟨node, producer, descriptor, same⟩ := known
      exact same ▸ NodeFailed.groupDependency descriptor member ih

/-- For generated defer-only work, queue invalidation exactly describes historical failure.
Witness: mutual causal reflection in one direction and direct cut-preserving embedding
in the other. Matching and output history are arbitrary; the work-shape restriction is not.
-/
theorem ExecutedWork.defer_nodeFailed_iff_invalidated
    {work matching events failures ref} (generated : ExecutedWork work)
    (shape : Correctness.DeferOnly work)
    : NodeFailed work matching events failures ref
      ↔ GroupInvalidated work (failedBefore failures events.length) ref :=
  ⟨
    generated.defer_nodeFailed_invalidated shape,
    fun invalid => invalid.historical (List.Subset.refl _)
  ⟩

-----------------------------------------------------------------------------------------
-- Conditional causal bridge, discharged by the later generated health replay
-----------------------------------------------------------------------------------------

/-- Every accepted defer-only failure retains a historically healthy contributing owner
once replay preserves missing-parent health. Witness: exact source-cut guard reflection
and the causal equivalence above. All earlier cuts, including equal-index predecessors,
are retained; neither output admission nor publication matching correctness is assumed.
`GuardHealthCuts` supplies the historical premise from the general replay theorem.
-/
theorem createWorkQueue_eligibleObjectFailureCuts_deferHealthyOwner
    {work : Execution.Work} (generated : ExecutedWork work)
    (shape : Correctness.DeferOnly work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (missing
      : ∀ received : List GraphEvent,
          received.IsPrefix batches.flatten
          → State.MissingParentAncestorsHealthy
              ((State.initialize (Work.fromExecution work)).replayGraphEvents received)
              work
              ((State.initialize (Work.fromExecution work)).objectFailureContributions
                received))
    {before after : FailureCuts} {cut : Nat} {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        = before ++ (cut, occurrence) :: after)
    (matching : PublicationMatching) (events : List Execution.WorkQueueEvent)
    : ∃ owners ref,
        TaskHasOwners work occurrence owners
        ∧ ref ∈ owners
        ∧ ¬NodeFailed work matching events before ref := by
  obtain ⟨owners, ref, known, owner, safe⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_uninvalidatedOwner
      generated valid started missing split
  refine ⟨owners, ref, known, owner, ?_⟩
  intro failure
  apply safe ((generated.defer_nodeFailed_invalidated shape failure).toRecordInvalidated.mono ?_)
  intro task member
  obtain ⟨entry, kept, same⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp kept).1, same⟩

namespace ConformancePlan

/-- Missing-parent preservation supplies the defer-only owner-health graph node on the
exact accepted object cuts. Witness: recover each actual pre-handler guard and transport
its health to the witness's historical prefix. No alternate matching or cuts are chosen.
-/
theorem failureCutOwnerHealth_of_deferMissingParentHealth {work : Execution.Work}
    (generated : ExecutedWork work) (shape : Correctness.DeferOnly work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (missing
      : ∀ received : List GraphEvent,
          received.IsPrefix batches.flatten
          → State.MissingParentAncestorsHealthy
              ((initialQueue work).replayGraphEvents received) work
              ((initialQueue work).objectFailureContributions received))
    {w : Witness}
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = sourceObjectFailureCuts 0
            (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2))
    : FailureCutOwnerHealth work w := by
  intro before cut occurrence after split
  exact createWorkQueue_eligibleObjectFailureCuts_deferHealthyOwner generated shape
    valid started missing (exactCuts.symm.trans split) w.matching (w.events.take cut)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
