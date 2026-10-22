import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialDeferredExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization
import Proofs.GraphQL.IncrementalDelivery.Correctness.BoundedTaskReportAssembly
import Tests.GraphQL.IncrementalDelivery.DeferredPhase
import Tests.GraphQL.IncrementalDelivery.NestedStreamExistence

/-! Multiple shared deferred tasks admit full runs, including their child notices. -/

namespace GraphQL.IncrementalDelivery.Tests.InitialDeferredExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics
open DeferredPhase

/-- Two root deferred tasks with overlapping owners and a child stream have a complete
run for successful or positive-error outcomes. Witness: the finite deferred phase, a reserved
success carrier or causal cancellation, then stream completion with actual failure reports.
-/
theorem multiple_run_exists (first second : Result (List (Name × ResponseValue)))
    (firstPositive : BasicErrors.PositiveFailure first)
    (secondPositive : BasicErrors.PositiveFailure second)
    : ∃ history, AdmissibleRun (work first second) history := by
  apply completeRun_exists_of_root_deferred_coverage (paths := fun _ => []) (bound := 3)
    (roles := fun ref => ref == 2) (ancestry := fun _ => []) (refBound := 3) (base := [])
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [Ancestry.Valid]
  · simp [work, MixedRefs.WorkAt, Ancestry.FragmentAt, node]
  · simp [work, RefRoles.WorkRoles, node]
  · simp [work, ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder, node]
  · simpa [work, ExecutionErrors.WorkPositive, ExecutionErrors.ItemsPositive]
      using And.intro firstPositive secondPositive
  · simp [work, GeneralScheduling.streamAllocationRefs, node]
  · exact initialized first second
  · exact fun _ _ _ _ known => (deferred_task known).1
  · intro address owners producer payload known
    simpa [node] using (deferred_task known).2

/-- The two-task construction is observable through an actual conforming source queue constructor.
Witness: complete-history realization, with no supplied history or queue constructor as a premise.
-/
example (response : Response) (first second : Result (List (Name × ResponseValue)))
    (firstPositive : BasicErrors.PositiveFailure first)
    (secondPositive : BasicErrors.PositiveFailure second)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((work first second).size ≠ 0
          → (scheduler (work first second)).Conforms (work first second))
        ∧ (executionFromWork scheduler response (work first second)).Observes observed
            true :=
  (completeObservation_exists_iff _ _).mpr
    (Or.inr (multiple_run_exists first second firstPositive secondPositive))

/-- An empty root stream is initially announced, while a sibling root stream and its
nested descendants are omitted. Covering initialization must add the missing root notice.
-/
def independentStreams (outer middle inner : Result ResponseValue) : Work :=
  .combine (.stream (node 9) []) (NestedStreamExistence.nested outer middle inner)

/-- Nested stream tasks retain ordered producer refs for every fixed outcome, including
raw failures. Witness: structural ref descent; no health, licensing, notice, or publication
premise is supplied. This checks the bound needed when a cancelled producer cannot run.
-/
theorem nested_producer_ref_bound
    (outer middle inner : Result ResponseValue)
    {occurrence owners producer payload ref}
    (known
      : TaskAt (independentStreams outer middle inner) occurrence owners
          (some producer) payload)
    (member : ref ∈ owners)
    : ∃ parentOwners ancestor result parentRef,
        TaskAt (independentStreams outer middle inner) producer parentOwners ancestor
          result
        ∧ parentRef ∈ parentOwners
        ∧ parentRef ≤ ref := by
  apply producer_owner_ref_le_structural (parents := fun _ => []) (bound := 10)
    (known := known) (member := member)
  · simp [Ancestry.Valid]
  · simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      MixedRefs.WorkAt, node]
  · simp [GeneralScheduling.DeferContinuous,
      independentStreams, NestedStreamExistence.nested]
  · simp [GeneralScheduling.StreamOwnersOrdered, independentStreams,
      NestedStreamExistence.nested]

/-- Even an exhausted generated stream has an earlier contributing producer ref.
Witness: structural stream allocation bounds, without assuming that an item exists.
-/
theorem nested_stream_producer_ref_bound
    (outer middle inner : Result ResponseValue)
    {stream dependencies producer}
    (known
      : NodeAt (independentStreams outer middle inner) stream .stream dependencies
          (some producer))
    : ∃ owners ancestor payload ref,
        TaskAt (independentStreams outer middle inner) producer owners ancestor payload
        ∧ ref ∈ owners
        ∧ ref < stream.ref := by
  apply stream_producer_owner_lt (parents := fun _ => []) (bound := 10) (known := known)
  · simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      MixedRefs.WorkAt, node]
  · simp [GeneralScheduling.DeferContinuous,
      independentStreams, NestedStreamExistence.nested]
  · simp [GeneralScheduling.StreamOwnersOrdered, independentStreams,
      NestedStreamExistence.nested]

/-- A cancelled nested stream task is covered using only reports below its chosen bound.
Witness: bounded mutual causal assembly with actual accepted-failure reports; this fixture
has no deferred groups, so the earlier-group premise is empty. Arbitrary admitted histories
and cuts exercise producer cancellation without assuming a complete or terminal run.
-/
theorem nested_cancelled_reported_below_bound
    (outer middle inner : Result ResponseValue)
    (outerPositive : BasicErrors.PositiveFailure outer)
    (middlePositive : BasicErrors.PositiveFailure middle)
    (innerPositive : BasicErrors.PositiveFailure inner)
    {groups streams events matching failures occurrence owners producer payload ref limit}
    (explained
      : Explains (independentStreams outer middle inner) groups streams events
          matching failures)
    (closed
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (cancelled
      : TaskCancelled (independentStreams outer middle inner) matching events
          failures occurrence)
    (known
      : TaskAt (independentStreams outer middle inner) occurrence owners producer payload)
    (member : ref ∈ owners) (bounded : ref < limit)
    : FailureReportedFor events payload.path := by
  have valid : Ancestry.Valid (fun _ => []) 10 := by simp [Ancestry.Valid]
  have coherent : MixedRefs.WorkAt (fun _ => []) 0 10
      (independentStreams outer middle inner) := by
    simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      MixedRefs.WorkAt, node]
  have roles
      : RefRoles.WorkRoles (fun _ => true) (independentStreams outer middle inner) := by
    simp [RefRoles.WorkRoles, independentStreams, NestedStreamExistence.nested]
  have continuous : GeneralScheduling.DeferContinuous (fun _ => [])
      (independentStreams outer middle inner) := by
    simp [GeneralScheduling.DeferContinuous, independentStreams, NestedStreamExistence.nested]
  have ordered : GeneralScheduling.StreamOwnersOrdered (independentStreams outer middle
      inner) := by
    simp [GeneralScheduling.StreamOwnersOrdered, independentStreams,
      NestedStreamExistence.nested]
  have paths : MixedOwnerPaths.WorkAt (fun _ => []) 10
      (independentStreams outer middle inner) := by
    simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      MixedOwnerPaths.WorkAt, OwnerPaths.Assigned, node]
  have under : ExecutionPaths.WorkUnder [] (independentStreams outer middle inner) := by
    simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder, node]
  have positive : ExecutionErrors.WorkPositive (independentStreams outer middle inner) := by
    simpa [independentStreams, NestedStreamExistence.nested, ExecutionErrors.WorkPositive,
      ExecutionErrors.ItemsPositive]
      using ⟨outerPositive, middlePositive, innerPositive⟩
  apply cancelled_reported_of_bounded_owner_task_scopes valid coherent roles continuous
    ordered paths under ?_ ?_ cancelled known member bounded
  · intro address owners producer payload group dependencies birth task descriptor
      contributes earlier failed
    have role := node_ref_role roles descriptor
    change true = false at role
    cases role
  · intro cut task recorded owners birth result descriptor
    exact Explains.accepted_failure_reported valid coherent roles paths positive explained
      closed recorded descriptor

/-- The root-deferred theorem also covers an empty deferred phase with independent nested
streams and positive errors. Witness: enlarge a singleton frontier that initially omits the active
root stream; absent deferred tasks make the deferred-owner premise vacuous.
-/
example (outer middle inner : Result ResponseValue)
    (outerPositive : BasicErrors.PositiveFailure outer)
    (middlePositive : BasicErrors.PositiveFailure middle)
    (innerPositive : BasicErrors.PositiveFailure inner)
    : ∃ history, AdmissibleRun (independentStreams outer middle inner) history := by
  have only : StreamOnly (independentStreams outer middle inner) := by
    simp [StreamOnly, independentStreams, NestedStreamExistence.nested]
  have noDeferred {address owners producer payload}
      (known : TaskAt (independentStreams outer middle inner) (.executionGroup address)
        owners producer payload) : False := by
    obtain ⟨stream, result, _, itemShape, _⟩ := only.task known
    obtain ⟨_, _, _, _, _, _, _, objectShape⟩ := known
    cases objectShape.symm.trans itemShape
  apply completeRun_exists_of_root_deferred_coverage (paths := fun _ => []) (bound := 10)
    (roles := fun _ => true) (groups := []) (streams := [node 9])
    (ancestry := fun _ => []) (refBound := 10) (base := [])
  · simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      MixedOwnerPaths.WorkAt, OwnerPaths.Assigned, node]
  · simp [Ancestry.Valid]
  · simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      MixedRefs.WorkAt, node]
  · simp [independentStreams, NestedStreamExistence.nested, RefRoles.WorkRoles]
  · simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder, node]
  · simpa [independentStreams, NestedStreamExistence.nested, ExecutionErrors.WorkPositive,
      ExecutionErrors.ItemsPositive] using ⟨outerPositive, middlePositive, innerPositive⟩
  · simp [independentStreams, NestedStreamExistence.nested,
      GeneralScheduling.streamAllocationRefs,
      NestedStreamExistence.node, node]
  · refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro stream member
    have same := List.mem_singleton.mp member
    subst stream
    refine ⟨[], none, NodeAt.stream (.left (Located.root (root := independentStreams outer middle inner))), ?_⟩
    exact ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨fun failure => failure.nonempty rfl, Or.inl rfl⟩, by simp, Or.inl rfl⟩
  · exact fun _ _ _ _ known => (noDeferred known).elim
  · exact fun _ _ _ _ known => (noDeferred known).elim

/-- Raw zero-count failures do not satisfy the reporting certificate used by full progress.
Witness: unfold the fixed deferred payload; success outcomes can still have arbitrary
counted errors, but a failed outcome must carry a positive count.
-/
example : ¬ExecutionErrors.WorkPositive (work (.error 0) (.ok ([], 0))) := by
  simp [work, ExecutionErrors.WorkPositive, BasicErrors.PositiveFailure]

#print axioms Explains.cancelled_reported_of_announced_groups
#print axioms finish_released_streams
#print axioms completeRun_exists_of_root_deferred_coverage
#print axioms multiple_run_exists
#print axioms nested_producer_ref_bound
#print axioms nested_stream_producer_ref_bound
#print axioms nested_cancelled_reported_below_bound
#print axioms cancelled_reported_of_bounded_owner_task_scopes

end GraphQL.IncrementalDelivery.Tests.InitialDeferredExistence
