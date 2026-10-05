import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredStreamExistence
import Tests.GraphQL.IncrementalDelivery.NestedStreamExistence

/-! A real group-success carrier releases nested streams; failures cancel descendants. -/

namespace GraphQL.IncrementalDelivery.Tests.DeferredStreamExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

/-- A defer ref distinct from the four stream refs in the nested-stream fixture. -/
def parent : DeliveryNode := { ref := 4, path := [] }

/-- One deferred task produces three stream levels and an empty sibling stream.
The raw fixture permits every combination of producer and item outcomes.
-/
def mixed (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    : Work :=
  .executionGroup [{ node := parent }] [] result
    (NestedStreamExistence.nested outer middle inner)

/-- Local mixed fixture outcomes with positive failures have a complete run.
Witness: actual root or stream error reports cover cancelled descendants; successful
deferred release reserves a real group carrier for the produced streams.
-/
theorem mixed_run_exists (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    (resultPositive : BasicErrors.PositiveFailure result)
    (outerPositive : BasicErrors.PositiveFailure outer)
    (middlePositive : BasicErrors.PositiveFailure middle)
    (innerPositive : BasicErrors.PositiveFailure inner)
    : ∃ history, AdmissibleRun (mixed result outer middle inner) history := by
  apply deferredStreams_completeRun_exists (paths := fun _ => []) (bound := 5)
    (roles := fun ref => ref != 4)
  · simp [StreamOnly, NestedStreamExistence.nested]
  · simp [MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, parent,
      NestedStreamExistence.nested, NestedStreamExistence.node]
  · simp [RefRoles.WorkRoles, parent, NestedStreamExistence.nested,
      NestedStreamExistence.node]
  · simp [ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder,
      NestedStreamExistence.nested, NestedStreamExistence.node]
  · simp [ExecutionErrors.WorkPositive, ExecutionErrors.ItemsPositive, resultPositive,
      outerPositive, middlePositive, innerPositive, NestedStreamExistence.nested]

/-- Another owner of the same deferred field selection, distinct from every stream ref. -/
def coOwner : DeliveryNode := { ref := 5, path := [] }

/-- Shared ownership repeats one descriptor to check that it never licenses repeat closure.
The producer still has just one task occurrence, independently of owner count.
-/
def shared (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    : Work :=
  .executionGroup ([parent, coOwner, parent].map (fun node => { node })) [] result
    (NestedStreamExistence.nested outer middle inner)

/-- Every shared-producer outcome admits a run completing both original IDs exactly once.
Witness: covering initialization retained by the shared existence theorem and the general
terminal-history lifecycle theorem; repeated owner descriptors do not multiply completions.
-/
theorem shared_run_completes_owners (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    (resultPositive : BasicErrors.PositiveFailure result)
    (outerPositive : BasicErrors.PositiveFailure outer)
    (middlePositive : BasicErrors.PositiveFailure middle)
    (innerPositive : BasicErrors.PositiveFailure inner)
    : ∃ history,
        AdmissibleRun (shared result outer middle inner) history
        ∧ (completedRefs history.batches.flatten).count 4 = 1
        ∧ (completedRefs history.batches.flatten).count 5 = 1 := by
  have onlyStreams : StreamOnly (NestedStreamExistence.nested outer middle inner) := by
    simp [StreamOnly, NestedStreamExistence.nested]
  have coherent : MixedOwnerPaths.WorkAt (fun _ => []) 6
      (shared result outer middle inner) := by
    simp [shared, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, parent, coOwner,
      NestedStreamExistence.nested, NestedStreamExistence.node]
  have roles : RefRoles.WorkRoles (fun ref => decide (ref < 4))
      (shared result outer middle inner) := by
    simp [shared, RefRoles.WorkRoles, parent, coOwner, NestedStreamExistence.nested,
      NestedStreamExistence.node]
  obtain ⟨history, run, notified⟩ := sharedDeferredStreams_completeRun_with_owners
    (nodes := [parent, coOwner, parent]) (by simp) onlyStreams coherent roles
    (by simp [ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder,
      NestedStreamExistence.nested, NestedStreamExistence.node])
    (by simp [ExecutionErrors.WorkPositive, ExecutionErrors.ItemsPositive, resultPositive,
      outerPositive, middlePositive, innerPositive, NestedStreamExistence.nested])
  refine ⟨history, run, ?_, ?_⟩
  · exact run.refsCompleteExactlyOnce 4
      (List.mem_append_left _ (notified parent (by simp)))
  · exact run.refsCompleteExactlyOnce 5
      (List.mem_append_left _ (notified coOwner (by simp)))

/-- Shared work realizes a complete response stream even when a nested item fails.
Witness: construct its raw terminal history, then apply the general realization bridge.
-/
example (response : Response) (result : Result (List (Name × ResponseValue)))
    (positive : BasicErrors.PositiveFailure result)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((shared result (.ok (.null, 0)) (.error 1) (.ok (.null, 0))).size ≠ 0
          → (scheduler
              (shared result (.ok (.null, 0)) (.error 1) (.ok (.null, 0)))).Conforms
              (shared result (.ok (.null, 0)) (.error 1) (.ok (.null, 0))))
        ∧ (executionFromWork scheduler response
            (shared result (.ok (.null, 0)) (.error 1) (.ok (.null, 0)))).Observes
            observed true := by
  obtain ⟨history, run, _, _⟩ := shared_run_completes_owners result
    (.ok (.null, 0)) (.error 1) (.ok (.null, 0)) positive
    (by simp [BasicErrors.PositiveFailure]) (by simp [BasicErrors.PositiveFailure])
    (by simp [BasicErrors.PositiveFailure])
  exact (completeObservation_exists_iff _ _).mpr (Or.inr ⟨history, run⟩)

/-- Publishing the deferred value alone does not release its child stream. Witness:
the parent's announced but uncompleted ref fails the dependency rule. A later group-success
carrier, rather than the object publication, must introduce the stream notice.
-/
example (data : List (Name × ResponseValue)) (outer middle inner : Result ResponseValue)
    : ¬CanAnnounce (mixed (.ok (data, 0)) outer middle inner) [4]
        (fun _ => .executionGroup []) [.groupValues parent [{ path := [], data }]] []
        (NestedStreamExistence.node 0) .stream [4] (some (.executionGroup [])) := by
  intro eligible
  have dependencies := eligible.2.2.2
  simp [DependencySatisfied, announcedRefs, pendingRefs, completedRefs, eventPending,
    eventCompleted] at dependencies
  exact dependencies.2 none
    ⟨parent, .group, [], NodeAt.group (group := { node := parent }) .root (by simp), rfl⟩

/-- The constructed mixed run realizes complete wire observations without supplied history
or scheduler evidence. Witness: general realization of the independently constructed run.
-/
example (response : Response) (result : Result (List (Name × ResponseValue)))
    (positive : BasicErrors.PositiveFailure result)
    : ∃ scheduler : (Execution.Work → Execution.WorkQueue),
      ∃ observed : ExecutionObservation,
        ((mixed result (.ok (.null, 0)) (.error 1) (.ok (.null, 0))).size ≠ 0
          → (scheduler
              (mixed result (.ok (.null, 0)) (.error 1) (.ok (.null, 0)))).Conforms
              (mixed result (.ok (.null, 0)) (.error 1) (.ok (.null, 0))))
        ∧ (executionFromWork scheduler response
            (mixed result (.ok (.null, 0)) (.error 1) (.ok (.null, 0)))).Observes
            observed true :=
  (completeObservation_exists_iff _ _).mpr
    (Or.inr
      (mixed_run_exists _ _ _ _ positive
        (by simp [BasicErrors.PositiveFailure]) (by simp [BasicErrors.PositiveFailure])
        (by simp [BasicErrors.PositiveFailure])))

/-- A released-stream continuation preserves even nontrivial supplied response grouping.
Witness: the batching extension theorem, which appends rather than replacing old batches.
-/
example {paths bound work groups streams events matching failures batches}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder [] work)
    (positive : ExecutionErrors.WorkPositive work)
    (healthyGroups
      : ∀ outputs next cuts,
          Explains work groups streams outputs next cuts
          → ∀ node dependencies birth,
              NodeAt work node .group dependencies birth
              → ¬NodeFailed work next outputs cuts node.ref)
    (explained : Explains work groups streams events matching failures)
    (deferred : DeferredTasksAccounted work matching events failures)
    (closed : StreamDependenciesCompleted work events)
    (notified
      : StreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (batched : WorkBatching events batches)
    : ∃ tail : List WorkQueueEvent,
        AdmissibleRun work
          ⟨
            groups,
            streams,
            batches ++ tail.map (fun event => [event]) ++ [[.workQueueTermination]]
          ⟩ :=
  released_streams_run_extension_of_healthy_groups coherent under positive healthyGroups
    explained deferred closed notified batched

/-- The producer's positive failure reports unannounced streams at deeper attachments.
Witness: the root report covers user and all local descendants; they need no separate ID.
-/
example
    : ∃ history,
        AdmissibleRun
          (.executionGroup [{ node := { ref := 0, path := [] } }]
            [.field "user"] (.error 1)
            (.stream { ref := 1, path := [.field "user", .field "items"] }
              [(.ok (.null, 0), .empty)])) history := by
  apply deferredStreams_completeRun_exists
    (paths := fun ref => if ref = 0 then [] else [.field "user", .field "items"])
    (bound := 2) (roles := fun ref => ref != 0)
  · simp [StreamOnly]
  · simp [MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below]
  · simp [RefRoles.WorkRoles]
  · simp [ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder]
  · simp [ExecutionErrors.WorkPositive, ExecutionErrors.ItemsPositive,
      BasicErrors.PositiveFailure]

/-- Zero-count raw producer failures cannot provide the required positive report.
Witness: the generated-work positivity certificate rejects this raw outcome.
-/
example
    : ¬ExecutionErrors.WorkPositive
        (mixed (.error 0) (.ok (.null, 0)) (.ok (.null, 0)) (.ok (.null, 0))) := by
  simp [mixed, ExecutionErrors.WorkPositive, BasicErrors.PositiveFailure]

#print axioms sharedDeferredStreams_success_groups_healthy
#print axioms Explains.cancelled_reported_of_healthy_groups
#print axioms released_streams_run_extension_of_healthy_groups
#print axioms sharedDeferredStreams_completeRun_with_owners

end GraphQL.IncrementalDelivery.Tests.DeferredStreamExistence
