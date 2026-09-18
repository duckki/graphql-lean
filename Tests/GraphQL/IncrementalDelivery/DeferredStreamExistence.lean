import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredStreamExistence
import Tests.GraphQL.IncrementalDelivery.NestedStreamExistence

/-! A real group-success carrier releases nested streams; failures cancel descendants. -/

namespace GraphQL.IncrementalDelivery.Tests.DeferredStreamExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- A defer key distinct from the four stream keys in the nested-stream fixture. -/
def parent : DeliveryNode := { key := 4, path := [] }

/-- One deferred task produces three stream levels and an empty sibling stream.
The raw fixture permits every combination of producer and item outcomes.
-/
def mixed (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    : Work :=
  .deferred [{ node := parent }] [] result
    (NestedStreamExistence.nested outer middle inner)

/-- Every combination of mixed fixture outcomes has a complete run, including zero-count
raw failures. Witness: deferred release or cancellation followed by stream continuation.
-/
theorem mixed_run_exists (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    : ∃ history, AdmissibleRun (mixed result outer middle inner) history := by
  apply deferredStreams_completeRun_exists (paths := fun _ => []) (bound := 5)
    (roles := fun key => key != 4)
  · simp [StreamOnly, NestedStreamExistence.nested]
  · simp [MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, parent,
      NestedStreamExistence.nested, NestedStreamExistence.node]
  · simp [KeyRoles.WorkRoles, parent, NestedStreamExistence.nested,
      NestedStreamExistence.node]

/-- Another owner of the same deferred field selection, distinct from every stream key. -/
def coOwner : DeliveryNode := { key := 5, path := [] }

/-- Shared ownership repeats one descriptor to check that it never licenses repeat closure.
The producer still has just one task occurrence, independently of owner count.
-/
def shared (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    : Work :=
  .deferred ([parent, coOwner, parent].map (fun node => { node })) [] result
    (NestedStreamExistence.nested outer middle inner)

/-- Every shared-producer outcome admits a run completing both original IDs exactly once.
Witness: covering initialization retained by the shared existence theorem and the general
terminal-history lifecycle theorem; repeated owner descriptors do not multiply completions.
-/
theorem shared_run_completes_owners (result : Result (List (Name × ResponseValue)))
    (outer middle inner : Result ResponseValue)
    : ∃ history,
        AdmissibleRun (shared result outer middle inner) history
        ∧ (completedKeys history.batches.flatten).count 4 = 1
        ∧ (completedKeys history.batches.flatten).count 5 = 1 := by
  have onlyStreams : StreamOnly (NestedStreamExistence.nested outer middle inner) := by
    simp [StreamOnly, NestedStreamExistence.nested]
  have coherent : MixedOwnerPaths.WorkAt (fun _ => []) 6
      (shared result outer middle inner) := by
    simp [shared, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, parent, coOwner,
      NestedStreamExistence.nested, NestedStreamExistence.node]
  have roles : KeyRoles.WorkRoles (fun key => decide (key < 4))
      (shared result outer middle inner) := by
    simp [shared, KeyRoles.WorkRoles, parent, coOwner, NestedStreamExistence.nested,
      NestedStreamExistence.node]
  obtain ⟨history, run, notified⟩ := sharedDeferredStreams_completeRun_with_owners
    (nodes := [parent, coOwner, parent]) (by simp) onlyStreams coherent roles
  refine ⟨history, run, ?_, ?_⟩
  · exact run.keysCompleteExactlyOnce 4
      (List.mem_append_left _ (notified parent (by simp)))
  · exact run.keysCompleteExactlyOnce 5
      (List.mem_append_left _ (notified coOwner (by simp)))

/-- Shared work realizes a complete response stream even when a nested item fails.
Witness: construct its raw terminal history, then apply the general realization bridge.
-/
example (response : Response) (result : Result (List (Name × ResponseValue)))
    : ∃ scheduler : Execution.WorkScheduler,
      ∃ observed : QueryResult,
        scheduler.Conforms (shared result (.ok (.null, 0)) (.error 0) (.ok (.null, 0)))
        ∧ (executionFromWork scheduler response
            (shared result (.ok (.null, 0)) (.error 0) (.ok (.null, 0)))).Observes
            observed true := by
  obtain ⟨history, run, _, _⟩ := shared_run_completes_owners result
    (.ok (.null, 0)) (.error 0) (.ok (.null, 0))
  exact (completeObservation_exists_iff _ _).mpr (Or.inr ⟨history, run⟩)

/-- Publishing the deferred value alone does not release its child stream. Witness:
the parent's announced but uncompleted key fails the dependency rule. A later group-success
carrier, rather than the object publication, must introduce the stream notice.
-/
example (data : List (Name × ResponseValue)) (outer middle inner : Result ResponseValue)
    : ¬CanAnnounce (mixed (.ok (data, 0)) outer middle inner) [4]
        (fun _ => .deferred []) [.groupValues parent [{ path := [], data }]] []
        (NestedStreamExistence.node 0) .stream [4] (some (.deferred [])) := by
  intro eligible
  have dependencies := eligible.2.2.2.2
  simp [DependencySatisfied, announcedKeys, pendingKeys, completedKeys, eventPending,
    eventCompleted] at dependencies
  exact dependencies.2 none
    ⟨parent, .group, [], NodeAt.group (group := { node := parent }) .root (by simp), rfl⟩

/-- The constructed mixed run realizes complete wire observations without supplied history
or scheduler evidence. Witness: general realization of the independently constructed run.
-/
example (response : Response) (result : Result (List (Name × ResponseValue)))
    : ∃ scheduler : Execution.WorkScheduler,
      ∃ observed : QueryResult,
        scheduler.Conforms (mixed result (.ok (.null, 0)) (.error 0) (.ok (.null, 0)))
        ∧ (executionFromWork scheduler response
            (mixed result (.ok (.null, 0)) (.error 0) (.ok (.null, 0)))).Observes
            observed true :=
  (completeObservation_exists_iff _ _).mpr (Or.inr (mixed_run_exists _ _ _ _))

/-- A released-stream continuation preserves even nontrivial supplied response grouping.
Witness: the batching extension theorem, which appends rather than replacing old batches.
-/
example {paths bound work groups streams events matching failures batches}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (deferred : DeferredTasksAccounted work matching events (failures.map Prod.snd))
    (closed : StreamParentsCompleted work events)
    (notified
      : StreamsNotified work ((groups ++ streams).map DeliveryNode.key)
          matching events (failures.map Prod.snd))
    (batched : WorkBatching events batches)
    : ∃ tail : List WorkEvent,
        AdmissibleRun work
          ⟨
            groups,
            streams,
            batches ++ tail.map (fun event => [event]) ++ [[.workQueueTermination]]
          ⟩ :=
  released_streams_run_extension coherent explained deferred closed notified batched

end GraphQL.IncrementalDelivery.Tests.DeferredStreamExistence
