import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialDeferredExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization
import Tests.GraphQL.IncrementalDelivery.DeferredPhase
import Tests.GraphQL.IncrementalDelivery.NestedStreamExistence

/-! Multiple shared deferred tasks admit full runs, including their child notices. -/

namespace GraphQL.IncrementalDelivery.Tests.InitialDeferredExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler
open DeferredPhase

/-- Two root deferred tasks with overlapping owners and a child stream have a complete
run for every outcome pair, including raw zero-count failures. Witness: the finite
deferred phase, a reserved success carrier or causal cancellation, then stream completion.
-/
theorem multiple_run_exists (first second : Result (List (Name × ResponseValue)))
    : ∃ history, AdmissibleRun (work first second) history := by
  apply completeRun_exists_of_root_deferred_coverage (paths := fun _ => []) (bound := 3)
    (roles := fun key => key == 2)
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [work, KeyRoles.WorkRoles, node]
  · exact initialized first second
  · exact fun _ _ _ _ known => (deferred_task known).1
  · intro address owners producer payload known
    simpa [node] using (deferred_task known).2

/-- The two-task construction is observable through an actual conforming source factory.
Witness: complete-history realization, with no supplied history or factory as a premise.
-/
example (response : Response) (first second : Result (List (Name × ResponseValue)))
    : ∃ scheduler : Execution.WorkScheduler,
      ∃ observed : QueryResult,
        scheduler.Conforms (work first second)
        ∧ (executionFromWork scheduler response (work first second)).Observes observed
            true :=
  (completeObservation_exists_iff _ _).mpr (Or.inr (multiple_run_exists first second))

/-- An empty root stream is initially announced, while a sibling root stream and its
nested descendants are omitted. Covering initialization must add the missing root notice.
-/
def independentStreams (outer middle inner : Result ResponseValue) : Work :=
  .append (.stream (node 9) []) (NestedStreamExistence.nested outer middle inner)

/-- The root-deferred theorem also covers an empty deferred phase with independent nested
streams and errors. Witness: enlarge a singleton frontier that initially omits the active
root stream; absent deferred tasks make the deferred-owner premise vacuous.
-/
example (outer middle inner : Result ResponseValue)
    : ∃ history, AdmissibleRun (independentStreams outer middle inner) history := by
  have only : StreamOnly (independentStreams outer middle inner) := by
    simp [StreamOnly, independentStreams, NestedStreamExistence.nested]
  have noDeferred {address owners producer payload}
      (known : TaskAt (independentStreams outer middle inner) (.deferred address)
        owners producer payload) : False := by
    obtain ⟨stream, result, _, itemShape, _⟩ := only.task known
    obtain ⟨_, _, _, _, _, _, _, objectShape⟩ := known
    cases objectShape.symm.trans itemShape
  apply completeRun_exists_of_root_deferred_coverage (paths := fun _ => []) (bound := 10)
    (roles := fun _ => true) (groups := []) (streams := [node 9])
  · simp [independentStreams, NestedStreamExistence.nested, NestedStreamExistence.node,
      MixedOwnerPaths.WorkAt, OwnerPaths.Assigned, node]
  · simp [independentStreams, NestedStreamExistence.nested, KeyRoles.WorkRoles]
  · refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro stream member
    have same := List.mem_singleton.mp member
    subst stream
    refine ⟨[], none, NodeAt.stream (.left .root), ?_⟩
    exact ⟨by simp [announcedKeys, pendingKeys], fun failure => failure.nonempty rfl,
      Or.inl rfl, by simp, Or.inl rfl⟩
  · exact fun _ _ _ _ known => (noDeferred known).elim
  · exact fun _ _ _ _ known => (noDeferred known).elim

end GraphQL.IncrementalDelivery.Tests.InitialDeferredExistence
