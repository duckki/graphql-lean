import Tests.GraphQL.IncrementalDelivery.MixedNoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Nonblocking

/-! Supported-prefix progress retains existing observations, even without full coverage. -/

namespace GraphQL.IncrementalDelivery.Tests.SupportedContinuation
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler Ancestry GeneralScheduling MixedNoticeCoverage

/-- The shared-owner publication has a terminal continuation retaining its batches.
Witness: generated-style metadata and supported coverage, despite the eligible child
stream having no notice yet. No initial output or batch is regenerated.
-/
theorem continuation {batches} (batched : WorkBatching [value] batches)
    : (History.mk [node 0] [] batches).CanFinish work := by
  apply mixed_supported_continuation (ancestry := ancestry) (bound := 3)
    (roles := fun key => key == 2) (paths := fun _ => []) (pathBound := 3)
    (explained := published)
  · intro key bounded parent member
    by_cases one : key = 1
    · simp [ancestry, one] at member
      subst parent
      simp [one, ancestry, List.Subset]
    · simp [ancestry, one] at member
  · simp [work, MixedKeys.WorkAt, FragmentAt, node, ancestry]
  · simp [work, KeyRoles.WorkRoles, node]
  · simp [work, DeferContinuous, DeferUnder, node]
  · simp [work, StreamOwnersOrdered, OwnersBefore, node]
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simpa [node] using published_supported
  · exact batched

/-- The supported prefix belongs to a conforming nonblocking source with the same
initial notices. Witness: continuation proves viability; prefix closure initializes it.
-/
example
    : (viableSource work [node 0] []).Conforms work
      ∧ (viableSource work [node 0] []).Nonblocking
      ∧ (viableSource work [node 0] []).workEventStream.admissible [[value]] := by
  have viable := continuation (WorkBatching.singletons [value])
  refine ⟨viableSource_conforms ?_, viableSource_nonblocking _ _ _, viable⟩
  exact History.CanFinish.prefix (before := []) (after := [[value]]) viable

end GraphQL.IncrementalDelivery.Tests.SupportedContinuation
