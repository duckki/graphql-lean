import Proofs.GraphQL.IncrementalDelivery.Correctness.PublicationCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling

/-! Publication multiplicity and payload-count regressions under arbitrary witnesses. -/

namespace GraphQL.IncrementalDelivery.Tests.PublicationCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler

/-- Two owners cannot independently publish their shared task. This rejects every
matching and failure witness, not only the fixture's constant matching function.
-/
example (matching : PublicationMatching) (failures : FailureCuts)
    : ¬Explains HistoryScheduling.shared [HistoryScheduling.left, HistoryScheduling.right]
        []
        [
          HistoryScheduling.value HistoryScheduling.left,
          HistoryScheduling.value HistoryScheduling.right
        ]
        matching failures := by
  intro explained
  have first : Published matching [HistoryScheduling.value HistoryScheduling.left,
      HistoryScheduling.value HistoryScheduling.right] (matching 0) :=
    ⟨0, _, rfl, trivial, rfl⟩
  have second : Published matching [HistoryScheduling.value HistoryScheduling.left,
      HistoryScheduling.value HistoryScheduling.right] (matching 1) :=
    ⟨1, _, rfl, trivial, rfl⟩
  obtain ⟨_, _, _, firstTask, _⟩ := explained.published_task first
  obtain ⟨_, _, _, secondTask, _⟩ := explained.published_task second
  have equal := (HistoryScheduling.task_shared firstTask).trans
    (HistoryScheduling.task_shared secondTask).symm
  have impossible : 0 = 1 :=
    explained.publication_unique rfl trivial rfl trivial equal
  omega

/-- Caught errors are still conserved even if no failure-completion event occurs. -/
example
    : (replayResponse { data := .object [], errors := 2 } [HistoryScheduling.left] []
        [
          [[.groupValues HistoryScheduling.left
              [{ path := [], data := [], errors := 3 }]]],
          [[.groupSuccess HistoryScheduling.left [] [], .workQueueTermination]]
        ]).totalErrors
      = 5 := by
  rw [replayResponse_errors]
  rfl

/-- Grouping equal-valued streamed items keeps both error contributions. -/
example
    : workEventErrors
        (.streamValues HistoryScheduling.stream
          [{ item := .null, errors := 2 }, { item := .null, errors := 3 }] [] [])
      = 5 :=
  rfl

/-- Permissive raw work may reuse keys at incompatible paths, but cannot pass the
generated-work metadata certificate. The scheduler contract remains unchanged.
-/
example (paths : Semantics.OwnerPaths.Assignment) (bound : Nat)
    : ¬Semantics.MixedOwnerPaths.WorkAt paths bound
        HistoryScheduling.Lookup.repeated := by
  intro coherent
  have root : NodeAt HistoryScheduling.Lookup.repeated
      HistoryScheduling.Lookup.rootNode .group [] none :=
    .group (group := { node := HistoryScheduling.Lookup.rootNode }) (.left .root) (by simp)
  have nested : NodeAt HistoryScheduling.Lookup.repeated
      HistoryScheduling.Lookup.nestedNode .stream [1] (some (.executionGroup [1])) :=
    .stream (.executionGroup (.right .root))
  have impossible := workAt_same_path coherent root nested rfl
  cases impossible

end GraphQL.IncrementalDelivery.Tests.PublicationCoverage
