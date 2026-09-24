import Proofs.GraphQL.IncrementalDelivery.Correctness.QuerySourceCoverage

/-! Complete source coverage retains occurrences, both position modes, and batching. -/

namespace GraphQL.IncrementalDelivery.Tests.SourceCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler

/-- Every full successful source inventory is recovered in publication order, even when
different occurrences have identical payloads. No deterministic order is selected.
-/
example {work groups streams events matching failures initial}
    (explained : Explains work groups streams events matching failures)
    (complete
      : ∀ occurrence owners producer payload,
          TaskAt work occurrence owners producer payload
          → Published matching events occurrence)
    : (sourcePrefixTasks (sourceTasks [] none initial work) matching events
        events.length).Perm
        (sourceTasks [] none initial work) :=
  sourcePrefixTasks_perm explained complete

/-- Leaf-only coverage uses exactly the same terminal and batching premises as coverage
with containers. The source positions are not assumed to equal basic execution here.
-/
example {paths bound response work result sourceSlices}
    (observed : WorkObservation response work true result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (positive : ExecutionErrors.WorkPositive work)
    (seeded
      : Semantics.MixedPaths.WorkCursorSeed
          (ResponsePositions.listCursors [] response.data) work sourceSlices)
    (unique
      : (ResponsePositions.value true [] response.data ++ sourceSlices.flatten).Nodup)
    (zero : result.totalErrors = 0)
    : ∃ slices,
        result.DeliversSlices false slices
        ∧ slices.flatten.Perm
            (ResponsePositions.value false [] response.data
              ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                    work).flatMap
                  (SourceTask.positions false)) :=
  observed.source_coverage coherent positive seeded unique zero false

/-- An empty work inventory has no future positions in either mode. -/
example (containers : Bool) (cursors : ResponsePositions.Cursors)
    : (sourceTasks [] none cursors .empty).flatMap (SourceTask.positions containers)
      = [] :=
  rfl

end GraphQL.IncrementalDelivery.Tests.SourceCoverage
