import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTaskProvenance
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling

/-! Ordered stream publication and absolute source-index regressions. -/

namespace GraphQL.IncrementalDelivery.Tests.PublicationOrder
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler

/-- Equal-valued items cannot be observed in reversed occurrence order, for any matching
or failure witness; use the general history-order theorem rather than payload inequality.
-/
example (matching : PublicationMatching) (failures : FailureCuts)
    (first : matching 0 = .item [] 1) (second : matching 1 = .item [] 0)
    : ¬Explains HistoryScheduling.items [] [HistoryScheduling.stream]
        [HistoryScheduling.itemValue, HistoryScheduling.itemValue] matching failures := by
  intro explained
  have order := explained.item_order (left := 0) (right := 1) rfl trivial first
    rfl trivial second
  have impossible := order.mp (by decide)
  omega

/-- Structural item ordinals start at zero while absolute response positions continue
from the initial list length. The proof projection does not choose an output history.
-/
example
    : (sourceTasks [] none [(HistoryScheduling.stream.path, 7)]
        HistoryScheduling.items).map
        (fun task => (task.occurrence, task.index))
      = [(.item [] 0, 7), (.item [] 1, 8)] := by
  rfl

/-- Two equal null values at consecutive stream positions introduce disjoint source paths.
-/
example
    : ((sourceTasks [] none [(HistoryScheduling.stream.path, 7)]
          HistoryScheduling.items).flatMap
        (SourceTask.positions true)).Nodup := by
  decide

/-- Task lookup retains the original payload while recovering its absolute index. -/
example
    : ∃ task ∈
        sourceTasks [] none [(HistoryScheduling.stream.path, 7)] HistoryScheduling.items,
        task.occurrence = .item [] 1
        ∧ task.producer = none
        ∧ task.payload = .item HistoryScheduling.stream (.ok (.null, 0)) :=
  sourceTasks_task (TaskAt.item .root rfl) _

end GraphQL.IncrementalDelivery.Tests.PublicationOrder
