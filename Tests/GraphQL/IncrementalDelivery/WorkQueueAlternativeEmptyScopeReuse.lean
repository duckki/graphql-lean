import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EmptyScopeReuse

/-! Completed-item reuse preserves actual value/error/occurrence/child-work projections.
An intentionally retained empty-array view demonstrates why work must be omitted.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.EmptyScopeReuseTests

example : EmptySequentialScopeOptimization := EmptySequentialScopeOptimization_holds

private def emptyItem (index : Nat) : CompletedItemScope :=
  { item := { occurrence := .item [0] index, value := { item := .scalar "value" } } }

private def childStream : Execution.DeliveryNode := { ref := 9, path := [.index 0] }

private def childWork : ReferenceWorkQueue.Work :=
  ReferenceWorkQueue.Work.fromExecution (.stream childStream []) [0, 1]

private def childItem : CompletedItemScope :=
  {
    item :=
      { occurrence := .item [0] 1, value := { item := .object [] }, work := childWork }
  }

private def errorItem : CompletedItemScope :=
  { item := { occurrence := .item [0] 2, value := { item := .null, errors := 3 } } }

example (scopes : List CompletedItemScope)
    : (runSequentialScopes false scopes).results.map ScopedItemResult.project
      = scopes.map CompletedItemScope.item :=
  runSequentialScopes_projection false scopes

example (cursor : ResponseStreamCursor) (stream : Execution.DeliveryNode)
    (scopes : List CompletedItemScope)
    : cursor.handleBatch
        [.streamItems stream
          ((runSequentialScopes false scopes).results.map ScopedItemResult.project)]
      = cursor.handleBatch [.streamItems stream (scopes.map CompletedItemScope.item)] :=
  runSequentialScopes_reader cursor stream scopes

example : (emptyItem 0).buildResult.work = none := rfl

example
    : (runSequentialScopes false [emptyItem 0, emptyItem 1, emptyItem 2]).allocations
      = 1 :=
  rfl

-- A child stream boundary is work even if its finite remaining item list is empty.
example : childItem.canReuse = false := rfl

example : childItem.buildResult.project = childItem.item :=
  childItem.buildResult_project

example : errorItem.canReuse = false := rfl

example
    : errorItem.buildResult.value.errors = 3 ∧ errorItem.buildResult.work = some {} := by
  constructor <;> rfl

-- The previous empty scope may serve the nonempty/error item; that item then ends reuse.
example
    : (runSequentialScopes false [emptyItem 0, childItem, emptyItem 2]).allocations = 2 :=
  rfl

example
    : (runSequentialScopes false [emptyItem 0, errorItem, emptyItem 3]).allocations = 2 :=
  rfl

example
    : (runSequentialScopes false [childItem, errorItem, emptyItem 3]).allocations = 3 :=
  rfl

example : ({ emptyItem 0 with aborted := true } : CompletedItemScope).canReuse = false :=
  rfl

-- No groups or streams does not imply no work: task-only inventories also end reuse.
example
    : ({
          item :=
            {
              (emptyItem 0).item with
                work :=
                  ReferenceWorkQueue.Work.fromExecution
                    (.executionGroup [] [] (.ok ([], 0)) .empty)
            }
        }
        : CompletedItemScope).canReuse
      = false :=
  rfl

example (before after : Nat → ReferenceWorkQueue.Work)
    : (emptyItem 0).buildResult.work = none
      ∧ (emptyItem 0).buildResult.value.errors = 0
      ∧ (emptyItem 0).buildResult.occurrence = (emptyItem 0).item.occurrence
      ∧ ((emptyItem 0).buildResult.workView 0).read before = (emptyItem 0).item.work
      ∧ ((emptyItem 0).buildResult.workView 0).read after = (emptyItem 0).item.work :=
  (emptyItem 0).empty_result_noninterference rfl 0 before after

-- A naïve fast path that exposed its empty arrays would change an earlier result later.
private def beforeReuse (_ : Nat) : ReferenceWorkQueue.Work := {}
private def afterReuse (_ : Nat) : ReferenceWorkQueue.Work := childWork

example : (ScopeWorkView.retained 0).read beforeReuse = ({} : ReferenceWorkQueue.Work) :=
  rfl

example
    : (ScopeWorkView.retained 0).read beforeReuse
      ≠ (ScopeWorkView.retained 0).read afterReuse := by
  intro changed
  have lengths := congrArg (fun work => work.streams.length) changed
  contradiction

example
    : ((emptyItem 0).buildResult.workView 0).read beforeReuse
      = ((emptyItem 0).buildResult.workView 0).read afterReuse :=
  rfl

#print axioms EmptySequentialScopeOptimization_holds
#print axioms runSequentialScopes_empty_allocations
#print axioms runSequentialScopes_reader
#print axioms CompletedItemScope.canReuse_inventory
#print axioms CompletedItemScope.empty_result_noninterference

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.EmptyScopeReuseTests
