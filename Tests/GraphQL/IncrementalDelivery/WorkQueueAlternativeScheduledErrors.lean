import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ExecutionSiblingPlans
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Error policy regressions: cancellation, late settlement, earlier nullable errors,
zero-count fatal status and unchanged eager completion wrappers.
-/

namespace AlternativeScheduledErrorChecks

open GraphQL.IncrementalDelivery
open AlternativeWorkQueue.NativeRefinement.ScheduledErrors

private def first : Sibling String := ⟨0, .error 1⟩
private def second : Sibling String := ⟨1, .error 1⟩
private def plan : List (Sibling String) := [first, second]
private def initial : Scope String := { pending := plan }
private def started := (initial.start first.id).start second.id
private def firstSettled := started.settle [] first [second]
private def allSettled := firstSettled.settle [] second []
private def cut := firstSettled.cancel [] second []

private theorem both_started : History plan started := by
  have one : History plan (initial.start first.id) :=
    .start .initial first (by simp [plan]) rfl (by simp)
  exact .start one second (by simp [Scope.start, initial, plan]) rfl (by decide)

private theorem first_settled : History plan firstSettled :=
  .settle both_started [] [second] first rfl (by decide)

private theorem late_settled : History plan allSettled :=
  .settle first_settled [] [] second rfl (by decide)

private theorem cancelled : History plan cut :=
  .cancel first_settled [] [] second rfl rfl

-- The same fixed sibling plan permits different counts, with exactly explained cuts.
example : countedErrors (eager plan) = 2 := rfl
example : cut.observe plan = some (.error 1) := rfl
example : allSettled.observe plan = some (.error 2) := rfl
example : History plan allSettled := late_settled
example : History plan cut := cancelled
example : cut.actions = [.start 0, .start 1, .settle 0, .cancel 1] := rfl
example : allSettled.actions = [.start 0, .start 1, .settle 0, .settle 1] := rfl

example : cut.reportedErrors + errorTotal cut.cancelled = countedErrors (eager plan) :=
  cancelled.error_accounting

example : allSettled.reportedErrors = countedErrors (eager plan) :=
  late_settled.error_accounting

-- Propagation repeats no originating error and cannot erase a late recorded error.
example : History plan allSettled.bubble := .bubble late_settled rfl
example : allSettled.reportedErrors = 2 := rfl

example : ¬History plan (firstSettled.start second.id) := by
  intro history
  have unique := history.starts_unique
  exact (by decide : ¬(firstSettled.start second.id).started.Nodup) unique

private def nullable : Sibling String := ⟨2, .ok ("null", 1)⟩
private def prefixedPlan := [nullable, first, second]
private def prefixedStart : Scope String := { pending := prefixedPlan }
private def nullableStarted := prefixedStart.start nullable.id
private def nullableSettled := nullableStarted.settle [] nullable [first, second]
private def fatalStarted := nullableSettled.start first.id
private def fatalSettled := fatalStarted.settle [] first [second]
private def prefixedCut := fatalSettled.cancel [] second []

private theorem nullable_history : History prefixedPlan nullableSettled := by
  have start : History prefixedPlan nullableStarted :=
    .start .initial nullable (by simp [prefixedPlan]) rfl (by simp)
  exact .settle start [] [first, second] nullable rfl (by decide)

private theorem prefixed_cut : History prefixedPlan prefixedCut := by
  have start : History prefixedPlan fatalStarted :=
    .start nullable_history first (by simp [nullableSettled, Scope.settle]) rfl (by decide)
  have settled : History prefixedPlan fatalSettled :=
    .settle start [] [second] first rfl (by decide)
  exact .cancel settled [] [] second rfl rfl

-- Cancellation can explain 3 -> 2 here, but not 3 -> 1: nullable's error was recorded.
example : countedErrors (eager prefixedPlan) = 3 := rfl
example : prefixedCut.observe prefixedPlan = some (.error 2) := rfl
example : prefixedCut.reportedErrors ≠ 1 := by decide

example
    : prefixedCut.reportedErrors + errorTotal prefixedCut.cancelled
      = countedErrors (eager prefixedPlan) :=
  prefixed_cut.error_accounting

private def nullablePlan : List (Sibling String) := [nullable, ⟨3, .ok ("null", 2)⟩]

private def nullableFirst : Scope String :=
  (({ pending := nullablePlan } : Scope String).start 3).settle [nullable]
    ⟨3, .ok ("null", 2)⟩ []

private def nullableComplete := (nullableFirst.start nullable.id).settle [] nullable []

private theorem nullable_complete : History nullablePlan nullableComplete := by
  have start : History nullablePlan (({ pending := nullablePlan } : Scope String).start 3) :=
    .start .initial ⟨3, .ok ("null", 2)⟩ (by simp [nullablePlan]) rfl (by simp)
  have settled : History nullablePlan nullableFirst :=
    .settle start [nullable] [] ⟨3, .ok ("null", 2)⟩ rfl (by decide)
  have next : History nullablePlan (nullableFirst.start nullable.id) :=
    .start settled nullable (by simp [nullableFirst, Scope.settle]) rfl (by decide)
  exact .settle next [] [] nullable rfl (by decide)

-- Nonfatal/nullable siblings all aggregate, even when they settle in reverse order.
example : nullableComplete.observe nullablePlan = some (eager nullablePlan) :=
  nullable_complete.complete_nonfatal_agrees
    (by intro sibling member; simp [nullablePlan, nullable] at member
        rcases member with same | same <;> subst sibling <;> rfl) rfl

example : nullableComplete.observe nullablePlan = some (.ok (["null", "null"], 3)) := rfl

private def zeroFatal : Sibling String := ⟨4, .error 0⟩
private def zeroPlan := [zeroFatal, nullable]

private def zeroSettled : Scope String :=
  (({ pending := zeroPlan } : Scope String).start zeroFatal.id).settle [] zeroFatal
    [nullable]

private def zeroCut := zeroSettled.cancel [] nullable []

private theorem zero_cut : History zeroPlan zeroCut := by
  have start : History zeroPlan (({ pending := zeroPlan } : Scope String).start zeroFatal.id) :=
    .start .initial zeroFatal (by simp [zeroPlan]) rfl (by simp)
  have settled : History zeroPlan zeroSettled :=
    .settle start [] [nullable] zeroFatal rfl (by decide)
  exact .cancel settled [] [] nullable rfl rfl

-- Zero reported errors alone do not imply successful completion or forbid cancellation.
example : History zeroPlan zeroCut := zero_cut
example : zeroCut.observe zeroPlan = some (.error 0) := rfl
example : zeroCut.fatal = true := rfl

-- The generic root observes this same completed schedule and explains its count gap.
example
    : ∃ observed,
        cut.observe plan = some observed
        ∧ SameData observed (eager plan)
        ∧ countedErrors observed = cut.reportedErrors
        ∧ countedErrors observed + errorTotal cut.cancelled
          = countedErrors (eager plan) :=
  cancelled.complete_observation rfl

-----------------------------------------------------------------------------------------
-- Generated outcomes from actual list/field execution, not hand-selected model results
-----------------------------------------------------------------------------------------

private def listObserved :=
  (observeActions
    (listActions Tests.schema Tests.resolvers [] 2
      (.nonNull (.named "String")) [] [] [] [] [.null, .null] 0)).run
    17

private def listPlan := completionPlan listObserved.1 0
private def listFirst : Sibling Execution.ResponseValue := ⟨0, .error 1⟩
private def listSecond : Sibling Execution.ResponseValue := ⟨1, .error 1⟩
private def listScope : Scope Execution.ResponseValue := { pending := listPlan }
private def listStarted := listScope.start listFirst.id
private def listSettled := listStarted.settle [] listFirst [listSecond]
private def listCut := listSettled.cancel [] listSecond []

private theorem list_plan : listPlan = [listFirst, listSecond] := by cbv

private theorem generated_list_cut : History listPlan listCut := by
  have start : History listPlan listStarted :=
    .start .initial listFirst (by rw [list_plan]; simp) rfl (by simp)
  have settled : History listPlan listSettled :=
    .settle start [] [listSecond] listFirst list_plan (by decide)
  exact .cancel settled [] [] listSecond rfl rfl

example
    : ((Execution.completeListValue Tests.schema Tests.resolvers [] 2
          (.nonNull (.named "String")) [] [.null, .null] [] 0 [] []).run
        17).1.result
      = .error 2 := by cbv

example : listCut.observe listPlan = some (.error 1) := rfl
example : listObserved.2 = 17 := by cbv
example : ((listPlan.map Sibling.id)).Nodup := completionPlan_unique _ _

-- The count gap is proved against this actual execution, with its exact supplies/outcomes.
example
    : listCut.reportedErrors + errorTotal listCut.pending + errorTotal listCut.cancelled
      = countedErrors
          ((Execution.completeListValue Tests.schema Tests.resolvers [] 2
              (.nonNull (.named "String")) [] [.null, .null] [] 0 [] []).run
            17).1.result :=
  completeListValue_scheduled_errors _ _ _ _ _ _ _ _ _ _ _ _ _ generated_list_cut

example
    : ∃ observed,
        listCut.observe listPlan = some observed
        ∧ SameData observed
            ((Execution.completeListValue Tests.schema Tests.resolvers [] 2
                (.nonNull (.named "String")) [] [.null, .null] [] 0 [] []).run
              17).1.result
        ∧ countedErrors observed = listCut.reportedErrors
        ∧ countedErrors observed + errorTotal listCut.cancelled
          = countedErrors
              ((Execution.completeListValue Tests.schema Tests.resolvers [] 2
                  (.nonNull (.named "String")) [] [.null, .null] [] 0 [] []).run
                17).1.result :=
  completeListValue_scheduled_observation _ _ _ _ _ _ _ _ _ _ _ _ _ generated_list_cut rfl

private def fatalFields : Execution.CollectedFieldsMap :=
  [
    ("left", [{ fieldName := "required", arguments := [], selectionSet := [] }]),
    ("right", [{ fieldName := "required", arguments := [], selectionSet := [] }])
  ]

private def fieldsObserved :=
  (observeActions
    (fieldActions Tests.schema Tests.resolvers [] 3 "Query"
      (.object "Query" 0) fatalFields [] [] [])).run
    29

example : errorTotal (completionPlan fieldsObserved.1 0) = 2 := by cbv
example : fieldsObserved.2 = 29 := by cbv

example
    : (Execution.executeCollectedFields Tests.schema Tests.resolvers [] 3 "Query"
        (.object "Query" 0) fatalFields [] [] []).run
        29
      = (foldCompletions List.append [] fieldsObserved.1, fieldsObserved.2) :=
  executeCollectedFields_observed ..

#print axioms History.partition
#print axioms History.positions_unique
#print axioms History.error_accounting
#print axioms History.complete_nonfatal_agrees
#print axioms History.complete_observation
#print axioms catchNull_errors
#print axioms fatal_combine_work
#print axioms prefixed_cut
#print axioms nullable_complete
#print axioms zero_cut
#print axioms executeActions_observed
#print axioms completionPlan_unique
#print axioms completeListValue_observed
#print axioms executeCollectedFields_observed
#print axioms completeListValue_scheduled_observation
#print axioms executeCollectedFields_scheduled_errors
#print axioms generated_list_cut

end AlternativeScheduledErrorChecks
