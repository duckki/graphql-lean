import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveCutAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginRecordingConstruction

/-! General same-execution, sequential recording correspondence. Initial,
deferred and item reports each get their own constructed history. These are
finite policy witnesses, not a claim that future work has already executed,
nor observations of native asynchronous resolver starts or error objects. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledWork

mutual
  inductive WorkRecordings : RecordedWork → RecordedWork → Prop where
    | empty : WorkRecordings .empty .empty
    | declareGroups {groups eagerGroups tasks eagerTasks}
      (nested : WorkRecordings tasks eagerTasks)
      : WorkRecordings (.declareGroups groups tasks)
          (.declareGroups eagerGroups eagerTasks)
    | combine {left eagerLeft right eagerRight}
      (head : WorkRecordings left eagerLeft) (tail : WorkRecordings right eagerRight)
      : WorkRecordings (.combine left right) (.combine eagerLeft eagerRight)
    | executionGroup
      {groups eagerGroups path eagerPath report eagerReport children eagerChildren}
      (head : ReportRecording report.toReport eagerReport.toReport)
      (nested : WorkRecordings children eagerChildren)
      : WorkRecordings (.executionGroup groups path report children)
          (.executionGroup eagerGroups eagerPath eagerReport eagerChildren)
    | stream {node eagerNode items eagerItems} (nested : ItemsRecordings items eagerItems)
      : WorkRecordings (.stream node items) (.stream eagerNode eagerItems)

  inductive ItemsRecordings
      : List (RecordedOutcome ResponseValue × RecordedWork)
        → List (RecordedOutcome ResponseValue × RecordedWork) → Prop where
    | nil : ItemsRecordings [] []
    | cons {report eagerReport children eagerChildren rest eagerRest}
      (head : ReportRecording report.toReport eagerReport.toReport)
      (nested : WorkRecordings children eagerChildren)
      (tail : ItemsRecordings rest eagerRest)
      : ItemsRecordings ((report, children) :: rest)
          ((eagerReport, eagerChildren) :: eagerRest)
end

mutual
  theorem WorkCutTrace.recording {cut eager} (trace : WorkCutTrace cut eager)
      (unique : eager.origins.Nodup)
      : WorkRecordings cut eager := by
    cases trace with
    | empty => exact .empty
    | declareGroups nested =>
        exact .declareGroups
          (nested.recording (by simpa only [RecordedWork.origins] using unique))
    | combine head tail =>
        simp only [RecordedWork.origins] at unique
        exact .combine (head.recording (List.nodup_append.mp unique).1)
          (tail.recording (List.nodup_append.mp unique).2.1)
    | executionGroup head nested =>
        simp only [RecordedWork.origins] at unique
        exact .executionGroup (head.recording (List.nodup_append.mp unique).1)
          (nested.recording (List.nodup_append.mp unique).2.1)
    | stream nested =>
        exact .stream
          (nested.recording
            (by simpa only [RecordedWork.origins, itemOrigins] using unique))
  termination_by sizeOf cut
  decreasing_by all_goals subst_vars; simp_wf; omega

  theorem ItemsCutTrace.recording {cut eager} (trace : ItemsCutTrace cut eager)
      (unique : (itemOrigins eager).Nodup)
      : ItemsRecordings cut eager := by
    cases trace with
    | nil => exact .nil
    | cons head nested tail =>
        simp only [itemOrigins, List.flatMap_cons] at unique
        have pair := (List.nodup_append.mp unique).1
        exact .cons (head.recording (List.nodup_append.mp pair).1)
          (nested.recording (List.nodup_append.mp pair).2.1)
          (tail.recording (List.nodup_append.mp unique).2.1)
  termination_by sizeOf cut
  decreasing_by all_goals subst_vars; simp_wf; omega
end

/-- No history, recording identity, cancellation explanation or desired output
relation is supplied by the caller. All scopes refer to the same two actual runs. -/
def RecursiveRecordingCorrespondence : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel parentType (source : ResolverValue ObjectRef) selections route
    initial left right,
    SupplyMap initial left right
    → let cut :=
        (RecordedExecution.executeRootSelectionSetCore schema resolvers variables fuel
          parentType source selections route).run
          left
      let eager :=
        (EagerRecordedExecution.executeRootSelectionSetCore schema resolvers variables
          fuel parentType source selections route).run
          right
      ∃ next initialSites futureSites,
        RunRefines initial next left right (eraseCompletionRun cut)
          (eraseCompletionRun eager)
        ∧ WorkSemanticsRefines next cut.1.erase.work eager.1.erase.work
        ∧ CompletionCutTrace cut.1 eager.1
        ∧ CutAccounted cut.1.report.origins eager.1.report.origins initialSites
        ∧ CutAccounted cut.1.work.origins eager.1.work.origins futureSites
        ∧ CutAccounted cut.1.origins eager.1.origins (initialSites ++ futureSites)
        ∧ ReportRecording cut.1.report eager.1.report
        ∧ WorkRecordings cut.1.work eager.1.work
        ∧ ScheduledErrors.countedErrors cut.1.report.outcome
            + (omittedOrigins cut.1.report.origins eager.1.report.origins).length
          = ScheduledErrors.countedErrors eager.1.report.outcome
        ∧ cut.1.origins.length + (omittedOrigins cut.1.origins eager.1.origins).length
          = eager.1.origins.length

theorem recursiveRecordingCorrespondence_holds : RecursiveRecordingCorrespondence := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route initial left right supplies
  obtain ⟨next, initialSites, futureSites, related, semantics, trace, initialCuts, futureCuts,
      allCuts, reportGap, wholeGap⟩ :=
    recursiveCutAccounting_holds ObjectRef schema resolvers variables fuel parentType source selections route
      initial left right supplies
  have eagerUnique := EagerScopes.recursiveEagerOriginUniqueness_holds ObjectRef schema resolvers variables fuel
    parentType source selections route right
  exact ⟨next, initialSites, futureSites, related, semantics, trace, initialCuts, futureCuts, allCuts,
    trace.1.recording eagerUnique.left.unique, trace.2.recording eagerUnique.right.unique,
    reportGap, wholeGap⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
