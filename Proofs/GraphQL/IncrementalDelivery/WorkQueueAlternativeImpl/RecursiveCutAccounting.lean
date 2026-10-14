import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveCutConstruction

/-! General reached-cut accounting, constructed for the two actual finite runs.
Initial and future scopes remain distinct. The same runs retain the existing
execution/causality map and exact identity gaps; no native history is assumed. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledWork

/-- Reached cuts are witnessed by the recursively constructed control-flow
derivation, not inferred from a smaller count or supplied as a caller premise. -/
def RecursiveCutAccounting : Prop :=
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
        ∧ ScheduledErrors.countedErrors cut.1.report.outcome
            + (omittedOrigins cut.1.report.origins eager.1.report.origins).length
          = ScheduledErrors.countedErrors eager.1.report.outcome
        ∧ cut.1.origins.length + (omittedOrigins cut.1.origins eager.1.origins).length
          = eager.1.origins.length

theorem recursiveCutAccounting_holds : RecursiveCutAccounting := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route initial left right supplies
  obtain ⟨next, _, _, _, _, related, semantics, _, reportGap, wholeGap⟩ :=
    pairedOriginCoverage_holds ObjectRef schema resolvers variables fuel parentType source selections route
      initial left right supplies
  have trace := recursiveCutConstruction_holds ObjectRef schema resolvers variables fuel parentType source
    selections route initial left right supplies
  obtain ⟨initialSites, initialAccounting⟩ := trace.1.accounting
  obtain ⟨futureSites, futureAccounting⟩ := trace.2.accounting
  exact ⟨next, initialSites, futureSites, related, semantics, trace,
    initialAccounting, futureAccounting, initialAccounting.append futureAccounting,
    reportGap, wholeGap⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
