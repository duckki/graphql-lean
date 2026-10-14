import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveOriginCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginOmissions

/-! One actual paired run couples full origin coverage to unique inventories,
exact erasures and the already-constructed execution/causality map. This witness
is selected before all scope observations; no native recording history is claimed. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledWork

/-- General paired execution and originating-reference coverage under one final
map. Initial report counts and the whole retained inventory remain separate. -/
def PairedOriginCoverage : Prop :=
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
      ∃ next,
        Scoped route cut.1.origins
        ∧ Scoped route eager.1.origins
        ∧ eraseCompletionRun cut
          = (ScheduledExecution.executeRootSelectionSetCore schema resolvers variables
              fuel parentType source selections).run
              left
        ∧ eraseCompletionRun eager
          = (Execution.executeRootSelectionSetCore schema resolvers variables fuel
              parentType source selections).run
              right
        ∧ RunRefines initial next left right (eraseCompletionRun cut)
            (eraseCompletionRun eager)
        ∧ WorkSemanticsRefines next cut.1.erase.work eager.1.erase.work
        ∧ CompletionOriginsRefine cut.1 eager.1
        ∧ ScheduledErrors.countedErrors cut.1.report.outcome
            + (omittedOrigins cut.1.report.origins eager.1.report.origins).length
          = ScheduledErrors.countedErrors eager.1.report.outcome
        ∧ cut.1.origins.length + (omittedOrigins cut.1.origins eager.1.origins).length
          = eager.1.origins.length

theorem pairedOriginCoverage_holds : PairedOriginCoverage := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route initial left right supplies
  obtain ⟨next, cutUnique, eagerUnique, cutErasure, eagerErasure, related, semantics⟩ :=
    pairedOriginConstruction_holds ObjectRef schema resolvers variables fuel parentType source selections route
      initial left right supplies
  have covered := recursiveOriginCoverage_holds ObjectRef schema resolvers variables fuel parentType source
    selections route initial left right supplies
  exact ⟨next, cutUnique, eagerUnique, cutErasure, eagerErasure, related, semantics, covered,
    covered.1.omitted_count eagerUnique.left.unique,
    omittedOrigins_partition covered.origins eagerUnique.unique⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
