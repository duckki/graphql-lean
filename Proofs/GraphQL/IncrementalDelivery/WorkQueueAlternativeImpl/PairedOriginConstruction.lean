import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveOriginConstruction

/-! Actual eager and cut primitive inventories under one execution-refinement witness.
The inventories erase exactly and are each unique. Their comparison is constructed
separately in RecursiveOriginCoverage; aggregate count refinement does not prove it. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledWork

/-- Construct both actual inventories, exact erasures and one key map before any
task observation or causal cut. RecursiveOriginCoverage constructs their origin comparison. -/
def PairedOriginConstruction : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel parentType (source : ResolverValue ObjectRef) selections route
    initial left right,
    SupplyMap initial left right
    → let cut :=
        (RecordedExecution.executeRootSelectionSetCore schema resolvers variables
          fuel parentType source selections route).run
          left
      let eager :=
        (EagerRecordedExecution.executeRootSelectionSetCore schema resolvers
          variables fuel parentType source selections route).run
          right
      ∃ next,
        Scoped route cut.1.origins
        ∧ Scoped route eager.1.origins
        ∧ eraseCompletionRun cut
          = (ScheduledExecution.executeRootSelectionSetCore schema
              resolvers variables fuel parentType source selections).run
              left
        ∧ eraseCompletionRun eager
          = (Execution.executeRootSelectionSetCore schema resolvers
              variables fuel parentType source selections).run
              right
        ∧ RunRefines initial next left right (eraseCompletionRun cut)
            (eraseCompletionRun eager)
        ∧ WorkSemanticsRefines next cut.1.erase.work eager.1.erase.work

theorem pairedOriginConstruction_holds : PairedOriginConstruction := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route
    initial left right supplies
  obtain ⟨next, unique, erasure, related, semantics⟩ := recursiveOriginConstruction_holds
    ObjectRef schema resolvers variables fuel parentType source selections route
    initial left right supplies
  have eagerUnique := EagerScopes.recursiveEagerOriginUniqueness_holds ObjectRef schema
    resolvers variables fuel parentType source selections route right
  have eagerErasure := EagerErasure.recursiveEagerOriginErasure_holds ObjectRef schema
    resolvers variables fuel parentType source selections route right
  refine ⟨next, unique, eagerUnique, erasure, eagerErasure, ?_, ?_⟩
  · simpa only [eagerErasure] using related
  · have work := congrArg (fun output => output.1.work) eagerErasure
    dsimp only [eraseCompletionRun] at work
    simpa only [work] using semantics

/-- Origin-coverage target: the actual cut retains an ordered subsequence
of the actual eager primitive references, both initially and across retained Work.
Its witness is in RecursiveOriginCoverage. Coverage alone does not justify omitting
a native error already recorded before a cut. -/
def RecursiveOriginSubsequence : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel parentType (source : ResolverValue ObjectRef) selections route
    initial left right,
    SupplyMap initial left right
    → let cut :=
        (RecordedExecution.executeRootSelectionSetCore schema resolvers variables
          fuel parentType source selections route).run
          left
      let eager :=
        (EagerRecordedExecution.executeRootSelectionSetCore schema resolvers
          variables fuel parentType source selections route).run
          right
      cut.1.report.origins.Sublist eager.1.report.origins
      ∧ cut.1.origins.Sublist eager.1.origins

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
