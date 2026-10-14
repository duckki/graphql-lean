import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveOriginUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveExecutionSemantics

/-! One constructed witness couples primitive-origin inventories to the actual
recursive eager/cut execution and its structural/causal key-map certificate. Origins
are not independent per-task witnesses and do not stand in for native error objects,
recording times, or an eager-origin cancellation/omission relation. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open ScheduledWork

-----------------------------------------------------------------------------------------
-- One actual annotated run and one map precede all retained scopes and causal cuts
-----------------------------------------------------------------------------------------

/-- Arbitrary actual cut execution has a unique retained primitive inventory and
erases exactly. The same run and one extending map carry the eager comparison and
all structural/causal consequences. Public eager execution remains unchanged. -/
def RecursiveOriginConstruction : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel parentType (source : ResolverValue ObjectRef) selections route
    initial left right,
    SupplyMap initial left right
    → let annotated :=
        (RecordedExecution.executeRootSelectionSetCore schema resolvers variables fuel
          parentType source selections route).run
          left
      let scheduled :=
        (ScheduledExecution.executeRootSelectionSetCore schema resolvers variables fuel
          parentType source selections).run
          left
      let eager :=
        (Execution.executeRootSelectionSetCore schema resolvers variables fuel parentType
          source selections).run
          right
      ∃ next,
        Scoped route annotated.1.origins
        ∧ eraseCompletionRun annotated = scheduled
        ∧ RunRefines initial next left right (eraseCompletionRun annotated) eager
        ∧ WorkSemanticsRefines next annotated.1.erase.work eager.1.work

theorem recursiveOriginConstruction_holds : RecursiveOriginConstruction := by
  intro ObjectRef schema resolvers variables fuel parentType source selections route
    initial left right supplies
  have unique := recursiveOriginUniqueness_holds ObjectRef schema resolvers variables
    fuel parentType source selections route left
  have erasure := recursiveOriginErasure_holds ObjectRef schema resolvers variables fuel
    parentType source selections route left
  obtain ⟨next, related, semantics⟩ := recursiveExecutionSemantics_holds ObjectRef schema
    resolvers variables fuel parentType source selections initial left right supplies
  refine ⟨next, unique, erasure, ?_, ?_⟩
  · simpa only [erasure] using related
  · have work := congrArg (fun output => output.1.work) erasure
    dsimp only [eraseCompletionRun] at work
    simpa only [work] using semantics

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
