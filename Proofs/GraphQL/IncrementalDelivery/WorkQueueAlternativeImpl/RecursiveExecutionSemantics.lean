import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveExecutionConstruction
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkCausality

/-! Structural and causal consequences of the constructed actual recursive executions.
The same final key map is selected before any location, task, node or failure/publication
snapshot. No related-output premise or separately chosen per-snapshot identity map is
required. Native settlement/admission and originating-error records remain outside this
pure execution result. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- One witness covers both structural inventories and every shared causal cut
-----------------------------------------------------------------------------------------

structure WorkSemanticsRefines (keys : Nat → Nat) (scheduled eager : Work) : Prop where
  locations
    : ∀ address,
        OptionRefines (LocationRefines keys) (locateWork scheduled address)
          (locateWork eager address)
  tasks
    : ∀ occurrence owners producer value,
        TaskAt scheduled occurrence owners producer value
        → ∃ after,
            TaskAt eager occurrence (owners.map keys) producer after
            ∧ PayloadRefines keys value after
  taskCoverage
    : ∀ occurrence owners producer value,
        TaskAt eager occurrence owners producer value
        → ∃ before outcome,
            TaskAt scheduled occurrence before producer outcome
            ∧ before.map keys = owners
            ∧ PayloadRefines keys outcome value
  nodes
    : ∀ descriptor kind dependencies producer,
        NodeAt eager descriptor kind dependencies producer
        ↔ ∃ before parents,
            NodeAt scheduled before kind parents producer
            ∧ KeyRenaming.node keys before = descriptor
            ∧ parents.map keys = dependencies
  reachable : ∀ occurrence, Reachable eager occurrence ↔ Reachable scheduled occurrence
  nodeFailures
    : ∀ failed published renamed,
        Causality.NodeFailed eager failed published renamed
        ↔ ∃ key, keys key = renamed ∧ Causality.NodeFailed scheduled failed published key
  cancellations
    : ∀ failed published occurrence,
        Causality.TaskCancelled eager failed published occurrence
        ↔ Causality.TaskCancelled scheduled failed published occurrence

theorem workSemanticsRefines_of_work {keys scheduled eager}
    (related : WorkRefines keys scheduled eager) (injective : Function.Injective keys)
    : WorkSemanticsRefines keys scheduled eager := by
  obtain ⟨locations, tasks, coverage, nodes⟩ := recursiveWorkStructure_holds keys scheduled eager related
  refine ⟨locations, tasks, coverage, nodes, related.reachable, ?_, ?_⟩
  · intro failed published
    exact (recursiveWorkCausality_holds keys injective scheduled eager related failed published).2.1
  · intro failed published
    exact (recursiveWorkCausality_holds keys injective scheduled eager related failed published).2.2

theorem RunRefines.workSemantics {initial next left right}
    {scheduled eager : Completion α × Nat}
    (known : RunRefines initial next left right scheduled eager)
    : WorkSemanticsRefines next scheduled.1.work eager.1.work :=
  workSemanticsRefines_of_work known.completion.2 known.supplies.injective

-----------------------------------------------------------------------------------------
-- Construct from actual roots, without an assumed recursive Work correspondence
-----------------------------------------------------------------------------------------

/-- One existential is outside all semantic observations and causal snapshots. Failed
occurrences and already-published occurrences must be shared between the two sides;
the theorem neither constructs native histories nor changes that comparison boundary. -/
def RecursiveExecutionSemantics : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    selections initial left right,
    SupplyMap initial left right
    → let scheduled :=
        (ScheduledExecution.executeRootSelectionSetCore schema resolvers variables
          fuel parentType source selections).run
          left
      let eager :=
        (Execution.executeRootSelectionSetCore schema resolvers variables fuel
          parentType source selections).run
          right
      ∃ next,
        RunRefines initial next left right scheduled eager
        ∧ WorkSemanticsRefines next scheduled.1.work eager.1.work

theorem recursiveExecutionSemantics_holds : RecursiveExecutionSemantics := by
  intro ObjectRef schema resolvers variables fuel parentType source selections initial left right supplies
  obtain ⟨next, constructed⟩ := recursiveExecutionConstruction_holds ObjectRef schema resolvers variables
    fuel parentType source selections initial left right supplies
  exact ⟨next, constructed, constructed.workSemantics⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
