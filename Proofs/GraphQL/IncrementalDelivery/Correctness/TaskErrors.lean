import Proofs.GraphQL.IncrementalDelivery.Correctness.ExecutionErrors
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence

/-! Structural execution certificates apply to each scheduler-visible task. -/

namespace GraphQL.IncrementalDelivery.Correctness.ExecutionErrors
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- Every selected stream entry inherits the list certificate, by membership induction. -/
theorem ItemsPositive.member {items : List (Result ResponseValue × Work)}
    (positive : ItemsPositive items) {result children}
    (member : (result, children) ∈ items)
    : BasicErrors.PositiveFailure result ∧ WorkPositive children := by
  induction items with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst entry; exact ⟨positive.1, positive.2.1⟩
      · exact ih positive.2.2 member

/-- Lookup preserves the work certificate at every address, by navigation induction. -/
theorem WorkPositive.located {work address current producer owners}
    (positive : WorkPositive work)
    (located : Located work address current producer owners)
    : WorkPositive current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact positive
  | left _ ih => exact ih.1
  | right _ ih => exact ih.2
  | deferred _ ih => exact ih.2
  | item _ entry ih => exact (ih.member (List.mem_of_getElem? entry)).2

/-- Every scheduler-visible failing task has a positive count; witness: its located
result and the execution certificate, with no restriction on streams or raw syntax.
-/
theorem WorkPositive.task {work occurrence owners producer payload}
    (positive : WorkPositive work)
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true)
    : 0 < payload.failure.getD 0 := by
  cases StructuralEquivalence.taskAt_of_current known with
  | @deferred address groups path result children producer enclosing located =>
      have resultPositive := (positive.located located.toCurrent).1
      cases result <;> simp_all [Payload.failure, BasicErrors.PositiveFailure]
  | @item address node items producer enclosing index result children located entry =>
      have resultPositive :=
        ((positive.located located.toCurrent).member (List.mem_of_getElem? entry)).1
      cases result <;> simp_all [Payload.failure, BasicErrors.PositiveFailure]

end GraphQL.IncrementalDelivery.Correctness.ExecutionErrors
