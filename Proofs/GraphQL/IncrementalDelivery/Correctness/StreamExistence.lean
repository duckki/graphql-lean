import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerAvailability

/-! Complete-run existence for arbitrary finite streams without child work. Item values
and error outcomes are unrestricted; no complete history is supplied as a premise.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- A child-free stream has only its root stream boundary and empty located subtrees.
Witness: structural navigation and the supplied empty-child equations for every item.
-/
theorem childFreeStream_located {node items address current producer owners}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (located : Located (.stream node items) address current producer owners)
    : (address = [] ∧ current = .stream node items ∧ producer = none ∧ owners = [])
      ∨ current = .empty := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  | left _ ih | right _ ih | executionGroup _ ih =>
      rcases ih with ⟨_, impossible, _, _⟩ | impossible <;> cases impossible
  | item located selected ih =>
      rcases ih with ⟨rfl, same, rfl, rfl⟩ | impossible
      · cases same
        exact Or.inr (childrenEmpty _ (List.mem_of_getElem? selected))
      · cases impossible

/-- Every task in a child-free stream has the stream's sole owner and no producer.
Witness: its only nonempty located boundary; no deferred task can occur there.
-/
theorem childFreeStream_task {node items occurrence owners producer payload}
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    (known : TaskAt (.stream node items) occurrence owners producer payload)
    : owners = [node.key] ∧ producer = none := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      rcases childFreeStream_located childrenEmpty located.toCurrent with
        ⟨_, impossible, _, _⟩ | impossible <;> cases impossible
  | item located selected =>
      rcases childFreeStream_located childrenEmpty located.toCurrent with
        ⟨rfl, same, rfl, rfl⟩ | impossible
      · cases same
        exact ⟨rfl, rfl⟩
      · cases impossible

/-- A finite stream with no nested child work always admits a complete run, even with
failing items or no items. Witness: announce the root stream, cover all task owners, then
use the maximal-history construction and its derived terminal completion.
-/
theorem childFreeStream_completeRun_exists (node : DeliveryNode)
    (items : List (Result ResponseValue × Work))
    (childrenEmpty : ∀ item ∈ items, item.2 = Work.empty)
    : ∃ history, AdmissibleRun (.stream node items) history := by
  have coherent : MixedOwnerPaths.WorkAt (fun _ => node.path) (node.key + 1)
      (.stream node items) := by
    rw [MixedOwnerPaths.WorkAt]
    exact ⟨⟨by omega, rfl⟩, fun item member => by
      rw [childrenEmpty item member, MixedOwnerPaths.WorkAt]
      trivial⟩
  have initialized : Initializes (.stream node items) [] [node] := by
    refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro stream member
    have same := List.mem_singleton.mp member
    subst stream
    refine ⟨[], none, .stream .root, ?_⟩
    exact ⟨by simp [announcedKeys, pendingKeys],
      fun failure => failure.nonempty rfl, Or.inl rfl, by simp, Or.inl rfl⟩
  apply completeRun_exists_of_initial_owner_coverage coherent initialized
  intro occurrence owners producer payload known
  obtain ⟨rfl, _⟩ := childFreeStream_task childrenEmpty known
  simp

end GraphQL.IncrementalDelivery.Correctness
