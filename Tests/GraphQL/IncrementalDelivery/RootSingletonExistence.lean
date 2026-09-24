import Proofs.GraphQL.IncrementalDelivery.Correctness.RootSingletonExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization

/-! Dependent defer IDs need later group-success notices, not full initial coverage. -/

namespace GraphQL.IncrementalDelivery.Tests.RootSingletonExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

/-- Root group and descendant-ID descriptors have separate keys but the same object path.
-/
def node (key : Nat) : DeliveryNode := { key, path := [] }

/-- The second root task's defer ID depends on completion of the first task's group.
Neither task is a structural producer of the other; the dependency is defer ancestry.
-/
def work (first second : Result (List (Name × ResponseValue))) : Work :=
  .combine (.executionGroup [{ node := node 0 }] [] first .empty)
    (.executionGroup [{ node := node 1, ancestors := [node 0] }] [] second .empty)

/-- Structural locations stop at one of the two root tasks or its empty child.
Witness: navigation induction; no task-producing edge can reveal further work.
-/
theorem located_work {first second address current producer owners}
    (located : Located (work first second) address current producer owners)
    : (current = work first second ∧ producer = none)
      ∨ (current = .executionGroup [{ node := node 0 }] [] first .empty ∧ producer = none)
      ∨ (current
            = .executionGroup [{ node := node 1, ancestors := [node 0] }] [] second .empty
          ∧ producer = none)
      ∨ current = .empty := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact Or.inl ⟨rfl, rfl⟩
  | left _ ih =>
      rcases ih with ⟨same, birth⟩ | ⟨same, _⟩ | ⟨same, _⟩ | same
      · cases same
        exact Or.inr (Or.inl ⟨rfl, birth⟩)
      all_goals cases same
  | right _ ih =>
      rcases ih with ⟨same, birth⟩ | ⟨same, _⟩ | ⟨same, _⟩ | same
      · cases same
        exact Or.inr (Or.inr (Or.inl ⟨rfl, birth⟩))
      all_goals cases same
  | executionGroup _ ih =>
      rcases ih with ⟨same, _⟩ | ⟨same, _⟩ | ⟨same, _⟩ | same
      all_goals cases same
      all_goals exact Or.inr (Or.inr (Or.inr rfl))
  | item _ _ ih =>
      rcases ih with ⟨same, _⟩ | ⟨same, _⟩ | ⟨same, _⟩ | same
      all_goals cases same

/-- All fixture nodes are root groups and every task has a singleton owner list.
Witness: the preceding structural location classification; ancestry is left intact.
-/
theorem root_singleton (first second : Result (List (Name × ResponseValue)))
    : RootSingletonGroups (work first second) := by
  constructor
  · intro node kind parents producer known
    cases StructuralEquivalence.nodeAt_of_current known with
    | group located member =>
        rcases located_work located.toCurrent with
          ⟨same, birth⟩ | ⟨same, birth⟩ | ⟨same, birth⟩ | same
        · cases same
        · exact ⟨rfl, birth⟩
        · exact ⟨rfl, birth⟩
        · cases same
    | stream located =>
        rcases located_work located.toCurrent with
          ⟨same, _⟩ | ⟨same, _⟩ | ⟨same, _⟩ | same
        all_goals cases same
  · intro occurrence owners producer payload known
    cases StructuralEquivalence.taskAt_of_current known with
    | executionGroup located =>
        rcases located_work located.toCurrent with
          ⟨same, _⟩ | ⟨same, _⟩ | ⟨same, _⟩ | same
        all_goals cases same
        all_goals exact ⟨_, rfl⟩
    | item located entry =>
        rcases located_work located.toCurrent with
          ⟨same, _⟩ | ⟨same, _⟩ | ⟨same, _⟩ | same
        all_goals cases same

/-- Key one has the complete strict ancestry list containing key zero. -/
def ancestors (key : Nat) : Keys := if key = 1 then [0] else []

/-- Every pair of fixed outcomes admits a terminal history despite delayed child-ID
announcement. Witness: the root-singleton existence theorem with explicit coherent
ancestry metadata, not an assumed history or an initial notice for the dependent ID.
-/
theorem dependent_run_exists (first second : Result (List (Name × ResponseValue)))
    : ∃ history, AdmissibleRun (work first second) history := by
  apply (root_singleton first second).completeRun_exists (parents := ancestors)
    (bound := 2) (paths := fun _ => []) (pathBound := 2)
  · intro key bounded parent member
    by_cases same : key = 1
    · simp [ancestors, same] at member
      subst parent
      simp [same, ancestors, List.Subset]
    · simp [ancestors, same] at member
  · simp [work, MixedKeys.WorkAt, FragmentAt, node, ancestors]
  · simp [work, DeferContinuous, DeferUnder]
  · simp [work, StreamOwnersOrdered, OwnersBefore]
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · simp [work, Work.size]

/-- The dependent group is not initially eligible. Witness: key zero is present work
and is neither completed nor accounted for before its sole task publishes.
-/
example (first second : Result (List (Name × ResponseValue)))
    : ¬CanAnnounce (work first second) [] (fun _ => .executionGroup [0]) [] []
        (node 1) .group [0] none := by
  intro eligible
  have dependency := eligible.2.2.2.2 0 (by simp)
  rcases dependency.2 with absent | completed | ⟨_, accounted⟩
  · exact absent ⟨none, node 0, .group, [],
      NodeAt.group (group := { node := node 0 }) (.left .root) (by simp), rfl⟩
  · simp [completedKeys] at completed
  · rcases accounted (.executionGroup [0]) [0]
      ⟨none, .object [] first, TaskAt.executionGroup (.left .root)⟩ (by simp)
      with cancelled | published
    · exact cancelled.nonempty rfl
    · simp [Published] at published

/-- Complete dependent-ID histories realize actual complete response streams for every
outcome pair. Witness: construct the history first, then use the general source bridge.
-/
example (response : Response) (first second : Result (List (Name × ResponseValue)))
    : ∃ scheduler : Execution.WorkScheduler,
      ∃ observed : ExecutionObservation,
        scheduler.Conforms (work first second)
        ∧ (executionFromWork scheduler response (work first second)).Observes observed
            true :=
  (completeObservation_exists_iff _ _).mpr (Or.inr (dependent_run_exists first second))

end GraphQL.IncrementalDelivery.Tests.RootSingletonExistence
