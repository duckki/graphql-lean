import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredPhase

/-! Multiple deferred tasks can share owners without consuming later notice carriers. -/

namespace GraphQL.IncrementalDelivery.Tests.DeferredPhase
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- Empty-path nodes keep ownership independent of the two task addresses. -/
def node (key : Nat) : DeliveryNode := { key, path := [] }

/-- Two deferred tasks share key zero; the second also owns key one. The first produces
an empty stream whose notice still needs a success carrier after its producer publishes.
-/
def work (first second : Result (List (Name × ResponseValue))) : Work :=
  .append
    (.deferred [{ node := node 0 }] [] first (.stream (node 2) []))
    (.deferred [{ node := node 0 }, { node := node 1 }] [] second .empty)

/-- Every deferred task in this fixture is producer-free with initially covered owners.
Witness: the two valid deferred addresses; entering either child cannot find another task.
-/
theorem deferred_task {first second address owners producer payload}
    (known : TaskAt (work first second) (.deferred address) owners producer payload)
    : producer = none ∧ owners ≠ [] ∧ ∀ key ∈ owners, key ∈ [0, 1] := by
  obtain ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩ := known
  cases address with
  | nil => simp [Located, locateWork, locateWork.go, work] at located
  | cons side rest =>
      cases side with
      | zero =>
          cases rest with
          | nil =>
              simp [Located, locateWork, locateWork.go, WorkLocation.child?, work] at located
              rcases located with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
              simp [node]
          | cons edge tail =>
              cases edge <;> cases tail <;>
                simp [Located, locateWork, locateWork.go, WorkLocation.child?, work] at located
      | succ side =>
          cases side with
          | zero =>
              cases rest with
              | nil =>
                  simp [Located, locateWork, locateWork.go, WorkLocation.child?, work] at located
                  rcases located with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
                  simp [node]
              | cons edge tail =>
                  cases edge <;> cases tail <;>
                    simp [Located, locateWork, locateWork.go, WorkLocation.child?, work] at located
          | succ side =>
              simp [Located, locateWork, locateWork.go, WorkLocation.child?, work] at located

/-- Both group notices are initially eligible for every combination of task outcomes.
Witness: the second, still-unaccounted task contributes to both keys; failure evidence is
empty initially, so an eventual error does not preemptively cancel it.
-/
theorem initialized (first second : Result (List (Name × ResponseValue)))
    : Initializes (work first second) [node 0, node 1] [] := by
  have task : TaskAt (work first second) (.deferred [1]) [0, 1] none
      (.object [] second) := .deferred (.right .root)
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro owner member
  have known : NodeAt (work first second) owner .group [] none := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .group (group := { node := node 0 }) (.right .root) (by simp)
    · exact .group (group := { node := node 1 }) (.right .root) (by simp)
  have contributes : owner.key ∈ [0, 1] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [node]
  refine ⟨
    [],
    none,
    known,
    by simp [announcedKeys, pendingKeys],
    fun failure => failure.nonempty rfl,
    Or.inr ?_,
    by simp,
    by simp
  ⟩
  intro accounted
  rcases accounted (.deferred [1]) [0, 1] ⟨none, .object [] second, task⟩ contributes
    with cancelled | published
  · exact cancelled.nonempty rfl
  · simp [Published] at published

/-- Both deferred tasks finish their phase, including shared-owner cancellation on error,
while healthy keys zero and one remain available as success carriers. The child stream
is not forced into an invalid early notice. Witness: the general finite deferred phase.
-/
theorem phase_exists (first second : Result (List (Name × ResponseValue)))
    : ∃ events matching failures,
        Explains (work first second) [node 0, node 1] [] events matching failures
        ∧ (∀ event ∈ events, DeferredPhaseEvent event)
        ∧ DeferredTasksAccounted (work first second) matching events
            (failures.map Prod.snd)
        ∧ ∀ key ∈ [0, 1],
            ¬NodeFailed (work first second) (failures.map Prod.snd) key
            → Open [0, 1] events key := by
  apply finish_root_deferred_tasks (paths := fun _ => []) (bound := 3)
  · simp [work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt, OwnerPaths.mapNodes,
      OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below, node]
  · exact initialized first second
  · exact fun _ _ _ _ known => (deferred_task known).1
  · intro address owners producer payload known
    simpa [node] using (deferred_task known).2

end GraphQL.IncrementalDelivery.Tests.DeferredPhase
