import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! Live-ancestor health checking and its exact missing-parent boundary.
The fuel only totalizes malformed graphs; a native bridge must establish acyclic ancestry.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- An absent ancestor ends this health walk without consulting cancellation history. -/
def ancestorsHealthy (queue : ReferenceWorkQueue.State) : Nat → Option Nat → Bool
  | _, none => true
  | 0, some _ => false
  | fuel + 1, some parent =>
      match queue.groupNode? parent with
      | none => true
      | some node => node.failure.isNone && ancestorsHealthy queue fuel node.group.parent

def groupIsHealthy (queue : ReferenceWorkQueue.State) (key : Nat) : Bool :=
  match queue.groupNode? key with
  | none => false
  | some node =>
      node.failure.isNone
      && ancestorsHealthy queue queue.groupNodes.length node.group.parent

/-- A structural cut invariant, not an assumption added to EventSource.ValidFor.
Each live record's absent immediate parent was not removed by failure.
-/
def SafeParentCuts (queue : ReferenceWorkQueue.State) : Prop :=
  ∀ node ∈ queue.groupNodes,
    ∀ parent,
      node.group.parent = some parent
      → queue.groupNode? parent = none
      → parent ∉ queue.cancelledGroups

private theorem ancestorsHealthy_eq (queue : ReferenceWorkQueue.State)
    (cuts : SafeParentCuts queue) (fuel : Nat) (parent : Option Nat)
    (first
      : ∀ key,
          parent = some key → queue.groupNode? key = none → key ∉ queue.cancelledGroups)
    : ancestorsHealthy queue fuel parent
      = ReferenceWorkQueue.State.groupIsHealthy.ancestorsHealthy queue fuel parent := by
  induction fuel generalizing parent with
  | zero => cases parent <;> rfl
  | succ fuel ih =>
      cases parent with
      | none => rfl
      | some key =>
          cases found : queue.groupNode? key with
          | none =>
              simp [ancestorsHealthy, ReferenceWorkQueue.State.groupIsHealthy.ancestorsHealthy,
                found, first key rfl found]
          | some node =>
              simp only [ancestorsHealthy, found,
                ReferenceWorkQueue.State.groupIsHealthy.ancestorsHealthy]
              rw [ih node.group.parent (cuts node (List.mem_of_find?_eq_some found))]

/-- Under the precise structural cut invariant, the two guards agree for every key. -/
theorem groupIsHealthy_eq_reference (queue : ReferenceWorkQueue.State)
    (cuts : SafeParentCuts queue) (key : Nat)
    : groupIsHealthy queue key = queue.groupIsHealthy key := by
  unfold groupIsHealthy ReferenceWorkQueue.State.groupIsHealthy
  cases found : queue.groupNode? key with
  | none => rfl
  | some node =>
      simp only
      rw [ancestorsHealthy_eq queue cuts _ _ (cuts node (List.mem_of_find?_eq_some found))]

/-- Raw counterexample: an orphan live child of a failed absent parent separates the guards. -/
def orphanedChild : ReferenceWorkQueue.State :=
  {
    cancelledGroups := [0],
    groupNodes := [{ group := { node := { ref := 1, path := [] }, parent := some 0 } }]
  }

theorem orphanedChild_separates_guards
    : groupIsHealthy orphanedChild 1 = true ∧ orphanedChild.groupIsHealthy 1 = false := by
  decide

theorem orphanedChild_cuts_unsafe : ¬SafeParentCuts orphanedChild := by
  intro cuts
  have absent := cuts
    { group := { node := { ref := 1, path := [] }, parent := some 0 } }
    (by simp [orphanedChild]) 0 rfl (by decide)
  exact absent (by simp [orphanedChild])

/-- Construction target for safe cuts at actual generated replay boundaries.
`GeneratedParentCuts_holds` in GeneratedParentCuts supplies its unconditional witness.
-/
def GeneratedParentCuts : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → SafeParentCuts ((State.initialize work).runNormalized inputs).1.queue

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
