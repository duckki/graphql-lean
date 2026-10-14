import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentDiscovery

/-! Shared ancestors, insertion order, once-only parent reads and unsafe early-stop inputs. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ParentDiscovery.Tests

example : ParentDiscoveryOptimization := ParentDiscoveryOptimization_holds

private def parent : Parents
  | 12 => some 11
  | 11 | 13 => some 10
  | _ => none

private def height : Nat → Nat
  | 12 => 2
  | 11 | 13 => 1
  | _ => 0

private theorem decreasing : Decreasing parent height := by
  intro key ancestor edge
  unfold parent at edge
  split at edge <;> simp_all [height] <;> subst ancestor <;> decide

private def seeds : List Nat := [12, 13, 12, 20]

example : (discover parent height seeds).nodes = [12, 11, 10, 13, 20] := rfl

example
    : (discover parent height seeds).finished = true
      ∧ (discover parent height seeds).parentReads = 5
      ∧ (discover parent height seeds).probes = 7 := by decide

example : ParentClosed parent (discover parent height seeds).nodes :=
  (ParentDiscoveryOptimization_holds parent height decreasing seeds).2.2.1

example (key : Nat)
    : key ∈ (discover parent height seeds).nodes ↔ Reachable parent seeds key :=
  (ParentDiscoveryOptimization_holds parent height decreasing seeds).2.2.2.1 key

-- Ancestors not selected by any field are discovered; an unrelated node is not.
example
    : 10 ∈ (discover parent height seeds).nodes
      ∧ 999 ∉ (discover parent height seeds).nodes := by decide

example
    : (discover parent height []).nodes = []
      ∧ (discover parent height []).probes = 0 := by decide

-- A partial walk may have inserted a node without yet closing its parent edge.
example
    : (walk parent 1 (some 12) []).finished = false
      ∧ (walk parent 1 (some 12) []).nodes = [12] := by decide

-- The early-stop rule alone cannot repair an already indexed but unclosed ancestor.
example
    : (discoverFrom parent height [12] [11]).finished = true
      ∧ (discoverFrom parent height [12] [11]).nodes = [11, 12] := by decide

example : ¬ ParentClosed parent (discoverFrom parent height [12] [11]).nodes := by
  intro closed
  have missing := closed 11 (by decide) 10 (by rfl)
  contradiction

private def cycle : Parents :=
  fun key => if key = 1 then some 2 else if key = 2 then some 1 else none

-- Seen membership can stop a cycle, but that graph cannot license a parent-forest index.
example
    : (walk cycle 3 (some 1) []).finished = true
      ∧ (walk cycle 3 (some 1) []).nodes = [1, 2] := by decide

example : ¬ ∃ height, Decreasing cycle height := by
  rintro ⟨rank, decreases⟩
  have first := decreases 1 2 (by simp [cycle])
  have second := decreases 2 1 (by simp [cycle])
  omega

#print axioms ParentDiscoveryOptimization_holds

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ParentDiscovery.Tests
