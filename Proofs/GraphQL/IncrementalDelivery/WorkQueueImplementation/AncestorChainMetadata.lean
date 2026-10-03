import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedWorkRefs

/-! Strengthened pure-execution ancestry metadata for immediate-parent queue links. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.AncestorChains
open GraphQL.IncrementalDelivery.Execution
open Semantics
open Semantics.Ancestry Semantics.MixedRefs

/-- Below `bound`, every nonempty ancestor list is its head followed by that head's list.
The assignment is proof evidence, not additional state in execution or the scheduler. -/
def Chains (parents : Assignment) (bound : Nat) : Prop :=
  ∀ ref < bound, ∀ parent rest, parents ref = parent :: rest → rest = parents parent

/-- The existing bounded/transitive ancestry certificate, strengthened with exact chains.
Its projection leaves all existing semantic metadata statements unchanged. -/
def Valid (parents : Assignment) (bound : Nat) : Prop :=
  Semantics.Ancestry.Valid parents bound ∧ Chains parents bound

/-- Fresh defer allocation preserves exact ancestor chains as well as earlier metadata.
Witness: the new ref copies its parent's complete list; all older refs and their smaller
parents retain their assignments. Stream allocation is the empty-parent case. -/
theorem allocate_valid (parents : Assignment) (state : Nat) (usage : Option DeferUsage)
    (valid : Valid parents state)
    (known : ∀ actual ∈ usage, actual.ref < state ∧ parents actual.ref = actual.ancestors)
    : Valid
        (allocate parents state
          ((usage.map (fun actual => actual.ref :: actual.ancestors)).getD []))
        (state + 1) := by
  refine ⟨Semantics.Ancestry.allocate_valid parents state usage valid.1 known, ?_⟩
  intro ref bound parent rest chain
  by_cases same : ref = state
  · subst ref
    cases usage with
    | none => simp [allocate] at chain
    | some actual =>
        have facts := known actual rfl
        have equal : actual.ref = parent ∧ actual.ancestors = rest := by
          simpa [allocate] using chain
        obtain ⟨rfl, rfl⟩ := equal
        simpa [allocate, Nat.ne_of_lt facts.1] using facts.2.symm
  · have earlier : ref < state := by omega
    have old : parents ref = parent :: rest := by simpa [allocate, same] using chain
    have parentBound : parent < state := by
      have smaller := (valid.1 ref earlier parent (by rw [old]; simp)).1
      omega
    simpa [allocate, Nat.ne_of_lt parentBound] using valid.2 ref earlier parent rest old

/-- Strengthened validity retains the original usage-before-allocation property.
Witness: project the original certificate; exact chains impose no extra usage premise. -/
theorem optionalUsageAt_before {parents : Assignment} {state : Nat} {deferMap : DeferMap}
    {usage : Option DeferUsage} (valid : Valid parents state)
    (known : OptionalUsageAt parents state deferMap usage)
    : UsageBefore state usage :=
  Semantics.MixedRefs.optionalUsageAt_before valid.1 known

/-- Executed work has the existing mixed-ref certificate and a chain-valid final assignment.
`lower` bounds work refs; `start` and `finish` are allocation counters. -/
def Output (parents : Assignment) (lower start : Nat) (work : Work) (finish : Nat)
    : Prop :=
  start ≤ finish
  ∧ ∃ next,
      Extends start parents next
      ∧ Valid next finish
      ∧ MixedRefs.WorkAt next lower finish work

/-- Completion's generated work and final counter satisfy the stronger output certificate.
Response data and errors are intentionally unconstrained by this metadata predicate. -/
def Completed (parents : Assignment) (lower start : Nat) (output : Completion α × Nat)
    : Prop :=
  Output parents lower start output.1.work output.2

/-- Empty work leaves the chain assignment and allocation counter unchanged.
Witness: reflexive extension and the empty mixed-work certificate. -/
theorem output_empty (parents : Assignment) (lower state : Nat)
    (valid : Valid parents state)
    : Output parents lower state .empty state :=
  ⟨Nat.le_refl _, parents, Extends.refl _ _, valid, by simp only [MixedRefs.WorkAt]⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.AncestorChains
