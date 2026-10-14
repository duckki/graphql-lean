import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceCredits

/-! Source-credit regressions keep reserve/release distinct from receipt acknowledgement.
Raw pushes ignoring waits deliberately refute a universal hard-capacity claim.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.SourceCreditTests

example : ContinuousSourceCreditSafety := ContinuousSourceCreditSafety_holds

example (actions : List (SourceCreditAction Nat))
    (legal : ({} : SourceBuffer Nat).Legal 100 actions) (count : Nat)
    : (({} : SourceBuffer Nat).run 100 (actions.take count)).1.occupied ≤ 100 :=
  SourceBuffer.prefix_occupied_le 100 (by decide) actions legal count

private def fullWindow : List (SourceCreditAction Nat) :=
  [.beginPull, .push .pending, .beginPull, .push (.fulfilled 20)]

example : ({} : SourceBuffer Nat).Legal 2 fullWindow := by
  simp [SourceBuffer.Legal, SourceBuffer.Enabled, SourceBuffer.step, fullWindow]

example
    : let full := ({} : SourceBuffer Nat).run 2 fullWindow
      full.1.occupied = 2 ∧ full.1.waiting = true ∧ ¬ full.1.Enabled .beginPull := by
  simp [SourceBuffer.run, SourceBuffer.Enabled, SourceBuffer.step, SourceBuffer.occupied, fullWindow]

-- The settled second slot cannot overtake the pending first slot.
example : (({} : SourceBuffer Nat).run 2 (fullWindow ++ [.take])).2 = [] := by
  decide

example
    : (({} : SourceBuffer Nat).run 2
        (fullWindow ++ [.settle 0 (.fulfilled 10), .take, .take])).2
      = [10, 20] := by
  decide

-- No receipt acknowledgement or next wire-reader turn occurs before this refill.
private def refillBeforeAck : List (SourceCreditAction Nat) :=
  fullWindow ++ [.settle 0 (.fulfilled 10), .take, .beginPull, .push .pending]

example : ({} : SourceBuffer Nat).Legal 2 refillBeforeAck := by
  simp [SourceBuffer.Legal, SourceBuffer.Enabled, SourceBuffer.step, fullWindow, refillBeforeAck]

example
    : let observed := ({} : SourceBuffer Nat).run 2 refillBeforeAck
      observed.2 = [10]
      ∧ observed.1.entries = [.fulfilled 20, .pending]
      ∧ observed.1.occupied = 2
      ∧ observed.1.waiting = true := by
  decide

-- An acknowledgement after partial consumption releases no producer-owned suffix slots.
example
    : ({} : SourceBuffer Nat).run 2 (refillBeforeAck ++ [.acknowledge])
      = ({} : SourceBuffer Nat).run 2 refillBeforeAck := by
  decide

example (state : SourceBuffer Nat) : state.step 2 .acknowledge = (state, []) :=
  state.acknowledge_identity 2

-- Synthetic failure entries are not counted: a rejected original completion still owns its slot.
example
    : let observed :=
        ({} : SourceBuffer Nat).run 1 [.beginPull, .push .rejected, .take, .acknowledge]
      observed.1.occupied = 1 ∧ observed.1.waiting = true ∧ observed.2 = [] := by
  decide

example
    : (({} : SourceBuffer Nat).run 2 (fullWindow ++ [.cancel])).1
      = (⟨[], false, false, true⟩ : SourceBuffer Nat) := by
  decide

example
    : (({} : SourceBuffer Nat).run 2 (fullWindow ++ [.finishSource])).1.entries
      = [.pending, .fulfilled 20] := by
  decide

-- The protocol, not raw Queue.push, supplies the bound. Ignoring its wait overfills the queue.
private def ignoresPushWait : List (SourceCreditAction Nat) :=
  [.beginPull, .push (.fulfilled 10), .beginPull, .push (.fulfilled 20)]

example : ¬ ({} : SourceBuffer Nat).Legal 1 ignoresPushWait := by
  simp [SourceBuffer.Legal, SourceBuffer.Enabled, SourceBuffer.step, ignoresPushWait]

example : 1 < (({} : SourceBuffer Nat).run 1 ignoresPushWait).1.occupied := by
  decide

#print axioms ContinuousSourceCreditSafety_holds
#print axioms SourceBuffer.prefix_occupied_le
#print axioms SourceBuffer.take_releases_before_yield
#print axioms SourceBuffer.refill_before_acknowledgement

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.SourceCreditTests
