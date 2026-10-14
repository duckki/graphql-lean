import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LazyComputation

/-! Pin lazy construction, cached reads and late promise callbacks, including the
negative boundary: abort does not guarantee a permanently rejected cache.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.LazyComputationTests

example : LazyComputationOptimization := LazyComputationOptimization_holds

example (started : ComputationResult Nat String)
    : (⟨none, true, false⟩ : CachedComputation Nat String).run
        [.abort "stop", .prime started]
      = (⟨some (.rejected "stop"), true, false⟩, []) :=
  CachedComputation.abort_before_prime true "stop" started

example (state : CachedComputation Nat String)
    (first later : ComputationResult Nat String)
    : (state.prime first).1.prime later = ((state.prime first).1, []) :=
  state.prime_twice first later

-- A fulfilled value is opaque: cleanup must not erase data/errors/nested work in that value.
example (result : Execution.Work)
    : ((⟨some (.fulfilled result), true, false⟩
        : CachedComputation Execution.Work String).abort
        "stop").1.cache
      = some (.fulfilled result) :=
  CachedComputation.abort_fulfilled _ result rfl "stop"

example (state : CachedComputation Nat String)
    (invoked : .abortCallback ∈ (state.abort "stop").2)
    : (state.abort "stop").1.abortAvailable = false
      ∧ ∀ later, ((state.abort "stop").1.abort later).2 = [] :=
  state.abort_callback_disabled "stop" invoked

example
    : let observed :=
        ({} : CachedComputation Nat String).run
          [
            .prime .pending,
            .abort "stop",
            .settle (.ok 7),
            .abort "again",
            .prime (.fulfilled 9)
          ]
      observed.1.cache = some (.fulfilled 7)
      ∧ observed.2 = [.evaluate, .abortCallback] := by
  simp [CachedComputation.run, CachedComputation.step, CachedComputation.prime,
    CachedComputation.abort, CachedComputation.settle, ComputationResult.isPending]

-- Deliberately reject the tempting but false invariant that abort permanently poisons cache.
example
    : let observed :=
        ({} : CachedComputation Nat String).run
          [.prime .pending, .abort "stop", .settle (.ok 7)]
      observed.1.cache ≠ some (.rejected "stop") := by
  simp [CachedComputation.run, CachedComputation.step, CachedComputation.prime,
    CachedComputation.abort, CachedComputation.settle, ComputationResult.isPending]

example
    : let observed :=
        (⟨none, false, false⟩ : CachedComputation Nat String).run
          [.prime .pending, .abort "stop", .settle (.error "late"), .abort "again"]
      observed.1.cache = some (.rejected "late") ∧ observed.2 = [.evaluate] := by
  simp [CachedComputation.run, CachedComputation.step, CachedComputation.prime,
    CachedComputation.abort, CachedComputation.settle, ComputationResult.isPending]

example (cursor : ResponseStreamCursor) (toBatch : Nat → List GraphEvent)
    : let observed :=
        ({} : CachedComputation Nat String).run
          [.prime .pending, .abort "stop", .settle (.ok 7), .abort "stop"]
      observed.1.cache = some (.fulfilled 7)
      ∧ observed.2 = [.evaluate, .abortCallback]
      ∧ cursor.close.1.handleBatch (toBatch 7) = (none, cursor.close.1, []) :=
  CachedComputation.late_fulfilment_closed_reader "stop" 7 cursor toBatch

#print axioms LazyComputationOptimization_holds
#print axioms CachedComputation.abort_before_prime
#print axioms CachedComputation.abort_callback_disabled
#print axioms CachedComputation.pending_abort_late_fulfilment
#print axioms CachedComputation.late_fulfilment_closed_reader

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.LazyComputationTests
