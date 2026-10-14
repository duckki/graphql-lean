import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecordedErrors

/-! A pending sibling has already recorded one inner error when a different sibling
fails. Cancellation may omit its remaining error, but must retain the earlier record.
This is a checked finite policy witness, not a claim about an unobserved native run.
-/

namespace AlternativeRecordedErrorChecks

open GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

private def fatal : Sibling String := ⟨0, .error 1⟩
private def nested : Sibling String := ⟨1, .ok ("null", 2)⟩
private def plan := [fatal, nested]

private def initial : Recording String :=
  { scope := { pending := plan }, available := errorSlots plan }

private def firstStarted :=
  initial.scopeStep (initial.scope.start fatal.id) (.start fatal.id)

private def bothStarted :=
  firstStarted.scopeStep (firstStarted.scope.start nested.id) (.start nested.id)

private def earlyError := bothStarted.record [(0, 0)] (1, 0) [(1, 1)]
private def fatalError := earlyError.record [] (0, 0) [(1, 1)]

private def fatalSettled :=
  fatalError.scopeStep (fatalError.scope.settle [] fatal [nested]) (.settle fatal.id)

private def cancelled :=
  fatalSettled.scopeStep (fatalSettled.scope.cancel [] nested []) (.cancel nested.id)

private def complete := cancelled.omit [] (1, 1) []
private def propagated := complete.scopeStep complete.scope.bubble .bubble

private theorem early_record : RecordingHistory plan earlyError := by
  have first : RecordingHistory plan firstStarted :=
    .start .initial fatal (by simp [plan]) rfl (by simp)
  have both : RecordingHistory plan bothStarted :=
    .start first nested (by simp [firstStarted, Recording.scopeStep, Scope.start, initial, plan])
      rfl (by decide)
  exact .record both [(0, 0)] [(1, 1)] (1, 0) rfl (by decide) (by decide)

private theorem complete_history : RecordingHistory plan complete := by
  have recorded : RecordingHistory plan fatalError :=
    .record early_record [] [(1, 1)] (0, 0) rfl (by decide) (by decide)
  have settled : RecordingHistory plan fatalSettled :=
    .settle recorded [] [nested] fatal rfl (by decide) (by
      intro slot member
      simp [fatal, Sibling.errorSlots, countedErrors] at member
      subst slot
      decide)
  have cut : RecordingHistory plan cancelled :=
    .cancel settled [] [] nested rfl rfl
  exact .omitError cut [] [] (1, 1) rfl (by decide)

-- The early error occurs while the nested response position is still pending.
example : earlyError.scope.pending = plan := rfl
example : earlyError.scope.settled = [] := rfl
example : earlyError.recorded = [(1, 0)] := rfl

-- Cancelled response positions can contain recorded and unrecorded errors simultaneously.
example : complete.scope.cancelled = [nested] := rfl
example : complete.recorded = [(1, 0), (0, 0)] := rfl
example : complete.omitted = [(1, 1)] := rfl
example : complete.scope.reportedErrors = 1 := rfl
example : complete.observe plan = some (.error 2) := rfl
example : countedErrors (eager plan) = 3 := rfl

example
    : complete.recorded.length + complete.omitted.length = countedErrors (eager plan) :=
  complete_history.error_accounting

example : ∀ slot ∈ complete.omitted, slot.1 ∈ complete.scope.cancelled.map Sibling.id :=
  complete_history.omitted_cancelled

example : (complete.available ++ complete.recorded ++ complete.omitted).Nodup :=
  complete_history.slots_unique (by decide)

example
    : ∃ observed,
        complete.observe plan = some observed
        ∧ SameData observed (eager plan)
        ∧ countedErrors observed = complete.recorded.length
        ∧ countedErrors observed + complete.omitted.length = countedErrors (eager plan) :=
  complete_history.complete_observation rfl rfl

-- Bubbling changes the ordered scope trace but records no additional originating error.
example : RecordingHistory plan propagated := .bubble complete_history rfl
example : propagated.observe plan = complete.observe plan := rfl
example : propagated.recorded = complete.recorded := rfl

example
    : complete.actions
      = [
        .scope (.start 0),
        .scope (.start 1),
        .record (1, 0),
        .record (0, 0),
        .scope (.settle 0),
        .scope (.cancel 1),
        .omit (1, 1)
      ] :=
  rfl

#print axioms errorSlots_unique
#print axioms RecordingHistory.scope_history
#print axioms RecordingHistory.scope_actions
#print axioms RecordingHistory.recorded_trace
#print axioms RecordingHistory.error_accounting
#print axioms RecordingHistory.complete_observation
#print axioms complete_history

end AlternativeRecordedErrorChecks
