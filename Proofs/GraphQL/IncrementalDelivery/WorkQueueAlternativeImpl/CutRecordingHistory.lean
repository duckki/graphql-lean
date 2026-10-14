import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecordedErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingCutHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutKeySupply

/-! Construct the fine error ledger from the actual atomic cut, rather than assuming an
independent recording history. Completed actions record before settlement; untouched
actions are cancelled and their still-unrecorded slots omitted. This sequential policy
does not identify ghost slots with native error objects or model asynchronous races.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Record/omit a known available prefix through actual ledger transitions
-----------------------------------------------------------------------------------------

private theorem slots_origin {sibling : Sibling α} {slot : ErrorSlot}
    (member : slot ∈ sibling.errorSlots)
    : slot.1 = sibling.id := by
  obtain ⟨index, _, same⟩ := List.mem_map.mp member
  exact congrArg Prod.fst same.symm

private theorem record_prefix {plan : List (Sibling α)} {state : Recording α}
    (history : RecordingHistory plan state) (slots after : List ErrorSlot)
    (available : state.available = slots ++ after)
    (started : ∀ slot ∈ slots, slot.1 ∈ state.scope.started)
    (live : ∀ slot ∈ slots, slot.1 ∉ state.scope.cancelled.map Sibling.id)
    : ∃ final,
        RecordingHistory plan final
        ∧ final.scope = state.scope
        ∧ final.available = after
        ∧ final.recorded = state.recorded ++ slots
        ∧ final.omitted = state.omitted := by
  induction slots generalizing state with
  | nil => exact ⟨state, history, rfl, available, (List.append_nil _).symm, rfl⟩
  | cons slot rest ih =>
      have recorded : RecordingHistory plan (state.record [] slot (rest ++ after)) :=
        .record history [] (rest ++ after) slot available (started slot (by simp))
          (live slot (by simp))
      obtain ⟨final, valid, scope, available, recordedAll, omitted⟩ := ih recorded rfl
        (fun slot member => started slot (List.mem_cons_of_mem _ member))
        (fun slot member => live slot (List.mem_cons_of_mem _ member))
      refine ⟨final, valid, scope, available, ?_, omitted⟩
      simpa only [Recording.record, List.append_assoc, List.singleton_append]
        using recordedAll

private theorem omit_prefix {plan : List (Sibling α)} {state : Recording α}
    (history : RecordingHistory plan state) (slots after : List ErrorSlot)
    (available : state.available = slots ++ after)
    (cancelled : ∀ slot ∈ slots, slot.1 ∈ state.scope.cancelled.map Sibling.id)
    : ∃ final,
        RecordingHistory plan final
        ∧ final.scope = state.scope
        ∧ final.available = after
        ∧ final.recorded = state.recorded
        ∧ final.omitted = state.omitted ++ slots := by
  induction slots generalizing state with
  | nil => exact ⟨state, history, rfl, available, rfl, (List.append_nil _).symm⟩
  | cons slot rest ih =>
      have omitted : RecordingHistory plan (state.omit [] slot (rest ++ after)) :=
        .omitError history [] (rest ++ after) slot available (cancelled slot (by simp))
      obtain ⟨final, valid, scope, available, recorded, omittedAll⟩ := ih omitted rfl
        (fun slot member => cancelled slot (List.mem_cons_of_mem _ member))
      refine ⟨final, valid, scope, available, recorded, ?_⟩
      simpa only [Recording.omit, List.append_assoc, List.singleton_append]
        using omittedAll

-----------------------------------------------------------------------------------------
-- Construct all completed records before settlement, then cancelled-only omissions
-----------------------------------------------------------------------------------------

private theorem cancel_recording_suffix {plan : List (Sibling α)} {state : Recording α}
    (history : RecordingHistory plan state) (omitted : List (Sibling α))
    (pending : state.scope.pending = omitted) (failed : state.scope.fatal = true)
    (available : state.available = errorSlots omitted)
    : ∃ final,
        RecordingHistory plan final
        ∧ final.scope.pending = []
        ∧ final.available = []
        ∧ final.scope.settled = state.scope.settled
        ∧ final.scope.cancelled = state.scope.cancelled ++ omitted
        ∧ final.recorded = state.recorded
        ∧ final.omitted = state.omitted ++ errorSlots omitted
        ∧ final.scope.actions
          = state.scope.actions ++ omitted.map (fun sibling => .cancel sibling.id) := by
  induction omitted generalizing state with
  | nil => exact ⟨state, history, pending, available, rfl, (List.append_nil _).symm,
      rfl, (List.append_nil _).symm, (List.append_nil _).symm⟩
  | cons sibling rest ih =>
      let cancelled := state.scopeStep (state.scope.cancel [] sibling rest) (.cancel sibling.id)
      have valid : RecordingHistory plan cancelled := .cancel history [] rest sibling pending failed
      obtain ⟨recording, recorded, scope, available, kept, dropped⟩ :=
        omit_prefix valid sibling.errorSlots (errorSlots rest)
          (by simpa only [cancelled, Recording.scopeStep, errorSlots, List.flatMap_cons] using available)
          (fun slot member => by
            simp only [cancelled, Recording.scopeStep, Scope.cancel, List.map_append,
              List.map_singleton]
            exact List.mem_append_right _ (by simp [slots_origin member]))
      have pendingLater : recording.scope.pending = rest := by rw [scope]; rfl
      have failedLater : recording.scope.fatal = true := by rw [scope]; exact failed
      obtain ⟨final, history, complete, accounted, settled, cancelledAll, recordedAll, omittedAll, actions⟩ :=
        ih recorded pendingLater failedLater available
      refine ⟨final, history, complete, accounted, ?_, ?_, ?_, ?_, ?_⟩
      · rw [settled, scope]; rfl
      · simpa only [scope, cancelled, Recording.scopeStep, Scope.cancel, List.append_assoc,
          List.singleton_append] using cancelledAll
      · exact recordedAll.trans kept
      · simpa only [dropped, cancelled, Recording.scopeStep, errorSlots, List.flatMap_cons,
          List.append_assoc] using omittedAll
      · simpa only [scope, cancelled, Recording.scopeStep, Scope.cancel, List.map_cons,
          List.append_assoc, List.singleton_append] using actions

private theorem CutPrefix.recording_history {plan : List (Sibling α)}
    {state : Recording α} {completed omitted : List (Sibling α)}
    (cut : CutPrefix completed omitted) (history : RecordingHistory plan state)
    (pending : state.scope.pending = completed ++ omitted)
    (available : state.available = errorSlots (completed ++ omitted))
    (running : state.scope.fatal = false)
    (unique : ((completed ++ omitted).map Sibling.id).Nodup)
    (fresh : ∀ sibling ∈ completed ++ omitted, sibling.id ∉ state.scope.started)
    (live
      : ∀ sibling ∈ completed ++ omitted,
          sibling.id ∉ state.scope.cancelled.map Sibling.id)
    : ∃ final,
        RecordingHistory plan final
        ∧ final.scope.pending = []
        ∧ final.available = []
        ∧ final.scope.settled = state.scope.settled ++ completed
        ∧ final.scope.cancelled = state.scope.cancelled ++ omitted
        ∧ final.recorded = state.recorded ++ errorSlots completed
        ∧ final.omitted = state.omitted ++ errorSlots omitted
        ∧ final.scope.actions
          = state.scope.actions
            ++ completed.flatMap (fun sibling => [.start sibling.id, .settle sibling.id])
            ++ omitted.map (fun sibling => .cancel sibling.id) := by
  induction cut generalizing state with
  | empty =>
      exact ⟨
        state,
        history,
        pending,
        available,
        (List.append_nil _).symm,
        (List.append_nil _).symm,
        (List.append_nil _).symm,
        (List.append_nil _).symm,
        (by simp)
      ⟩
  | fatal sibling omitted failed =>
      let started := state.scopeStep (state.scope.start sibling.id) (.start sibling.id)
      have start : RecordingHistory plan started := .start history sibling
        (by rw [pending]; simp) running (fresh sibling (by simp))
      obtain ⟨recording, recorded, scope, available, kept, dropped⟩ :=
        record_prefix start sibling.errorSlots (errorSlots omitted)
          (by simpa only [started, Recording.scopeStep, errorSlots, List.flatMap_cons,
            List.flatMap_nil, List.nil_append, List.singleton_append] using available)
          (fun slot member => by simp [started, Recording.scopeStep, Scope.start, slots_origin member])
          (fun slot member => by simpa only [started, Recording.scopeStep, Scope.start,
            (slots_origin member)] using live sibling (by simp))
      let settled := recording.scopeStep (recording.scope.settle [] sibling omitted) (.settle sibling.id)
      have settle : RecordingHistory plan settled := .settle recorded [] omitted sibling
        (by rw [scope]; exact pending) (by rw [scope]; simp [started, Recording.scopeStep, Scope.start])
        (fun slot member => by rw [kept]; exact List.mem_append_right _ member)
      obtain ⟨final, valid, complete, accounted, settledAll, cancelledAll, recordedAll, omittedAll, actions⟩ :=
        cancel_recording_suffix settle omitted rfl
          (by simp [settled, Recording.scopeStep, Scope.settle, failed]) available
      refine ⟨final, valid, complete, accounted, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [settled, Recording.scopeStep, Scope.settle, scope, started,
          Scope.start]
          using settledAll
      · simpa only [settled, Recording.scopeStep, Scope.settle, scope, started,
          Scope.start]
          using cancelledAll
      · simpa only [settled, Recording.scopeStep, kept, started, errorSlots, List.flatMap_cons,
          List.flatMap_nil, List.append_nil] using recordedAll
      · simpa only [settled, Recording.scopeStep, dropped, started] using omittedAll
      · simpa only [settled, Recording.scopeStep, Scope.settle, scope, started, Scope.start,
          List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.append_nil,
          List.singleton_append] using actions
  | success sibling healthy later ih =>
      rename_i tail skipped
      let started := state.scopeStep (state.scope.start sibling.id) (.start sibling.id)
      have start : RecordingHistory plan started := .start history sibling
        (by rw [pending]; simp) running (fresh sibling (by simp))
      obtain ⟨recording, recorded, scope, available, kept, dropped⟩ :=
        record_prefix start sibling.errorSlots (errorSlots (tail ++ skipped))
          (by simpa only [started, Recording.scopeStep, errorSlots, List.flatMap_cons,
            List.cons_append] using available)
          (fun slot member => by simp [started, Recording.scopeStep, Scope.start, slots_origin member])
          (fun slot member => by simpa only [started, Recording.scopeStep, Scope.start,
            (slots_origin member)] using live sibling (by simp))
      let settled := recording.scopeStep
        (recording.scope.settle [] sibling (tail ++ skipped)) (.settle sibling.id)
      have settle : RecordingHistory plan settled := .settle recorded [] (tail ++ skipped) sibling
        (by rw [scope]; exact pending) (by rw [scope]; simp [started, Recording.scopeStep, Scope.start])
        (fun slot member => by rw [kept]; exact List.mem_append_right _ member)
      have ids := unique
      simp only [List.cons_append, List.map_cons, List.nodup_cons] at ids
      have freshLater : ∀ other ∈ tail ++ skipped, other.id ∉ settled.scope.started := by
        intro other member repeated
        simp only [settled, Recording.scopeStep, Scope.settle, scope, started, Scope.start,
          List.mem_append, List.mem_singleton] at repeated
        rcases repeated with old | same
        · exact fresh other (List.mem_cons_of_mem _ member) old
        · exact ids.1 (same ▸ List.mem_map_of_mem member)
      have liveLater : ∀ other ∈ tail ++ skipped,
          other.id ∉ settled.scope.cancelled.map Sibling.id := by
        intro other member
        simpa only [settled, Recording.scopeStep, Scope.settle, scope, started,
          Scope.start]
          using live other (List.mem_cons_of_mem _ member)
      obtain ⟨final, valid, complete, accounted, settledAll, cancelledAll, recordedAll, omittedAll, actions⟩ :=
        ih settle rfl available
          (by simp [settled, Recording.scopeStep, Scope.settle, scope, started, Scope.start,
            running, healthy]) ids.2 freshLater liveLater
      refine ⟨final, valid, complete, accounted, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [settled, Recording.scopeStep, Scope.settle, scope, started, Scope.start,
          List.append_assoc, List.singleton_append] using settledAll
      · simpa only [settled, Recording.scopeStep, Scope.settle, scope, started,
          Scope.start]
          using cancelledAll
      · simpa only [settled, Recording.scopeStep, kept, started, errorSlots, List.flatMap_cons,
          List.append_assoc] using recordedAll
      · simpa only [settled, Recording.scopeStep, dropped, started] using omittedAll
      · simpa only [settled, Recording.scopeStep, Scope.settle, scope, started, Scope.start,
          List.flatMap_cons, List.append_assoc, List.singleton_append, List.cons_append,
          List.nil_append] using actions

-----------------------------------------------------------------------------------------
-- Actual action-cut root: one fine ledger with exact completed/omitted inventories
-----------------------------------------------------------------------------------------

theorem ActionCut.recording_history {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next) (id : Nat)
    : ∃ recording,
        RecordingHistory (completionPlan ((observeActions actions).run supply).1 id)
          recording
        ∧ recording.scope.pending = []
        ∧ recording.available = []
        ∧ recording.scope.settled = completionPlan completed id
        ∧ recording.scope.cancelled
          = completionPlan ((observeActions remaining).run next).1 (id + completed.length)
        ∧ recording.recorded = errorSlots (completionPlan completed id)
        ∧ recording.omitted
          = errorSlots
              (completionPlan ((observeActions remaining).run next).1
                (id + completed.length))
        ∧ recording.scope.actions
          = (completionPlan completed id).flatMap
              (fun sibling => [.start sibling.id, .settle sibling.id])
            ++ (completionPlan ((observeActions remaining).run next).1
                  (id + completed.length)).map
                (fun sibling => .cancel sibling.id) := by
  rw [cut.observed]
  dsimp only
  have shaped := cut.prefix id
  have unique := completionPlan_unique (completed ++ ((observeActions remaining).run next).1) id
  rw [completionPlan_append] at unique ⊢
  obtain ⟨recording, history, complete, accounted, settled, cancelled, recorded, omitted, trace⟩ :=
    shaped.recording_history (RecordingHistory.initial (plan := completionPlan completed id
      ++ completionPlan ((observeActions remaining).run next).1 (id + completed.length)))
      rfl rfl rfl unique (by simp) (by simp)
  exact ⟨
    recording,
    history,
    complete,
    accounted,
    settled,
    cancelled,
    recorded,
    omitted,
    trace
  ⟩

theorem SameData.symm {left right : Result α} (same : SameData left right)
    : SameData right left := by
  cases left <;> cases right <;> simp_all [SameData]

theorem SameData.trans {left middle right : Result α}
    (first : SameData left middle) (second : SameData middle right)
    : SameData left right := by
  cases left <;> cases middle <;> cases right <;> simp_all [SameData]

theorem SameData.eq_of_count {left right : Result α} (same : SameData left right)
    (count : countedErrors left = countedErrors right)
    : left = right := by
  cases left with
  | error errors => cases right <;> simp_all [SameData, countedErrors]
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      cases right with
      | error => simp [SameData] at same
      | ok completed =>
          rcases completed with ⟨value, errors⟩
          simp_all [SameData, countedErrors]

/-- The constructed ledger reports the exact atomic cut result, including prior nullable
counts; the proof does not post-process a supplied native error payload.
-/
theorem ActionCut.recording_observation {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next) (id : Nat)
    : ∃ recording,
        RecordingHistory (completionPlan ((observeActions actions).run supply).1 id)
          recording
        ∧ recording.scope.pending = []
        ∧ recording.available = []
        ∧ recording.recorded = errorSlots (completionPlan completed id)
        ∧ recording.omitted
          = errorSlots
              (completionPlan ((observeActions remaining).run next).1
                (id + completed.length))
        ∧ recording.scope.actions
          = (completionPlan completed id).flatMap
              (fun sibling => [.start sibling.id, .settle sibling.id])
            ++ (completionPlan ((observeActions remaining).run next).1
                  (id + completed.length)).map
                (fun sibling => .cancel sibling.id)
        ∧ recording.observe (completionPlan ((observeActions actions).run supply).1 id)
          = some (foldCompletions List.cons [] completed).result := by
  obtain ⟨recording, history, complete, accounted, settled, cancelled, recorded, omitted, trace⟩ :=
    cut.recording_history id
  obtain ⟨observed, report, data, count, _⟩ := history.complete_observation complete accounted
  have cutData : SameData (foldCompletions List.cons [] completed).result
      (eager (completionPlan ((observeActions actions).run supply).1 id)) := by
    simpa only [executeActions_observed, foldCompletions_cons_result _ id]
      using cut.sameData List.cons []
  have equalCount : countedErrors observed = countedErrors (foldCompletions List.cons [] completed).result := by
    rw [count, recorded, errorSlots_length, foldCompletions_errors List.cons [] completed id]
  have exactResult := (data.trans cutData.symm).eq_of_count equalCount
  exact ⟨
    recording,
    history,
    complete,
    accounted,
    recorded,
    omitted,
    trace,
    exactResult ▸ report
  ⟩

/-- One action cut constructs its fine recording history and compatible key-boundary
map. No independently selected outcome/history or response-equality premise is required.
This is the sequential atomic policy, not a recursively scheduled/native execution.
-/
def AtomicCutWitness : Prop :=
  ∀ (α : Type) (actions : List (StateM Nat (Completion α))) supply id,
    MonotoneAbove supply actions
    → let cut := (observeUntilFatal actions).run supply
      let original := (observeActions actions).run supply
      let plan := completionPlan original.1 id
      ∃ recording,
        RecordingHistory plan recording
        ∧ recording.scope.pending = []
        ∧ recording.available = []
        ∧ recording.recorded = errorSlots (completionPlan cut.1.1 id)
        ∧ recording.omitted
          = errorSlots
              (completionPlan ((observeActions cut.1.2).run cut.2).1
                (id + cut.1.1.length))
        ∧ recording.scope.actions
          = (completionPlan cut.1.1 id).flatMap
              (fun sibling => [.start sibling.id, .settle sibling.id])
            ++ (completionPlan ((observeActions cut.1.2).run cut.2).1
                  (id + cut.1.1.length)).map
                (fun sibling => .cancel sibling.id)
        ∧ recording.observe plan = some (foldCompletions List.cons [] cut.1.1).result
        ∧ recording.recorded.length + recording.omitted.length
          = countedErrors (eager plan)
        ∧ (recording.recorded ++ recording.omitted).Nodup
        ∧ SupplyExtension supply cut.2 original.2

theorem atomicCutWitness_holds : AtomicCutWitness := by
  intro α actions supply id monotone
  have cut := observeUntilFatal_cut actions supply
  obtain ⟨recording, history, complete, accounted, recorded, omitted, trace, observed⟩ :=
    cut.recording_observation id
  refine ⟨
    recording,
    history,
    complete,
    accounted,
    recorded,
    omitted,
    trace,
    observed,
    ?_,
    ?_,
    cutSupplyExtension_holds α actions supply monotone
  ⟩
  · simpa only [accounted, List.length_nil, Nat.add_zero] using history.error_accounting
  · simpa only [accounted, List.nil_append]
      using history.slots_unique (completionPlan_unique _ _)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
