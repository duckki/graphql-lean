import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginRecordingDerivation

/-! Recording histories constructed from primitive/cut derivations. One report
gets one history, including its nested synchronous calls. Future task/item reports
are handled separately; a pure future outcome is not an already-recorded error. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution

def ReportRecording (cut eager : Report α) : Prop :=
  ∃ actions omitted,
    OriginReplay eager.origins {} (actions ++ [.settle cut.origins])
      ⟨cut.origins, cut.origins, omitted⟩
    ∧ (cut.origins ++ omitted).Perm eager.origins
    ∧ RecordingDerivation cut eager (actions ++ [.settle cut.origins])

theorem ReportRecording.of_replay {cut eager : Report α} {actions omitted}
    (replay : OriginReplay eager.origins {} actions ⟨cut.origins, cut.origins, omitted⟩)
    (partition : (cut.origins ++ omitted).Perm eager.origins)
    (derived : RecordingDerivation cut eager actions)
    : ReportRecording cut eager :=
  ⟨
    actions,
    omitted,
    replay.append (.cons (.settle _ _ (.refl _)) (.nil _)),
    partition,
    derived.settle
  ⟩

theorem ReportRecording.map (f : α → β) {cut eager : Report α}
    (known : ReportRecording cut eager)
    : ReportRecording (cut.map f) (eager.map f) := by
  obtain ⟨actions, omitted, replay, partition, derived⟩ := known
  exact ⟨actions, omitted, replay, partition, derived.map f⟩

theorem ReportRecording.catchNull (f : α → ResponseValue) {cut eager : Report α}
    (known : ReportRecording cut eager)
    : ReportRecording (cut.catchNull f) (eager.catchNull f) := by
  obtain ⟨actions, omitted, replay, partition, derived⟩ := known
  exact ⟨actions, omitted, replay, partition, derived.catchNull f⟩

theorem ReportRecording.bubble (route : List Nat) {cut eager : Report ResponseValue}
    (known : ReportRecording cut eager) (left : (cut.nonNull route).origins = cut.origins)
    (right : (eager.nonNull route).origins = eager.origins)
    : ReportRecording (cut.nonNull route) (eager.nonNull route) := by
  obtain ⟨actions, omitted, replay, partition, derived⟩ := known
  apply ReportRecording.of_replay
    (actions := (actions ++ [.settle cut.origins]) ++ [.bubble cut.origins]) (omitted := omitted)
  · rw [left, right]
    exact replay.append (.cons (.bubble _ _ (.refl _)) (.nil _))
  · simpa only [left, right] using partition
  · exact derived.nonNullKeep route left right

theorem ReportRecording.combine (f : α → β → γ)
    {cut eager : Report α} {rest eagerRest : Report β}
    (head : ReportRecording cut eager) (tail : ReportRecording rest eagerRest)
    (unique : (eager.origins ++ eagerRest.origins).Nodup)
    : ReportRecording (Report.combine f cut rest) (Report.combine f eager eagerRest) := by
  obtain ⟨actions, omitted, history, partition, derived⟩ := head
  obtain ⟨laterActions, laterOmitted, laterHistory, laterPartition, laterDerived⟩ := tail
  have apart := (List.nodup_append.mp unique).2.2
  have used : ∀ origin ∈ cut.origins ++ omitted, origin ∈ eager.origins :=
    fun origin member => partition.mem_iff.mp member
  have advanced := history.enlarge (eager.origins ++ eagerRest.origins)
    (fun origin member => List.mem_append_left _ member)
  have next := laterHistory.frame (eager.origins ++ eagerRest.origins)
    ⟨cut.origins, cut.origins, omitted⟩ (fun origin member => List.mem_append_right _ member) (by
      intro origin member
      have outside : origin ∉ eager.origins := fun earlier => apart origin earlier origin member rfl
      exact ⟨fun earlier => outside (used origin (List.mem_append_left _ earlier)),
        fun earlier => outside (used origin (List.mem_append_left _ earlier)),
        fun earlier => outside (used origin (List.mem_append_right _ earlier))⟩)
  simp only [OriginLedger.frame, List.append_nil] at next
  have combined := advanced.append next
  apply ReportRecording.of_replay (actions := (actions ++ [.settle cut.origins])
    ++ (laterActions ++ [.settle rest.origins])) (omitted := omitted ++ laterOmitted)
  · simpa only [OriginLedger.frame, Report.combine] using combined
  · change ((cut.origins ++ rest.origins) ++ (omitted ++ laterOmitted)).Perm
      (eager.origins ++ eagerRest.origins)
    have swapped : ((cut.origins ++ rest.origins) ++ (omitted ++ laterOmitted)).Perm
        ((cut.origins ++ omitted) ++ (rest.origins ++ laterOmitted)) := by
      simpa only [List.append_assoc]
        using (List.perm_append_comm (l₁ := rest.origins) (l₂ := omitted)).append_left
                cut.origins
        |>.append_right laterOmitted
    exact swapped.trans (partition.append laterPartition)
  · exact derived.combine f laterDerived

theorem ReportRecording.fatalCut (f : α → β → γ) (wrap : α → γ) {cut eagerHead : Report α}
    (eagerTail : Report β) (route : List Nat) (errors : Nat)
    (head : ReportRecording cut eagerHead) (fatal : cut.outcome = .error errors)
    (positive : 0 < errors) (headScope : Scoped (route ++ [0]) cut.origins)
    (tailScope : Scoped (route ++ [1]) eagerTail.origins)
    (unique : (eagerHead.origins ++ eagerTail.origins).Nodup)
    : ReportRecording (cut.map wrap) (Report.combine f eagerHead eagerTail) := by
  obtain ⟨actions, omitted, history, partition, derived⟩ := head
  have apart := (List.nodup_append.mp unique).2.2
  have advanced := history.enlarge (eagerHead.origins ++ eagerTail.origins)
    (fun origin member => List.mem_append_left _ member)
  have cancel : OriginStep (eagerHead.origins ++ eagerTail.origins)
      ⟨cut.origins, cut.origins, omitted⟩ (.cancel ⟨route ++ [1], errors⟩ eagerTail.origins)
      ⟨cut.origins, cut.origins, omitted ++ eagerTail.origins⟩ := by
    apply OriginStep.cancel _ _ _ positive tailScope.unique
      (fun origin member => List.mem_append_right _ member) tailScope.within
    · intro origin member recorded
      exact Scoped.separated route origin.1 (headScope.within origin recorded) (tailScope.within origin member)
    · intro origin member earlier
      exact apart origin (partition.mem_iff.mp (List.mem_append_right _ earlier)) origin member rfl
  apply ReportRecording.of_replay
    (actions :=
      (actions ++ [.settle cut.origins])
      ++ [.cancel ⟨route ++ [1], errors⟩ eagerTail.origins])
    (omitted := omitted ++ eagerTail.origins)
  · exact advanced.append (.cons cancel (.nil _))
  · simpa only [Report.map, Report.combine, List.append_assoc] using partition.append_right eagerTail.origins
  · exact derived.fatalCut f wrap eagerTail route errors fatal positive headScope tailScope

/-- Non-null introduces a primitive only for a previously error-free null.
Otherwise it propagates the exact existing references, including prior errors. -/
theorem ReportRefines.nonNull_origins_cases (route : List Nat)
    {cut eager : Report ResponseValue} (known : ReportRefines cut eager)
    : ((cut.nonNull route).origins = cut.origins
        ∧ (eager.nonNull route).origins = eager.origins)
      ∨ (cut.origins = []
          ∧ eager.origins = []
          ∧ (cut.nonNull route).origins = primitiveOrigins route 1
          ∧ (eager.nonNull route).origins = primitiveOrigins route 1) := by
  obtain ⟨cut, cutOrigins, cutAccounts⟩ := cut
  obtain ⟨eager, eagerOrigins, eagerAccounts⟩ := eager
  rcases cut with errors | ⟨value, errors⟩
  <;> rcases eager with eagerErrors | ⟨eagerValue, eagerErrors⟩
  <;> simp_all only [ReportRefines, ScheduledErrors.ResultRefines,
    ScheduledErrors.SameData, ScheduledErrors.countedErrors, false_and]
  · exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨⟨rfl, bounded, zero⟩, origins⟩ := known
    cases value <;> cases errors <;> cases eagerErrors <;>
      simp_all [Report.nonNull, Report.fault, ScheduledErrors.countedErrors]
    have cutEmpty : cutOrigins = [] := List.length_eq_zero_iff.mp cutAccounts
    have eagerEmpty : eagerOrigins = [] := List.length_eq_zero_iff.mp eagerAccounts
    exact Or.inr ⟨cutEmpty, eagerEmpty⟩

theorem ReportCutTrace.recording {cut eager : Report α} (trace : ReportCutTrace cut eager)
    (unique : eager.origins.Nodup)
    : ReportRecording cut eager := by
  induction trace with
  | pure value =>
      exact ReportRecording.of_replay (.nil _) (.refl _) (.pure value)
  | fault route outcome =>
      apply ReportRecording.of_replay (primitiveActions_replay _ unique)
      · simpa only [List.append_nil] using List.Perm.refl (Report.fault route outcome).origins
      · exact .fault route outcome
  | combine f head tail ihHead ihTail =>
      exact (ihHead (List.nodup_append.mp unique).1).combine f
        (ihTail (List.nodup_append.mp unique).2.1) unique
  | map f child ih => exact (ih unique).map f
  | catchNull f child ih => exact (ih unique).catchNull f
  | nonNull route child ih =>
      rcases child.refines.nonNull_origins_cases route with unchanged | fresh
      · exact (ih (unchanged.2 ▸ unique)).bubble route unchanged.1 unchanged.2
      · obtain ⟨cutEmpty, eagerEmpty, cutNew, eagerNew⟩ := fresh
        obtain ⟨actions, omitted, history, partition, derived⟩ := ih (by simp [eagerEmpty])
        have omittedEmpty : omitted = [] := by
          have length := partition.length_eq
          simp [cutEmpty, eagerEmpty] at length
          exact length
        rw [cutEmpty, eagerEmpty, omittedEmpty] at history
        have before := history.enlarge (primitiveOrigins route 1) (by simp)
        have minted := primitiveActions_replay (primitiveOrigins route 1) (Scoped.primitive route 1).unique
        apply ReportRecording.of_replay
          (actions := (actions ++ [.settle []]) ++ primitiveActions (primitiveOrigins route 1)) (omitted := [])
        · rw [cutNew, eagerNew]
          exact before.append minted
        · rw [cutNew, eagerNew, List.append_nil]
        · simpa only [cutEmpty] using derived.nonNullFresh route cutEmpty eagerEmpty cutNew eagerNew
  | fatalCut f wrap eagerTail route errors head fatal positive headScope tailScope ih =>
      exact (ih (List.nodup_append.mp unique).1).fatalCut f wrap eagerTail route errors
        fatal positive headScope tailScope unique

/-- The reported count is the cardinality of this history's actual record
events. Its difference from eager is exactly its omitted inventory. -/
theorem ReportRecording.observation {cut eager : Report α}
    (known : ReportRecording cut eager)
    : ∃ actions omitted,
        OriginReplay eager.origins {} actions ⟨cut.origins, cut.origins, omitted⟩
        ∧ RecordingDerivation cut eager actions
        ∧ actions.filterMap OriginAction.recorded? = cut.origins
        ∧ (actions.filterMap OriginAction.recorded?).length
          = ScheduledErrors.countedErrors cut.outcome
        ∧ ScheduledErrors.countedErrors cut.outcome + omitted.length
          = ScheduledErrors.countedErrors eager.outcome := by
  obtain ⟨actions, omitted, history, partition, derived⟩ := known
  have recorded : (actions ++ [OriginAction.settle cut.origins]).filterMap OriginAction.recorded?
      = cut.origins := by simpa only [List.nil_append] using history.recorded_trace.symm
  refine ⟨actions ++ [.settle cut.origins], omitted, history, derived, recorded, ?_, ?_⟩
  · rw [recorded, cut.accounts]
  · simpa only [List.length_append, cut.accounts, eager.accounts] using partition.length_eq

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
