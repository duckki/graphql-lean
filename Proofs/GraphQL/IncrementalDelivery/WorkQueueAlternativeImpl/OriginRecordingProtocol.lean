import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveCutTrace

/-! A finite primitive-origin recording protocol. Starts, records, skipped
suffixes and aggregate settlement are distinct. Records never disappear;
cancellation can affect only unstarted origins. This is a ghost protocol for
the sequential cut policy, not a model of native asynchronous resolver starts. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

inductive OriginAction where
  | start (origin : Origin)
  | record (origin : Origin)
  | cancel (site : SiblingCut) (origins : List Origin)
  | settle (origins : List Origin)
  | bubble (origins : List Origin)
deriving Repr

structure OriginLedger where
  started : List Origin := []
  recorded : List Origin := []
  omitted : List Origin := []
deriving Repr

def OriginLedger.frame (prior state : OriginLedger) : OriginLedger :=
  ⟨
    prior.started ++ state.started,
    prior.recorded ++ state.recorded,
    prior.omitted ++ state.omitted
  ⟩

inductive OriginStep (plan : List Origin)
    : OriginLedger → OriginAction → OriginLedger → Prop where
  | start (state : OriginLedger) (origin : Origin) (member : origin ∈ plan)
    (fresh : origin ∉ state.started) (uncancelled : origin ∉ state.omitted)
    : OriginStep plan state (.start origin)
        { state with started := state.started ++ [origin] }
  | record (state : OriginLedger) (origin : Origin) (member : origin ∈ plan)
    (started : origin ∈ state.started) (fresh : origin ∉ state.recorded)
    : OriginStep plan state (.record origin)
        { state with recorded := state.recorded ++ [origin] }
  | cancel (state : OriginLedger) (site : SiblingCut) (origins : List Origin)
    (positive : 0 < site.errors) (unique : origins.Nodup)
    (member : ∀ origin ∈ origins, origin ∈ plan)
    (within : ∀ origin ∈ origins, site.tailRoute.IsPrefix origin.1)
    (unstarted : ∀ origin ∈ origins, origin ∉ state.started)
    (fresh : ∀ origin ∈ origins, origin ∉ state.omitted)
    : OriginStep plan state (.cancel site origins)
        { state with omitted := state.omitted ++ origins }
  | settle (state : OriginLedger) (origins : List Origin)
    (recorded : origins.Sublist state.recorded)
    : OriginStep plan state (.settle origins) state
  | bubble (state : OriginLedger) (origins : List Origin)
    (recorded : origins.Sublist state.recorded)
    : OriginStep plan state (.bubble origins) state

inductive OriginReplay (plan : List Origin)
    : OriginLedger → List OriginAction → OriginLedger → Prop where
  | nil (state) : OriginReplay plan state [] state
  | cons {before middle after action actions}
    (step : OriginStep plan before action middle)
    (rest : OriginReplay plan middle actions after)
    : OriginReplay plan before (action :: actions) after

theorem OriginReplay.append {plan before middle after actions rest}
    (head : OriginReplay plan before actions middle)
    (tail : OriginReplay plan middle rest after)
    : OriginReplay plan before (actions ++ rest) after := by
  induction head with
  | nil => exact tail
  | cons step head ih => exact .cons step (ih tail)

theorem OriginStep.frame {plan before after action}
    (step : OriginStep plan before action after) (larger : List Origin)
    (prior : OriginLedger) (included : ∀ origin ∈ plan, origin ∈ larger)
    (apart
      : ∀ origin ∈ plan,
          origin ∉ prior.started ∧ origin ∉ prior.recorded ∧ origin ∉ prior.omitted)
    : OriginStep larger (prior.frame before) action (prior.frame after) := by
  cases step with
  | start origin member fresh uncancelled =>
      simpa only [OriginLedger.frame, List.append_assoc]
        using OriginStep.start (prior.frame before) origin (included origin member)
          (by simpa [OriginLedger.frame] using And.intro (apart origin member).1 fresh)
          (by
            simpa [OriginLedger.frame]
              using And.intro (apart origin member).2.2 uncancelled)
  | record origin member started fresh =>
      simpa only [OriginLedger.frame, List.append_assoc]
        using OriginStep.record (prior.frame before) origin (included origin member)
          (List.mem_append_right _ started)
          (by simpa [OriginLedger.frame] using And.intro (apart origin member).2.1 fresh)
  | cancel site origins positive unique member within unstarted fresh =>
      simpa only [OriginLedger.frame, List.append_assoc]
        using OriginStep.cancel (prior.frame before) site origins positive unique
          (fun origin selected => included origin (member origin selected)) within
          (fun origin selected => by
            simpa [OriginLedger.frame]
              using And.intro (apart origin (member origin selected)).1
                (unstarted origin selected))
          (fun origin selected => by
            simpa [OriginLedger.frame]
              using And.intro (apart origin (member origin selected)).2.2
                (fresh origin selected))
  | settle origins recorded =>
      exact .settle _ _ (List.sublist_append_of_sublist_right recorded)
  | bubble origins recorded =>
      exact .bubble _ _ (List.sublist_append_of_sublist_right recorded)

theorem OriginReplay.frame {plan before after actions}
    (history : OriginReplay plan before actions after) (larger : List Origin)
    (prior : OriginLedger) (included : ∀ origin ∈ plan, origin ∈ larger)
    (apart
      : ∀ origin ∈ plan,
          origin ∉ prior.started ∧ origin ∉ prior.recorded ∧ origin ∉ prior.omitted)
    : OriginReplay larger (prior.frame before) actions (prior.frame after) := by
  induction history with
  | nil => exact .nil _
  | cons step rest ih => exact .cons (step.frame larger prior included apart) ih

theorem OriginReplay.enlarge {plan before after actions}
    (history : OriginReplay plan before actions after) (larger : List Origin)
    (included : ∀ origin ∈ plan, origin ∈ larger)
    : OriginReplay larger before actions after := by
  simpa only [OriginLedger.frame, List.nil_append]
    using history.frame larger {} included (by simp)

theorem OriginReplay.records_monotone {plan before after actions}
    (history : OriginReplay plan before actions after)
    : before.recorded.Sublist after.recorded := by
  induction history with
  | nil => exact .refl _
  | cons step rest ih =>
      apply List.Sublist.trans _ ih
      cases step with
      | record => exact List.sublist_append_left _ _
      | start => exact .refl _
      | cancel => exact .refl _
      | settle => exact .refl _
      | bubble => exact .refl _

/-- A recording can never be retroactively removed by cancellation or bubbling. -/
theorem OriginReplay.preserves_record {plan before after actions origin}
    (history : OriginReplay plan before actions after)
    (recorded : origin ∈ before.recorded)
    : origin ∈ after.recorded :=
  history.records_monotone.subset recorded

def primitiveActions (origins : List Origin) : List OriginAction :=
  origins.flatMap (fun origin => [.start origin, .record origin, .settle [origin]])

theorem primitiveActions_replay (origins : List Origin) (unique : origins.Nodup)
    : OriginReplay origins {} (primitiveActions origins) ⟨origins, origins, []⟩ := by
  induction origins with
  | nil => exact .nil _
  | cons origin rest ih =>
      have different := (List.nodup_cons.mp unique).1
      have tail := ih (List.nodup_cons.mp unique).2
      have framed := tail.frame (origin :: rest) ⟨[origin], [origin], []⟩
        (fun selected member => List.mem_cons_of_mem _ member) (by
          intro selected member
          have other : selected ≠ origin := by intro same; subst selected; exact different member
          simp [other])
      simpa only [primitiveActions, List.flatMap_cons, List.singleton_append,
        List.cons_append, List.nil_append, OriginLedger.frame]
        using OriginReplay.cons (OriginStep.start {} origin (by simp) (by simp) (by simp))
          (OriginReplay.cons
            (OriginStep.record ⟨[origin], [], []⟩ origin (by simp) (by simp) (by simp))
            (OriginReplay.cons
              (OriginStep.settle ⟨[origin], [origin], []⟩ [origin] (.refl _)) framed))

def OriginAction.recorded? : OriginAction → Option Origin
  | .record origin => some origin
  | _ => none

theorem OriginReplay.recorded_trace {plan before after actions}
    (history : OriginReplay plan before actions after)
    : after.recorded = before.recorded ++ actions.filterMap OriginAction.recorded? := by
  induction history with
  | nil => simp
  | cons step rest ih =>
      rw [ih]
      cases step <;> simp [List.filterMap_cons, OriginAction.recorded?, List.append_assoc]

theorem OriginReplay.recorded_started {plan before after actions}
    (history : OriginReplay plan before actions after)
    (initial : ∀ origin ∈ before.recorded, origin ∈ before.started)
    : ∀ origin ∈ after.recorded, origin ∈ after.started := by
  induction history with
  | nil => exact initial
  | cons step rest ih =>
      apply ih
      cases step with
      | start => exact fun origin member => List.mem_append_left _ (initial origin member)
      | record origin member started fresh =>
          intro selected present
          rcases List.mem_append.mp present with earlier | latest
          · exact initial selected earlier
          · have same := List.mem_singleton.mp latest
            subst selected
            exact started
      | cancel => exact initial
      | settle => exact initial
      | bubble => exact initial

/-- Even before settlement, a started primitive cannot be cancelled. In
particular every previously recorded origin is excluded from cancellation. -/
theorem OriginStep.cancel_excludes_records {plan before after site origins}
    (step : OriginStep plan before (.cancel site origins) after)
    (known : ∀ origin ∈ before.recorded, origin ∈ before.started)
    : ∀ origin ∈ origins, origin ∉ before.recorded := by
  cases step with
  | cancel site origins positive unique member within unstarted fresh =>
      exact fun origin selected recorded => unstarted origin selected (known origin recorded)

def OriginAction.cancelled : OriginAction → List Origin
  | .cancel _ origins => origins
  | _ => []

theorem OriginReplay.omitted_trace {plan before after actions}
    (history : OriginReplay plan before actions after)
    : after.omitted = before.omitted ++ actions.flatMap OriginAction.cancelled := by
  induction history with
  | nil => simp
  | cons step rest ih =>
      rw [ih]
      cases step <;> simp [List.flatMap_cons, OriginAction.cancelled, List.append_assoc]

theorem OriginReplay.action_boundary {plan before after actions action}
    (history : OriginReplay plan before actions after) (selected : action ∈ actions)
    : ∃ earlier later boundary next,
        actions = earlier ++ action :: later
        ∧ OriginReplay plan before earlier boundary
        ∧ OriginStep plan boundary action next := by
  induction history with
  | nil => simp at selected
  | cons step rest ih =>
      rcases List.mem_cons.mp selected with first | later
      · subst action
        exact ⟨[], _, _, _, rfl, .nil _, step⟩
      · obtain ⟨earlier, later, boundary, next, same, prefixRun, selectedStep⟩ := ih later
        exact ⟨_ :: earlier, later, boundary, next, by simp [same], .cons step prefixRun, selectedStep⟩

/-- Every omitted origin has an actual cancellation event in this same history;
at its boundary the origin has neither started nor been recorded. -/
theorem OriginReplay.omission_boundary {plan after actions origin}
    (history : OriginReplay plan {} actions after) (omitted : origin ∈ after.omitted)
    : ∃ earlier later boundary next site origins,
        actions = earlier ++ OriginAction.cancel site origins :: later
        ∧ OriginReplay plan {} earlier boundary
        ∧ OriginStep plan boundary (.cancel site origins) next
        ∧ origin ∈ origins
        ∧ site.tailRoute.IsPrefix origin.1
        ∧ 0 < site.errors
        ∧ origin ∉ boundary.started
        ∧ origin ∉ boundary.recorded := by
  rw [history.omitted_trace] at omitted
  simp only [List.nil_append] at omitted
  obtain ⟨action, selected, member⟩ := List.mem_flatMap.mp omitted
  cases action <;> simp only [OriginAction.cancelled, List.not_mem_nil] at member
  rename_i site origins
  obtain ⟨earlier, later, boundary, next, same, prior, step⟩ := history.action_boundary selected
  have noRecord := step.cancel_excludes_records (prior.recorded_started (by simp)) origin member
  have inside : site.tailRoute.IsPrefix origin.1 := by
    cases step with
    | cancel site origins positive unique available within unstarted fresh =>
        exact within origin member
  have positive : 0 < site.errors := by cases step; assumption
  have unstarted : origin ∉ boundary.started := by
    cases step with
    | cancel site origins positive unique available within unstarted fresh =>
        exact unstarted origin member
  exact ⟨earlier, later, boundary, next, site, origins, same, prior, step, member,
    inside, positive, unstarted, noRecord⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
