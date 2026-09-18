import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamContinuation

/-! Account for initially covered root deferred tasks without consuming success carriers.
This restricted existential phase is proof machinery, not a scheduler admission rule.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Reserve successful closures while publishing deferred values
-----------------------------------------------------------------------------------------

/-- This construction permits deferred publications and failure notifications only.
It emits neither successful completions nor stream values, reserving notice carriers.
-/
def DeferredPhaseEvent : WorkEvent → Prop
  | .groupValues _ _ | .groupFailure _ _ | .streamFailure _ _ => True
  | _ => False

/-- A phase event has no newly announced keys. Witness: its three permitted event forms.
-/
theorem DeferredPhaseEvent.no_notices {event} (phase : DeferredPhaseEvent event)
    : eventPending event = [] := by
  cases event <;> simp_all [DeferredPhaseEvent, eventPending]

/-- Every key closed during this phase has actually failed. Witness: inspect its allowed
failure completion and transport the causal failure to the final output boundary.
-/
theorem deferredPhase_completed_failed {work groups streams events matching failures key}
    (explained : Explains work groups streams events matching failures)
    (phase : ∀ event ∈ events, DeferredPhaseEvent event)
    (closed : key ∈ completedKeys events)
    : NodeFailed work (failedBefore failures events.length) key := by
  obtain ⟨event, member, completes⟩ := List.mem_flatMap.mp closed
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  have bound := Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1
  have allowed := explained.2.2 index event selected
  have permitted := phase event member
  cases event <;>
    simp only [DeferredPhaseEvent, eventCompleted, List.mem_singleton,
      List.not_mem_nil] at permitted completes
  all_goals try contradiction
  all_goals subst key
  all_goals exact allowed.2.2.1.mono (failedBefore_subset failures bound)

/-- Every initially announced healthy key remains open after the phase. Witness: phase
closures require failure, while initial notice membership persists throughout a history.
-/
theorem deferredPhase_healthy_open {work groups streams events matching failures key}
    (explained : Explains work groups streams events matching failures)
    (phase : ∀ event ∈ events, DeferredPhaseEvent event)
    (initial : key ∈ (groups ++ streams).map DeliveryNode.key)
    (healthy : ¬NodeFailed work (failedBefore failures events.length) key)
    : Open ((groups ++ streams).map DeliveryNode.key) events key :=
  ⟨
    List.mem_append_left _ initial,
    fun closed => healthy (deferredPhase_completed_failed explained phase closed)
  ⟩

-----------------------------------------------------------------------------------------
-- Every ready announced deferred task can advance within the phase
-----------------------------------------------------------------------------------------

/-- A ready deferred task with an announced healthy owner has a phase-compatible step.
Witness: publish its object value once under an available owner, or record its actual
failure and emit a counted failure completion. Neither case consumes a success carrier.
-/
theorem extend_deferred_phase
    {paths bound work groups streams events matching failures address owners producer
      payload}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work (.deferred address) owners producer payload)
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          (.deferred address) producer)
    (announced
      : ∃ key ∈ owners,
          key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events
          ∧ ¬NodeFailed work (failedBefore failures events.length) key)
    : ∃ event next cuts,
        Explains work groups streams (events ++ [event]) next cuts
        ∧ DeferredPhaseEvent event := by
  obtain ⟨key, member, notified, healthy⟩ := announced
  have opened : Open ((groups ++ streams).map DeliveryNode.key) events key := by
    refine ⟨notified, ?_⟩
    intro closed
    rcases explained.completed_accounted closed with failed | accounted
    · exact healthy failed
    · rcases accounted (.deferred address) owners ⟨producer, payload, known⟩ member
        with cancelled | published
      · exact ready.2.1 cancelled
      · exact ready.1 published
  cases StructuralEquivalence.taskAt_of_current known with
  | @deferred address fragments path result children producer enclosing located =>
      cases result with
      | error errors =>
          obtain ⟨node, count, event, _, control, _, extended⟩ :=
            explained.failure_step known rfl (ready.reachable explained known)
              ⟨key, member, opened⟩
              (by simpa only [explained.2.1.failedBefore_eq (Nat.le_refl _)]
                using ready.2.1)
          refine ⟨event, matching, _, extended, ?_⟩
          rcases control with rfl | rfl <;> trivial
      | ok value =>
          obtain ⟨data, errors⟩ := value
          obtain ⟨node, kind, parents, birth, nodeKnown, same⟩ := known.owner_known member
          obtain ⟨owner, selected⟩ := owner_exists_of_available coherent known
            ⟨node, ⟨kind, parents, birth, nodeKnown⟩, same ▸ member, same ▸ opened,
              same ▸ healthy⟩
          exact ⟨_, _, _, explained.publish_object known ready selected, trivial⟩

-----------------------------------------------------------------------------------------
-- Finite completion of the initially covered deferred phase
-----------------------------------------------------------------------------------------

/-- Initially covered producer-free deferred tasks can all be accounted for without
successful closures or stream publications. Witness: a maximal finite phase; every
outstanding deferred task is ready and has an announced healthy owner, so can extend it.
Arbitrarily many tasks and shared owner keys are allowed; nested deferred producers are
not covered by the producer-free premise. No history or terminal-run premise is supplied.
-/
theorem finish_root_deferred_tasks {paths bound work groups streams}
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (initialized : Initializes work groups streams)
    (roots
      : ∀ address owners producer payload,
          TaskAt work (.deferred address) owners producer payload → producer = none)
    (covered
      : ∀ address owners producer payload,
          TaskAt work (.deferred address) owners producer payload
          → owners ≠ [] ∧ ∀ key ∈ owners, key ∈ (groups ++ streams).map DeliveryNode.key)
    : ∃ events matching failures,
        Explains work groups streams events matching failures
        ∧ (∀ event ∈ events, DeferredPhaseEvent event)
        ∧ DeferredTasksAccounted work matching events (failures.map Prod.snd)
        ∧ ∀ key ∈ (groups ++ streams).map DeliveryNode.key,
            ¬NodeFailed work (failures.map Prod.snd) key
            → Open ((groups ++ streams).map DeliveryNode.key) events key := by
  classical
  have initial : Explains work groups streams [] (fun _ => .deferred []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  obtain ⟨events, matching, failures, explained, phase, maximal⟩ :=
    initial.maximal_extension_preserving
      (fun events _ _ => ∀ event ∈ events, DeferredPhaseEvent event) (by simp)
  simp only [List.nil_append] at explained phase maximal
  have stable := explained.2.1.failedBefore_eq (Nat.le_refl _)
  refine ⟨events, matching, failures, explained, phase, ?_, ?_⟩
  · intro address owners producer payload known
    rw [← stable]
    apply Classical.byContradiction
    intro outstanding
    have root := roots address owners producer payload known
    subst producer
    have ready : CanPublish work matching events (failedBefore failures events.length)
        (.deferred address) none :=
      ⟨fun published => outstanding (Or.inr published),
        fun cancelled => outstanding (Or.inl cancelled), by simp, trivial⟩
    obtain ⟨nonempty, notices⟩ := covered address owners none payload known
    obtain ⟨key, member, healthy, _⟩ := explained.outstanding_owner known nonempty outstanding
    obtain ⟨event, next, cuts, extended, permitted⟩ := extend_deferred_phase coherent
      explained known ready ⟨key, member, List.mem_append_left _ (notices key member), healthy⟩
    have impossible := maximal [event] next cuts extended (by
      intro other inEvents
      rcases List.mem_append.mp inEvents with earlier | last
      · exact phase other earlier
      · exact List.mem_singleton.mp last ▸ permitted)
    cases impossible
  · intro key member healthy
    exact deferredPhase_healthy_open explained phase member (stable ▸ healthy)

end GraphQL.IncrementalDelivery.Correctness
