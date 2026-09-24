import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamContinuation
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StreamNotices

/-! Constructive complete-run existence for arbitrarily nested finite stream work.
Stream-item carriers supply notices for new child streams; no complete run is assumed.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Stream-only work has no deferred dependencies
-----------------------------------------------------------------------------------------

/-- The finite work contains streams, combinations, and empty subwork, but no deferred task.
Item outcomes, errors, nesting depth, and branching are unrestricted.
-/
def StreamOnly : Work → Prop
  | .empty => True
  | .combine left right => StreamOnly left ∧ StreamOnly right
  | .executionGroup .. => False
  | .stream _ items => ∀ entry ∈ items, StreamOnly entry.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem ‹entry ∈ items›
  have pairSize : sizeOf entry = 1 + sizeOf entry.1 + sizeOf entry.2 :=
    Prod.mk.sizeOf_spec _ _
  omega

/-- Every location in stream-only work is stream-only and has no enclosing defer keys.
Witness: structural navigation; stream-item edges reset enclosing owners to empty.
-/
theorem StreamOnly.located {work address current producer owners}
    (onlyStreams : StreamOnly work)
    (located : Located work address current producer owners)
    : StreamOnly current ∧ owners = [] := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact ⟨onlyStreams, rfl⟩
  | left _ ih =>
      rw [StreamOnly] at ih
      exact ⟨ih.1.1, ih.2⟩
  | right _ ih =>
      rw [StreamOnly] at ih
      exact ⟨ih.1.2, ih.2⟩
  | executionGroup _ ih => exact False.elim (by simpa only [StreamOnly] using ih.1)
  | item _ entry ih =>
      rw [StreamOnly] at ih
      exact ⟨ih.1 _ (List.mem_of_getElem? entry), rfl⟩

/-- Every stream-only task has a single stream owner without defer dependencies.
Witness: its item descriptor and the empty enclosing-owner context at its location.
-/
theorem StreamOnly.task {work occurrence owners producer payload}
    (onlyStreams : StreamOnly work)
    (known : TaskAt work occurrence owners producer payload)
    : ∃ node result,
        owners = [node.key]
        ∧ payload = .item node result
        ∧ NodeAt work node .stream [] producer := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      exact False.elim
        (by simpa only [StreamOnly] using (onlyStreams.located located.toCurrent).1)
  | item located selected =>
      have empty := (onlyStreams.located located.toCurrent).2
      exact ⟨_, _, rfl, rfl, empty ▸ NodeAt.stream located.toCurrent⟩

/-- A descriptor in stream-only work is a stream with no deferred dependency keys.
Witness: its located boundary cannot be deferred and has an empty owner context.
-/
theorem StreamOnly.node {work node kind dependencies producer}
    (onlyStreams : StreamOnly work)
    (known : NodeAt work node kind dependencies producer)
    : kind = .stream ∧ dependencies = [] := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      exact False.elim
        (by simpa only [StreamOnly] using (onlyStreams.located located.toCurrent).1)
  | stream located => exact ⟨rfl, (onlyStreams.located located.toCurrent).2⟩

/-- Nonempty stream-only subwork has a first stream with the location's producer.
Witness: descend through combine nodes only, stopping before the first stream's items.
-/
theorem StreamOnly.first_stream {work address current producer owners}
    (onlyStreams : StreamOnly current)
    (nonempty : current.size ≠ 0)
    (located : Located work address current producer owners)
    : ∃ node, NodeAt work node .stream owners producer := by
  cases current with
  | empty => exact False.elim (nonempty rfl)
  | executionGroup => simp only [StreamOnly] at onlyStreams
  | stream node items => exact ⟨node, .stream located⟩
  | combine left right =>
      rw [StreamOnly] at onlyStreams
      by_cases empty : left.size = 0
      · apply onlyStreams.2.first_stream (located := .right located)
        simpa only [Work.size, empty, Nat.zero_add] using nonempty
      · exact onlyStreams.1.first_stream empty (.left located)
termination_by sizeOf current

-----------------------------------------------------------------------------------------
-- Choose covering carriers until all tasks are accounted for
-----------------------------------------------------------------------------------------

/-- Every nonempty stream-only work tree with coherent owner paths admits a complete run.
Witness: covering initialization satisfies the released-stream continuation boundary,
since there are no deferred tasks or dependencies. The continuation constructs the
terminal run.
-/
theorem StreamOnly.completeRun_exists {paths bound work}
    (onlyStreams : StreamOnly work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (nonempty : work.size ≠ 0)
    : ∃ history, AdmissibleRun work history := by
  classical
  obtain ⟨node, descriptor⟩ := onlyStreams.first_stream nonempty Located.root
  have initialized : Initializes work [] [node] := by
    refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro stream member
    have same := List.mem_singleton.mp member
    subst stream
    refine ⟨[], none, descriptor, ?_⟩
    exact ⟨by simp [announcedKeys, pendingKeys], fun failure => failure.nonempty rfl,
      Or.inl rfl, by simp, Or.inl rfl⟩
  obtain ⟨groups, streams, initialized, covers⟩ := initialized.covering_exists
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  have deferred : DeferredTasksAccounted work (fun _ => .executionGroup []) [] [] := by
    intro address owners producer payload known
    obtain ⟨node, result, _, impossible, _⟩ := onlyStreams.task known
    obtain ⟨_, _, _, _, _, _, _, shape⟩ := known
    cases shape.symm.trans impossible
  have closed : StreamDependenciesCompleted work [] := by
    intro node dependencies producer known key member
    rw [(onlyStreams.node known).2] at member
    cases member
  have notified : StreamsNotified work ((groups ++ streams).map DeliveryNode.key)
      (fun _ => .executionGroup []) [] [] := by
    intro node dependencies producer known ready healthy
    have empty := (onlyStreams.node known).2
    exact DependencyFreeStreamsNotified.initial covers node producer (empty ▸ known) ready healthy
  obtain ⟨tail, run⟩ := released_streams_run_extension coherent initial deferred closed
    notified WorkBatching.nil
  exact ⟨_, run⟩

end GraphQL.IncrementalDelivery.Correctness
