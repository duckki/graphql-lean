import Proofs.GraphQL.IncrementalDelivery.Correctness.ReleasedStreamAccounting
import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamFailureScopes

/-! Complete stream-only runs have actual scopes for every cancelled descendant. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Choose covering carriers until all tasks are accounted for
-----------------------------------------------------------------------------------------

/-- Coherent stream-only work with local attachments and positive failures has a complete run.
Witness: covering initialization and released-stream accounting, followed by actual
closures. Singleton failure reports propagate through producer attachment prefixes to
cover all cancelled descendants. No complete history or terminal reporting is assumed.
-/
theorem StreamOnly.completeRun_exists {paths bound work}
    (onlyStreams : StreamOnly work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder [] work)
    (positive : ExecutionErrors.WorkPositive work)
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
    exact ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨fun failure => failure.nonempty rfl, Or.inl rfl⟩, by simp, Or.inl rfl⟩
  obtain ⟨groups, streams, initialized, covers⟩ := initialized.covering_exists
  have initial : Explains work groups streams [] (fun _ => .executionGroup []) [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  have deferred : DeferredTasksAccounted work (fun _ => .executionGroup []) [] [] := by
    intro address owners producer payload known
    obtain ⟨node, result, _, impossible, _⟩ := onlyStreams.task known
    obtain ⟨_, _, _, _, _, _, _, shape⟩ := known
    cases shape.symm.trans impossible
  have closed : StreamDependenciesCompleted work [] := by
    intro node dependencies producer known ref member
    rw [(onlyStreams.node known).2] at member
    cases member
  have notified : StreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
      (fun _ => .executionGroup []) [] [] := by
    intro node dependencies producer known ready healthy
    have empty := (onlyStreams.node known).2
    exact DependencyFreeStreamsNotified.initial covers node producer (empty ▸ known) ready healthy
  obtain ⟨tail, next, cuts, accountedHistory, accounted⟩ :=
    account_released_streams coherent initial deferred closed notified
  obtain ⟨closures, _, _, finished, allClosed⟩ := accountedHistory.close_open_refs accounted
    (announcedRefs ((groups ++ streams).map DeliveryNode.ref) ([] ++ tail))
    (fun _ opened => opened.1)
  apply (admissibleRun_exists_iff_reported_history work).mpr
  refine ⟨groups, streams, ([] ++ tail) ++ closures, next, cuts, finished, ?_⟩
  intro occurrence owners producer payload known
  by_cases published : Published next (([] ++ tail) ++ closures) occurrence
  · exact Or.inr published
  · have cancelled := ((accounted _ _ _ _ known).append closures).resolve_right published
    exact Or.inl ⟨cancelled,
      onlyStreams.cancelled_reported coherent under positive finished allClosed cancelled known⟩

end GraphQL.IncrementalDelivery.Correctness
