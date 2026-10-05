import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureAwareSourceCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting

/-! Failed prepared tasks have scopes decoded from actual wire completion notices. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failure payloads cannot publish and must have observable terminal reports
-----------------------------------------------------------------------------------------

/-- Each failing task in a complete observation has a decoded covering failure scope.
Witness: publication provenance excludes failing payloads; the strengthened terminal
contract reports unpublished attachments, and wire mapping preserves each reported scope.
The returned scope comes from the client's ID/notice decoder, not a hidden failure cut.
-/
theorem WorkObservation.failedTaskScopes
    {paths bound response work result scopes}
    (observed : WorkObservation response work true result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (decoded : result.collectFailureScopes = some scopes)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true)
    : ∃ scope ∈ scopes, scope.IsPrefix payload.path := by
  cases observed with
  | single empty => exact False.elim (no_tasks_of_size_zero empty known)
  | incremental groups streams batches _ _ _ finished =>
      obtain ⟨events, matching, failures, explained, terminal, batching⟩ := finished rfl
      have unpublished : ¬Published matching events occurrence := by
        intro published
        have successful := explained.published_succeeds known published
        simp only [successful, Option.isSome_none, Bool.false_eq_true] at fails
      exact replayResponse_unpublishedScope coherent explained terminal batching decoded
        known unpublished

-----------------------------------------------------------------------------------------
-- A reference null may bubble above the exact reported scope
-----------------------------------------------------------------------------------------

/-- A decoded report covering an attachment also explains a null reference ancestor.
Witness: two prefixes of one attachment are comparable. The report either covers the
reference path directly or lies below that null path, exactly the public bubbling case.
-/
theorem reported_attachment_explains_null {scopes : List ResponsePath}
    {reference : ResponseValue} {path attachment : ResponsePath}
    (reported : ∃ scope ∈ scopes, scope.IsPrefix attachment)
    (isNull : reference.isNullAt path = true)
    (above : path.IsPrefix attachment)
    : ∃ scope ∈ scopes,
        scope.IsPrefix path ∨ reference.isNullAt path = true ∧ path.IsPrefix scope := by
  obtain ⟨scope, member, covers⟩ := reported
  exact ⟨scope, member,
    (List.prefix_or_prefix_of_prefix covers above).imp id (fun below => ⟨isNull, below⟩)⟩

end GraphQL.IncrementalDelivery.Correctness
