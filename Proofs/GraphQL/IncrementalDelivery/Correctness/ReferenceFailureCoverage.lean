import Proofs.GraphQL.IncrementalDelivery.Correctness.FailedTaskScopes
import Proofs.GraphQL.IncrementalDelivery.Correctness.Query

/-! Isolate the remaining pure-execution comparison from scheduler and wire reasoning. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics
open Semantics.MixedPaths

-----------------------------------------------------------------------------------------
-- Pure prepared execution versus ordinary response positions
-----------------------------------------------------------------------------------------

/-- Proof-only execution comparison target, independent of schedules and wire IDs.
`reference` is the ordinary response; `response` and `work` are prepared incremental
execution. Every reference position occurs in the successful source inventory or is
explained by a failing task attachment, including null bubbling above that attachment.
This is an intermediate conjecture target, not a public conformance premise.
-/
def PreparedResponseCovers (reference : ResponseValue) (response : Response)
    (work : Work) (containers : Bool)
    : Prop :=
  ∀ path ∈ ResponsePositions.value containers [] reference,
    path
      ∈ ResponsePositions.value containers [] response.data
        ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
              work).flatMap
            (SourceTask.positions containers)
    ∨ ∃ occurrence owners producer payload,
        TaskAt work occurrence owners producer payload
        ∧ payload.failure.isSome = true
        ∧ (payload.path.IsPrefix path
            ∨ reference.isNullAt path = true ∧ path.IsPrefix payload.path)

/-- A pure execution comparison suffices for the full client-facing coverage property.
Witness: successful source positions deliver or inherit a reported scope; failed payloads
have decoded terminal scopes; prefix comparability supplies the null-ancestor case.
No extra scheduler premise is needed. Proving the prepared comparison remains separate.
-/
theorem WorkObservation.addresses_reference
    {paths bound response work result sourceSlices reference containers}
    (observed : WorkObservation response work true result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (seeded
      : WorkCursorSeed (ResponsePositions.listCursors [] response.data) work sourceSlices)
    (source
      : (ResponsePositions.value true [] response.data ++ sourceSlices.flatten).Nodup)
    (comparison : PreparedResponseCovers reference response work containers)
    : result.AddressesResponsePositions containers reference := by
  obtain ⟨slices, scopes, delivered, decoded, addressed⟩ :=
    observed.source_addressed coherent seeded source containers
  refine ⟨slices, scopes, delivered, decoded, ?_⟩
  intro path member
  rcases comparison path member with prepared | failed
  · rcases addressed path prepared with published | reported
    · exact Or.inl published
    · obtain ⟨scope, member, covers⟩ := reported
      exact Or.inr ⟨scope, member, Or.inl covers⟩
  · obtain ⟨occurrence, owners, producer, payload, known, fails, relationship⟩ := failed
    have reported := observed.failedTaskScopes coherent decoded known fails
    rcases relationship with below | bubbled
    · obtain ⟨scope, member, covers⟩ := reported
      exact Or.inr ⟨scope, member, Or.inl (covers.trans below)⟩
    · exact Or.inr (reported_attachment_explains_null reported bubbled.1 bubbled.2)

-----------------------------------------------------------------------------------------
-- Actual queries need only the ordinary-versus-prepared execution certificate
-----------------------------------------------------------------------------------------

/-- Error-free initial query coverage reduces to the pure root-execution comparison.
Witness: the actual query observation supplies the root work history and execution path
certificates; invalid roots contradict initial zero errors. This is a checked dependency
edge, not yet the public theorem's witness: `comparison` remains to be proved by execution.
-/
theorem ResponsePositionsDeliveredOrFailed_of_preparedComparison
    (schema : Schema) (operation : Operation)
    (comparison
      : ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef) variables fuel
          (source : ResolverValue ObjectRef),
          let completed :=
            ((executeRootSelectionSetCore schema resolvers
                (coerceVariableValues operation variables) fuel
                (operation.rootType schema) source operation.selectionSet).run
              0).1
          let response := selectionSetResultToResponse completed.result
          operation.incrementalArgumentsValid variables
          → rootSourceAppliesBool schema operation source = true
          → response.errors = 0
          → ∀ containers,
              PreparedResponseCovers
                (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
                  operation.eraseIncrementalDirectives fuel source).data
                response completed.work containers)
    : ResponsePositionsDeliveredOrFailed schema operation := by
  intro ObjectRef resolvers variables fuel source createWorkQueue result valid conforms observed
    initialZero containers
  have witnessed := queryObservation_workHistory conforms observed
  split at witnessed
  · rename_i applies
    obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet 0
    obtain ⟨slices, seeded, unique⟩ := executeRoot_source_positions schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet 0
    have initial : result.initialErrors
        = (selectionSetResultToResponse
            ((executeRootSelectionSetCore schema resolvers
                (coerceVariableValues operation variables) fuel (operation.rootType schema)
                source operation.selectionSet).run 0).1.result).errors := by
      cases witnessed <;> rfl
    exact witnessed.addresses_reference coherent seeded unique
      (comparison resolvers variables fuel source valid applies (initial ▸ initialZero)
        containers)
  · subst result
    simp [ExecutionObservation.initialErrors] at initialZero

end GraphQL.IncrementalDelivery.Correctness
