import Proofs.GraphQL.Execution.InputValues
import Proofs.GraphQL.Theories.AnnotatedExecution
import Proofs.GraphQL.Theories.ExecutionReadiness.ArgumentDefaults
import Proofs.GraphQL.Theories.QueryInclusion.ErrorFreeExecution

/-! Semantic existence of an error-free execution from the readiness predicates. -/

namespace GraphQL

theorem executionReadiness_sound {schema : Schema} {operation : Operation}
    : ExecutionReadinessSound schema operation := by
  intro hschema hvalid hinhabited hdefaults
  obtain ⟨values, hvalues⟩ := Execution.exists_variablesHaveNonNullValues hschema
    (Validation.operationDefinitionValid_variableDefinitionsValid hvalid)
  have hcoercion := ExecutionReadiness.operationArgumentsCoercible_of_defaults
    hschema hvalid hvalues hdefaults
  obtain ⟨fields, hfields⟩ := QueryInclusion.executeQueryAnnotated_supported schema values
    operation hschema hvalid hcoercion hinhabited
  refine ⟨PUnit, QueryInclusion.supportedResolvers schema, values, PUnit.unit, ?_⟩
  have herasure := AnnotatedExecution.executeQueryAnnotated_toResponse schema
    (QueryInclusion.supportedResolvers schema) values operation
    (.object (operation.rootType schema) PUnit.unit)
  simpa only [hfields, AnnotatedExecution.AnnotatedResponse.toResponse]
    using congrArg Execution.Response.errors herasure.symm

end GraphQL
