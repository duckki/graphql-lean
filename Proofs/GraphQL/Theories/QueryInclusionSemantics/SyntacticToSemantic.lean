import Proofs.GraphQL.Theories.ResponsePath.OperationToReferenceChecker
import Proofs.GraphQL.Theories.QueryInclusion.Soundness

/-! Selected-path inclusion implies inclusion of error-free executions. -/

namespace GraphQL
namespace QueryInclusionSemantics

theorem includesSyntacticToSemantic {schema : Schema} {left right : Operation}
    : IncludesSyntacticToSemantic schema left right := by
  intro hschema hleftValid hrightValid hpath
  exact QueryInclusion.includes_of_selectionSetChecks hschema hleftValid hrightValid
    (ResponsePath.rootType_eq schema left right) hpath.1
    (ResponsePath.selectionSetChecks_of_includes hschema hleftValid hrightValid hpath)

end QueryInclusionSemantics
end GraphQL
