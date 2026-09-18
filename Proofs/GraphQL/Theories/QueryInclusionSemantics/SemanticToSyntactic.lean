import Proofs.GraphQL.Theories.QueryInclusion.Completeness

/-! Execution inclusion implies selected-path inclusion on the witness domain. -/

namespace GraphQL
namespace QueryInclusionSemantics

theorem includesSemanticToSyntactic {schema : Schema} {left right : Operation}
    : IncludesSemanticToSyntactic schema left right := by
  intro hschema hleftValid hrightValid hleftFields hrightFields hleftInhabited
    hrightInhabited hincludes
  have hcheck : QueryInclusion.includesBool schema left right = true :=
    QueryInclusion.includesBool_complete_semantic hschema hleftValid hrightValid
      hleftFields hrightFields hleftInhabited hrightInhabited hincludes
  exact QueryInclusion.includesBool_sound hschema hleftValid hrightValid hcheck

theorem includesToIncludesUnannotated {schema : Schema} {left right : Operation}
    : IncludesToIncludesUnannotated schema left right :=
  QueryInclusion.includesToIncludesUnannotated

end QueryInclusionSemantics
end GraphQL
