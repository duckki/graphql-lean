import GraphQL.SchemaWellFormedness

/-!
Directive-definition well-formedness facts.

A schema that declares no directive definitions of its own is well-formed with respect to
directives: the built-in definitions have unique names.
-/

namespace GraphQL.SchemaWellFormedness

theorem directiveDefinitionsWellFormed_of_directives_nil {schema : Schema}
    (hnil : schema.directives = [])
    : directiveDefinitionsWellFormed schema := by
  refine ⟨?_, ?_⟩
  · simp [namesAreUnique, Schema.allDirectives, Schema.builtinDirectiveDefinitions, hnil]
  · simp [hnil]

end GraphQL.SchemaWellFormedness
