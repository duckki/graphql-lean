import GraphQL.Theories.SelectionConditions

/-! Boolean-variable provenance for flat selection conditions. -/

namespace GraphQL
namespace SelectionConditions

def BranchCondition.BooleanVariableWithin (variables : List Name)
    : BranchCondition -> Prop
  | .typeCondition _typeName => True
  | .booleanLiteral literal => literal.variableName ∈ variables

theorem literalsForDirectives_variable_mem
    (directives : List DirectiveApplication) (literals : List BooleanLiteral)
    (hresult : literalsForDirectives directives = some literals)
    (literal : BooleanLiteral) (hliteral : literal ∈ literals)
    : literal.variableName ∈ directives.filterMap directiveBooleanVariable? := by
  induction directives generalizing literals with
  | nil =>
      simp [literalsForDirectives] at hresult
      subst literals
      simp at hliteral
  | cons directive rest ih =>
      rw [literalsForDirectives] at hresult
      cases hhead : literalsForDirective directive with
      | none => simp [hhead] at hresult
      | some head =>
          cases htail : literalsForDirectives rest with
          | none => simp [hhead, htail] at hresult
          | some tail =>
              simp [hhead, htail] at hresult
              subst literals
              simp only [List.mem_append] at hliteral
              rcases hliteral with hliteral | hliteral
              · cases directive with
                | skip ifArgument =>
                    cases ifArgument with
                    | null => simp_all [literalsForDirective]
                    | int value => simp_all [literalsForDirective]
                    | float value => simp_all [literalsForDirective]
                    | string value => simp_all [literalsForDirective]
                    | boolean value =>
                        cases value <;> simp_all [literalsForDirective]
                    | enum value => simp_all [literalsForDirective]
                    | list values => simp_all [literalsForDirective]
                    | object fields => simp_all [literalsForDirective]
                    | «variable» variableName =>
                        simp [literalsForDirective] at hhead
                        subst head
                        simp only [List.mem_singleton] at hliteral
                        subst literal
                        simp [directiveBooleanVariable?, BooleanLiteral.variableName]
                | «include» ifArgument =>
                    cases ifArgument with
                    | null => simp [literalsForDirective] at hhead
                    | int value => simp [literalsForDirective] at hhead
                    | float value => simp [literalsForDirective] at hhead
                    | string value => simp [literalsForDirective] at hhead
                    | boolean value =>
                        cases value <;> simp_all [literalsForDirective]
                    | enum value => simp [literalsForDirective] at hhead
                    | list values => simp [literalsForDirective] at hhead
                    | object fields => simp [literalsForDirective] at hhead
                    | «variable» variableName =>
                        simp [literalsForDirective] at hhead
                        subst head
                        simp only [List.mem_singleton] at hliteral
                        subst literal
                        simp [directiveBooleanVariable?, BooleanLiteral.variableName]
              · have htailVariable := ih tail htail hliteral
                simp only [List.filterMap_cons]
                cases hvariable : directiveBooleanVariable? directive <;>
                  simp [htailVariable]

theorem branchConditionsForDirectives?_within
    (directives : List DirectiveApplication) (branches : List BranchCondition)
    (variables : List Name)
    (hresult : branchConditionsForDirectives? directives = some branches)
    (hvariables
      : ∀ variableName,
          variableName ∈ directives.filterMap directiveBooleanVariable?
          -> variableName ∈ variables)
    : ∀ branch,
        branch ∈ branches -> BranchCondition.BooleanVariableWithin variables branch := by
  unfold branchConditionsForDirectives? at hresult
  cases hliterals : literalsForDirectives directives with
  | none => simp [hliterals] at hresult
  | some literals =>
      simp [hliterals] at hresult
      subst branches
      intro branch hbranch
      rcases List.mem_map.mp hbranch with ⟨literal, hliteral, rfl⟩
      exact hvariables literal.variableName
        (literalsForDirectives_variable_mem directives literals hliterals literal hliteral)

theorem branchConditionsForInlineFragment?_within
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (branches : List BranchCondition) (variables : List Name)
    (hresult
      : branchConditionsForInlineFragment? typeCondition directives = some branches)
    (hvariables
      : ∀ variableName,
          variableName ∈ directives.filterMap directiveBooleanVariable?
          -> variableName ∈ variables)
    : ∀ branch,
        branch ∈ branches -> BranchCondition.BooleanVariableWithin variables branch := by
  unfold branchConditionsForInlineFragment? at hresult
  cases hboolean : branchConditionsForDirectives? directives with
  | none => simp [hboolean] at hresult
  | some booleanBranches =>
      simp [hboolean] at hresult
      subst branches
      intro branch hbranch
      simp only [List.mem_append, List.mem_map] at hbranch
      rcases hbranch with ⟨typeName, _htypeName, rfl⟩ | hbranch
      · trivial
      · exact branchConditionsForDirectives?_within directives booleanBranches
          variables hboolean hvariables branch hbranch

end SelectionConditions
end GraphQL
