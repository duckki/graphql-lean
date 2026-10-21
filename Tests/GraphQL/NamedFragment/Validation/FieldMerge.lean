import GraphQL.NamedFragment.Validation
import Tests.GraphQL.Validation.FieldMerge

namespace GraphQL.Tests.NamedFragment.Validation.FieldMerge

open GraphQL.NamedFragment
open GraphQL.NamedFragment.Validation.FieldMerge

private def schema : Schema :=
  GraphQL.Tests.Validation.FieldMerge.disjointReturnSchema

private def nameFragment (parent : Name) : FragmentDefinition :=
  {
    name := parent
    typeCondition := parent
    selectionSet := [.field "name" "name" [] [] []]
  }

private def fragments : List FragmentDefinition :=
  [nameFragment "User", nameFragment "Other"]

private def branchField (parent returnType : Name) : ScopedField :=
  {
    parentType := parent
    responseName := "result"
    fieldName := "user"
    arguments := []
    outputType := .named returnType
    selectionSet := [.fragmentSpread returnType []]
    availableFragments := fragments
  }

private def leafField (parent leafType remainingParent : Name) : ScopedField :=
  {
    parentType := parent
    responseName := "name"
    fieldName := "name"
    arguments := []
    outputType := .named leafType
    selectionSet := []
    availableFragments := [nameFragment remainingParent]
  }

private theorem collectedChildren (left right : Name)
    : collectSubfields schema (branchField left "User") (branchField right "User")
      = [leafField "User" "String" "Other", leafField "User" "String" "Other"] := by
  simp [collectSubfields, collectFields, collectSelection, branchField, nameFragment,
    leafField, fragments, lookupFragmentAndRestLt?, TypeRef.namedType, schema,
    GraphQL.Tests.Validation.FieldMerge.disjointReturnSchema,
    GraphQL.Tests.Validation.FieldMerge.returnScopeSchema,
    Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
    TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name]

theorem sameResponseShape_fragmentSpread_matching
    : sameResponseShape schema fragments
        (branchField "LeftBranch" "User") (branchField "RightBranch" "User") := by
  refine .intro _ _ ?_ ?_
  · exact GraphQL.SchemaWellFormedness.sameTypeShape_refl schema _
      (GraphQL.Tests.Validation.FieldMerge.sameTypeShape_differentCompositeReturns.1)
  · intro _ _ subLeft hleft subRight hright _
    rw [collectedChildren] at hleft hright
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hleft hright
    subst subLeft
    subst subRight
    refine .intro _ _ ?_ ?_
    · exact ⟨⟨.builtinScalar .string, rfl, trivial⟩,
        ⟨.builtinScalar .string, rfl, trivial⟩, fun _ => rfl⟩
    · intro _ _ child hchild
      simp [collectSubfields, collectFields, leafField] at hchild

/-- Response-shape recursion follows named spreads, including on disjoint branches. -/
theorem sameResponseShape_fragmentSpread_nestedMismatch_rejected
    : ¬ sameResponseShape schema fragments
          (branchField "LeftBranch" "User") (branchField "RightBranch" "Other") := by
  intro hshape
  cases hshape with
  | intro _ _ _ hchildren =>
      have huser : schema.isCompositeType "User" := by
        exact ⟨.object { name := "User", fields := [{ name := "name", outputType := .named "String" }] },
          by rfl, trivial⟩
      have hother : schema.isCompositeType "Other" := by
        exact ⟨.object { name := "Other", fields := [{ name := "name", outputType := .named "Int" }] },
          by rfl, trivial⟩
      have hcollect : collectSubfields schema
          (branchField "LeftBranch" "User") (branchField "RightBranch" "Other")
          = [leafField "User" "String" "Other", leafField "Other" "Int" "User"] := by
        simp [collectSubfields, collectFields, collectSelection, branchField, nameFragment,
          leafField, fragments, lookupFragmentAndRestLt?, TypeRef.namedType, schema,
          GraphQL.Tests.Validation.FieldMerge.disjointReturnSchema,
          GraphQL.Tests.Validation.FieldMerge.returnScopeSchema,
          Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
          TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name]
      have hchild := hchildren huser hother (leafField "User" "String" "Other")
        (by rw [hcollect]; simp) (leafField "Other" "Int" "User")
        (by rw [hcollect]; simp) rfl
      cases hchild with
      | intro _ _ htypes _ =>
          have hleaf : schema.isLeafType "String" :=
            ⟨.builtinScalar .string, rfl, trivial⟩
          have heq : ("String" : String) = "Int" := htypes.2.2 (Or.inl hleaf)
          exact (by decide : ("String" : String) ≠ "Int") heq

end GraphQL.Tests.NamedFragment.Validation.FieldMerge
