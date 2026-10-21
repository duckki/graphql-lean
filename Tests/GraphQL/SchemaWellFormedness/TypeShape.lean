import Proofs.GraphQL.SchemaWellFormedness.TypeShape

namespace GraphQL.Tests.SchemaWellFormedness.TypeShape

open GraphQL.SchemaWellFormedness

private def schema : Schema :=
  { queryType := "Query", types := [] }

theorem wrappedScalarShape
    : sameTypeShape schema
        (.nonNull (.list (.named "String"))) (.nonNull (.list (.named "String"))) := by
  exact sameTypeShape_refl schema _ ⟨.builtinScalar .string, rfl, trivial⟩

theorem wrapperMismatch_rejected
    : ¬ sameTypeShape schema (.list (.named "String"))
          (.list (.nonNull (.named "String"))) := by
  intro hshape
  exact hshape

theorem scalarMismatch_rejected
    : ¬ sameTypeShape schema (.named "String") (.named "Int") := by
  intro hshape
  have hleaf : schema.isLeafType "String" :=
    ⟨.builtinScalar .string, rfl, trivial⟩
  exact (by decide : ("String" : String) ≠ "Int") (hshape.2.2 (Or.inl hleaf))

theorem shapeSymmetry (left right : TypeRef) (hshape : sameTypeShape schema left right)
    : sameTypeShape schema right left :=
  sameTypeShape_symm schema left right hshape

theorem shapeTransitivity (left middle right : TypeRef)
    (hleft : sameTypeShape schema left middle)
    (hright : sameTypeShape schema middle right)
    : sameTypeShape schema left right :=
  sameTypeShape_trans schema left middle right hleft hright

end GraphQL.Tests.SchemaWellFormedness.TypeShape
