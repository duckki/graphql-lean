import GraphQL.Theories.ResponseShape.Relations
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Variables
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Ground

/-!
Structural facts for public response-shape relations.

This module deliberately stops at support equivalence, relation projections,
and reflexivity. It proves neither subset transitivity nor any theorem licensing
response projection from shape subset.
-/

namespace GraphQL

namespace ResponseShape

/-- The combined support is duplicate-free even when either input is not. -/
theorem supportUnion_nodup (left right : List NormalForm.BoolVar)
    : (supportUnion left right).Nodup := by
  exact NormalForm.CompleteNormalization.dedupBoolVars_nodup _

/-- Membership in the combined support is membership in either input support. -/
theorem mem_supportUnion_iff
    (varName : NormalForm.BoolVar)
    (left right : List NormalForm.BoolVar)
    : varName ∈ supportUnion left right ↔ varName ∈ left ∨ varName ∈ right := by
  simpa [supportUnion] using
    (NormalForm.CompleteNormalization.mem_dedupBoolVars_iff
      varName (left ++ right))

/-- Extensional Boolean-support equivalence is reflexive. -/
theorem boolSupportEquivalent_refl (support : List NormalForm.BoolVar)
    : BoolSupportEquivalent support support := by
  intro varName
  rfl

/-- Extensional Boolean-support equivalence is symmetric. -/
theorem boolSupportEquivalent_symm
    {left right : List NormalForm.BoolVar}
    (hequivalent : BoolSupportEquivalent left right)
    : BoolSupportEquivalent right left := by
  intro varName
  exact (hequivalent varName).symm

/-- Extensional Boolean-support equivalence is transitive. -/
theorem boolSupportEquivalent_trans
    {left middle right : List NormalForm.BoolVar}
    (hleft : BoolSupportEquivalent left middle)
    (hright : BoolSupportEquivalent middle right)
    : BoolSupportEquivalent left right := by
  intro varName
  exact Iff.trans (hleft varName) (hright varName)

/-- A subset relates operation shapes of the same operation kind. -/
theorem ShapeSubset.operationType_eq
    {schema : Schema} {required provided : OperationShape}
    (hsubset : ShapeSubset schema required provided)
    : required.operationType = provided.operationType :=
  hsubset.1

/-- A subset relates operation shapes rooted at the same GraphQL type. -/
theorem ShapeSubset.rootType_eq
    {schema : Schema} {required provided : OperationShape}
    (hsubset : ShapeSubset schema required provided)
    : required.rootType = provided.rootType :=
  hsubset.2.1

/-- The path-coverage component of a shape subset. -/
theorem ShapeSubset.denotesEquivalentPath
    {schema : Schema} {required provided : OperationShape}
    (hsubset : ShapeSubset schema required provided)
    {assignment : NormalForm.BoolCase} {path : List PathStep}
    (hcomplete
      : NormalForm.completeNormalBoolCase
          (supportUnion required.boolSupport provided.boolSupport) assignment)
    (hdenotes : required.root.DenotesPath schema assignment required.rootType path)
    : provided.root.DenotesEquivalentPath schema assignment provided.rootType path :=
  hsubset.2.2 assignment hcomplete path hdenotes

/-- Every operation shape is a subset of itself. -/
theorem shapeSubset_refl (schema : Schema) (shape : OperationShape)
    : ShapeSubset schema shape shape := by
  refine ⟨rfl, rfl, ?_⟩
  intro assignment _hcomplete path hdenotes
  exact ResponseShape.DenotesEquivalentPath.of_denotes hdenotes

/-- The forward subset carried by shape equivalence. -/
theorem ShapeEquivalent.leftSubset
    {schema : Schema} {left right : OperationShape}
    (hequivalent : ShapeEquivalent schema left right)
    : ShapeSubset schema left right :=
  hequivalent.1

/-- The reverse subset carried by shape equivalence. -/
theorem ShapeEquivalent.rightSubset
    {schema : Schema} {left right : OperationShape}
    (hequivalent : ShapeEquivalent schema left right)
    : ShapeSubset schema right left :=
  hequivalent.2

/-- Shape equivalence is reflexive. -/
theorem shapeEquivalent_refl (schema : Schema) (shape : OperationShape)
    : ShapeEquivalent schema shape shape :=
  ⟨shapeSubset_refl schema shape, shapeSubset_refl schema shape⟩

/-- The footprint-equivalence component of strict shape equivalence. -/
theorem StrictShapeEquivalent.shapeEquivalent
    {schema : Schema} {left right : OperationShape}
    (hequivalent : StrictShapeEquivalent schema left right)
    : ShapeEquivalent schema left right :=
  hequivalent.1

/-- The support-equivalence component of strict shape equivalence. -/
theorem StrictShapeEquivalent.boolSupportEquivalent
    {schema : Schema} {left right : OperationShape}
    (hequivalent : StrictShapeEquivalent schema left right)
    : BoolSupportEquivalent left.boolSupport right.boolSupport :=
  hequivalent.2

/-- Strict shape equivalence is reflexive. -/
theorem strictShapeEquivalent_refl (schema : Schema) (shape : OperationShape)
    : StrictShapeEquivalent schema shape shape :=
  ⟨shapeEquivalent_refl schema shape, boolSupportEquivalent_refl shape.boolSupport⟩

end ResponseShape

end GraphQL
