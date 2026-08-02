import Proofs.GraphQL.Theories.ResponseShape.Compute.WellFormed
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Root

/-!
Operation-level correspondence for shapes produced by the complete-normal
decoder.
-/

namespace GraphQL

namespace ResponseShape

open NormalForm
open NormalForm.CompleteNormalization

/-- A computed root shape and source field collection represent the same
semantic paths at every complete assignment. -/
theorem computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (assignment : NormalForm.BoolCase) (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape)
    (hcomplete : completeNormalBoolCase shape.boolSupport assignment) :
    shape.root.DenotesEquivalentPath schema assignment shape.rootType path
      ↔ operationSelectsPath schema operation assignment path := by
  rcases computeOperationShape_fields schema operation shape hcompute with
    ⟨_hoperationType, hrootType, hsupport, hrootDecode⟩
  have hcompleteSource :
      completeNormalBoolCase (operationBoolVars operation) assignment := by
    simpa [hsupport] using hcomplete
  have hrootDecodeSource :
      decodeCompleteRoot schema (operationBoolVars operation)
          (operation.rootType schema)
          (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
            (operation.rootType schema) operation.selectionSet) = .ok shape.root := by
    simpa [completeNormalizeOperation] using hrootDecode
  have hrootCorrespondence :=
    decodeCompleteRoot_denotesEquivalentPath_iff_operationSelectsPath
      schema operation shape.root assignment hschema hvalid hrootDecodeSource
      hcompleteSource path
  simpa [hrootType] using hrootCorrespondence

/-- The operation-level semantic denotation wrapper is equivalent to source
field selection when its assignment-completeness premise is available. -/
theorem computeOperationShape_denotesEquivalent_iff_operationSelectsPath
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (obligation : ShapeObligation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape)
    (hcomplete : completeNormalBoolCase shape.boolSupport
      obligation.assignment) :
    shape.DenotesEquivalent schema obligation
      ↔ operationSelectsPath schema operation obligation.assignment
          obligation.path := by
  unfold OperationShape.DenotesEquivalent
  rw [computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath
    schema operation shape obligation.assignment obligation.path hschema hvalid
    hcompute hcomplete]
  simp [hcomplete]

/-- Exact stored-path denotation implies source field selection. The converse
uses semantic-path denotation because field collection ignores argument order. -/
theorem computeOperationShape_denotesPath_operationSelectsPath
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (assignment : NormalForm.BoolCase) (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape)
    (hcomplete : completeNormalBoolCase shape.boolSupport assignment)
    (hdenotes : shape.root.DenotesPath schema assignment shape.rootType path) :
    operationSelectsPath schema operation assignment path :=
  (computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath
      schema operation shape assignment path hschema hvalid hcompute hcomplete).mp
    (ResponseShape.DenotesEquivalentPath.of_denotes hdenotes)

/-- Exact operation-shape denotation implies the source footprint. -/
theorem computeOperationShape_denotes_operationSelectsPath
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (obligation : ShapeObligation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape)
    (hdenotes : shape.Denotes schema obligation) :
    operationSelectsPath schema operation obligation.assignment
      obligation.path :=
  computeOperationShape_denotesPath_operationSelectsPath schema operation shape
    obligation.assignment obligation.path hschema hvalid hcompute hdenotes.1
    hdenotes.2

end ResponseShape

end GraphQL
