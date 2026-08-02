import Proofs.GraphQL.Theories.ResponseShape.Compute.Activity
import Proofs.GraphQL.Theories.ResponseShape.Compute.Soundness

/-!
Well-formedness facts for response shapes produced by complete-normal decoding.
-/

namespace GraphQL

namespace ResponseShape

/-- Definition-level decoder evidence: recursive child kind is already checked
by the public Boolean predicate, while the guard is a complete minterm. -/
def DecoderDefinitionInvariant
    (schema : Schema) (support : List NormalForm.BoolVar)
    (definition : ShapeDefinition) : Prop :=
  definition.wellFormedBool schema support = true
  ∧ definition.clause.CompleteMinterm support

def decoderDefinitionsInvariant
    (schema : Schema) (support : List NormalForm.BoolVar)
    (definitions : List ShapeDefinition) : Prop :=
  ∀ definition ∈ definitions,
    DecoderDefinitionInvariant schema support definition

def DecoderGroupInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (possible : PossibleDefinitions) : Prop :=
  GroundSet.Valid schema parentType possible.objectTypes
  ∧ (possible.definitions.map ShapeDefinition.clause).Nodup
  ∧ decoderDefinitionsInvariant schema support possible.definitions

def DecoderPositionInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition) : Prop :=
  ∃ objectTypes : List GroundObject,
    position.possibleDefinitions.map PossibleDefinitions.objectTypes =
      objectTypes.map (fun objectType => [objectType])
    ∧ objectTypes.Nodup
    ∧ ∀ possible ∈ position.possibleDefinitions,
        DecoderGroupInvariant schema support parentType possible

def decoderPositionsInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (positions : List ResponsePosition) : Prop :=
  ∀ position ∈ positions,
    DecoderPositionInvariant schema support parentType position

/-- Proof-facing invariant of shapes emitted by the decoder.  Unlike public
well-formedness, this records the singleton concrete-object partition and the
local guard unambiguity that make decoder merges well-formed. -/
def DecoderShapeInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name) :
    ResponseShape -> Prop
  | .object positions =>
      (positions.map ResponsePosition.responseName).Nodup
      ∧ decoderPositionsInvariant schema support parentType positions

/-- A concrete object accepted in a parent scope forms a valid singleton
ground set. -/
theorem groundSetValid_singleton
    (schema : Schema) (parentType objectType : Name)
    (hobject : schema.objectType objectType)
    (hincludes : schema.typeIncludesObjectBool parentType objectType = true) :
    GroundSet.Valid schema parentType [objectType] := by
  rcases hobject with ⟨objectDefinition, hlookup⟩
  unfold GroundSet.Valid GroundSet.validBool
  simp [NormalForm.objectTypeNameBool, hlookup, hincludes,
    namesStrictlyIncreasing]

/-- An object scope includes itself as its singleton ground set. -/
theorem groundSetValid_objectSingleton
    (schema : Schema) (objectType : Name)
    (hobject : schema.objectType objectType) :
    GroundSet.Valid schema objectType [objectType] :=
  groundSetValid_singleton schema objectType objectType hobject
    (NormalForm.object_typeIncludesObjectBool_self schema hobject)

private theorem responsePositionCasesValidBool_of_invariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition)
    (hinvariant : DecoderPositionInvariant schema support parentType position) :
    responsePositionCasesValidBool schema support parentType position = true := by
  rcases hinvariant with ⟨objectTypes, hobjects, hnodup, hgroups⟩
  apply responsePositionCasesValidBool_of_singletonObjectGroups schema support
    parentType position
  · exact ⟨objectTypes, hobjects, hnodup⟩
  · intro possible hpossible
    exact (hgroups possible hpossible).2.1
  · intro possible hpossible definition hdefinition
    exact (hgroups possible hpossible).2.2 definition hdefinition |>.2

private theorem shapeDefinitionsWellFormedBool_of_invariant
    (schema : Schema) (support : List NormalForm.BoolVar) :
    ∀ definitions,
      decoderDefinitionsInvariant schema support definitions ->
      shapeDefinitionsWellFormedBool schema support definitions = true
  | [], _hinvariant => rfl
  | definition :: rest, hinvariant => by
      rw [shapeDefinitionsWellFormedBool, Bool.and_eq_true_iff]
      constructor
      · exact (hinvariant definition (by simp)).1
      · exact shapeDefinitionsWellFormedBool_of_invariant schema support rest
          (fun candidate hcandidate =>
            hinvariant candidate (List.mem_cons_of_mem definition hcandidate))

private theorem possibleDefinitionsWellFormedBool_of_invariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name) :
    ∀ groups,
      (∀ possible ∈ groups,
        DecoderGroupInvariant schema support parentType possible) ->
      possibleDefinitionsWellFormedBool schema support parentType groups = true
  | [], _hinvariant => rfl
  | possible :: groups, hinvariant => by
      rw [possibleDefinitionsWellFormedBool, Bool.and_eq_true_iff]
      constructor
      · cases possible with
        | mk possibleObjects definitions =>
            rcases hinvariant (.mk possibleObjects definitions) (by simp) with
              ⟨hvalid, _hclauses, hdefinitions⟩
            simp only [PossibleDefinitions.wellFormedBool,
              Bool.and_eq_true_iff]
            exact ⟨hvalid,
              shapeDefinitionsWellFormedBool_of_invariant schema support
                definitions hdefinitions⟩
      · exact possibleDefinitionsWellFormedBool_of_invariant schema support
          parentType groups (fun candidate hcandidate =>
            hinvariant candidate (List.mem_cons_of_mem possible hcandidate))

private theorem responsePositionWellFormedBool_of_invariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition)
    (hinvariant : DecoderPositionInvariant schema support parentType position) :
    position.wellFormedBool schema support parentType = true := by
  rcases hinvariant with ⟨objectTypes, hobjects, hnodup, hgroups⟩
  cases position with
  | mk responseName groups =>
      rw [ResponsePosition.wellFormedBool, Bool.and_eq_true_iff]
      exact ⟨responsePositionCasesValidBool_of_invariant schema support
        parentType (.mk responseName groups)
          ⟨objectTypes, hobjects, hnodup, hgroups⟩,
        possibleDefinitionsWellFormedBool_of_invariant schema support parentType
          groups hgroups⟩

private theorem responsePositionsWellFormedBool_of_invariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name) :
    ∀ positions,
      decoderPositionsInvariant schema support parentType positions ->
      responsePositionsWellFormedBool schema support parentType positions = true
  | [], _hinvariant => rfl
  | position :: rest, hinvariant => by
      rw [responsePositionsWellFormedBool, Bool.and_eq_true_iff]
      constructor
      · exact responsePositionWellFormedBool_of_invariant schema support
          parentType position (hinvariant position (by simp))
      · exact responsePositionsWellFormedBool_of_invariant schema support
          parentType rest (fun candidate hcandidate =>
            hinvariant candidate (List.mem_cons_of_mem position hcandidate))

/-- The proof-facing decoder invariant is stronger than the public recursive
well-formedness check. -/
theorem DecoderShapeInvariant.wellFormedBool
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (shape : ResponseShape)
    (hinvariant : DecoderShapeInvariant schema support parentType shape) :
    shape.wellFormedBool schema support parentType = true := by
  cases shape with
  | object positions =>
      rcases hinvariant with ⟨hnames, hpositions⟩
      rw [ResponseShape.wellFormedBool, Bool.and_eq_true_iff]
      exact ⟨by simpa using hnames,
        responsePositionsWellFormedBool_of_invariant schema support parentType
          positions hpositions⟩

/-- Composite decoder definitions inherit recursive child well-formedness from
the stronger child invariant. -/
theorem DecoderDefinitionInvariant.composite
    (schema : Schema) (support : List NormalForm.BoolVar)
    (clause : Clause) (field : FieldHead) (child : ResponseShape)
    (hvalid : clause.Valid support)
    (hcomplete : clause.CompleteMinterm support)
    (hcomposite : field.outputType.isCompositeBool schema = true)
    (hchild : DecoderShapeInvariant schema support
      field.outputType.namedType child) :
    DecoderDefinitionInvariant schema support
      (.mk clause field (some child)) := by
  unfold Clause.Valid at hvalid
  constructor
  · simp [ShapeDefinition.wellFormedBool, hvalid, hcomposite,
      hchild.wellFormedBool]
  · exact hcomplete

/-- Leaf decoder definitions have no child and satisfy the public child-kind
check directly. -/
theorem DecoderDefinitionInvariant.leaf
    (schema : Schema) (support : List NormalForm.BoolVar)
    (clause : Clause) (field : FieldHead)
    (hvalid : clause.Valid support)
    (hcomplete : clause.CompleteMinterm support)
    (hnotComposite : field.outputType.isCompositeBool schema = false)
    (hleaf : NormalForm.leafTypeNameBool schema
      field.outputType.namedType = true) :
    DecoderDefinitionInvariant schema support (.mk clause field none) := by
  unfold Clause.Valid at hvalid
  constructor
  · simp [ShapeDefinition.wellFormedBool, hvalid, hnotComposite, hleaf]
  · exact hcomplete

/-- The empty object shape satisfies the decoder invariant in every scope. -/
theorem DecoderShapeInvariant.empty
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name) :
    DecoderShapeInvariant schema support parentType (.object []) := by
  constructor <;> simp [decoderPositionsInvariant]

/-- One decoded field establishes the full proof-facing invariant. -/
theorem DecoderShapeInvariant.singletonDefinition
    (schema : Schema) (support : List NormalForm.BoolVar)
    (parentType parentObject responseName : Name)
    (definition : ShapeDefinition)
    (hground : GroundSet.Valid schema parentType [parentObject])
    (hdefinition : DecoderDefinitionInvariant schema support definition) :
    DecoderShapeInvariant schema support parentType
      (singletonDefinitionShape parentObject responseName definition) := by
  unfold singletonDefinitionShape DecoderShapeInvariant
  constructor
  · simp [ResponsePosition.responseName]
  · intro position hposition
    simp only [List.mem_singleton] at hposition
    subst position
    unfold DecoderPositionInvariant
    refine ⟨[parentObject], ?_, by simp, ?_⟩
    · rfl
    intro possible hpossible
    change possible ∈ [.mk [parentObject] [definition]] at hpossible
    simp only [List.mem_singleton] at hpossible
    subst possible
    unfold DecoderGroupInvariant
    refine ⟨hground, by simp [PossibleDefinitions.definitions,
      ShapeDefinition.clause], ?_⟩
    intro candidate hcandidate
    change candidate ∈ [definition] at hcandidate
    simp only [List.mem_singleton] at hcandidate
    subst candidate
    exact hdefinition

/-- Decoder invariants plus support uniqueness imply public shape
well-formedness. -/
theorem DecoderShapeInvariant.wellFormed
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (shape : ResponseShape) (hsupport : support.Nodup)
    (hinvariant : DecoderShapeInvariant schema support parentType shape) :
    shape.WellFormed schema support parentType := by
  unfold ResponseShape.WellFormed
  simp [hsupport, hinvariant.wellFormedBool]

/-- Successful computation preserves its operation payload and exposes the
successful staged root decode. -/
theorem computeOperationShape_fields
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape) :
    shape.operationType = operation.operationType
      ∧ shape.rootType = operation.rootType schema
      ∧ shape.boolSupport = NormalForm.operationBoolVars operation
      ∧ decodeCompleteRoot schema (NormalForm.operationBoolVars operation)
          (operation.rootType schema)
          (NormalForm.completeNormalizeOperation schema operation).selectionSet =
        .ok shape.root := by
  exact decodeCompleteOperationShape_fields schema
    (NormalForm.operationBoolVars operation)
    (NormalForm.completeNormalizeOperation schema operation) shape
    (by simpa [computeOperationShape] using hcompute)

/-- Successful computation establishes uniqueness of the stored Boolean support. -/
theorem computeOperationShape_support_nodup
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape) :
    shape.boolSupport.Nodup := by
  exact decodeCompleteOperationShape_support_nodup schema
    (NormalForm.operationBoolVars operation)
    (NormalForm.completeNormalizeOperation schema operation) shape
    (by simpa [computeOperationShape] using hcompute)

/-- For a computed shape, operation-level well-formedness reduces exactly to
the still-structural root check: root identity and support uniqueness already
follow from successful decoding. -/
theorem computeOperationShape_wellFormed_iff_root
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape) :
    shape.WellFormed schema ↔
      shape.root.wellFormedBool schema shape.boolSupport shape.rootType = true := by
  rcases computeOperationShape_fields schema operation shape hcompute with
    ⟨hoperationType, hrootType, _hsupport, _hrootDecode⟩
  have hsupport := computeOperationShape_support_nodup
    schema operation shape hcompute
  unfold OperationShape.WellFormed ResponseShape.WellFormed
  simp [hoperationType, hrootType, hsupport, Operation.rootType]

/-- Staged introduction form for operation well-formedness of a successful
computation. -/
theorem computeOperationShape_wellFormed_of_root
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape)
    (hroot :
      shape.root.wellFormedBool schema shape.boolSupport shape.rootType = true) :
    shape.WellFormed schema :=
  (computeOperationShape_wellFormed_iff_root schema operation shape hcompute).2
    hroot

/-- Stronger staged introduction form: it is enough to establish the decoder
image invariant for the successfully computed root. -/
theorem computeOperationShape_wellFormed_of_invariant
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape)
    (hinvariant : DecoderShapeInvariant schema shape.boolSupport shape.rootType
      shape.root) :
    shape.WellFormed schema := by
  exact computeOperationShape_wellFormed_of_root schema operation shape hcompute
    (hinvariant.wellFormedBool)

end ResponseShape

end GraphQL
