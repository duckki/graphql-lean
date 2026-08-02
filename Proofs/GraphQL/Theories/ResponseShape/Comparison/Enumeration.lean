import GraphQL.Theories.ResponseShape.Comparison
import Proofs.GraphQL.Theories.ResponseShape.Denotation

/-!
Correctness of the finite structural response-path enumerator.

The proof follows the syntax's eight-way nested mutual recursion as one coupled
family. In particular, recursive child paths are proved in the same induction
that proves singleton paths; there is no second traversal theorem to keep in
sync with the executable enumerator.
-/

namespace GraphQL

namespace ResponseShape

namespace Comparison

private def activeDefinitionPath
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (responseName runtimeObject : Name) (definition : ShapeDefinition)
    (path : List PathStep)
    : Prop :=
  definition.clause.HoldsIn assignment
  ∧ let step : PathStep :=
      {
        parentObject := runtimeObject
        responseName := responseName
        field := definition.field
      }
    path = [step]
    ∨ ∃ child childPath,
        definition.subshape = some child
        ∧ child.DenotesPath schema assignment
            definition.field.outputType.namedType childPath
        ∧ path = step :: childPath

private def possiblePath
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name) (possible : PossibleDefinitions)
    (path : List PathStep)
    : Prop :=
  ∃ runtimeObject ∈ possible.objectTypes,
    schema.typeIncludesObject parentType runtimeObject
    ∧ ∃ definition ∈ possible.definitions,
        activeDefinitionPath schema assignment responseName runtimeObject definition path

private def positionPath
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (position : ResponsePosition)
    (path : List PathStep)
    : Prop :=
  ∃ possible ∈ position.possibleDefinitions,
    possiblePath schema assignment parentType position.responseName possible path

mutual
  private theorem mem_enumerateShapeCore_iff
      (shape : ResponseShape) (schema : Schema)
      (assignment : NormalForm.BoolCase) (parentType : Name)
      (path : List PathStep)
      : path ∈ enumerateShapeCore shape schema assignment parentType
        ↔ shape.DenotesPath schema assignment parentType path := by
    cases shape with
    | object positions =>
      rw [enumerateShapeCore, mem_enumeratePositionsCore_iff]
      constructor
      · rintro ⟨position, hposition, possible, hpossible, runtimeObject,
          hruntime, hincludes, definition, hdefinition, hactive⟩
        rcases hactive with ⟨hclause, hpath⟩
        cases hpath with
        | inl heq =>
          subst path
          exact .field
            hincludes hposition hpossible hruntime hdefinition hclause
        | inr hchild =>
          rcases hchild with
            ⟨child, childPath, hsubshape, hdenotes, heq⟩
          subst path
          exact .child
            hincludes hposition hpossible hruntime hdefinition hclause
              hsubshape hdenotes
      · intro hdenotes
        cases hdenotes with
        | @field _ _ position possible definition runtimeObject hincludes
            hposition hpossible hruntime hdefinition hclause =>
          exact
            ⟨position, hposition, possible, hpossible, runtimeObject, hruntime,
              hincludes, definition, hdefinition, hclause, Or.inl rfl⟩
        | @child _ _ position possible definition runtimeObject child childPath
            hincludes hposition hpossible hruntime hdefinition hclause
            hsubshape hchild =>
          exact
            ⟨position, hposition, possible, hpossible, runtimeObject, hruntime,
              hincludes, definition, hdefinition, hclause,
              Or.inr ⟨child, childPath, hsubshape, hchild, rfl⟩⟩

  private theorem mem_enumeratePositionCore_iff
      (position : ResponsePosition) (schema : Schema)
      (assignment : NormalForm.BoolCase) (parentType : Name)
      (path : List PathStep)
      : path ∈ enumeratePositionCore position schema assignment parentType
        ↔ positionPath schema assignment parentType position path := by
    cases position with
    | mk responseName possibles =>
      simp only [enumeratePositionCore, positionPath,
        ResponsePosition.possibleDefinitions, ResponsePosition.responseName]
      exact mem_enumeratePossiblesCore_iff
        possibles schema assignment parentType responseName path

  private theorem mem_enumeratePossibleCore_iff
      (possible : PossibleDefinitions) (schema : Schema)
      (assignment : NormalForm.BoolCase) (parentType responseName : Name)
      (path : List PathStep)
      : path ∈ enumeratePossibleCore possible schema assignment parentType responseName
        ↔ possiblePath schema assignment parentType responseName possible path := by
    cases possible with
    | mk objectTypes definitions =>
      simp only [enumeratePossibleCore, possiblePath,
        PossibleDefinitions.objectTypes, PossibleDefinitions.definitions,
        List.mem_flatMap]
      constructor
      · rintro ⟨runtimeObject, hruntime, hpaths⟩
        split at hpaths
        next hincludesBool =>
          refine ⟨runtimeObject, hruntime, ?_, ?_⟩
          · simpa [Schema.typeIncludesObjectBool, Schema.typeIncludesObject]
              using hincludesBool
          · exact
              (mem_enumerateDefinitionsCore_iff
                definitions schema assignment responseName runtimeObject path).mp
                hpaths
        next => simp at hpaths
      · rintro ⟨runtimeObject, hruntime, hincludes, hdefinition⟩
        refine ⟨runtimeObject, hruntime, ?_⟩
        have hincludesBool :
            schema.typeIncludesObjectBool parentType runtimeObject = true := by
          simpa [Schema.typeIncludesObjectBool, Schema.typeIncludesObject]
            using hincludes
        simp only [hincludesBool, if_true]
        exact
          (mem_enumerateDefinitionsCore_iff
            definitions schema assignment responseName runtimeObject path).mpr
            hdefinition

  private theorem mem_enumerateDefinitionCore_iff
      (definition : ShapeDefinition) (schema : Schema)
      (assignment : NormalForm.BoolCase) (responseName runtimeObject : Name)
      (path : List PathStep)
      : path
          ∈ enumerateDefinitionCore
              definition schema assignment responseName runtimeObject
        ↔ activeDefinitionPath
            schema assignment responseName runtimeObject definition path := by
    cases definition with
    | mk clause field subshape =>
      simp only [enumerateDefinitionCore, activeDefinitionPath,
        ShapeDefinition.clause, ShapeDefinition.field,
        ShapeDefinition.subshape]
      split
      next hclauseBool =>
        rw [Clause.holdsInBool_iff] at hclauseBool
        simp only [List.mem_cons, mem_enumerateSubshapeCore_iff]
        constructor
        · intro hpath
          exact ⟨hclauseBool, hpath⟩
        · exact fun h => h.2
      next hclauseBool =>
        have hnot : ¬ clause.HoldsIn assignment := by
          intro hholds
          have htrue :=
            (Clause.holdsInBool_iff assignment clause).mpr hholds
          simp [htrue] at hclauseBool
        simp [hnot]

  private theorem mem_enumeratePositionsCore_iff
      (positions : List ResponsePosition) (schema : Schema)
      (assignment : NormalForm.BoolCase) (parentType : Name)
      (path : List PathStep)
      : path ∈ enumeratePositionsCore positions schema assignment parentType
        ↔ ∃ position ∈ positions,
            positionPath schema assignment parentType position path := by
    cases positions with
    | nil => simp [enumeratePositionsCore]
    | cons position rest =>
      simp only [enumeratePositionsCore, List.mem_append, List.mem_cons,
        mem_enumeratePositionCore_iff, mem_enumeratePositionsCore_iff]
      constructor
      · rintro (hhead | ⟨selected, hrest, hselected⟩)
        · exact ⟨position, Or.inl rfl, hhead⟩
        · exact ⟨selected, Or.inr hrest, hselected⟩
      · rintro ⟨selected, hmem, hselected⟩
        rcases hmem with rfl | hrest
        · exact Or.inl hselected
        · exact Or.inr ⟨selected, hrest, hselected⟩

  private theorem mem_enumeratePossiblesCore_iff
      (possibles : List PossibleDefinitions) (schema : Schema)
      (assignment : NormalForm.BoolCase) (parentType responseName : Name)
      (path : List PathStep)
      : path ∈ enumeratePossiblesCore possibles schema assignment parentType responseName
        ↔ ∃ possible ∈ possibles,
            possiblePath schema assignment parentType responseName possible path := by
    cases possibles with
    | nil => simp [enumeratePossiblesCore]
    | cons possible rest =>
      simp only [enumeratePossiblesCore, List.mem_append, List.mem_cons,
        mem_enumeratePossibleCore_iff, mem_enumeratePossiblesCore_iff]
      constructor
      · rintro (hhead | ⟨selected, hrest, hselected⟩)
        · exact ⟨possible, Or.inl rfl, hhead⟩
        · exact ⟨selected, Or.inr hrest, hselected⟩
      · rintro ⟨selected, hmem, hselected⟩
        rcases hmem with rfl | hrest
        · exact Or.inl hselected
        · exact Or.inr ⟨selected, hrest, hselected⟩

  private theorem mem_enumerateDefinitionsCore_iff
      (definitions : List ShapeDefinition) (schema : Schema)
      (assignment : NormalForm.BoolCase) (responseName runtimeObject : Name)
      (path : List PathStep)
      : path
          ∈ enumerateDefinitionsCore
              definitions schema assignment responseName runtimeObject
        ↔ ∃ definition ∈ definitions,
            activeDefinitionPath
              schema assignment responseName runtimeObject definition path := by
    cases definitions with
    | nil => simp [enumerateDefinitionsCore]
    | cons definition rest =>
      simp only [enumerateDefinitionsCore, List.mem_append, List.mem_cons,
        mem_enumerateDefinitionCore_iff, mem_enumerateDefinitionsCore_iff]
      constructor
      · rintro (hhead | ⟨selected, hrest, hselected⟩)
        · exact ⟨definition, Or.inl rfl, hhead⟩
        · exact ⟨selected, Or.inr hrest, hselected⟩
      · rintro ⟨selected, hmem, hselected⟩
        rcases hmem with rfl | hrest
        · exact Or.inl hselected
        · exact Or.inr ⟨selected, hrest, hselected⟩

  private theorem mem_enumerateSubshapeCore_iff
      (subshape : Option ResponseShape) (schema : Schema)
      (assignment : NormalForm.BoolCase) (step : PathStep) (field : FieldHead)
      (path : List PathStep)
      : path ∈ enumerateSubshapeCore subshape schema assignment step field
        ↔ ∃ child childPath,
            subshape = some child
            ∧ child.DenotesPath schema assignment field.outputType.namedType childPath
            ∧ path = step :: childPath := by
    cases subshape with
    | none => simp [enumerateSubshapeCore]
    | some child =>
      simp only [enumerateSubshapeCore, List.mem_map]
      constructor
      · rintro ⟨childPath, hmem, rfl⟩
        exact
          ⟨child, childPath, rfl,
            (mem_enumerateShapeCore_iff
              child schema assignment field.outputType.namedType childPath).mp
              hmem,
            rfl⟩
      · rintro ⟨selectedChild, childPath, heq, hdenotes, rfl⟩
        cases heq
        exact
          ⟨childPath,
            (mem_enumerateShapeCore_iff
              child schema assignment field.outputType.namedType childPath).mpr
              hdenotes,
            rfl⟩
end

end Comparison

/-- Structural enumeration contains exactly the paths in `DenotesPath`. -/
theorem ResponseShape.mem_enumeratePaths_iff
    (shape : ResponseShape) (schema : Schema)
    (assignment : NormalForm.BoolCase) (parentType : Name)
    (path : List PathStep)
    : path ∈ shape.enumeratePaths schema assignment parentType
      ↔ shape.DenotesPath schema assignment parentType path := by
  exact Comparison.mem_enumerateShapeCore_iff
    shape schema assignment parentType path

end ResponseShape

end GraphQL
