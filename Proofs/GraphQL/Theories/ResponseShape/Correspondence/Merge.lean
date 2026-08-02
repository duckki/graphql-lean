import GraphQL.Theories.ResponseShape.Compute
import GraphQL.Theories.ResponseShape.Denotation

/-!
Path-denotation algebra for the response-shape merge operations.

The merge functions only reorganize the containers around stored definitions.
Consequently their path denotation is exactly the union of the input
denotations; no well-formedness or decoder-image premise is needed.
-/

namespace GraphQL

namespace ResponseShape

private def groupsContainDefinition
    (runtimeObject : GroundObject) (definition : ShapeDefinition)
    (groups : List PossibleDefinitions) : Prop :=
  ∃ possible ∈ groups,
    runtimeObject ∈ possible.objectTypes
      ∧ definition ∈ possible.definitions

private def positionsContainDefinition
    (responseName : Name) (runtimeObject : GroundObject)
    (definition : ShapeDefinition)
    (positions : List ResponsePosition) : Prop :=
  ∃ position ∈ positions,
    position.responseName = responseName
      ∧ groupsContainDefinition runtimeObject definition
        position.possibleDefinitions

private def definitionDenotesPath
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (path : List PathStep)
    (responseName : Name) (runtimeObject : GroundObject)
    (definition : ShapeDefinition) : Prop :=
  schema.typeIncludesObject parentType runtimeObject
  ∧ definition.clause.HoldsIn assignment
  ∧ (path =
      [{ parentObject := runtimeObject
         responseName := responseName
         field := definition.field }]
    ∨ ∃ childShape childPath,
        definition.subshape = some childShape
        ∧ ResponseShape.DenotesPath schema assignment
            definition.field.outputType.namedType childShape childPath
        ∧ path =
            { parentObject := runtimeObject
              responseName := responseName
              field := definition.field } :: childPath)

private theorem denotesPath_object_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (positions : List ResponsePosition)
    (path : List PathStep) :
    ResponseShape.DenotesPath schema assignment parentType
        (.object positions) path ↔
      ∃ responseName runtimeObject definition,
        positionsContainDefinition responseName runtimeObject definition positions
        ∧ definitionDenotesPath schema assignment parentType path
            responseName runtimeObject definition := by
  constructor
  · intro hdenotes
    cases hdenotes with
    | @field _ _ selectedPosition _ selectedDefinition selectedObject
        runtimePossible positionMem possibleMem runtimeMem definitionMem
        clauseHolds =>
        refine ⟨selectedPosition.responseName, selectedObject,
          selectedDefinition, ?_,
          runtimePossible, clauseHolds, Or.inl rfl⟩
        exact ⟨_, positionMem, rfl, _, possibleMem, runtimeMem, definitionMem⟩
    | @child _ _ selectedPosition _ selectedDefinition selectedObject _ _
        runtimePossible positionMem possibleMem runtimeMem definitionMem
        clauseHolds subshapeEq childDenotes =>
        refine ⟨selectedPosition.responseName, selectedObject,
          selectedDefinition, ?_,
          runtimePossible, clauseHolds, Or.inr ?_⟩
        · exact ⟨_, positionMem, rfl, _, possibleMem, runtimeMem,
            definitionMem⟩
        · exact ⟨_, _, subshapeEq, childDenotes, rfl⟩
  · rintro ⟨responseName, runtimeObject, definition,
      ⟨position, positionMem, positionName, possible, possibleMem,
        runtimeMem, definitionMem⟩,
      runtimePossible, clauseHolds, pathCase⟩
    subst responseName
    cases pathCase with
    | inl pathEq =>
        subst path
        exact .field runtimePossible positionMem possibleMem runtimeMem
          definitionMem clauseHolds
    | inr childCase =>
        rcases childCase with
          ⟨childShape, childPath, subshapeEq, childDenotes, pathEq⟩
        subst path
        exact .child runtimePossible positionMem possibleMem runtimeMem
          definitionMem clauseHolds subshapeEq childDenotes

private theorem groupsContainDefinition_insert_iff
    (incoming : PossibleDefinitions) (groups : List PossibleDefinitions)
    (runtimeObject : GroundObject) (definition : ShapeDefinition) :
    groupsContainDefinition runtimeObject definition
        (insertPossibleDefinitions incoming groups) ↔
      groupsContainDefinition runtimeObject definition groups
      ∨ (runtimeObject ∈ incoming.objectTypes
        ∧ definition ∈ incoming.definitions) := by
  have cons_iff (current : PossibleDefinitions)
      (rest : List PossibleDefinitions) :
      groupsContainDefinition runtimeObject definition (current :: rest) ↔
        (runtimeObject ∈ current.objectTypes
          ∧ definition ∈ current.definitions)
        ∨ groupsContainDefinition runtimeObject definition rest := by
    simp [groupsContainDefinition]
  induction groups with
  | nil =>
      simp [groupsContainDefinition, insertPossibleDefinitions]
  | cons current rest ih =>
      unfold insertPossibleDefinitions
      by_cases heq : current.objectTypes = incoming.objectTypes
      · have hbeq : (current.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        rw [if_pos hbeq]
        rw [cons_iff]
        change
          (runtimeObject ∈ current.objectTypes
              ∧ definition ∈ current.definitions ++ incoming.definitions
            ∨ groupsContainDefinition runtimeObject definition rest) ↔ _
        rw [List.mem_append]
        rw [cons_iff]
        constructor
        · rintro (⟨runtimeMem, definitionMem | definitionMem⟩ | restContains)
          · exact Or.inl (Or.inl ⟨runtimeMem, definitionMem⟩)
          · exact Or.inr ⟨heq ▸ runtimeMem, definitionMem⟩
          · exact Or.inl (Or.inr restContains)
        · intro h
          cases h with
          | inl hgroups =>
              cases hgroups with
              | inl hcurrent =>
                  exact Or.inl ⟨hcurrent.1, Or.inl hcurrent.2⟩
              | inr hrest => exact Or.inr hrest
          | inr hincoming =>
              exact Or.inl ⟨heq.symm ▸ hincoming.1,
                Or.inr hincoming.2⟩
      · have hbeq : (current.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        rw [if_neg (by simpa using hbeq)]
        rw [cons_iff]
        rw [cons_iff]
        constructor
        · rintro (hcurrent | hinsert)
          · exact Or.inl (Or.inl hcurrent)
          · cases ih.mp hinsert with
            | inl hrest => exact Or.inl (Or.inr hrest)
            | inr hincoming => exact Or.inr hincoming
        · rintro (hgroups | hincoming)
          · cases hgroups with
            | inl hcurrent => exact Or.inl hcurrent
            | inr hrest => exact Or.inr (ih.mpr (Or.inl hrest))
          · exact Or.inr (ih.mpr (Or.inr hincoming))

private theorem groupsContainDefinition_merge_iff
    (left right : List PossibleDefinitions)
    (runtimeObject : GroundObject) (definition : ShapeDefinition) :
    groupsContainDefinition runtimeObject definition
        (mergePossibleDefinitions left right) ↔
      groupsContainDefinition runtimeObject definition left
      ∨ groupsContainDefinition runtimeObject definition right := by
  unfold mergePossibleDefinitions
  induction right generalizing left with
  | nil => simp [groupsContainDefinition]
  | cons incoming rest ih =>
      rw [List.foldl_cons, ih,
        groupsContainDefinition_insert_iff]
      have cons_iff :
          groupsContainDefinition runtimeObject definition (incoming :: rest) ↔
            (runtimeObject ∈ incoming.objectTypes
              ∧ definition ∈ incoming.definitions)
            ∨ groupsContainDefinition runtimeObject definition rest := by
        simp [groupsContainDefinition]
      rw [cons_iff]
      simp only [or_assoc]

private theorem positionsContainDefinition_insert_iff
    (incoming : ResponsePosition) (positions : List ResponsePosition)
    (responseName : Name) (runtimeObject : GroundObject)
    (definition : ShapeDefinition) :
    positionsContainDefinition responseName runtimeObject definition
        (insertResponsePosition incoming positions) ↔
      positionsContainDefinition responseName runtimeObject definition positions
      ∨ (incoming.responseName = responseName
        ∧ groupsContainDefinition runtimeObject definition
          incoming.possibleDefinitions) := by
  have cons_iff (current : ResponsePosition)
      (rest : List ResponsePosition) :
      positionsContainDefinition responseName runtimeObject definition
          (current :: rest) ↔
        (current.responseName = responseName
          ∧ groupsContainDefinition runtimeObject definition
            current.possibleDefinitions)
        ∨ positionsContainDefinition responseName runtimeObject definition
            rest := by
    simp [positionsContainDefinition]
  induction positions with
  | nil =>
      simp [positionsContainDefinition, insertResponsePosition]
  | cons current rest ih =>
      unfold insertResponsePosition
      by_cases heq : current.responseName = incoming.responseName
      · have hbeq : (current.responseName == incoming.responseName) = true := by
          simp [heq]
        rw [if_pos hbeq]
        rw [cons_iff]
        change
          (current.responseName = responseName
              ∧ groupsContainDefinition runtimeObject definition
                (mergePossibleDefinitions current.possibleDefinitions
                  incoming.possibleDefinitions)
            ∨ positionsContainDefinition responseName runtimeObject definition
                rest) ↔ _
        rw [groupsContainDefinition_merge_iff]
        rw [cons_iff]
        constructor
        · rintro (⟨positionName, currentContains | incomingContains⟩
              | restContains)
          · exact Or.inl (Or.inl ⟨positionName, currentContains⟩)
          · exact Or.inr ⟨heq.symm.trans positionName, incomingContains⟩
          · exact Or.inl (Or.inr restContains)
        · intro h
          cases h with
          | inl hpositions =>
              cases hpositions with
              | inl hcurrent =>
                  exact Or.inl ⟨hcurrent.1, Or.inl hcurrent.2⟩
              | inr hrest => exact Or.inr hrest
          | inr hincoming =>
              exact Or.inl ⟨heq.trans hincoming.1,
                Or.inr hincoming.2⟩
      · have hbeq : (current.responseName == incoming.responseName) = false := by
          simp [heq]
        rw [if_neg (by simpa using hbeq)]
        rw [cons_iff]
        rw [cons_iff]
        constructor
        · rintro (hcurrent | hinsert)
          · exact Or.inl (Or.inl hcurrent)
          · cases ih.mp hinsert with
            | inl hrest => exact Or.inl (Or.inr hrest)
            | inr hincoming => exact Or.inr hincoming
        · rintro (hpositions | hincoming)
          · cases hpositions with
            | inl hcurrent => exact Or.inl hcurrent
            | inr hrest => exact Or.inr (ih.mpr (Or.inl hrest))
          · exact Or.inr (ih.mpr (Or.inr hincoming))

private theorem positionsContainDefinition_fold_iff
    (incoming current : List ResponsePosition)
    (responseName : Name) (runtimeObject : GroundObject)
    (definition : ShapeDefinition) :
    positionsContainDefinition responseName runtimeObject definition
        (incoming.foldl
          (fun merged position => insertResponsePosition position merged)
          current) ↔
      positionsContainDefinition responseName runtimeObject definition current
      ∨ positionsContainDefinition responseName runtimeObject definition incoming := by
  induction incoming generalizing current with
  | nil => simp [positionsContainDefinition]
  | cons position rest ih =>
      rw [List.foldl_cons, ih,
        positionsContainDefinition_insert_iff]
      have cons_iff :
          positionsContainDefinition responseName runtimeObject definition
              (position :: rest) ↔
            (position.responseName = responseName
              ∧ groupsContainDefinition runtimeObject definition
                position.possibleDefinitions)
            ∨ positionsContainDefinition responseName runtimeObject definition
                rest := by
        simp [positionsContainDefinition]
      rw [cons_iff]
      simp only [or_assoc]

private theorem groupsContainDefinition_singleton_iff
    (possible : PossibleDefinitions) (runtimeObject : GroundObject)
    (definition : ShapeDefinition) :
    groupsContainDefinition runtimeObject definition [possible] ↔
      runtimeObject ∈ possible.objectTypes
        ∧ definition ∈ possible.definitions := by
  simp [groupsContainDefinition]

private theorem positionsContainDefinition_singleton_iff
    (position : ResponsePosition) (responseName : Name)
    (runtimeObject : GroundObject) (definition : ShapeDefinition) :
    positionsContainDefinition responseName runtimeObject definition
        [position] ↔
      position.responseName = responseName
        ∧ groupsContainDefinition runtimeObject definition
          position.possibleDefinitions := by
  simp [positionsContainDefinition]

private theorem denotesPath_split_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (result left right : List ResponsePosition)
    (path : List PathStep)
    (hsplit : ∀ responseName runtimeObject definition,
      positionsContainDefinition responseName runtimeObject definition result ↔
        positionsContainDefinition responseName runtimeObject definition left
        ∨ positionsContainDefinition responseName runtimeObject definition
            right) :
    ResponseShape.DenotesPath schema assignment parentType
        (.object result) path ↔
      ResponseShape.DenotesPath schema assignment parentType
          (.object left) path
      ∨ ResponseShape.DenotesPath schema assignment parentType
          (.object right) path := by
  rw [denotesPath_object_iff, denotesPath_object_iff,
    denotesPath_object_iff]
  constructor
  · rintro ⟨responseName, runtimeObject, definition, resultContains,
      pathDenotes⟩
    cases (hsplit responseName runtimeObject definition).mp resultContains with
    | inl leftContains =>
        exact Or.inl ⟨responseName, runtimeObject, definition,
          leftContains, pathDenotes⟩
    | inr rightContains =>
        exact Or.inr ⟨responseName, runtimeObject, definition,
          rightContains, pathDenotes⟩
  · intro h
    cases h with
    | inl hleft =>
        rcases hleft with
          ⟨responseName, runtimeObject, definition, leftContains,
            pathDenotes⟩
        exact ⟨responseName, runtimeObject, definition,
          (hsplit responseName runtimeObject definition).mpr
            (Or.inl leftContains), pathDenotes⟩
    | inr hright =>
        rcases hright with
          ⟨responseName, runtimeObject, definition, rightContains,
            pathDenotes⟩
        exact ⟨responseName, runtimeObject, definition,
          (hsplit responseName runtimeObject definition).mpr
            (Or.inr rightContains), pathDenotes⟩

/-- The one-definition constructor denotes exactly its active field path and,
when present, the paths obtained by prefixing its child denotation. -/
theorem singletonDefinitionShape_denotesPath_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType parentObject responseName : Name)
    (definition : ShapeDefinition) (path : List PathStep) :
    ResponseShape.DenotesPath schema assignment parentType
        (singletonDefinitionShape parentObject responseName definition) path ↔
      schema.typeIncludesObject parentType parentObject
      ∧ definition.clause.HoldsIn assignment
      ∧ (path =
          [{ parentObject := parentObject
             responseName := responseName
             field := definition.field }]
        ∨ ∃ childShape childPath,
            definition.subshape = some childShape
            ∧ ResponseShape.DenotesPath schema assignment
                definition.field.outputType.namedType childShape childPath
            ∧ path =
                { parentObject := parentObject
                  responseName := responseName
                  field := definition.field } :: childPath) := by
  rw [singletonDefinitionShape, denotesPath_object_iff]
  simp only [positionsContainDefinition_singleton_iff,
    ResponsePosition.responseName, ResponsePosition.possibleDefinitions,
    groupsContainDefinition_singleton_iff,
    PossibleDefinitions.objectTypes, PossibleDefinitions.definitions,
    List.mem_singleton]
  unfold definitionDenotesPath
  constructor
  · rintro ⟨selectedName, selectedObject, selectedDefinition,
      ⟨nameEq, objectEq, definitionEq⟩, pathDenotes⟩
    subst selectedName
    subst selectedObject
    subst selectedDefinition
    exact pathDenotes
  · intro pathDenotes
    exact ⟨responseName, parentObject, definition,
      ⟨rfl, rfl, rfl⟩, pathDenotes⟩

/-- Introduces the singleton field path of an active definition. -/
theorem singletonDefinitionShape_denotesPath_field
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType parentObject responseName : Name)
    (definition : ShapeDefinition)
    (runtimePossible :
      schema.typeIncludesObject parentType parentObject)
    (clauseHolds : definition.clause.HoldsIn assignment) :
    ResponseShape.DenotesPath schema assignment parentType
      (singletonDefinitionShape parentObject responseName definition)
      [{ parentObject := parentObject
         responseName := responseName
         field := definition.field }] := by
  apply (singletonDefinitionShape_denotesPath_iff schema assignment parentType
    parentObject responseName definition _).mpr
  exact ⟨runtimePossible, clauseHolds, Or.inl rfl⟩

/-- Introduces a singleton path by prefixing a path of the stored child. -/
theorem singletonDefinitionShape_denotesPath_child
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType parentObject responseName : Name)
    (definition : ShapeDefinition) (childShape : ResponseShape)
    (childPath : List PathStep)
    (runtimePossible :
      schema.typeIncludesObject parentType parentObject)
    (clauseHolds : definition.clause.HoldsIn assignment)
    (subshapeEq : definition.subshape = some childShape)
    (childDenotes :
      ResponseShape.DenotesPath schema assignment
        definition.field.outputType.namedType childShape childPath) :
    ResponseShape.DenotesPath schema assignment parentType
      (singletonDefinitionShape parentObject responseName definition)
      ({ parentObject := parentObject
         responseName := responseName
         field := definition.field } :: childPath) := by
  apply (singletonDefinitionShape_denotesPath_iff schema assignment parentType
    parentObject responseName definition _).mpr
  exact ⟨runtimePossible, clauseHolds,
    Or.inr ⟨childShape, childPath, subshapeEq, childDenotes, rfl⟩⟩

/-- Inserting a definition group adds exactly the paths of that group. -/
theorem insertPossibleDefinitions_denotesPath_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name)
    (incoming : PossibleDefinitions) (groups : List PossibleDefinitions)
    (path : List PathStep) :
    ResponseShape.DenotesPath schema assignment parentType
        (.object [.mk responseName
          (insertPossibleDefinitions incoming groups)]) path ↔
      ResponseShape.DenotesPath schema assignment parentType
          (.object [.mk responseName groups]) path
      ∨ ResponseShape.DenotesPath schema assignment parentType
          (.object [.mk responseName [incoming]]) path := by
  apply denotesPath_split_iff
  intro selectedName runtimeObject definition
  simp only [positionsContainDefinition_singleton_iff,
    ResponsePosition.responseName, ResponsePosition.possibleDefinitions]
  rw [groupsContainDefinition_insert_iff,
    groupsContainDefinition_singleton_iff]
  constructor
  · rintro ⟨nameEq, groupContains | incomingContains⟩
    · exact Or.inl ⟨nameEq, groupContains⟩
    · exact Or.inr ⟨nameEq, incomingContains⟩
  · rintro (⟨nameEq, groupContains⟩ | ⟨nameEq, incomingContains⟩)
    · exact ⟨nameEq, Or.inl groupContains⟩
    · exact ⟨nameEq, Or.inr incomingContains⟩

/-- Existing definition-group paths survive insertion. -/
theorem insertPossibleDefinitions_denotesPath_existing
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name)
    (incoming : PossibleDefinitions) (groups : List PossibleDefinitions)
    (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName groups]) path) :
    ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName
        (insertPossibleDefinitions incoming groups)]) path :=
  (insertPossibleDefinitions_denotesPath_iff schema assignment parentType
    responseName incoming groups path).mpr (Or.inl hdenotes)

/-- The inserted definition group's paths occur in the result. -/
theorem insertPossibleDefinitions_denotesPath_incoming
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name)
    (incoming : PossibleDefinitions) (groups : List PossibleDefinitions)
    (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName [incoming]]) path) :
    ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName
        (insertPossibleDefinitions incoming groups)]) path :=
  (insertPossibleDefinitions_denotesPath_iff schema assignment parentType
    responseName incoming groups path).mpr (Or.inr hdenotes)

/-- Merging definition-group lists denotes exactly the union of their paths. -/
theorem mergePossibleDefinitions_denotesPath_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name)
    (left right : List PossibleDefinitions) (path : List PathStep) :
    ResponseShape.DenotesPath schema assignment parentType
        (.object [.mk responseName
          (mergePossibleDefinitions left right)]) path ↔
      ResponseShape.DenotesPath schema assignment parentType
          (.object [.mk responseName left]) path
      ∨ ResponseShape.DenotesPath schema assignment parentType
          (.object [.mk responseName right]) path := by
  apply denotesPath_split_iff
  intro selectedName runtimeObject definition
  simp only [positionsContainDefinition_singleton_iff,
    ResponsePosition.responseName, ResponsePosition.possibleDefinitions]
  rw [groupsContainDefinition_merge_iff]
  constructor
  · rintro ⟨nameEq, leftContains | rightContains⟩
    · exact Or.inl ⟨nameEq, leftContains⟩
    · exact Or.inr ⟨nameEq, rightContains⟩
  · rintro (⟨nameEq, leftContains⟩ | ⟨nameEq, rightContains⟩)
    · exact ⟨nameEq, Or.inl leftContains⟩
    · exact ⟨nameEq, Or.inr rightContains⟩

/-- Left definition-group paths survive a definition-group merge. -/
theorem mergePossibleDefinitions_denotesPath_left
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name)
    (left right : List PossibleDefinitions) (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName left]) path) :
    ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName
        (mergePossibleDefinitions left right)]) path :=
  (mergePossibleDefinitions_denotesPath_iff schema assignment parentType
    responseName left right path).mpr (Or.inl hdenotes)

/-- Right definition-group paths occur in a definition-group merge. -/
theorem mergePossibleDefinitions_denotesPath_right
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name)
    (left right : List PossibleDefinitions) (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName right]) path) :
    ResponseShape.DenotesPath schema assignment parentType
      (.object [.mk responseName
        (mergePossibleDefinitions left right)]) path :=
  (mergePossibleDefinitions_denotesPath_iff schema assignment parentType
    responseName left right path).mpr (Or.inr hdenotes)

/-- Inserting a response position adds exactly the paths of that position. -/
theorem insertResponsePosition_denotesPath_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (incoming : ResponsePosition)
    (positions : List ResponsePosition) (path : List PathStep) :
    ResponseShape.DenotesPath schema assignment parentType
        (.object (insertResponsePosition incoming positions)) path ↔
      ResponseShape.DenotesPath schema assignment parentType
          (.object positions) path
      ∨ ResponseShape.DenotesPath schema assignment parentType
          (.object [incoming]) path := by
  apply denotesPath_split_iff
  intro responseName runtimeObject definition
  rw [positionsContainDefinition_insert_iff,
    positionsContainDefinition_singleton_iff]

/-- Existing response-position paths survive insertion. -/
theorem insertResponsePosition_denotesPath_existing
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (incoming : ResponsePosition)
    (positions : List ResponsePosition) (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      (.object positions) path) :
    ResponseShape.DenotesPath schema assignment parentType
      (.object (insertResponsePosition incoming positions)) path :=
  (insertResponsePosition_denotesPath_iff schema assignment parentType
    incoming positions path).mpr (Or.inl hdenotes)

/-- The inserted response position's paths occur in the result. -/
theorem insertResponsePosition_denotesPath_incoming
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (incoming : ResponsePosition)
    (positions : List ResponsePosition) (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      (.object [incoming]) path) :
    ResponseShape.DenotesPath schema assignment parentType
      (.object (insertResponsePosition incoming positions)) path :=
  (insertResponsePosition_denotesPath_iff schema assignment parentType
    incoming positions path).mpr (Or.inr hdenotes)

/-- Response-shape merge denotes exactly the union of its input paths. -/
theorem mergeResponseShapes_denotesPath_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (left right : ResponseShape)
    (path : List PathStep) :
    ResponseShape.DenotesPath schema assignment parentType
        (mergeResponseShapes left right) path ↔
      ResponseShape.DenotesPath schema assignment parentType left path
      ∨ ResponseShape.DenotesPath schema assignment parentType right path := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold mergeResponseShapes
          apply denotesPath_split_iff
          intro responseName runtimeObject definition
          exact positionsContainDefinition_fold_iff rightPositions leftPositions
            responseName runtimeObject definition

/-- Left paths survive response-shape merge. -/
theorem mergeResponseShapes_denotesPath_left
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (left right : ResponseShape)
    (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      left path) :
    ResponseShape.DenotesPath schema assignment parentType
      (mergeResponseShapes left right) path :=
  (mergeResponseShapes_denotesPath_iff schema assignment parentType
    left right path).mpr (Or.inl hdenotes)

/-- Right paths occur in response-shape merge. -/
theorem mergeResponseShapes_denotesPath_right
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (left right : ResponseShape)
    (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      right path) :
    ResponseShape.DenotesPath schema assignment parentType
      (mergeResponseShapes left right) path :=
  (mergeResponseShapes_denotesPath_iff schema assignment parentType
    left right path).mpr (Or.inr hdenotes)

/-- Inverts a merged path to the input shape which already denoted it. -/
theorem mergeResponseShapes_denotesPath_cases
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (left right : ResponseShape)
    (path : List PathStep)
    (hdenotes : ResponseShape.DenotesPath schema assignment parentType
      (mergeResponseShapes left right) path) :
    ResponseShape.DenotesPath schema assignment parentType left path
    ∨ ResponseShape.DenotesPath schema assignment parentType right path :=
  (mergeResponseShapes_denotesPath_iff schema assignment parentType
    left right path).mp hdenotes

end ResponseShape

end GraphQL
