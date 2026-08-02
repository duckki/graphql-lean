import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.ReorderingVariables
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.BoolCases
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.CaseBodies
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff
import Proofs.GraphQL.Theories.NormalForm.SelectionReordering
import Proofs.GraphQL.Theories.ResponseShape.Comparison.Subset
import Proofs.GraphQL.Theories.ResponseShape.Compute.RootInvariant
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Operation
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Reification
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.ReorderingFootprint
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.WrappedCaseBranches

/-!
Canonicity of response shapes computed from complete-normal operations.
-/

namespace GraphQL

namespace ResponseShape

open NormalForm
open NormalForm.CompleteNormalization

private structure ActiveDefinitionWitness
    (schema : Schema) (assignment : BoolCase) (parentType runtimeObject : Name)
    (shape : ResponseShape) (responseName : Name)
    (definition : ShapeDefinition)
    : Type where
  position : ResponsePosition
  positionMem : position ∈ shape.positions
  responseName_eq : position.responseName = responseName
  possible : PossibleDefinitions
  possibleMem : possible ∈ position.possibleDefinitions
  runtimeMem : runtimeObject ∈ possible.objectTypes
  runtimePossible : schema.typeIncludesObject parentType runtimeObject
  definitionMem : definition ∈ possible.definitions
  clauseHolds : definition.clause.HoldsIn assignment

private theorem eq_of_map_nodup_of_mem
    {α β : Type} {key : α → β} {items : List α}
    (hnodup : (items.map key).Nodup)
    {left right : α} (hleft : left ∈ items) (hright : right ∈ items)
    (heq : key left = key right)
    : left = right := by
  induction items generalizing left right with
  | nil => simp at hleft
  | cons head tail ih =>
      have hparts : key head ∉ tail.map key ∧ (tail.map key).Nodup := by
        simpa using hnodup
      rcases List.mem_cons.mp hleft with hleftHead | hleftTail
      · subst left
        rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · subst right
          rfl
        · exact False.elim
            (hparts.1 (List.mem_map.mpr ⟨right, hrightTail, heq.symm⟩))
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · subst right
          exact False.elim
            (hparts.1 (List.mem_map.mpr ⟨left, hleftTail, heq⟩))
        · exact ih hparts.2 hleftTail hrightTail heq

private theorem list_map_nodup_of_injective
    {α β : Type} {items : List α} (key : α → β)
    (hnodup : items.Nodup) (hinjective : Function.Injective key)
    : (items.map key).Nodup := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      have hparts : head ∉ tail ∧ tail.Nodup := by simpa using hnodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨candidate, hcandidate, heq⟩
        exact hparts.1 (hinjective heq.symm ▸ hcandidate)
      · exact ih hparts.2

private theorem filterMap_nodup_of_injective_on
    {α β : Type} {items : List α} (key : α → Option β)
    (hnodup : items.Nodup)
    (hinjective
      : ∀ left,
          left ∈ items → ∀ right, right ∈ items → key left = key right → left = right)
    : (items.filterMap key).Nodup := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      have hparts := List.nodup_cons.mp hnodup
      cases hkey : key head with
      | none =>
          simp only [List.filterMap_cons, hkey]
          apply ih hparts.2
          intro left hleft right hright heq
          exact hinjective left (List.mem_cons_of_mem head hleft) right
            (List.mem_cons_of_mem head hright) heq
      | some value =>
          simp only [List.filterMap_cons, hkey, List.nodup_cons]
          constructor
          · intro hmem
            rw [List.mem_filterMap] at hmem
            rcases hmem with ⟨candidate, hcandidate, hcandidateKey⟩
            have heq : head = candidate :=
              hinjective head (by simp) candidate
                (List.mem_cons_of_mem head hcandidate)
                (hkey.trans hcandidateKey.symm)
            exact hparts.1 (heq ▸ hcandidate)
          · apply ih hparts.2
            intro left hleft right hright heq
            exact hinjective left (List.mem_cons_of_mem head hleft) right
              (List.mem_cons_of_mem head hright) heq

private theorem singleton_map_injective {α : Type}
    : Function.Injective (fun item : α => [item]) := by
  intro left right heq
  simpa using heq

private theorem ActiveDefinitionWitness.unique
    {schema : Schema} {support : List BoolVar} {assignment : BoolCase}
    {parentType runtimeObject : Name} {shape : ResponseShape}
    (hinvariant : DecoderShapeInvariant schema support parentType shape)
    {responseName : Name} {left right : ShapeDefinition}
    (hleft
      : ActiveDefinitionWitness schema assignment parentType runtimeObject shape
          responseName left)
    (hright
      : ActiveDefinitionWitness schema assignment parentType runtimeObject shape
          responseName right)
    : left = right := by
  rcases hleft with ⟨leftPosition, hleftPositionMem, hleftResponseName,
    leftPossible, hleftPossibleMem, hleftRuntimeMem, hleftRuntimePossible,
    hleftDefinitionMem, hleftClauseHolds⟩
  rcases hright with ⟨rightPosition, hrightPositionMem, hrightResponseName,
    rightPossible, hrightPossibleMem, hrightRuntimeMem, hrightRuntimePossible,
    hrightDefinitionMem, hrightClauseHolds⟩
  cases shape with
  | object positions =>
      rcases hinvariant with ⟨hpositionsNodup, hpositions⟩
      have hpositionEq : leftPosition = rightPosition := by
        apply eq_of_map_nodup_of_mem hpositionsNodup hleftPositionMem
          hrightPositionMem
        exact hleftResponseName.trans hrightResponseName.symm
      subst rightPosition
      rcases hpositions leftPosition hleftPositionMem with
        ⟨objectTypes, hobjects, hobjectsNodup, hgroups⟩
      have hgroupKeysNodup :
          (leftPosition.possibleDefinitions.map
            PossibleDefinitions.objectTypes).Nodup := by
        rw [hobjects]
        exact list_map_nodup_of_injective (fun item : GroundObject => [item])
          hobjectsNodup singleton_map_injective
      have hleftSingleton : leftPossible.objectTypes = [runtimeObject] := by
        have hkeyMem : leftPossible.objectTypes ∈
            leftPosition.possibleDefinitions.map
              PossibleDefinitions.objectTypes :=
          List.mem_map.mpr ⟨leftPossible, hleftPossibleMem, rfl⟩
        rw [hobjects] at hkeyMem
        rcases List.mem_map.mp hkeyMem with ⟨objectType, _hobjectType, heq⟩
        rw [← heq] at hleftRuntimeMem
        have : runtimeObject = objectType := by simpa using hleftRuntimeMem
        subst objectType
        exact heq.symm
      have hrightSingleton : rightPossible.objectTypes = [runtimeObject] := by
        have hkeyMem : rightPossible.objectTypes ∈
            leftPosition.possibleDefinitions.map
              PossibleDefinitions.objectTypes :=
          List.mem_map.mpr ⟨rightPossible, hrightPossibleMem, rfl⟩
        rw [hobjects] at hkeyMem
        rcases List.mem_map.mp hkeyMem with ⟨objectType, _hobjectType, heq⟩
        rw [← heq] at hrightRuntimeMem
        have : runtimeObject = objectType := by simpa using hrightRuntimeMem
        subst objectType
        exact heq.symm
      have hpossibleEq : leftPossible = rightPossible := by
        apply eq_of_map_nodup_of_mem hgroupKeysNodup hleftPossibleMem
          hrightPossibleMem
        exact hleftSingleton.trans hrightSingleton.symm
      subst rightPossible
      rcases hgroups leftPossible hleftPossibleMem with
        ⟨_hground, hclausesNodup, hdefinitions⟩
      have hclauseEq : left.clause = right.clause := by
        apply Clause.eq_of_completeMinterm_of_holdsInBool
          (hdefinitions left hleftDefinitionMem).2
          (hdefinitions right hrightDefinitionMem).2
        · exact (Clause.holdsInBool_iff assignment left.clause).2
            hleftClauseHolds
        · exact (Clause.holdsInBool_iff assignment right.clause).2
            hrightClauseHolds
      exact eq_of_map_nodup_of_mem hclausesNodup hleftDefinitionMem
        hrightDefinitionMem hclauseEq

private theorem ActiveDefinitionWitness.denotesSingleton
    {schema : Schema} {assignment : BoolCase} {parentType runtimeObject : Name}
    {shape : ResponseShape} {responseName : Name}
    {definition : ShapeDefinition}
    (hactive
      : ActiveDefinitionWitness schema assignment parentType runtimeObject shape
          responseName definition)
    : shape.DenotesPath schema assignment parentType
        [{
          parentObject := runtimeObject
          responseName := responseName
          field := definition.field
        }] := by
  rcases hactive with ⟨position, hposition, hresponse, possible, hpossible,
    hruntime, hincludes, hdefinition, hclause⟩
  cases shape with
  | object positions =>
      change position ∈ positions at hposition
      change ResponseShape.DenotesPath schema assignment parentType
        (.object positions)
        [{ parentObject := runtimeObject
           responseName := responseName
           field := definition.field }]
      simpa [hresponse] using
        (ResponseShape.DenotesPath.field hincludes hposition hpossible hruntime
          hdefinition hclause)

private theorem activeDefinitionAt_of_denotesSingleton
    {schema : Schema} {assignment : BoolCase} {parentType : Name}
    {shape : ResponseShape} {step : PathStep}
    (hdenotes : shape.DenotesPath schema assignment parentType [step])
    : ∃ definition,
      ∃ _active
          : ActiveDefinitionWitness schema assignment parentType
              step.parentObject shape step.responseName definition,
        definition.field = step.field := by
  cases hdenotes with
  | field runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds =>
      exact ⟨_,
        ⟨_, positionMem, rfl, _, possibleMem, runtimeMem, runtimePossible,
          definitionMem, clauseHolds⟩,
        rfl⟩
  | child runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds subshapeEq childDenotes =>
      exact False.elim (childDenotes.nonempty rfl)

private theorem mem_reifyShapeDefinitions_iff
    (schema : Schema) (assignment : BoolCase) (responseName : Name)
    (selection : Selection)
    : ∀ definitions : List ShapeDefinition,
        selection ∈ reifyShapeDefinitions schema assignment responseName definitions
        ↔ ∃ definition,
            definition ∈ definitions
            ∧ definition.clause.HoldsIn assignment
            ∧ selection = definition.reifyField schema assignment responseName
  | [] => by simp [reifyShapeDefinitions]
  | definition :: rest => by
      by_cases hholds : definition.clause.HoldsIn assignment
      · have hbool : definition.clause.holdsInBool assignment = true :=
          (Clause.holdsInBool_iff assignment definition.clause).2 hholds
        simp [reifyShapeDefinitions, hbool, hholds,
          mem_reifyShapeDefinitions_iff schema assignment responseName
            selection rest]
      · have hbool : definition.clause.holdsInBool assignment = false := by
          cases heq : definition.clause.holdsInBool assignment
          · rfl
          · exact False.elim
              (hholds ((Clause.holdsInBool_iff assignment definition.clause).1
                heq))
        simp [reifyShapeDefinitions, hbool, hholds,
          mem_reifyShapeDefinitions_iff schema assignment responseName
            selection rest]

private theorem mem_reifyPossibleDefinitions_iff
    (schema : Schema) (assignment : BoolCase) (runtimeObject : GroundObject)
    (responseName : Name) (selection : Selection)
    : ∀ possibles : List PossibleDefinitions,
        selection
          ∈ reifyPossibleDefinitions schema assignment runtimeObject
              responseName possibles
        ↔ ∃ possible,
            possible ∈ possibles
            ∧ runtimeObject ∈ possible.objectTypes
            ∧ ∃ definition,
                definition ∈ possible.definitions
                ∧ definition.clause.HoldsIn assignment
                ∧ selection = definition.reifyField schema assignment responseName
  | [] => by simp [reifyPossibleDefinitions]
  | possible :: rest => by
      cases possible with
      | mk objectTypes definitions =>
          simp [reifyPossibleDefinitions, PossibleDefinitions.reifyFields,
            PossibleDefinitions.objectTypes, PossibleDefinitions.definitions,
            mem_reifyShapeDefinitions_iff schema assignment responseName
              selection definitions,
            mem_reifyPossibleDefinitions_iff schema assignment runtimeObject
              responseName selection rest]

private theorem mem_reifyResponsePositions_iff
    (schema : Schema) (assignment : BoolCase) (runtimeObject : GroundObject)
    (selection : Selection)
    : ∀ positions : List ResponsePosition,
        selection ∈ reifyResponsePositions schema assignment runtimeObject positions
        ↔ ∃ position,
            position ∈ positions
            ∧ ∃ possible,
                possible ∈ position.possibleDefinitions
                ∧ runtimeObject ∈ possible.objectTypes
                ∧ ∃ definition,
                    definition ∈ possible.definitions
                    ∧ definition.clause.HoldsIn assignment
                    ∧ selection
                      = definition.reifyField schema assignment position.responseName
  | [] => by simp [reifyResponsePositions]
  | position :: rest => by
      cases position with
      | mk responseName possibles =>
          simp [reifyResponsePositions, ResponsePosition.reifyFields,
            ResponsePosition.possibleDefinitions, ResponsePosition.responseName,
            mem_reifyPossibleDefinitions_iff schema assignment runtimeObject
              responseName selection possibles,
            mem_reifyResponsePositions_iff schema assignment runtimeObject
              selection rest]

private theorem reifyShapeDefinitions_length_eq
    (schema : Schema) (assignment : BoolCase) (responseName : Name)
    : ∀ definitions : List ShapeDefinition,
        (reifyShapeDefinitions schema assignment responseName definitions).length
        = ((definitions.map ShapeDefinition.clause).filter
            (fun clause => clause.holdsInBool assignment)).length
  | [] => rfl
  | definition :: rest => by
      cases hholds : definition.clause.holdsInBool assignment <;>
        simp [reifyShapeDefinitions, hholds,
          reifyShapeDefinitions_length_eq schema assignment responseName rest]

private theorem reifyShapeDefinitions_length_le_one
    (schema : Schema) (support : List BoolVar) (assignment : BoolCase)
    (responseName : Name) (definitions : List ShapeDefinition)
    (hclauses : (definitions.map ShapeDefinition.clause).Nodup)
    (hinvariant : decoderDefinitionsInvariant schema support definitions)
    : (reifyShapeDefinitions schema assignment responseName definitions).length ≤ 1 := by
  rw [reifyShapeDefinitions_length_eq]
  apply Clause.filter_holdsInBool_length_le_one assignment
    (definitions.map ShapeDefinition.clause) hclauses
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨definition, hdefinition, rfl⟩
  exact (hinvariant definition hdefinition).2

private theorem reifyPossibleDefinitions_eq_nil_of_runtime_not_mem
    (schema : Schema) (assignment : BoolCase) (runtimeObject : GroundObject)
    (responseName : Name)
    : ∀ possibles : List PossibleDefinitions,
        (∀ possible ∈ possibles, runtimeObject ∉ possible.objectTypes)
        → reifyPossibleDefinitions schema assignment runtimeObject responseName possibles
          = []
  | [], _hnot => rfl
  | possible :: rest, hnot => by
      have hhead := hnot possible (by simp)
      have hrest : ∀ candidate ∈ rest,
          runtimeObject ∉ candidate.objectTypes := by
        intro candidate hcandidate
        exact hnot candidate (List.mem_cons_of_mem possible hcandidate)
      cases possible with
      | mk objectTypes definitions =>
          change runtimeObject ∉ objectTypes at hhead
          have hcontains : objectTypes.contains runtimeObject = false := by
            cases heq : objectTypes.contains runtimeObject
            · rfl
            · exact False.elim (hhead (List.contains_iff_mem.mp heq))
          simp [reifyPossibleDefinitions, PossibleDefinitions.reifyFields,
            hhead,
            reifyPossibleDefinitions_eq_nil_of_runtime_not_mem schema assignment
              runtimeObject responseName rest hrest]

private theorem reifyPossibleDefinitions_length_le_one
    (schema : Schema) (support : List BoolVar) (assignment : BoolCase)
    (parentType : Name) (runtimeObject : GroundObject) (responseName : Name)
    (possibles : List PossibleDefinitions)
    (hinvariant
      : ∃ objectTypes : List GroundObject,
          possibles.map PossibleDefinitions.objectTypes
            = objectTypes.map (fun objectType => [objectType])
          ∧ objectTypes.Nodup
          ∧ ∀ possible ∈ possibles,
              DecoderGroupInvariant schema support parentType possible)
    : (reifyPossibleDefinitions schema assignment runtimeObject responseName
        possibles).length
      ≤ 1 := by
  rcases hinvariant with ⟨objectTypes, hobjects, hobjectsNodup, hgroups⟩
  induction possibles generalizing objectTypes with
  | nil => simp [reifyPossibleDefinitions]
  | cons possible rest ih =>
      cases objectTypes with
      | nil => simp at hobjects
      | cons objectType objectTypes =>
          have hobjectParts := List.cons.inj hobjects
          have hpossibleObjects : possible.objectTypes = [objectType] :=
            hobjectParts.1
          have hrestObjects : rest.map PossibleDefinitions.objectTypes =
              objectTypes.map (fun candidate => [candidate]) :=
            hobjectParts.2
          have hnodupParts : objectType ∉ objectTypes ∧ objectTypes.Nodup := by
            simpa using hobjectsNodup
          have hrestGroups : ∀ candidate ∈ rest,
              DecoderGroupInvariant schema support parentType candidate := by
            intro candidate hcandidate
            exact hgroups candidate (List.mem_cons_of_mem possible hcandidate)
          cases possible with
          | mk possibleObjects definitions =>
              change possibleObjects = [objectType] at hpossibleObjects
              by_cases hruntime : runtimeObject = objectType
              · subst objectType
                have hrestNot : ∀ candidate ∈ rest,
                    runtimeObject ∉ candidate.objectTypes := by
                  intro candidate hcandidate hruntimeMem
                  have hkeyMem : candidate.objectTypes ∈
                      rest.map PossibleDefinitions.objectTypes :=
                    List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩
                  rw [hrestObjects] at hkeyMem
                  rcases List.mem_map.mp hkeyMem with
                    ⟨candidateObject, hcandidateObject, heq⟩
                  rw [← heq] at hruntimeMem
                  have : runtimeObject = candidateObject := by
                    simpa using hruntimeMem
                  exact hnodupParts.1 (this ▸ hcandidateObject)
                have hrestEmpty :=
                  reifyPossibleDefinitions_eq_nil_of_runtime_not_mem schema
                    assignment runtimeObject responseName rest hrestNot
                rcases hgroups (.mk possibleObjects definitions) (by simp) with
                  ⟨_hground, hclauses, hdefinitions⟩
                have hheadMem : runtimeObject ∈ possibleObjects := by
                  rw [hpossibleObjects]
                  simp
                simp [reifyPossibleDefinitions, PossibleDefinitions.reifyFields,
                  hheadMem, hrestEmpty]
                exact reifyShapeDefinitions_length_le_one schema support assignment
                  responseName definitions hclauses hdefinitions
              · have hheadNot : runtimeObject ∉ possibleObjects := by
                  rw [hpossibleObjects]
                  simp [hruntime]
                simp [reifyPossibleDefinitions, PossibleDefinitions.reifyFields,
                  hheadNot]
                exact ih objectTypes hrestObjects hnodupParts.2 hrestGroups

private theorem selection_responseName_of_mem_reifyPossibleDefinitions
    (schema : Schema) (assignment : BoolCase) (runtimeObject : GroundObject)
    (responseName : Name) (possibles : List PossibleDefinitions)
    {selection : Selection}
    (hselection
      : selection
        ∈ reifyPossibleDefinitions schema assignment runtimeObject responseName possibles)
    : selection.responseName? = some responseName := by
  rcases (mem_reifyPossibleDefinitions_iff schema assignment runtimeObject
      responseName selection possibles).1 hselection with
    ⟨possible, _hpossible, _hruntime, definition, _hdefinition, _hholds,
      hselectionEq⟩
  subst selection
  cases definition
  simp [ShapeDefinition.reifyField, Selection.responseName?]

private theorem list_nodup_of_length_le_one {α : Type} {items : List α}
    (hlength : items.length ≤ 1)
    : items.Nodup := by
  cases items with
  | nil => simp
  | cons head tail =>
      cases tail with
      | nil => simp
      | cons next rest => simp at hlength

private theorem reifyResponsePositions_nodup
    (schema : Schema) (support : List BoolVar) (assignment : BoolCase)
    (parentType runtimeObject : Name) (positions : List ResponsePosition)
    (hinvariant
      : (positions.map ResponsePosition.responseName).Nodup
        ∧ decoderPositionsInvariant schema support parentType positions)
    : (reifyResponsePositions schema assignment runtimeObject positions).Nodup := by
  rcases hinvariant with ⟨hnames, hpositions⟩
  induction positions with
  | nil => simp [reifyResponsePositions]
  | cons position rest ih =>
      have hnameParts : position.responseName ∉
          rest.map ResponsePosition.responseName
          ∧ (rest.map ResponsePosition.responseName).Nodup := by
        simpa using hnames
      have hpositionInvariant := hpositions position (by simp)
      have hrestInvariant : decoderPositionsInvariant schema support parentType
          rest := by
        intro candidate hcandidate
        exact hpositions candidate (List.mem_cons_of_mem position hcandidate)
      cases position with
      | mk responseName possibles =>
          have hcurrentLength :
              (reifyPossibleDefinitions schema assignment runtimeObject
                responseName possibles).length ≤ 1 := by
            exact reifyPossibleDefinitions_length_le_one schema support assignment
              parentType runtimeObject responseName possibles hpositionInvariant
          have hcurrentNodup := list_nodup_of_length_le_one hcurrentLength
          have hrestNodup := ih hnameParts.2 hrestInvariant
          simp only [reifyResponsePositions, ResponsePosition.reifyFields]
          apply List.nodup_append.mpr
          refine ⟨hcurrentNodup, hrestNodup, ?_⟩
          intro leftSelection hleft rightSelection hright heq
          subst rightSelection
          have hleftName :=
            selection_responseName_of_mem_reifyPossibleDefinitions schema
              assignment runtimeObject responseName possibles hleft
          rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject
              leftSelection rest).1 hright with
            ⟨rightPosition, hrightPosition, rightPossible, hrightPossible,
              hrightRuntime, rightDefinition, hrightDefinition, hrightHolds,
              hrightEq⟩
          have hrightName : leftSelection.responseName? =
              some rightPosition.responseName := by
            subst leftSelection
            cases rightDefinition
            simp [ShapeDefinition.reifyField, Selection.responseName?]
          have hresponseEq : responseName = rightPosition.responseName :=
            Option.some.inj (hleftName.symm.trans hrightName)
          exact hnameParts.1
            (List.mem_map.mpr ⟨rightPosition, hrightPosition, hresponseEq.symm⟩)

private theorem reifiedSelection_eq_of_responseName
    (schema : Schema) (support : List BoolVar) (assignment : BoolCase)
    (parentType runtimeObject : Name) (shape : ResponseShape)
    (hinvariant : DecoderShapeInvariant schema support parentType shape)
    (hincludes : schema.typeIncludesObject parentType runtimeObject)
    {left right : Selection}
    (hleft
      : left ∈ reifyResponsePositions schema assignment runtimeObject shape.positions)
    (hright
      : right ∈ reifyResponsePositions schema assignment runtimeObject shape.positions)
    (hresponse : left.responseName? = right.responseName?)
    : left = right := by
  rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject left
      shape.positions).1 hleft with
    ⟨leftPosition, hleftPosition, leftPossible, hleftPossible, hleftRuntime,
      leftDefinition, hleftDefinition, hleftHolds, hleftEq⟩
  rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject right
      shape.positions).1 hright with
    ⟨rightPosition, hrightPosition, rightPossible, hrightPossible, hrightRuntime,
      rightDefinition, hrightDefinition, hrightHolds, hrightEq⟩
  have hleftName : left.responseName? = some leftPosition.responseName := by
    rw [hleftEq]
    cases leftDefinition
    simp [ShapeDefinition.reifyField, Selection.responseName?]
  have hrightName : right.responseName? = some rightPosition.responseName := by
    rw [hrightEq]
    cases rightDefinition
    simp [ShapeDefinition.reifyField, Selection.responseName?]
  have hnameEq : leftPosition.responseName = rightPosition.responseName :=
    Option.some.inj (hleftName.symm.trans (hresponse.trans hrightName))
  let leftActive : ActiveDefinitionWitness schema assignment parentType
      runtimeObject shape leftPosition.responseName leftDefinition :=
    ⟨leftPosition, hleftPosition, rfl, leftPossible, hleftPossible,
      hleftRuntime, hincludes, hleftDefinition, hleftHolds⟩
  let rightActiveAtOwnName : ActiveDefinitionWitness schema assignment parentType
      runtimeObject shape rightPosition.responseName rightDefinition :=
    ⟨rightPosition, hrightPosition, rfl, rightPossible, hrightPossible,
      hrightRuntime, hincludes, hrightDefinition, hrightHolds⟩
  let rightActive : ActiveDefinitionWitness schema assignment parentType
      runtimeObject shape leftPosition.responseName rightDefinition := by
    simpa [hnameEq] using rightActiveAtOwnName
  have hdefinitionEq : leftDefinition = rightDefinition :=
    ActiveDefinitionWitness.unique hinvariant leftActive rightActive
  subst rightDefinition
  rw [hleftEq, hrightEq, hnameEq]

private theorem ActiveDefinitionWitness.invariant
    {schema : Schema} {support : List BoolVar} {assignment : BoolCase}
    {parentType runtimeObject : Name} {shape : ResponseShape}
    {responseName : Name} {definition : ShapeDefinition}
    (hinvariant : DecoderShapeInvariant schema support parentType shape)
    (hactive
      : ActiveDefinitionWitness schema assignment parentType runtimeObject
          shape responseName definition)
    : DecoderDefinitionInvariant schema support definition := by
  cases shape with
  | object positions =>
      rcases hinvariant with ⟨_hnames, hpositions⟩
      rcases hpositions hactive.position hactive.positionMem with
        ⟨_objectTypes, _hobjects, _hnodup, hgroups⟩
      exact (hgroups hactive.possible hactive.possibleMem).2.2 definition
        hactive.definitionMem

mutual
  private inductive RecursiveDecoderShapeInvariant
      (schema : Schema) (support : List BoolVar)
      : Name → ResponseShape → Prop where
    | object (parentType : Name) (positions : List ResponsePosition)
      (shallow : DecoderShapeInvariant schema support parentType (.object positions))
      (positionsInvariant : positionsRecursivelyInvariant schema support positions)
      : RecursiveDecoderShapeInvariant schema support parentType (.object positions)

  private inductive positionsRecursivelyInvariant
      (schema : Schema) (support : List BoolVar)
      : List ResponsePosition → Prop where
    | nil : positionsRecursivelyInvariant schema support []
    | cons (position : ResponsePosition) (rest : List ResponsePosition)
      (head : groupsRecursivelyInvariant schema support position.possibleDefinitions)
      (tail : positionsRecursivelyInvariant schema support rest)
      : positionsRecursivelyInvariant schema support (position :: rest)

  private inductive groupsRecursivelyInvariant (schema : Schema) (support : List BoolVar)
      : List PossibleDefinitions → Prop where
    | nil : groupsRecursivelyInvariant schema support []
    | cons (possible : PossibleDefinitions) (rest : List PossibleDefinitions)
      (head : definitionsRecursivelyInvariant schema support possible.definitions)
      (tail : groupsRecursivelyInvariant schema support rest)
      : groupsRecursivelyInvariant schema support (possible :: rest)

  private inductive definitionsRecursivelyInvariant
      (schema : Schema) (support : List BoolVar)
      : List ShapeDefinition → Prop where
    | nil : definitionsRecursivelyInvariant schema support []
    | leaf (definition : ShapeDefinition) (rest : List ShapeDefinition)
      (hleaf : definition.subshape = none)
      (tail : definitionsRecursivelyInvariant schema support rest)
      : definitionsRecursivelyInvariant schema support (definition :: rest)
    | child (definition : ShapeDefinition) (rest : List ShapeDefinition)
      (childShape : ResponseShape)
      (hchild : definition.subshape = some childShape)
      (childInvariant
        : RecursiveDecoderShapeInvariant schema support
            definition.field.outputType.namedType childShape)
      (tail : definitionsRecursivelyInvariant schema support rest)
      : definitionsRecursivelyInvariant schema support (definition :: rest)
end

private theorem RecursiveDecoderShapeInvariant.shallow
    {schema : Schema} {support : List BoolVar} {parentType : Name}
    {shape : ResponseShape}
    (hinvariant : RecursiveDecoderShapeInvariant schema support parentType shape)
    : DecoderShapeInvariant schema support parentType shape := by
  cases shape
  cases hinvariant with
  | object parentType positions shallow positionsInvariant => exact shallow

private theorem RecursiveDecoderShapeInvariant.positionsInvariant
    {schema : Schema} {support : List BoolVar} {parentType : Name}
    {shape : ResponseShape}
    (hinvariant : RecursiveDecoderShapeInvariant schema support parentType shape)
    : positionsRecursivelyInvariant schema support shape.positions := by
  cases hinvariant with
  | object parentType positions shallow positionsInvariant =>
      exact positionsInvariant

private theorem definitionsRecursivelyInvariant_of_mem
    {schema : Schema} {support : List BoolVar}
    {definitions : List ShapeDefinition}
    (hinvariant : definitionsRecursivelyInvariant schema support definitions)
    {definition : ShapeDefinition} (hdefinition : definition ∈ definitions)
    {child : ResponseShape} (hchild : definition.subshape = some child)
    : RecursiveDecoderShapeInvariant schema support
        definition.field.outputType.namedType child := by
  induction definitions with
  | nil => simp at hdefinition
  | cons head rest ih =>
      rcases List.mem_cons.mp hdefinition with heq | hmem
      · subst definition
        cases hinvariant with
        | leaf _ _ hleaf _ => rw [hleaf] at hchild; contradiction
        | child _ _ childShape hstored childInvariant _ =>
            rw [hstored] at hchild
            cases hchild
            exact childInvariant
      · cases hinvariant with
        | leaf _ _ _ tail => exact ih tail hmem
        | child _ _ _ _ _ tail => exact ih tail hmem

private theorem groupsRecursivelyInvariant_of_mem
    {schema : Schema} {support : List BoolVar}
    {groups : List PossibleDefinitions}
    (hinvariant : groupsRecursivelyInvariant schema support groups)
    {possible : PossibleDefinitions} (hpossible : possible ∈ groups)
    : definitionsRecursivelyInvariant schema support possible.definitions := by
  induction groups with
  | nil => simp at hpossible
  | cons head rest ih =>
      rcases List.mem_cons.mp hpossible with heq | hmem
      · subst possible
        cases hinvariant with
        | cons _ _ head tail => exact head
      · cases hinvariant with
        | cons _ _ head tail => exact ih tail hmem

private theorem positionsRecursivelyInvariant_of_mem
    {schema : Schema} {support : List BoolVar}
    {positions : List ResponsePosition}
    (hinvariant : positionsRecursivelyInvariant schema support positions)
    {position : ResponsePosition} (hposition : position ∈ positions)
    : groupsRecursivelyInvariant schema support position.possibleDefinitions := by
  induction positions with
  | nil => simp at hposition
  | cons head rest ih =>
      rcases List.mem_cons.mp hposition with heq | hmem
      · subst position
        cases hinvariant with
        | cons _ _ head tail => exact head
      · cases hinvariant with
        | cons _ _ head tail => exact ih tail hmem

private theorem RecursiveDecoderShapeInvariant.child
    {schema : Schema} {support : List BoolVar} {parentType : Name}
    {shape : ResponseShape}
    (hinvariant : RecursiveDecoderShapeInvariant schema support parentType shape)
    {position : ResponsePosition} (hposition : position ∈ shape.positions)
    {possible : PossibleDefinitions}
    (hpossible : possible ∈ position.possibleDefinitions)
    {definition : ShapeDefinition}
    (hdefinition : definition ∈ possible.definitions)
    {child : ResponseShape} (hchild : definition.subshape = some child)
    : RecursiveDecoderShapeInvariant schema support
        definition.field.outputType.namedType child := by
  cases shape with
  | object positions =>
      cases hinvariant with
      | object parentType positions shallow positionsInvariant =>
      exact definitionsRecursivelyInvariant_of_mem
        (groupsRecursivelyInvariant_of_mem
          (positionsRecursivelyInvariant_of_mem positionsInvariant hposition)
          hpossible)
        hdefinition hchild

private theorem definitionsRecursivelyInvariant_append
    {schema : Schema} {support : List BoolVar}
    {left right : List ShapeDefinition}
    (hleft : definitionsRecursivelyInvariant schema support left)
    (hright : definitionsRecursivelyInvariant schema support right)
    : definitionsRecursivelyInvariant schema support (left ++ right) := by
  induction left with
  | nil => exact hright
  | cons definition rest ih =>
      cases hleft with
      | leaf _ _ hleaf tail =>
          exact definitionsRecursivelyInvariant.leaf definition _ hleaf
            (ih tail)
      | child _ _ childShape hchild childInvariant tail =>
          exact definitionsRecursivelyInvariant.child definition _ childShape
            hchild childInvariant (ih tail)

private theorem insertPossibleDefinitions_recursive
    (schema : Schema) (support : List BoolVar)
    (incoming : PossibleDefinitions)
    (hincoming : definitionsRecursivelyInvariant schema support incoming.definitions)
    : ∀ groups,
        groupsRecursivelyInvariant schema support groups
        → groupsRecursivelyInvariant schema support
            (insertPossibleDefinitions incoming groups)
  | [], _hgroups => by
      simpa [insertPossibleDefinitions] using
        groupsRecursivelyInvariant.cons incoming [] hincoming
          groupsRecursivelyInvariant.nil
  | current :: rest, hgroups => by
      cases hgroups with
      | cons _ _ hcurrent hrest =>
      by_cases heq : current.objectTypes = incoming.objectTypes
      · have hbeq : (current.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        rw [insertPossibleDefinitions, if_pos hbeq]
        apply groupsRecursivelyInvariant.cons
        · exact definitionsRecursivelyInvariant_append hcurrent hincoming
        · exact hrest
      · have hbeq : (current.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        rw [insertPossibleDefinitions, if_neg (by simpa using hbeq)]
        exact groupsRecursivelyInvariant.cons current _ hcurrent
          (insertPossibleDefinitions_recursive schema support incoming hincoming
            rest hrest)

private theorem mergePossibleDefinitions_recursive
    (schema : Schema) (support : List BoolVar)
    (left right : List PossibleDefinitions)
    (hleft : groupsRecursivelyInvariant schema support left)
    (hright : groupsRecursivelyInvariant schema support right)
    : groupsRecursivelyInvariant schema support
        (mergePossibleDefinitions left right) := by
  unfold mergePossibleDefinitions
  induction right generalizing left with
  | nil => exact hleft
  | cons incoming rest ih =>
      cases hright with
      | cons _ _ hincoming hrest =>
          exact ih (insertPossibleDefinitions incoming left)
            (insertPossibleDefinitions_recursive schema support incoming
              hincoming left hleft)
            hrest

private theorem insertResponsePosition_recursive
    (schema : Schema) (support : List BoolVar)
    (incoming : ResponsePosition)
    (hincoming : groupsRecursivelyInvariant schema support incoming.possibleDefinitions)
    : ∀ positions,
        positionsRecursivelyInvariant schema support positions
        → positionsRecursivelyInvariant schema support
            (insertResponsePosition incoming positions)
  | [], _hpositions => by
      simpa [insertResponsePosition] using
        positionsRecursivelyInvariant.cons incoming [] hincoming
          positionsRecursivelyInvariant.nil
  | current :: rest, hpositions => by
      cases hpositions with
      | cons _ _ hcurrent hrest =>
      by_cases heq : current.responseName = incoming.responseName
      · have hbeq : (current.responseName == incoming.responseName) = true := by
          simp [heq]
        rw [insertResponsePosition, if_pos hbeq]
        apply positionsRecursivelyInvariant.cons
        · exact mergePossibleDefinitions_recursive schema support
            current.possibleDefinitions incoming.possibleDefinitions
            hcurrent hincoming
        · exact hrest
      · have hbeq : (current.responseName == incoming.responseName) = false := by
          simp [heq]
        rw [insertResponsePosition, if_neg (by simpa using hbeq)]
        exact positionsRecursivelyInvariant.cons current _ hcurrent
          (insertResponsePosition_recursive schema support incoming hincoming
            rest hrest)

private theorem foldl_insertResponsePosition_recursive
    (schema : Schema) (support : List BoolVar)
    (left right : List ResponsePosition)
    (hleft : positionsRecursivelyInvariant schema support left)
    (hright : positionsRecursivelyInvariant schema support right)
    : positionsRecursivelyInvariant schema support
        (right.foldl
          (fun merged incoming => insertResponsePosition incoming merged) left) := by
  induction right generalizing left with
  | nil => exact hleft
  | cons incoming rest ih =>
      cases hright with
      | cons _ _ hincoming hrest =>
          exact ih (insertResponsePosition incoming left)
            (insertResponsePosition_recursive schema support incoming hincoming
              left hleft)
            hrest

private theorem mergeResponseShapes_positionsRecursive
    (schema : Schema) (support : List BoolVar) (left right : ResponseShape)
    (hleft : positionsRecursivelyInvariant schema support left.positions)
    (hright : positionsRecursivelyInvariant schema support right.positions)
    : positionsRecursivelyInvariant schema support
        (mergeResponseShapes left right).positions := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          change positionsRecursivelyInvariant schema support
            (rightPositions.foldl
              (fun merged incoming => insertResponsePosition incoming merged)
              leftPositions)
          exact foldl_insertResponsePosition_recursive schema support
            leftPositions rightPositions hleft hright

private theorem mergeResponseShapes_recursive
    (schema : Schema) (support : List BoolVar) (parentType : Name)
    (left right : ResponseShape)
    (hleft : RecursiveDecoderShapeInvariant schema support parentType left)
    (hright : RecursiveDecoderShapeInvariant schema support parentType right)
    (hcompatible : MergeCompatible left right)
    : RecursiveDecoderShapeInvariant schema support parentType
        (mergeResponseShapes left right) := by
  cases hleft with
  | object _ leftPositions hleftShallow hleftChildren =>
      cases hright with
      | object _ rightPositions hrightShallow hrightChildren =>
          let mergedPositions := rightPositions.foldl
            (fun merged position => insertResponsePosition position merged)
            leftPositions
          have hrecursive : positionsRecursivelyInvariant schema support
              mergedPositions := by
            exact foldl_insertResponsePosition_recursive schema support
              leftPositions rightPositions hleftChildren hrightChildren
          apply RecursiveDecoderShapeInvariant.object parentType mergedPositions
          · simpa [mergedPositions, mergeResponseShapes] using
              mergeResponseShapes_decoderShapeInvariant schema support parentType
                (.object leftPositions) (.object rightPositions) hleftShallow
                hrightShallow hcompatible
          · exact hrecursive

private theorem mergeResponseShapes_recursive_of_shallow
    (schema : Schema) (support : List BoolVar) (parentType : Name)
    (leftParentType rightParentType : Name)
    (left right : ResponseShape)
    (hleft : RecursiveDecoderShapeInvariant schema support leftParentType left)
    (hright : RecursiveDecoderShapeInvariant schema support rightParentType right)
    (hshallow
      : DecoderShapeInvariant schema support parentType (mergeResponseShapes left right))
    : RecursiveDecoderShapeInvariant schema support parentType
        (mergeResponseShapes left right) := by
  cases hleft with
  | object _ leftPositions _ hleftChildren =>
      cases hright with
      | object _ rightPositions _ hrightChildren =>
          let mergedPositions := rightPositions.foldl
            (fun merged position => insertResponsePosition position merged)
            leftPositions
          have hrecursive : positionsRecursivelyInvariant schema support
              mergedPositions := by
            exact foldl_insertResponsePosition_recursive schema support
              leftPositions rightPositions hleftChildren hrightChildren
          apply RecursiveDecoderShapeInvariant.object parentType mergedPositions
          · simpa [mergedPositions, mergeResponseShapes] using hshallow
          · exact hrecursive

private theorem singletonDefinitionShape_recursive_leaf
    (schema : Schema) (support : List BoolVar) (parentType responseName : Name)
    (definition : ShapeDefinition)
    (hdefinition : DecoderDefinitionInvariant schema support definition)
    (hground : GroundSet.Valid schema parentType [parentType])
    (hleaf : definition.subshape = none)
    : RecursiveDecoderShapeInvariant schema support parentType
        (singletonDefinitionShape parentType responseName definition) := by
  apply RecursiveDecoderShapeInvariant.object parentType
  · exact DecoderShapeInvariant.singletonDefinition schema support parentType
      parentType responseName definition hground hdefinition
  · apply positionsRecursivelyInvariant.cons
    · apply groupsRecursivelyInvariant.cons
      · exact definitionsRecursivelyInvariant.leaf definition [] hleaf
          definitionsRecursivelyInvariant.nil
      · exact groupsRecursivelyInvariant.nil
    · exact positionsRecursivelyInvariant.nil

private theorem singletonDefinitionShape_recursive_child
    (schema : Schema) (support : List BoolVar) (parentType responseName : Name)
    (definition : ShapeDefinition) (child : ResponseShape)
    (hdefinition : DecoderDefinitionInvariant schema support definition)
    (hground : GroundSet.Valid schema parentType [parentType])
    (hchild : definition.subshape = some child)
    (hchildInvariant
      : RecursiveDecoderShapeInvariant schema support
          definition.field.outputType.namedType child)
    : RecursiveDecoderShapeInvariant schema support parentType
        (singletonDefinitionShape parentType responseName definition) := by
  apply RecursiveDecoderShapeInvariant.object parentType
  · exact DecoderShapeInvariant.singletonDefinition schema support parentType
      parentType responseName definition hground hdefinition
  · apply positionsRecursivelyInvariant.cons
    · apply groupsRecursivelyInvariant.cons
      · exact definitionsRecursivelyInvariant.child definition [] child hchild
          hchildInvariant definitionsRecursivelyInvariant.nil
      · exact groupsRecursivelyInvariant.nil
    · exact positionsRecursivelyInvariant.nil

private theorem RecursiveDecoderShapeInvariant.withShallow
    {schema : Schema} {support : List BoolVar} {oldParentType newParentType : Name}
    {shape : ResponseShape}
    (hinvariant : RecursiveDecoderShapeInvariant schema support oldParentType shape)
    (hshallow : DecoderShapeInvariant schema support newParentType shape)
    : RecursiveDecoderShapeInvariant schema support newParentType shape := by
  cases hinvariant with
  | object _ positions _ positionsInvariant =>
      exact RecursiveDecoderShapeInvariant.object newParentType positions
        hshallow positionsInvariant

private def GroundFieldRecursiveResult
    (schema : Schema) (support : List BoolVar) (clause : Clause)
    (fieldDefinition : FieldDefinition) (selectionSet : List Selection)
    : Prop :=
  (∃ shape,
    foldGroundSelectionSet schema clause fieldDefinition.outputType.namedType selectionSet
      = .ok shape
    ∧ RecursiveDecoderShapeInvariant schema support
        fieldDefinition.outputType.namedType shape)
  ∨ (NormalForm.leafTypeNameBool schema fieldDefinition.outputType.namedType = true
      ∧ selectionSet = [])

private theorem foldGroundSelectionSet_recursive_success_of_image
    (schema : Schema) (support : List BoolVar) (clause : Clause)
    (hvalid : clause.Valid support)
    (hcomplete : clause.CompleteMinterm support)
    : ∀ {parentType selectionSet},
        (himage : GroundSelectionSetImage schema parentType selectionSet)
        → ∃ shape,
            foldGroundSelectionSet schema clause parentType selectionSet = .ok shape
            ∧ RecursiveDecoderShapeInvariant schema support parentType shape := by
  intro _parentType _selectionSet himage
  induction himage using GroundSelectionSetImage.rec
      (motive_2 := fun fieldDefinition selectionSet _hchild =>
        GroundFieldRecursiveResult schema support clause
          fieldDefinition selectionSet) with
  | @objectNil parentType hobject =>
      rcases hobject with ⟨objectDefinition, hlookup⟩
      refine ⟨.object [], by
        simp [foldGroundSelectionSet, NormalForm.objectTypeNameBool, hlookup], ?_⟩
      exact RecursiveDecoderShapeInvariant.object parentType []
        (DecoderShapeInvariant.empty schema support parentType)
        positionsRecursivelyInvariant.nil
  | @objectField parentType responseName fieldName arguments fieldDefinition
      selectionSet rest hobject hlookup hresponseName hchild hrest ihchild ihrest =>
      rcases hobject with ⟨parentObject, hparentLookup⟩
      have hparentObjectBool :
          NormalForm.objectTypeNameBool schema parentType = true := by
        simp [NormalForm.objectTypeNameBool, hparentLookup]
      have hnotDuplicate : ¬ (rest.any
          (fun selection =>
            match selection with
            | .field candidate _ _ _ _ => candidate == responseName
            | .inlineFragment .. => false) = true) := by
        intro hduplicate
        have hfalse :=
          noResponseName_any_eq_false responseName rest hresponseName
        exact Bool.false_ne_true (hfalse.symm.trans hduplicate)
      rcases ihrest with ⟨restShape, hrestFold, hrestInvariant⟩
      cases hchild with
      | composite hcomposite hselection =>
          have hnotLeaf : ¬ (NormalForm.leafTypeNameBool schema
              fieldDefinition.outputType.namedType = true ∧ selectionSet = []) := by
            intro hleaf
            have hfalse :=
              isCompositeBool_eq_false_of_leafTypeNameBool schema hleaf.1
            rw [hcomposite] at hfalse
            contradiction
          rcases ihchild.resolve_right hnotLeaf with
            ⟨childShape, hchildFold, hchildInvariant⟩
          let definition : ShapeDefinition :=
            .mk clause
              { fieldName := fieldName, arguments := arguments,
                outputType := fieldDefinition.outputType }
              (some childShape)
          let currentShape :=
            singletonDefinitionShape parentType responseName definition
          have hdefinition : DecoderDefinitionInvariant schema support definition :=
            DecoderDefinitionInvariant.composite schema support clause _ _
              hvalid hcomplete hcomposite hchildInvariant.shallow
          have hcurrentInvariant : RecursiveDecoderShapeInvariant schema support
              parentType currentShape :=
            singletonDefinitionShape_recursive_child schema support parentType
              responseName definition childShape hdefinition
              (groundSetValid_objectSingleton schema parentType
                ⟨parentObject, hparentLookup⟩)
              rfl hchildInvariant
          let resultShape := mergeResponseShapes currentShape restShape
          have hresultFold : foldGroundSelectionSet schema clause parentType
              (.field responseName fieldName arguments [] selectionSet :: rest) =
              .ok resultShape := by
            unfold foldGroundSelectionSet selectionHasResponseName
            simp only [hparentObjectBool, if_true, List.isEmpty_nil,
              Bool.not_true, Bool.false_eq_true, if_false]
            split
            · rename_i hduplicate
              exact (hnotDuplicate hduplicate).elim
            · simp [Bind.bind, Except.bind, hlookup, hcomposite,
                hchildFold, hrestFold, resultShape, currentShape, definition]
          have hshallow :=
            (foldGroundSelectionSet_decoderShapeInvariant_of_image schema support
              clause parentType
              (.field responseName fieldName arguments [] selectionSet :: rest)
              resultShape hvalid hcomplete
              (GroundSelectionSetImage.objectField
                ⟨parentObject, hparentLookup⟩ hlookup hresponseName
                (GroundFieldChildImage.composite hcomposite hselection) hrest)
              hresultFold).1
          exact ⟨resultShape, hresultFold,
            mergeResponseShapes_recursive_of_shallow schema support parentType
              parentType parentType currentShape restShape hcurrentInvariant
              hrestInvariant hshallow⟩
      | leaf hleaf =>
          have hnotComposite :=
            isCompositeBool_eq_false_of_leafTypeNameBool schema hleaf
          let definition : ShapeDefinition :=
            .mk clause
              { fieldName := fieldName, arguments := arguments,
                outputType := fieldDefinition.outputType }
              none
          let currentShape :=
            singletonDefinitionShape parentType responseName definition
          have hdefinition : DecoderDefinitionInvariant schema support definition :=
            DecoderDefinitionInvariant.leaf schema support clause _ hvalid
              hcomplete hnotComposite hleaf
          have hcurrentInvariant : RecursiveDecoderShapeInvariant schema support
              parentType currentShape :=
            singletonDefinitionShape_recursive_leaf schema support parentType
              responseName definition hdefinition
              (groundSetValid_objectSingleton schema parentType
                ⟨parentObject, hparentLookup⟩)
              rfl
          let resultShape := mergeResponseShapes currentShape restShape
          have hresultFold : foldGroundSelectionSet schema clause parentType
              (.field responseName fieldName arguments [] [] :: rest) =
              .ok resultShape := by
            unfold foldGroundSelectionSet selectionHasResponseName
            simp only [hparentObjectBool, if_true, List.isEmpty_nil,
              Bool.not_true, Bool.false_eq_true, if_false]
            split
            · rename_i hduplicate
              exact (hnotDuplicate hduplicate).elim
            · simp [Bind.bind, Except.bind, hlookup, hnotComposite, hleaf,
                hrestFold, resultShape, currentShape, definition]
          have hshallow :=
            (foldGroundSelectionSet_decoderShapeInvariant_of_image schema support
              clause parentType
              (.field responseName fieldName arguments [] [] :: rest)
              resultShape hvalid hcomplete
              (GroundSelectionSetImage.objectField
                ⟨parentObject, hparentLookup⟩ hlookup hresponseName
                (GroundFieldChildImage.leaf hleaf) hrest)
              hresultFold).1
          exact ⟨resultShape, hresultFold,
            mergeResponseShapes_recursive_of_shallow schema support parentType
              parentType parentType currentShape restShape hcurrentInvariant
              hrestInvariant hshallow⟩
  | @abstractNil parentType habstract =>
      refine ⟨.object [], ?_, ?_⟩
      · rcases habstract with ⟨interfaceType, hlookup⟩ |
          ⟨unionType, hlookup⟩
        · simp [foldGroundSelectionSet, abstractTypeNameBool,
            NormalForm.objectTypeNameBool, hlookup]
        · simp [foldGroundSelectionSet, abstractTypeNameBool,
            NormalForm.objectTypeNameBool, hlookup]
      · exact RecursiveDecoderShapeInvariant.object parentType []
          (DecoderShapeInvariant.empty schema support parentType)
          positionsRecursivelyInvariant.nil
  | @abstractFragment parentType objectType selection rest habstract hobject
      hincludes hnonempty htypeCondition hselection hrest ihselection ihrest =>
      rcases hobject with ⟨objectDefinition, hobjectLookup⟩
      have hlookupObject : schema.lookupObject objectType = some objectDefinition := by
        simp [Schema.lookupObject, hobjectLookup]
      have hnotDuplicate : ¬ ∃ candidate,
          candidate ∈ rest ∧
          (match candidate with
            | .inlineFragment (some possible) _ _ => possible == objectType
            | _ => false) = true :=
        noTypeCondition_exists objectType rest htypeCondition
      rcases ihselection with
        ⟨selectionShape, hselectionFold, hselectionInvariant⟩
      rcases ihrest with ⟨restShape, hrestFold, hrestInvariant⟩
      let resultShape := mergeResponseShapes selectionShape restShape
      have hresultFold : foldGroundSelectionSet schema clause parentType
          (.inlineFragment (some objectType) [] selection :: rest) =
          .ok resultShape := by
        cases hselectionSet : selection with
        | nil => exact (hnonempty hselectionSet).elim
        | cons head tail =>
            rcases habstract with ⟨interfaceType, hparentLookup⟩ |
              ⟨unionType, hparentLookup⟩
            · unfold foldGroundSelectionSet selectionHasTypeCondition
              simp [Bind.bind, Except.bind, NormalForm.objectTypeNameBool,
                abstractTypeNameBool, hparentLookup, hlookupObject, hincludes,
                hrestFold]
              split
              · rename_i hduplicate
                exact (hnotDuplicate hduplicate).elim
              · have hselectionFold' :
                    foldGroundSelectionSet schema clause objectType
                      (head :: tail) = .ok selectionShape := by
                  simpa [hselectionSet] using hselectionFold
                simp [hselectionFold', resultShape]
            · unfold foldGroundSelectionSet selectionHasTypeCondition
              simp [Bind.bind, Except.bind, NormalForm.objectTypeNameBool,
                abstractTypeNameBool, hparentLookup, hlookupObject, hincludes,
                hrestFold]
              split
              · rename_i hduplicate
                exact (hnotDuplicate hduplicate).elim
              · have hselectionFold' :
                    foldGroundSelectionSet schema clause objectType
                      (head :: tail) = .ok selectionShape := by
                  simpa [hselectionSet] using hselectionFold
                simp [hselectionFold', resultShape]
      have hshallow :=
        (foldGroundSelectionSet_decoderShapeInvariant_of_image schema support
          clause parentType
          (.inlineFragment (some objectType) [] selection :: rest)
          resultShape hvalid hcomplete
          (GroundSelectionSetImage.abstractFragment habstract
            ⟨objectDefinition, hobjectLookup⟩ hincludes hnonempty htypeCondition
            hselection hrest)
          hresultFold).1
      exact ⟨resultShape, hresultFold,
        mergeResponseShapes_recursive_of_shallow schema support parentType
          objectType parentType selectionShape restShape hselectionInvariant
          hrestInvariant hshallow⟩
  | composite hcomposite hselection ihselection =>
      exact Or.inl ihselection
  | leaf hleaf =>
      exact Or.inr ⟨hleaf, rfl⟩

private theorem decodeRootBranches_generatedCases_recursive
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List BoolVar) (hsupport : support.Nodup)
    (hsupportNonempty : support ≠ [])
    (parentType : Name) (hparentObject : schema.objectType parentType)
    (selectionSet : List Selection)
    : ∀ (boolCases : List BoolCase) (seen : List Clause),
        boolCases.Nodup
        → (∀ boolCase, boolCase ∈ boolCases → boolCase ∈ NormalForm.allBoolCases support)
        → (∀ clause,
            clause ∈ seen
            → ∃ seenCase,
                seenCase ∈ NormalForm.allBoolCases support
                ∧ seenCase ∉ boolCases
                ∧ clause = Clause.canonical { literals := seenCase })
        → ∃ shape,
            decodeRootBranches schema support parentType seen
                (List.flatten
                  (boolCases.map (normalizedRootBranch schema parentType selectionSet)))
              = .ok shape
            ∧ positionsRecursivelyInvariant schema support shape.positions
  | [], seen, _hcasesNodup, _hcasesGenerated, _hseen => by
      exact ⟨.object [], rfl, positionsRecursivelyInvariant.nil⟩
  | boolCase :: restCases, seen, hcasesNodup, hcasesGenerated, hseen => by
      have hcaseGenerated :
          boolCase ∈ NormalForm.allBoolCases support :=
        hcasesGenerated boolCase (by simp)
      have hrestGenerated :
          ∀ candidate, candidate ∈ restCases →
            candidate ∈ NormalForm.allBoolCases support := by
        intro candidate hcandidate
        exact hcasesGenerated candidate
          (List.mem_cons_of_mem boolCase hcandidate)
      have hcaseNonempty : boolCase ≠ [] := by
        intro hnil
        have hnames :=
          NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
            hcaseGenerated
        simp [hnil] at hnames
        exact hsupportNonempty hnames
      have hcaseLength : boolCase.length = support.length :=
        boolCase_length_of_mem_allBoolCases hcaseGenerated
      have hparts := List.nodup_cons.mp hcasesNodup
      cases hbody :
          NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase boolCase selectionSet) with
      | nil =>
          simpa [normalizedRootBranch, hbody] using
            decodeRootBranches_generatedCases_recursive schema hschema support
              hsupport hsupportNonempty parentType hparentObject selectionSet
              restCases seen hparts.2 hrestGenerated
              (fun clause hclause => by
                rcases hseen clause hclause with
                  ⟨seenCase, hseenGenerated, hseenAbsent, hclauseEq⟩
                exact ⟨seenCase, hseenGenerated,
                  fun hseenRest =>
                    hseenAbsent (List.mem_cons_of_mem boolCase hseenRest),
                  hclauseEq⟩)
      | cons bodyHead bodyTail =>
          let body := bodyHead :: bodyTail
          have hbodyNonempty : body ≠ [] := by simp [body]
          rcases
              NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                boolCase body hcaseNonempty with
            ⟨wrappedSelection, hwrap⟩
          let clause : Clause := Clause.canonical { literals := boolCase }
          have hstem :
              decodeCompleteStem support.length wrappedSelection =
                .ok (boolCase, body) := by
            rw [← hcaseLength]
            exact decodeCompleteStem_wrapWithBoolCase hcaseNonempty
              hbodyNonempty hwrap
          have hclause :
              clauseFromCompleteStem support boolCase = .ok clause :=
            clauseFromCompleteStem_allBoolCases support hsupport hcaseGenerated
          have hclauseValid : clause.Valid support :=
            canonicalClause_valid_of_mem_allBoolCases support hsupport
              hcaseGenerated
          have hclauseComplete : clause.CompleteMinterm support :=
            canonicalClause_completeMinterm_of_mem_allBoolCases support hsupport
              hcaseGenerated
          have hclauseNotSeen : clause ∉ seen := by
            intro hclauseSeen
            rcases hseen clause hclauseSeen with
              ⟨seenCase, hseenGenerated, hseenAbsent, hseenClause⟩
            have hcaseEq : boolCase = seenCase :=
              canonicalClause_injective_of_mem_allBoolCases support hsupport
                hcaseGenerated hseenGenerated (by
                  change Clause.canonical { literals := boolCase } =
                    Clause.canonical { literals := seenCase }
                  exact hseenClause)
            exact hseenAbsent (by simp [hcaseEq])
          have hduplicate :
              seen.any (clausesEqualBool clause) = false :=
            clausesEqualBool_any_eq_false_of_not_mem clause seen hclauseNotSeen
          have hfilteredFree :
              NormalForm.selectionSetDirectiveFree
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet) :=
            NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
              schema boolCase selectionSet
          have himage : GroundSelectionSetImage schema parentType body := by
            simpa [body, hbody] using
              normalizeSelectionSet_groundSelectionSetImage schema hschema
                parentType
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
                hparentObject hfilteredFree
          rcases foldGroundSelectionSet_recursive_success_of_image schema support
              clause hclauseValid hclauseComplete himage with
            ⟨branchShape, hbranchShape, hbranchInvariant⟩
          have hrestSeen :
              ∀ seenClause, seenClause ∈ clause :: seen →
                ∃ seenCase,
                  seenCase ∈ NormalForm.allBoolCases support ∧
                  seenCase ∉ restCases ∧
                  seenClause = Clause.canonical { literals := seenCase } := by
            intro seenClause hseenClause
            rcases List.mem_cons.mp hseenClause with hhead | htail
            · subst seenClause
              exact ⟨boolCase, hcaseGenerated, hparts.1, rfl⟩
            · rcases hseen seenClause htail with
                ⟨seenCase, hseenGenerated, hseenAbsent, hseenClauseEq⟩
              exact ⟨seenCase, hseenGenerated,
                fun hseenRest =>
                  hseenAbsent (List.mem_cons_of_mem boolCase hseenRest),
                hseenClauseEq⟩
          rcases decodeRootBranches_generatedCases_recursive schema hschema
              support hsupport hsupportNonempty parentType hparentObject
              selectionSet restCases (clause :: seen) hparts.2 hrestGenerated
              hrestSeen with
            ⟨restShape, hrestShape, hrestInvariant⟩
          refine ⟨mergeResponseShapes branchShape restShape, ?_,
            mergeResponseShapes_positionsRecursive schema support branchShape
              restShape hbranchInvariant.positionsInvariant hrestInvariant⟩
          simp only [List.map_cons, List.flatten_cons]
          have hbranch :
              normalizedRootBranch schema parentType selectionSet boolCase =
                NormalForm.wrapWithBoolCase boolCase body := by
            simp [normalizedRootBranch, hbody, body]
          rw [hbranch]
          change decodeRootBranches schema support parentType seen
              (NormalForm.wrapWithBoolCase boolCase body ++
                List.flatten
                  (List.map
                    (normalizedRootBranch schema parentType selectionSet)
                    restCases)) =
            .ok (mergeResponseShapes branchShape restShape)
          rw [hwrap]
          simp only [List.singleton_append]
          rw [decodeRootBranches, hstem]
          simp only [Bind.bind, Except.bind]
          rw [hclause]
          simp only
          rw [hduplicate]
          simp only [Bool.false_eq_true, if_false]
          rw [hbranchShape, hrestShape]

private theorem decodeCompleteRoot_recursive_success
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List BoolVar) (hsupport : support.Nodup)
    (parentType : Name) (hparentObject : schema.objectType parentType)
    (selectionSet : List Selection)
    : ∃ shape,
        decodeCompleteRoot schema support parentType
            (NormalForm.completeNormalizeRootSelectionSet
              schema support parentType selectionSet)
          = .ok shape
        ∧ RecursiveDecoderShapeInvariant schema support parentType shape := by
  rcases decodeCompleteRoot_completeNormalizeRootSelectionSet_invariant
      schema hschema support hsupport parentType hparentObject selectionSet with
    ⟨shallowShape, hshallowDecode, hshallow⟩
  cases support with
  | nil =>
      let clause : Clause := { literals := [] }
      have hvalid : clause.Valid [] := by rfl
      have hcomplete : clause.CompleteMinterm [] := by rfl
      have hfree : NormalForm.selectionSetDirectiveFree
          (NormalForm.filterSelectionSetBoolCase [] selectionSet) :=
        NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
          schema [] selectionSet
      have himage : GroundSelectionSetImage schema parentType
          (NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase [] selectionSet)) :=
        normalizeSelectionSet_groundSelectionSetImage schema hschema parentType
          (NormalForm.filterSelectionSetBoolCase [] selectionSet)
          hparentObject hfree
      rcases foldGroundSelectionSet_recursive_success_of_image schema [] clause
          hvalid hcomplete himage with
        ⟨recursiveShape, hrecursiveFold, hrecursive⟩
      have hrecursiveDecode : decodeCompleteRoot schema [] parentType
          (NormalForm.completeNormalizeRootSelectionSet
            schema [] parentType selectionSet) = .ok recursiveShape := by
        cases hnormalized :
            NormalForm.normalizeSelectionSet schema parentType
              (NormalForm.filterSelectionSetBoolCase [] selectionSet) with
        | nil =>
            simpa [decodeCompleteRoot, firstDuplicate?,
              NormalForm.completeNormalizeRootSelectionSet,
              NormalForm.allBoolCases, NormalForm.wrapWithBoolCase,
              clause, hnormalized] using hrecursiveFold
        | cons head tail =>
            simpa [decodeCompleteRoot, firstDuplicate?,
              NormalForm.completeNormalizeRootSelectionSet,
              NormalForm.allBoolCases, NormalForm.wrapWithBoolCase,
              clause, hnormalized] using hrecursiveFold
      have heq : recursiveShape = shallowShape :=
        Except.ok.inj (hrecursiveDecode.symm.trans hshallowDecode)
      subst shallowShape
      exact ⟨recursiveShape, hrecursiveDecode,
        hrecursive.withShallow hshallow⟩
  | cons varName variables =>
      have hsupportNonempty : (varName :: variables) ≠ [] := by simp
      have hcasesNodup :
          (NormalForm.allBoolCases (varName :: variables)).Nodup :=
        NormalForm.CompleteNormalization.allBoolCases_nodup hsupport
      rcases decodeRootBranches_generatedCases_recursive schema hschema
          (varName :: variables) hsupport hsupportNonempty parentType
          hparentObject selectionSet
          (NormalForm.allBoolCases (varName :: variables)) [] hcasesNodup
          (fun boolCase hcase => hcase) (by simp) with
        ⟨recursiveShape, hrecursiveBranches, hrecursivePositions⟩
      have hduplicate : firstDuplicate? (varName :: variables) = none :=
        firstDuplicate?_eq_none_of_nodup _ hsupport
      have hrecursiveDecode : decodeCompleteRoot schema (varName :: variables)
          parentType
          (NormalForm.completeNormalizeRootSelectionSet schema
            (varName :: variables) parentType selectionSet) =
          .ok recursiveShape := by
        unfold NormalForm.completeNormalizeRootSelectionSet
        change decodeCompleteRoot schema (varName :: variables) parentType
            (List.flatten
              ((NormalForm.allBoolCases (varName :: variables)).map
                (normalizedRootBranch schema parentType selectionSet))) =
          .ok recursiveShape
        simpa [decodeCompleteRoot, hduplicate] using hrecursiveBranches
      have heq : recursiveShape = shallowShape :=
        Except.ok.inj (hrecursiveDecode.symm.trans hshallowDecode)
      subst shallowShape
      cases recursiveShape with
      | object positions =>
          exact ⟨.object positions, hrecursiveDecode,
            RecursiveDecoderShapeInvariant.object parentType positions
              hshallow hrecursivePositions⟩

private theorem computeOperationShape_recursiveInvariant
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape)
    : RecursiveDecoderShapeInvariant schema
        (NormalForm.operationBoolVars operation) shape.rootType shape.root := by
  let support := NormalForm.operationBoolVars operation
  have hsupport : support.Nodup :=
    NormalForm.CompleteNormalization.dedupBoolVars_nodup _
  have hrootEq : operation.rootType schema = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject : schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  rcases decodeCompleteRoot_recursive_success schema hschema support hsupport
      (operation.rootType schema) hrootObject operation.selectionSet with
    ⟨root, hrootDecode, hrootInvariant⟩
  rcases computeOperationShape_fields schema operation shape hcompute with
    ⟨_hoperationType, hshapeRootType, hshapeSupport, hshapeRootDecode⟩
  have hroot : root = shape.root :=
    Except.ok.inj (hrootDecode.symm.trans (by
      simpa [NormalForm.completeNormalizeOperation] using hshapeRootDecode))
  subst root
  simpa [support, hshapeSupport, hshapeRootType] using hrootInvariant

private def PathsEquivalentAt
    (schema : Schema) (assignment : BoolCase) (parentType : Name)
    (left right : ResponseShape)
    : Prop :=
  (∀ path,
    left.DenotesPath schema assignment parentType path
    → right.DenotesEquivalentPath schema assignment parentType path)
  ∧ (∀ path,
      right.DenotesPath schema assignment parentType path
      → left.DenotesEquivalentPath schema assignment parentType path)

private def ReifyCanonical (schema : Schema) (parentType : Name) (left : ResponseShape)
    : Prop :=
  ∀ (assignment : BoolCase) {rightSupport : List BoolVar} (right : ResponseShape),
    RecursiveDecoderShapeInvariant schema rightSupport parentType right
    → PathsEquivalentAt schema assignment parentType left right
    → NormalForm.SelectionSetEqualUpToReordering
        (left.reifySelectionSet schema assignment parentType)
        (right.reifySelectionSet schema assignment parentType)

private theorem pathsSemanticallyEquivalent_length_eq
    : ∀ {left right : List PathStep},
        PathsSemanticallyEquivalent left right → left.length = right.length
  | [], [], _h => rfl
  | left :: leftRest, right :: rightRest, h => by
      simpa using congrArg Nat.succ
        (pathsSemanticallyEquivalent_length_eq h.2)

private theorem matchingActiveDefinition_of_coverage
    {schema : Schema} {assignment : BoolCase} {parentType runtimeObject : Name}
    {left right : ResponseShape} {responseName : Name}
    {leftDefinition : ShapeDefinition}
    (hleftActive
      : ActiveDefinitionWitness schema assignment parentType
          runtimeObject left responseName leftDefinition)
    (hcoverage
      : ∀ path,
          left.DenotesPath schema assignment parentType path
          → right.DenotesEquivalentPath schema assignment parentType path)
    : ∃ rightDefinition,
      ∃ _rightActive
          : ActiveDefinitionWitness schema assignment parentType
              runtimeObject right responseName rightDefinition,
        PathStep.SemanticallyEquivalent
          {
            parentObject := runtimeObject
            responseName := responseName
            field := rightDefinition.field
          }
          {
            parentObject := runtimeObject
            responseName := responseName
            field := leftDefinition.field
          } := by
  let leftStep : PathStep :=
    { parentObject := runtimeObject
      responseName := responseName
      field := leftDefinition.field }
  rcases hcoverage [leftStep]
      (by simpa [leftStep] using hleftActive.denotesSingleton) with
    ⟨rightPath, hrightDenotes, hpaths⟩
  cases hrightDenotes with
  | @field _ _ position possible definition rightRuntime runtimePossible
      positionMem possibleMem runtimeMem definitionMem clauseHolds =>
      change PathsSemanticallyEquivalent [_] [leftStep] at hpaths
      have hparent : rightRuntime = runtimeObject := by
        simpa [leftStep] using hpaths.1.1
      have hresponse : position.responseName = responseName := by
        simpa [leftStep] using hpaths.1.2.1
      subst rightRuntime
      refine ⟨_,
        ⟨position, positionMem, hresponse, possible, possibleMem, runtimeMem,
          runtimePossible, definitionMem, clauseHolds⟩,
        ?_⟩
      simpa [leftStep, hresponse] using hpaths.1
  | @child _ _ position possible definition rightRuntime child childPath
      runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds subshapeEq childDenotes =>
      change PathsSemanticallyEquivalent (_ :: _) [leftStep] at hpaths
      have hlength := pathsSemanticallyEquivalent_length_eq hpaths
      have hchildNonempty := childDenotes.nonempty
      cases childPath with
      | nil => exact False.elim (hchildNonempty rfl)
      | cons childStep childRest => simp at hlength

private theorem activeChild_coverage
    {schema : Schema} {assignment : BoolCase} {parentType runtimeObject : Name}
    {left right leftChild rightChild : ResponseShape} {responseName : Name}
    {leftDefinition rightDefinition : ShapeDefinition}
    (hleftInvariant : DecoderShapeInvariant schema leftSupport parentType left)
    (hrightInvariant : DecoderShapeInvariant schema rightSupport parentType right)
    (hleftActive
      : ActiveDefinitionWitness schema assignment parentType
          runtimeObject left responseName leftDefinition)
    (hrightActive
      : ActiveDefinitionWitness schema assignment parentType
          runtimeObject right responseName rightDefinition)
    (hleftChild : leftDefinition.subshape = some leftChild)
    (hrightChild : rightDefinition.subshape = some rightChild)
    (hcoverage
      : ∀ path,
          left.DenotesPath schema assignment parentType path
          → right.DenotesEquivalentPath schema assignment parentType path)
    : ∀ childPath,
        leftChild.DenotesPath schema assignment
          leftDefinition.field.outputType.namedType childPath
        → rightChild.DenotesEquivalentPath schema assignment
            rightDefinition.field.outputType.namedType childPath := by
  intro childPath hchildDenotes
  let leftStep : PathStep :=
    { parentObject := runtimeObject
      responseName := responseName
      field := leftDefinition.field }
  have hleftWhole : left.DenotesPath schema assignment parentType
      (leftStep :: childPath) := by
    rcases hleftActive with
      ⟨position, hposition, hresponse, possible, hpossible, hruntime,
        hincludes, hdefinition, hholds⟩
    cases left with
    | object positions =>
        change position ∈ positions at hposition
        simpa [leftStep, hresponse] using
          (ResponseShape.DenotesPath.child hincludes hposition hpossible
            hruntime hdefinition hholds hleftChild hchildDenotes)
  rcases hcoverage (leftStep :: childPath) hleftWhole with
    ⟨rightPath, hrightWhole, hequivalent⟩
  cases hrightWhole with
  | field runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds =>
      change PathsSemanticallyEquivalent [_] (leftStep :: childPath) at hequivalent
      have hchildNonempty := hchildDenotes.nonempty
      cases childPath with
      | nil => exact False.elim (hchildNonempty rfl)
      | cons childStep childRest =>
          exact False.elim hequivalent.2
  | @child _ _ position possible definition rightRuntime denotedChild
      denotedChildPath runtimePossible positionMem possibleMem runtimeMem
      definitionMem clauseHolds subshapeEq childDenotes =>
      change PathsSemanticallyEquivalent
        (_ :: denotedChildPath) (leftStep :: childPath) at hequivalent
      have hparent : rightRuntime = runtimeObject := by
        simpa [leftStep] using hequivalent.1.1
      have hresponse : position.responseName = responseName := by
        simpa [leftStep] using hequivalent.1.2.1
      subst rightRuntime
      let hchosen : ActiveDefinitionWitness schema assignment parentType
          runtimeObject (.object _) responseName definition :=
        ⟨position, positionMem, hresponse, possible, possibleMem, runtimeMem,
          runtimePossible, definitionMem, clauseHolds⟩
      have hdefinitionEq : definition = rightDefinition :=
        ActiveDefinitionWitness.unique hrightInvariant hchosen hrightActive
      subst definition
      rw [hrightChild] at subshapeEq
      cases subshapeEq
      refine ⟨denotedChildPath, ?_, hequivalent.2⟩
      simpa using childDenotes

private theorem objectType_of_objectTypeNameBool_true
    (schema : Schema) {typeName : Name}
    (hobject : NormalForm.objectTypeNameBool schema typeName = true)
    : schema.objectType typeName := by
  unfold NormalForm.objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none => simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType => exact ⟨objectType, hlookup⟩
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

private theorem reifyField_responseName?
    (schema : Schema) (assignment : BoolCase) (responseName : Name)
    (definition : ShapeDefinition)
    : (definition.reifyField schema assignment responseName).responseName?
      = some responseName := by
  cases definition
  case mk clause field subshape =>
    cases subshape <;> rfl

private theorem reifyField_eq
    (schema : Schema) (assignment : BoolCase) (responseName : Name)
    (definition : ShapeDefinition)
    : definition.reifyField schema assignment responseName
      = .field responseName definition.field.fieldName definition.field.arguments []
          (match definition.subshape with
            | none => []
            | some child =>
                child.reifySelectionSet schema assignment
                  definition.field.outputType.namedType) := by
  cases definition
  case mk clause field subshape =>
    cases subshape <;> rfl

private theorem reifyResponsePositions_equal_of_paths
    (schema : Schema) (leftSupport rightSupport : List BoolVar)
    (assignment : BoolCase)
    (parentType runtimeObject : Name) (left right : ResponseShape)
    (hleftInvariant : RecursiveDecoderShapeInvariant schema leftSupport parentType left)
    (hrightInvariant
      : RecursiveDecoderShapeInvariant schema rightSupport parentType right)
    (hleftChildren
      : ∀ position ∈ left.positions,
        ∀ possible ∈ position.possibleDefinitions,
        ∀ definition ∈ possible.definitions,
          ∀ child,
            definition.subshape = some child
            → ReifyCanonical schema definition.field.outputType.namedType child)
    (hincludes : schema.typeIncludesObject parentType runtimeObject)
    (hequivalent : PathsEquivalentAt schema assignment parentType left right)
    : NormalForm.SelectionSetEqualUpToReordering
        (reifyResponsePositions schema assignment runtimeObject left.positions)
        (reifyResponsePositions schema assignment runtimeObject right.positions) := by
  apply
    NormalForm.GroundTypeNormalization.selectionSetEqualUpToReordering_of_field_responseName_matches
  · intro selection hselection
    rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject
        selection left.positions).1 hselection with
      ⟨position, hposition, possible, hpossible, _hruntime, definition,
        hdefinition, _hholds, heq⟩
    subst selection
    cases definition
    simp [ShapeDefinition.reifyField, Selection.isField]
  · intro selection hselection
    rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject
        selection right.positions).1 hselection with
      ⟨position, hposition, possible, hpossible, _hruntime, definition,
        hdefinition, _hholds, heq⟩
    subst selection
    cases definition
    simp [ShapeDefinition.reifyField, Selection.isField]
  · unfold NormalForm.responseNamesNodup
    apply filterMap_nodup_of_injective_on Selection.responseName?
    · exact reifyResponsePositions_nodup schema leftSupport assignment parentType
        runtimeObject left.positions (by
          cases left
          exact hleftInvariant.shallow)
    · intro leftSelection hleft rightSelection hright heq
      exact reifiedSelection_eq_of_responseName schema leftSupport assignment
        parentType runtimeObject left hleftInvariant.shallow hincludes hleft hright heq
  · unfold NormalForm.responseNamesNodup
    apply filterMap_nodup_of_injective_on Selection.responseName?
    · exact reifyResponsePositions_nodup schema rightSupport assignment parentType
        runtimeObject right.positions (by
          cases right
          exact hrightInvariant.shallow)
    · intro leftSelection hleft rightSelection hright heq
      exact reifiedSelection_eq_of_responseName schema rightSupport assignment
        parentType runtimeObject right hrightInvariant.shallow hincludes hleft hright heq
  · intro responseName fieldName arguments directives childSelectionSet
      hleftSelection
    rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject
        (.field responseName fieldName arguments directives childSelectionSet)
        left.positions).1 hleftSelection with
      ⟨leftPosition, hleftPosition, leftPossible, hleftPossible, hleftRuntime,
        leftDefinition, hleftDefinition, hleftHolds, hleftEq⟩
    have hleftExplicit := hleftEq.trans
      (reifyField_eq schema assignment leftPosition.responseName leftDefinition)
    simp only [Selection.field.injEq] at hleftExplicit
    rcases hleftExplicit with
      ⟨hresponseEq, hfieldEq, hargumentsEq, hdirectivesEq, hchildEq⟩
    have hleftResponse : leftPosition.responseName = responseName := by
      exact hresponseEq.symm
    subst fieldName
    subst arguments
    subst directives
    subst childSelectionSet
    let hleftActive : ActiveDefinitionWitness schema assignment parentType
        runtimeObject left responseName leftDefinition :=
      ⟨leftPosition, hleftPosition, hleftResponse, leftPossible, hleftPossible,
        hleftRuntime, hincludes,
        hleftDefinition, hleftHolds⟩
    rcases matchingActiveDefinition_of_coverage hleftActive hequivalent.1 with
      ⟨rightDefinition, hrightActive, hstep⟩
    let rightSelection := rightDefinition.reifyField schema assignment responseName
    have hrightSelection : rightSelection ∈
        reifyResponsePositions schema assignment runtimeObject right.positions := by
      apply (mem_reifyResponsePositions_iff schema assignment runtimeObject
        rightSelection right.positions).2
      exact ⟨hrightActive.position, hrightActive.positionMem,
        hrightActive.possible, hrightActive.possibleMem,
        hrightActive.runtimeMem, rightDefinition,
        hrightActive.definitionMem, hrightActive.clauseHolds, by
          unfold rightSelection
          rw [hrightActive.responseName_eq]⟩
    refine ⟨rightDefinition.field.fieldName, rightDefinition.field.arguments, [],
      (match rightDefinition.subshape with
        | none => []
        | some child => child.reifySelectionSet schema assignment
            rightDefinition.field.outputType.namedType), ?_, ?_⟩
    · rw [← reifyField_eq]
      change rightSelection ∈
        reifyResponsePositions schema assignment runtimeObject right.positions
      exact hrightSelection
    · cases leftDefinition with
      | mk leftClause leftField leftSubshape =>
          cases rightDefinition with
          | mk rightClause rightField rightSubshape =>
              simp only [ShapeDefinition.field] at hstep
              have hfieldName : leftField.fieldName = rightField.fieldName :=
                hstep.2.2.1.symm
              have harguments : Argument.argumentsEquivalent
                  leftField.arguments rightField.arguments :=
                FieldMerge.argumentsEquivalent_symm hstep.2.2.2.1
              have houtput : rightField.outputType = leftField.outputType :=
                hstep.2.2.2.2
              simp only [ShapeDefinition.field, ShapeDefinition.subshape]
              rw [hfieldName]
              apply NormalForm.SelectionEqualUpToReordering.field responseName
                rightField.fieldName []
              · exact harguments
              · cases leftSubshape with
                | none =>
                    cases rightSubshape with
                    | none =>
                        exact
                          NormalForm.GroundTypeNormalization.selectionSetEqualUpToReordering_refl
                            []
                    | some rightChild =>
                        have hleftDefinitionInvariant :=
                          hleftActive.invariant hleftInvariant.shallow
                        have hrightDefinitionInvariant :=
                          hrightActive.invariant hrightInvariant.shallow
                        simp [DecoderDefinitionInvariant,
                          ShapeDefinition.wellFormedBool, houtput] at hleftDefinitionInvariant hrightDefinitionInvariant
                        exact False.elim (Bool.false_ne_true
                          (hleftDefinitionInvariant.1.2.1.symm.trans
                            hrightDefinitionInvariant.1.2.1))
                | some leftChild =>
                    cases rightSubshape with
                    | none =>
                        have hleftDefinitionInvariant :=
                          hleftActive.invariant hleftInvariant.shallow
                        have hrightDefinitionInvariant :=
                          hrightActive.invariant hrightInvariant.shallow
                        simp [DecoderDefinitionInvariant,
                          ShapeDefinition.wellFormedBool, houtput] at hleftDefinitionInvariant hrightDefinitionInvariant
                        exact False.elim (Bool.false_ne_true
                          (hrightDefinitionInvariant.1.2.1.symm.trans
                            hleftDefinitionInvariant.1.2.1))
                    | some rightChild =>
                        have hleftChildCanonical :=
                          hleftChildren hleftActive.position
                            hleftActive.positionMem hleftActive.possible
                            hleftActive.possibleMem (.mk leftClause leftField
                              (some leftChild)) hleftActive.definitionMem
                            leftChild rfl
                        have hrightChildInvariant :=
                          hrightInvariant.child hrightActive.positionMem
                            hrightActive.possibleMem hrightActive.definitionMem
                            (child := rightChild) rfl
                        have hchildrenEquivalent : PathsEquivalentAt schema assignment
                            leftField.outputType.namedType leftChild rightChild := by
                          constructor
                          · have hforward :=
                              activeChild_coverage hleftInvariant.shallow
                                hrightInvariant.shallow hleftActive hrightActive
                                rfl rfl hequivalent.1
                            simp only [ShapeDefinition.field] at hforward
                            simpa [houtput] using hforward
                          · intro path hpath
                            have hreverse :=
                              activeChild_coverage hrightInvariant.shallow
                                hleftInvariant.shallow hrightActive hleftActive rfl rfl
                                hequivalent.2
                            simp only [ShapeDefinition.field] at hreverse
                            have hresult := hreverse path (by
                              simpa [houtput] using hpath)
                            simpa [houtput] using hresult
                        change NormalForm.SelectionSetEqualUpToReordering
                          (leftChild.reifySelectionSet schema assignment
                            leftField.outputType.namedType)
                          (rightChild.reifySelectionSet schema assignment
                            rightField.outputType.namedType)
                        simp only [ShapeDefinition.field] at hleftChildCanonical
                        have hchildRelation := hleftChildCanonical assignment rightChild
                          (by
                            simp only [ShapeDefinition.field] at hrightChildInvariant
                            simpa [houtput] using hrightChildInvariant)
                          hchildrenEquivalent
                        simpa [houtput] using hchildRelation
  · intro responseName hrightName
    rw [List.mem_filterMap] at hrightName ⊢
    rcases hrightName with ⟨rightSelection, hrightSelection, hrightName⟩
    rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject
        rightSelection right.positions).1 hrightSelection with
      ⟨rightPosition, hrightPosition, rightPossible, hrightPossible,
        hrightRuntime, rightDefinition, hrightDefinition, hrightHolds,
        hrightEq⟩
    have hresponse : rightPosition.responseName = responseName := by
      have hname := congrArg Selection.responseName? hrightEq
      rw [reifyField_responseName?] at hname
      rw [hrightName] at hname
      exact Option.some.inj hname.symm
    let hrightActive : ActiveDefinitionWitness schema assignment parentType
        runtimeObject right responseName rightDefinition :=
      ⟨rightPosition, hrightPosition, hresponse, rightPossible, hrightPossible,
        hrightRuntime, hincludes, hrightDefinition, hrightHolds⟩
    rcases matchingActiveDefinition_of_coverage hrightActive hequivalent.2 with
      ⟨leftDefinition, hleftActive, _hstep⟩
    let leftSelection := leftDefinition.reifyField schema assignment responseName
    refine ⟨leftSelection, ?_, ?_⟩
    · apply (mem_reifyResponsePositions_iff schema assignment runtimeObject
        leftSelection left.positions).2
      exact ⟨hleftActive.position, hleftActive.positionMem,
        hleftActive.possible, hleftActive.possibleMem, hleftActive.runtimeMem,
        leftDefinition, hleftActive.definitionMem, hleftActive.clauseHolds, by
          unfold leftSelection
          rw [hleftActive.responseName_eq]⟩
    · cases leftDefinition
      simp [leftSelection, ShapeDefinition.reifyField, Selection.responseName?]

private theorem reifyResponsePositions_nonempty_of_coverage
    (schema : Schema) (assignment : BoolCase) (parentType runtimeObject : Name)
    (left right : ResponseShape)
    (hincludes : schema.typeIncludesObject parentType runtimeObject)
    (hcoverage
      : ∀ path,
          left.DenotesPath schema assignment parentType path
          → right.DenotesEquivalentPath schema assignment parentType path)
    (hleftNonempty
      : reifyResponsePositions schema assignment runtimeObject left.positions ≠ [])
    : reifyResponsePositions schema assignment runtimeObject right.positions ≠ [] := by
  intro hrightEmpty
  rcases List.exists_mem_of_ne_nil _ hleftNonempty with
    ⟨leftSelection, hleftSelection⟩
  rcases (mem_reifyResponsePositions_iff schema assignment runtimeObject
      leftSelection left.positions).1 hleftSelection with
    ⟨leftPosition, hleftPosition, leftPossible, hleftPossible, hleftRuntime,
      leftDefinition, hleftDefinition, hleftHolds, hleftEq⟩
  let hleftActive : ActiveDefinitionWitness schema assignment parentType
      runtimeObject left leftPosition.responseName leftDefinition :=
    ⟨leftPosition, hleftPosition, rfl, leftPossible, hleftPossible,
      hleftRuntime, hincludes, hleftDefinition, hleftHolds⟩
  rcases matchingActiveDefinition_of_coverage hleftActive hcoverage with
    ⟨rightDefinition, hrightActive, _hstep⟩
  let rightSelection := rightDefinition.reifyField schema assignment
    leftPosition.responseName
  have hrightSelection : rightSelection ∈
      reifyResponsePositions schema assignment runtimeObject right.positions := by
    apply (mem_reifyResponsePositions_iff schema assignment runtimeObject
      rightSelection right.positions).2
    exact ⟨hrightActive.position, hrightActive.positionMem,
      hrightActive.possible, hrightActive.possibleMem, hrightActive.runtimeMem,
      rightDefinition, hrightActive.definitionMem, hrightActive.clauseHolds, by
        unfold rightSelection
        rw [hrightActive.responseName_eq]⟩
  rw [hrightEmpty] at hrightSelection
  simp at hrightSelection

private theorem reifyAbstractCandidates_equal_of_paths
    (schema : Schema) (leftSupport rightSupport : List BoolVar)
    (assignment : BoolCase)
    (parentType : Name) (left right : ResponseShape)
    (hleftInvariant : RecursiveDecoderShapeInvariant schema leftSupport parentType left)
    (hrightInvariant
      : RecursiveDecoderShapeInvariant schema rightSupport parentType right)
    (hleftChildren
      : ∀ position ∈ left.positions,
        ∀ possible ∈ position.possibleDefinitions,
        ∀ definition ∈ possible.definitions,
          ∀ child,
            definition.subshape = some child
            → ReifyCanonical schema definition.field.outputType.namedType child)
    (hequivalent : PathsEquivalentAt schema assignment parentType left right)
    : ∀ candidates : List Name,
        (∀ objectType,
          objectType ∈ candidates → schema.typeIncludesObject parentType objectType)
        → NormalForm.SelectionSetEqualUpToReordering
            (candidates.filterMap
              (fun objectType =>
                match reifyResponsePositions schema assignment objectType
                        left.positions with
                | [] => none
                | selections =>
                    some (.inlineFragment (some objectType) [] selections)))
            (candidates.filterMap
              (fun objectType =>
                match reifyResponsePositions schema assignment objectType
                        right.positions with
                | [] => none
                | selections =>
                    some (.inlineFragment (some objectType) [] selections)))
  | [], _hincludes =>
      NormalForm.GroundTypeNormalization.selectionSetEqualUpToReordering_refl []
  | objectType :: rest, hincludes => by
      have hobjectIncludes := hincludes objectType (by simp)
      have hrestIncludes : ∀ candidate, candidate ∈ rest →
          schema.typeIncludesObject parentType candidate := by
        intro candidate hcandidate
        exact hincludes candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestRelation := reifyAbstractCandidates_equal_of_paths schema
        leftSupport rightSupport assignment parentType left right hleftInvariant
        hrightInvariant
        hleftChildren hequivalent rest hrestIncludes
      cases hleftFields :
          reifyResponsePositions schema assignment objectType left.positions with
      | nil =>
          cases hrightFields :
              reifyResponsePositions schema assignment objectType right.positions with
          | nil =>
              simpa [hleftFields, hrightFields] using hrestRelation
          | cons rightHead rightTail =>
              have hrightNonempty : reifyResponsePositions schema assignment
                  objectType right.positions ≠ [] := by simp [hrightFields]
              have := reifyResponsePositions_nonempty_of_coverage schema assignment
                parentType objectType right left hobjectIncludes hequivalent.2
                hrightNonempty
              exact False.elim (this hleftFields)
      | cons leftHead leftTail =>
          have hleftNonempty : reifyResponsePositions schema assignment objectType
              left.positions ≠ [] := by simp [hleftFields]
          cases hrightFields :
              reifyResponsePositions schema assignment objectType right.positions with
          | nil =>
              have := reifyResponsePositions_nonempty_of_coverage schema assignment
                parentType objectType left right hobjectIncludes hequivalent.1
                hleftNonempty
              exact False.elim (this hrightFields)
          | cons rightHead rightTail =>
              have hfieldRelation := reifyResponsePositions_equal_of_paths schema
                leftSupport rightSupport assignment parentType objectType left right
                hleftInvariant hrightInvariant hleftChildren hobjectIncludes
                hequivalent
              rcases hrestRelation with
                ⟨pairs, hpairsLeft, hpairsRight, hpairsRelation⟩
              apply NormalForm.SelectionSetEqualUpToReordering.paired
                ((.inlineFragment (some objectType) [] (leftHead :: leftTail),
                  .inlineFragment (some objectType) [] (rightHead :: rightTail)) ::
                  pairs)
              · simp only [List.map_cons]
                simpa [hleftFields] using
                  List.Perm.cons
                    (.inlineFragment (some objectType) [] (leftHead :: leftTail))
                    hpairsLeft
              · simp only [List.map_cons]
                simpa [hrightFields] using
                  List.Perm.cons
                    (.inlineFragment (some objectType) [] (rightHead :: rightTail))
                    hpairsRight
              · intro pair hpair
                rcases List.mem_cons.mp hpair with hhead | htail
                · subst pair
                  apply NormalForm.SelectionEqualUpToReordering.inlineFragment
                    (some objectType) []
                  simpa [hleftFields, hrightFields] using hfieldRelation
                · exact hpairsRelation pair htail

private theorem RecursiveDecoderShapeInvariant.reifyCanonical
    {schema : Schema} {support : List BoolVar} {parentType : Name}
    {shape : ResponseShape}
    (hinvariant : RecursiveDecoderShapeInvariant schema support parentType shape)
    : ReifyCanonical schema parentType shape := by
  refine RecursiveDecoderShapeInvariant.rec
    (motive_1 := fun parentType shape _hinvariant =>
      ReifyCanonical schema parentType shape)
    (motive_2 := fun positions _hinvariant =>
      ∀ position ∈ positions,
        ∀ possible ∈ position.possibleDefinitions,
          ∀ definition ∈ possible.definitions,
            ∀ child, definition.subshape = some child →
              ReifyCanonical schema
                definition.field.outputType.namedType child)
    (motive_3 := fun groups _hinvariant =>
      ∀ possible ∈ groups,
        ∀ definition ∈ possible.definitions,
          ∀ child, definition.subshape = some child →
            ReifyCanonical schema
              definition.field.outputType.namedType child)
    (motive_4 := fun definitions _hinvariant =>
      ∀ definition ∈ definitions,
        ∀ child, definition.subshape = some child →
          ReifyCanonical schema
            definition.field.outputType.namedType child)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hinvariant
  · intro currentParent positions shallow positionsInvariant childrenCanonical
      assignment rightSupport right hrightInvariant hequivalent
    cases right with
    | object rightPositions =>
        by_cases hobject :
            NormalForm.objectTypeNameBool schema currentParent = true
        · have hobjectType :=
            objectType_of_objectTypeNameBool_true schema hobject
          have hincludes : schema.typeIncludesObject currentParent currentParent :=
            List.contains_iff_mem.mp
              (NormalForm.object_typeIncludesObjectBool_self schema hobjectType)
          unfold ResponseShape.reifySelectionSet
          simp only [hobject, if_true]
          exact reifyResponsePositions_equal_of_paths schema support rightSupport
            assignment currentParent currentParent (.object positions)
            (.object rightPositions)
            (RecursiveDecoderShapeInvariant.object currentParent positions
              shallow positionsInvariant)
            hrightInvariant childrenCanonical hincludes hequivalent
        · have hobjectFalse :
              NormalForm.objectTypeNameBool schema currentParent = false := by
            cases hmatch :
                NormalForm.objectTypeNameBool schema currentParent with
            | false => rfl
            | true => contradiction
          unfold ResponseShape.reifySelectionSet
          simp only [hobjectFalse, Bool.false_eq_true, if_false]
          exact reifyAbstractCandidates_equal_of_paths schema support rightSupport
            assignment currentParent (.object positions) (.object rightPositions)
            (RecursiveDecoderShapeInvariant.object currentParent positions
              shallow positionsInvariant)
            hrightInvariant childrenCanonical hequivalent
            (schema.getPossibleTypes currentParent) (fun objectType hmem => hmem)
  · intro position hposition
    simp at hposition
  · intro position rest head tail headCanonical tailCanonical
      candidate hcandidate
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      exact headCanonical
    · exact tailCanonical candidate htail
  · intro possible hpossible
    simp at hpossible
  · intro possible rest head tail headCanonical tailCanonical
      candidate hcandidate
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      exact headCanonical
    · exact tailCanonical candidate htail
  · intro definition hdefinition
    simp at hdefinition
  · intro definition rest hleaf tail tailCanonical candidate hcandidate
      child hchild
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      rw [hleaf] at hchild
      contradiction
    · exact tailCanonical candidate htail child hchild
  · intro definition rest childShape hstored childInvariant tail
      childCanonical tailCanonical candidate hcandidate child hchild
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      rw [hstored] at hchild
      cases hchild
      exact childCanonical
    · exact tailCanonical candidate htail child hchild

private theorem BoolCase.mem_of_lookup?_eq
    {boolCase : BoolCase} {varName : BoolVar} {value : Bool}
    (hlookup : boolCase.lookup? varName = some value)
    : (varName, value) ∈ boolCase := by
  induction boolCase with
  | nil => simp [BoolCase.lookup?] at hlookup
  | cons head rest ih =>
      rcases head with ⟨headVar, headValue⟩
      by_cases heq : headVar = varName
      · subst headVar
        simp [BoolCase.lookup?] at hlookup
        subst headValue
        simp
      · simp [BoolCase.lookup?, heq] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

private theorem BoolCase.lookup?_eq_of_equivalent
    {left right : BoolCase}
    (hleftNodup : (left.map Prod.fst).Nodup)
    (hrightNodup : (right.map Prod.fst).Nodup)
    (hequivalent : NormalForm.completeNormalBoolCasesEquivalent left right)
    : ∀ varName, left.lookup? varName = right.lookup? varName := by
  intro varName
  cases hleftLookup : left.lookup? varName with
  | none =>
      cases hrightLookup : right.lookup? varName with
      | none => rfl
      | some value =>
          have hrightMem := BoolCase.mem_of_lookup?_eq hrightLookup
          have hleftMem := (hequivalent varName value).2 hrightMem
          have := BoolCase.lookup?_eq_of_pair_mem_nodup hleftNodup hleftMem
          rw [hleftLookup] at this
          contradiction
  | some value =>
      have hleftMem := BoolCase.mem_of_lookup?_eq hleftLookup
      have hrightMem := (hequivalent varName value).1 hleftMem
      exact (BoolCase.lookup?_eq_of_pair_mem_nodup
        hrightNodup hrightMem).symm

private theorem Clause.holdsInBool_eq_of_equivalent_cases
    (clause : Clause) {left right : BoolCase}
    (hleftNodup : (left.map Prod.fst).Nodup)
    (hrightNodup : (right.map Prod.fst).Nodup)
    (hequivalent : NormalForm.completeNormalBoolCasesEquivalent left right)
    : clause.holdsInBool left = clause.holdsInBool right := by
  unfold Clause.holdsInBool
  apply congrArg (List.all clause.literals)
  funext literal
  rw [BoolCase.lookup?_eq_of_equivalent hleftNodup hrightNodup
    hequivalent literal.1]

private theorem RecursiveDecoderShapeInvariant.reify_eq_of_equivalent_cases
    {schema : Schema} {support : List BoolVar} {parentType : Name}
    {shape : ResponseShape}
    (hinvariant : RecursiveDecoderShapeInvariant schema support parentType shape)
    (left right : BoolCase)
    (hleftNodup : (left.map Prod.fst).Nodup)
    (hrightNodup : (right.map Prod.fst).Nodup)
    (hequivalent : NormalForm.completeNormalBoolCasesEquivalent left right)
    : shape.reifySelectionSet schema left parentType
      = shape.reifySelectionSet schema right parentType := by
  refine RecursiveDecoderShapeInvariant.rec
    (motive_1 := fun parentType shape _hinvariant =>
      shape.reifySelectionSet schema left parentType =
        shape.reifySelectionSet schema right parentType)
    (motive_2 := fun positions _hinvariant =>
      ∀ runtimeObject,
        reifyResponsePositions schema left runtimeObject positions =
          reifyResponsePositions schema right runtimeObject positions)
    (motive_3 := fun groups _hinvariant =>
      ∀ runtimeObject responseName,
        reifyPossibleDefinitions schema left runtimeObject responseName groups =
          reifyPossibleDefinitions schema right runtimeObject responseName groups)
    (motive_4 := fun definitions _hinvariant =>
      ∀ responseName,
        reifyShapeDefinitions schema left responseName definitions =
          reifyShapeDefinitions schema right responseName definitions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hinvariant
  · intro currentParent positions shallow positionsInvariant positionsEq
    unfold ResponseShape.reifySelectionSet
    split
    · exact positionsEq currentParent
    · apply congrArg
        (fun f => List.filterMap f (schema.getPossibleTypes currentParent))
      funext runtimeObject
      rw [positionsEq runtimeObject]
  · intro runtimeObject
    rfl
  · intro position rest head tail headEq tailEq runtimeObject
    cases position with
    | mk responseName possibleDefinitions =>
        simp only [reifyResponsePositions, ResponsePosition.reifyFields]
        have hheadEq := headEq runtimeObject responseName
        simp only [ResponsePosition.possibleDefinitions] at hheadEq
        rw [hheadEq, tailEq runtimeObject]
  · intro runtimeObject responseName
    rfl
  · intro possible rest head tail headEq tailEq runtimeObject responseName
    cases possible with
    | mk objectTypes definitions =>
        simp only [reifyPossibleDefinitions, PossibleDefinitions.reifyFields]
        split
        · have hheadEq := headEq responseName
          simp only [PossibleDefinitions.definitions] at hheadEq
          rw [hheadEq, tailEq runtimeObject responseName]
        · exact tailEq runtimeObject responseName
  · intro responseName
    rfl
  · intro definition rest hleaf tail tailEq responseName
    cases definition with
    | mk clause field subshape =>
        simp only [ShapeDefinition.subshape] at hleaf
        subst subshape
        have hholds := Clause.holdsInBool_eq_of_equivalent_cases clause
          hleftNodup hrightNodup hequivalent
        cases hleftActive : clause.holdsInBool left with
        | false =>
            have hrightActive : clause.holdsInBool right = false :=
              hholds.symm.trans hleftActive
            simp only [reifyShapeDefinitions, ShapeDefinition.clause,
              hleftActive, Bool.false_eq_true, if_false, hrightActive]
            exact tailEq responseName
        | true =>
            have hrightActive : clause.holdsInBool right = true :=
              hholds.symm.trans hleftActive
            simp only [reifyShapeDefinitions, ShapeDefinition.clause,
              hleftActive, if_true, hrightActive, ShapeDefinition.reifyField]
            rw [tailEq responseName]
  · intro definition rest child hchild childInvariant tail childEq tailEq
      responseName
    cases definition with
    | mk clause field subshape =>
        simp only [ShapeDefinition.subshape] at hchild
        subst subshape
        simp only [ShapeDefinition.field] at childEq
        have hholds := Clause.holdsInBool_eq_of_equivalent_cases clause
          hleftNodup hrightNodup hequivalent
        cases hleftActive : clause.holdsInBool left with
        | false =>
            have hrightActive : clause.holdsInBool right = false :=
              hholds.symm.trans hleftActive
            simp only [reifyShapeDefinitions, ShapeDefinition.clause,
              hleftActive, Bool.false_eq_true, if_false, hrightActive]
            exact tailEq responseName
        | true =>
            have hrightActive : clause.holdsInBool right = true :=
              hholds.symm.trans hleftActive
            simp only [reifyShapeDefinitions, ShapeDefinition.clause,
              hleftActive, if_true, hrightActive, ShapeDefinition.reifyField]
            rw [childEq, tailEq responseName]

private theorem selectionSetDirectiveFree_filterMap
    {alpha : Type} (items : List alpha) (f : alpha → Option Selection)
    (hfree
      : ∀ item selection,
          f item = some selection → NormalForm.selectionDirectiveFree selection)
    : NormalForm.selectionSetDirectiveFree (items.filterMap f) := by
  induction items with
  | nil => trivial
  | cons item rest ih =>
      cases hitem : f item with
      | none => simpa only [List.filterMap_cons, hitem] using ih
      | some selection =>
          simp only [List.filterMap_cons, hitem,
            NormalForm.selectionSetDirectiveFree]
          exact ⟨hfree item selection hitem, ih⟩

private theorem RecursiveDecoderShapeInvariant.reifyDirectiveFree
    {schema : Schema} {support : List BoolVar} {parentType : Name}
    {shape : ResponseShape}
    (hinvariant : RecursiveDecoderShapeInvariant schema support parentType shape)
    : ∀ assignment,
        NormalForm.selectionSetDirectiveFree
          (shape.reifySelectionSet schema assignment parentType) := by
  refine RecursiveDecoderShapeInvariant.rec
    (motive_1 := fun currentParent currentShape _hinvariant =>
      ∀ assignment, NormalForm.selectionSetDirectiveFree
        (currentShape.reifySelectionSet schema assignment currentParent))
    (motive_2 := fun positions _hinvariant =>
      ∀ assignment runtimeObject, NormalForm.selectionSetDirectiveFree
        (reifyResponsePositions schema assignment runtimeObject positions))
    (motive_3 := fun groups _hinvariant =>
      ∀ assignment runtimeObject responseName,
        NormalForm.selectionSetDirectiveFree
          (reifyPossibleDefinitions schema assignment runtimeObject responseName
            groups))
    (motive_4 := fun definitions _hinvariant =>
      ∀ assignment responseName, NormalForm.selectionSetDirectiveFree
        (reifyShapeDefinitions schema assignment responseName definitions))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hinvariant
  · intro currentParent positions shallow positionsInvariant positionsFree
      assignment
    unfold ResponseShape.reifySelectionSet
    split
    · exact positionsFree assignment currentParent
    · apply selectionSetDirectiveFree_filterMap
      intro runtimeObject selection hselection
      cases hfields : reifyResponsePositions schema assignment runtimeObject
          positions with
      | nil => simp [hfields] at hselection
      | cons head tail =>
          simp [hfields] at hselection
          subst selection
          have hfieldsFree := positionsFree assignment runtimeObject
          rw [hfields] at hfieldsFree
          exact ⟨rfl, hfieldsFree⟩
  · intro assignment runtimeObject
    trivial
  · intro position rest head tail headFree tailFree assignment runtimeObject
    cases position with
    | mk responseName possibleDefinitions =>
        simp only [reifyResponsePositions, ResponsePosition.reifyFields]
        exact NormalForm.selectionSetDirectiveFree_append
          (headFree assignment runtimeObject responseName)
          (tailFree assignment runtimeObject)
  · intro assignment runtimeObject responseName
    trivial
  · intro possible rest head tail headFree tailFree assignment runtimeObject
      responseName
    cases possible with
    | mk objectTypes definitions =>
        simp only [reifyPossibleDefinitions, PossibleDefinitions.reifyFields]
        split
        · exact NormalForm.selectionSetDirectiveFree_append
            (headFree assignment responseName)
            (tailFree assignment runtimeObject responseName)
        · exact tailFree assignment runtimeObject responseName
  · intro assignment responseName
    trivial
  · intro definition rest hleaf tail tailFree assignment responseName
    cases definition with
    | mk clause field subshape =>
        simp only [ShapeDefinition.subshape] at hleaf
        subst subshape
        simp only [reifyShapeDefinitions, ShapeDefinition.clause]
        split
        · exact ⟨by simp [NormalForm.selectionDirectiveFree,
              NormalForm.selectionSetDirectiveFree,
              ShapeDefinition.reifyField], tailFree assignment responseName⟩
        · exact tailFree assignment responseName
  · intro definition rest child hchild childInvariant tail childFree tailFree
      assignment responseName
    cases definition with
    | mk clause field subshape =>
        simp only [ShapeDefinition.subshape] at hchild
        subst subshape
        simp only [reifyShapeDefinitions, ShapeDefinition.clause]
        split
        · exact ⟨⟨by simp, childFree assignment⟩,
            tailFree assignment responseName⟩
        · exact tailFree assignment responseName

private theorem perm_cons_append {alpha : Type} (item : alpha) (before after : List alpha)
    : (item :: before ++ after).Perm (before ++ item :: after) := by
  simpa [List.append_assoc] using
    ((List.perm_append_comm (l₁ := [item]) (l₂ := before)).append_right after)

private theorem wrappedEquivalentCaseBranches_completeEqual_aux
    (leftSupport rightSupport : List BoolVar)
    (hleftSupportNodup : leftSupport.Nodup)
    (hrightSupportNodup : rightSupport.Nodup)
    (hleftSupportNonempty : leftSupport ≠ [])
    (hrightSupportNonempty : rightSupport ≠ [])
    (leftBodies rightBodies : BoolCase → List Selection)
    (hbodyRelation
      : ∀ leftCase,
          leftCase ∈ NormalForm.allBoolCases leftSupport
          → ∀ rightCase,
              rightCase ∈ NormalForm.allBoolCases rightSupport
              → NormalForm.completeNormalBoolCasesEquivalent leftCase rightCase
              → NormalForm.SelectionSetEqualUpToReordering
                  (leftBodies leftCase) (rightBodies rightCase))
    : ∀ (leftCases rightCases : List BoolCase),
        leftCases.Nodup
        → rightCases.Nodup
        → (∀ leftCase,
            leftCase ∈ leftCases → leftCase ∈ NormalForm.allBoolCases leftSupport)
        → (∀ rightCase,
            rightCase ∈ rightCases → rightCase ∈ NormalForm.allBoolCases rightSupport)
        → (∀ leftCase,
            leftCase ∈ leftCases
            → ∃ rightCase,
                rightCase ∈ rightCases
                ∧ NormalForm.completeNormalBoolCasesEquivalent leftCase rightCase)
        → (∀ rightCase,
            rightCase ∈ rightCases
            → ∃ leftCase,
                leftCase ∈ leftCases
                ∧ NormalForm.completeNormalBoolCasesEquivalent leftCase rightCase)
        → NormalForm.CompleteNormalSelectionSetEqualUpToReordering
            leftSupport rightSupport
            (List.flatten
              (leftCases.map
                (fun boolCase =>
                  wrapNonemptyCase boolCase (leftBodies boolCase))))
            (List.flatten
              (rightCases.map
                (fun boolCase =>
                  wrapNonemptyCase boolCase (rightBodies boolCase))))
  | [], rightCases, _hleftNodup, _hrightNodup, _hleftGenerated,
      _hrightGenerated, _hforward, hreverse => by
      cases rightCases with
      | nil => exact ⟨[], by simp, by simp, by simp⟩
      | cons rightCase rest =>
          rcases hreverse rightCase (by simp) with
            ⟨leftCase, hleftCase, _hequivalent⟩
          simp at hleftCase
  | leftCase :: leftRest, rightCases, hleftNodup, hrightNodup,
      hleftGenerated, hrightGenerated, hforward, hreverse => by
      have hleftParts := List.nodup_cons.mp hleftNodup
      rcases hforward leftCase (by simp) with
        ⟨rightCase, hrightCase, hcasesEquivalent⟩
      rcases List.mem_iff_append.mp hrightCase with
        ⟨rightBefore, rightAfter, hrightCases⟩
      subst rightCases
      let rightRest := rightBefore ++ rightAfter
      have hrightRestNodup : rightRest.Nodup := by
        apply List.Nodup.sublist
          ((List.Sublist.refl rightBefore).append
            ((List.Sublist.refl rightAfter).cons rightCase))
        exact hrightNodup
      have hrightCaseNotRest : rightCase ∉ rightRest := by
        intro hmem
        change rightCase ∈ rightBefore ++ rightAfter at hmem
        have hparts := List.nodup_append.mp hrightNodup
        have htailParts := List.nodup_cons.mp hparts.2.1
        rcases List.mem_append.mp hmem with hbefore | hafter
        · exact (hparts.2.2 rightCase hbefore rightCase (by simp)) rfl
        · exact htailParts.1 hafter
      have hleftRestGenerated : ∀ candidate, candidate ∈ leftRest →
          candidate ∈ NormalForm.allBoolCases leftSupport := by
        intro candidate hcandidate
        exact hleftGenerated candidate
          (List.mem_cons_of_mem leftCase hcandidate)
      have hrightRestGenerated : ∀ candidate, candidate ∈ rightRest →
          candidate ∈ NormalForm.allBoolCases rightSupport := by
        intro candidate hcandidate
        apply hrightGenerated candidate
        change candidate ∈ rightBefore ++ rightAfter at hcandidate
        simp only [List.mem_append, List.mem_cons]
        rcases List.mem_append.mp hcandidate with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (Or.inr hafter)
      have hforwardRest : ∀ candidate, candidate ∈ leftRest →
          ∃ matched, matched ∈ rightRest ∧
            NormalForm.completeNormalBoolCasesEquivalent candidate matched := by
        intro candidate hcandidate
        rcases hforward candidate
            (List.mem_cons_of_mem leftCase hcandidate) with
          ⟨matched, hmatched, hmatchedEquivalent⟩
        have hmatchedNe : matched ≠ rightCase := by
          intro heq
          subst matched
          have hcandidateHead :
              NormalForm.completeNormalBoolCasesEquivalent candidate leftCase :=
            NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_trans
              hmatchedEquivalent
              (NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_symm
                hcasesEquivalent)
          have hcandidateEq : candidate = leftCase :=
            NormalForm.CompleteNormalization.boolCase_eq_of_mem_allBoolCases_equivalent
              hleftSupportNodup (hleftRestGenerated candidate hcandidate)
              (hleftGenerated leftCase (by simp)) hcandidateHead
          exact hleftParts.1 (hcandidateEq ▸ hcandidate)
        refine ⟨matched, ?_, hmatchedEquivalent⟩
        change matched ∈ rightBefore ++ rightAfter
        simp only [List.mem_append, List.mem_cons] at hmatched ⊢
        rcases hmatched with hbefore | hhead | hafter
        · exact Or.inl hbefore
        · exact False.elim (hmatchedNe hhead)
        · exact Or.inr hafter
      have hreverseRest : ∀ candidate, candidate ∈ rightRest →
          ∃ matched, matched ∈ leftRest ∧
            NormalForm.completeNormalBoolCasesEquivalent matched candidate := by
        intro candidate hcandidate
        have hcandidateFull :
            candidate ∈ rightBefore ++ rightCase :: rightAfter := by
          simp only [List.mem_append, List.mem_cons]
          rcases List.mem_append.mp hcandidate with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (Or.inr hafter)
        rcases hreverse candidate hcandidateFull with
          ⟨matched, hmatched, hmatchedEquivalent⟩
        rcases List.mem_cons.mp hmatched with hhead | htail
        · subst matched
          have hcandidateRight :
              NormalForm.completeNormalBoolCasesEquivalent rightCase candidate :=
            NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_trans
              (NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_symm
                hcasesEquivalent) hmatchedEquivalent
          have hcandidateEq : rightCase = candidate :=
            NormalForm.CompleteNormalization.boolCase_eq_of_mem_allBoolCases_equivalent
              hrightSupportNodup
              (hrightGenerated rightCase (by simp))
              (hrightRestGenerated candidate hcandidate) hcandidateRight
          subst candidate
          exact False.elim (hrightCaseNotRest hcandidate)
        · exact ⟨matched, htail, hmatchedEquivalent⟩
      have hrest := wrappedEquivalentCaseBranches_completeEqual_aux
        leftSupport rightSupport hleftSupportNodup hrightSupportNodup
        hleftSupportNonempty hrightSupportNonempty leftBodies rightBodies
        hbodyRelation leftRest rightRest hleftParts.2 hrightRestNodup
        hleftRestGenerated hrightRestGenerated hforwardRest hreverseRest
      have hleftGeneratedHead := hleftGenerated leftCase (by simp)
      have hrightGeneratedHead := hrightGenerated rightCase (by simp)
      have hrelation := hbodyRelation leftCase hleftGeneratedHead rightCase
        hrightGeneratedHead hcasesEquivalent
      cases hleftBody : leftBodies leftCase with
      | nil =>
          cases hrightBody : rightBodies rightCase with
          | nil =>
              simpa [wrapNonemptyCase, hleftBody, hrightBody, rightRest,
                List.map_append] using hrest
          | cons rightHead rightTail =>
              rcases hrelation with ⟨pairs, hpairsLeft, hpairsRight, _⟩
              have hlength : (leftBodies leftCase).length =
                  (rightBodies rightCase).length := by
                calc
                  _ = pairs.length := by
                    simpa using hpairsLeft.length_eq.symm
                  _ = _ := by simpa using hpairsRight.length_eq
              simp [hleftBody, hrightBody] at hlength
      | cons leftHead leftTail =>
          cases hrightBody : rightBodies rightCase with
          | nil =>
              rcases hrelation with ⟨pairs, hpairsLeft, hpairsRight, _⟩
              have hlength : (leftBodies leftCase).length =
                  (rightBodies rightCase).length := by
                calc
                  _ = pairs.length := by
                    simpa using hpairsLeft.length_eq.symm
                  _ = _ := by simpa using hpairsRight.length_eq
              simp [hleftBody, hrightBody] at hlength
          | cons rightHead rightTail =>
              have hleftCaseNonempty : leftCase ≠ [] := by
                intro hnil
                have hnames :=
                  NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
                    hleftGeneratedHead
                simp [hnil] at hnames
                exact hleftSupportNonempty hnames
              have hrightCaseNonempty : rightCase ≠ [] := by
                intro hnil
                have hnames :=
                  NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
                    hrightGeneratedHead
                simp [hnil] at hnames
                exact hrightSupportNonempty hnames
              rcases
                  NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                    leftCase (leftHead :: leftTail) hleftCaseNonempty with
                ⟨leftSelection, hleftWrap⟩
              rcases
                  NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                    rightCase (rightHead :: rightTail) hrightCaseNonempty with
                ⟨rightSelection, hrightWrap⟩
              rcases hrest with
                ⟨pairs, hpairsLeft, hpairsRight, hpairsEqual⟩
              refine ⟨(leftSelection, rightSelection) :: pairs, ?_, ?_, ?_⟩
              · simp only [List.map_cons]
                simpa [wrapNonemptyCase, hleftBody, hleftWrap] using
                  hpairsLeft.cons leftSelection
              · simp only [List.map_cons]
                have hrightMove := perm_cons_append rightSelection
                  (List.flatten (rightBefore.map (fun boolCase =>
                    wrapNonemptyCase boolCase (rightBodies boolCase))))
                  (List.flatten (rightAfter.map (fun boolCase =>
                    wrapNonemptyCase boolCase (rightBodies boolCase))))
                have hpairsRightUnfolded :
                    (pairs.map Prod.snd).Perm
                      (List.flatten (rightBefore.map (fun boolCase =>
                          wrapNonemptyCase boolCase (rightBodies boolCase))) ++
                        List.flatten (rightAfter.map (fun boolCase =>
                          wrapNonemptyCase boolCase (rightBodies boolCase)))) := by
                  simpa [rightRest, List.map_append] using hpairsRight
                have hpairsRight' :=
                  (hpairsRightUnfolded.cons rightSelection).trans hrightMove
                simpa [rightRest, List.map_append, wrapNonemptyCase,
                  hrightBody, hrightWrap] using hpairsRight'
              · intro pair hpair
                rcases List.mem_cons.mp hpair with hhead | htail
                · subst pair
                  exact ⟨leftCase, rightCase, leftHead :: leftTail,
                    rightHead :: rightTail,
                    NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
                      hleftSupportNodup hleftGeneratedHead,
                    NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
                      hrightSupportNodup hrightGeneratedHead,
                    NormalForm.CompleteNormalization.completeNormalBooleanStem_wrapWithBoolCase
                      leftCase (leftHead :: leftTail) leftSelection
                      hleftCaseNonempty hleftWrap,
                    NormalForm.CompleteNormalization.completeNormalBooleanStem_wrapWithBoolCase
                      rightCase (rightHead :: rightTail) rightSelection
                      hrightCaseNonempty hrightWrap,
                    hcasesEquivalent, by
                      simpa [hleftBody, hrightBody] using hrelation⟩
                · exact hpairsEqual pair htail

private theorem wrappedEquivalentCaseBranches_completeEqual
    (leftSupport rightSupport : List BoolVar)
    (hleftSupportNodup : leftSupport.Nodup)
    (hrightSupportNodup : rightSupport.Nodup)
    (hsupportEquivalent : ∀ varName, varName ∈ leftSupport ↔ varName ∈ rightSupport)
    (hleftSupportNonempty : leftSupport ≠ [])
    (leftBodies rightBodies : BoolCase → List Selection)
    (hbodyRelation
      : ∀ leftCase,
          leftCase ∈ NormalForm.allBoolCases leftSupport
          → ∀ rightCase,
              rightCase ∈ NormalForm.allBoolCases rightSupport
              → NormalForm.completeNormalBoolCasesEquivalent leftCase rightCase
              → NormalForm.SelectionSetEqualUpToReordering
                  (leftBodies leftCase) (rightBodies rightCase))
    : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
        leftSupport rightSupport
        (List.flatten
          ((NormalForm.allBoolCases leftSupport).map
            (fun boolCase => wrapNonemptyCase boolCase (leftBodies boolCase))))
        (List.flatten
          ((NormalForm.allBoolCases rightSupport).map
            (fun boolCase => wrapNonemptyCase boolCase (rightBodies boolCase)))) := by
  have hrightSupportNonempty : rightSupport ≠ [] := by
    intro hnil
    rcases List.exists_mem_of_ne_nil leftSupport hleftSupportNonempty with
      ⟨varName, hvarName⟩
    have := (hsupportEquivalent varName).1 hvarName
    simp [hnil] at this
  apply wrappedEquivalentCaseBranches_completeEqual_aux leftSupport rightSupport
    hleftSupportNodup hrightSupportNodup hleftSupportNonempty
    hrightSupportNonempty leftBodies rightBodies hbodyRelation
  · exact NormalForm.CompleteNormalization.allBoolCases_nodup
      hleftSupportNodup
  · exact NormalForm.CompleteNormalization.allBoolCases_nodup
      hrightSupportNodup
  · intro leftCase hleftCase
    exact hleftCase
  · intro rightCase hrightCase
    exact hrightCase
  · intro leftCase hleftCase
    have hleftComplete :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
        hleftSupportNodup hleftCase
    have hrightComplete :
        NormalForm.completeNormalBoolCase rightSupport leftCase :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
        hleftComplete hrightSupportNodup (fun varName =>
          (hleftComplete.2.2 varName).trans (hsupportEquivalent varName))
    exact allBoolCases_complete_representative hrightComplete
  · intro rightCase hrightCase
    have hrightComplete :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
        hrightSupportNodup hrightCase
    have hleftComplete :
        NormalForm.completeNormalBoolCase leftSupport rightCase :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
        hrightComplete hleftSupportNodup (fun varName =>
          (hrightComplete.2.2 varName).trans (hsupportEquivalent varName).symm)
    rcases allBoolCases_complete_representative hleftComplete with
      ⟨leftCase, hleftCase, hequivalent⟩
    exact ⟨leftCase, hleftCase,
      NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_symm
        hequivalent⟩

private theorem completeNormalSelectionSetEqual_change_variables
    {leftVariables rightVariables newLeftVariables newRightVariables : List BoolVar}
    {left right : List Selection}
    (hequal
      : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
          leftVariables rightVariables left right)
    (hnewLeftNodup : newLeftVariables.Nodup) (hnewRightNodup : newRightVariables.Nodup)
    (hleftVariables : ∀ varName, varName ∈ leftVariables ↔ varName ∈ newLeftVariables)
    (hrightVariables : ∀ varName, varName ∈ rightVariables ↔ varName ∈ newRightVariables)
    : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
        newLeftVariables newRightVariables left right := by
  rcases hequal with ⟨pairs, hpairsLeft, hpairsRight, hpairsEqual⟩
  refine ⟨pairs, hpairsLeft, hpairsRight, ?_⟩
  intro pair hpair
  rcases hpairsEqual pair hpair with
    ⟨leftCase, rightCase, leftBody, rightBody, hleftCase, hrightCase,
      hleftStem, hrightStem, hcasesEquivalent, hbodiesEqual⟩
  exact ⟨leftCase, rightCase, leftBody, rightBody,
    NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
      hleftCase hnewLeftNodup (fun varName =>
        (hleftCase.2.2 varName).trans (hleftVariables varName)),
    NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
      hrightCase hnewRightNodup (fun varName =>
        (hrightCase.2.2 varName).trans (hrightVariables varName)),
    hleftStem, hrightStem, hcasesEquivalent, hbodiesEqual⟩

private theorem reifyOperations_equal_of_strict
    (schema : Schema) (left right : Operation)
    (leftShape rightShape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    (hstrict : StrictShapeEquivalent schema leftShape rightShape)
    : NormalForm.completeNormalOperationsEqualUpToReordering
        (reifyOperation schema left leftShape)
        (reifyOperation schema right rightShape) := by
  rcases hstrict with ⟨⟨hleftSubset, hrightSubset⟩, hsupportEquivalent⟩
  have hoperationType : leftShape.operationType = rightShape.operationType :=
    hleftSubset.1
  have hrootType : leftShape.rootType = rightShape.rootType :=
    hleftSubset.2.1
  have hleftSupportNodup : leftShape.boolSupport.Nodup :=
    computeOperationShape_support_nodup schema left leftShape hleftCompute
  have hrightSupportNodup : rightShape.boolSupport.Nodup :=
    computeOperationShape_support_nodup schema right rightShape hrightCompute
  have hleftInvariant : RecursiveDecoderShapeInvariant schema
      leftShape.boolSupport leftShape.rootType leftShape.root := by
    have hinvariant := computeOperationShape_recursiveInvariant schema left
      leftShape hschema hleftValid hleftCompute
    rcases computeOperationShape_fields schema left leftShape hleftCompute with
      ⟨_hoperationType, _hrootType, hsupport, _hdecode⟩
    simpa [hsupport] using hinvariant
  have hrightInvariant : RecursiveDecoderShapeInvariant schema
      rightShape.boolSupport rightShape.rootType rightShape.root := by
    have hinvariant := computeOperationShape_recursiveInvariant schema right
      rightShape hschema hrightValid hrightCompute
    rcases computeOperationShape_fields schema right rightShape hrightCompute with
      ⟨_hoperationType, _hrootType, hsupport, _hdecode⟩
    simpa [hsupport] using hinvariant
  let leftBodies : BoolCase → List Selection := fun assignment =>
    leftShape.root.reifySelectionSet schema assignment leftShape.rootType
  let rightBodies : BoolCase → List Selection := fun assignment =>
    rightShape.root.reifySelectionSet schema assignment rightShape.rootType
  let leftSelectionSet := List.flatten
    ((NormalForm.allBoolCases leftShape.boolSupport).map (fun assignment =>
      wrapNonemptyCase assignment (leftBodies assignment)))
  let rightSelectionSet := List.flatten
    ((NormalForm.allBoolCases rightShape.boolSupport).map (fun assignment =>
      wrapNonemptyCase assignment (rightBodies assignment)))
  have hleftSelectionSet :
      (reifyOperation schema left leftShape).selectionSet = leftSelectionSet := by
    rfl
  have hrightSelectionSet :
      (reifyOperation schema right rightShape).selectionSet = rightSelectionSet := by
    rfl
  have hleftBodyVariables : ∀ assignment,
      NormalForm.selectionSetBooleanVariables (leftBodies assignment) = [] := by
    intro assignment
    exact
      NormalForm.CompleteNormalization.selectionSetDirectiveFree_booleanVariables_nil
        _ (hleftInvariant.reifyDirectiveFree assignment)
  have hrightBodyVariables : ∀ assignment,
      NormalForm.selectionSetBooleanVariables (rightBodies assignment) = [] := by
    intro assignment
    exact
      NormalForm.CompleteNormalization.selectionSetDirectiveFree_booleanVariables_nil
        _ (hrightInvariant.reifyDirectiveFree assignment)
  have hleftUnionVariables : ∀ varName,
      varName ∈ leftShape.boolSupport ↔
        varName ∈ supportUnion leftShape.boolSupport rightShape.boolSupport := by
    intro varName
    unfold supportUnion
    rw [NormalForm.CompleteNormalization.mem_dedupBoolVars_iff]
    simp only [List.mem_append]
    exact ⟨Or.inl, fun hmem => hmem.elim id
      (fun hright => (hsupportEquivalent varName).2 hright)⟩
  have hrightUnionVariables : ∀ varName,
      varName ∈ leftShape.boolSupport ↔
        varName ∈ supportUnion rightShape.boolSupport leftShape.boolSupport := by
    intro varName
    unfold supportUnion
    rw [NormalForm.CompleteNormalization.mem_dedupBoolVars_iff]
    simp only [List.mem_append]
    exact ⟨fun hleft => Or.inr hleft, fun hmem => hmem.elim
      (fun hright => (hsupportEquivalent varName).2 hright) id⟩
  have hbodyRelation : ∀ leftCase,
      leftCase ∈ NormalForm.allBoolCases leftShape.boolSupport →
      ∀ rightCase,
      rightCase ∈ NormalForm.allBoolCases rightShape.boolSupport →
      NormalForm.completeNormalBoolCasesEquivalent leftCase rightCase →
      NormalForm.SelectionSetEqualUpToReordering
        (leftBodies leftCase) (rightBodies rightCase) := by
    intro leftCase hleftCase rightCase hrightCase hcasesEquivalent
    have hleftComplete :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
        hleftSupportNodup hleftCase
    have hleftUnionComplete : NormalForm.completeNormalBoolCase
        (supportUnion leftShape.boolSupport rightShape.boolSupport) leftCase :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
        hleftComplete
        (NormalForm.CompleteNormalization.dedupBoolVars_nodup _)
        (fun varName =>
          (hleftComplete.2.2 varName).trans (hleftUnionVariables varName))
    have hrightUnionComplete : NormalForm.completeNormalBoolCase
        (supportUnion rightShape.boolSupport leftShape.boolSupport) leftCase :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
        hleftComplete
        (NormalForm.CompleteNormalization.dedupBoolVars_nodup _)
        (fun varName =>
          (hleftComplete.2.2 varName).trans (hrightUnionVariables varName))
    have hpaths : PathsEquivalentAt schema leftCase leftShape.rootType
        leftShape.root rightShape.root := by
      constructor
      · intro path hpath
        have hcovered := hleftSubset.2.2 leftCase hleftUnionComplete path hpath
        simpa [hrootType] using hcovered
      · intro path hpath
        have hcovered := hrightSubset.2.2 leftCase hrightUnionComplete path (by
          simpa [hrootType] using hpath)
        exact hcovered
    have hrightInvariantAtLeft : RecursiveDecoderShapeInvariant schema
        rightShape.boolSupport leftShape.rootType rightShape.root := by
      simpa [hrootType] using hrightInvariant
    have hrelation := hleftInvariant.reifyCanonical leftCase rightShape.root
      hrightInvariantAtLeft hpaths
    have hrightCasesEqual := hrightInvariant.reify_eq_of_equivalent_cases
      leftCase rightCase hleftComplete.2.1
      (NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
        hrightSupportNodup hrightCase).2.1 hcasesEquivalent
    dsimp [leftBodies, rightBodies]
    simpa [hrootType, hrightCasesEqual] using hrelation
  unfold NormalForm.completeNormalOperationsEqualUpToReordering
  refine ⟨hoperationType, ?_⟩
  cases hleftSupportValue : leftShape.boolSupport with
  | nil =>
      have hrightSupportValue : rightShape.boolSupport = [] := by
        cases hright : rightShape.boolSupport with
        | nil => rfl
        | cons head tail =>
            have hrightMem : head ∈ rightShape.boolSupport := by
              simp [hright]
            have hleftMem := (hsupportEquivalent head).2 hrightMem
            simp [hleftSupportValue] at hleftMem
      have hselectionRelation := hbodyRelation [] (by
        simp [hleftSupportValue, NormalForm.allBoolCases]) [] (by
        simp [hrightSupportValue, NormalForm.allBoolCases])
        (NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_refl [])
      have hleftVariables : NormalForm.operationBoolVars
          (reifyOperation schema left leftShape) = [] := by
        unfold NormalForm.operationBoolVars
        rw [hleftSelectionSet]
        have hselection : leftSelectionSet = leftBodies [] := by
          simp [leftSelectionSet, hleftSupportValue,
            NormalForm.allBoolCases, wrapNonemptyCase_nil]
        rw [hselection, hleftBodyVariables]
        rfl
      rw [hleftVariables, hleftSelectionSet, hrightSelectionSet]
      simpa [leftSelectionSet, rightSelectionSet, hleftSupportValue,
        hrightSupportValue, NormalForm.allBoolCases, wrapNonemptyCase_nil] using
          hselectionRelation
  | cons supportHead supportTail =>
      have hleftSupportNonempty : leftShape.boolSupport ≠ [] := by
        simp [hleftSupportValue]
      have hcompleteRelation := wrappedEquivalentCaseBranches_completeEqual
        leftShape.boolSupport rightShape.boolSupport hleftSupportNodup
        hrightSupportNodup hsupportEquivalent hleftSupportNonempty leftBodies
        rightBodies hbodyRelation
      have hselectionLength : leftSelectionSet.length =
          rightSelectionSet.length := by
        rcases hcompleteRelation with
          ⟨pairs, hpairsLeft, hpairsRight, _hpairsEqual⟩
        calc
          _ = pairs.length := by
            simpa [leftSelectionSet] using hpairsLeft.length_eq.symm
          _ = _ := by
            simpa [rightSelectionSet] using hpairsRight.length_eq
      by_cases hleftEmpty : leftSelectionSet = []
      · have hrightEmpty : rightSelectionSet = [] := by
          apply List.length_eq_zero_iff.mp
          rw [← hselectionLength, hleftEmpty]
          rfl
        have hleftVariables : NormalForm.operationBoolVars
            (reifyOperation schema left leftShape) = [] := by
          unfold NormalForm.operationBoolVars
          rw [hleftSelectionSet, hleftEmpty]
          rfl
        rw [hleftVariables, hleftSelectionSet, hrightSelectionSet,
          hleftEmpty, hrightEmpty]
        exact
          NormalForm.GroundTypeNormalization.selectionSetEqualUpToReordering_refl
            []
      · have hrightNonempty : rightSelectionSet ≠ [] := by
          intro hrightEmpty
          apply hleftEmpty
          apply List.length_eq_zero_iff.mp
          rw [hselectionLength, hrightEmpty]
          rfl
        have hleftVariablesIff : ∀ varName,
            varName ∈ NormalForm.operationBoolVars
                (reifyOperation schema left leftShape) ↔
              varName ∈ leftShape.boolSupport := by
          intro varName
          unfold NormalForm.operationBoolVars
          rw [hleftSelectionSet]
          exact wrappedCaseBranches_variables_mem_iff leftShape.boolSupport
            leftBodies (NormalForm.allBoolCases leftShape.boolSupport)
            (fun boolCase hcase => hcase)
            (fun boolCase _hcase => hleftBodyVariables boolCase)
            hleftEmpty varName
        have hrightVariablesIff : ∀ varName,
            varName ∈ NormalForm.operationBoolVars
                (reifyOperation schema right rightShape) ↔
              varName ∈ rightShape.boolSupport := by
          intro varName
          unfold NormalForm.operationBoolVars
          rw [hrightSelectionSet]
          exact wrappedCaseBranches_variables_mem_iff rightShape.boolSupport
            rightBodies (NormalForm.allBoolCases rightShape.boolSupport)
            (fun boolCase hcase => hcase)
            (fun boolCase _hcase => hrightBodyVariables boolCase)
            hrightNonempty varName
        have hchangedRelation := completeNormalSelectionSetEqual_change_variables
          hcompleteRelation
          (NormalForm.CompleteNormalization.operationBoolVars_nodup
            (reifyOperation schema left leftShape))
          (NormalForm.CompleteNormalization.operationBoolVars_nodup
            (reifyOperation schema right rightShape))
          (fun varName => (hleftVariablesIff varName).symm)
          (fun varName => (hrightVariablesIff varName).symm)
        cases hleftVariablesValue : NormalForm.operationBoolVars
            (reifyOperation schema left leftShape) with
        | nil =>
            have hheadMem : supportHead ∈ leftShape.boolSupport := by
              simp [hleftSupportValue]
            have := (hleftVariablesIff supportHead).2 hheadMem
            simp [hleftVariablesValue] at this
        | cons leftHead leftTail =>
            rw [hleftSelectionSet, hrightSelectionSet]
            simpa [hleftVariablesValue] using hchangedRelation

private theorem completeNormalSelectionSetEqual_symm
    {leftVariables rightVariables : List BoolVar}
    {left right : List Selection}
    (hequal
      : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
          leftVariables rightVariables left right)
    : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
        rightVariables leftVariables right left := by
  rcases hequal with ⟨pairs, hleft, hright, hrelations⟩
  refine ⟨pairs.map (fun pair => (pair.2, pair.1)), ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using hright
  · simpa [List.map_map, Function.comp_def] using hleft
  · intro pair hpair
    rcases List.mem_map.mp hpair with ⟨source, hsource, rfl⟩
    rcases hrelations source hsource with
      ⟨leftCase, rightCase, leftBody, rightBody, hleftCase, hrightCase,
        hleftStem, hrightStem, hcasesEquivalent, hbodiesEqual⟩
    exact ⟨rightCase, leftCase, rightBody, leftBody, hrightCase, hleftCase,
      hrightStem, hleftStem,
      NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_symm
        hcasesEquivalent,
      NormalForm.SelectionSetEqualUpToReordering.symm hbodiesEqual⟩

private theorem compose_aligned_complete_pairs
    (middleVariables : List BoolVar) (hmiddleNonempty : middleVariables ≠ [])
    : ∀ (firstPairs secondPairs : List (Selection × Selection)),
        firstPairs.map Prod.snd = secondPairs.map Prod.fst
        → (∀ pair,
            pair ∈ firstPairs
            → NormalForm.CompleteNormalSelectionEqualUpToReordering
                leftVariables middleVariables pair.1 pair.2)
        → (∀ pair,
            pair ∈ secondPairs
            → NormalForm.CompleteNormalSelectionEqualUpToReordering
                middleVariables rightVariables pair.1 pair.2)
        → ∃ outputPairs : List (Selection × Selection),
            outputPairs.map Prod.fst = firstPairs.map Prod.fst
            ∧ outputPairs.map Prod.snd = secondPairs.map Prod.snd
            ∧ ∀ pair,
                pair ∈ outputPairs
                → NormalForm.CompleteNormalSelectionEqualUpToReordering
                    leftVariables rightVariables pair.1 pair.2
  | [], [], _hmaps, _hfirst, _hsecond =>
      ⟨[], rfl, rfl, by intro pair hpair; simp at hpair⟩
  | first :: firstRest, second :: secondRest, hmaps, hfirst, hsecond => by
      have hheads : first.2 = second.1 :=
        List.cons.inj (by simpa using hmaps) |>.1
      have htails : firstRest.map Prod.snd = secondRest.map Prod.fst :=
        List.cons.inj (by simpa using hmaps) |>.2
      have hfirstHead := hfirst first List.mem_cons_self
      have hsecondHead := hsecond second List.mem_cons_self
      have hfirstRest : ∀ pair, pair ∈ firstRest →
          NormalForm.CompleteNormalSelectionEqualUpToReordering
            leftVariables middleVariables pair.1 pair.2 := by
        intro pair hpair
        exact hfirst pair (List.mem_cons_of_mem first hpair)
      have hsecondRest : ∀ pair, pair ∈ secondRest →
          NormalForm.CompleteNormalSelectionEqualUpToReordering
            middleVariables rightVariables pair.1 pair.2 := by
        intro pair hpair
        exact hsecond pair (List.mem_cons_of_mem second hpair)
      rcases compose_aligned_complete_pairs middleVariables hmiddleNonempty
          firstRest secondRest htails hfirstRest hsecondRest with
        ⟨outputRest, houtLeft, houtRight, houtRelations⟩
      let outputHead : Selection × Selection := (first.1, second.2)
      refine ⟨outputHead :: outputRest, ?_, ?_, ?_⟩
      · simp [outputHead, houtLeft]
      · simp [outputHead, houtRight]
      · intro pair hpair
        rcases List.mem_cons.mp hpair with hhead | hrest
        · subst pair
          change NormalForm.CompleteNormalSelectionEqualUpToReordering
            leftVariables rightVariables first.1 second.2
          rcases hfirstHead with
            ⟨leftCase, firstMiddleCase, leftBody, firstMiddleBody,
              hleftCase, hfirstMiddleCase, hleftStem, hfirstMiddleStem,
              hfirstCasesEquivalent, hfirstBodiesEqual⟩
          rcases hsecondHead with
            ⟨secondMiddleCase, rightCase, secondMiddleBody, rightBody,
              hsecondMiddleCase, hrightCase, hsecondMiddleStem, hrightStem,
              hsecondCasesEquivalent, hsecondBodiesEqual⟩
          have hsecondMiddleStem' :
              NormalForm.completeNormalBooleanStem secondMiddleCase first.2
                secondMiddleBody := by
            simpa [hheads] using hsecondMiddleStem
          have hmiddleEqual :=
            completeNormalBooleanStem_case_body_eq
              hfirstMiddleCase hsecondMiddleCase hmiddleNonempty
              hfirstMiddleStem hsecondMiddleStem'
          rcases hmiddleEqual with ⟨hmiddleCase, hmiddleBody⟩
          subst secondMiddleCase
          subst secondMiddleBody
          exact ⟨leftCase, rightCase, leftBody, rightBody, hleftCase,
            hrightCase, hleftStem, hrightStem,
            NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_trans
              hfirstCasesEquivalent hsecondCasesEquivalent,
            NormalForm.SelectionSetEqualUpToReordering.trans hfirstBodiesEqual
              hsecondBodiesEqual⟩
        · exact houtRelations pair hrest
  | [], _ :: _, hmaps, _hfirst, _hsecond => by
      simp at hmaps
  | _ :: _, [], hmaps, _hfirst, _hsecond => by
      simp at hmaps

private theorem completeNormalSelectionSetEqual_trans
    {leftVariables middleVariables rightVariables : List BoolVar}
    {left middle right : List Selection}
    (hmiddleNonempty : middleVariables ≠ [])
    (hfirst
      : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
          leftVariables middleVariables left middle)
    (hsecond
      : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
          middleVariables rightVariables middle right)
    : NormalForm.CompleteNormalSelectionSetEqualUpToReordering
        leftVariables rightVariables left right := by
  rcases hfirst with
    ⟨firstPairs, hfirstLeft, hfirstRight, hfirstRelations⟩
  rcases hsecond with
    ⟨secondPairs, hsecondLeft, hsecondRight, hsecondRelations⟩
  have hmaps : (firstPairs.map Prod.snd).Perm
      (secondPairs.map Prod.fst) := hfirstRight.trans hsecondLeft.symm
  rcases NormalForm.selectionPairs_align_fst
      (firstPairs.map Prod.snd) secondPairs hmaps with
    ⟨alignedSecond, halignedSecond, halignedMap⟩
  have halignedRelations : ∀ pair, pair ∈ alignedSecond →
      NormalForm.CompleteNormalSelectionEqualUpToReordering
        middleVariables rightVariables pair.1 pair.2 := by
    intro pair hpair
    exact hsecondRelations pair (halignedSecond.mem_iff.mp hpair)
  rcases compose_aligned_complete_pairs middleVariables hmiddleNonempty
      firstPairs alignedSecond halignedMap.symm hfirstRelations
      halignedRelations with
    ⟨outputPairs, houtLeft, houtRight, houtRelations⟩
  exact ⟨outputPairs,
    houtLeft ▸ hfirstLeft,
    by
      rw [houtRight]
      exact (halignedSecond.map Prod.snd).trans hsecondRight,
    houtRelations⟩

private theorem completeNormalOperationsEqual_symm
    {left right : Operation}
    (hequal : NormalForm.completeNormalOperationsEqualUpToReordering left right)
    : NormalForm.completeNormalOperationsEqualUpToReordering right left := by
  have hvariables :=
    operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReordering
      hequal
  rcases hequal with ⟨hoperationType, hselectionSet⟩
  unfold NormalForm.completeNormalOperationsEqualUpToReordering
  refine ⟨hoperationType.symm, ?_⟩
  cases hleftVariables : NormalForm.operationBoolVars left with
  | nil =>
      have hrightVariables := operationBoolVars_eq_nil_of_equivalent_left_nil
        hvariables hleftVariables
      rw [hrightVariables]
      apply NormalForm.SelectionSetEqualUpToReordering.symm
      simpa [hleftVariables] using hselectionSet
  | cons leftHead leftTail =>
      have hrightNonempty : NormalForm.operationBoolVars right ≠ [] := by
        intro hrightNil
        have hheadLeft : leftHead ∈ NormalForm.operationBoolVars left := by
          simp [hleftVariables]
        have hheadRight := (hvariables leftHead).1 hheadLeft
        simp [hrightNil] at hheadRight
      cases hrightVariables : NormalForm.operationBoolVars right with
      | nil => exact False.elim (hrightNonempty hrightVariables)
      | cons rightHead rightTail =>
          apply completeNormalSelectionSetEqual_symm
          simpa [hleftVariables, hrightVariables] using hselectionSet

private theorem completeNormalOperationsEqual_trans
    {left middle right : Operation}
    (hfirst : NormalForm.completeNormalOperationsEqualUpToReordering left middle)
    (hsecond : NormalForm.completeNormalOperationsEqualUpToReordering middle right)
    : NormalForm.completeNormalOperationsEqualUpToReordering left right := by
  have hfirstVariables :=
    operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReordering
      hfirst
  have hsecondVariables :=
    operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReordering
      hsecond
  rcases hfirst with ⟨hfirstType, hfirstSelections⟩
  rcases hsecond with ⟨hsecondType, hsecondSelections⟩
  unfold NormalForm.completeNormalOperationsEqualUpToReordering
  refine ⟨hfirstType.trans hsecondType, ?_⟩
  cases hleftVariables : NormalForm.operationBoolVars left with
  | nil =>
      have hmiddleVariables := operationBoolVars_eq_nil_of_equivalent_left_nil
        hfirstVariables hleftVariables
      have hrightVariables := operationBoolVars_eq_nil_of_equivalent_left_nil
        hsecondVariables hmiddleVariables
      have hfirstSelectionSet :
          NormalForm.SelectionSetEqualUpToReordering
            left.selectionSet middle.selectionSet := by
        simpa [hleftVariables] using hfirstSelections
      have hsecondSelectionSet :
          NormalForm.SelectionSetEqualUpToReordering
            middle.selectionSet right.selectionSet := by
        simpa [hmiddleVariables] using hsecondSelections
      exact NormalForm.SelectionSetEqualUpToReordering.trans hfirstSelectionSet
        hsecondSelectionSet
  | cons leftHead leftTail =>
      have hmiddleNonempty : NormalForm.operationBoolVars middle ≠ [] := by
        intro hmiddleNil
        have hheadLeft : leftHead ∈ NormalForm.operationBoolVars left := by
          simp [hleftVariables]
        have hheadMiddle := (hfirstVariables leftHead).1 hheadLeft
        simp [hmiddleNil] at hheadMiddle
      cases hmiddleVariables : NormalForm.operationBoolVars middle with
      | nil => exact False.elim (hmiddleNonempty hmiddleVariables)
      | cons middleHead middleTail =>
          have hfirstComplete :
              NormalForm.CompleteNormalSelectionSetEqualUpToReordering
                (leftHead :: leftTail)
                (middleHead :: middleTail)
                left.selectionSet middle.selectionSet := by
            simpa [hleftVariables, hmiddleVariables] using hfirstSelections
          have hsecondComplete :
              NormalForm.CompleteNormalSelectionSetEqualUpToReordering
                (middleHead :: middleTail)
                (NormalForm.operationBoolVars right)
                middle.selectionSet right.selectionSet := by
            simpa [hmiddleVariables] using hsecondSelections
          have hmiddleNonempty' : (middleHead :: middleTail) ≠ [] := by simp
          exact completeNormalSelectionSetEqual_trans hmiddleNonempty'
            hfirstComplete hsecondComplete

private theorem normalizedEqualUpToReordering_of_strictEquivalent
    (schema : Schema) (left right : Operation)
    (leftShape rightShape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    (hstrict : StrictShapeEquivalent schema leftShape rightShape)
    : NormalForm.completeNormalOperationsEqualUpToReordering
        (NormalForm.completeNormalizeOperation schema left)
        (NormalForm.completeNormalizeOperation schema right) := by
  have hleftBridge := reify_compute_equalUpToReordering schema left leftShape
    hschema hleftValid hleftCompute
  have hrightBridge := reify_compute_equalUpToReordering schema right rightShape
    hschema hrightValid hrightCompute
  have hreified := reifyOperations_equal_of_strict schema left right leftShape
    rightShape hschema hleftValid hrightValid hleftCompute hrightCompute hstrict
  exact completeNormalOperationsEqual_trans
    (completeNormalOperationsEqual_symm hleftBridge)
    (completeNormalOperationsEqual_trans hreified hrightBridge)

private theorem shapeSubset_of_normalizedEqualUpToReordering
    (schema : Schema) (required provided : Operation)
    (requiredShape providedShape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrequiredValid : Validation.operationDefinitionValid schema required)
    (hprovidedValid : Validation.operationDefinitionValid schema provided)
    (hsupport : NormalForm.operationBoolVarsEquivalent required provided)
    (hrequiredCompute : computeOperationShape schema required = .ok requiredShape)
    (hprovidedCompute : computeOperationShape schema provided = .ok providedShape)
    (hequal
      : NormalForm.completeNormalOperationsEqualUpToReordering
          (NormalForm.completeNormalizeOperation schema required)
          (NormalForm.completeNormalizeOperation schema provided))
    : ShapeSubset schema requiredShape providedShape := by
  rcases computeOperationShape_fields schema required requiredShape
      hrequiredCompute with
    ⟨hrequiredOperationType, hrequiredRootType, hrequiredSupport, _⟩
  rcases computeOperationShape_fields schema provided providedShape
      hprovidedCompute with
    ⟨hprovidedOperationType, hprovidedRootType, hprovidedSupport, _⟩
  have hsourceOperationType :
      required.operationType = provided.operationType := by
    exact hequal.1
  have hshapeSupport : ∀ varName,
      varName ∈ requiredShape.boolSupport ↔
        varName ∈ providedShape.boolSupport := by
    intro varName
    rw [hrequiredSupport, hprovidedSupport]
    exact hsupport varName
  have hrequiredSupportNodup : requiredShape.boolSupport.Nodup :=
    computeOperationShape_support_nodup schema required requiredShape
      hrequiredCompute
  have hprovidedSupportNodup : providedShape.boolSupport.Nodup :=
    computeOperationShape_support_nodup schema provided providedShape
      hprovidedCompute
  refine ⟨hrequiredOperationType.trans
      (hsourceOperationType.trans hprovidedOperationType.symm), ?_, ?_⟩
  · calc
      requiredShape.rootType = required.rootType schema := hrequiredRootType
      _ = schema.queryType :=
        Validation.operationDefinitionValid_rootType_eq hrequiredValid
      _ = provided.rootType schema :=
        (Validation.operationDefinitionValid_rootType_eq hprovidedValid).symm
      _ = providedShape.rootType := hprovidedRootType.symm
  · intro assignment hcomplete path hdenotes
    have hunionRequired : ∀ varName,
        varName ∈ supportUnion requiredShape.boolSupport
            providedShape.boolSupport ↔
          varName ∈ requiredShape.boolSupport := by
      intro varName
      rw [mem_supportUnion_iff]
      exact ⟨fun hmem => hmem.elim id
          (fun hprovided => (hshapeSupport varName).2 hprovided),
        Or.inl⟩
    have hunionProvided : ∀ varName,
        varName ∈ supportUnion requiredShape.boolSupport
            providedShape.boolSupport ↔
          varName ∈ providedShape.boolSupport := by
      intro varName
      rw [mem_supportUnion_iff]
      exact ⟨fun hmem => hmem.elim
          (fun hrequired => (hshapeSupport varName).1 hrequired) id,
        Or.inr⟩
    have hrequiredComplete : NormalForm.completeNormalBoolCase
        requiredShape.boolSupport assignment :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
        hcomplete hrequiredSupportNodup (fun varName =>
          (hcomplete.2.2 varName).trans (hunionRequired varName))
    have hprovidedComplete : NormalForm.completeNormalBoolCase
        providedShape.boolSupport assignment :=
      NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
        hcomplete hprovidedSupportNodup (fun varName =>
          (hcomplete.2.2 varName).trans (hunionProvided varName))
    have hrequiredOperationComplete : NormalForm.completeNormalBoolCase
        (NormalForm.operationBoolVars required) assignment := by
      simpa [← hrequiredSupport] using hrequiredComplete
    have hrequiredSelects :=
      computeOperationShape_denotesPath_operationSelectsPath schema required
        requiredShape assignment path hschema hrequiredValid hrequiredCompute
        hrequiredComplete hdenotes
    have hsourceFootprint :=
      completeNormalize_equalUpToReordering_operationSelectsPath_iff schema
        required provided assignment path hschema hrequiredValid hprovidedValid
        hsupport hequal hrequiredOperationComplete
    have hprovidedSelects := hsourceFootprint.1 hrequiredSelects
    exact
      (computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath
        schema provided providedShape assignment path hschema hprovidedValid
        hprovidedCompute hprovidedComplete).2 hprovidedSelects

private theorem strictEquivalent_of_normalizedEqualUpToReordering
    (schema : Schema) (left right : Operation)
    (leftShape rightShape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hsupport : NormalForm.operationBoolVarsEquivalent left right)
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    (hequal
      : NormalForm.completeNormalOperationsEqualUpToReordering
          (NormalForm.completeNormalizeOperation schema left)
          (NormalForm.completeNormalizeOperation schema right))
    : StrictShapeEquivalent schema leftShape rightShape := by
  have hleftSubset := shapeSubset_of_normalizedEqualUpToReordering schema
    left right leftShape rightShape hschema hleftValid hrightValid hsupport
    hleftCompute hrightCompute hequal
  have hrightSubset := shapeSubset_of_normalizedEqualUpToReordering schema
    right left rightShape leftShape hschema hrightValid hleftValid
    (fun varName => (hsupport varName).symm) hrightCompute hleftCompute
    (completeNormalOperationsEqual_symm hequal)
  have hleftSupport := computeOperationShape_support schema left leftShape
    hleftCompute
  have hrightSupport := computeOperationShape_support schema right rightShape
    hrightCompute
  exact ⟨⟨hleftSubset, hrightSubset⟩, fun varName => by
    rw [hleftSupport, hrightSupport]
    exact hsupport varName⟩

theorem computeOperationShape_strictEquivalent_iff_normalizedEqualUpToReordering
    (schema : Schema) (left right : Operation)
    (leftShape rightShape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hsupport : NormalForm.operationBoolVarsEquivalent left right)
    (hleftCompute : computeOperationShape schema left = .ok leftShape)
    (hrightCompute : computeOperationShape schema right = .ok rightShape)
    : StrictShapeEquivalent schema leftShape rightShape
      ↔ NormalForm.completeNormalOperationsEqualUpToReordering
          (NormalForm.completeNormalizeOperation schema left)
          (NormalForm.completeNormalizeOperation schema right) := by
  constructor
  · exact normalizedEqualUpToReordering_of_strictEquivalent schema left right
      leftShape rightShape hschema hleftValid hrightValid hleftCompute
      hrightCompute
  · exact strictEquivalent_of_normalizedEqualUpToReordering schema left right
      leftShape rightShape hschema hleftValid hrightValid hsupport hleftCompute
      hrightCompute

end ResponseShape

end GraphQL
