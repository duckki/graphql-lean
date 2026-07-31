import GraphQL.Theories.ResponseShape.Reification
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.Basics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Probes
import Proofs.GraphQL.Theories.NormalForm.SelectionReordering
import Proofs.GraphQL.Theories.ResponseShape.Compute.Totality
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.WrappedCaseBranches

/-!
Structural round-trip facts for reifying response shapes produced by the
complete-normal decoder.
-/

namespace GraphQL

namespace ResponseShape

private theorem reifyShapeDefinitions_append
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (responseName : Name) (left right : List ShapeDefinition) :
    reifyShapeDefinitions schema assignment responseName (left ++ right) =
      reifyShapeDefinitions schema assignment responseName left ++
        reifyShapeDefinitions schema assignment responseName right := by
  induction left with
  | nil => rfl
  | cons definition rest ih =>
      simp only [List.cons_append, reifyShapeDefinitions]
      rw [ih]
      split <;> simp

private theorem perm_append_middle
    {α : Type} (left middle right : List α) :
    (left ++ middle ++ right).Perm (left ++ right ++ middle) := by
  simpa only [List.append_assoc] using
    List.Perm.append_left left
      (List.perm_append_comm (l₁ := middle) (l₂ := right))

private theorem reifyPossibleDefinitions_insert_perm
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (responseName : Name)
    (incoming : PossibleDefinitions) :
    ∀ groups,
      (reifyPossibleDefinitions schema assignment objectType responseName
          (insertPossibleDefinitions incoming groups)).Perm
        (reifyPossibleDefinitions schema assignment objectType responseName groups ++
          incoming.reifyFields schema assignment objectType responseName)
  | [] => by
      simp [insertPossibleDefinitions, reifyPossibleDefinitions]
  | current :: rest => by
      unfold insertPossibleDefinitions
      by_cases heq : current.objectTypes = incoming.objectTypes
      · have hbeq : (current.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        rw [if_pos hbeq]
        cases current with
        | mk currentObjects currentDefinitions =>
            cases incoming with
            | mk incomingObjects incomingDefinitions =>
                simp only [PossibleDefinitions.objectTypes] at heq
                subst incomingObjects
                simp only [reifyPossibleDefinitions,
                  PossibleDefinitions.reifyFields]
                by_cases hmem : objectType ∈ currentObjects
                · simp only [PossibleDefinitions.objectTypes,
                    PossibleDefinitions.definitions]
                  simp [hmem, reifyShapeDefinitions_append]
                  simpa only [List.append_assoc] using
                    perm_append_middle
                      (reifyShapeDefinitions schema assignment responseName
                        currentDefinitions)
                      (reifyShapeDefinitions schema assignment responseName
                        incomingDefinitions)
                      (reifyPossibleDefinitions schema assignment objectType
                        responseName rest)
                · simp only [PossibleDefinitions.objectTypes,
                    PossibleDefinitions.definitions]
                  simp [hmem]
      · have hbeq : (current.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        rw [if_neg (by simpa using hbeq)]
        simp only [reifyPossibleDefinitions]
        simpa only [List.append_assoc] using
          List.Perm.append_left
            (current.reifyFields schema assignment objectType responseName)
            (reifyPossibleDefinitions_insert_perm schema assignment objectType
              responseName incoming rest)

private theorem reifyPossibleDefinitions_merge_perm
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (responseName : Name) :
    ∀ left right,
      (reifyPossibleDefinitions schema assignment objectType responseName
          (mergePossibleDefinitions left right)).Perm
        (reifyPossibleDefinitions schema assignment objectType responseName left ++
          reifyPossibleDefinitions schema assignment objectType responseName right)
  | left, [] => by simp [mergePossibleDefinitions, reifyPossibleDefinitions]
  | left, incoming :: rest => by
      unfold mergePossibleDefinitions
      rw [List.foldl_cons]
      exact
        (reifyPossibleDefinitions_merge_perm schema assignment objectType
          responseName (insertPossibleDefinitions incoming left) rest).trans
        (by
          simpa only [reifyPossibleDefinitions, List.append_assoc] using
            (reifyPossibleDefinitions_insert_perm schema assignment objectType
                responseName incoming left).append
              (List.Perm.refl
                (reifyPossibleDefinitions schema assignment objectType responseName
                  rest)))

private theorem reifyResponsePositions_insert_perm
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (incoming : ResponsePosition) :
    ∀ positions,
      (reifyResponsePositions schema assignment objectType
          (insertResponsePosition incoming positions)).Perm
        (reifyResponsePositions schema assignment objectType positions ++
          incoming.reifyFields schema assignment objectType)
  | [] => by simp [insertResponsePosition, reifyResponsePositions]
  | current :: rest => by
      unfold insertResponsePosition
      by_cases heq : current.responseName = incoming.responseName
      · have hbeq : (current.responseName == incoming.responseName) = true := by
          simp [heq]
        rw [if_pos hbeq]
        cases current with
        | mk currentName currentGroups =>
            cases incoming with
            | mk incomingName incomingGroups =>
                simp only [ResponsePosition.responseName] at heq
                subst incomingName
                simp only [reifyResponsePositions, ResponsePosition.reifyFields]
                exact
                  ((reifyPossibleDefinitions_merge_perm schema assignment objectType
                      currentName currentGroups incomingGroups).append
                    (List.Perm.refl
                      (reifyResponsePositions schema assignment objectType rest))).trans
                  (perm_append_middle
                    (reifyPossibleDefinitions schema assignment objectType
                      currentName currentGroups)
                    (reifyPossibleDefinitions schema assignment objectType
                      currentName incomingGroups)
                    (reifyResponsePositions schema assignment objectType rest))
      · have hbeq : (current.responseName == incoming.responseName) = false := by
          simp [heq]
        rw [if_neg (by simpa using hbeq)]
        simp only [reifyResponsePositions]
        simpa only [List.append_assoc] using
          List.Perm.append_left
            (current.reifyFields schema assignment objectType)
            (reifyResponsePositions_insert_perm schema assignment objectType
              incoming rest)

private theorem reifyResponsePositions_fold_perm
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) :
    ∀ incoming current,
      (reifyResponsePositions schema assignment objectType
          (incoming.foldl
            (fun merged position => insertResponsePosition position merged)
            current)).Perm
        (reifyResponsePositions schema assignment objectType current ++
          reifyResponsePositions schema assignment objectType incoming)
  | [], current => by simp [reifyResponsePositions]
  | position :: rest, current => by
      rw [List.foldl_cons]
      exact
        (reifyResponsePositions_fold_perm schema assignment objectType rest
          (insertResponsePosition position current)).trans
        (by
          simpa only [reifyResponsePositions, List.append_assoc] using
            (reifyResponsePositions_insert_perm schema assignment objectType
                position current).append
              (List.Perm.refl
                (reifyResponsePositions schema assignment objectType rest)))

/-- Merging shapes at one concrete object only reorders their reified fields. -/
private theorem reifyResponsePositions_mergeResponseShapes_perm
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (left right : ResponseShape) :
    (reifyResponsePositions schema assignment objectType
        (mergeResponseShapes left right).positions).Perm
      (reifyResponsePositions schema assignment objectType left.positions ++
        reifyResponsePositions schema assignment objectType right.positions) := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          exact reifyResponsePositions_fold_perm schema assignment objectType
            rightPositions leftPositions

private theorem reifySelectionSet_merge_perm_of_object
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (left right : ResponseShape)
    (hobject : NormalForm.objectTypeNameBool schema parentType = true) :
    ((mergeResponseShapes left right).reifySelectionSet
        schema assignment parentType).Perm
      (left.reifySelectionSet schema assignment parentType ++
        right.reifySelectionSet schema assignment parentType) := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold ResponseShape.reifySelectionSet
          simp only [hobject, if_true]
          exact reifyResponsePositions_fold_perm schema assignment parentType
            rightPositions leftPositions

mutual
  private theorem selectionEqualUpToReordering_refl
      : ∀ selection, NormalForm.SelectionEqualUpToReordering selection selection
    | .field responseName fieldName arguments directives selectionSet =>
        .field responseName fieldName directives
          (NormalForm.GroundTypeNormalization.argumentsEquivalent_refl arguments)
          (selectionSetEqualUpToReordering_refl selectionSet)
    | .inlineFragment typeCondition directives selectionSet =>
        .inlineFragment typeCondition directives
          (selectionSetEqualUpToReordering_refl selectionSet)

  private theorem selectionSetEqualUpToReordering_refl
      : ∀ selectionSet,
          NormalForm.SelectionSetEqualUpToReordering selectionSet selectionSet
    | [] =>
        .paired [] List.Perm.nil List.Perm.nil
          (by intro pair hpair; simp at hpair)
    | selection :: rest => by
        rcases selectionSetEqualUpToReordering_refl rest with
          ⟨pairs, hleft, hright, hrelations⟩
        exact .paired ((selection, selection) :: pairs)
          (hleft.cons selection) (hright.cons selection)
          (by
            intro pair hpair
            rcases List.mem_cons.mp hpair with hhead | htail
            · subst pair
              exact selectionEqualUpToReordering_refl selection
            · exact hrelations pair htail)
end

private theorem selectionSetEqualUpToReordering_of_perm
    {left right : List Selection} (hperm : left.Perm right) :
    NormalForm.SelectionSetEqualUpToReordering left right := by
  rcases selectionSetEqualUpToReordering_refl right with
    ⟨pairs, hleft, hright, hrelations⟩
  exact .paired pairs (hleft.trans hperm.symm) hright hrelations

private theorem selectionSetEqualUpToReordering_perm_left
    {source left right : List Selection}
    (hperm : source.Perm left)
    (hequal : NormalForm.SelectionSetEqualUpToReordering source right) :
    NormalForm.SelectionSetEqualUpToReordering left right := by
  rcases hequal with ⟨pairs, hpairsLeft, hpairsRight, hrelations⟩
  exact .paired pairs (hpairsLeft.trans hperm) hpairsRight hrelations

private theorem selectionSetEqualUpToReordering_perm_right
    {source left right : List Selection}
    (hequal : NormalForm.SelectionSetEqualUpToReordering left source)
    (hperm : source.Perm right) :
    NormalForm.SelectionSetEqualUpToReordering left right := by
  rcases hequal with ⟨pairs, hpairsLeft, hpairsRight, hrelations⟩
  exact .paired pairs hpairsLeft (hpairsRight.trans hperm) hrelations

private theorem selectionSetEqualUpToReordering_length_eq
    {left right : List Selection}
    (hequal : NormalForm.SelectionSetEqualUpToReordering left right) :
    left.length = right.length := by
  rcases hequal with ⟨pairs, hleft, hright, _hrelations⟩
  calc
    left.length = pairs.length := by simpa using hleft.length_eq.symm
    _ = right.length := by simpa using hright.length_eq

private theorem selectionSetEqualUpToReordering_append
    {left₁ right₁ left₂ right₂ : List Selection}
    (hfirst : NormalForm.SelectionSetEqualUpToReordering left₁ right₁)
    (hsecond : NormalForm.SelectionSetEqualUpToReordering left₂ right₂) :
    NormalForm.SelectionSetEqualUpToReordering
      (left₁ ++ left₂) (right₁ ++ right₂) := by
  rcases hfirst with ⟨firstPairs, hfirstLeft, hfirstRight, hfirstRelations⟩
  rcases hsecond with
    ⟨secondPairs, hsecondLeft, hsecondRight, hsecondRelations⟩
  exact .paired (firstPairs ++ secondPairs)
    (by simpa using hfirstLeft.append hsecondLeft)
    (by simpa using hfirstRight.append hsecondRight)
    (by
      intro pair hpair
      rcases List.mem_append.mp hpair with hmem | hmem
      · exact hfirstRelations pair hmem
      · exact hsecondRelations pair hmem)

private theorem selectionSetEqualUpToReordering_cons
    {left right : Selection} {leftRest rightRest : List Selection}
    (hhead : NormalForm.SelectionEqualUpToReordering left right)
    (hrest : NormalForm.SelectionSetEqualUpToReordering leftRest rightRest) :
    NormalForm.SelectionSetEqualUpToReordering
      (left :: leftRest) (right :: rightRest) := by
  rcases hrest with ⟨pairs, hleft, hright, hrelations⟩
  exact .paired ((left, right) :: pairs) (hleft.cons left) (hright.cons right)
    (by
      intro pair hpair
      rcases List.mem_cons.mp hpair with hfirst | htail
      · subst pair
        exact hhead
      · exact hrelations pair htail)

private theorem reifyShapeDefinitions_eq_nil_of_uniform_inactive
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (responseName : Name) (clause : Clause) :
    ∀ definitions,
      (∀ definition ∈ definitions, definition.clause = clause) ->
      clause.holdsInBool assignment = false ->
      reifyShapeDefinitions schema assignment responseName definitions = []
  | [], _huniform, _hinactive => rfl
  | definition :: rest, huniform, hinactive => by
      have hdefinition := huniform definition (by simp)
      have hrest : ∀ candidate ∈ rest, candidate.clause = clause := by
        intro candidate hcandidate
        exact huniform candidate (List.mem_cons_of_mem definition hcandidate)
      simp [reifyShapeDefinitions, hdefinition, hinactive,
        reifyShapeDefinitions_eq_nil_of_uniform_inactive schema assignment
          responseName clause rest hrest hinactive]

private theorem reifyPossibleDefinitions_eq_nil_of_uniform_inactive
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (responseName : Name) (clause : Clause) :
    ∀ groups,
      (∀ group ∈ groups,
        ∀ definition ∈ group.definitions, definition.clause = clause) ->
      clause.holdsInBool assignment = false ->
      reifyPossibleDefinitions schema assignment objectType responseName groups = []
  | [], _huniform, _hinactive => rfl
  | group :: rest, huniform, hinactive => by
      have hgroup : ∀ definition ∈ group.definitions,
          definition.clause = clause :=
        huniform group (by simp)
      have hrest : ∀ candidate ∈ rest,
          ∀ definition ∈ candidate.definitions,
            definition.clause = clause := by
        intro candidate hcandidate
        exact huniform candidate (List.mem_cons_of_mem group hcandidate)
      cases group with
      | mk objectTypes definitions =>
          simp only [reifyPossibleDefinitions,
            PossibleDefinitions.reifyFields]
          by_cases hmem : objectType ∈ objectTypes
          · simp [hmem,
              reifyShapeDefinitions_eq_nil_of_uniform_inactive schema assignment
                responseName clause definitions hgroup hinactive,
              reifyPossibleDefinitions_eq_nil_of_uniform_inactive schema assignment
                objectType responseName clause rest hrest hinactive]
          · simp [hmem,
              reifyPossibleDefinitions_eq_nil_of_uniform_inactive schema assignment
                objectType responseName clause rest hrest hinactive]

private theorem reifyResponsePositions_eq_nil_of_uniform_inactive
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (clause : Clause) :
    ∀ positions,
      (∀ position ∈ positions,
        ∀ group ∈ position.possibleDefinitions,
          ∀ definition ∈ group.definitions, definition.clause = clause) ->
      clause.holdsInBool assignment = false ->
      reifyResponsePositions schema assignment objectType positions = []
  | [], _huniform, _hinactive => rfl
  | position :: rest, huniform, hinactive => by
      have hposition : ∀ group ∈ position.possibleDefinitions,
          ∀ definition ∈ group.definitions,
            definition.clause = clause :=
        huniform position (by simp)
      have hrest : ∀ candidate ∈ rest,
          ∀ group ∈ candidate.possibleDefinitions,
            ∀ definition ∈ group.definitions,
              definition.clause = clause := by
        intro candidate hcandidate
        exact huniform candidate (List.mem_cons_of_mem position hcandidate)
      cases position with
      | mk responseName groups =>
          simp [reifyResponsePositions, ResponsePosition.reifyFields,
            reifyPossibleDefinitions_eq_nil_of_uniform_inactive schema assignment
              objectType responseName clause groups hposition hinactive,
            reifyResponsePositions_eq_nil_of_uniform_inactive schema assignment
              objectType clause rest hrest hinactive]

private theorem reifySelectionSet_eq_nil_of_uniform_inactive
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (shape : ResponseShape) (clause : Clause)
    (huniform : ShapeClausesEqual clause shape)
    (hinactive : clause.holdsInBool assignment = false) :
    shape.reifySelectionSet schema assignment parentType = [] := by
  cases shape with
  | object positions =>
      have hpositions : ∀ objectType,
          reifyResponsePositions schema assignment objectType positions = [] := by
        intro objectType
        exact reifyResponsePositions_eq_nil_of_uniform_inactive schema assignment
          objectType clause positions huniform hinactive
      unfold ResponseShape.reifySelectionSet
      split
      · exact hpositions parentType
      · simp [hpositions]

private theorem reifyPossibleDefinitions_eq_nil_of_object_not_in
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (responseName : Name)
    (allowed : List GroundObject) :
    ∀ groups,
      (∀ group ∈ groups,
        ∀ candidate ∈ group.objectTypes, candidate ∈ allowed) ->
      objectType ∉ allowed ->
      reifyPossibleDefinitions schema assignment objectType responseName groups = []
  | [], _hkeys, _hnotAllowed => rfl
  | group :: rest, hkeys, hnotAllowed => by
      have hgroup : ∀ candidate ∈ group.objectTypes, candidate ∈ allowed :=
        hkeys group (by simp)
      have hnotGroup : objectType ∉ group.objectTypes := by
        intro hmem
        exact hnotAllowed (hgroup objectType hmem)
      have hrest : ∀ candidateGroup ∈ rest,
          ∀ candidate ∈ candidateGroup.objectTypes, candidate ∈ allowed := by
        intro candidateGroup hcandidate
        exact hkeys candidateGroup (List.mem_cons_of_mem group hcandidate)
      cases group with
      | mk objectTypes definitions =>
          have hnotObjects : objectType ∉ objectTypes := by
            simpa only [PossibleDefinitions.objectTypes] using hnotGroup
          simp [reifyPossibleDefinitions, PossibleDefinitions.reifyFields,
            hnotObjects,
            reifyPossibleDefinitions_eq_nil_of_object_not_in schema assignment
              objectType responseName allowed rest hrest hnotAllowed]

private theorem reifyResponsePositions_eq_nil_of_object_not_in_raw
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (allowed : List GroundObject) :
    ∀ positions,
      (∀ position ∈ positions,
        ∀ group ∈ position.possibleDefinitions,
          ∀ candidate ∈ group.objectTypes, candidate ∈ allowed) ->
      objectType ∉ allowed ->
      reifyResponsePositions schema assignment objectType positions = []
  | [], _hkeys, _hnotAllowed => rfl
  | position :: rest, hkeys, hnotAllowed => by
      have hposition : ∀ group ∈ position.possibleDefinitions,
          ∀ candidate ∈ group.objectTypes, candidate ∈ allowed :=
        hkeys position List.mem_cons_self
      have hrest : ∀ candidatePosition ∈ rest,
          ∀ group ∈ candidatePosition.possibleDefinitions,
            ∀ candidate ∈ group.objectTypes, candidate ∈ allowed := by
        intro candidatePosition hcandidate
        exact hkeys candidatePosition
          (List.mem_cons_of_mem position hcandidate)
      cases position with
      | mk responseName groups =>
          simp [reifyResponsePositions, ResponsePosition.reifyFields,
            reifyPossibleDefinitions_eq_nil_of_object_not_in schema assignment
              objectType responseName allowed groups hposition hnotAllowed,
            reifyResponsePositions_eq_nil_of_object_not_in_raw schema assignment
              objectType allowed rest hrest hnotAllowed]

private theorem reifyResponsePositions_eq_nil_of_object_not_in
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (objectType : GroundObject) (allowed : List GroundObject)
    (shape : ResponseShape)
    (hkeys : ShapeObjectTypesIn allowed shape)
    (hnotAllowed : objectType ∉ allowed) :
    reifyResponsePositions schema assignment objectType shape.positions = [] := by
  exact reifyResponsePositions_eq_nil_of_object_not_in_raw schema assignment
    objectType allowed shape.positions hkeys hnotAllowed

private def reifyObjectFragment
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (shape : ResponseShape) (objectType : GroundObject) : Option Selection :=
  match shape with
  | .object positions =>
      match reifyResponsePositions schema assignment objectType positions with
      | [] => none
      | selections =>
          some (.inlineFragment (some objectType) [] selections)

private theorem reifyObjectFragment_eq_none
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (shape : ResponseShape) (objectType : GroundObject)
    (hempty : reifyResponsePositions schema assignment objectType
      shape.positions = []) :
    reifyObjectFragment schema assignment shape objectType = none := by
  cases shape with
  | object positions =>
      change reifyResponsePositions schema assignment objectType positions = []
        at hempty
      simp [reifyObjectFragment, hempty]

private theorem reifyObjectFragment_eq_some
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (shape : ResponseShape) (objectType : GroundObject)
    (head : Selection) (tail : List Selection)
    (hnonempty : reifyResponsePositions schema assignment objectType
      shape.positions = head :: tail) :
    reifyObjectFragment schema assignment shape objectType =
      some (.inlineFragment (some objectType) [] (head :: tail)) := by
  cases shape with
  | object positions =>
      change reifyResponsePositions schema assignment objectType positions =
        head :: tail at hnonempty
      simp [reifyObjectFragment, hnonempty]

private theorem reifyObjectFragments_merge_without_focus
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (focus : GroundObject) (left right : ResponseShape)
    (hleftKeys : ShapeObjectTypesIn [focus] left) :
    ∀ candidates : List GroundObject,
      focus ∉ candidates ->
      NormalForm.SelectionSetEqualUpToReordering
        (candidates.filterMap
          (reifyObjectFragment schema assignment
            (mergeResponseShapes left right)))
        (candidates.filterMap
          (reifyObjectFragment schema assignment right))
  | [], _hfocus => selectionSetEqualUpToReordering_refl []
  | candidate :: rest, hfocus => by
      have hcandidate : candidate ≠ focus := by
        intro heq
        exact hfocus (by simp [heq])
      have hrest : focus ∉ rest := by
        intro hmem
        exact hfocus (List.mem_cons_of_mem candidate hmem)
      have hleftEmpty :
          reifyResponsePositions schema assignment candidate left.positions = [] :=
        reifyResponsePositions_eq_nil_of_object_not_in schema assignment
          candidate [focus] left hleftKeys (by simp [hcandidate])
      have hperm :
          (reifyResponsePositions schema assignment candidate
              (mergeResponseShapes left right).positions).Perm
            (reifyResponsePositions schema assignment candidate right.positions) := by
        simpa [hleftEmpty] using
          reifyResponsePositions_mergeResponseShapes_perm schema assignment
            candidate left right
      have ih := reifyObjectFragments_merge_without_focus schema assignment
        focus left right hleftKeys rest hrest
      cases hmerged :
          reifyResponsePositions schema assignment candidate
            (mergeResponseShapes left right).positions with
      | nil =>
          cases hright :
              reifyResponsePositions schema assignment candidate right.positions with
          | nil =>
              rw [List.filterMap_cons, List.filterMap_cons,
                reifyObjectFragment_eq_none schema assignment
                  (mergeResponseShapes left right) candidate hmerged,
                reifyObjectFragment_eq_none schema assignment right candidate
                  hright]
              exact ih
          | cons head tail =>
              have hlength := hperm.length_eq
              simp [hmerged, hright] at hlength
      | cons mergedHead mergedTail =>
          cases hright :
              reifyResponsePositions schema assignment candidate right.positions with
          | nil =>
              have hlength := hperm.length_eq
              simp [hmerged, hright] at hlength
          | cons rightHead rightTail =>
              have hbody : NormalForm.SelectionSetEqualUpToReordering
                  (mergedHead :: mergedTail) (rightHead :: rightTail) :=
                selectionSetEqualUpToReordering_of_perm (by
                  simpa [hmerged, hright] using hperm)
              have hhead : NormalForm.SelectionEqualUpToReordering
                  (.inlineFragment (some candidate) []
                    (mergedHead :: mergedTail))
                  (.inlineFragment (some candidate) []
                    (rightHead :: rightTail)) :=
                .inlineFragment (some candidate) [] hbody
              rw [List.filterMap_cons, List.filterMap_cons,
                reifyObjectFragment_eq_some schema assignment
                  (mergeResponseShapes left right) candidate mergedHead mergedTail
                  hmerged,
                reifyObjectFragment_eq_some schema assignment right candidate
                  rightHead rightTail hright]
              exact selectionSetEqualUpToReordering_cons hhead ih

private theorem reifyObjectFragment_merge_focus
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (focus : GroundObject) (left right : ResponseShape)
    (rightAllowed : List GroundObject)
    (hrightKeys : ShapeObjectTypesIn rightAllowed right)
    (hfocusNotRight : focus ∉ rightAllowed)
    (body : List Selection)
    (hleftBody : NormalForm.SelectionSetEqualUpToReordering
      (reifyResponsePositions schema assignment focus left.positions) body)
    (hbodyNonempty : body ≠ []) :
    NormalForm.SelectionSetEqualUpToReordering
      ([focus].filterMap
        (reifyObjectFragment schema assignment
          (mergeResponseShapes left right)))
      [.inlineFragment (some focus) [] body] := by
  have hrightEmpty :
      reifyResponsePositions schema assignment focus right.positions = [] :=
    reifyResponsePositions_eq_nil_of_object_not_in schema assignment focus
      rightAllowed right hrightKeys hfocusNotRight
  have hperm :
      (reifyResponsePositions schema assignment focus
          (mergeResponseShapes left right).positions).Perm
        (reifyResponsePositions schema assignment focus left.positions) := by
    simpa [hrightEmpty] using
      reifyResponsePositions_mergeResponseShapes_perm schema assignment
        focus left right
  have hleftNonempty :
      reifyResponsePositions schema assignment focus left.positions ≠ [] := by
    intro hempty
    have hlength := selectionSetEqualUpToReordering_length_eq hleftBody
    rw [hempty] at hlength
    apply hbodyNonempty
    exact List.length_eq_zero_iff.mp hlength.symm
  cases hmerged :
      reifyResponsePositions schema assignment focus
        (mergeResponseShapes left right).positions with
  | nil =>
      have hleftEmpty :
          reifyResponsePositions schema assignment focus left.positions = [] := by
        have hlength := hperm.length_eq
        rw [hmerged] at hlength
        exact List.length_eq_zero_iff.mp hlength.symm
      exact (hleftNonempty hleftEmpty).elim
  | cons head tail =>
      have hmergedBody : NormalForm.SelectionSetEqualUpToReordering
          (head :: tail) body :=
        selectionSetEqualUpToReordering_perm_left
          (by simpa [hmerged] using hperm.symm) hleftBody
      have hfragment : NormalForm.SelectionEqualUpToReordering
          (.inlineFragment (some focus) [] (head :: tail))
          (.inlineFragment (some focus) [] body) :=
        .inlineFragment (some focus) [] hmergedBody
      rw [List.filterMap_cons, List.filterMap_nil,
        reifyObjectFragment_eq_some schema assignment
          (mergeResponseShapes left right) focus head tail hmerged]
      exact selectionSetEqualUpToReordering_cons hfragment
        (selectionSetEqualUpToReordering_refl [])

private theorem abstractType_objectTypeNameBool_eq_false
    (schema : Schema) (parentType : Name)
    (habstract : AbstractType schema parentType) :
    NormalForm.objectTypeNameBool schema parentType = false := by
  rcases habstract with ⟨interfaceType, hlookup⟩ |
      ⟨unionType, hlookup⟩ <;>
    simp [NormalForm.objectTypeNameBool, hlookup]

private theorem reifySelectionSet_abstract_merge_cons
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (assignment : NormalForm.BoolCase) (parentType focus : Name)
    (body : List Selection) (left right : ResponseShape)
    (rightAllowed : List GroundObject)
    (habstract : AbstractType schema parentType)
    (hincludes : schema.typeIncludesObjectBool parentType focus = true)
    (hleftKeys : ShapeObjectTypesIn [focus] left)
    (hrightKeys : ShapeObjectTypesIn rightAllowed right)
    (hfocusNotRight : focus ∉ rightAllowed)
    (hleftBody : NormalForm.SelectionSetEqualUpToReordering
      (reifyResponsePositions schema assignment focus left.positions) body)
    (hbodyNonempty : body ≠ []) :
    NormalForm.SelectionSetEqualUpToReordering
      ((mergeResponseShapes left right).reifySelectionSet
        schema assignment parentType)
      (.inlineFragment (some focus) [] body ::
        right.reifySelectionSet schema assignment parentType) := by
  let possibleTypes := schema.getPossibleTypes parentType
  have hfocusMem : focus ∈ possibleTypes := by
    simpa [possibleTypes, Schema.typeIncludesObjectBool] using
      List.contains_iff_mem.mp hincludes
  rcases List.mem_iff_append.mp hfocusMem with
    ⟨before, after, hpossible⟩
  have hpossibleNodup : possibleTypes.Nodup := by
    exact SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
      hschema parentType
  have hsplitNodup : (before ++ focus :: after).Nodup := by
    rw [← hpossible]
    exact hpossibleNodup
  have hfocusNotBefore : focus ∉ before := by
    intro hmem
    exact ((List.nodup_append.mp hsplitNodup).2.2 focus hmem focus
      List.mem_cons_self) rfl
  have hfocusNotAfter : focus ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp hsplitNodup).2.1).1
  have hbefore := reifyObjectFragments_merge_without_focus schema assignment
    focus left right hleftKeys before hfocusNotBefore
  have hfocus := reifyObjectFragment_merge_focus schema assignment focus
    left right rightAllowed hrightKeys hfocusNotRight body hleftBody
    hbodyNonempty
  have hafter := reifyObjectFragments_merge_without_focus schema assignment
    focus left right hleftKeys after hfocusNotAfter
  have hcombined := selectionSetEqualUpToReordering_append
    (selectionSetEqualUpToReordering_append hbefore hfocus) hafter
  let focusSelection : Selection := .inlineFragment (some focus) [] body
  have hrightPermutation :
      (before.filterMap (reifyObjectFragment schema assignment right) ++
          [focusSelection] ++
          after.filterMap (reifyObjectFragment schema assignment right)).Perm
        (focusSelection ::
          (before.filterMap (reifyObjectFragment schema assignment right) ++
            after.filterMap (reifyObjectFragment schema assignment right))) := by
    have hperm := (List.perm_append_comm
      (l₁ := before.filterMap
        (reifyObjectFragment schema assignment right))
      (l₂ := [focusSelection])).append_right
        (after.filterMap (reifyObjectFragment schema assignment right))
    have hrightEq :
        ([focusSelection] ++
            before.filterMap (reifyObjectFragment schema assignment right)) ++
            after.filterMap (reifyObjectFragment schema assignment right) =
          focusSelection ::
            (before.filterMap (reifyObjectFragment schema assignment right) ++
              after.filterMap (reifyObjectFragment schema assignment right)) := by
      simp
    exact hperm.trans (List.Perm.of_eq hrightEq)
  have hreordered := selectionSetEqualUpToReordering_perm_right hcombined
    hrightPermutation
  have hparentFalse :=
    abstractType_objectTypeNameBool_eq_false schema parentType habstract
  have hrightFocusEmpty :
      reifyResponsePositions schema assignment focus right.positions = [] :=
    reifyResponsePositions_eq_nil_of_object_not_in schema assignment focus
      rightAllowed right hrightKeys hfocusNotRight
  have hmergedReify :
      (mergeResponseShapes left right).reifySelectionSet
          schema assignment parentType =
        (schema.getPossibleTypes parentType).filterMap
          (reifyObjectFragment schema assignment
            (mergeResponseShapes left right)) := by
    cases left with
    | object leftPositions =>
        cases right with
        | object rightPositions =>
            unfold mergeResponseShapes
            unfold ResponseShape.reifySelectionSet
            rw [hparentFalse]
            simp only [Bool.false_eq_true, if_false]
            unfold reifyObjectFragment
            rfl
  have hrightReify :
      right.reifySelectionSet schema assignment parentType =
        (schema.getPossibleTypes parentType).filterMap
          (reifyObjectFragment schema assignment right) := by
    cases right with
    | object positions =>
        unfold ResponseShape.reifySelectionSet
        rw [hparentFalse]
        simp only [Bool.false_eq_true, if_false]
        unfold reifyObjectFragment
        rfl
  dsimp [possibleTypes] at hpossible
  have hpossible' : schema.getPossibleTypes parentType =
      before ++ [focus] ++ after := by
    simpa [List.append_assoc] using hpossible
  rw [hmergedReify, hrightReify, hpossible']
  have hmergedSplit :
      (before ++ [focus] ++ after).filterMap
          (reifyObjectFragment schema assignment
            (mergeResponseShapes left right)) =
        before.filterMap
            (reifyObjectFragment schema assignment
              (mergeResponseShapes left right)) ++
          [focus].filterMap
            (reifyObjectFragment schema assignment
              (mergeResponseShapes left right)) ++
          after.filterMap
            (reifyObjectFragment schema assignment
              (mergeResponseShapes left right)) := by
    let reifyMerged := reifyObjectFragment schema assignment
      (mergeResponseShapes left right)
    calc
      (before ++ [focus] ++ after).filterMap reifyMerged =
          (before ++ [focus]).filterMap reifyMerged ++
            after.filterMap reifyMerged := by
              exact List.filterMap_append
      _ = (before.filterMap reifyMerged ++
            [focus].filterMap reifyMerged) ++
            after.filterMap reifyMerged := by
              rw [List.filterMap_append]
      _ = before.filterMap reifyMerged ++
            [focus].filterMap reifyMerged ++
            after.filterMap reifyMerged := by
              rw [List.append_assoc]
  have hrightFocusOption :
      reifyObjectFragment schema assignment right focus = none :=
    reifyObjectFragment_eq_none schema assignment right focus
      hrightFocusEmpty
  have hrightSplit :
      (before ++ [focus] ++ after).filterMap
          (reifyObjectFragment schema assignment right) =
        before.filterMap (reifyObjectFragment schema assignment right) ++
          after.filterMap (reifyObjectFragment schema assignment right) := by
    simp [List.filterMap_append, hrightFocusOption, List.append_assoc]
  rw [hmergedSplit, hrightSplit]
  simpa [focusSelection] using hreordered

private theorem selectionHasResponseName_any_eq_false
    (responseName : Name) : ∀ selectionSet : List Selection,
      responseName ∉ selectionSet.filterMap Selection.responseName? ->
      selectionSet.any (selectionHasResponseName responseName) = false
  | [], _hnot => rfl
  | selection :: rest, hnot => by
      have hrest : responseName ∉ rest.filterMap Selection.responseName? := by
        intro hmem
        apply hnot
        rw [List.mem_filterMap] at hmem ⊢
        rcases hmem with ⟨candidate, hcandidate, heq⟩
        exact ⟨candidate, List.mem_cons_of_mem selection hcandidate, heq⟩
      cases selection with
      | field candidate fieldName arguments directives child =>
          have hne : candidate ≠ responseName := by
            intro heq
            apply hnot
            simp [Selection.responseName?, heq]
          simp [selectionHasResponseName, hne,
            selectionHasResponseName_any_eq_false responseName rest hrest]
      | inlineFragment typeCondition directives child =>
          simp [selectionHasResponseName,
            selectionHasResponseName_any_eq_false responseName rest hrest]

private theorem selectionHasTypeCondition_any_eq_false
    (typeCondition : Name) : ∀ selectionSet : List Selection,
      typeCondition ∉
        selectionSet.filterMap NormalForm.inlineFragmentTypeCondition? ->
      selectionSet.any (selectionHasTypeCondition typeCondition) = false
  | [], _hnot => rfl
  | selection :: rest, hnot => by
      have hrest : typeCondition ∉
          rest.filterMap NormalForm.inlineFragmentTypeCondition? := by
        intro hmem
        apply hnot
        rw [List.mem_filterMap] at hmem ⊢
        rcases hmem with ⟨candidate, hcandidate, heq⟩
        exact ⟨candidate, List.mem_cons_of_mem selection hcandidate, heq⟩
      cases selection with
      | field responseName fieldName arguments directives child =>
          simp [selectionHasTypeCondition,
            selectionHasTypeCondition_any_eq_false typeCondition rest hrest]
      | inlineFragment condition directives child =>
          cases condition with
          | none =>
              simp [selectionHasTypeCondition,
                selectionHasTypeCondition_any_eq_false typeCondition rest hrest]
          | some candidate =>
              have hne : candidate ≠ typeCondition := by
                intro heq
                apply hnot
                simp [NormalForm.inlineFragmentTypeCondition?, heq]
              simp [selectionHasTypeCondition, hne,
                selectionHasTypeCondition_any_eq_false typeCondition rest hrest]

private theorem reify_singletonDefinitionShape_object_active
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType responseName : Name) (definition : ShapeDefinition)
    (hobject : NormalForm.objectTypeNameBool schema parentType = true)
    (hactive : definition.clause.holdsInBool assignment = true) :
    (singletonDefinitionShape parentType responseName definition).reifySelectionSet
        schema assignment parentType =
      [definition.reifyField schema assignment responseName] := by
  cases definition with
  | mk clause field subshape =>
      simp [singletonDefinitionShape, ResponseShape.reifySelectionSet, hobject,
        reifyResponsePositions, ResponsePosition.reifyFields,
        reifyPossibleDefinitions, PossibleDefinitions.reifyFields,
        reifyShapeDefinitions, ShapeDefinition.clause] at hactive ⊢
      exact hactive

private theorem foldGroundSelectionSet_reify_active
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List NormalForm.BoolVar) (clause : Clause)
    (hvalid : clause.Valid support) (hcomplete : clause.CompleteMinterm support)
    (assignment : NormalForm.BoolCase)
    (hactive : clause.holdsInBool assignment = true)
    {parentType : Name} {selectionSet : List Selection}
    (himage : GroundSelectionSetImage schema parentType selectionSet) :
    ∀ shape,
      foldGroundSelectionSet schema clause parentType selectionSet = .ok shape ->
      NormalForm.SelectionSetEqualUpToReordering
        (shape.reifySelectionSet schema assignment parentType) selectionSet := by
  intro shape hfold
  induction himage using GroundSelectionSetImage.rec
      (motive_2 := fun fieldDefinition childSelectionSet _hchild =>
        ∀ childShape,
          foldGroundSelectionSet schema clause
              fieldDefinition.outputType.namedType childSelectionSet =
            .ok childShape ->
          NormalForm.SelectionSetEqualUpToReordering
            (childShape.reifySelectionSet schema assignment
              fieldDefinition.outputType.namedType)
            childSelectionSet)
      generalizing shape with
  | @objectNil decodedParent hobject =>
      rcases hobject with ⟨objectDefinition, hlookup⟩
      have hshape : shape = .object [] := by
        have hfold' :
            (Except.ok (.object []) : Except ShapeBuildError ResponseShape) =
              Except.ok shape := by
          simpa [foldGroundSelectionSet, NormalForm.objectTypeNameBool,
            hlookup] using hfold
        exact (Except.ok.inj hfold').symm
      subst shape
      simpa [ResponseShape.reifySelectionSet,
        NormalForm.objectTypeNameBool, hlookup, reifyResponsePositions] using
        selectionSetEqualUpToReordering_refl []
  | @objectField decodedParent responseName fieldName arguments fieldDefinition
      childSelectionSet rest hobject hlookup hresponseName hchild hrest
      ihchild ihrest =>
      rcases hobject with ⟨parentObject, hparentLookup⟩
      have hparentBool :
          NormalForm.objectTypeNameBool schema decodedParent = true := by
        simp [NormalForm.objectTypeNameBool, hparentLookup]
      have hduplicate : rest.any (selectionHasResponseName responseName) = false :=
        selectionHasResponseName_any_eq_false responseName rest hresponseName
      cases hchild with
      | composite hcomposite hselection =>
          cases hchildFold : foldGroundSelectionSet schema clause
              fieldDefinition.outputType.namedType childSelectionSet with
          | error error =>
              simp [foldGroundSelectionSet, Bind.bind, Except.bind, hparentBool,
                hduplicate, hlookup, hcomposite, hchildFold] at hfold
          | ok childShape =>
              cases hrestFold : foldGroundSelectionSet schema clause decodedParent
                  rest with
              | error error =>
                  simp [foldGroundSelectionSet, Bind.bind, Except.bind,
                    hparentBool, hduplicate, hlookup, hcomposite, hchildFold,
                    hrestFold] at hfold
              | ok restShape =>
                  let fieldHead : FieldHead :=
                    { fieldName := fieldName, arguments := arguments,
                      outputType := fieldDefinition.outputType }
                  let definition : ShapeDefinition :=
                    .mk clause fieldHead (some childShape)
                  let currentShape := singletonDefinitionShape decodedParent
                    responseName definition
                  have hfold' :
                      (Except.ok (mergeResponseShapes currentShape restShape) :
                          Except ShapeBuildError ResponseShape) = Except.ok shape := by
                    simpa [foldGroundSelectionSet, Bind.bind, Except.bind,
                      hparentBool, hduplicate, hlookup, hcomposite, hchildFold, hrestFold,
                      currentShape, definition, fieldHead] using hfold
                  have hshape : shape =
                      mergeResponseShapes currentShape restShape :=
                    (Except.ok.inj hfold').symm
                  subst shape
                  have hchildRelation := ihchild childShape hchildFold
                  have hrestRelation := ihrest restShape hrestFold
                  have hcurrent : currentShape.reifySelectionSet
                      schema assignment decodedParent =
                        [.field responseName fieldName arguments []
                          (childShape.reifySelectionSet schema assignment
                            fieldDefinition.outputType.namedType)] := by
                    rw [reify_singletonDefinitionShape_object_active schema
                      assignment decodedParent responseName definition hparentBool
                      (by simpa [definition, ShapeDefinition.clause] using hactive)]
                    rfl
                  have hfield : NormalForm.SelectionEqualUpToReordering
                      (.field responseName fieldName arguments []
                        (childShape.reifySelectionSet schema assignment
                          fieldDefinition.outputType.namedType))
                      (.field responseName fieldName arguments []
                        childSelectionSet) :=
                    .field responseName fieldName []
                      (NormalForm.GroundTypeNormalization.argumentsEquivalent_refl
                        arguments)
                      hchildRelation
                  have hcurrentRelation :
                      NormalForm.SelectionSetEqualUpToReordering
                        (currentShape.reifySelectionSet schema assignment
                          decodedParent)
                        [.field responseName fieldName arguments []
                          childSelectionSet] := by
                    rw [hcurrent]
                    exact selectionSetEqualUpToReordering_cons hfield
                      (selectionSetEqualUpToReordering_refl [])
                  have happend := selectionSetEqualUpToReordering_append
                    hcurrentRelation hrestRelation
                  exact selectionSetEqualUpToReordering_perm_left
                    (reifySelectionSet_merge_perm_of_object schema assignment
                      decodedParent currentShape restShape hparentBool).symm
                    happend
      | leaf hleaf =>
          have hcompositeFalse :
              fieldDefinition.outputType.isCompositeBool schema = false := by
            unfold NormalForm.leafTypeNameBool at hleaf
            unfold TypeRef.isCompositeBool
            cases htype : schema.lookupType fieldDefinition.outputType.namedType with
            | none => simp [htype] at hleaf
            | some typeDefinition =>
                cases typeDefinition <;> simp_all
          cases hrestFold : foldGroundSelectionSet schema clause decodedParent rest with
          | error error =>
              simp [foldGroundSelectionSet, Bind.bind, Except.bind, hparentBool,
                hduplicate, hlookup, hcompositeFalse, hleaf, hrestFold] at hfold
          | ok restShape =>
              let fieldHead : FieldHead :=
                { fieldName := fieldName, arguments := arguments,
                  outputType := fieldDefinition.outputType }
              let definition : ShapeDefinition := .mk clause fieldHead none
              let currentShape := singletonDefinitionShape decodedParent
                responseName definition
              have hfold' :
                  (Except.ok (mergeResponseShapes currentShape restShape) :
                      Except ShapeBuildError ResponseShape) = Except.ok shape := by
                simpa [foldGroundSelectionSet, Bind.bind, Except.bind,
                  hparentBool, hduplicate, hlookup,
                  hcompositeFalse, hleaf, hrestFold, currentShape, definition,
                  fieldHead] using hfold
              have hshape : shape = mergeResponseShapes currentShape restShape :=
                (Except.ok.inj hfold').symm
              subst shape
              have hrestRelation := ihrest restShape hrestFold
              have hcurrent : currentShape.reifySelectionSet schema assignment
                  decodedParent = [.field responseName fieldName arguments [] []] := by
                rw [reify_singletonDefinitionShape_object_active schema assignment
                  decodedParent responseName definition hparentBool
                  (by simpa [definition, ShapeDefinition.clause] using hactive)]
                rfl
              have hfield : NormalForm.SelectionEqualUpToReordering
                  (.field responseName fieldName arguments [] [])
                  (.field responseName fieldName arguments [] []) :=
                .field responseName fieldName []
                  (NormalForm.GroundTypeNormalization.argumentsEquivalent_refl
                    arguments)
                  (selectionSetEqualUpToReordering_refl [])
              have hcurrentRelation : NormalForm.SelectionSetEqualUpToReordering
                  (currentShape.reifySelectionSet schema assignment decodedParent)
                  [.field responseName fieldName arguments [] []] := by
                rw [hcurrent]
                exact selectionSetEqualUpToReordering_cons hfield
                  (selectionSetEqualUpToReordering_refl [])
              have happend := selectionSetEqualUpToReordering_append
                hcurrentRelation hrestRelation
              exact selectionSetEqualUpToReordering_perm_left
                (reifySelectionSet_merge_perm_of_object schema assignment
                  decodedParent currentShape restShape hparentBool).symm happend
  | @composite fieldDefinition childSelection hcomposite hselection
      ihselection childShape hchildFold =>
      exact ihselection childShape hchildFold
  | @leaf fieldDefinition hleaf childShape hchildFold =>
      unfold foldGroundSelectionSet at hchildFold
      unfold NormalForm.leafTypeNameBool at hleaf
      cases hlookup : schema.lookupType fieldDefinition.outputType.namedType with
      | none => simp [hlookup] at hleaf
      | some typeDefinition =>
          cases typeDefinition <;>
            simp_all [NormalForm.objectTypeNameBool, abstractTypeNameBool]
  | @abstractNil decodedParent habstract =>
      have hobjectFalse :=
        abstractType_objectTypeNameBool_eq_false schema decodedParent habstract
      have habstractTrue : abstractTypeNameBool schema decodedParent = true := by
        rcases habstract with ⟨interfaceType, hlookup⟩ |
            ⟨unionType, hlookup⟩ <;>
          simp [abstractTypeNameBool, hlookup]
      have hshape : shape = .object [] := by
        have hfold' :
            (Except.ok (.object []) : Except ShapeBuildError ResponseShape) =
              Except.ok shape := by
          simpa [foldGroundSelectionSet, hobjectFalse, habstractTrue] using hfold
        exact (Except.ok.inj hfold').symm
      subst shape
      have hempty :
          (ResponseShape.object []).reifySelectionSet schema assignment
            decodedParent = [] := by
        simp [ResponseShape.reifySelectionSet, hobjectFalse,
          reifyResponsePositions]
      rw [hempty]
      exact selectionSetEqualUpToReordering_refl []
  | @abstractFragment decodedParent objectType body rest habstract hobject
      hincludes hnonempty htypeCondition hselection hrest ihselection ihrest =>
      rcases hobject with ⟨objectDefinition, hobjectLookup⟩
      have hparentFalse :=
        abstractType_objectTypeNameBool_eq_false schema decodedParent habstract
      have habstractTrue : abstractTypeNameBool schema decodedParent = true := by
        rcases habstract with ⟨interfaceType, hlookup⟩ |
            ⟨unionType, hlookup⟩ <;>
          simp [abstractTypeNameBool, hlookup]
      have hlookupObject : schema.lookupObject objectType = some objectDefinition := by
        simp [Schema.lookupObject, hobjectLookup]
      have hobjectBool :
          NormalForm.objectTypeNameBool schema objectType = true := by
        simp [NormalForm.objectTypeNameBool, hobjectLookup]
      have hduplicate :
          rest.any (selectionHasTypeCondition objectType) = false :=
        selectionHasTypeCondition_any_eq_false objectType rest htypeCondition
      cases body with
      | nil => exact (hnonempty rfl).elim
      | cons head tail =>
          cases hchildFold : foldGroundSelectionSet schema clause objectType
              (head :: tail) with
          | error error =>
              simp [foldGroundSelectionSet, Bind.bind, Except.bind, hparentFalse,
                habstractTrue, hduplicate, hlookupObject, hincludes, hchildFold] at hfold
          | ok childShape =>
              cases hrestFold : foldGroundSelectionSet schema clause decodedParent
                  rest with
              | error error =>
                  simp [foldGroundSelectionSet, Bind.bind, Except.bind,
                    hparentFalse, habstractTrue, hduplicate, hlookupObject,
                    hincludes, hchildFold, hrestFold] at hfold
              | ok restShape =>
                  have hfold' :
                      (Except.ok (mergeResponseShapes childShape restShape) :
                          Except ShapeBuildError ResponseShape) = Except.ok shape := by
                    simpa [foldGroundSelectionSet, Bind.bind, Except.bind,
                      hparentFalse, habstractTrue, hduplicate, hlookupObject,
                      hincludes, hchildFold, hrestFold] using hfold
                  have hshape : shape =
                      mergeResponseShapes childShape restShape :=
                    (Except.ok.inj hfold').symm
                  subst shape
                  have hchildRelation := ihselection childShape hchildFold
                  have hchildReifyEq :
                      childShape.reifySelectionSet schema assignment objectType =
                        reifyResponsePositions schema assignment objectType
                          childShape.positions := by
                    cases childShape with
                    | object positions =>
                        unfold ResponseShape.reifySelectionSet
                        rw [hobjectBool]
                        rfl
                  have hchildBody : NormalForm.SelectionSetEqualUpToReordering
                      (reifyResponsePositions schema assignment objectType
                        childShape.positions)
                      (head :: tail) := by
                    rw [← hchildReifyEq]
                    exact hchildRelation
                  have hrestRelation := ihrest restShape hrestFold
                  have hchildResult :=
                    foldGroundSelectionSet_invariant_of_image schema support clause
                      hvalid hcomplete hselection hchildFold
                  have hchildKeys : ShapeObjectTypesIn [objectType] childShape :=
                    (hchildResult.2.2.1
                      ⟨objectDefinition, hobjectLookup⟩).2
                  have hrestResult :=
                    foldGroundSelectionSet_invariant_of_image schema support clause
                      hvalid hcomplete hrest hrestFold
                  have hrestKeys : ShapeObjectTypesIn
                      (rest.filterMap NormalForm.inlineFragmentTypeCondition?)
                      restShape :=
                    hrestResult.2.2.2 habstract
                  have hmergedRelation :=
                    reifySelectionSet_abstract_merge_cons schema hschema assignment
                      decodedParent objectType (head :: tail) childShape restShape
                      (rest.filterMap NormalForm.inlineFragmentTypeCondition?)
                      habstract hincludes hchildKeys hrestKeys htypeCondition
                      hchildBody (by simp)
                  have hheadRelation :=
                    selectionEqualUpToReordering_refl
                      (.inlineFragment (some objectType) [] (head :: tail))
                  have htargetRelation :=
                    selectionSetEqualUpToReordering_cons hheadRelation hrestRelation
                  exact NormalForm.SelectionSetEqualUpToReordering.trans hmergedRelation
                    htargetRelation

private theorem foldGroundSelectionSet_reify_inactive
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (hvalid : clause.Valid support) (hcomplete : clause.CompleteMinterm support)
    (assignment : NormalForm.BoolCase)
    {parentType : Name} {selectionSet : List Selection}
    (himage : GroundSelectionSetImage schema parentType selectionSet)
    {shape : ResponseShape}
    (hfold : foldGroundSelectionSet schema clause parentType selectionSet = .ok shape)
    (hinactive : clause.holdsInBool assignment = false) :
    shape.reifySelectionSet schema assignment parentType = [] := by
  have hresult := foldGroundSelectionSet_invariant_of_image schema support clause
    hvalid hcomplete himage hfold
  exact reifySelectionSet_eq_nil_of_uniform_inactive schema assignment parentType
    shape clause hresult.2.1 hinactive

private theorem decodeRootBranches_reify_case
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List NormalForm.BoolVar) (hsupport : support.Nodup)
    (hsupportNonempty : support ≠ [])
    (parentType : Name) (hparentObject : schema.objectType parentType)
    (selectionSet : List Selection) :
    ∀ (boolCases : List NormalForm.BoolCase) (seen : List Clause)
        (shape : ResponseShape) (assignment : NormalForm.BoolCase),
      boolCases.Nodup ->
      (∀ boolCase, boolCase ∈ boolCases ->
        boolCase ∈ NormalForm.allBoolCases support) ->
      (∀ clause, clause ∈ seen ->
        ∃ seenCase,
          seenCase ∈ NormalForm.allBoolCases support
          ∧ seenCase ∉ boolCases
          ∧ clause = Clause.canonical { literals := seenCase }) ->
      assignment ∈ NormalForm.allBoolCases support ->
      decodeRootBranches schema support parentType seen
          (List.flatten
            (boolCases.map
              (normalizedRootBranch schema parentType selectionSet))) = .ok shape ->
      NormalForm.SelectionSetEqualUpToReordering
        (shape.reifySelectionSet schema assignment parentType)
        (if assignment ∈ boolCases then
          NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase assignment selectionSet)
        else [])
  | [], seen, shape, assignment, _hcasesNodup, _hcasesGenerated, _hseen,
      _hassignment, hdecode => by
      have hshape : shape = .object [] := by
        exact (Except.ok.inj hdecode).symm
      subst shape
      have hparentBool :
          NormalForm.objectTypeNameBool schema parentType = true :=
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
          schema hparentObject
      simpa [ResponseShape.reifySelectionSet, hparentBool,
        reifyResponsePositions] using selectionSetEqualUpToReordering_refl []
  | boolCase :: restCases, seen, shape, assignment, hcasesNodup,
      hcasesGenerated, hseen, hassignment, hdecode => by
      have hcaseGenerated :
          boolCase ∈ NormalForm.allBoolCases support :=
        hcasesGenerated boolCase (by simp)
      have hrestGenerated :
          ∀ candidate, candidate ∈ restCases ->
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
          have hrestSeen :
              ∀ clause, clause ∈ seen ->
                ∃ seenCase,
                  seenCase ∈ NormalForm.allBoolCases support
                  ∧ seenCase ∉ restCases
                  ∧ clause = Clause.canonical { literals := seenCase } := by
            intro clause hclause
            rcases hseen clause hclause with
              ⟨seenCase, hseenGenerated, hseenAbsent, hclauseEq⟩
            exact ⟨seenCase, hseenGenerated,
              fun hseenRest =>
                hseenAbsent (List.mem_cons_of_mem boolCase hseenRest),
              hclauseEq⟩
          have hrestDecode :
              decodeRootBranches schema support parentType seen
                  (List.flatten
                    (restCases.map
                      (normalizedRootBranch schema parentType selectionSet))) =
                .ok shape := by
            simpa [normalizedRootBranch, hbody] using hdecode
          have ih := decodeRootBranches_reify_case schema hschema support hsupport
            hsupportNonempty parentType hparentObject selectionSet restCases seen
            shape assignment hparts.2 hrestGenerated hrestSeen hassignment hrestDecode
          by_cases heq : assignment = boolCase
          · subst assignment
            simp [hparts.1, hbody] at ih ⊢
            exact ih
          · simpa [heq] using ih
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
            canonicalClause_valid_of_mem_allBoolCases support hsupport hcaseGenerated
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
              normalizeSelectionSet_groundSelectionSetImage schema hschema parentType
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
                hparentObject hfilteredFree
          have hrestSeen :
              ∀ seenClause, seenClause ∈ clause :: seen ->
                ∃ seenCase,
                  seenCase ∈ NormalForm.allBoolCases support
                  ∧ seenCase ∉ restCases
                  ∧ seenClause = Clause.canonical { literals := seenCase } := by
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
          have hbranchInput :
              List.flatten
                  ((boolCase :: restCases).map
                    (normalizedRootBranch schema parentType selectionSet)) =
                wrappedSelection ::
                  List.flatten
                    (restCases.map
                      (normalizedRootBranch schema parentType selectionSet)) := by
            simp only [List.map_cons, List.flatten_cons]
            have hbranch :
                normalizedRootBranch schema parentType selectionSet boolCase =
                  NormalForm.wrapWithBoolCase boolCase body := by
              simp [normalizedRootBranch, hbody, body]
            rw [hbranch, hwrap]
            rfl
          rw [hbranchInput, decodeRootBranches, hstem] at hdecode
          simp only [Bind.bind, Except.bind] at hdecode
          rw [hclause] at hdecode
          simp only at hdecode
          rw [hduplicate] at hdecode
          simp only [Bool.false_eq_true, if_false] at hdecode
          cases hbranchFold :
              foldGroundSelectionSet schema clause parentType body with
          | error error => simp [hbranchFold] at hdecode
          | ok branchShape =>
              rw [hbranchFold] at hdecode
              cases hrestDecode :
                  decodeRootBranches schema support parentType (clause :: seen)
                    (List.flatten
                      (restCases.map
                        (normalizedRootBranch schema parentType selectionSet))) with
              | error error => simp [hrestDecode] at hdecode
              | ok restShape =>
                  rw [hrestDecode] at hdecode
                  have hshape : shape =
                      mergeResponseShapes branchShape restShape :=
                    (Except.ok.inj hdecode).symm
                  subst shape
                  have hrestRelation := decodeRootBranches_reify_case schema
                    hschema support hsupport hsupportNonempty parentType
                    hparentObject selectionSet restCases (clause :: seen)
                    restShape assignment hparts.2 hrestGenerated hrestSeen
                    hassignment hrestDecode
                  have hparentBool :
                      NormalForm.objectTypeNameBool schema parentType = true :=
                    NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
                      schema hparentObject
                  have hmergePerm :=
                    reifySelectionSet_merge_perm_of_object schema assignment
                      parentType branchShape restShape hparentBool
                  by_cases heq : assignment = boolCase
                  · subst assignment
                    have hactive : clause.holdsInBool boolCase = true := by
                      apply (Clause.holdsInBool_iff boolCase clause).2
                      simpa [clause] using
                        canonicalClause_holdsIn_of_mem_allBoolCases support
                          hsupport hcaseGenerated
                    have hbranchRelation := foldGroundSelectionSet_reify_active
                      schema hschema support clause hclauseValid hclauseComplete
                      boolCase hactive himage branchShape hbranchFold
                    have hrestEmpty :
                        NormalForm.SelectionSetEqualUpToReordering
                          (restShape.reifySelectionSet schema boolCase parentType) [] := by
                      simpa [hparts.1] using hrestRelation
                    have happend := selectionSetEqualUpToReordering_append
                      hbranchRelation hrestEmpty
                    have hmerged := selectionSetEqualUpToReordering_perm_left
                      hmergePerm.symm happend
                    simpa [hbody, body] using hmerged
                  · have htargetComplete :
                        Clause.CompleteMinterm support
                          (Clause.canonical { literals := assignment }) :=
                      canonicalClause_completeMinterm_of_mem_allBoolCases support
                        hsupport hassignment
                    have htargetActive :
                        Clause.holdsInBool assignment
                          (Clause.canonical { literals := assignment }) = true := by
                      apply (Clause.holdsInBool_iff assignment
                        (Clause.canonical { literals := assignment })).2
                      exact canonicalClause_holdsIn_of_mem_allBoolCases support
                        hsupport hassignment
                    have hinactive : clause.holdsInBool assignment = false := by
                      cases hholds : clause.holdsInBool assignment with
                      | false => rfl
                      | true =>
                          have hclauseEq :=
                            Clause.eq_of_completeMinterm_of_holdsInBool
                              hclauseComplete htargetComplete hholds htargetActive
                          have hcaseEq : boolCase = assignment :=
                            canonicalClause_injective_of_mem_allBoolCases support
                              hsupport hcaseGenerated hassignment (by
                                simpa [clause] using hclauseEq)
                          exact (heq hcaseEq.symm).elim
                    have hbranchEmpty :
                        branchShape.reifySelectionSet schema assignment parentType = [] :=
                      foldGroundSelectionSet_reify_inactive schema support clause
                        hclauseValid hclauseComplete assignment himage hbranchFold
                        hinactive
                    have hbranchRelation :
                        NormalForm.SelectionSetEqualUpToReordering
                          (branchShape.reifySelectionSet schema assignment parentType)
                          [] := by
                      rw [hbranchEmpty]
                      exact selectionSetEqualUpToReordering_refl []
                    have happend := selectionSetEqualUpToReordering_append
                      hbranchRelation hrestRelation
                    have hmerged := selectionSetEqualUpToReordering_perm_left
                      hmergePerm.symm happend
                    simpa [heq] using hmerged

private theorem decodeCompleteRoot_reify_case
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List NormalForm.BoolVar) (hsupport : support.Nodup)
    (parentType : Name) (hparentObject : schema.objectType parentType)
    (selectionSet : List Selection) (shape : ResponseShape)
    (hdecode :
      decodeCompleteRoot schema support parentType
          (NormalForm.completeNormalizeRootSelectionSet
            schema support parentType selectionSet) = .ok shape) :
    ∀ assignment, assignment ∈ NormalForm.allBoolCases support ->
      NormalForm.SelectionSetEqualUpToReordering
        (shape.reifySelectionSet schema assignment parentType)
        (NormalForm.normalizeSelectionSet schema parentType
          (NormalForm.filterSelectionSetBoolCase assignment selectionSet)) := by
  have hduplicate : firstDuplicate? support = none :=
    firstDuplicate?_eq_none_of_nodup support hsupport
  cases support with
  | nil =>
      intro assignment hassignment
      have hassignmentEq : assignment = [] := by
        simpa [NormalForm.allBoolCases] using hassignment
      subst assignment
      let body := NormalForm.normalizeSelectionSet schema parentType
        (NormalForm.filterSelectionSetBoolCase [] selectionSet)
      have hrootInput :
          NormalForm.completeNormalizeRootSelectionSet schema [] parentType
              selectionSet = body := by
        unfold NormalForm.completeNormalizeRootSelectionSet
        change List.flatten
            ((NormalForm.allBoolCases []).map
              (fun boolCase =>
                match NormalForm.normalizeSelectionSet schema parentType
                    (NormalForm.filterSelectionSetBoolCase boolCase selectionSet) with
                | [] => []
                | selection :: rest =>
                    NormalForm.wrapWithBoolCase boolCase (selection :: rest))) = body
        simp only [NormalForm.allBoolCases, List.map_cons, List.map_nil,
          List.flatten_cons, List.flatten_nil, List.append_nil]
        change (match body with
          | [] => []
          | selection :: rest =>
              NormalForm.wrapWithBoolCase [] (selection :: rest)) = body
        cases body <;> rfl
      have hfold :
          foldGroundSelectionSet schema { literals := [] } parentType body =
            .ok shape := by
        simpa [decodeCompleteRoot, hduplicate, hrootInput] using hdecode
      have hfilteredFree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.filterSelectionSetBoolCase [] selectionSet) :=
        NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
          schema [] selectionSet
      have himage : GroundSelectionSetImage schema parentType body := by
        exact normalizeSelectionSet_groundSelectionSetImage schema hschema parentType
          (NormalForm.filterSelectionSetBoolCase [] selectionSet)
          hparentObject hfilteredFree
      have hactive :
          Clause.holdsInBool [] ({ literals := [] } : Clause) = true := rfl
      exact foldGroundSelectionSet_reify_active schema hschema []
        { literals := [] } (by rfl) (by rfl) [] hactive himage shape hfold
  | cons varName variables =>
      intro assignment hassignment
      have hrootDecode :
          decodeRootBranches schema (varName :: variables) parentType []
              (List.flatten
                ((NormalForm.allBoolCases (varName :: variables)).map
                  (normalizedRootBranch schema parentType selectionSet))) =
            .ok shape := by
        have hrootDecode' := hdecode
        simp only [decodeCompleteRoot, hduplicate,
          NormalForm.completeNormalizeRootSelectionSet] at hrootDecode'
        change decodeRootBranches schema (varName :: variables) parentType []
            (List.flatten
              ((NormalForm.allBoolCases (varName :: variables)).map
                (normalizedRootBranch schema parentType selectionSet))) =
          .ok shape at hrootDecode'
        exact hrootDecode'
      have hcasesNodup :
          (NormalForm.allBoolCases (varName :: variables)).Nodup :=
        NormalForm.CompleteNormalization.allBoolCases_nodup hsupport
      have hrelation := decodeRootBranches_reify_case schema hschema
        (varName :: variables) hsupport (by simp) parentType hparentObject
        selectionSet (NormalForm.allBoolCases (varName :: variables)) [] shape
        assignment hcasesNodup (fun boolCase hcase => hcase) (by simp)
        hassignment hrootDecode
      simpa [hassignment] using hrelation

private theorem wrappedCaseBranches_completeEqual
    (support leftVariables rightVariables : List NormalForm.BoolVar)
    (hsupportNonempty : support ≠ [])
    (leftBodies rightBodies : NormalForm.BoolCase -> List Selection) :
    ∀ cases : List NormalForm.BoolCase,
      (∀ boolCase, boolCase ∈ cases ->
        boolCase ∈ NormalForm.allBoolCases support) ->
      (∀ boolCase, boolCase ∈ cases ->
        NormalForm.completeNormalBoolCase leftVariables boolCase) ->
      (∀ boolCase, boolCase ∈ cases ->
        NormalForm.completeNormalBoolCase rightVariables boolCase) ->
      (∀ boolCase, boolCase ∈ cases ->
        NormalForm.SelectionSetEqualUpToReordering
          (leftBodies boolCase) (rightBodies boolCase)) ->
      NormalForm.CompleteNormalSelectionSetEqualUpToReordering
        leftVariables rightVariables
        (List.flatten (cases.map
          (fun boolCase => wrapNonemptyCase boolCase (leftBodies boolCase))))
        (List.flatten (cases.map
          (fun boolCase => wrapNonemptyCase boolCase (rightBodies boolCase))))
  | [], _hgenerated, _hleftCases, _hrightCases, _hrelations => by
      exact ⟨[], by simp, by simp, by simp⟩
  | boolCase :: rest, hgenerated, hleftCases, hrightCases, hrelations => by
      have hcaseGenerated :
          boolCase ∈ NormalForm.allBoolCases support :=
        hgenerated boolCase (by simp)
      have hcaseNonempty : boolCase ≠ [] := by
        intro hnil
        have hnames :=
          NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
            hcaseGenerated
        simp [hnil] at hnames
        exact hsupportNonempty hnames
      have hrestGenerated :
          ∀ candidate, candidate ∈ rest ->
            candidate ∈ NormalForm.allBoolCases support := by
        intro candidate hcandidate
        exact hgenerated candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrestLeftCases :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.completeNormalBoolCase leftVariables candidate := by
        intro candidate hcandidate
        exact hleftCases candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrestRightCases :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.completeNormalBoolCase rightVariables candidate := by
        intro candidate hcandidate
        exact hrightCases candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrestRelations :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.SelectionSetEqualUpToReordering
              (leftBodies candidate) (rightBodies candidate) := by
        intro candidate hcandidate
        exact hrelations candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrest := wrappedCaseBranches_completeEqual support leftVariables
        rightVariables hsupportNonempty leftBodies rightBodies rest
        hrestGenerated hrestLeftCases hrestRightCases hrestRelations
      have hrelation := hrelations boolCase (by simp)
      cases hleftBody : leftBodies boolCase with
      | nil =>
          cases hrightBody : rightBodies boolCase with
          | nil =>
              simpa [wrapNonemptyCase, hleftBody, hrightBody] using hrest
          | cons rightHead rightTail =>
              have hlength := selectionSetEqualUpToReordering_length_eq hrelation
              simp [hleftBody, hrightBody] at hlength
      | cons leftHead leftTail =>
          cases hrightBody : rightBodies boolCase with
          | nil =>
              have hlength := selectionSetEqualUpToReordering_length_eq hrelation
              simp [hleftBody, hrightBody] at hlength
          | cons rightHead rightTail =>
              rcases
                  NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                    boolCase (leftHead :: leftTail) hcaseNonempty with
                ⟨leftSelection, hleftWrap⟩
              rcases
                  NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                    boolCase (rightHead :: rightTail) hcaseNonempty with
                ⟨rightSelection, hrightWrap⟩
              rcases hrest with ⟨pairs, hpairsLeft, hpairsRight, hpairsEqual⟩
              refine ⟨(leftSelection, rightSelection) :: pairs, ?_, ?_, ?_⟩
              · simp only [List.map_cons]
                simpa [wrapNonemptyCase, hleftBody, hleftWrap] using
                  List.Perm.cons leftSelection hpairsLeft
              · simp only [List.map_cons]
                simpa [wrapNonemptyCase, hrightBody, hrightWrap] using
                  List.Perm.cons rightSelection hpairsRight
              · intro pair hpair
                rcases List.mem_cons.mp hpair with hhead | htail
                · subst pair
                  refine ⟨boolCase, boolCase, leftHead :: leftTail,
                    rightHead :: rightTail,
                    hleftCases boolCase (by simp),
                    hrightCases boolCase (by simp), ?_, ?_,
                    NormalForm.CompleteNormalization.completeNormalBoolCasesEquivalent_refl
                      boolCase, ?_⟩
                  · exact NormalForm.CompleteNormalization.completeNormalBooleanStem_wrapWithBoolCase
                      boolCase
                        (leftHead :: leftTail) leftSelection hcaseNonempty hleftWrap
                  · exact NormalForm.CompleteNormalization.completeNormalBooleanStem_wrapWithBoolCase
                      boolCase
                        (rightHead :: rightTail) rightSelection hcaseNonempty hrightWrap
                  · simpa [hleftBody, hrightBody] using hrelation
                · exact hpairsEqual pair htail

private theorem mem_selectionSetBooleanVariables_iff
    (varName : NormalForm.BoolVar) (selectionSet : List Selection) :
    varName ∈ NormalForm.selectionSetBooleanVariables selectionSet ↔
      ∃ selection,
        selection ∈ selectionSet ∧
          varName ∈ NormalForm.selectionBooleanVariables selection := by
  induction selectionSet with
  | nil => simp [NormalForm.selectionSetBooleanVariables]
  | cons selection rest ih =>
      simp [NormalForm.selectionSetBooleanVariables, ih]

private theorem selectionSetBooleanVariables_mem_iff_of_reordering
    {left right : List Selection}
    (hequal : NormalForm.SelectionSetEqualUpToReordering left right)
    (varName : NormalForm.BoolVar) :
    varName ∈ NormalForm.selectionSetBooleanVariables left ↔
      varName ∈ NormalForm.selectionSetBooleanVariables right := by
  refine NormalForm.SelectionSetEqualUpToReordering.rec
    (motive_1 := fun left right _hequal =>
      ∀ varName,
        varName ∈ NormalForm.selectionBooleanVariables left ↔
          varName ∈ NormalForm.selectionBooleanVariables right)
    (motive_2 := fun left right _hequal =>
      ∀ varName,
        varName ∈ NormalForm.selectionSetBooleanVariables left ↔
          varName ∈ NormalForm.selectionSetBooleanVariables right)
    ?_ ?_ ?_ hequal varName
  · intro responseName fieldName leftArguments rightArguments directives
      leftSelectionSet rightSelectionSet _harguments _hselectionSet ih varName
    simp only [NormalForm.selectionBooleanVariables, List.mem_append]
    exact or_congr Iff.rfl (ih varName)
  · intro typeCondition directives leftSelectionSet rightSelectionSet
      _hselectionSet ih varName
    simp only [NormalForm.selectionBooleanVariables, List.mem_append]
    exact or_congr Iff.rfl (ih varName)
  · intro left right pairs hleft hright _hpairs ih varName
    rw [mem_selectionSetBooleanVariables_iff,
      mem_selectionSetBooleanVariables_iff]
    constructor
    · rintro ⟨leftSelection, hleftMem, hvarMem⟩
      have hleftPairMem : leftSelection ∈ pairs.map Prod.fst :=
        hleft.mem_iff.mpr hleftMem
      rcases List.mem_map.mp hleftPairMem with
        ⟨pair, hpairMem, hpairLeft⟩
      refine ⟨pair.2, hright.mem_iff.mp ?_, ?_⟩
      · exact List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
      · exact (ih pair hpairMem varName).mp
          (by simpa [hpairLeft] using hvarMem)
    · rintro ⟨rightSelection, hrightMem, hvarMem⟩
      have hrightPairMem : rightSelection ∈ pairs.map Prod.snd :=
        hright.mem_iff.mpr hrightMem
      rcases List.mem_map.mp hrightPairMem with
        ⟨pair, hpairMem, hpairRight⟩
      refine ⟨pair.1, hleft.mem_iff.mp ?_, ?_⟩
      · exact List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
      · exact (ih pair hpairMem varName).mpr
          (by simpa [hpairRight] using hvarMem)

private theorem wrappedCaseBranches_length_eq
    (support : List NormalForm.BoolVar) (hsupportNonempty : support ≠ [])
    (leftBodies rightBodies : NormalForm.BoolCase -> List Selection) :
    ∀ cases : List NormalForm.BoolCase,
      (∀ boolCase, boolCase ∈ cases ->
        boolCase ∈ NormalForm.allBoolCases support) ->
      (∀ boolCase, boolCase ∈ cases ->
        NormalForm.SelectionSetEqualUpToReordering
          (leftBodies boolCase) (rightBodies boolCase)) ->
      (List.flatten (cases.map
        (fun boolCase => wrapNonemptyCase boolCase (leftBodies boolCase)))).length =
      (List.flatten (cases.map
        (fun boolCase => wrapNonemptyCase boolCase (rightBodies boolCase)))).length
  | [], _hgenerated, _hrelations => rfl
  | boolCase :: rest, hgenerated, hrelations => by
      have hcaseGenerated :
          boolCase ∈ NormalForm.allBoolCases support :=
        hgenerated boolCase (by simp)
      have hcaseNonempty : boolCase ≠ [] := by
        intro hnil
        have hnames :=
          NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
            hcaseGenerated
        simp [hnil] at hnames
        exact hsupportNonempty hnames
      have hrestGenerated :
          ∀ candidate, candidate ∈ rest ->
            candidate ∈ NormalForm.allBoolCases support := by
        intro candidate hcandidate
        exact hgenerated candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrestRelations :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.SelectionSetEqualUpToReordering
              (leftBodies candidate) (rightBodies candidate) := by
        intro candidate hcandidate
        exact hrelations candidate (List.mem_cons_of_mem boolCase hcandidate)
      have hrestLength := wrappedCaseBranches_length_eq support hsupportNonempty
        leftBodies rightBodies rest hrestGenerated hrestRelations
      have hcurrentLength := selectionSetEqualUpToReordering_length_eq
        (hrelations boolCase (by simp))
      cases hleftBody : leftBodies boolCase with
      | nil =>
          cases hrightBody : rightBodies boolCase with
          | nil => simpa [wrapNonemptyCase, hleftBody, hrightBody] using hrestLength
          | cons rightHead rightTail =>
              simp [hleftBody, hrightBody] at hcurrentLength
      | cons leftHead leftTail =>
          cases hrightBody : rightBodies boolCase with
          | nil => simp [hleftBody, hrightBody] at hcurrentLength
          | cons rightHead rightTail =>
              rcases
                  NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                    boolCase (leftHead :: leftTail) hcaseNonempty with
                ⟨leftSelection, hleftWrap⟩
              rcases
                  NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                    boolCase (rightHead :: rightTail) hcaseNonempty with
                ⟨rightSelection, hrightWrap⟩
              simpa [wrapNonemptyCase, hleftBody, hrightBody, hleftWrap,
                hrightWrap] using congrArg Nat.succ hrestLength

theorem reify_compute_equalUpToReordering
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape) :
    NormalForm.completeNormalOperationsEqualUpToReordering
      (reifyOperation schema operation shape)
      (NormalForm.completeNormalizeOperation schema operation) := by
  let support := NormalForm.operationBoolVars operation
  let rootType := operation.rootType schema
  let cases := NormalForm.allBoolCases support
  let leftBodies : NormalForm.BoolCase -> List Selection :=
    fun assignment =>
      shape.root.reifySelectionSet schema assignment shape.rootType
  let rightBodies : NormalForm.BoolCase -> List Selection :=
    fun assignment =>
      NormalForm.normalizeSelectionSet schema rootType
        (NormalForm.filterSelectionSetBoolCase assignment operation.selectionSet)
  let leftSelectionSet := List.flatten
    (cases.map
      (fun assignment => wrapNonemptyCase assignment (leftBodies assignment)))
  let rightSelectionSet := List.flatten
    (cases.map
      (fun assignment => wrapNonemptyCase assignment (rightBodies assignment)))
  rcases computeOperationShape_fields schema operation shape hcompute with
    ⟨hoperationType, hrootType, hshapeSupport, hrootDecode⟩
  have hsupport : support.Nodup := by
    exact NormalForm.CompleteNormalization.dedupBoolVars_nodup _
  have hrootEq : rootType = schema.queryType := by
    exact Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject : schema.objectType rootType := by
    simpa [hrootEq] using hschema.2.1
  have hdecode :
      decodeCompleteRoot schema support rootType
          (NormalForm.completeNormalizeRootSelectionSet schema support rootType
            operation.selectionSet) = .ok shape.root := by
    simpa [support, rootType, NormalForm.completeNormalizeOperation] using
      hrootDecode
  have hcaseRelation : ∀ assignment, assignment ∈ cases ->
      NormalForm.SelectionSetEqualUpToReordering
        (leftBodies assignment) (rightBodies assignment) := by
    intro assignment hassignment
    dsimp [leftBodies, rightBodies]
    rw [hrootType]
    exact decodeCompleteRoot_reify_case schema hschema support hsupport rootType
      hrootObject operation.selectionSet shape.root hdecode assignment
      (by simpa [cases] using hassignment)
  have hleftSelectionSet :
      (reifyOperation schema operation shape).selectionSet = leftSelectionSet := by
    unfold reifyOperation reifyCompleteSelectionSet
    rw [hshapeSupport]
    rfl
  have hrightSelectionSet :
      (NormalForm.completeNormalizeOperation schema operation).selectionSet =
        rightSelectionSet := by
    rfl
  have hrightBodyVariables : ∀ assignment,
      NormalForm.selectionSetBooleanVariables (rightBodies assignment) = [] := by
    intro assignment
    have hfilteredFree :
        NormalForm.selectionSetDirectiveFree
          (NormalForm.filterSelectionSetBoolCase assignment
            operation.selectionSet) :=
      NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
        schema assignment operation.selectionSet
    have hnormalizedFree :
        NormalForm.selectionSetDirectiveFree (rightBodies assignment) := by
      exact NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
        schema rootType
        (NormalForm.filterSelectionSetBoolCase assignment operation.selectionSet)
        hfilteredFree
    exact NormalForm.CompleteNormalization.selectionSetDirectiveFree_booleanVariables_nil
        (rightBodies assignment) hnormalizedFree
  have hleftBodyVariables : ∀ assignment, assignment ∈ cases ->
      NormalForm.selectionSetBooleanVariables (leftBodies assignment) = [] := by
    intro assignment hassignment
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro varName hvar
    have hvariables := selectionSetBooleanVariables_mem_iff_of_reordering
      (hcaseRelation assignment hassignment) varName
    have hrightNil := hrightBodyVariables assignment
    have hrightNotMem :
        varName ∉ NormalForm.selectionSetBooleanVariables
          (rightBodies assignment) := by
      rw [hrightNil]
      simp
    exact hrightNotMem (hvariables.mp hvar)
  unfold NormalForm.completeNormalOperationsEqualUpToReordering
  refine ⟨?_, ?_⟩
  · exact hoperationType
  · cases hsupportValue : support with
    | nil =>
        have hnilMem : ([] : NormalForm.BoolCase) ∈ cases := by
          simp [cases, hsupportValue, NormalForm.allBoolCases]
        have hselectionRelation := hcaseRelation [] hnilMem
        have hfullRelation :
            NormalForm.SelectionSetEqualUpToReordering
              leftSelectionSet rightSelectionSet := by
          simpa [leftSelectionSet, rightSelectionSet, cases, hsupportValue,
            NormalForm.allBoolCases, wrapNonemptyCase_nil] using
              hselectionRelation
        have hrightVariablesNil :
            NormalForm.selectionSetBooleanVariables rightSelectionSet = [] := by
          simpa [rightSelectionSet, cases, hsupportValue,
            NormalForm.allBoolCases, wrapNonemptyCase_nil] using
              hrightBodyVariables []
        have hleftVariablesNil :
            NormalForm.selectionSetBooleanVariables leftSelectionSet = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro varName hvar
          have hvariables := selectionSetBooleanVariables_mem_iff_of_reordering
            hfullRelation varName
          have hrightNotMem : varName ∉
              NormalForm.selectionSetBooleanVariables rightSelectionSet := by
            rw [hrightVariablesNil]
            simp
          exact hrightNotMem (hvariables.mp hvar)
        have hleftOperationVariables :
            NormalForm.operationBoolVars
                (reifyOperation schema operation shape) = [] := by
          unfold NormalForm.operationBoolVars
          rw [hleftSelectionSet, hleftVariablesNil]
          rfl
        rw [hleftOperationVariables, hleftSelectionSet, hrightSelectionSet]
        exact hfullRelation
    | cons supportHead supportTail =>
        have hsupportNonempty : support ≠ [] := by simp [hsupportValue]
        have hcasesGenerated : ∀ assignment, assignment ∈ cases ->
            assignment ∈ NormalForm.allBoolCases support := by
          intro assignment hassignment
          simpa [cases] using hassignment
        have hselectionLength := wrappedCaseBranches_length_eq support
          hsupportNonempty leftBodies rightBodies cases hcasesGenerated
          hcaseRelation
        have hselectionLength' :
            leftSelectionSet.length = rightSelectionSet.length :=
          hselectionLength
        by_cases hleftEmpty : leftSelectionSet = []
        · have hrightLength : rightSelectionSet.length = 0 := by
            rw [← hselectionLength', hleftEmpty]
            rfl
          have hrightEmpty : rightSelectionSet = [] :=
            List.length_eq_zero_iff.mp hrightLength
          have hleftOperationVariables :
              NormalForm.operationBoolVars
                  (reifyOperation schema operation shape) = [] := by
            unfold NormalForm.operationBoolVars
            rw [hleftSelectionSet, hleftEmpty]
            rfl
          rw [hleftOperationVariables, hleftSelectionSet, hrightSelectionSet,
            hleftEmpty, hrightEmpty]
          exact selectionSetEqualUpToReordering_refl []
        · have hrightNonempty : rightSelectionSet ≠ [] := by
            intro hrightEmpty
            apply hleftEmpty
            apply List.length_eq_zero_iff.mp
            rw [hselectionLength', hrightEmpty]
            rfl
          have hleftVariablesIff : ∀ varName,
              varName ∈ NormalForm.operationBoolVars
                  (reifyOperation schema operation shape) ↔
                varName ∈ support := by
            intro varName
            unfold NormalForm.operationBoolVars
            rw [hleftSelectionSet]
            exact wrappedCaseBranches_variables_mem_iff support leftBodies cases
              hcasesGenerated hleftBodyVariables hleftEmpty varName
          have hrightVariablesIff : ∀ varName,
              varName ∈ NormalForm.operationBoolVars
                  (NormalForm.completeNormalizeOperation schema operation) ↔
                varName ∈ support := by
            intro varName
            unfold NormalForm.operationBoolVars
            rw [hrightSelectionSet]
            exact wrappedCaseBranches_variables_mem_iff support rightBodies cases
              hcasesGenerated (fun assignment _ => hrightBodyVariables assignment)
              hrightNonempty varName
          have hleftCases : ∀ assignment, assignment ∈ cases ->
              NormalForm.completeNormalBoolCase
                (NormalForm.operationBoolVars
                  (reifyOperation schema operation shape)) assignment := by
            intro assignment hassignment
            have hsourceCase :=
              NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
                hsupport (hcasesGenerated assignment hassignment)
            exact NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
                hsourceCase
                (NormalForm.CompleteNormalization.operationBoolVars_nodup
                  (reifyOperation schema operation shape))
                (fun varName =>
                  (hsourceCase.2.2 varName).trans
                    (hleftVariablesIff varName).symm)
          have hrightCases : ∀ assignment, assignment ∈ cases ->
              NormalForm.completeNormalBoolCase
                (NormalForm.operationBoolVars
                  (NormalForm.completeNormalizeOperation schema operation))
                assignment := by
            intro assignment hassignment
            have hsourceCase :=
              NormalForm.CompleteNormalization.completeNormalBoolCase_of_mem_allBoolCases
                hsupport (hcasesGenerated assignment hassignment)
            exact NormalForm.CompleteNormalization.completeNormalBoolCase_of_variable_mem_iff
                hsourceCase
                (NormalForm.CompleteNormalization.operationBoolVars_nodup
                  (NormalForm.completeNormalizeOperation schema operation))
                (fun varName =>
                  (hsourceCase.2.2 varName).trans
                    (hrightVariablesIff varName).symm)
          have hcompleteRelation := wrappedCaseBranches_completeEqual support
            (NormalForm.operationBoolVars
              (reifyOperation schema operation shape))
            (NormalForm.operationBoolVars
              (NormalForm.completeNormalizeOperation schema operation))
            hsupportNonempty leftBodies rightBodies cases hcasesGenerated
            hleftCases hrightCases hcaseRelation
          cases hleftVariablesEq : NormalForm.operationBoolVars
              (reifyOperation schema operation shape) with
          | nil =>
              have hheadMem : supportHead ∈ support := by
                simp [hsupportValue]
              have himpossible := (hleftVariablesIff supportHead).2 hheadMem
              simp [hleftVariablesEq] at himpossible
          | cons leftHead leftTail =>
              simp only
              rw [hleftSelectionSet, hrightSelectionSet]
              simpa [hleftVariablesEq] using hcompleteRelation

end ResponseShape

end GraphQL
