import Proofs.GraphQL.Theories.ResponseShape.Compute.WellFormed

/-!
Preservation of the proof-facing decoder invariant by response-shape merge.
-/

namespace GraphQL

namespace ResponseShape

/-- Extensional list disjointness in the orientation expected by
`List.nodup_append`. -/
def ClausesDisjoint (left right : List Clause) : Prop :=
  ∀ leftClause ∈ left, ∀ rightClause ∈ right, leftClause ≠ rightClause

/-- Two possible-definition groups may be merged when clauses cannot be
duplicated in the only case in which the implementation concatenates them. -/
def PossibleDefinitionsMergeCompatible
    (left right : PossibleDefinitions) : Prop :=
  left.objectTypes = right.objectTypes ->
    ClausesDisjoint (left.definitions.map ShapeDefinition.clause)
      (right.definitions.map ShapeDefinition.clause)

/-- Two response positions may be merged when every pair of groups which the
implementation can coalesce has disjoint definition clauses. -/
def ResponsePositionMergeCompatible
    (left right : ResponsePosition) : Prop :=
  left.responseName = right.responseName ->
    ∀ leftGroup ∈ left.possibleDefinitions,
      ∀ rightGroup ∈ right.possibleDefinitions,
        PossibleDefinitionsMergeCompatible leftGroup rightGroup

/-- Collision-local compatibility for `mergeResponseShapes`.  No condition is
imposed on distinct response names or distinct singleton object keys. -/
def MergeCompatible : ResponseShape -> ResponseShape -> Prop
  | .object left, .object right =>
      ∀ leftPosition ∈ left, ∀ rightPosition ∈ right,
        ResponsePositionMergeCompatible leftPosition rightPosition

private theorem decoderDefinitionsInvariant_append
    (schema : Schema) (support : List NormalForm.BoolVar)
    (left right : List ShapeDefinition)
    (hleft : decoderDefinitionsInvariant schema support left)
    (hright : decoderDefinitionsInvariant schema support right) :
    decoderDefinitionsInvariant schema support (left ++ right) := by
  intro definition hdefinition
  rw [List.mem_append] at hdefinition
  cases hdefinition with
  | inl h => exact hleft definition h
  | inr h => exact hright definition h

private theorem mergedGroupInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (left right : PossibleDefinitions)
    (heq : left.objectTypes = right.objectTypes)
    (hleft : DecoderGroupInvariant schema support parentType left)
    (hright : DecoderGroupInvariant schema support parentType right)
    (hcompatible : PossibleDefinitionsMergeCompatible left right) :
    DecoderGroupInvariant schema support parentType
      (.mk left.objectTypes (left.definitions ++ right.definitions)) := by
  refine ⟨hleft.1, ?_, ?_⟩
  · simp only [PossibleDefinitions.definitions, List.map_append]
    exact List.nodup_append.mpr
      ⟨hleft.2.1, hright.2.1, hcompatible heq⟩
  · simp only [PossibleDefinitions.definitions]
    exact decoderDefinitionsInvariant_append schema support
      left.definitions right.definitions hleft.2.2 hright.2.2

private def decoderGroupsMergeInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (groups : List PossibleDefinitions) : Prop :=
  (groups.map PossibleDefinitions.objectTypes).Nodup
  ∧ (∀ group ∈ groups, ∃ objectType, group.objectTypes = [objectType])
  ∧ ∀ group ∈ groups,
      DecoderGroupInvariant schema support parentType group

private theorem singletonMap_nodup
    {objects : List GroundObject}
    (hnodup : objects.Nodup) :
    (objects.map (fun objectType => [objectType])).Nodup := by
  induction objects with
  | nil => simp
  | cons objectType rest ih =>
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmember
        simp only [List.mem_map] at hmember
        rcases hmember with ⟨candidate, hcandidate, heq⟩
        simp only [List.cons.injEq] at heq
        exact (List.nodup_cons.mp hnodup).1 (heq.1 ▸ hcandidate)
      · exact ih (List.nodup_cons.mp hnodup).2

private theorem nodup_of_singletonMap_nodup
    {objects : List GroundObject}
    (hnodup : (objects.map (fun objectType => [objectType])).Nodup) :
    objects.Nodup := by
  induction objects with
  | nil => simp
  | cons objectType rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmember
        exact hnodup.1 (List.mem_map.mpr ⟨objectType, hmember, rfl⟩)
      · exact ih hnodup.2

private theorem decoderGroupsMergeInvariant_of_position
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition)
    (hinvariant : DecoderPositionInvariant schema support parentType position) :
    decoderGroupsMergeInvariant schema support parentType
      position.possibleDefinitions := by
  rcases hinvariant with ⟨objects, hobjects, hnodup, hgroups⟩
  refine ⟨?_, ?_, hgroups⟩
  · rw [hobjects]
    exact singletonMap_nodup hnodup
  · intro group hgroup
    have hkey : group.objectTypes ∈
        position.possibleDefinitions.map PossibleDefinitions.objectTypes :=
      List.mem_map.mpr ⟨group, hgroup, rfl⟩
    rw [hobjects] at hkey
    simp only [List.mem_map] at hkey
    rcases hkey with ⟨objectType, _hobjectType, heq⟩
    exact ⟨objectType, heq.symm⟩

private theorem positionInvariant_of_decoderGroupsMergeInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition)
    (hinvariant : decoderGroupsMergeInvariant schema support parentType
      position.possibleDefinitions) :
    DecoderPositionInvariant schema support parentType position := by
  have buildObjects : ∀ groups : List PossibleDefinitions,
      (∀ group ∈ groups, ∃ objectType, group.objectTypes = [objectType]) ->
      ∃ objects : List GroundObject,
        groups.map PossibleDefinitions.objectTypes =
          objects.map (fun objectType => [objectType]) := by
    intro groups hsingletons
    induction groups with
    | nil => exact ⟨[], rfl⟩
    | cons group rest ih =>
        rcases hsingletons group (by simp) with ⟨objectType, hobjectType⟩
        rcases ih (fun candidate hcandidate => hsingletons candidate
          (List.mem_cons_of_mem group hcandidate)) with ⟨objects, hobjects⟩
        exact ⟨objectType :: objects, by simp [hobjectType, hobjects]⟩
  rcases buildObjects position.possibleDefinitions hinvariant.2.1 with
    ⟨objects, hobjects⟩
  refine ⟨objects, hobjects, ?_, hinvariant.2.2⟩
  apply nodup_of_singletonMap_nodup
  rw [← hobjects]
  exact hinvariant.1

private theorem key_mem_insertPossibleDefinitions
    (incoming : PossibleDefinitions) (key : List GroundObject) :
    ∀ groups,
      key ∈ (insertPossibleDefinitions incoming groups).map
          PossibleDefinitions.objectTypes ↔
        key ∈ groups.map PossibleDefinitions.objectTypes
          ∨ key = incoming.objectTypes
  | [] => by simp [insertPossibleDefinitions]
  | current :: rest => by
      unfold insertPossibleDefinitions
      by_cases heq : current.objectTypes = incoming.objectTypes
      · have hbeq : (current.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        rw [if_pos hbeq]
        simp only [PossibleDefinitions.objectTypes, List.map_cons, List.mem_cons]
        constructor
        · intro h
          exact Or.inl h
        · intro h
          cases h with
          | inl h => exact h
          | inr h => exact Or.inl (h.trans heq.symm)
      · have hbeq : (current.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.map_cons,
          List.mem_cons]
        rw [key_mem_insertPossibleDefinitions incoming key rest]
        simp only [or_assoc]

private theorem insertPossibleDefinitions_preserves
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (incoming : PossibleDefinitions)
    (hincoming : DecoderGroupInvariant schema support parentType incoming)
    (hincomingSingleton : ∃ objectType, incoming.objectTypes = [objectType]) :
    ∀ groups,
      decoderGroupsMergeInvariant schema support parentType groups ->
      (∀ current ∈ groups,
        PossibleDefinitionsMergeCompatible current incoming) ->
      decoderGroupsMergeInvariant schema support parentType
        (insertPossibleDefinitions incoming groups)
  | [], _hgroups, _hcompatible => by
      refine ⟨by simp [insertPossibleDefinitions], ?_, ?_⟩
      · intro group hgroup
        simp [insertPossibleDefinitions] at hgroup
        subst group
        exact hincomingSingleton
      · simpa [insertPossibleDefinitions] using hincoming
  | current :: rest, hgroups, hcompatible => by
      have hcurrentSingleton := hgroups.2.1 current (by simp)
      have hcurrentInvariant := hgroups.2.2 current (by simp)
      have hrest : decoderGroupsMergeInvariant schema support parentType rest := by
        refine ⟨(List.nodup_cons.mp hgroups.1).2, ?_, ?_⟩
        · intro group hgroup
          exact hgroups.2.1 group (List.mem_cons_of_mem current hgroup)
        · intro group hgroup
          exact hgroups.2.2 group (List.mem_cons_of_mem current hgroup)
      unfold insertPossibleDefinitions
      by_cases heq : current.objectTypes = incoming.objectTypes
      · have hbeq : (current.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        simp only [hbeq, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [List.map_cons, PossibleDefinitions.objectTypes] using
            hgroups.1
        · intro group hgroup
          simp only [List.mem_cons] at hgroup
          cases hgroup with
          | inl hgroup =>
              subst group
              exact hcurrentSingleton
          | inr hgroup => exact hrest.2.1 group hgroup
        · intro group hgroup
          simp only [List.mem_cons] at hgroup
          cases hgroup with
          | inl hgroup =>
              subst group
              exact mergedGroupInvariant schema support parentType current
                incoming heq hcurrentInvariant hincoming
                (hcompatible current (by simp))
          | inr hgroup => exact hrest.2.2 group hgroup
      · have hbeq : (current.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        have hinsert := insertPossibleDefinitions_preserves schema support
          parentType incoming hincoming hincomingSingleton rest hrest
          (fun group hgroup => hcompatible group
            (List.mem_cons_of_mem current hgroup))
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.map_cons, List.nodup_cons]
          constructor
          · intro hmember
            rw [key_mem_insertPossibleDefinitions] at hmember
            cases hmember with
            | inl hmember => exact (List.nodup_cons.mp hgroups.1).1 hmember
            | inr hkey => exact heq hkey
          · exact hinsert.1
        · intro group hgroup
          simp only [List.mem_cons] at hgroup
          cases hgroup with
          | inl hgroup =>
              subst group
              exact hcurrentSingleton
          | inr hgroup => exact hinsert.2.1 group hgroup
        · intro group hgroup
          simp only [List.mem_cons] at hgroup
          cases hgroup with
          | inl hgroup =>
              subst group
              exact hcurrentInvariant
          | inr hgroup => exact hinsert.2.2 group hgroup

private def groupsMergeCompatible
    (left right : List PossibleDefinitions) : Prop :=
  ∀ leftGroup ∈ left, ∀ rightGroup ∈ right,
    PossibleDefinitionsMergeCompatible leftGroup rightGroup

private theorem insertPossibleDefinitions_compatible_with
    (incoming : PossibleDefinitions) (current future : List PossibleDefinitions)
    (hcurrent : groupsMergeCompatible current future)
    (hincomingKey : ∀ futureGroup ∈ future,
      incoming.objectTypes ≠ futureGroup.objectTypes) :
    groupsMergeCompatible (insertPossibleDefinitions incoming current) future := by
  intro resultGroup hresult futureGroup hfuture
  induction current with
  | nil =>
      simp only [insertPossibleDefinitions, List.mem_singleton] at hresult
      subst resultGroup
      intro heq
      exact False.elim ((hincomingKey futureGroup hfuture) heq)
  | cons currentGroup rest ih =>
      unfold insertPossibleDefinitions at hresult
      by_cases heq : currentGroup.objectTypes = incoming.objectTypes
      · have hbeq : (currentGroup.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        rw [if_pos hbeq] at hresult
        simp only [List.mem_cons] at hresult
        cases hresult with
        | inl hresult =>
            subst resultGroup
            intro hkey
            exact False.elim ((hincomingKey futureGroup hfuture)
              (heq.symm.trans hkey))
        | inr hresult =>
            exact hcurrent resultGroup (List.mem_cons_of_mem currentGroup hresult)
              futureGroup hfuture
      · have hbeq : (currentGroup.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        rw [if_neg (by simpa using hbeq)] at hresult
        simp only [List.mem_cons] at hresult
        cases hresult with
        | inl hresult =>
            subst resultGroup
            exact hcurrent currentGroup (by simp) futureGroup hfuture
        | inr hresult =>
            exact ih
              (fun leftGroup hleft => hcurrent leftGroup
                (List.mem_cons_of_mem currentGroup hleft)) hresult

private theorem foldPossibleDefinitions_preserves
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name) :
    ∀ incoming current,
      decoderGroupsMergeInvariant schema support parentType current ->
      decoderGroupsMergeInvariant schema support parentType incoming ->
      groupsMergeCompatible current incoming ->
      decoderGroupsMergeInvariant schema support parentType
        (incoming.foldl
          (fun merged group => insertPossibleDefinitions group merged) current)
  | [], current, hcurrent, _hincoming, _hcompatible => by
      simpa using hcurrent
  | incomingGroup :: rest, current, hcurrent, hincoming, hcompatible => by
      have hincomingGroup := hincoming.2.2 incomingGroup (by simp)
      have hincomingSingleton := hincoming.2.1 incomingGroup (by simp)
      have hrest : decoderGroupsMergeInvariant schema support parentType rest := by
        refine ⟨(List.nodup_cons.mp hincoming.1).2, ?_, ?_⟩
        · intro group hgroup
          exact hincoming.2.1 group
            (List.mem_cons_of_mem incomingGroup hgroup)
        · intro group hgroup
          exact hincoming.2.2 group
            (List.mem_cons_of_mem incomingGroup hgroup)
      have hinsert := insertPossibleDefinitions_preserves schema support
        parentType incomingGroup hincomingGroup hincomingSingleton current
        hcurrent (fun group hgroup =>
          hcompatible group hgroup incomingGroup (by simp))
      apply foldPossibleDefinitions_preserves schema support parentType rest
        (insertPossibleDefinitions incomingGroup current) hinsert hrest
      apply insertPossibleDefinitions_compatible_with incomingGroup current rest
      · intro leftGroup hleft rightGroup hright
        exact hcompatible leftGroup hleft rightGroup
          (List.mem_cons_of_mem incomingGroup hright)
      · intro futureGroup hfuture heq
        exact (List.nodup_cons.mp hincoming.1).1
          (List.mem_map.mpr ⟨futureGroup, hfuture, heq.symm⟩)

private theorem mergePossibleDefinitions_preserves
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (left right : ResponsePosition)
    (hleft : DecoderPositionInvariant schema support parentType left)
    (hright : DecoderPositionInvariant schema support parentType right)
    (hcompatible : groupsMergeCompatible left.possibleDefinitions
      right.possibleDefinitions) :
    DecoderPositionInvariant schema support parentType
      (.mk left.responseName
        (mergePossibleDefinitions left.possibleDefinitions
          right.possibleDefinitions)) := by
  apply positionInvariant_of_decoderGroupsMergeInvariant schema support
    parentType
  unfold mergePossibleDefinitions
  exact foldPossibleDefinitions_preserves schema support parentType
    right.possibleDefinitions left.possibleDefinitions
    (decoderGroupsMergeInvariant_of_position schema support parentType left hleft)
    (decoderGroupsMergeInvariant_of_position schema support parentType right hright)
    hcompatible

private theorem responseName_mem_insertResponsePosition
    (incoming : ResponsePosition) (responseName : Name) :
    ∀ positions,
      responseName ∈ (insertResponsePosition incoming positions).map
          ResponsePosition.responseName ↔
        responseName ∈ positions.map ResponsePosition.responseName
          ∨ responseName = incoming.responseName
  | [] => by simp [insertResponsePosition]
  | current :: rest => by
      unfold insertResponsePosition
      by_cases heq : current.responseName = incoming.responseName
      · have hbeq : (current.responseName == incoming.responseName) = true := by
          simp [heq]
        rw [if_pos hbeq]
        simp only [ResponsePosition.responseName, List.map_cons, List.mem_cons]
        constructor
        · intro h
          exact Or.inl h
        · intro h
          cases h with
          | inl h => exact h
          | inr h => exact Or.inl (h.trans heq.symm)
      · have hbeq : (current.responseName == incoming.responseName) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.map_cons,
          List.mem_cons]
        rw [responseName_mem_insertResponsePosition incoming responseName rest]
        simp only [or_assoc]

private theorem insertResponsePosition_preserves
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (incoming : ResponsePosition)
    (hincoming : DecoderPositionInvariant schema support parentType incoming) :
    ∀ positions,
      (positions.map ResponsePosition.responseName).Nodup ->
      decoderPositionsInvariant schema support parentType positions ->
      (∀ current ∈ positions,
        ResponsePositionMergeCompatible current incoming) ->
      ((insertResponsePosition incoming positions).map
          ResponsePosition.responseName).Nodup
      ∧ decoderPositionsInvariant schema support parentType
          (insertResponsePosition incoming positions)
  | [], _hnames, _hpositions, _hcompatible => by
      constructor
      · simp [insertResponsePosition]
      · simpa [insertResponsePosition, decoderPositionsInvariant] using hincoming
  | current :: rest, hnames, hpositions, hcompatible => by
      have hcurrent := hpositions current (by simp)
      have hrest : decoderPositionsInvariant schema support parentType rest :=
        fun position hposition => hpositions position
          (List.mem_cons_of_mem current hposition)
      unfold insertResponsePosition
      by_cases heq : current.responseName = incoming.responseName
      · have hbeq : (current.responseName == incoming.responseName) = true := by
          simp [heq]
        simp only [hbeq, ↓reduceIte]
        constructor
        · simpa only [List.map_cons, ResponsePosition.responseName] using hnames
        · intro position hposition
          simp only [List.mem_cons] at hposition
          cases hposition with
          | inl hposition =>
              subst position
              exact mergePossibleDefinitions_preserves schema support parentType
                current incoming hcurrent hincoming
                (hcompatible current (by simp) heq)
          | inr hposition => exact hrest position hposition
      · have hbeq : (current.responseName == incoming.responseName) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        have hinsert := insertResponsePosition_preserves schema support parentType
          incoming hincoming rest (List.nodup_cons.mp hnames).2 hrest
          (fun position hposition => hcompatible position
            (List.mem_cons_of_mem current hposition))
        constructor
        · simp only [List.map_cons, List.nodup_cons]
          constructor
          · intro hmember
            rw [responseName_mem_insertResponsePosition] at hmember
            cases hmember with
            | inl hmember => exact (List.nodup_cons.mp hnames).1 hmember
            | inr hname => exact heq hname
          · exact hinsert.1
        · intro position hposition
          simp only [List.mem_cons] at hposition
          cases hposition with
          | inl hposition =>
              subst position
              exact hcurrent
          | inr hposition => exact hinsert.2 position hposition

private theorem insertResponsePosition_compatible_with
    (incoming : ResponsePosition) (current future : List ResponsePosition)
    (hcurrent : ∀ currentPosition ∈ current,
      ∀ futurePosition ∈ future,
        ResponsePositionMergeCompatible currentPosition futurePosition)
    (hincomingName : ∀ futurePosition ∈ future,
      incoming.responseName ≠ futurePosition.responseName) :
    ∀ resultPosition ∈ insertResponsePosition incoming current,
      ∀ futurePosition ∈ future,
        ResponsePositionMergeCompatible resultPosition futurePosition := by
  intro resultPosition hresult futurePosition hfuture
  induction current with
  | nil =>
      simp only [insertResponsePosition, List.mem_singleton] at hresult
      subst resultPosition
      intro heq
      exact False.elim ((hincomingName futurePosition hfuture) heq)
  | cons currentPosition rest ih =>
      unfold insertResponsePosition at hresult
      by_cases heq : currentPosition.responseName = incoming.responseName
      · have hbeq :
          (currentPosition.responseName == incoming.responseName) = true := by
            simp [heq]
        rw [if_pos hbeq] at hresult
        simp only [List.mem_cons] at hresult
        cases hresult with
        | inl hresult =>
            subst resultPosition
            intro hname
            exact False.elim ((hincomingName futurePosition hfuture)
              (heq.symm.trans hname))
        | inr hresult =>
            exact hcurrent resultPosition
              (List.mem_cons_of_mem currentPosition hresult)
              futurePosition hfuture
      · have hbeq :
          (currentPosition.responseName == incoming.responseName) = false := by
            simp [heq]
        rw [if_neg (by simpa using hbeq)] at hresult
        simp only [List.mem_cons] at hresult
        cases hresult with
        | inl hresult =>
            subst resultPosition
            exact hcurrent currentPosition (by simp) futurePosition hfuture
        | inr hresult =>
            exact ih
              (fun leftPosition hleft => hcurrent leftPosition
                (List.mem_cons_of_mem currentPosition hleft)) hresult

private theorem foldResponsePositions_preserves
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name) :
    ∀ incoming current,
      (current.map ResponsePosition.responseName).Nodup ->
      decoderPositionsInvariant schema support parentType current ->
      (incoming.map ResponsePosition.responseName).Nodup ->
      decoderPositionsInvariant schema support parentType incoming ->
      (∀ currentPosition ∈ current, ∀ incomingPosition ∈ incoming,
        ResponsePositionMergeCompatible currentPosition incomingPosition) ->
      let result := incoming.foldl
        (fun merged position => insertResponsePosition position merged) current
      (result.map ResponsePosition.responseName).Nodup
        ∧ decoderPositionsInvariant schema support parentType result
  | [], current, hcurrentNames, hcurrent, _hincomingNames, _hincoming,
      _hcompatible => by
        exact ⟨hcurrentNames, hcurrent⟩
  | incomingPosition :: rest, current, hcurrentNames, hcurrent,
      hincomingNames, hincoming, hcompatible => by
        have hincomingPosition := hincoming incomingPosition (by simp)
        have hrest : decoderPositionsInvariant schema support parentType rest :=
          fun position hposition => hincoming position
            (List.mem_cons_of_mem incomingPosition hposition)
        have hinsert := insertResponsePosition_preserves schema support
          parentType incomingPosition hincomingPosition current hcurrentNames
          hcurrent (fun position hposition =>
            hcompatible position hposition incomingPosition (by simp))
        apply foldResponsePositions_preserves schema support parentType rest
          (insertResponsePosition incomingPosition current) hinsert.1 hinsert.2
          (List.nodup_cons.mp hincomingNames).2 hrest
        apply insertResponsePosition_compatible_with incomingPosition current rest
        · intro currentPosition hcurrentPosition futurePosition hfuturePosition
          exact hcompatible currentPosition hcurrentPosition futurePosition
            (List.mem_cons_of_mem incomingPosition hfuturePosition)
        · intro futurePosition hfuturePosition heq
          exact (List.nodup_cons.mp hincomingNames).1
            (List.mem_map.mpr ⟨futurePosition, hfuturePosition, heq.symm⟩)

/-- A response-shape merge preserves the decoder image invariant exactly when
all actual cross-shape collisions are locally compatible. -/
theorem mergeResponseShapes_decoderShapeInvariant
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (left right : ResponseShape)
    (hleft : DecoderShapeInvariant schema support parentType left)
    (hright : DecoderShapeInvariant schema support parentType right)
    (hcompatible : MergeCompatible left right) :
    DecoderShapeInvariant schema support parentType
      (mergeResponseShapes left right) := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold DecoderShapeInvariant at hleft hright
          unfold mergeResponseShapes DecoderShapeInvariant
          exact foldResponsePositions_preserves schema support parentType
            rightPositions leftPositions hleft.1 hleft.2 hright.1 hright.2
            hcompatible

/-- Every definition in a shape has the specified clause. -/
def ShapeClausesEqual (clause : Clause) (shape : ResponseShape) : Prop :=
  ∀ position ∈ shape.positions,
    ∀ group ∈ position.possibleDefinitions,
      ∀ definition ∈ group.definitions,
        definition.clause = clause

/-- Every response name in a shape belongs to the specified set. -/
def ShapeResponseNamesIn (allowed : List Name) (shape : ResponseShape) : Prop :=
  ∀ position ∈ shape.positions, position.responseName ∈ allowed

/-- Every concrete object key in a shape belongs to the specified set. -/
def ShapeObjectTypesIn
    (allowed : List GroundObject) (shape : ResponseShape) : Prop :=
  ∀ position ∈ shape.positions,
    ∀ group ∈ position.possibleDefinitions,
      ∀ objectType ∈ group.objectTypes, objectType ∈ allowed

private def groupsClausesEqual
    (clause : Clause) (groups : List PossibleDefinitions) : Prop :=
  ∀ group ∈ groups, ∀ definition ∈ group.definitions,
    definition.clause = clause

private theorem insertPossibleDefinitions_clausesEqual
    (clause : Clause) (incoming : PossibleDefinitions)
    (hincoming : ∀ definition ∈ incoming.definitions,
      definition.clause = clause) :
    ∀ groups,
      groupsClausesEqual clause groups ->
      groupsClausesEqual clause (insertPossibleDefinitions incoming groups)
  | [], _hgroups => by
      intro group hgroup
      simp only [insertPossibleDefinitions, List.mem_singleton] at hgroup
      subst group
      exact hincoming
  | current :: rest, hgroups => by
      intro group hgroup
      unfold insertPossibleDefinitions at hgroup
      by_cases heq : current.objectTypes = incoming.objectTypes
      · have hbeq : (current.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        rw [if_pos hbeq] at hgroup
        simp only [List.mem_cons] at hgroup
        cases hgroup with
        | inl hgroup =>
            subst group
            intro definition hdefinition
            simp only [PossibleDefinitions.definitions, List.mem_append] at hdefinition
            cases hdefinition with
            | inl hdefinition => exact hgroups current (by simp) definition hdefinition
            | inr hdefinition => exact hincoming definition hdefinition
        | inr hgroup =>
            exact hgroups group (List.mem_cons_of_mem current hgroup)
      · have hbeq : (current.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hgroup
        simp only [List.mem_cons] at hgroup
        cases hgroup with
        | inl hgroup =>
            subst group
            exact hgroups current (by simp)
        | inr hgroup =>
            exact insertPossibleDefinitions_clausesEqual clause incoming hincoming
              rest (fun candidate hcandidate => hgroups candidate
                (List.mem_cons_of_mem current hcandidate)) group hgroup

private theorem mergePossibleDefinitions_clausesEqual
    (clause : Clause) (left right : List PossibleDefinitions)
    (hleft : groupsClausesEqual clause left)
    (hright : groupsClausesEqual clause right) :
    groupsClausesEqual clause (mergePossibleDefinitions left right) := by
  unfold mergePossibleDefinitions
  induction right generalizing left with
  | nil => exact hleft
  | cons incoming rest ih =>
      apply ih
      · apply insertPossibleDefinitions_clausesEqual clause incoming
        · exact hright incoming (by simp)
        · exact hleft
      · intro group hgroup
        exact hright group (List.mem_cons_of_mem incoming hgroup)

private theorem insertResponsePosition_clausesEqual
    (clause : Clause) (incoming : ResponsePosition)
    (hincoming : groupsClausesEqual clause incoming.possibleDefinitions) :
    ∀ positions,
      (∀ position ∈ positions,
        groupsClausesEqual clause position.possibleDefinitions) ->
      ∀ position ∈ insertResponsePosition incoming positions,
        groupsClausesEqual clause position.possibleDefinitions
  | [], _hpositions => by
      intro position hposition
      simp only [insertResponsePosition, List.mem_singleton] at hposition
      subst position
      exact hincoming
  | current :: rest, hpositions => by
      intro position hposition
      unfold insertResponsePosition at hposition
      by_cases heq : current.responseName = incoming.responseName
      · have hbeq : (current.responseName == incoming.responseName) = true := by
          simp [heq]
        rw [if_pos hbeq] at hposition
        simp only [List.mem_cons] at hposition
        cases hposition with
        | inl hposition =>
            subst position
            exact mergePossibleDefinitions_clausesEqual clause
              current.possibleDefinitions incoming.possibleDefinitions
              (hpositions current (by simp)) hincoming
        | inr hposition =>
            exact hpositions position (List.mem_cons_of_mem current hposition)
      · have hbeq : (current.responseName == incoming.responseName) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hposition
        simp only [List.mem_cons] at hposition
        cases hposition with
        | inl hposition =>
            subst position
            exact hpositions current (by simp)
        | inr hposition =>
            exact insertResponsePosition_clausesEqual clause incoming hincoming
              rest (fun candidate hcandidate => hpositions candidate
                (List.mem_cons_of_mem current hcandidate)) position hposition

/-- Uniform definition-clause metadata is preserved by merge. -/
theorem ShapeClausesEqual.merge
    (clause : Clause) (left right : ResponseShape)
    (hleft : ShapeClausesEqual clause left)
    (hright : ShapeClausesEqual clause right) :
    ShapeClausesEqual clause (mergeResponseShapes left right) := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold mergeResponseShapes ShapeClausesEqual
          induction rightPositions generalizing leftPositions with
          | nil => exact hleft
          | cons incoming rest ih =>
              apply ih
              · apply insertResponsePosition_clausesEqual clause incoming
                · exact hright incoming (List.mem_cons_self)
                · exact hleft
              · intro position hposition
                exact hright position
                  (List.mem_cons_of_mem incoming hposition)

private theorem insertResponsePosition_responseNamesIn
    (allowed : List Name) (incoming : ResponsePosition)
    (hincoming : incoming.responseName ∈ allowed)
    (positions : List ResponsePosition)
    (hpositions : ∀ position ∈ positions,
      position.responseName ∈ allowed) :
    ∀ position ∈ insertResponsePosition incoming positions,
      position.responseName ∈ allowed := by
  intro position hposition
  have hname : position.responseName ∈
      (insertResponsePosition incoming positions).map
        ResponsePosition.responseName :=
    List.mem_map.mpr ⟨position, hposition, rfl⟩
  rw [responseName_mem_insertResponsePosition] at hname
  cases hname with
  | inl hname =>
      simp only [List.mem_map] at hname
      rcases hname with ⟨source, hsource, heq⟩
      exact heq ▸ hpositions source hsource
  | inr hname => exact hname ▸ hincoming

/-- Response-name membership metadata is preserved by merge. -/
theorem ShapeResponseNamesIn.merge
    (allowed : List Name) (left right : ResponseShape)
    (hleft : ShapeResponseNamesIn allowed left)
    (hright : ShapeResponseNamesIn allowed right) :
    ShapeResponseNamesIn allowed (mergeResponseShapes left right) := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold mergeResponseShapes ShapeResponseNamesIn
          induction rightPositions generalizing leftPositions with
          | nil => exact hleft
          | cons incoming rest ih =>
              apply ih
              · exact insertResponsePosition_responseNamesIn allowed incoming
                  (hright incoming List.mem_cons_self) leftPositions hleft
              · intro position hposition
                exact hright position
                  (List.mem_cons_of_mem incoming hposition)

private def groupsObjectTypesIn
    (allowed : List GroundObject) (groups : List PossibleDefinitions) : Prop :=
  ∀ group ∈ groups, ∀ objectType ∈ group.objectTypes, objectType ∈ allowed

private theorem insertPossibleDefinitions_objectTypesIn
    (allowed : List GroundObject) (incoming : PossibleDefinitions)
    (hincoming : ∀ objectType ∈ incoming.objectTypes, objectType ∈ allowed) :
    ∀ groups,
      groupsObjectTypesIn allowed groups ->
      groupsObjectTypesIn allowed (insertPossibleDefinitions incoming groups)
  | [], _hgroups => by
      intro group hgroup
      simp only [insertPossibleDefinitions, List.mem_singleton] at hgroup
      subst group
      exact hincoming
  | current :: rest, hgroups => by
      intro group hgroup
      unfold insertPossibleDefinitions at hgroup
      by_cases heq : current.objectTypes = incoming.objectTypes
      · have hbeq : (current.objectTypes == incoming.objectTypes) = true := by
          simp [heq]
        rw [if_pos hbeq] at hgroup
        simp only [List.mem_cons] at hgroup
        cases hgroup with
        | inl hgroup =>
            subst group
            exact hgroups current List.mem_cons_self
        | inr hgroup =>
            exact hgroups group (List.mem_cons_of_mem current hgroup)
      · have hbeq : (current.objectTypes == incoming.objectTypes) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hgroup
        simp only [List.mem_cons] at hgroup
        cases hgroup with
        | inl hgroup =>
            subst group
            exact hgroups current List.mem_cons_self
        | inr hgroup =>
            exact insertPossibleDefinitions_objectTypesIn allowed incoming hincoming
              rest (fun candidate hcandidate => hgroups candidate
                (List.mem_cons_of_mem current hcandidate)) group hgroup

private theorem mergePossibleDefinitions_objectTypesIn
    (allowed : List GroundObject) (left right : List PossibleDefinitions)
    (hleft : groupsObjectTypesIn allowed left)
    (hright : groupsObjectTypesIn allowed right) :
    groupsObjectTypesIn allowed (mergePossibleDefinitions left right) := by
  unfold mergePossibleDefinitions
  induction right generalizing left with
  | nil => exact hleft
  | cons incoming rest ih =>
      apply ih
      · exact insertPossibleDefinitions_objectTypesIn allowed incoming
          (hright incoming List.mem_cons_self) left hleft
      · intro group hgroup
        exact hright group (List.mem_cons_of_mem incoming hgroup)

private theorem insertResponsePosition_objectTypesIn
    (allowed : List GroundObject) (incoming : ResponsePosition)
    (hincoming : groupsObjectTypesIn allowed incoming.possibleDefinitions) :
    ∀ positions,
      (∀ position ∈ positions,
        groupsObjectTypesIn allowed position.possibleDefinitions) ->
      ∀ position ∈ insertResponsePosition incoming positions,
        groupsObjectTypesIn allowed position.possibleDefinitions
  | [], _hpositions => by
      intro position hposition
      simp only [insertResponsePosition, List.mem_singleton] at hposition
      subst position
      exact hincoming
  | current :: rest, hpositions => by
      intro position hposition
      unfold insertResponsePosition at hposition
      by_cases heq : current.responseName = incoming.responseName
      · have hbeq : (current.responseName == incoming.responseName) = true := by
          simp [heq]
        rw [if_pos hbeq] at hposition
        simp only [List.mem_cons] at hposition
        cases hposition with
        | inl hposition =>
            subst position
            exact mergePossibleDefinitions_objectTypesIn allowed
              current.possibleDefinitions incoming.possibleDefinitions
              (hpositions current List.mem_cons_self) hincoming
        | inr hposition =>
            exact hpositions position (List.mem_cons_of_mem current hposition)
      · have hbeq : (current.responseName == incoming.responseName) = false := by
          simp [heq]
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hposition
        simp only [List.mem_cons] at hposition
        cases hposition with
        | inl hposition =>
            subst position
            exact hpositions current List.mem_cons_self
        | inr hposition =>
            exact insertResponsePosition_objectTypesIn allowed incoming hincoming
              rest (fun candidate hcandidate => hpositions candidate
                (List.mem_cons_of_mem current hcandidate)) position hposition

/-- Concrete-object membership metadata is preserved by merge. -/
theorem ShapeObjectTypesIn.merge
    (allowed : List GroundObject) (left right : ResponseShape)
    (hleft : ShapeObjectTypesIn allowed left)
    (hright : ShapeObjectTypesIn allowed right) :
    ShapeObjectTypesIn allowed (mergeResponseShapes left right) := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold mergeResponseShapes ShapeObjectTypesIn
          induction rightPositions generalizing leftPositions with
          | nil => exact hleft
          | cons incoming rest ih =>
              apply ih
              · exact insertResponsePosition_objectTypesIn allowed incoming
                  (hright incoming List.mem_cons_self) leftPositions hleft
              · intro position hposition
                exact hright position
                  (List.mem_cons_of_mem incoming hposition)

/-- Shapes whose response names lie in disjoint allowed sets have no root
collision and are therefore merge-compatible. -/
theorem mergeCompatible_of_responseNamesIn_disjoint
    (leftAllowed rightAllowed : List Name) (left right : ResponseShape)
    (hdisjoint : ∀ responseName ∈ leftAllowed,
      responseName ∉ rightAllowed)
    (hleft : ShapeResponseNamesIn leftAllowed left)
    (hright : ShapeResponseNamesIn rightAllowed right) :
    MergeCompatible left right := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          intro leftPosition hleftPosition rightPosition hrightPosition heq
          exact False.elim (hdisjoint leftPosition.responseName
            (hleft leftPosition hleftPosition)
            (heq ▸ hright rightPosition hrightPosition))

/-- Decoder shapes whose singleton object keys lie in disjoint allowed sets
cannot collide at the possible-definition-group level. -/
theorem mergeCompatible_of_objectTypesIn_disjoint
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (leftAllowed rightAllowed : List GroundObject)
    (left right : ResponseShape)
    (hdisjoint : ∀ objectType ∈ leftAllowed, objectType ∉ rightAllowed)
    (hleftInvariant : DecoderShapeInvariant schema support parentType left)
    (hrightInvariant : DecoderShapeInvariant schema support parentType right)
    (hleft : ShapeObjectTypesIn leftAllowed left)
    (hright : ShapeObjectTypesIn rightAllowed right) :
    MergeCompatible left right := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          intro leftPosition hleftPosition rightPosition hrightPosition _hname
          intro leftGroup hleftGroup rightGroup hrightGroup
          intro hkeys
          have hleftPositionInvariant := hleftInvariant.2 leftPosition hleftPosition
          have hrightPositionInvariant := hrightInvariant.2 rightPosition hrightPosition
          rcases (decoderGroupsMergeInvariant_of_position schema support parentType
            leftPosition hleftPositionInvariant).2.1 leftGroup hleftGroup with
            ⟨leftObject, hleftKey⟩
          rcases (decoderGroupsMergeInvariant_of_position schema support parentType
            rightPosition hrightPositionInvariant).2.1 rightGroup hrightGroup with
            ⟨rightObject, hrightKey⟩
          have hobjects : leftObject = rightObject := by
            rw [hleftKey, hrightKey] at hkeys
            exact (List.cons.inj hkeys).1
          exact False.elim (hdisjoint leftObject
            (hleft leftPosition hleftPosition leftGroup hleftGroup leftObject
              (by simp [hleftKey]))
            (hobjects ▸ hright rightPosition hrightPosition rightGroup hrightGroup
              rightObject (by simp [hrightKey])))

/-- Uniform but distinct root-branch clauses make every definition-list
collision disjoint. -/
theorem mergeCompatible_of_distinct_equalClauses
    (leftClause rightClause : Clause) (left right : ResponseShape)
    (hne : leftClause ≠ rightClause)
    (hleft : ShapeClausesEqual leftClause left)
    (hright : ShapeClausesEqual rightClause right) :
    MergeCompatible left right := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          intro leftPosition hleftPosition rightPosition hrightPosition _hname
          intro leftGroup hleftGroup rightGroup hrightGroup _hkeys
          intro leftDefinitionClause hleftClause
          intro rightDefinitionClause hrightClause
          simp only [List.mem_map] at hleftClause hrightClause
          rcases hleftClause with
            ⟨leftDefinition, hleftDefinition, hleftDefinitionClause⟩
          rcases hrightClause with
            ⟨rightDefinition, hrightDefinition, hrightDefinitionClause⟩
          subst leftDefinitionClause
          subst rightDefinitionClause
          intro heq
          exact hne ((hleft leftPosition hleftPosition leftGroup hleftGroup
            leftDefinition hleftDefinition).symm.trans
              (heq.trans (hright rightPosition hrightPosition rightGroup
                hrightGroup rightDefinition hrightDefinition)))

end ResponseShape

end GraphQL
