import Proofs.GraphQL.Theories.ResponseShape.Compute.Merge

/-!
Clause-exclusion facts for response-shape merges.
-/

namespace GraphQL

namespace ResponseShape

/-- No root definition in the shape has the specified clause. -/
def ShapeExcludesClause (clause : Clause) (shape : ResponseShape) : Prop :=
  ∀ position ∈ shape.positions,
    ∀ group ∈ position.possibleDefinitions,
      ∀ definition ∈ group.definitions,
        definition.clause ≠ clause

/-- The empty response shape excludes every clause. -/
theorem ShapeExcludesClause.empty (clause : Clause) :
    ShapeExcludesClause clause (.object []) := by
  simp [ShapeExcludesClause, ResponseShape.positions]

/-- A shape whose definitions all have one clause excludes every distinct
clause. -/
theorem ShapeClausesEqual.excludes
    (current excluded : Clause) (shape : ResponseShape)
    (hcurrent : ShapeClausesEqual current shape)
    (hne : current ≠ excluded) :
    ShapeExcludesClause excluded shape := by
  intro position hposition group hgroup definition hdefinition heq
  exact hne ((hcurrent position hposition group hgroup definition
    hdefinition).symm.trans heq)

private def groupsExcludeClause
    (clause : Clause) (groups : List PossibleDefinitions) : Prop :=
  ∀ group ∈ groups, ∀ definition ∈ group.definitions,
    definition.clause ≠ clause

private theorem insertPossibleDefinitions_excludesClause
    (clause : Clause) (incoming : PossibleDefinitions)
    (hincoming : ∀ definition ∈ incoming.definitions,
      definition.clause ≠ clause) :
    ∀ groups,
      groupsExcludeClause clause groups ->
      groupsExcludeClause clause (insertPossibleDefinitions incoming groups)
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
            | inl hdefinition =>
                exact hgroups current (by simp) definition hdefinition
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
            exact insertPossibleDefinitions_excludesClause clause incoming
              hincoming rest (fun candidate hcandidate => hgroups candidate
                (List.mem_cons_of_mem current hcandidate)) group hgroup

private theorem mergePossibleDefinitions_excludesClause
    (clause : Clause) (left right : List PossibleDefinitions)
    (hleft : groupsExcludeClause clause left)
    (hright : groupsExcludeClause clause right) :
    groupsExcludeClause clause (mergePossibleDefinitions left right) := by
  unfold mergePossibleDefinitions
  induction right generalizing left with
  | nil => exact hleft
  | cons incoming rest ih =>
      apply ih
      · apply insertPossibleDefinitions_excludesClause clause incoming
        · exact hright incoming (by simp)
        · exact hleft
      · intro group hgroup
        exact hright group (List.mem_cons_of_mem incoming hgroup)

private theorem insertResponsePosition_excludesClause
    (clause : Clause) (incoming : ResponsePosition)
    (hincoming : groupsExcludeClause clause incoming.possibleDefinitions) :
    ∀ positions,
      (∀ position ∈ positions,
        groupsExcludeClause clause position.possibleDefinitions) ->
      ∀ position ∈ insertResponsePosition incoming positions,
        groupsExcludeClause clause position.possibleDefinitions
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
            exact mergePossibleDefinitions_excludesClause clause
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
            exact insertResponsePosition_excludesClause clause incoming hincoming
              rest (fun candidate hcandidate => hpositions candidate
                (List.mem_cons_of_mem current hcandidate)) position hposition

/-- Clause exclusion is preserved by response-shape merge. -/
theorem ShapeExcludesClause.merge
    (clause : Clause) (left right : ResponseShape)
    (hleft : ShapeExcludesClause clause left)
    (hright : ShapeExcludesClause clause right) :
    ShapeExcludesClause clause (mergeResponseShapes left right) := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold mergeResponseShapes ShapeExcludesClause
          induction rightPositions generalizing leftPositions with
          | nil => exact hleft
          | cons incoming rest ih =>
              apply ih
              · apply insertResponsePosition_excludesClause clause incoming
                · exact hright incoming List.mem_cons_self
                · exact hleft
              · intro position hposition
                exact hright position
                  (List.mem_cons_of_mem incoming hposition)

/-- A uniform left shape is merge-compatible with a right shape which excludes
that uniform clause. -/
theorem mergeCompatible_of_clausesEqual_excludes
    (current : Clause) (left right : ResponseShape)
    (hleft : ShapeClausesEqual current left)
    (hright : ShapeExcludesClause current right) :
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
          exact hright rightPosition hrightPosition rightGroup hrightGroup
            rightDefinition hrightDefinition
            ((hleft leftPosition hleftPosition leftGroup hleftGroup
              leftDefinition hleftDefinition).symm.trans heq).symm

end ResponseShape

end GraphQL
