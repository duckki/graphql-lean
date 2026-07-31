import Proofs.GraphQL.Theories.ResponseShape.Compute.Minterm
import GraphQL.Theories.ResponseShape.Validity

/-!
Activity bounds for response positions whose possible-definition groups form a
singleton partition of concrete object types.
-/

namespace GraphQL

namespace ResponseShape

private theorem definitionsPairwiseCompatibleBool_eq_true_of_length_le_one :
    ∀ definitions : List ShapeDefinition,
      definitions.length ≤ 1 ->
      definitionsPairwiseCompatibleBool definitions = true
  | [], _hlength => rfl
  | [_definition], _hlength => rfl
  | _first :: _second :: rest, hlength => by simp at hlength

private theorem map_clause_filter_holdsInBool
    (assignment : NormalForm.BoolCase) :
    ∀ definitions : List ShapeDefinition,
      (definitions.filter
        (fun definition =>
          definition.clause.holdsInBool assignment)).map ShapeDefinition.clause =
      (definitions.map ShapeDefinition.clause).filter
        (fun clause => clause.holdsInBool assignment)
  | [] => rfl
  | definition :: rest => by
      by_cases hholds : definition.clause.holdsInBool assignment = true
      · simp [hholds, map_clause_filter_holdsInBool assignment rest]
      · simp [hholds, map_clause_filter_holdsInBool assignment rest]

private theorem definitions_filter_holdsInBool_length_le_one
    {support : List NormalForm.BoolVar} (assignment : NormalForm.BoolCase)
    (definitions : List ShapeDefinition)
    (hnodup : (definitions.map ShapeDefinition.clause).Nodup)
    (hcomplete : ∀ definition ∈ definitions,
      definition.clause.CompleteMinterm support) :
    (definitions.filter
      (fun definition =>
        definition.clause.holdsInBool assignment)).length ≤ 1 := by
  have hclausesComplete : ∀ clause ∈ definitions.map ShapeDefinition.clause,
      clause.CompleteMinterm support := by
    intro clause hclause
    rcases List.mem_map.mp hclause with ⟨definition, hdefinition, rfl⟩
    exact hcomplete definition hdefinition
  have hbound := Clause.filter_holdsInBool_length_le_one assignment
    (definitions.map ShapeDefinition.clause) hnodup hclausesComplete
  calc
    (definitions.filter
      (fun definition =>
        definition.clause.holdsInBool assignment)).length =
        ((definitions.filter
          (fun definition =>
            definition.clause.holdsInBool assignment)).map
              ShapeDefinition.clause).length := by simp
    _ = ((definitions.map ShapeDefinition.clause).filter
          (fun clause => clause.holdsInBool assignment)).length := by
        rw [map_clause_filter_holdsInBool assignment definitions]
    _ ≤ 1 := hbound

private theorem activeDefinitionsIn_eq_nil_of_singleton_ne
    (candidate objectType : GroundObject) (assignment : NormalForm.BoolCase)
    (possible : PossibleDefinitions)
    (hobjects : possible.objectTypes = [objectType])
    (hne : candidate ≠ objectType) :
    activeDefinitionsIn candidate assignment possible = [] := by
  cases possible with
  | mk objectTypes definitions =>
      simp only [PossibleDefinitions.objectTypes] at hobjects
      subst objectTypes
      simp [activeDefinitionsIn, PossibleDefinitions.objectTypes, hne]

private theorem activeDefinitionsIn_length_le_one_of_singleton
    (objectType : GroundObject) (assignment : NormalForm.BoolCase)
    (possible : PossibleDefinitions)
    (hobjects : possible.objectTypes = [objectType])
    (hactive :
      (possible.definitions.filter
        (fun definition => definition.clause.holdsInBool assignment)).length ≤ 1) :
    (activeDefinitionsIn objectType assignment possible).length ≤ 1 := by
  cases possible with
  | mk objectTypes definitions =>
      simp only [PossibleDefinitions.objectTypes] at hobjects
      subst objectTypes
      simpa [activeDefinitionsIn, PossibleDefinitions.objectTypes,
        PossibleDefinitions.definitions] using hactive

private theorem activeDefinitions_eq_nil_of_not_mem
    (candidate : GroundObject) (assignment : NormalForm.BoolCase) :
    ∀ {groups : List PossibleDefinitions} {objectTypes : List GroundObject},
      groups.map PossibleDefinitions.objectTypes =
        objectTypes.map (fun objectType => [objectType]) ->
      candidate ∉ objectTypes ->
      activeDefinitions candidate assignment groups = []
  | [], [], _hgroups, _hnotMem => rfl
  | possible :: groups, objectType :: objectTypes, hgroups, hnotMem => by
      simp only [List.map_cons, List.cons.injEq] at hgroups
      have hne : candidate ≠ objectType := by
        intro heq
        subst candidate
        exact hnotMem (by simp)
      have hnotRest : candidate ∉ objectTypes := by
        intro hmem
        exact hnotMem (by simp [hmem])
      rw [activeDefinitions]
      rw [activeDefinitionsIn_eq_nil_of_singleton_ne candidate objectType
        assignment possible hgroups.1 hne]
      simp [activeDefinitions_eq_nil_of_not_mem candidate assignment
        hgroups.2 hnotRest]

private theorem activeDefinitions_length_le_one_of_singletonGroups
    (candidate : GroundObject) (assignment : NormalForm.BoolCase) :
    ∀ {groups : List PossibleDefinitions} {objectTypes : List GroundObject},
      groups.map PossibleDefinitions.objectTypes =
        objectTypes.map (fun objectType => [objectType]) ->
      objectTypes.Nodup ->
      (∀ possible ∈ groups,
        (possible.definitions.filter
          (fun definition =>
            definition.clause.holdsInBool assignment)).length ≤ 1) ->
      (activeDefinitions candidate assignment groups).length ≤ 1
  | [], [], _hgroups, _hnodup, _hactive => by
      simp [activeDefinitions]
  | possible :: groups, objectType :: objectTypes, hgroups, hnodup, hactive => by
      simp only [List.map_cons, List.cons.injEq] at hgroups
      have hnodupParts := List.nodup_cons.mp hnodup
      by_cases hcandidate : candidate = objectType
      · subst candidate
        rw [activeDefinitions]
        rw [activeDefinitions_eq_nil_of_not_mem objectType assignment
          hgroups.2 hnodupParts.1]
        simp only [List.append_nil]
        apply activeDefinitionsIn_length_le_one_of_singleton objectType assignment
          possible hgroups.1
        exact hactive possible (by simp)
      · rw [activeDefinitions]
        rw [activeDefinitionsIn_eq_nil_of_singleton_ne candidate objectType
          assignment possible hgroups.1 hcandidate]
        simp only [List.nil_append]
        apply activeDefinitions_length_le_one_of_singletonGroups candidate
          assignment hgroups.2 hnodupParts.2
        intro group hgroup
        exact hactive group (by simp [hgroup])

private theorem applicableGroupsUnambiguousBool_of_singletonGroups
    (candidate : GroundObject) (assignment : NormalForm.BoolCase) :
    ∀ {groups : List PossibleDefinitions} {objectTypes : List GroundObject},
      groups.map PossibleDefinitions.objectTypes =
        objectTypes.map (fun objectType => [objectType]) ->
      (∀ possible ∈ groups,
        (possible.definitions.filter
          (fun definition =>
            definition.clause.holdsInBool assignment)).length ≤ 1) ->
      applicableGroupsUnambiguousBool candidate assignment groups = true
  | [], [], _hgroups, _hactive => rfl
  | possible :: groups, objectType :: objectTypes, hgroups, hactive => by
      simp only [List.map_cons, List.cons.injEq] at hgroups
      rw [applicableGroupsUnambiguousBool]
      simp only [List.all_cons, Bool.and_eq_true_iff, decide_eq_true_eq]
      constructor
      · by_cases hcandidate : candidate = objectType
        · subst candidate
          apply activeDefinitionsIn_length_le_one_of_singleton objectType
            assignment possible hgroups.1
          exact hactive possible (by simp)
        · rw [activeDefinitionsIn_eq_nil_of_singleton_ne candidate objectType
            assignment possible hgroups.1 hcandidate]
          simp
      · apply applicableGroupsUnambiguousBool_of_singletonGroups candidate
          assignment hgroups.2
        intro group hgroup
        exact hactive group (by simp [hgroup])

/-- Singleton object-keyed groups with unique keys satisfy response-case
validity whenever each group has at most one active definition. -/
theorem responsePositionCasesValidBool_of_singletonGroups_active
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition)
    (hgroups : ∃ objectTypes : List GroundObject,
      position.possibleDefinitions.map PossibleDefinitions.objectTypes =
        objectTypes.map (fun objectType => [objectType])
      ∧ objectTypes.Nodup)
    (hactive : ∀ possible ∈ position.possibleDefinitions,
      ∀ assignment ∈ NormalForm.allBoolCases support,
        (possible.definitions.filter
          (fun definition =>
            definition.clause.holdsInBool assignment)).length ≤ 1) :
    responsePositionCasesValidBool schema support parentType position = true := by
  rcases hgroups with ⟨objectTypes, hobjects, hnodup⟩
  rw [responsePositionCasesValidBool]
  apply List.all_eq_true.mpr
  intro candidate _hcandidate
  apply List.all_eq_true.mpr
  intro assignment hassignment
  rw [responseCaseValidBool, Bool.and_eq_true_iff]
  constructor
  · apply applicableGroupsUnambiguousBool_of_singletonGroups candidate
      assignment hobjects
    intro possible hpossible
    exact hactive possible hpossible assignment hassignment
  · apply definitionsPairwiseCompatibleBool_eq_true_of_length_le_one
    apply activeDefinitions_length_le_one_of_singletonGroups candidate assignment
      hobjects hnodup
    intro possible hpossible
    exact hactive possible hpossible assignment hassignment

/-- A position partitioned into duplicate-free singleton object groups is
valid when every group contains distinct complete-minterm clauses.  Complete
minterms are mutually exclusive under every Boolean assignment, so each
object/assignment pair has at most one active definition. -/
theorem responsePositionCasesValidBool_of_singletonObjectGroups
    (schema : Schema) (support : List NormalForm.BoolVar) (parentType : Name)
    (position : ResponsePosition)
    (hgroups : ∃ objectTypes : List GroundObject,
      position.possibleDefinitions.map PossibleDefinitions.objectTypes =
        objectTypes.map (fun objectType => [objectType])
      ∧ objectTypes.Nodup)
    (hclauses : ∀ possible ∈ position.possibleDefinitions,
      (possible.definitions.map ShapeDefinition.clause).Nodup)
    (hcomplete : ∀ possible ∈ position.possibleDefinitions,
      ∀ definition ∈ possible.definitions,
        definition.clause.CompleteMinterm support) :
    responsePositionCasesValidBool schema support parentType position = true := by
  apply responsePositionCasesValidBool_of_singletonGroups_active schema support
    parentType position hgroups
  intro possible hpossible assignment _hassignment
  exact definitions_filter_holdsInBool_length_le_one assignment
    possible.definitions (hclauses possible hpossible)
    (hcomplete possible hpossible)

end ResponseShape

end GraphQL
