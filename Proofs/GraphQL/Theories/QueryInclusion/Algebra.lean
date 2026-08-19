import GraphQL.Theories.QueryInclusion

/-! Algebraic facts about error-free query inclusion. -/

namespace GraphQL
namespace QueryInclusion

open Execution AnnotatedExecution
open scoped SyntacticEquivalence

mutual
  private theorem inputValueStructuralEquivalent_trans
      : ∀ {left middle right : InputValue},
          InputValue.structuralEquivalent left middle
          -> InputValue.structuralEquivalent middle right
          -> InputValue.structuralEquivalent left right := by
    intro left middle right hleft hright
    cases left <;> cases middle <;> cases right <;>
      simp [InputValue.structuralEquivalent] at hleft hright ⊢
    all_goals
      first
      | exact hleft.trans hright
      | exact inputValuesStructuralEquivalent_trans hleft hright
      | exact inputObjectFieldsStructuralEquivalent_trans hleft hright
      | trivial
      | contradiction

  private theorem inputValuesStructuralEquivalent_trans
      : ∀ {left middle right : List InputValue},
          InputValue.structuralValuesEquivalent left middle
          -> InputValue.structuralValuesEquivalent middle right
          -> InputValue.structuralValuesEquivalent left right
    | [], [], [], _hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent]
    | left :: lefts, middle :: middles, right :: rights, hleft, hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft hright ⊢
        exact ⟨inputValueStructuralEquivalent_trans hleft.1 hright.1,
          inputValuesStructuralEquivalent_trans hleft.2 hright.2⟩
    | [], [], _ :: _, _hleft, hright => by
        simp [InputValue.structuralValuesEquivalent] at hright
    | [], _ :: _, [], hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | [], _ :: _, _ :: _, hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | _ :: _, [], [], hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | _ :: _, [], _ :: _, hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | _ :: _, _ :: _, [], _hleft, hright => by
        simp [InputValue.structuralValuesEquivalent] at hright

  private theorem inputObjectFieldsStructuralEquivalent_trans
      : ∀ {left middle right : List (Name × InputValue)},
          InputValue.structuralObjectFieldsEquivalent left middle
          -> InputValue.structuralObjectFieldsEquivalent middle right
          -> InputValue.structuralObjectFieldsEquivalent left right
    | [], [], [], _hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent]
    | (leftName, leftValue) :: lefts,
        (middleName, middleValue) :: middles,
        (rightName, rightValue) :: rights, hleft, hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft hright ⊢
        exact ⟨hleft.1.trans hright.1,
          inputValueStructuralEquivalent_trans hleft.2.1 hright.2.1,
          inputObjectFieldsStructuralEquivalent_trans hleft.2.2 hright.2.2⟩
    | [], [], _ :: _, _hleft, hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hright
    | [], _ :: _, [], hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | [], _ :: _, _ :: _, hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | _ :: _, [], [], hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | _ :: _, [], _ :: _, hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | _ :: _, _ :: _, [], _hleft, hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hright
end

mutual
  theorem inputValueStructuralEquivalent_refl
      : ∀ value : InputValue, InputValue.structuralEquivalent value value
    | .null => trivial
    | .int _value => rfl
    | .float _value => rfl
    | .string _value => rfl
    | .boolean _value => rfl
    | .enum _value => rfl
    | .variable _name => rfl
    | .list values => inputValuesStructuralEquivalent_refl values
    | .object fields => inputObjectFieldsStructuralEquivalent_refl fields

  theorem inputValuesStructuralEquivalent_refl
      : ∀ values : List InputValue, InputValue.structuralValuesEquivalent values values
    | [] => trivial
    | value :: values =>
        ⟨
          inputValueStructuralEquivalent_refl value,
          inputValuesStructuralEquivalent_refl values
        ⟩

  theorem inputObjectFieldsStructuralEquivalent_refl
      : ∀ fields : List (Name × InputValue),
          InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => trivial
    | (_name, value) :: fields =>
        ⟨
          rfl,
          inputValueStructuralEquivalent_refl value,
          inputObjectFieldsStructuralEquivalent_refl fields
        ⟩
end

private theorem argumentsEquivalent_refl (arguments : List Argument)
    : Argument.argumentsEquivalent arguments arguments :=
  ⟨
    fun argument hmember =>
      ⟨argument, hmember, ⟨rfl, inputValueStructuralEquivalent_refl _⟩⟩,
    fun argument hmember =>
      ⟨argument, hmember, ⟨rfl, inputValueStructuralEquivalent_refl _⟩⟩
  ⟩

theorem argumentsEquivalent_trans {left middle right : List Argument}
    : Argument.argumentsEquivalent left middle
      -> Argument.argumentsEquivalent middle right
      -> Argument.argumentsEquivalent left right := by
  intro hleft hright
  exact ⟨
    by
      intro argument hargument
      rcases hleft.1 argument hargument with ⟨middleArgument, hmiddle, hequivalentLeft⟩
      rcases hright.1 middleArgument hmiddle with ⟨rightArgument, hrightMember, hequivalentRight⟩
      exact ⟨rightArgument, hrightMember,
        ⟨hequivalentLeft.1.trans hequivalentRight.1,
          inputValueStructuralEquivalent_trans hequivalentLeft.2 hequivalentRight.2⟩⟩,
    by
      intro argument hargument
      rcases hright.2 argument hargument with ⟨middleArgument, hmiddle, hequivalentRight⟩
      rcases hleft.2 middleArgument hmiddle with ⟨leftArgument, hleftMember, hequivalentLeft⟩
      exact ⟨leftArgument, hleftMember,
        ⟨hequivalentLeft.1.trans hequivalentRight.1,
          inputValueStructuralEquivalent_trans hequivalentLeft.2 hequivalentRight.2⟩⟩⟩

theorem inputValueStructuralEquivalentBool_iff (left right : InputValue)
    : left.structuralEquivalentBool right = true ↔ left.structuralEquivalent right := by
  simp only [InputValue.structuralEquivalentBool, decide_eq_true_iff]

theorem inputValuesStructuralEquivalentBool_iff (left right : List InputValue)
    : InputValue.structuralValuesEquivalentBool left right = true
      ↔ InputValue.structuralValuesEquivalent left right := by
  simp only [InputValue.structuralValuesEquivalentBool, decide_eq_true_iff]

theorem inputObjectFieldsStructuralEquivalentBool_iff
    (left right : List (Name × InputValue))
    : InputValue.structuralObjectFieldsEquivalentBool left right = true
      ↔ InputValue.structuralObjectFieldsEquivalent left right := by
  simp only [InputValue.structuralObjectFieldsEquivalentBool, decide_eq_true_iff]

theorem inputValueSyntacticallyEquivalentBool_iff (left right : InputValue)
    : left.syntacticallyEquivalentBool right = true ↔ left ≡ right := by
  change left.syntacticallyEquivalentBool right = true ↔ left.equivalent right
  simp only [InputValue.syntacticallyEquivalentBool, decide_eq_true_iff]

theorem argumentSyntacticallyEquivalentBool_iff (left right : Argument)
    : left.syntacticallyEquivalentBool right = true ↔ left ≡ right := by
  change left.syntacticallyEquivalentBool right = true ↔ left.equivalent right
  simp only [Argument.syntacticallyEquivalentBool, decide_eq_true_iff]

theorem argumentsSyntacticallyEquivalentBool_iff (left right : List Argument)
    : Argument.argumentsSyntacticallyEquivalentBool left right = true ↔ left ≡ right := by
  change Argument.argumentsSyntacticallyEquivalentBool left right = true
    ↔ Argument.argumentsEquivalent left right
  simp only [Argument.argumentsSyntacticallyEquivalentBool, decide_eq_true_iff]

theorem sharedVariableDefinitionsSyntacticallyCompatibleBool_iff
    (left right : List VariableDefinition)
    : sharedVariableDefinitionsSyntacticallyCompatibleBool left right = true
      ↔ sharedVariableDefinitionsSyntacticallyCompatible left right := by
  simp only [sharedVariableDefinitionsSyntacticallyCompatibleBool,
    decide_eq_true_iff]

theorem variableDefinitionSyntacticallyEquivalent_refl (definition : VariableDefinition)
    : VariableDefinition.equivalent definition definition := by
  refine ⟨rfl, rfl, ?_⟩
  cases definition.defaultValue with
  | none => trivial
  | some defaultValue => exact inputValueStructuralEquivalent_refl _

theorem variableDefinitionsSyntacticallyEquivalent_refl
    (definitions : List VariableDefinition)
    : variableDefinitionsSyntacticallyEquivalent definitions definitions :=
  ⟨
    fun definition hmember =>
      ⟨definition, hmember, variableDefinitionSyntacticallyEquivalent_refl definition⟩,
    fun definition hmember =>
      ⟨definition, hmember, variableDefinitionSyntacticallyEquivalent_refl definition⟩
  ⟩

private theorem variableDefinition_eq_of_name_eq_of_mem_of_names_nodup
    {definitions : List VariableDefinition} {left right : VariableDefinition}
    (hnodup : (definitions.map VariableDefinition.name).Nodup)
    (hleft : left ∈ definitions) (hright : right ∈ definitions)
    (hname : left.name = right.name)
    : left = right := by
  induction definitions generalizing left right with
  | nil => simp at hleft
  | cons definition rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hleft with rfl | hleftRest
      · rcases List.mem_cons.mp hright with rfl | hrightRest
        · rfl
        · exact False.elim (hnodup.1 (by
            rw [hname]
            exact List.mem_map.mpr ⟨right, hrightRest, rfl⟩))
      · rcases List.mem_cons.mp hright with rfl | hrightRest
        · exact False.elim (hnodup.1 (by
            rw [← hname]
            exact List.mem_map.mpr ⟨left, hleftRest, rfl⟩))
        · exact ih hnodup.2 hleftRest hrightRest hname

theorem sharedVariableDefinitionsSyntacticallyCompatible_of_mem
    {left right : List VariableDefinition} {leftDefinition rightDefinition}
    (hequivalent : sharedVariableDefinitionsSyntacticallyCompatible left right)
    (hrightNodup : (right.map VariableDefinition.name).Nodup)
    (hleft : leftDefinition ∈ left) (hright : rightDefinition ∈ right)
    (hname : leftDefinition.name = rightDefinition.name)
    : VariableDefinition.equivalent leftDefinition rightDefinition := by
  have hleftShared : leftDefinition ∈ variableDefinitionsSharedWith left right := by
    apply List.mem_filter.mpr
    refine ⟨hleft, ?_⟩
    rw [List.any_eq_true]
    exact ⟨rightDefinition, hright, by simp [hname]⟩
  rcases hequivalent.1 leftDefinition hleftShared with
    ⟨candidate, hcandidateShared, hcandidateEquivalent⟩
  have hcandidate : candidate ∈ right :=
    (List.mem_filter.mp hcandidateShared).1
  have hcandidateName : candidate.name = rightDefinition.name :=
    hcandidateEquivalent.1.symm.trans hname
  rw [variableDefinition_eq_of_name_eq_of_mem_of_names_nodup hrightNodup
    hcandidate hright hcandidateName] at hcandidateEquivalent
  exact hcandidateEquivalent

theorem sharedVariableDefinitionsSyntacticallyCompatible_refl
    (definitions : List VariableDefinition)
    (_hnodup : (definitions.map VariableDefinition.name).Nodup)
    : sharedVariableDefinitionsSyntacticallyCompatible definitions definitions := by
  exact variableDefinitionsSyntacticallyEquivalent_refl _

theorem sameFieldProvenance_iff (left right : ResolvedFieldProvenance)
    : sameFieldProvenance left right
      ↔ left.parentType = right.parentType
        ∧ left.fieldName = right.fieldName
        ∧ Argument.argumentsEquivalent left.originalArguments
            right.originalArguments := by
  rfl

mutual
  private theorem inputValue_eq_of_structuralEquivalent
      (left right : InputValue)
      (hequivalent : InputValue.structuralEquivalent left right)
      : left = right := by
    cases left <;> cases right <;>
      simp [InputValue.structuralEquivalent] at hequivalent
    all_goals
      first
      | rfl
      | subst hequivalent; rfl
      | rw [inputValues_eq_of_structuralEquivalent _ _ hequivalent]
      | rw [inputObjectFields_eq_of_structuralEquivalent _ _ hequivalent]

  private theorem inputValues_eq_of_structuralEquivalent
      (left right : List InputValue)
      (hequivalent : InputValue.structuralValuesEquivalent left right)
      : left = right := by
    cases left with
    | nil => cases right <;> simp_all [InputValue.structuralValuesEquivalent]
    | cons leftValue leftRest =>
        cases right with
        | nil => simp_all [InputValue.structuralValuesEquivalent]
        | cons rightValue rightRest =>
            simp only [InputValue.structuralValuesEquivalent] at hequivalent
            rw [inputValue_eq_of_structuralEquivalent leftValue rightValue hequivalent.1,
              inputValues_eq_of_structuralEquivalent leftRest rightRest hequivalent.2]

  private theorem inputObjectFields_eq_of_structuralEquivalent
      (left right : List (Name × InputValue))
      (hequivalent : InputValue.structuralObjectFieldsEquivalent left right)
      : left = right := by
    cases left with
    | nil => cases right <;> simp_all [InputValue.structuralObjectFieldsEquivalent]
    | cons leftField leftRest =>
        cases right with
        | nil => simp_all [InputValue.structuralObjectFieldsEquivalent]
        | cons rightField rightRest =>
            rcases leftField with ⟨leftName, leftValue⟩
            rcases rightField with ⟨rightName, rightValue⟩
            simp only [InputValue.structuralObjectFieldsEquivalent] at hequivalent
            rw [hequivalent.1,
              inputValue_eq_of_structuralEquivalent leftValue rightValue hequivalent.2.1,
              inputObjectFields_eq_of_structuralEquivalent leftRest rightRest hequivalent.2.2]
end

theorem inputValue_canonical_eq_of_equivalent {left right : InputValue}
    (hequivalent : left.equivalent right)
    : left.canonical = right.canonical :=
  inputValue_eq_of_structuralEquivalent left.canonical right.canonical hequivalent

theorem annotatedResponseValueIncludes_refl
    : ∀ value : AnnotatedResponseValue, annotatedResponseValueIncludes value value
  | .null => by simp [annotatedResponseValueIncludes]
  | .scalar _value => by simp [annotatedResponseValueIncludes]
  | .object _runtimeType fields => by
      simp only [annotatedResponseValueIncludes]
      intro responseName call child hmember
      exact ⟨responseName, call, child, hmember, rfl,
        (sameFieldProvenance_iff call call).mpr
          ⟨rfl, rfl, argumentsEquivalent_refl _⟩,
        annotatedResponseValueIncludes_refl child⟩
  | .list values => by
      simp only [annotatedResponseValueIncludes]
      intro index value hmember
      exact ⟨value, hmember, annotatedResponseValueIncludes_refl value⟩
termination_by value => value.structuralSize
decreasing_by
  all_goals
    first
    | exact AnnotatedResponseValue.structuralSize_lt_of_object_field_mem hmember
    | exact AnnotatedResponseValue.structuralSize_lt_of_list_get? hmember

theorem annotatedResponseValueIncludes_trans
    : ∀ left middle right : AnnotatedResponseValue,
        annotatedResponseValueIncludes left middle
        -> annotatedResponseValueIncludes middle right
        -> annotatedResponseValueIncludes left right
  | left, middle, .null => by
      intro leftMiddle middleRight
      have hmiddle : middle = .null := by
        cases middle <;> simp_all [annotatedResponseValueIncludes]
      subst hmiddle
      cases left <;> simp_all [annotatedResponseValueIncludes]
  | left, middle, .scalar value => by
      intro leftMiddle middleRight
      have hmiddle : middle = .scalar value := by
        cases middle <;> simp_all [annotatedResponseValueIncludes]
      subst hmiddle
      cases left <;> simp_all [annotatedResponseValueIncludes]
  | .object _leftType leftFields, .object _middleType middleFields,
    .object _rightType rightFields => by
      simp only [annotatedResponseValueIncludes]
      intro leftMiddle middleRight responseName rightCall rightValue rightMember
      rcases middleRight responseName rightCall rightValue rightMember with
        ⟨middleName, middleCall, middleValue, middleMember, middleNameEq,
          middleCallEq, middleValueIncludes⟩
      rcases leftMiddle middleName middleCall middleValue middleMember with
        ⟨leftName, leftCall, leftValue, leftMember, leftNameEq, leftCallEq,
          leftValueIncludes⟩
      rcases (sameFieldProvenance_iff _ _).mp leftCallEq with
        ⟨leftParent, leftField, leftArguments⟩
      rcases (sameFieldProvenance_iff _ _).mp middleCallEq with
        ⟨middleParent, middleField, middleArguments⟩
      exact ⟨leftName, leftCall, leftValue, leftMember,
        leftNameEq.trans middleNameEq,
        (sameFieldProvenance_iff _ _).mpr
          ⟨leftParent.trans middleParent, leftField.trans middleField,
            argumentsEquivalent_trans leftArguments middleArguments⟩,
        annotatedResponseValueIncludes_trans leftValue middleValue rightValue
          leftValueIncludes middleValueIncludes⟩
  | .list leftValues, .list middleValues, .list rightValues => by
      simp only [annotatedResponseValueIncludes]
      intro leftMiddle middleRight index rightValue rightMember
      rcases middleRight index rightValue rightMember with
        ⟨middleValue, middleMember, middleValueIncludes⟩
      rcases leftMiddle index middleValue middleMember with
        ⟨leftValue, leftMember, leftValueIncludes⟩
      exact ⟨leftValue, leftMember,
        annotatedResponseValueIncludes_trans leftValue middleValue rightValue
          leftValueIncludes middleValueIncludes⟩
  | _left, .null, .object _type _fields => by simp [annotatedResponseValueIncludes]
  | _left, .scalar _value, .object _type _fields => by simp [annotatedResponseValueIncludes]
  | _left, .list _values, .object _type _fields => by simp [annotatedResponseValueIncludes]
  | .null, .object _type _fields, .object _rightType _rightFields => by
      simp [annotatedResponseValueIncludes]
  | .scalar _value, .object _type _fields, .object _rightType _rightFields => by
      simp [annotatedResponseValueIncludes]
  | .list _values, .object _type _fields, .object _rightType _rightFields => by
      simp [annotatedResponseValueIncludes]
  | _left, .null, .list _values => by simp [annotatedResponseValueIncludes]
  | _left, .scalar _value, .list _values => by simp [annotatedResponseValueIncludes]
  | _left, .object _type _fields, .list _values => by simp [annotatedResponseValueIncludes]
  | .null, .list _middleValues, .list _rightValues => by simp [annotatedResponseValueIncludes]
  | .scalar _value, .list _middleValues, .list _rightValues => by
      simp [annotatedResponseValueIncludes]
  | .object _type _fields, .list _middleValues, .list _rightValues => by
      simp [annotatedResponseValueIncludes]
termination_by _left _middle right => right.structuralSize
decreasing_by
  all_goals
    first
    | exact AnnotatedResponseValue.structuralSize_lt_of_object_field_mem rightMember
    | exact AnnotatedResponseValue.structuralSize_lt_of_list_get? rightMember

theorem includes_refl (schema : Schema) (operation : Operation)
    (hdefinitions : (operation.variableDefinitions.map VariableDefinition.name).Nodup)
    : includes schema operation operation := by
  refine ⟨sharedVariableDefinitionsSyntacticallyCompatible_refl
    operation.variableDefinitions hdefinitions, ?_⟩
  intro ObjectRef resolvers variableValues source
  dsimp
  intro _errors _errors
  exact annotatedResponseValueIncludes_refl _

theorem includes_refl_of_valid (schema : Schema) (operation : Operation)
    (hvalid : Validation.operationDefinitionValid schema operation)
    : includes schema operation operation := by
  exact includes_refl schema operation hvalid.2.2.1.1

-- Shared-definition compatibility is pair-local and is not transitive when the middle
-- operation omits a name shared by the endpoints. The endpoint premise isolates that
-- boundary; error-freeness of the middle operation supplies both composed executions
-- with their remaining run-specific premise.
theorem includes_trans_of_middle_error_free (schema : Schema)
    (left middle right : Operation)
    (endpointSharedVariableDefinitions
      : sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
          right.variableDefinitions)
    (middleErrorFree
      : ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
          (variableValues : VariableValues) (source : ResolverValue ObjectRef),
          (executeQueryAnnotated schema resolvers variableValues middle source).errors
          = 0)
    : includes schema left middle
      -> includes schema middle right
      -> includes schema left right := by
  rintro ⟨_leftMiddleDefinitions, leftMiddle⟩
    ⟨_middleRightDefinitions, middleRight⟩
  refine ⟨endpointSharedVariableDefinitions, ?_⟩
  intro ObjectRef resolvers variableValues source
  dsimp only at leftMiddle middleRight ⊢
  intro leftErrors rightErrors
  exact annotatedResponseValueIncludes_trans _ _ _
    (leftMiddle ObjectRef resolvers variableValues source leftErrors
      (middleErrorFree ObjectRef resolvers variableValues source))
    (middleRight ObjectRef resolvers variableValues source
      (middleErrorFree ObjectRef resolvers variableValues source) rightErrors)

end QueryInclusion
end GraphQL
