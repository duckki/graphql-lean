import GraphQL.Theories.TreeSummary.StaticCost
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Soundness
import Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality
import Proofs.GraphQL.Theories.TreeSummary.Syntactic.Soundness

/-! Static-cost algebra laws, local optimality, and execution soundness.

`StaticCost.evaluateAnnotatedResponse` is the concrete cost fold. The generic exact-case
tree-summary theorem reduces execution soundness to the local compatibility proof below.
The optimality section independently proves feasible pointwise least bounds for the
same modeled local field transfers.
-/

namespace GraphQL
namespace TreeSummary
namespace StaticCost

open GraphQL.TreeSummary.ExactCases
open GraphQL.AnnotatedExecution
open TreeSummary.Optimality

private theorem cost_le_refl (cost : Bound) : cost ≤ cost :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

private theorem cost_le_trans {left middle right : Bound}
    (hleft : left ≤ middle) (hright : middle ≤ right)
    : left ≤ right :=
  ⟨Nat.le_trans hleft.1 hright.1, Nat.le_trans hleft.2 hright.2⟩

private theorem cost_add_le_add {left lower right upper : Bound}
    (hleft : left ≤ lower) (hright : right ≤ upper)
    : Bound.add left right ≤ Bound.add lower upper :=
  ⟨Nat.add_le_add hleft.1 hright.1, Nat.add_le_add hleft.2 hright.2⟩

private theorem cost_zero_le (cost : Bound) : Bound.zero ≤ cost :=
  ⟨Nat.zero_le _, Nat.zero_le _⟩

private theorem cost_add_zero (cost : Bound) : Bound.add cost Bound.zero = cost := by
  cases cost
  simp [Bound.add, Bound.zero]

private theorem cost_le_max_left (left right : Bound) : left ≤ Bound.max left right :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

private theorem cost_le_max_right (left right : Bound) : right ≤ Bound.max left right :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

private theorem cost_max_le {left right upper : Bound}
    (hleft : left ≤ upper) (hright : right ≤ upper)
    : Bound.max left right ≤ upper :=
  ⟨Nat.max_le.mpr ⟨hleft.1, hright.1⟩, Nat.max_le.mpr ⟨hleft.2, hright.2⟩⟩

private theorem cost_max_mono {leftLower leftUpper rightLower rightUpper : Bound}
    (hleft : leftLower ≤ leftUpper) (hright : rightLower ≤ rightUpper)
    : Bound.max leftLower rightLower ≤ Bound.max leftUpper rightUpper :=
  ⟨
    Nat.max_le.mpr
      ⟨
        Nat.le_trans hleft.1 (Nat.le_max_left _ _),
        Nat.le_trans hright.1 (Nat.le_max_right _ _)
      ⟩,
    Nat.max_le.mpr
      ⟨
        Nat.le_trans hleft.2 (Nat.le_max_left _ _),
        Nat.le_trans hright.2 (Nat.le_max_right _ _)
      ⟩
  ⟩

private theorem actualCost_le_refl (cost : Cost) : cost ≤ cost :=
  ⟨Int.le_refl _, Nat.le_refl _⟩

private theorem actualCost_le_trans {left middle right : Cost}
    (hleft : left ≤ middle) (hright : middle ≤ right)
    : left ≤ right :=
  ⟨Int.le_trans hleft.1 hright.1, Nat.le_trans hleft.2 hright.2⟩

private theorem actualCost_add_le_add {left lower right upper : Cost}
    (hleft : left ≤ lower) (hright : right ≤ upper)
    : Cost.add left right ≤ Cost.add lower upper :=
  ⟨Int.add_le_add hleft.1 hright.1, Nat.add_le_add hleft.2 hright.2⟩

private theorem actualCost_zero_add (cost : Cost) : Cost.add Cost.zero cost = cost := by
  cases cost
  simp [Cost.add, Cost.zero]

private theorem actualCost_add_zero (cost : Cost) : Cost.add cost Cost.zero = cost := by
  cases cost
  simp [Cost.add, Cost.zero]

private theorem bound_toCost_le_toCost {lower upper : Bound} (hle : lower ≤ upper)
    : lower.toCost ≤ upper.toCost :=
  ⟨Int.ofNat_le.mpr hle.1, hle.2⟩

private theorem bound_toCost_add (left right : Bound)
    : (Bound.add left right).toCost = Cost.add left.toCost right.toCost := by
  cases left
  cases right
  simp [Bound.add, Bound.toCost, Cost.add]

-----------------------------------------------------------------------------------------
-- Semantic argument invariance
-----------------------------------------------------------------------------------------

mutual
  private theorem inputValue_eq_of_structuralEquivalent
      (left right : InputValue)
      (hequivalent : InputValue.structuralEquivalent left right)
      : left = right := by
    cases left <;> cases right <;>
      simp only [InputValue.structuralEquivalent] at hequivalent
    all_goals try { contradiction }
    all_goals try { simp_all }
    case list.list left right =>
      exact congrArg InputValue.list
        (inputValues_eq_of_structuralEquivalent left right hequivalent)
    case object.object left right =>
      exact congrArg InputValue.object
        (inputObjectFields_eq_of_structuralEquivalent left right hequivalent)

  private theorem inputValues_eq_of_structuralEquivalent
      (left right : List InputValue)
      (hequivalent : InputValue.structuralValuesEquivalent left right)
      : left = right := by
    cases left with
    | nil =>
        cases right <;>
          simp_all [InputValue.structuralValuesEquivalent]
    | cons leftValue leftRest =>
        cases right with
        | nil => simp_all [InputValue.structuralValuesEquivalent]
        | cons rightValue rightRest =>
            simp only [InputValue.structuralValuesEquivalent] at hequivalent
            rw [inputValue_eq_of_structuralEquivalent leftValue rightValue
                hequivalent.1,
              inputValues_eq_of_structuralEquivalent leftRest rightRest
                hequivalent.2]

  private theorem inputObjectFields_eq_of_structuralEquivalent
      (left right : List (Name × InputValue))
      (hequivalent : InputValue.structuralObjectFieldsEquivalent left right)
      : left = right := by
    cases left with
    | nil =>
        cases right <;>
          simp_all [InputValue.structuralObjectFieldsEquivalent]
    | cons leftField leftRest =>
        cases right with
        | nil => simp_all [InputValue.structuralObjectFieldsEquivalent]
        | cons rightField rightRest =>
            rcases leftField with ⟨leftName, leftValue⟩
            rcases rightField with ⟨rightName, rightValue⟩
            simp only [InputValue.structuralObjectFieldsEquivalent] at hequivalent
            rw [hequivalent.1,
              inputValue_eq_of_structuralEquivalent leftValue rightValue
                hequivalent.2.1,
              inputObjectFields_eq_of_structuralEquivalent leftRest rightRest
                hequivalent.2.2]
end

private theorem inputValue_canonical_eq_of_equivalent
    {left right : InputValue} (hequivalent : left.equivalent right)
    : left.canonical = right.canonical :=
  inputValue_eq_of_structuralEquivalent left.canonical right.canonical hequivalent

private theorem insertInputObjectFieldSorted_perm (field : Name × InputValue)
    : ∀ fields, (InputValue.insertObjectFieldSorted field fields).Perm (field :: fields)
  | [] => List.Perm.refl _
  | candidate :: rest => by
      by_cases hle : field.1 ≤ candidate.1
      · simp [InputValue.insertObjectFieldSorted, hle]
      · rw [InputValue.insertObjectFieldSorted]
        simp only [hle, if_false]
        exact
          ((insertInputObjectFieldSorted_perm field rest).cons candidate).trans
            (List.Perm.swap field candidate rest)

private theorem sortInputObjectFieldsByName_perm
    : ∀ fields, (InputValue.sortObjectFieldsByName fields).Perm fields
  | [] => List.Perm.refl _
  | field :: rest =>
      (insertInputObjectFieldSorted_perm field
        (InputValue.sortObjectFieldsByName rest)).trans
        ((sortInputObjectFieldsByName_perm rest).cons field)

private theorem resolvedInputObjectFieldsCost_eq_of_perm
    (schema : Schema) (model : CostModel) (inputObject : InputObjectType)
    {left right : List (Name × InputValue)} (hperm : left.Perm right)
    : resolvedInputObjectFieldsCost schema model inputObject left
      = resolvedInputObjectFieldsCost schema model inputObject right := by
  induction hperm with
  | nil => rfl
  | cons field hperm ih =>
      rcases field with ⟨fieldName, value⟩
      simp [resolvedInputObjectFieldsCost, ih]
  | swap left right rest =>
      rcases left with ⟨leftName, leftValue⟩
      rcases right with ⟨rightName, rightValue⟩
      simp [resolvedInputObjectFieldsCost, Int.add_assoc, Int.add_left_comm,
        Int.add_comm]
  | trans _ _ ihleft ihrigh => exact ihleft.trans ihrigh

mutual
  private theorem resolvedInputValueCost_canonical
      (schema : Schema) (model : CostModel) (includeOwnWeight : Bool)
      (coordinate : CostCoordinate) (definition : InputValueDefinition)
      : ∀ value,
          resolvedInputValueCost schema model includeOwnWeight coordinate definition
            value.canonical
          = resolvedInputValueCost schema model includeOwnWeight coordinate definition
              value
    | .null => by simp [InputValue.canonical, resolvedInputValueCost]
    | .int value => by simp [InputValue.canonical, resolvedInputValueCost]
    | .float value => by simp [InputValue.canonical, resolvedInputValueCost]
    | .string value => by simp [InputValue.canonical, resolvedInputValueCost]
    | .boolean value => by simp [InputValue.canonical, resolvedInputValueCost]
    | .enum value => by simp [InputValue.canonical, resolvedInputValueCost]
    | .variable name => by simp [InputValue.canonical, resolvedInputValueCost]
    | .list values => by
        simp only [InputValue.canonical, resolvedInputValueCost]
        rw [resolvedInputValuesCost_canonical schema model coordinate definition values]
    | .object fields => by
        simp only [InputValue.canonical, resolvedInputValueCost]
        cases hlookup : schema.lookupInputObject definition.inputType.namedType with
        | none => rfl
        | some inputObject =>
            simp only
            congr 1
            exact
              (resolvedInputObjectFieldsCost_eq_of_perm schema model inputObject
                (sortInputObjectFieldsByName_perm
                  (InputValue.canonicalObjectFields fields))).trans
                (resolvedInputObjectFieldsCost_canonical schema model inputObject fields)

  private theorem resolvedInputValuesCost_canonical
      (schema : Schema) (model : CostModel) (coordinate : CostCoordinate)
      (definition : InputValueDefinition)
      : ∀ values,
          resolvedInputValuesCost schema model coordinate definition
            (InputValue.canonicalValues values)
          = resolvedInputValuesCost schema model coordinate definition values
    | [] => rfl
    | value :: rest => by
        simp [InputValue.canonicalValues, resolvedInputValuesCost,
          resolvedInputValueCost_canonical schema model false coordinate definition value,
          resolvedInputValuesCost_canonical schema model coordinate definition rest]

  private theorem resolvedInputObjectFieldsCost_canonical
      (schema : Schema) (model : CostModel) (inputObject : InputObjectType)
      : ∀ fields,
          resolvedInputObjectFieldsCost schema model inputObject
            (InputValue.canonicalObjectFields fields)
          = resolvedInputObjectFieldsCost schema model inputObject fields
    | [] => rfl
    | (fieldName, value) :: rest => by
        simp only [InputValue.canonicalObjectFields, resolvedInputObjectFieldsCost]
        cases hlookup : Schema.lookupArgumentDefinition inputObject.inputFields fieldName with
        | none =>
            simp [resolvedInputObjectFieldsCost_canonical schema model inputObject rest]
        | some fieldDefinition =>
            simp [resolvedInputValueCost_canonical schema model true
                (.inputFieldDefinition inputObject.name fieldName) fieldDefinition value,
              resolvedInputObjectFieldsCost_canonical schema model inputObject rest]
end

private theorem inputValueCost_eq_of_equivalent
    (schema : Schema) (model : CostModel) (coordinate : CostCoordinate)
    (definition : InputValueDefinition) {left right : InputValue}
    (hequivalent : left.equivalent right)
    : inputValueCost schema model coordinate definition left
      = inputValueCost schema model coordinate definition right := by
  unfold inputValueCost
  calc
    resolvedInputValueCost schema model true coordinate definition left
        = resolvedInputValueCost schema model true coordinate definition left.canonical :=
      (resolvedInputValueCost_canonical schema model true coordinate definition left).symm
    _ = resolvedInputValueCost schema model true coordinate definition
          right.canonical := by
      rw [inputValue_canonical_eq_of_equivalent hequivalent]
    _ = resolvedInputValueCost schema model true coordinate definition right :=
      resolvedInputValueCost_canonical schema model true coordinate definition right

private theorem inferListSize_eq_of_equivalent {left right : InputValue}
    (hequivalent : left.equivalent right)
    : inferListSize? left = inferListSize? right := by
  have hcanonical := inputValue_canonical_eq_of_equivalent hequivalent
  cases left <;> cases right <;>
    simp [InputValue.canonical] at hcanonical ⊢
  all_goals subst_vars <;> rfl

private def listsRelatedAsSets (relation : alpha -> alpha -> Prop)
    (left right : List alpha)
    : Prop :=
  (∀ value, value ∈ left -> ∃ other, other ∈ right ∧ relation value other)
  ∧ (∀ value, value ∈ right -> ∃ other, other ∈ left ∧ relation other value)

private theorem listFilterMap_mem_iff_of_related
    {alpha beta : Type} (relation : alpha -> alpha -> Prop)
    (project : alpha -> Option beta)
    (hproject : ∀ {left right}, relation left right -> project left = project right)
    {left right : List alpha} (hrelated : listsRelatedAsSets relation left right)
    (result : beta)
    : result ∈ left.filterMap project ↔ result ∈ right.filterMap project := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨value, hvalue, hvalueProject⟩
    rcases hrelated.1 value hvalue with ⟨other, hother, hrelation⟩
    exact ⟨other, hother, (hproject hrelation).symm.trans hvalueProject⟩
  · rintro ⟨value, hvalue, hvalueProject⟩
    rcases hrelated.2 value hvalue with ⟨other, hother, hrelation⟩
    exact ⟨other, hother, (hproject hrelation).trans hvalueProject⟩

private theorem listMap_mem_iff_of_related
    {alpha beta : Type} (relation : alpha -> alpha -> Prop)
    (project : alpha -> beta)
    (hproject : ∀ {left right}, relation left right -> project left = project right)
    {left right : List alpha} (hrelated : listsRelatedAsSets relation left right)
    (result : beta)
    : result ∈ left.map project ↔ result ∈ right.map project := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨value, hvalue, hvalueProject⟩
    rcases hrelated.1 value hvalue with ⟨other, hother, hrelation⟩
    exact ⟨other, hother, (hproject hrelation).symm.trans hvalueProject⟩
  · rintro ⟨value, hvalue, hvalueProject⟩
    rcases hrelated.2 value hvalue with ⟨other, hother, hrelation⟩
    exact ⟨other, hother, (hproject hrelation).trans hvalueProject⟩

private theorem listMax_eq_of_mem_iff
    {alpha : Type} [Max alpha] [LE alpha] [Std.IsLinearOrder alpha]
    [Std.LawfulOrderMax alpha]
    {left right : List alpha} (hmem : ∀ value, value ∈ left ↔ value ∈ right)
    : left.max? = right.max? := by
  cases hleft : left.max? with
  | none =>
      have hleftNil := List.max?_eq_none_iff.mp hleft
      have hrightNil : right = [] := by
        cases right with
        | nil => rfl
        | cons value rest =>
            have : value ∈ left := (hmem value).mpr (by simp)
            simp [hleftNil] at this
      simp [hrightNil]
  | some maximum =>
      rw [List.max?_eq_some_iff] at hleft
      symm
      apply List.max?_eq_some_iff.mpr
      exact ⟨(hmem maximum).mp hleft.1,
        fun value hvalue => hleft.2 value ((hmem value).mpr hvalue)⟩

private theorem slicingArgumentSize_eq_of_argumentValues
    {left right : List Argument}
    (hvalues
      : ∀ argumentName,
          listsRelatedAsSets InputValue.equivalent
            (argumentValues left argumentName) (argumentValues right argumentName))
    (argumentName : Name)
    : slicingArgumentSize? left argumentName
      = slicingArgumentSize? right argumentName := by
  unfold slicingArgumentSize?
  apply listMax_eq_of_mem_iff
  exact listFilterMap_mem_iff_of_related InputValue.equivalent inferListSize?
    inferListSize_eq_of_equivalent (hvalues argumentName)

private theorem expectedSize_eq_of_argumentValues
    (listSize : ListSize)
    {left right : List Argument}
    (hvalues
      : ∀ argumentName,
          listsRelatedAsSets InputValue.equivalent
            (argumentValues left argumentName) (argumentValues right argumentName))
    : listSize.expectedSize? left = listSize.expectedSize? right := by
  have hslicing :
      listSize.slicingArguments.filterMap
          (slicingArgumentSize? left)
        = listSize.slicingArguments.filterMap
          (slicingArgumentSize? right) := by
    apply congrArg
      (fun project : Name -> Option Nat =>
        listSize.slicingArguments.filterMap project)
    funext argumentName
    exact slicingArgumentSize_eq_of_argumentValues hvalues argumentName
  unfold ListSize.expectedSize?
  rw [hslicing]

private theorem argumentsCost_eq_of_argumentValues
    (schema : Schema) (model : CostModel)
    (field : FieldCoordinate)
    (definitions : List InputValueDefinition) {left right : List Argument}
    (hvalues
      : ∀ argumentName,
          listsRelatedAsSets InputValue.equivalent
            (argumentValues left argumentName) (argumentValues right argumentName))
    : argumentsCost schema model field definitions left
      = argumentsCost schema model field definitions right := by
  unfold argumentsCost
  apply congrArg
    (fun step : Int -> InputValueDefinition -> Int => definitions.foldl step 0)
  funext cost definition
  have hmaximum :
      maximumInt?
          ((argumentValues left definition.name).map
            fun value =>
              inputValueCost schema model
                (.argumentDefinition field definition.name) definition value)
        = maximumInt?
          ((argumentValues right definition.name).map
            fun value =>
              inputValueCost schema model
                (.argumentDefinition field definition.name) definition value) := by
    apply listMax_eq_of_mem_iff
    exact listMap_mem_iff_of_related InputValue.equivalent
      (fun value =>
        inputValueCost schema model
          (.argumentDefinition field definition.name) definition value)
      (inputValueCost_eq_of_equivalent schema model
        (.argumentDefinition field definition.name) definition)
      (hvalues definition.name)
  dsimp only
  rw [hmaximum]

private theorem argumentValues_related_of_argumentsEquivalent
    {left right : List Argument}
    (hequivalent : Argument.argumentsEquivalent left right)
    (argumentName : Name)
    : listsRelatedAsSets InputValue.equivalent
        (argumentValues left argumentName) (argumentValues right argumentName) := by
  constructor
  · intro value hvalue
    rcases List.mem_filterMap.mp hvalue with ⟨leftArgument, hleft, hproject⟩
    rcases hequivalent.1 leftArgument hleft with
      ⟨rightArgument, hright, hargument⟩
    rcases leftArgument with ⟨leftName, leftValue⟩
    rcases rightArgument with ⟨rightName, rightValue⟩
    rcases hargument with ⟨hname, hequivalentValue⟩
    change leftName = rightName at hname
    subst rightName
    change leftValue.equivalent rightValue at hequivalentValue
    by_cases hselected : leftName == argumentName
    · simp [hselected] at hproject
      subst value
      exact ⟨rightValue,
        List.mem_filterMap.mpr ⟨{ name := leftName, value := rightValue }, hright, by
          simp [hselected]⟩,
        hequivalentValue⟩
    · simp [hselected] at hproject
  · intro value hvalue
    rcases List.mem_filterMap.mp hvalue with ⟨rightArgument, hright, hproject⟩
    rcases hequivalent.2 rightArgument hright with
      ⟨leftArgument, hleft, hargument⟩
    rcases leftArgument with ⟨leftName, leftValue⟩
    rcases rightArgument with ⟨rightName, rightValue⟩
    rcases hargument with ⟨hname, hequivalentValue⟩
    change leftName = rightName at hname
    subst rightName
    change leftValue.equivalent rightValue at hequivalentValue
    by_cases hselected : leftName == argumentName
    · simp [hselected] at hproject
      subst value
      exact ⟨leftValue,
        List.mem_filterMap.mpr ⟨{ name := leftName, value := leftValue }, hleft, by
          simp [hselected]⟩,
        hequivalentValue⟩
    · simp [hselected] at hproject

private theorem expectedSize_eq_of_argumentsEquivalent
    (listSize : ListSize)
    {left right : List Argument}
    (hequivalent : Argument.argumentsEquivalent left right)
    : listSize.expectedSize? left = listSize.expectedSize? right := by
  apply expectedSize_eq_of_argumentValues
  exact argumentValues_related_of_argumentsEquivalent hequivalent

private theorem argumentsCost_eq_of_argumentsEquivalent
    (schema : Schema) (model : CostModel)
    (field : FieldCoordinate)
    (definitions : List InputValueDefinition) {left right : List Argument}
    (hequivalent : Argument.argumentsEquivalent left right)
    : argumentsCost schema model field definitions left
      = argumentsCost schema model field definitions right := by
  apply argumentsCost_eq_of_argumentValues
  exact argumentValues_related_of_argumentsEquivalent hequivalent

private theorem expectedListSize_eq_of_argumentsEquivalent
    (model : CostModel) (coordinate : FieldCoordinate)
    {left right : List Argument}
    (hequivalent : Argument.argumentsEquivalent left right)
    : expectedListSize? model coordinate left
      = expectedListSize? model coordinate right := by
  unfold expectedListSize?
  cases hlistSize : model.listSize coordinate with
  | none => rfl
  | some listSize =>
      simp only [Option.bind_some]
      exact expectedSize_eq_of_argumentsEquivalent listSize hequivalent

private theorem fieldCallWeight_eq_of_argumentsEquivalent
    (schema : Schema) (model : CostModel)
    (coordinate : FieldCoordinate)
    (definition : FieldDefinition) {left right : List Argument}
    (hequivalent : Argument.argumentsEquivalent left right)
    : fieldCallWeight schema model coordinate definition left
      = fieldCallWeight schema model coordinate definition right := by
  unfold fieldCallWeight
  rw [argumentsCost_eq_of_argumentsEquivalent schema model coordinate
    definition.arguments hequivalent]

private theorem fieldUseCostAtParentType_eq_of_argumentsEquivalent
    (schema : Schema) (model : CostModel)
    (parentType : Name)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    (fieldName : Name) {left right : List Argument}
    (hequivalent : Argument.argumentsEquivalent left right)
    : fieldUseCostAtParentType schema model parentType childSummary
        inheritedSizedFields fieldName left
      = fieldUseCostAtParentType schema model parentType childSummary
          inheritedSizedFields fieldName right := by
  unfold fieldUseCostAtParentType
  cases hlookup : schema.lookupField parentType fieldName with
  | none => rfl
  | some definition =>
      simp only
      have hexpected := expectedListSize_eq_of_argumentsEquivalent model
        (fieldCoordinate parentType fieldName) hequivalent
      have hweight := fieldCallWeight_eq_of_argumentsEquivalent schema model
        (fieldCoordinate parentType fieldName) definition hequivalent
      rw [hexpected]
      unfold fieldCallCost
      rw [hweight]

private theorem fieldUseCostAtParentTypeWithVariables_eq_of_argumentsEquivalent
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (parentType : Name)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    (fieldName : Name) {left right : List Argument}
    (hright : (right.map Argument.name).Nodup)
    (hequivalent : Argument.argumentsEquivalent left right)
    : fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
        childSummary inheritedSizedFields fieldName left
      = fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
          childSummary inheritedSizedFields fieldName right := by
  unfold fieldUseCostAtParentTypeWithVariables
  cases hlookup : schema.lookupField parentType fieldName with
  | none => rfl
  | some definition =>
      have hcoercion :=
        Execution.coerceArgumentValues_equivalent_of_equivalent_rightNodup schema
          variableValues definition.arguments hright hequivalent
      have harguments : Argument.argumentsEquivalent
          (argumentCoercionResultArguments
            (Execution.coerceArgumentValues schema variableValues definition.arguments
              left))
          (argumentCoercionResultArguments
            (Execution.coerceArgumentValues schema variableValues definition.arguments
              right)) := by
        cases hleft
              : Execution.coerceArgumentValues schema variableValues
                  definition.arguments left with
        | error =>
            cases hright'
                  : Execution.coerceArgumentValues schema variableValues
                      definition.arguments right with
            | error =>
                simp [argumentCoercionResultArguments, Argument.argumentsEquivalent]
            | success rightArguments =>
                simp [hleft, hright', Execution.ArgumentCoercionResult.equivalent]
                  at hcoercion
        | success leftArguments =>
            cases hright'
                  : Execution.coerceArgumentValues schema variableValues
                      definition.arguments right with
            | error =>
                simp [hleft, hright', Execution.ArgumentCoercionResult.equivalent]
                  at hcoercion
            | success rightArguments =>
                have hcoerced : Execution.CoercedArgument.argumentsEquivalent
                    leftArguments rightArguments := by
                  simpa [hleft, hright', Execution.ArgumentCoercionResult.equivalent]
                    using hcoercion
                simp only [argumentCoercionResultArguments]
                constructor
                · intro argument hargument
                  rcases List.mem_map.mp hargument with
                    ⟨leftArgument, hleftMem, rfl⟩
                  rcases hcoerced.1 leftArgument hleftMem with
                    ⟨rightArgument, hrightMem, hequivalent⟩
                  exact ⟨rightArgument.toArgument,
                    List.mem_map.mpr ⟨rightArgument, hrightMem, rfl⟩, hequivalent⟩
                · intro argument hargument
                  rcases List.mem_map.mp hargument with
                    ⟨rightArgument, hrightMem, rfl⟩
                  rcases hcoerced.2 rightArgument hrightMem with
                    ⟨leftArgument, hleftMem, hequivalent⟩
                  exact ⟨leftArgument.toArgument,
                    List.mem_map.mpr ⟨leftArgument, hleftMem, rfl⟩, hequivalent⟩
      exact fieldUseCostAtParentType_eq_of_argumentsEquivalent schema model parentType
        childSummary inheritedSizedFields fieldName harguments

def ResponseObservationBound (concrete : ResponseObservation) (abstract : Summary)
    : Prop :=
  ∀ sizedFields,
    concrete.admissible sizedFields
    -> concrete.cost sizedFields ≤ (abstract sizedFields).toCost

theorem empty_bound : ResponseObservationBound .empty (fun _sizedFields => .zero) := by
  intro _sizedFields _hadmissible
  exact actualCost_le_refl .zero

theorem combine_bound
    {concreteLeft concreteRight : ResponseObservation}
    {abstractLeft abstractRight : Summary}
    (hleft : ResponseObservationBound concreteLeft abstractLeft)
    (hright : ResponseObservationBound concreteRight abstractRight)
    : ResponseObservationBound
        (concreteLeft.combine concreteRight)
        (fun sizedFields =>
          Bound.add (abstractLeft sizedFields) (abstractRight sizedFields)) := by
  intro sizedFields hadmissible
  rw [bound_toCost_add]
  exact actualCost_add_le_add
    (hleft sizedFields hadmissible.1) (hright sizedFields hadmissible.2)

theorem concreteAlgebra_lawful (schema : Schema) (model : CostModel)
    : (concreteAlgebra schema model).Lawful := by
  constructor
  · intro left middle right
    cases left
    cases middle
    cases right
    simp [concreteAlgebra, ResponseObservation.combine, Cost.add, Int.add_assoc,
      Nat.add_assoc,
      and_assoc]
  · intro value
    cases value
    simp [concreteAlgebra, ResponseObservation.empty, ResponseObservation.combine,
      actualCost_zero_add]
  · intro value
    cases value
    simp [concreteAlgebra, ResponseObservation.empty, ResponseObservation.combine,
      actualCost_add_zero]

def algebraLawful (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues)
    : (algebra schema model variableValues).Lawful :=
  {
    le := fun lower upper => ∀ sizedFields, lower sizedFields ≤ upper sizedFields
    le_refl := fun _ _ => cost_le_refl _
    le_trans :=
      fun _ _ _ hleft hright sizedFields =>
        cost_le_trans (hleft sizedFields) (hright sizedFields)
    combine_assoc := by
      intro left middle right
      funext sizedFields
      cases left sizedFields
      cases middle sizedFields
      cases right sizedFields
      simp [Bound.add, Nat.add_assoc]
    combine_comm := by
      intro left right
      funext sizedFields
      cases left sizedFields
      cases right sizedFields
      simp [Bound.add, Nat.add_comm]
    empty_combine := by
      intro value
      funext sizedFields
      rcases hvalue : value sizedFields with ⟨typeCost, fieldCost⟩
      simp [Bound.add, Bound.zero, hvalue]
    combine_empty := by
      intro value
      funext sizedFields
      rcases hvalue : value sizedFields with ⟨typeCost, fieldCost⟩
      simp [Bound.add, Bound.zero, hvalue]
    empty_le := fun _ _ => cost_zero_le _
    combine_mono := by
      intro left lower right upper hleft hright sizedFields
      exact cost_add_le_add (hleft sizedFields) (hright sizedFields)
    le_join_left := fun _ _ _ => cost_le_max_left _ _
    le_join_right := fun _ _ _ => cost_le_max_right _ _
  }

private inductive CostComponent where
  | typeCost
  | fieldCost

private def CostComponent.get : CostComponent -> Bound -> Nat
  | .typeCost, cost => cost.typeCost
  | .fieldCost, cost => cost.fieldCost

private def CostComponent.set : CostComponent -> Bound -> Nat -> Bound
  | .typeCost, cost, value => { cost with typeCost := value }
  | .fieldCost, cost, value => { cost with fieldCost := value }

@[simp]
private theorem CostComponent.get_set (component : CostComponent)
    (cost : Bound) (value : Nat)
    : component.get (component.set cost value) = value := by
  cases component <;> rfl

private theorem CostComponent.get_mono (component : CostComponent)
    {lower upper : Bound} (hle : lower ≤ upper)
    : component.get lower ≤ component.get upper := by
  cases component
  · exact hle.1
  · exact hle.2

private theorem CostComponent.le_set (component : CostComponent)
    {lower upper : Bound} {value : Nat}
    (hle : lower ≤ upper) (hcomponent : component.get lower ≤ value)
    : lower ≤ component.set upper value := by
  cases component
  · exact ⟨hcomponent, hle.2⟩
  · exact ⟨hle.1, hcomponent⟩

private theorem summaryBestBound_component_attainsAt
    {outcomes : OutcomeSet Summary} {estimate : Summary}
    (hbest : BestBound SummaryBound SummaryBound outcomes estimate)
    (component : CostComponent)
    (sizedFields : List SizedField)
    : ∃ outcome,
        outcomes outcome
        ∧ component.get (outcome sizedFields) = component.get (estimate sizedFields) := by
  classical
  by_cases hattained : ∃ outcome, outcomes outcome
      ∧ component.get (outcome sizedFields) = component.get (estimate sizedFields)
  · exact hattained
  · cases hvalue : component.get (estimate sizedFields) with
    | zero =>
        rcases hbest.feasible with ⟨outcome, houtcome⟩
        have hsound := hbest.sound outcome houtcome sizedFields
        have hzero : component.get (outcome sizedFields) = 0 := by
          apply Nat.eq_zero_of_le_zero
          simpa [hvalue] using component.get_mono hsound
        exact ⟨outcome, houtcome, hzero⟩
    | succ predecessor =>
        let candidate : Summary :=
          fun current =>
            if current = sizedFields then
              component.set (estimate current) predecessor
            else
              estimate current
        have hbound : ∀ outcome, outcomes outcome ->
            ∀ current, outcome current ≤ candidate current := by
          intro outcome houtcome current
          have hsound := hbest.sound outcome houtcome current
          by_cases hcurrent : current = sizedFields
          · subst current
            have hne : component.get (outcome sizedFields) ≠ Nat.succ predecessor := by
              intro heq
              exact hattained ⟨outcome, houtcome, heq.trans hvalue.symm⟩
            have hcomponent : component.get (outcome sizedFields) ≤ predecessor :=
              Nat.le_of_lt_succ
                (Nat.lt_of_le_of_ne
                  (by simpa [hvalue] using component.get_mono hsound) hne)
            simp only [candidate, ↓reduceIte]
            exact component.le_set hsound hcomponent
          · simpa [candidate, hcurrent] using hsound
        have hleast := hbest.least candidate hbound sizedFields
        have himpossible : Nat.succ predecessor ≤ predecessor := by
          simpa [candidate, hvalue] using component.get_mono hleast
        exact False.elim (Nat.not_succ_le_self predecessor himpossible)

private theorem accumulator_le_foldl_project_max
    {α : Type} (project : α -> Bound) (values : List α) (accumulator : Bound)
    : accumulator
      ≤ values.foldl (fun maximum candidate => Bound.max maximum (project candidate))
          accumulator := by
  induction values generalizing accumulator with
  | nil => exact cost_le_refl _
  | cons first rest ih =>
      exact cost_le_trans (cost_le_max_left _ _) (ih _)

private theorem project_le_foldl_max_of_mem
    {α : Type} (project : α -> Bound) (value : α) (values : List α)
    (accumulator : Bound) (hvalue : value ∈ values)
    : project value
      ≤ values.foldl (fun maximum candidate => Bound.max maximum (project candidate))
          accumulator := by
  induction values generalizing accumulator with
  | nil => simp at hvalue
  | cons first rest ih =>
      simp only [List.mem_cons] at hvalue
      rw [List.foldl_cons]
      cases hvalue with
      | inl heq =>
          subst value
          exact cost_le_trans (cost_le_max_right _ _)
            (accumulator_le_foldl_project_max project rest _)
      | inr hrest => exact ih _ hrest

private theorem foldl_project_max_le
    {α : Type} (project : α -> Bound) (values : List α)
    (accumulator upper : Bound)
    (haccumulator : accumulator ≤ upper)
    (hproject : ∀ value, value ∈ values -> project value ≤ upper)
    : values.foldl (fun maximum candidate => Bound.max maximum (project candidate))
        accumulator
      ≤ upper := by
  induction values generalizing accumulator with
  | nil => exact haccumulator
  | cons first rest ih =>
      apply ih
      · exact cost_max_le haccumulator (hproject first (by simp))
      · intro value hvalue
        exact hproject value (by simp [hvalue])

private theorem foldl_project_max_mono
    {α : Type} (left right : α -> Bound) (values : List α)
    (leftAccumulator rightAccumulator : Bound)
    (haccumulator : leftAccumulator ≤ rightAccumulator)
    (hproject : ∀ value, value ∈ values -> left value ≤ right value)
    : values.foldl (fun maximum candidate => Bound.max maximum (left candidate))
        leftAccumulator
      ≤ values.foldl (fun maximum candidate => Bound.max maximum (right candidate))
          rightAccumulator := by
  induction values generalizing leftAccumulator rightAccumulator with
  | nil => exact haccumulator
  | cons first rest ih =>
      apply ih
      · exact cost_max_mono haccumulator (hproject first (by simp))
      · intro value hvalue
        exact hproject value (by simp [hvalue])

private def selectionCost (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    : Selection -> Bound
  | selection =>
      match selectionFieldUse? selection with
      | none => .zero
      | some (fieldName, arguments) =>
          fieldUseCost schema model variableValues group childSummary
            inheritedSizedFields fieldName arguments

private theorem groupCost_eq_foldl_selectionCost
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    : groupCost schema model variableValues group childSummary inheritedSizedFields
      = group.selections.foldl
          (fun maximum selection =>
            Bound.max maximum
              (selectionCost schema model variableValues group childSummary
                inheritedSizedFields selection))
          0 := by
  unfold groupCost
  apply congrArg
    (fun step : Bound -> Selection -> Bound => group.selections.foldl step .zero)
  funext cost selection
  cases cost
  cases selection <;> simp [selectionCost, selectionFieldUse?, Bound.max, Bound.zero]

private theorem fieldUseCost_le_groupCost_of_selection
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hselection
      : Selection.field responseName fieldName arguments directives selectionSet
        ∈ group.selections)
    : fieldUseCost schema model variableValues group childSummary inheritedSizedFields
        fieldName arguments
      ≤ groupCost schema model variableValues group childSummary
          inheritedSizedFields := by
  rw [groupCost_eq_foldl_selectionCost]
  simpa [selectionCost, selectionFieldUse?] using
    project_le_foldl_max_of_mem
      (selectionCost schema model variableValues group childSummary
        inheritedSizedFields)
      (.field responseName fieldName arguments directives selectionSet) group.selections 0
      hselection

private theorem fieldUseCostAtParentType_le_fieldUseCost
    (schema : Schema) (model : CostModel) (group : CollectedFieldGroup)
    (variableValues : Execution.VariableValues)
    (childSummary : Summary) (inheritedSizedFields : List SizedField)
    (runtimeType fieldName : Name) (arguments : List Argument)
    (hruntimeType : runtimeType ∈ group.condition.possibleTypes)
    : fieldUseCostAtParentTypeWithVariables schema model variableValues runtimeType
        childSummary inheritedSizedFields fieldName arguments
      ≤ fieldUseCost schema model variableValues group childSummary
          inheritedSizedFields fieldName arguments := by
  exact project_le_foldl_max_of_mem
    (fun parentType =>
      fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
        childSummary inheritedSizedFields fieldName arguments)
    runtimeType group.condition.possibleTypes 0 hruntimeType

private theorem fieldUseCostAtParentType_mono
    (schema : Schema) (model : CostModel)
    (parentType : Name)
    (lower upper : Summary)
    (hle : ∀ sizedFields, lower sizedFields ≤ upper sizedFields)
    (inheritedSizedFields : List SizedField) (fieldName : Name)
    (arguments : List Argument)
    : fieldUseCostAtParentType schema model parentType lower
        inheritedSizedFields fieldName arguments
      ≤ fieldUseCostAtParentType schema model parentType upper
          inheritedSizedFields fieldName arguments := by
  unfold fieldUseCostAtParentType
  cases hlookup : schema.lookupField parentType fieldName with
  | none => exact hle []
  | some definition =>
      let childContext :=
        childSizedFields model (fieldCoordinate parentType fieldName)
          (expectedListSize? model (fieldCoordinate parentType fieldName) arguments)
      have hchild := hle childContext
      constructor
      · apply Int.toNat_le_toNat
        apply Int.mul_le_mul_of_nonneg_left
        · exact Int.add_le_add_left (Int.ofNat_le.mpr hchild.1) _
        · exact Int.natCast_nonneg _
      · simpa [childContext] using
          Nat.add_le_add_left
            (Nat.mul_le_mul_left
              (staticInstanceCount model (fieldCoordinate parentType fieldName) fieldName
                definition (expectedListSize? model
                  (fieldCoordinate parentType fieldName) arguments)
                inheritedSizedFields)
              hchild.2)
            (fieldCallCost schema model
              (fieldCoordinate parentType fieldName) definition arguments)

private theorem fieldUseCost_mono
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (lower upper : Summary)
    (hle : ∀ sizedFields, lower sizedFields ≤ upper sizedFields)
    (inheritedSizedFields : List SizedField) (fieldName : Name)
    (arguments : List Argument)
    : fieldUseCost schema model variableValues group lower inheritedSizedFields
        fieldName arguments
      ≤ fieldUseCost schema model variableValues group upper inheritedSizedFields
          fieldName arguments := by
  exact foldl_project_max_mono
    (fun parentType =>
      fieldUseCostAtParentTypeWithVariables schema model variableValues parentType lower
        inheritedSizedFields fieldName arguments)
    (fun parentType =>
      fieldUseCostAtParentTypeWithVariables schema model variableValues parentType upper
        inheritedSizedFields fieldName arguments)
    group.condition.possibleTypes .zero .zero (cost_le_refl _) (by
      intro parentType _hparent
      unfold fieldUseCostAtParentTypeWithVariables
      split
      · exact hle []
      · exact fieldUseCostAtParentType_mono schema model parentType lower upper hle
          inheritedSizedFields fieldName _)

private theorem selectionCost_mono
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (lower upper : Summary)
    (hle : ∀ sizedFields, lower sizedFields ≤ upper sizedFields)
    (inheritedSizedFields : List SizedField) (selection : Selection)
    : selectionCost schema model variableValues group lower inheritedSizedFields selection
      ≤ selectionCost schema model variableValues group upper inheritedSizedFields
          selection := by
  cases selection with
  | inlineFragment => exact cost_le_refl _
  | field responseName fieldName arguments directives selectionSet =>
      exact fieldUseCost_mono schema model variableValues group lower upper hle
        inheritedSizedFields fieldName arguments

private theorem groupCost_mono
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    (lower upper : Summary)
    (hle : ∀ sizedFields, lower sizedFields ≤ upper sizedFields)
    (inheritedSizedFields : List SizedField)
    : groupCost schema model variableValues group lower inheritedSizedFields
      ≤ groupCost schema model variableValues group upper inheritedSizedFields := by
  rw [groupCost_eq_foldl_selectionCost, groupCost_eq_foldl_selectionCost]
  exact foldl_project_max_mono
    (selectionCost schema model variableValues group lower inheritedSizedFields)
    (selectionCost schema model variableValues group upper inheritedSizedFields)
    group.selections .zero .zero (cost_le_refl _) (by
      intro selection _hselection
      exact selectionCost_mono schema model variableValues group lower upper hle
        inheritedSizedFields selection)

private theorem fieldUseCostAtParentType_best_le
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    {children : OutcomeSet Summary} {abstractChildren : Summary}
    (hchildren : BestBound SummaryBound SummaryBound children abstractChildren)
    (inheritedSizedFields : List SizedField) (candidate : Bound)
    (hcandidate
      : ∀ child,
          children child
          -> groupCost schema model variableValues group child inheritedSizedFields
              ≤ candidate)
    (parentType responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hparent : parentType ∈ group.condition.possibleTypes)
    (hselection
      : Selection.field responseName fieldName arguments directives selectionSet
        ∈ group.selections)
    : fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
        abstractChildren inheritedSizedFields fieldName arguments
      ≤ candidate := by
  have hlocalBound : ∀ child, children child ->
      fieldUseCostAtParentTypeWithVariables schema model variableValues parentType child
          inheritedSizedFields fieldName arguments
        ≤ candidate := by
    intro child hchild
    exact cost_le_trans
      (fieldUseCostAtParentType_le_fieldUseCost schema model group variableValues child
        inheritedSizedFields parentType fieldName arguments hparent)
      (cost_le_trans
        (fieldUseCost_le_groupCost_of_selection schema model variableValues group child
          inheritedSizedFields responseName fieldName arguments directives selectionSet
          hselection)
        (hcandidate child hchild))
  cases hlookup : schema.lookupField parentType fieldName with
  | none =>
      rcases summaryBestBound_component_attainsAt hchildren .typeCost [] with
        ⟨typeChild, htypeChild, htype⟩
      change (typeChild []).typeCost = (abstractChildren []).typeCost at htype
      rcases summaryBestBound_component_attainsAt hchildren .fieldCost [] with
        ⟨fieldChild, hfieldChild, hfield⟩
      change (fieldChild []).fieldCost = (abstractChildren []).fieldCost at hfield
      have htypeBound := hlocalBound typeChild htypeChild
      have hfieldBound := hlocalBound fieldChild hfieldChild
      constructor
      · calc
          (fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
              abstractChildren inheritedSizedFields fieldName arguments).typeCost
              = (abstractChildren []).typeCost := by
                  simp [fieldUseCostAtParentTypeWithVariables, hlookup]
          _ = (typeChild []).typeCost := htype.symm
          _ = (fieldUseCostAtParentTypeWithVariables schema model variableValues
                parentType typeChild inheritedSizedFields fieldName arguments).typeCost := by
                  simp [fieldUseCostAtParentTypeWithVariables, hlookup]
          _ ≤ candidate.typeCost := htypeBound.1
      · calc
          (fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
              abstractChildren inheritedSizedFields fieldName arguments).fieldCost
              = (abstractChildren []).fieldCost := by
                  simp [fieldUseCostAtParentTypeWithVariables, hlookup]
          _ = (fieldChild []).fieldCost := hfield.symm
          _ = (fieldUseCostAtParentTypeWithVariables schema model variableValues
                parentType fieldChild inheritedSizedFields fieldName arguments).fieldCost := by
                  simp [fieldUseCostAtParentTypeWithVariables, hlookup]
          _ ≤ candidate.fieldCost := hfieldBound.2
  | some definition =>
      let coercedArguments :=
        argumentCoercionResultArguments
          (Execution.coerceArgumentValues schema variableValues definition.arguments
            arguments)
      let childContext :=
        childSizedFields model (fieldCoordinate parentType fieldName)
          (expectedListSize? model (fieldCoordinate parentType fieldName)
            coercedArguments)
      rcases summaryBestBound_component_attainsAt hchildren .typeCost childContext with
        ⟨typeChild, htypeChild, htype⟩
      change (typeChild childContext).typeCost
        = (abstractChildren childContext).typeCost at htype
      rcases summaryBestBound_component_attainsAt hchildren .fieldCost childContext with
        ⟨fieldChild, hfieldChild, hfield⟩
      change (fieldChild childContext).fieldCost
        = (abstractChildren childContext).fieldCost at hfield
      have htypeBound := hlocalBound typeChild htypeChild
      have hfieldBound := hlocalBound fieldChild hfieldChild
      constructor
      · calc
          (fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
              abstractChildren inheritedSizedFields fieldName arguments).typeCost
              = (fieldUseCostAtParentTypeWithVariables schema model variableValues
                  parentType typeChild inheritedSizedFields fieldName arguments).typeCost := by
                    simp only [fieldUseCostAtParentTypeWithVariables, hlookup,
                      fieldUseCostAtParentType]
                    rw [← htype]
          _ ≤ candidate.typeCost := htypeBound.1
      · calc
          (fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
              abstractChildren inheritedSizedFields fieldName arguments).fieldCost
              = (fieldUseCostAtParentTypeWithVariables schema model variableValues
                  parentType fieldChild inheritedSizedFields fieldName arguments).fieldCost := by
                    simp only [fieldUseCostAtParentTypeWithVariables, hlookup,
                      fieldUseCostAtParentType]
                    rw [← hfield]
          _ ≤ candidate.fieldCost := hfieldBound.2

private theorem groupCost_best_le
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (group : CollectedFieldGroup)
    {children : OutcomeSet Summary} {abstractChildren : Summary}
    (hchildren : BestBound SummaryBound SummaryBound children abstractChildren)
    (candidate : Summary)
    (hcandidate
      : ∀ child,
          children child
          -> ∀ sizedFields,
              groupCost schema model variableValues group child sizedFields
              ≤ candidate sizedFields)
    (inheritedSizedFields : List SizedField)
    : groupCost schema model variableValues group abstractChildren inheritedSizedFields
      ≤ candidate inheritedSizedFields := by
  rw [groupCost_eq_foldl_selectionCost]
  apply foldl_project_max_le _ _ _ _ (cost_zero_le _)
  intro selection hselection
  cases selection with
  | inlineFragment typeCondition directives selectionSet =>
      exact cost_zero_le _
  | field responseName fieldName arguments directives selectionSet =>
      simp only [selectionCost, selectionFieldUse?]
      unfold fieldUseCost
      apply foldl_project_max_le _ _ _ _ (cost_zero_le _)
      intro parentType hparent
      exact fieldUseCostAtParentType_best_le schema model variableValues group hchildren
        inheritedSizedFields (candidate inheritedSizedFields)
        (fun child hchild => hcandidate child hchild inheritedSizedFields)
        parentType responseName fieldName arguments directives selectionSet hparent
        hselection

private theorem fieldUseCostAtParentType_combine_le
    (schema : Schema) (model : CostModel)
    (parentType : Name)
    (left right : Summary) (inheritedSizedFields : List SizedField)
    (fieldName : Name) (arguments : List Argument)
    (houtputCost
      : ∀ definition,
          schema.lookupField parentType fieldName = some definition
          -> 0 ≤ outputTypeCost schema model definition.outputType)
    : fieldUseCostAtParentType schema model parentType
        (fun sizedFields => Bound.add (left sizedFields) (right sizedFields))
        inheritedSizedFields fieldName arguments
      ≤ Bound.add
          (fieldUseCostAtParentType schema model parentType left
            inheritedSizedFields fieldName arguments)
          (fieldUseCostAtParentType schema model parentType right
            inheritedSizedFields fieldName arguments) := by
  unfold fieldUseCostAtParentType
  cases hlookup : schema.lookupField parentType fieldName with
  | none => exact cost_le_refl _
  | some definition =>
      have houtputCost' : 0 ≤ outputTypeCost schema model definition.outputType := by
        exact houtputCost definition hlookup
      simp only
      cases hleft
            : left
                (childSizedFields model (fieldCoordinate parentType fieldName)
                  (expectedListSize? model (fieldCoordinate parentType fieldName)
                    arguments)) with
      | mk leftType leftField =>
          cases hright
                : right
                    (childSizedFields model (fieldCoordinate parentType fieldName)
                      (expectedListSize? model (fieldCoordinate parentType fieldName)
                        arguments)) with
          | mk rightType rightField =>
              have hcount : 0 ≤ Int.ofNat
                  (staticInstanceCount model (fieldCoordinate parentType fieldName)
                    fieldName definition
                    (expectedListSize? model (fieldCoordinate parentType fieldName)
                      arguments)
                    inheritedSizedFields) := Int.natCast_nonneg _
              have hinner :
                  outputTypeCost schema model definition.outputType
                      + Int.ofNat (leftType + rightType)
                    ≤ (outputTypeCost schema model definition.outputType
                        + Int.ofNat leftType)
                      + (outputTypeCost schema model definition.outputType
                        + Int.ofNat rightType) := by
                have hcast : Int.ofNat (leftType + rightType)
                    = Int.ofNat leftType + Int.ofNat rightType := by
                  change (↑(leftType + rightType) : Int)
                    = (↑leftType : Int) + ↑rightType
                  exact Int.natCast_add leftType rightType
                rw [hcast]
                omega
              have hraw :
                  Int.ofNat
                      (staticInstanceCount model (fieldCoordinate parentType fieldName)
                        fieldName definition
                        (expectedListSize? model (fieldCoordinate parentType fieldName)
                          arguments)
                        inheritedSizedFields)
                    * (outputTypeCost schema model definition.outputType
                      + Int.ofNat (leftType + rightType))
                  ≤ Int.ofNat
                      (staticInstanceCount model (fieldCoordinate parentType fieldName)
                        fieldName definition
                        (expectedListSize? model (fieldCoordinate parentType fieldName)
                          arguments)
                        inheritedSizedFields)
                      * (outputTypeCost schema model definition.outputType
                        + Int.ofNat leftType)
                    + Int.ofNat
                      (staticInstanceCount model (fieldCoordinate parentType fieldName)
                        fieldName definition
                        (expectedListSize? model (fieldCoordinate parentType fieldName)
                          arguments)
                        inheritedSizedFields)
                      * (outputTypeCost schema model definition.outputType
                        + Int.ofNat rightType) := by
                have hscaled := Int.mul_le_mul_of_nonneg_left hinner hcount
                simpa only [Int.mul_add] using hscaled
              have hleftNonnegative :
                  0 ≤ Int.ofNat
                      (staticInstanceCount model (fieldCoordinate parentType fieldName)
                        fieldName definition
                        (expectedListSize? model (fieldCoordinate parentType fieldName)
                          arguments)
                        inheritedSizedFields)
                    * (outputTypeCost schema model definition.outputType
                      + Int.ofNat leftType) :=
                Int.mul_nonneg hcount (Int.add_nonneg houtputCost'
                  (Int.natCast_nonneg _))
              have hrightNonnegative :
                  0 ≤ Int.ofNat
                      (staticInstanceCount model (fieldCoordinate parentType fieldName)
                        fieldName definition
                        (expectedListSize? model (fieldCoordinate parentType fieldName)
                          arguments)
                        inheritedSizedFields)
                    * (outputTypeCost schema model definition.outputType
                      + Int.ofNat rightType) :=
                Int.mul_nonneg hcount (Int.add_nonneg houtputCost'
                  (Int.natCast_nonneg _))
              have htype := Int.toNat_le_toNat hraw
              rw [Int.toNat_add hleftNonnegative hrightNonnegative] at htype
              constructor
              · simpa [Bound.add] using htype
              · simp only [Bound.add, Nat.mul_add]
                omega

private theorem fieldUseCostAtParentTypeWithVariables_combine_le
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (parentType : Name)
    (left right : Summary) (inheritedSizedFields : List SizedField)
    (fieldName : Name) (arguments : List Argument)
    (houtputCost
      : ∀ definition,
          schema.lookupField parentType fieldName = some definition
          -> 0 ≤ outputTypeCost schema model definition.outputType)
    : fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
        (fun sizedFields => Bound.add (left sizedFields) (right sizedFields))
        inheritedSizedFields fieldName arguments
      ≤ Bound.add
          (fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
            left inheritedSizedFields fieldName arguments)
          (fieldUseCostAtParentTypeWithVariables schema model variableValues parentType
            right inheritedSizedFields fieldName arguments) := by
  unfold fieldUseCostAtParentTypeWithVariables
  cases hlookup : schema.lookupField parentType fieldName with
  | none => exact cost_le_refl _
  | some definition =>
      exact fieldUseCostAtParentType_combine_le schema model parentType left right
        inheritedSizedFields fieldName
        (argumentCoercionResultArguments
          (Execution.coerceArgumentValues schema variableValues definition.arguments
            arguments))
        houtputCost

private theorem representedGroup_bounds_fieldUseCostAtParentType
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (runtimeType : Name)
    (ref : ObjectRef) (field : Execution.ExecutableField)
    (groups : List CollectedFieldGroup) (group : CollectedFieldGroup)
    (abstractChild : Summary) (inheritedSizedFields : List SizedField)
    (hgroup : group ∈ groups)
    (hconditions
      : TreeSummary.Syntactic.conditionsAllowGroupsAt variableValues runtimeType groups)
    (hmatch
      : TreeSummary.Syntactic.groupsRepresentField schema variableValues runtimeType ref
          groups field)
    (hfieldArgumentsNodup : (field.arguments.map Argument.name).Nodup)
    : fieldUseCostAtParentTypeWithVariables schema model variableValues runtimeType
        abstractChild inheritedSizedFields field.fieldName field.arguments
      ≤ groupCost schema model variableValues group abstractChild
          inheritedSizedFields := by
  rcases hmatch group hgroup with
    ⟨candidate, _hcover, hfieldName, harguments,
      selection, hselection, hselectionEq⟩
  have hruntimeType : runtimeType ∈ group.condition.possibleTypes :=
    List.contains_iff_mem.mp
      (Bool.and_eq_true_iff.mp (hconditions group hgroup)).1
  rw [hselectionEq] at hselection
  have hargumentCost :=
    fieldUseCostAtParentTypeWithVariables_eq_of_argumentsEquivalent schema model
      variableValues runtimeType abstractChild inheritedSizedFields candidate.fieldName
      hfieldArgumentsNodup harguments
  rw [hfieldName] at hargumentCost hselection
  rw [← hargumentCost]
  exact cost_le_trans
    (fieldUseCostAtParentType_le_fieldUseCost schema model group variableValues
      abstractChild inheritedSizedFields runtimeType field.fieldName candidate.arguments
      hruntimeType)
    (fieldUseCost_le_groupCost_of_selection schema model variableValues group
      abstractChild inheritedSizedFields group.responseName field.fieldName
      candidate.arguments [] candidate.selectionSet hselection)

private theorem representedGroups_capacity
    (schema : Schema) (model : CostModel)
    (hnonnegative : TypeCostsNonnegative schema model)
    (variableValues : Execution.VariableValues) (runtimeType : Name)
    (ref : ObjectRef) (field : Execution.ExecutableField)
    (groups : List CollectedFieldGroup)
    (abstractChildren : CollectedFieldGroup -> Summary)
    (inheritedSizedFields : List SizedField)
    (hnonempty : groups ≠ [])
    (hconditions
      : TreeSummary.Syntactic.conditionsAllowGroupsAt variableValues runtimeType groups)
    (hmatch
      : TreeSummary.Syntactic.groupsRepresentField schema variableValues runtimeType ref
          groups field)
    (hfieldArgumentsNodup : (field.arguments.map Argument.name).Nodup)
    : fieldUseCostAtParentTypeWithVariables schema model variableValues runtimeType
        (TreeSummary.Syntactic.foldChildSummaries
          (algebra schema model variableValues) abstractChildren groups)
        inheritedSizedFields field.fieldName field.arguments
      ≤ (TreeSummary.Syntactic.foldFieldGroups (algebra schema model variableValues)
          abstractChildren groups)
          inheritedSizedFields := by
  induction groups with
  | nil => contradiction
  | cons group rest ih =>
      have hgroup := representedGroup_bounds_fieldUseCostAtParentType schema model
        variableValues runtimeType ref field (group :: rest) group
        (abstractChildren group) inheritedSizedFields (by simp) hconditions hmatch
        hfieldArgumentsNodup
      cases rest with
      | nil =>
          simpa [TreeSummary.Syntactic.foldChildSummaries,
            TreeSummary.Syntactic.foldFieldGroups, algebra, cost_add_zero] using hgroup
      | cons next tail =>
          have hrest := ih (by simp) (by
            intro candidate hcandidate
            exact hconditions candidate (by simp [hcandidate])) (by
            intro candidate hcandidate
            exact hmatch candidate (by simp [hcandidate]))
          simp [TreeSummary.Syntactic.foldChildSummaries,
            TreeSummary.Syntactic.foldFieldGroups, algebra] at hrest
          have hsplit := fieldUseCostAtParentTypeWithVariables_combine_le schema model
            variableValues runtimeType
            (abstractChildren group)
            (TreeSummary.Syntactic.foldChildSummaries
              (algebra schema model variableValues) abstractChildren (next :: tail))
            inheritedSizedFields field.fieldName field.arguments
            (fun definition _hlookup => by
              exact hnonnegative definition.outputType.namedType)
          exact cost_le_trans (by
            simpa [TreeSummary.Syntactic.foldChildSummaries, algebra] using hsplit)
            (by
              simpa [TreeSummary.Syntactic.foldFieldGroups, algebra] using
                cost_add_le_add hgroup hrest)

private theorem cost_add_scale (left right : Nat) (cost : Bound)
    : Bound.add (Bound.scale left cost) (Bound.scale right cost)
      = Bound.scale (left + right) cost := by
  cases cost
  simp [Bound.add, Bound.scale, Nat.add_mul]

mutual
  private theorem responseValueTypeCost_le
      (schema : Schema) (model : CostModel) (outputType : TypeRef)
      (value : AnnotatedResponseValue)
      : responseValueTypeCost schema model outputType value
        ≤ actualInstanceCount value * outputTypeCost schema model outputType := by
    cases value with
    | null =>
        simp [responseValueTypeCost, actualInstanceCount]
    | scalar value =>
        simp [responseValueTypeCost, responseLeafTypeCost, actualInstanceCount]
    | object runtimeType fields =>
        simp [responseValueTypeCost, actualInstanceCount]
    | list values =>
        simpa [responseValueTypeCost, actualInstanceCount] using
          responseValuesTypeCost_le schema model outputType values

  private theorem responseValuesTypeCost_le
      (schema : Schema) (model : CostModel) (outputType : TypeRef)
      (values : List AnnotatedResponseValue)
      : responseValuesTypeCost schema model outputType values
        ≤ actualInstanceCountList values * outputTypeCost schema model outputType := by
    cases values with
    | nil => simp [responseValuesTypeCost, actualInstanceCountList]
    | cons value rest =>
        exact Int.le_trans
          (Int.add_le_add
            (responseValueTypeCost_le schema model outputType value)
            (responseValuesTypeCost_le schema model outputType rest))
          (by simp [actualInstanceCountList, Int.add_mul])
end

mutual
  private theorem foldChildSummaryForValue_le_scale
      (schema : Schema) (model : CostModel)
      (variableValues : Execution.VariableValues) (childSummary : Summary)
      (value : AnnotatedResponseValue) (sizedFields : List SizedField)
      : foldChildSummaryForValue (algebra schema model variableValues) childSummary value
          sizedFields
        ≤ Bound.scale (actualInstanceCount value) (childSummary sizedFields) := by
    cases value with
    | null =>
        simpa [foldChildSummaryForValue, actualInstanceCount, Bound.scale,
          Bound.zero]
          using cost_le_refl Bound.zero
    | scalar value =>
        simpa [foldChildSummaryForValue, actualInstanceCount, algebra,
          Bound.scale] using cost_zero_le (childSummary sizedFields)
    | object runtimeType fields =>
        simpa [foldChildSummaryForValue, actualInstanceCount, Bound.scale]
          using cost_le_refl (childSummary sizedFields)
    | list values =>
        exact foldChildSummaryForValues_le_scale schema model variableValues childSummary
          values sizedFields

  private theorem foldChildSummaryForValues_le_scale
      (schema : Schema) (model : CostModel)
      (variableValues : Execution.VariableValues) (childSummary : Summary)
      (values : List AnnotatedResponseValue) (sizedFields : List SizedField)
      : foldChildSummaryForValues (algebra schema model variableValues) childSummary
          values sizedFields
        ≤ Bound.scale (actualInstanceCountList values) (childSummary sizedFields) := by
    cases values with
    | nil =>
        simpa [foldChildSummaryForValues, actualInstanceCountList, Bound.scale,
          Bound.zero]
          using cost_le_refl Bound.zero
    | cons value rest =>
        change Bound.add
            (foldChildSummaryForValue (algebra schema model variableValues) childSummary
              value sizedFields)
            (foldChildSummaryForValues (algebra schema model variableValues) childSummary
              rest sizedFields)
          ≤ Bound.scale
              (actualInstanceCount value
                + actualInstanceCountList rest)
              (childSummary sizedFields)
        rw [← cost_add_scale]
        exact cost_add_le_add
          (foldChildSummaryForValue_le_scale schema model variableValues childSummary
            value sizedFields)
          (foldChildSummaryForValues_le_scale schema model variableValues childSummary
            rest sizedFields)
end

private theorem scaled_signed_le_staticBound
    {actualCount staticCount : Nat} (hcount : actualCount ≤ staticCount)
    (value : Int)
    : Int.ofNat actualCount * value
      ≤ Int.ofNat (Int.ofNat staticCount * value).toNat := by
  change Int.ofNat actualCount * value
    ≤ (↑(Int.ofNat staticCount * value).toNat : Int)
  rw [Int.ofNat_toNat]
  by_cases hvalue : 0 ≤ value
  · exact Int.le_trans
      (Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hcount) hvalue)
      (Int.le_max_left _ _)
  · exact Int.le_trans
      (Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _)
        (Int.le_of_lt (Int.lt_of_not_ge hvalue)))
      (Int.le_max_right _ _)

private theorem responseFieldCost_le_fieldUseCostAtParentType
    (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (field : Execution.ExecutableField)
    (schemaDefinition : FieldDefinition) (value : AnnotatedResponseValue)
    (children : ResponseObservation) (abstractChild : Summary)
    (inheritedSizedFields : List SizedField)
    (hlookup
      : schema.lookupField field.parentType field.fieldName = some schemaDefinition)
    (hchildren
      : ResponseObservationBound children
          (fun sizedFields =>
            Bound.scale (actualInstanceCount value) (abstractChild sizedFields)))
    (hadmissible
      : responseFieldAdmissible schema model
          (resolvedFieldProvenance schema variableValues schemaDefinition field)
          value children inheritedSizedFields)
    : responseFieldCost schema model
        (resolvedFieldProvenance schema variableValues schemaDefinition field)
        value children
        inheritedSizedFields
      ≤ (fieldUseCostAtParentType schema model field.parentType abstractChild
          inheritedSizedFields field.fieldName
          (argumentCoercionResultArguments
            (Execution.coerceArgumentValues schema variableValues
              schemaDefinition.arguments field.arguments))).toCost := by
  simp only [resolvedFieldProvenance] at hadmissible ⊢
  let parentType := field.parentType
  let fieldName := field.fieldName
  let arguments :=
    argumentCoercionResultArguments
      (Execution.coerceArgumentValues schema variableValues schemaDefinition.arguments
        field.arguments)
  have hlookup' : schema.lookupField parentType fieldName = some schemaDefinition :=
    hlookup
  let coordinate := fieldCoordinate parentType fieldName
  let expectedSize :=
    expectedListSize? model coordinate arguments
  let childContext :=
    childSizedFields model coordinate expectedSize
  let callWeight :=
    fieldCallWeight schema model coordinate schemaDefinition arguments
  have hadmissible' :
      actualInstanceCount value
            ≤ staticInstanceCount model coordinate fieldName schemaDefinition
                expectedSize inheritedSizedFields
        ∧ children.admissible childContext := by
    simpa [responseFieldAdmissible, hlookup, hlookup', parentType, fieldName, arguments,
      coordinate, expectedSize, childContext] using hadmissible
  have hchild := hchildren childContext hadmissible'.2
  have htype := responseValueTypeCost_le schema model schemaDefinition.outputType value
  let perInstanceTypeCost :=
    outputTypeCost schema model schemaDefinition.outputType
      + Int.ofNat (abstractChild childContext).typeCost
  have hchildType : (children.cost childContext).typeCost
      ≤ Int.ofNat (actualInstanceCount value)
          * Int.ofNat (abstractChild childContext).typeCost := by
    simpa [Bound.toCost, Bound.scale] using hchild.1
  have hvalueType :
      responseValueTypeCost schema model schemaDefinition.outputType value
          + (children.cost childContext).typeCost
        ≤ Int.ofNat (actualInstanceCount value) * perInstanceTypeCost := by
    rw [Int.mul_add]
    exact Int.add_le_add htype hchildType
  have hvalueField :
      callWeight.toNat + (children.cost childContext).fieldCost
        ≤ callWeight.toNat
          + actualInstanceCount value
            * (abstractChild childContext).fieldCost :=
    Nat.add_le_add_left hchild.2 callWeight.toNat
  have hscaledType :=
    scaled_signed_le_staticBound hadmissible'.1 perInstanceTypeCost
  have hscaledField := Nat.mul_le_mul hadmissible'.1
    (Nat.le_refl (abstractChild childContext).fieldCost)
  have hfinalType :
      Int.ofNat (actualInstanceCount value) * perInstanceTypeCost
        ≤ (fieldUseCostAtParentType schema model parentType abstractChild
            inheritedSizedFields fieldName arguments).toCost.typeCost := by
    simpa [fieldUseCostAtParentType, hlookup', coordinate, expectedSize,
      childContext, perInstanceTypeCost, Bound.toCost] using hscaledType
  have hfinalField :
      callWeight.toNat
          + actualInstanceCount value * (abstractChild childContext).fieldCost
        ≤ (fieldUseCostAtParentType schema model parentType abstractChild
            inheritedSizedFields fieldName arguments).toCost.fieldCost := by
    simpa [fieldUseCostAtParentType, hlookup', coordinate, expectedSize,
      childContext, fieldCallCost, callWeight, Bound.toCost] using
      Nat.add_le_add_left hscaledField callWeight.toNat
  constructor
  · cases value with
    | null =>
        exact Int.le_trans (by simp [responseFieldCost, hlookup])
          (Int.natCast_nonneg _)
    | scalar scalarValue =>
        have hleaf : responseLeafTypeCost schema model schemaDefinition.outputType
            ≤ perInstanceTypeCost := by
          exact Int.le_add_of_nonneg_right (Int.natCast_nonneg _)
        exact Int.le_trans (by
          simpa [responseFieldCost, hlookup, parentType, fieldName, arguments,
            responseLeafTypeCost, actualInstanceCount] using hleaf) hfinalType
    | list values =>
        exact Int.le_trans (by
          simpa [responseFieldCost, hlookup, parentType, fieldName, arguments, coordinate,
            expectedSize, childContext, responseValueTypeCost] using hvalueType) hfinalType
    | object runtimeType fields =>
        exact Int.le_trans (by
          simpa [responseFieldCost, hlookup, parentType, fieldName, arguments, coordinate,
            expectedSize, childContext, responseValueTypeCost] using hvalueType) hfinalType
  · cases value with
    | list values | object _ _ =>
        exact Nat.le_trans (by
          simpa [responseFieldCost, hlookup, parentType, fieldName, arguments, coordinate,
            expectedSize, childContext, callWeight] using hvalueField) hfinalField
    | null =>
        have hcall : callWeight.toNat
            ≤ callWeight.toNat
              + actualInstanceCount .null * (abstractChild childContext).fieldCost :=
          Nat.le_add_right _ _
        exact Nat.le_trans (by
          simp [responseFieldCost, hlookup, parentType, fieldName, arguments,
            coordinate, callWeight]) hfinalField
    | scalar scalarValue =>
        have hcall : callWeight.toNat
            ≤ callWeight.toNat
              + actualInstanceCount (.scalar scalarValue)
                * (abstractChild childContext).fieldCost :=
          Nat.le_add_right _ _
        exact Nat.le_trans (by
          simp [responseFieldCost, hlookup, parentType, fieldName, arguments,
            coordinate, callWeight]) hfinalField

private theorem actualCost_le_staticBound
    (schema : Schema) (model : CostModel) (response : AnnotatedResponse)
    (selectionBound : Bound)
    (hroot
      : response.data = .null
        ∨ ∃ runtimeType fields, response.data = .object runtimeType fields)
    (hselection
      : (evaluateAnnotatedResponse schema model response).cost [] ≤ selectionBound.toCost)
    : actualCost schema model response
      ≤ {
        typeCost :=
          max 0
            (namedTypeCost schema model schema.queryType
              + Int.ofNat selectionBound.typeCost)
        fieldCost := selectionBound.fieldCost
      } := by
  rcases response with ⟨data, errors⟩
  rcases hroot with hnull | ⟨runtimeType, fields, hobject⟩
  · change data = .null at hnull
    subst data
    constructor
    · simpa [actualCost, responseRootCost, evaluateAnnotatedResponse,
        TreeSummary.foldAnnotatedResponse,
        TreeSummary.foldAnnotatedResponseValueChildren,
        ResponseObservation.empty, Cost.add, Cost.zero] using
        (Int.le_max_left 0
          (namedTypeCost schema model schema.queryType
            + Int.ofNat selectionBound.typeCost))
    · simp [actualCost, responseRootCost, evaluateAnnotatedResponse,
        TreeSummary.foldAnnotatedResponse,
        TreeSummary.foldAnnotatedResponseValueChildren,
        ResponseObservation.empty, Cost.add, Cost.zero]
  · change data = .object runtimeType fields at hobject
    subst data
    constructor
    · exact Int.le_trans (Int.add_le_add_left hselection.1 _)
        (Int.le_max_right _ _)
    · simpa [actualCost, responseRootCost, Cost.add, Bound.toCost] using hselection.2

private theorem executeQueryAnnotatedWithFuel_rootShape
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    : let response :=
        executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source
      response.data = .null
      ∨ ∃ runtimeType fields, response.data = .object runtimeType fields := by
  simp only [executeQueryAnnotatedWithFuel]
  split
  · next hroot =>
      split
      · exact Or.inl rfl
      · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl rfl

namespace ExactCases

-- The static-cost transfer algebra computes feasible pointwise least bounds of its
-- local modeled field costs. In particular, componentwise maxima need not be realized
-- by one case: leastness supplies separate type-cost and field-cost witnesses.
private def bestTransferLaws (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues)
    : TreeSummary.ExactCases.BestTransferLaws
        (caseSemantics schema model variableValues)
        (algebra schema model variableValues) :=
  {
    related := SummaryBound
    le := SummaryBound
    empty_best := by
      let emptySummary : Summary := fun _sizedFields => .zero
      refine ⟨⟨emptySummary, rfl⟩, ?_, ?_⟩
      · intro concrete hconcrete
        subst concrete
        intro sizedFields
        exact cost_le_refl _
      · intro candidate hcandidate
        exact hcandidate emptySummary rfl
    combine_best := by
      intro left right abstractLeft abstractRight hleft hright
      refine ⟨?_, ?_, ?_⟩
      · rcases hleft.feasible with ⟨leftValue, hleftValue⟩
        rcases hright.feasible with ⟨rightValue, hrightValue⟩
        exact ⟨(fun sizedFields =>
            Bound.add (leftValue sizedFields) (rightValue sizedFields)),
          ⟨leftValue, rightValue, hleftValue, hrightValue, rfl⟩⟩
      · intro concrete hconcrete sizedFields
        rcases hconcrete with
          ⟨leftValue, rightValue, hleftValue, hrightValue, rfl⟩
        exact cost_add_le_add
          (hleft.sound leftValue hleftValue sizedFields)
          (hright.sound rightValue hrightValue sizedFields)
      · intro candidate hcandidate sizedFields
        have componentBound (component : CostComponent) :
            component.get
                (Bound.add (abstractLeft sizedFields) (abstractRight sizedFields))
              ≤ component.get (candidate sizedFields) := by
          rcases summaryBestBound_component_attainsAt hleft
              component sizedFields with
            ⟨leftValue, hleftValue, hleftEq⟩
          rcases summaryBestBound_component_attainsAt hright
              component sizedFields with
            ⟨rightValue, hrightValue, hrightEq⟩
          have hbound := hcandidate
            (fun current => Bound.add (leftValue current) (rightValue current))
            ⟨leftValue, rightValue, hleftValue, hrightValue, rfl⟩ sizedFields
          cases component
          · change (leftValue sizedFields).typeCost
              = (abstractLeft sizedFields).typeCost at hleftEq
            change (rightValue sizedFields).typeCost
              = (abstractRight sizedFields).typeCost at hrightEq
            simpa [CostComponent.get, Bound.add, hleftEq, hrightEq] using hbound.1
          · change (leftValue sizedFields).fieldCost
              = (abstractLeft sizedFields).fieldCost at hleftEq
            change (rightValue sizedFields).fieldCost
              = (abstractRight sizedFields).fieldCost at hrightEq
            simpa [CostComponent.get, Bound.add, hleftEq, hrightEq] using hbound.2
        exact ⟨componentBound .typeCost, componentBound .fieldCost⟩
    field_best := by
      intro group children abstractChildren hchildren
      refine ⟨?_, ?_, ?_⟩
      · rcases hchildren.feasible with ⟨child, hchild⟩
        exact ⟨(fun sizedFields =>
            groupCost schema model variableValues group child sizedFields),
          ⟨child, hchild, rfl⟩⟩
      · intro concrete hconcrete sizedFields
        rcases hconcrete with ⟨child, hchild, rfl⟩
        exact groupCost_mono schema model variableValues group child abstractChildren
          (hchildren.sound child hchild) sizedFields
      · intro candidate hcandidate sizedFields
        exact groupCost_best_le schema model variableValues group hchildren candidate
          (fun child hchild current =>
            hcandidate
              (fun fields =>
                groupCost schema model variableValues group child fields)
              ⟨child, hchild, rfl⟩ current)
          sizedFields
    join_best := by
      intro left right abstractLeft abstractRight hleft hright
      refine ⟨?_, ?_, ?_⟩
      · rcases hleft.feasible with ⟨concrete, hconcrete⟩
        exact ⟨concrete, Or.inl hconcrete⟩
      · intro concrete hconcrete sizedFields
        cases hconcrete with
        | inl hleftConcrete =>
            exact cost_le_trans (hleft.sound concrete hleftConcrete sizedFields)
              (cost_le_max_left _ _)
        | inr hrightConcrete =>
            exact cost_le_trans (hright.sound concrete hrightConcrete sizedFields)
              (cost_le_max_right _ _)
      · intro candidate hcandidate sizedFields
        exact cost_max_le
          (hleft.least candidate (fun concrete hconcrete =>
            hcandidate concrete (Or.inl hconcrete)) sizedFields)
          (hright.least candidate (fun concrete hconcrete =>
            hcandidate concrete (Or.inr hconcrete)) sizedFields)
  }

-- Public witness: the variable-aware exact static-cost summary is the pointwise least
-- bound of its local modeled field costs, recursively through every child selection
-- set.
theorem summaryOptimalWithVariables (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : SummaryOptimalWithVariables schema model variableValues operation := by
  have hbest :=
    TreeSummary.ExactCases.summarizeOperationWithVariables_best
      (algebra schema model) (schema := schema) variableValues operation
      (bestTransferLaws schema model
        (Execution.coerceVariableValues operation variableValues))
  change BestBound SummaryBound SummaryBound _ _ at hbest
  simpa [SummaryOptimalWithVariables] using hbest

def compatible (schema : Schema) (model : CostModel)
    (variableValues : Execution.VariableValues)
    : TreeSummary.ExactCases.Compatible (concreteAlgebra schema model)
        (algebra schema model variableValues) schema variableValues :=
  {
    related := ResponseObservationBound
    concreteLawful := concreteAlgebra_lawful schema model
    abstractLawful := algebraLawful schema model variableValues
    empty_related := empty_bound
    combine_related := by
      intro concreteLeft abstractLeft concreteRight abstractRight hleft hright
      exact combine_bound hleft hright
    related_mono := by
      intro concreteValue abstractLower abstractUpper hlower hle sizedFields hadmissible
      exact actualCost_le_trans (hlower sizedFields hadmissible)
        (bound_toCost_le_toCost (hle sizedFields))
    field_related := by
      intro group field definition value children abstractChildren hparent
        hrepresents hlookup _houtput hchildren
      intro inheritedSizedFields hadmissible
      have hchildren' :
          ResponseObservationBound children
            (fun sizedFields =>
              Bound.scale (actualInstanceCount value)
                (abstractChildren sizedFields)) := by
        intro sizedFields hchildrenAdmissible
        exact actualCost_le_trans (hchildren sizedFields hchildrenAdmissible)
          (bound_toCost_le_toCost
            (foldChildSummaryForValue_le_scale schema model variableValues
              abstractChildren value sizedFields))
      have hfield := responseFieldCost_le_fieldUseCostAtParentType schema model
        variableValues field definition value children abstractChildren
        inheritedSizedFields hlookup hchildren' hadmissible
      have hfield' :
          ((concreteAlgebra schema model).field
              (resolvedFieldProvenance schema variableValues definition field) value children).cost
              inheritedSizedFields
            ≤ (fieldUseCostAtParentTypeWithVariables schema model variableValues
                field.parentType abstractChildren inheritedSizedFields field.fieldName
                field.arguments).toCost := by
        simpa [concreteAlgebra, responseFieldObservation,
          fieldUseCostAtParentTypeWithVariables, hlookup] using hfield
      have hparentBound := fieldUseCostAtParentType_le_fieldUseCost schema model group
        variableValues abstractChildren inheritedSizedFields field.parentType
        field.fieldName field.arguments hparent
      have hselectionBound := fieldUseCost_le_groupCost_of_selection schema model
        variableValues group abstractChildren inheritedSizedFields field.responseName
        field.fieldName field.arguments [] field.selectionSet hrepresents
      exact actualCost_le_trans hfield' (bound_toCost_le_toCost
        (cost_le_trans hparentBound (by
          simpa [algebra] using hselectionBound)))
  }

theorem soundWithVariablesWithFuel
    (schema : Schema) (model : CostModel) (operation : Operation)
    : SoundWithVariablesWithFuel schema model operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source hadmissible
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  have hrefinement :=
    TreeSummary.ExactCases.operationWithVariablesSoundWithFuel
      (algebra schema model) (compatible schema model) operation hschema hoperation
      ObjectRef resolvers variableValues fuel source
  have hcost := actualCost_le_staticBound schema model
    (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel source)
    ((TreeSummary.ExactCases.summarizeOperationWithVariables
      (algebra schema model) schema variableValues operation) [])
    (executeQueryAnnotatedWithFuel_rootShape schema resolvers variableValues operation
      fuel source)
    (hrefinement [] hadmissible)
  simpa [ResponseWithinEstimatedSizes, actualCost,
    StaticCost.evaluateAnnotatedResponse, estimateOperationWithVariables,
    coercedVariableValues] using
    hcost

theorem soundWithVariables (schema : Schema) (model : CostModel) (operation : Operation)
    : SoundWithVariables schema model operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source hadmissible
  exact soundWithVariablesWithFuel schema model operation hschema hoperation ObjectRef
    resolvers variableValues (Execution.executeQueryFuelBound schema operation) source
    hadmissible

end ExactCases

namespace Syntactic

def compatible (schema : Schema) (model : CostModel)
    (hnonnegative : TypeCostsNonnegative schema model)
    (variableValues : Execution.VariableValues)
    : TreeSummary.Syntactic.Compatible (concreteAlgebra schema model)
        (algebra schema model variableValues) schema variableValues :=
  {
    related := ResponseObservationBound
    concreteLawful := concreteAlgebra_lawful schema model
    abstractLawful := algebraLawful schema model variableValues
    empty_related := empty_bound
    combine_related := by
      intro concreteLeft abstractLeft concreteRight abstractRight hleft hright
      exact combine_bound hleft hright
    related_mono := by
      intro concreteValue abstractLower abstractUpper hlower hle sizedFields hadmissible
      exact actualCost_le_trans (hlower sizedFields hadmissible)
        (bound_toCost_le_toCost (hle sizedFields))
    field_related := by
      intro ObjectRef runtimeType ref _responseName field _rest definition value children
        groups abstractChildren hparent hlookup hargumentsNodup hnonempty _hinherited
        hconditions _hcover hmatch hchildren
      intro inheritedSizedFields hadmissible
      let combinedChildren :=
        TreeSummary.Syntactic.foldChildSummaries
          (algebra schema model variableValues) abstractChildren groups
      have hchildren' :
          ResponseObservationBound children
            (fun sizedFields =>
              Bound.scale (actualInstanceCount value)
                (combinedChildren sizedFields)) := by
        intro sizedFields hchildrenAdmissible
        exact actualCost_le_trans (hchildren sizedFields hchildrenAdmissible)
          (bound_toCost_le_toCost
            (foldChildSummaryForValue_le_scale schema model variableValues
              combinedChildren value sizedFields))
      have hfield := responseFieldCost_le_fieldUseCostAtParentType schema model
        variableValues field definition value children combinedChildren
        inheritedSizedFields hlookup hchildren' hadmissible
      have hfield' :
          ((concreteAlgebra schema model).field
              (resolvedFieldProvenance schema variableValues definition field) value children).cost
              inheritedSizedFields
            ≤ (fieldUseCostAtParentTypeWithVariables schema model variableValues
                field.parentType combinedChildren inheritedSizedFields field.fieldName
                field.arguments).toCost := by
        simpa [concreteAlgebra, responseFieldObservation,
          fieldUseCostAtParentTypeWithVariables, hlookup] using hfield
      have hcapacity := representedGroups_capacity schema model hnonnegative variableValues
        runtimeType ref field groups abstractChildren inheritedSizedFields hnonempty
        hconditions hmatch hargumentsNodup
      exact actualCost_le_trans hfield' (bound_toCost_le_toCost (by
        simpa [hparent, combinedChildren, algebra] using hcapacity))
  }

theorem soundWithVariablesWithFuel
    (schema : Schema) (model : CostModel) (operation : Operation)
    : SoundWithVariablesWithFuel schema model operation := by
  intro hschema hoperation hnonnegative ObjectRef resolvers variableValues fuel source
    hadmissible
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  have hrefinement :=
    TreeSummary.Syntactic.operationWithVariablesSoundWithFuel
      (concrete := concreteAlgebra schema model)
      (algebra schema model)
      (fun values => compatible schema model hnonnegative values) operation hschema
      hoperation ObjectRef resolvers variableValues fuel source
  have hcost := actualCost_le_staticBound schema model
    (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel source)
    ((TreeSummary.Syntactic.summarizeOperationWithVariables
      (algebra schema model) schema variableValues operation) [])
    (executeQueryAnnotatedWithFuel_rootShape schema resolvers variableValues operation
      fuel source)
    (hrefinement [] hadmissible)
  simpa [ResponseWithinEstimatedSizes, actualCost,
    StaticCost.evaluateAnnotatedResponse, Syntactic.estimateOperationWithVariables,
    coercedVariableValues] using hcost

theorem soundWithVariables (schema : Schema) (model : CostModel) (operation : Operation)
    : SoundWithVariables schema model operation := by
  intro hschema hoperation hnonnegative ObjectRef resolvers variableValues source
    hadmissible
  exact soundWithVariablesWithFuel schema model operation hschema hoperation hnonnegative
    ObjectRef resolvers variableValues (Execution.executeQueryFuelBound schema operation)
    source hadmissible

end Syntactic

end StaticCost
end TreeSummary
end GraphQL
