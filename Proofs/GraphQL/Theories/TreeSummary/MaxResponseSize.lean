import GraphQL.Theories.TreeSummary.MaxResponseSize
import Proofs.GraphQL.Theories.TreeSummary.AnnotationErasure
import Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality

/-! Maximum-response-size soundness and local optimality.

The generic tree-summary theorem first bounds the concrete algebra over an annotated
response. This module then proves two analysis-specific refinement facts: uniformly
bounded resolver lists make the executed annotated response admissible, and erasing its
resolver-call annotations preserves the ordinary structural response size. The public
soundness theorem therefore mentions only resolvers and `Execution.Response`.

The exact-case optimality section separately proves that the response-size algebra's
four local transfers preserve feasible least bounds of its multiplicity semantics.
-/

namespace GraphQL
namespace TreeSummary
namespace MaxResponseSize

open GraphQL.AnnotatedExecution

open Execution
open GraphQL.TreeSummary.Syntactic
open TreeSummary.Optimality

-----------------------------------------------------------------------------------------
-- Concrete-algebra soundness obligations
-----------------------------------------------------------------------------------------

structure ResponseObservation where
  size : Nat
  admissible : Nat -> Prop

def ResponseObservation.empty : ResponseObservation :=
  { size := 0, admissible := fun _listSize => True }

def ResponseObservation.combine (left right : ResponseObservation)
    : ResponseObservation :=
  {
    size := left.size + right.size
    admissible := fun listSize => left.admissible listSize ∧ right.admissible listSize
  }

-- Analysis-specific multiplicity of values that can contain nested response fields.
-- Null and scalar values contribute no children; their containing response fields are
-- still counted by `responseFieldObservation` below.
mutual
  def responseValueChildMultiplicity : AnnotatedResponseValue -> Nat
    | .null => 0
    | .scalar _value => 0
    | .object _runtimeType _fields => 1
    | .list values => responseValuesChildMultiplicity values

  def responseValuesChildMultiplicity : List AnnotatedResponseValue -> Nat
    | [] => 0
    | value :: rest =>
        responseValueChildMultiplicity value + responseValuesChildMultiplicity rest
end

def responseFieldObservation (schema : Schema)
    (definition : ResolvedFieldProvenance) (value : AnnotatedResponseValue)
    (children : ResponseObservation)
    : ResponseObservation :=
  {
    size := 1 + children.size
    admissible :=
      fun listSize =>
        match schema.lookupField definition.parentType definition.fieldName with
        | none => children.admissible listSize
        | some schemaDefinition =>
            responseValueChildMultiplicity value
              ≤ max 1 (listMultiplier listSize schemaDefinition.outputType)
            ∧ children.admissible listSize
  }

abbrev concreteAlgebra (schema : Schema) : ConcreteAlgebra :=
  {
    Summary := ResponseObservation
    empty := .empty
    combine := ResponseObservation.combine
    field := responseFieldObservation schema
  }

def foldAnnotatedResponse (schema : Schema) (response : AnnotatedResponse)
    : ResponseObservation :=
  TreeSummary.foldAnnotatedResponse (concreteAlgebra schema) response

def annotatedSize (schema : Schema) (response : AnnotatedResponse) : Nat :=
  (foldAnnotatedResponse schema response).size

-- Every response field encountered by the operation stays within the multiplicity used
-- by the static field rule, and every recursively observed child is likewise admissible.
def ResponseWithinListSize (schema : Schema) (listSize : Nat)
    (response : AnnotatedResponse)
    : Prop :=
  (foldAnnotatedResponse schema response).admissible listSize

def ResponseObservationBound
    (listSize : Nat) (concrete : ResponseObservation) (abstract : Nat)
    : Prop :=
  concrete.admissible listSize -> concrete.size ≤ abstract

theorem empty_bound (listSize : Nat) : ResponseObservationBound listSize .empty 0 := by
  intro _hadmissible
  exact Nat.le_refl 0

theorem combine_bound
    {listSize : Nat}
    {concreteLeft concreteRight : ResponseObservation}
    {abstractLeft abstractRight : Nat}
    (hleft : ResponseObservationBound listSize concreteLeft abstractLeft)
    (hright : ResponseObservationBound listSize concreteRight abstractRight)
    : ResponseObservationBound listSize
        (concreteLeft.combine concreteRight) (abstractLeft + abstractRight) := by
  intro hadmissible
  exact Nat.add_le_add (hleft hadmissible.1) (hright hadmissible.2)

theorem concreteAlgebra_lawful (schema : Schema) : (concreteAlgebra schema).Lawful := by
  constructor
  · intro left middle right
    cases left
    cases middle
    cases right
    simp [concreteAlgebra, ResponseObservation.combine, Nat.add_assoc, and_assoc]
  · intro value
    cases value
    simp [concreteAlgebra, ResponseObservation.empty, ResponseObservation.combine]
  · intro value
    cases value
    simp [concreteAlgebra, ResponseObservation.empty, ResponseObservation.combine]

theorem responseValueSize_toResponseValue (schema : Schema)
    (value : AnnotatedResponseValue)
    : responseValueSize value.toResponseValue
      = (foldAnnotatedResponseValueChildren (concreteAlgebra schema) value).size := by
  apply AnnotatedResponseValue.rec
    (motive_1 := fun value =>
      responseValueSize value.toResponseValue
        = (foldAnnotatedResponseValueChildren (concreteAlgebra schema) value).size)
    (motive_2 := fun field =>
      responseValueSize field.value.toResponseValue
        = (foldAnnotatedResponseValueChildren
            (concreteAlgebra schema) field.value).size)
    (motive_3 := fun fields =>
      responseObjectFieldsSize (annotatedResponseFieldsToResponseFields fields)
        = (foldAnnotatedResponseFields (concreteAlgebra schema) fields).size)
    (motive_4 := fun values =>
      responseValuesSize (annotatedResponseValuesToResponseValues values)
        = (foldAnnotatedResponseValues (concreteAlgebra schema) values).size)
    (t := value)
  all_goals
    simp_all [AnnotatedResponseValue.toResponseValue,
      annotatedResponseFieldsToResponseFields, annotatedResponseValuesToResponseValues,
      responseValueSize, responseObjectFieldsSize, responseValuesSize,
      foldAnnotatedResponseValueChildren, foldAnnotatedResponseFields,
      foldAnnotatedResponseValues, concreteAlgebra,
      ResponseObservation.combine, ResponseObservation.empty,
      AnnotatedResponseField.value]
  intro head _tail _hhead _htail
  cases head
  simp only [annotatedResponseFieldsToResponseFields, responseObjectFieldsSize,
    foldAnnotatedResponseFields, ResponseObservation.combine,
    responseFieldObservation]
  rw [_hhead, _htail]

-- Erasing resolver-call annotations preserves the structural response-size measure.
theorem actualSize_toResponse_eq_annotatedSize
    (schema : Schema) (response : AnnotatedResponse)
    : actualSize response.toResponse = annotatedSize schema response := by
  exact responseValueSize_toResponseValue schema response.data

private def annotatedFieldsResultAdmissible (schema : Schema) (listSize : Nat)
    : Result (List AnnotatedResponseField) -> Prop
  | .error _errors => True
  | .ok (fields, _errors) =>
      (foldAnnotatedResponseFields (concreteAlgebra schema) fields).admissible listSize

private def annotatedValueResultAdmissible (schema : Schema) (listSize : Nat)
    (fieldType : TypeRef)
    : Result AnnotatedResponseValue -> Prop
  | .error _errors => True
  | .ok (value, _errors) =>
      responseValueChildMultiplicity value ≤ max 1 (listMultiplier listSize fieldType)
      ∧ (foldAnnotatedResponseValueChildren (concreteAlgebra schema) value).admissible
          listSize

private def annotatedValuesResultAdmissible (schema : Schema) (listSize length : Nat)
    (itemType : TypeRef)
    : Result (List AnnotatedResponseValue) -> Prop
  | .error _errors => True
  | .ok (values, _errors) =>
      responseValuesChildMultiplicity values
        ≤ length * max 1 (listMultiplier listSize itemType)
      ∧ (foldAnnotatedResponseValues (concreteAlgebra schema) values).admissible listSize

private theorem foldAnnotatedResponseFields_append_admissible
    (schema : Schema) (listSize : Nat)
    (left right : List AnnotatedResponseField)
    : (foldAnnotatedResponseFields (concreteAlgebra schema) (left ++ right)).admissible
        listSize
      ↔ (foldAnnotatedResponseFields (concreteAlgebra schema) left).admissible listSize
        ∧ (foldAnnotatedResponseFields (concreteAlgebra schema) right).admissible
            listSize := by
  induction left with
  | nil =>
      simp [foldAnnotatedResponseFields, concreteAlgebra, ResponseObservation.empty]
  | cons field rest ih =>
      cases field
      simp only [List.cons_append, foldAnnotatedResponseFields,
        ResponseObservation.combine]
      simp [ih, and_assoc]

private theorem one_le_listMultiplier_of_pos (listSize : Nat) (outputType : TypeRef)
    (hpositive : 0 < listSize)
    : 1 ≤ listMultiplier listSize outputType := by
  induction outputType with
  | named => simp [listMultiplier]
  | list inner ih =>
      simp only [listMultiplier]
      have hmul : 0 < listSize * listMultiplier listSize inner :=
        Nat.mul_pos hpositive (by omega)
      omega
  | nonNull inner ih => simpa [listMultiplier] using ih

private theorem length_mul_max_one_listMultiplier_le
    (listSize length : Nat) (outputType : TypeRef) (hlength : length ≤ listSize)
    : length * max 1 (listMultiplier listSize outputType)
      ≤ max 1 (listSize * listMultiplier listSize outputType) := by
  cases length with
  | zero => simp
  | succ length =>
      have hpositive : 0 < listSize := Nat.lt_of_lt_of_le (by omega) hlength
      have hmultiplier := one_le_listMultiplier_of_pos listSize outputType hpositive
      rw [Nat.max_eq_right hmultiplier]
      have hproduct : 1 ≤ listSize * listMultiplier listSize outputType := by
        have := Nat.mul_pos hpositive (by omega : 0 < listMultiplier listSize outputType)
        omega
      rw [Nat.max_eq_right hproduct]
      exact Nat.mul_le_mul_right (listMultiplier listSize outputType) hlength

private theorem annotatedExecution_admissible
    (schema : Schema) (listSize : Nat) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (hresolvers : ResolversRespectListSize listSize resolvers)
    : (∀ fuel source groups,
        annotatedFieldsResultAdmissible schema listSize
          (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
            source groups))
      ∧ (∀ fuel source responseName fields,
          annotatedFieldsResultAdmissible schema listSize
            (executeQueryAnnotatedField schema resolvers variableValues fuel source
              responseName fields))
      ∧ (∀ fuel fieldType fields value,
          resolverValueListsBounded listSize value
          -> annotatedValueResultAdmissible schema listSize fieldType
              (completeAnnotatedResponseValue schema resolvers variableValues fuel
                fieldType fields value))
      ∧ (∀ fuel itemType fields values,
          resolverValuesListsBounded listSize values
          -> annotatedValuesResultAdmissible schema listSize values.length itemType
              (completeAnnotatedResponseValueList schema resolvers variableValues fuel
                itemType fields values)) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  case case1 =>
    simp [executeQueryAnnotatedCollectedFields, annotatedFieldsResultAdmissible,
      foldAnnotatedResponseFields, ResponseObservation.empty]
  case case2 =>
    intro fuel source responseName fields rest field_ih rest_ih
    cases hfield : executeQueryAnnotatedField schema resolvers variableValues fuel source
        responseName fields with
    | error fieldErrors =>
        cases hrest : executeQueryAnnotatedCollectedFields schema resolvers variableValues
            fuel source rest <;>
          simp_all [executeQueryAnnotatedCollectedFields, annotatedFieldsResultAdmissible,
            Result.combine]
    | ok fieldResult =>
        rcases fieldResult with ⟨fieldValues, fieldErrors⟩
        cases hrest : executeQueryAnnotatedCollectedFields schema resolvers variableValues
            fuel source rest with
        | error restErrors =>
            simp_all [executeQueryAnnotatedCollectedFields,
              annotatedFieldsResultAdmissible, Result.combine]
        | ok restResult =>
            rcases restResult with ⟨restValues, restErrors⟩
            simp_all [executeQueryAnnotatedCollectedFields,
              annotatedFieldsResultAdmissible, Result.combine,
              foldAnnotatedResponseFields_append_admissible]
  case case3 =>
    simp [executeQueryAnnotatedField, annotatedFieldsResultAdmissible]
  case case4 =>
    simp [executeQueryAnnotatedField, annotatedFieldsResultAdmissible]
  case case5 =>
    intro source responseName field rest fuel hlookup
    simp [executeQueryAnnotatedField, hlookup, annotatedFieldsResultAdmissible]
  case case6 =>
    intro source responseName field rest fuel definition hlookup hcoerce
    cases htype : definition.outputType <;>
      simp [executeQueryAnnotatedField, hlookup, hcoerce, htype,
        singleAnnotatedResponseFieldResult, resolvedFieldProvenance,
        annotatedFieldsResultAdmissible,
        foldAnnotatedResponseFields, responseFieldObservation,
        ResponseObservation.combine, ResponseObservation.empty,
        foldAnnotatedResponseValueChildren, responseValueChildMultiplicity]
  case case7 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      hresolve
    cases htype : definition.outputType <;>
      simp [executeQueryAnnotatedField, hlookup, hcoerce, hresolve, htype,
        singleAnnotatedResponseFieldResult, resolvedFieldProvenance,
        annotatedFieldsResultAdmissible,
        foldAnnotatedResponseFields, responseFieldObservation,
        ResponseObservation.combine, ResponseObservation.empty,
        foldAnnotatedResponseValueChildren, responseValueChildMultiplicity]
  case case8 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      resolved hresolve complete_ih
    have hcomplete := complete_ih (hresolvers _ _ _ _ _ hresolve)
    cases hcompleted : completeAnnotatedResponseValue schema resolvers variableValues fuel
        definition.outputType (field :: rest) resolved with
    | error errors =>
        simp_all [executeQueryAnnotatedField,
          singleAnnotatedResponseFieldResult, annotatedFieldsResultAdmissible]
    | ok completed =>
        rcases completed with ⟨value, errors⟩
        simp_all [executeQueryAnnotatedField,
          singleAnnotatedResponseFieldResult, resolvedFieldProvenance,
          annotatedFieldsResultAdmissible,
          foldAnnotatedResponseFields, concreteAlgebra, responseFieldObservation,
          ResponseObservation.combine, ResponseObservation.empty]
        exact hcomplete
  case case9 =>
    simp [completeAnnotatedResponseValue, annotatedValueResultAdmissible]
  case case10 =>
    intro fuel inner fields value hfuel complete_ih hsafe
    have hcomplete := complete_ih hsafe
    cases hcompleted : completeAnnotatedResponseValue schema resolvers variableValues fuel
        inner fields value with
    | error errors =>
        simp_all [completeAnnotatedResponseValue,
          completeNonNullAnnotatedResponseValue, annotatedValueResultAdmissible]
    | ok completed =>
        rcases completed with ⟨outcome, errors⟩
        cases outcome <;>
          simp_all [completeAnnotatedResponseValue,
            completeNonNullAnnotatedResponseValue, annotatedValueResultAdmissible,
            listMultiplier]
  case case11 =>
    intro fuel fieldType fields hnotNonNull _hsafe
    simp [completeAnnotatedResponseValue,
      annotatedValueResultAdmissible, responseValueChildMultiplicity,
      foldAnnotatedResponseValueChildren, ResponseObservation.empty]
  case case12 =>
    intro fuel typeName fields value hcomposite _hsafe
    simp [completeAnnotatedResponseValue, hcomposite, annotatedValueResultAdmissible]
  case case13 =>
    intro fuel typeName fields value hnotComposite _hsafe
    have hcomposite : (TypeRef.named typeName).isCompositeBool schema = false := by
      cases hvalue : (TypeRef.named typeName).isCompositeBool schema with
      | false => rfl
      | true => exact False.elim (hnotComposite hvalue)
    simp [completeAnnotatedResponseValue, hcomposite, annotatedValueResultAdmissible,
      responseValueChildMultiplicity, foldAnnotatedResponseValueChildren,
      ResponseObservation.empty, listMultiplier]
  case case14 =>
    intro fuel parentType fields runtimeType ref hinclude childGroups child_ih _hsafe
    cases hcompleted : executeQueryAnnotatedCollectedFields schema resolvers variableValues
        fuel (.object runtimeType ref) childGroups with
    | error errors =>
        have hcompleted' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                (.object runtimeType ref)
                (collectFields schema variableValues runtimeType
                  (.object runtimeType ref) (mergedFieldSelectionSet fields))
              = .error errors := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hcompleted
        simp_all [completeAnnotatedResponseValue,
          catchAnnotatedResponseBubbleAsNull, annotatedValueResultAdmissible,
          responseValueChildMultiplicity, foldAnnotatedResponseValueChildren,
          ResponseObservation.empty, listMultiplier]
    | ok completed =>
        rcases completed with ⟨childFields, errors⟩
        have hcompleted' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                (.object runtimeType ref)
                (collectFields schema variableValues runtimeType
                  (.object runtimeType ref) (mergedFieldSelectionSet fields))
              = .ok (childFields, errors) := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hcompleted
        simp_all [completeAnnotatedResponseValue,
          catchAnnotatedResponseBubbleAsNull, annotatedValueResultAdmissible,
          responseValueChildMultiplicity, foldAnnotatedResponseValueChildren,
          listMultiplier]
        simpa [annotatedFieldsResultAdmissible] using child_ih
  case case15 =>
    intro fuel parentType fields runtimeType ref hnotInclude _hsafe
    have hinclude : schema.typeIncludesObjectBool parentType runtimeType = false := by
      cases hvalue : schema.typeIncludesObjectBool parentType runtimeType with
      | false => rfl
      | true => exact False.elim (hnotInclude hvalue)
    simp [completeAnnotatedResponseValue, hinclude, annotatedValueResultAdmissible]
  case case16 =>
    intro fuel inner fields values list_ih hsafe
    have hlist := list_ih hsafe.2
    cases hcompleted : completeAnnotatedResponseValueList schema resolvers variableValues
        fuel inner fields values with
    | error errors =>
        simp_all [completeAnnotatedResponseValue, catchAnnotatedResponseBubbleAsNull,
          annotatedValueResultAdmissible, responseValueChildMultiplicity,
          foldAnnotatedResponseValueChildren,
          ResponseObservation.empty, listMultiplier]
    | ok completed =>
        rcases completed with ⟨completedValues, errors⟩
        simp_all [completeAnnotatedResponseValue, catchAnnotatedResponseBubbleAsNull,
          annotatedValueResultAdmissible, responseValueChildMultiplicity,
          foldAnnotatedResponseValueChildren, listMultiplier]
        exact ⟨Nat.le_trans hlist.1
          (length_mul_max_one_listMultiplier_le listSize values.length inner hsafe.1),
          hlist.2⟩
  case case17 =>
    simp [completeAnnotatedResponseValue, annotatedValueResultAdmissible]
  case case18 =>
    intro fuel inner fields value hnotNull hnotList _hsafe
    simp [completeAnnotatedResponseValue, annotatedValueResultAdmissible]
  case case19 =>
    simp [completeAnnotatedResponseValueList, annotatedValuesResultAdmissible,
      responseValuesChildMultiplicity, foldAnnotatedResponseValues,
      ResponseObservation.empty]
  case case20 =>
    intro fuel itemType fields value values head_ih tail_ih hsafe
    have hhead := head_ih hsafe.1
    have htail := tail_ih hsafe.2
    cases hcompletedHead : completeAnnotatedResponseValue schema resolvers variableValues
        fuel itemType fields value with
    | error headErrors =>
        cases hcompletedTail : completeAnnotatedResponseValueList schema resolvers
            variableValues fuel itemType fields values <;>
          simp_all [completeAnnotatedResponseValueList, Result.combine,
            annotatedValuesResultAdmissible]
    | ok completedHead =>
        rcases completedHead with ⟨headValue, headErrors⟩
        cases hcompletedTail : completeAnnotatedResponseValueList schema resolvers
            variableValues fuel itemType fields values with
        | error tailErrors =>
            simp_all [completeAnnotatedResponseValueList, Result.combine,
              annotatedValuesResultAdmissible]
        | ok completedTail =>
            rcases completedTail with ⟨tailValues, tailErrors⟩
            simp_all [completeAnnotatedResponseValueList, Result.combine,
              annotatedValuesResultAdmissible, responseValuesChildMultiplicity,
              foldAnnotatedResponseValues, concreteAlgebra,
              ResponseObservation.combine, Nat.add_mul]
            constructor
            · simpa [Nat.add_comm] using Nat.add_le_add hhead.1 htail.1
            · exact hhead.2

def algebraLawful (schema : Schema) (listSize : Nat) : (algebra schema listSize).Lawful :=
  {
    le := Nat.le
    le_refl := Nat.le_refl
    le_trans := fun _ _ _ => Nat.le_trans
    combine_assoc := Nat.add_assoc
    combine_comm := Nat.add_comm
    empty_combine := Nat.zero_add
    combine_empty := Nat.add_zero
    empty_le := Nat.zero_le
    combine_mono := fun _ _ _ _ => Nat.add_le_add
    le_join_left := Nat.le_max_left
    le_join_right := Nat.le_max_right
  }

private theorem foldlListMultiplier_ge_accumulator (listSize : Nat)
    (outputTypes : List TypeRef) (accumulator : Nat)
    : accumulator
      ≤ outputTypes.foldl
          (fun maximum outputType =>
            max maximum (listMultiplier listSize outputType))
          accumulator := by
  induction outputTypes generalizing accumulator with
  | nil => exact Nat.le_refl _
  | cons outputType rest ih =>
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem listMultiplier_le_foldl_of_mem (listSize : Nat)
    (outputType : TypeRef) (outputTypes : List TypeRef) (accumulator : Nat)
    (hmem : outputType ∈ outputTypes)
    : listMultiplier listSize outputType
      ≤ outputTypes.foldl
          (fun maximum candidate =>
            max maximum (listMultiplier listSize candidate))
          accumulator := by
  induction outputTypes generalizing accumulator with
  | nil => simp at hmem
  | cons candidate rest ih =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
          subst candidate
          exact Nat.le_trans (Nat.le_max_right _ _)
            (foldlListMultiplier_ge_accumulator listSize rest _)
      | inr hrest => exact ih _ hrest

theorem listMultiplier_le_fieldListMultiplier (schema : Schema) (listSize : Nat)
    (group : CollectedFieldGroup) (outputType : TypeRef)
    (hmem : outputType ∈ group.fieldOutputTypes schema)
    : listMultiplier listSize outputType ≤ fieldListMultiplier schema listSize group := by
  exact listMultiplier_le_foldl_of_mem listSize outputType
    (group.fieldOutputTypes schema) 1 hmem

theorem one_le_fieldListMultiplier (schema : Schema) (listSize : Nat)
    (group : CollectedFieldGroup)
    : 1 ≤ fieldListMultiplier schema listSize group := by
  exact foldlListMultiplier_ge_accumulator listSize (group.fieldOutputTypes schema) 1

theorem max_one_listMultiplier_le_fieldListMultiplier
    (schema : Schema) (listSize : Nat) (group : CollectedFieldGroup)
    (outputType : TypeRef) (hmem : outputType ∈ group.fieldOutputTypes schema)
    : max 1 (listMultiplier listSize outputType)
      ≤ fieldListMultiplier schema listSize group := by
  exact Nat.max_le.mpr ⟨one_le_fieldListMultiplier schema listSize group,
    (listMultiplier_le_fieldListMultiplier schema listSize group outputType hmem)
  ⟩

mutual
  private theorem foldChildSummaryForValue_le_mul
      (schema : Schema) (listSize childSummary : Nat)
      (value : AnnotatedResponseValue)
      : foldChildSummaryForValue (algebra schema listSize) childSummary value
        ≤ responseValueChildMultiplicity value * childSummary := by
    cases value with
    | null => simp [foldChildSummaryForValue, responseValueChildMultiplicity, algebra]
    | scalar value =>
        simp [foldChildSummaryForValue, responseValueChildMultiplicity, algebra]
    | object runtimeType fields =>
        simp [foldChildSummaryForValue, responseValueChildMultiplicity]
    | list values =>
        exact foldChildSummaryForValues_le_mul schema listSize childSummary values

  private theorem foldChildSummaryForValues_le_mul
      (schema : Schema) (listSize childSummary : Nat)
      (values : List AnnotatedResponseValue)
      : foldChildSummaryForValues (algebra schema listSize) childSummary values
        ≤ responseValuesChildMultiplicity values * childSummary := by
    cases values with
    | nil => simp [foldChildSummaryForValues, responseValuesChildMultiplicity, algebra]
    | cons value rest =>
        exact Nat.le_trans
          (Nat.add_le_add
            (foldChildSummaryForValue_le_mul schema listSize childSummary value)
            (foldChildSummaryForValues_le_mul schema listSize childSummary rest))
          (by simp [responseValuesChildMultiplicity, Nat.add_mul])
end

namespace ExactCases

private theorem natBestBound_attains {outcomes : OutcomeSet Nat} {estimate : Nat}
    (hbest : BestBound Nat.le Nat.le outcomes estimate)
    : outcomes estimate := by
  by_cases hattained : outcomes estimate
  · exact hattained
  · cases estimate with
    | zero =>
        rcases hbest.feasible with ⟨outcome, houtcome⟩
        have hle := hbest.sound outcome houtcome
        have : outcome = 0 := Nat.eq_zero_of_le_zero hle
        exact False.elim (hattained (this ▸ houtcome))
    | succ predecessor =>
        have hupper : ∀ outcome, outcomes outcome -> outcome ≤ predecessor := by
          intro outcome houtcome
          have hle : outcome ≤ Nat.succ predecessor := hbest.sound outcome houtcome
          have hne : outcome ≠ Nat.succ predecessor := by
            intro heq
            subst outcome
            exact hattained houtcome
          exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hle hne)
        have hleast : Nat.succ predecessor ≤ predecessor :=
          hbest.least predecessor hupper
        exact False.elim (Nat.not_succ_le_self predecessor hleast)

-- The response-size transfer algebra computes feasible least bounds of its local
-- multiplicity semantics. Positivity of `listSize` is only needed when interpreting
-- the model as actual list cardinalities; the algebraic result is valid for every Nat.
private def bestTransferLaws (schema : Schema) (listSize : Nat)
    : TreeSummary.ExactCases.BestTransferLaws (caseSemantics schema listSize)
        (algebra schema listSize) :=
  {
    related := Nat.le
    le := Nat.le
    empty_best := by
      refine ⟨⟨0, rfl⟩, ?_, ?_⟩
      · intro concrete hconcrete
        simpa [OutcomeSet.singleton] using hconcrete
      · intro candidate hcandidate
        exact hcandidate 0 rfl
    combine_best := by
      intro left right abstractLeft abstractRight hleft hright
      refine ⟨?_, ?_, ?_⟩
      · rcases hleft.feasible with ⟨leftValue, hleftValue⟩
        rcases hright.feasible with ⟨rightValue, hrightValue⟩
        exact ⟨leftValue + rightValue,
          ⟨leftValue, rightValue, hleftValue, hrightValue, rfl⟩⟩
      · intro concrete hconcrete
        rcases hconcrete with
          ⟨leftValue, rightValue, hleftValue, hrightValue, rfl⟩
        exact Nat.add_le_add
          (hleft.sound leftValue hleftValue)
          (hright.sound rightValue hrightValue)
      · intro candidate hcandidate
        have hleftAttained := natBestBound_attains hleft
        have hrightAttained := natBestBound_attains hright
        exact hcandidate (abstractLeft + abstractRight)
          ⟨abstractLeft, abstractRight, hleftAttained, hrightAttained, rfl⟩
    field_best := by
      intro group children abstractChildren hchildren
      refine ⟨?_, ?_, ?_⟩
      · rcases hchildren.feasible with ⟨child, hchild⟩
        exact ⟨1, ⟨child, hchild, 0, Nat.zero_le _, by simp⟩⟩
      · intro concrete hconcrete
        rcases hconcrete with ⟨child, hchild, multiplicity, hmultiplicity, rfl⟩
        exact Nat.le_trans
          (Nat.add_le_add_left
            (Nat.mul_le_mul_left multiplicity (hchildren.sound child hchild)) 1)
          (Nat.add_le_add_left
            (Nat.mul_le_mul_right abstractChildren hmultiplicity) 1)
      · intro candidate hcandidate
        have hattained := natBestBound_attains hchildren
        exact hcandidate
          (1 + fieldListMultiplier schema listSize group * abstractChildren)
          ⟨abstractChildren, hattained,
            fieldListMultiplier schema listSize group, Nat.le_refl _, rfl⟩
    join_best := by
      intro left right abstractLeft abstractRight hleft hright
      refine ⟨?_, ?_, ?_⟩
      · rcases hleft.feasible with ⟨concrete, hconcrete⟩
        exact ⟨concrete, Or.inl hconcrete⟩
      · intro concrete hconcrete
        cases hconcrete with
        | inl hleftConcrete =>
            exact Nat.le_trans (hleft.sound concrete hleftConcrete)
              (Nat.le_max_left _ _)
        | inr hrightConcrete =>
            exact Nat.le_trans (hright.sound concrete hrightConcrete)
              (Nat.le_max_right _ _)
      · intro candidate hcandidate
        exact Nat.max_le.mpr
          ⟨hleft.least candidate fun concrete hconcrete =>
              hcandidate concrete (Or.inl hconcrete),
            hright.least candidate fun concrete hconcrete =>
              hcandidate concrete (Or.inr hconcrete)⟩
  }

-- Public witness: the exact response-size summary is the least bound of the local
-- multiplicity semantics, recursively through every child selection set.
theorem summaryOptimal (schema : Schema) (listSize : Nat) (operation : Operation)
    : SummaryOptimal schema listSize operation := by
  simpa [SummaryOptimal, estimateOperation, bestTransferLaws] using
    TreeSummary.ExactCases.summarizeOperation_best
      (bestTransferLaws schema listSize) operation

-- Public witness for the variable-aware response-size optimality statement.
theorem summaryOptimalWithVariables (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues) (operation : Operation)
    : SummaryOptimalWithVariables schema listSize variableValues operation := by
  simpa [SummaryOptimalWithVariables, estimateOperationWithVariables,
    bestTransferLaws] using
    TreeSummary.ExactCases.summarizeOperationWithVariables_best
      (fun _values => algebra schema listSize) variableValues operation
      (bestTransferLaws schema listSize)

def compatible (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues)
    : TreeSummary.ExactCases.Compatible (concreteAlgebra schema)
        (algebra schema listSize) schema variableValues :=
  {
    related := ResponseObservationBound listSize
    concreteLawful := concreteAlgebra_lawful schema
    abstractLawful := algebraLawful schema listSize
    empty_related := empty_bound listSize
    combine_related := by
      intro concreteLeft abstractLeft concreteRight abstractRight hleft hright
      exact combine_bound hleft hright
    related_mono := by
      intro concreteValue abstractLower abstractUpper hlower hle hadmissible
      exact Nat.le_trans (hlower hadmissible) hle
    field_related := by
      intro group _field schemaDefinition value children abstractChildren _hparent
        _hrepresents hlookup houtput hchildren
      intro hadmissible
      have hadmissible' :
          responseValueChildMultiplicity value
                ≤ max 1 (listMultiplier listSize schemaDefinition.outputType)
            ∧ children.admissible listSize := by
        simpa [concreteAlgebra, responseFieldObservation, resolvedFieldProvenance,
          hlookup] using hadmissible
      have hchild := Nat.le_trans (hchildren hadmissible'.2)
        (foldChildSummaryForValue_le_mul schema listSize abstractChildren value)
      have hmultiplier := Nat.le_trans hadmissible'.1
        (max_one_listMultiplier_le_fieldListMultiplier schema listSize group
          schemaDefinition.outputType houtput)
      exact Nat.add_le_add_left
        (Nat.le_trans hchild
          (Nat.mul_le_mul_right abstractChildren hmultiplier)) 1
  }

end ExactCases

private theorem summarizedGroups_capacity
    (schema : Schema) (listSize instanceCount : Nat)
    (abstractChildren : CollectedFieldGroup -> Nat)
    (groups : List CollectedFieldGroup)
    (hmultiplier
      : ∀ group,
          group ∈ groups -> instanceCount ≤ fieldListMultiplier schema listSize group)
    : groups.length
        + instanceCount
          * foldChildSummaries (algebra schema listSize) abstractChildren groups
      ≤ foldFieldGroups (algebra schema listSize) abstractChildren groups := by
  induction groups with
  | nil => simp [foldChildSummaries, foldFieldGroups, algebra]
  | cons group rest ih =>
      have hgroup := hmultiplier group (by simp)
      have hrest := ih (by
        intro candidate hcandidate
        exact hmultiplier candidate (by simp [hcandidate]))
      simp only [List.length_cons, foldChildSummaries, foldFieldGroups]
      change rest.length + 1
          + instanceCount
          * (abstractChildren group
              + foldChildSummaries (algebra schema listSize) abstractChildren rest)
        ≤ (1 + fieldListMultiplier schema listSize group
              * abstractChildren group)
            + foldFieldGroups (algebra schema listSize) abstractChildren rest
      rw [Nat.mul_add]
      have hchild := Nat.mul_le_mul_right
        (abstractChildren group)
        hgroup
      have hcombined := Nat.add_le_add (Nat.add_le_add_left hchild 1) hrest
      omega

namespace Syntactic

def compatible (schema : Schema) (listSize : Nat)
    (variableValues : Execution.VariableValues)
    : TreeSummary.Syntactic.Compatible (concreteAlgebra schema)
        (algebra schema listSize) schema variableValues :=
  {
    related := ResponseObservationBound listSize
    concreteLawful := concreteAlgebra_lawful schema
    abstractLawful := algebraLawful schema listSize
    empty_related := empty_bound listSize
    combine_related := by
      intro concreteLeft abstractLeft concreteRight abstractRight hleft hright
      exact combine_bound hleft hright
    related_mono := by
      intro concreteValue abstractLower abstractUpper hlower hle hadmissible
      exact Nat.le_trans (hlower hadmissible) hle
    field_related := by
      intro ObjectRef runtimeType ref responseName field rest definition value children
        groups abstractChildren hparent hlookup _harguments hnonempty _hinherited
        hconditions _hcover hmatch hchildren
      intro hadmissible
      have hadmissible' :
          responseValueChildMultiplicity value
                ≤ max 1 (listMultiplier listSize definition.outputType)
            ∧ children.admissible listSize := by
        simpa [concreteAlgebra, responseFieldObservation, resolvedFieldProvenance,
          hlookup] using hadmissible
      have hchild := Nat.le_trans (hchildren hadmissible'.2)
        (foldChildSummaryForValue_le_mul schema listSize
          (foldChildSummaries (algebra schema listSize) abstractChildren groups) value)
      have hmultipliers : ∀ group,
          group ∈ groups
          -> responseValueChildMultiplicity value
            ≤ fieldListMultiplier schema listSize group := by
        intro group hgroup
        have hlookupRuntime :
            schema.lookupField runtimeType field.fieldName = some definition := by
          simpa [hparent] using hlookup
        have hfieldName : field.fieldName ∈ group.fieldNames :=
          fieldName_mem_of_groupsRepresentField schema variableValues runtimeType ref
            groups field hmatch group hgroup
        have houtput :=
          lookupField_outputType_mem_fieldOutputTypes_of_condition_allows schema
            variableValues runtimeType group field.fieldName definition
            (hconditions group hgroup) hfieldName hlookupRuntime
        exact Nat.le_trans hadmissible'.1
          (max_one_listMultiplier_le_fieldListMultiplier schema listSize group
            definition.outputType houtput)
      have hcapacity := summarizedGroups_capacity schema listSize
        (responseValueChildMultiplicity value) abstractChildren groups hmultipliers
      have hlength : 1 ≤ groups.length := by
        exact List.length_pos_iff.mpr hnonempty
      have hbeforeCapacity :
          1 + children.size
            ≤ groups.length
              + responseValueChildMultiplicity value
                  * foldChildSummaries (algebra schema listSize) abstractChildren
                    groups :=
        by
          exact Nat.add_le_add hlength hchild
      exact Nat.le_trans hbeforeCapacity hcapacity
  }

end Syntactic

-- The resolver-level list bound is stronger than the concrete algebra's admissibility
-- predicate on the particular annotated response produced by execution.
theorem executeQueryAnnotatedWithFuel_responseWithinListSize
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (hresolvers : ResolversRespectListSize listSize resolvers)
    : ResponseWithinListSize schema listSize
        (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source) := by
  let coercedVariableValues := coerceVariableValues operation variableValues
  let groups :=
    collectFields schema coercedVariableValues (operation.rootType schema) source
      operation.selectionSet
  have hfields :=
    (annotatedExecution_admissible schema listSize resolvers coercedVariableValues
      hresolvers).1 fuel source groups
  cases hroot : rootSourceAppliesBool schema operation source with
  | false =>
      simp [ResponseWithinListSize, MaxResponseSize.foldAnnotatedResponse,
        TreeSummary.foldAnnotatedResponse, executeQueryAnnotatedWithFuel, hroot,
        foldAnnotatedResponseValueChildren, concreteAlgebra, ResponseObservation.empty]
  | true =>
      cases hresult
            : executeQueryAnnotatedCollectedFields schema resolvers
                coercedVariableValues fuel source groups with
      | error errors =>
          simp [ResponseWithinListSize, MaxResponseSize.foldAnnotatedResponse,
            TreeSummary.foldAnnotatedResponse, executeQueryAnnotatedWithFuel, hroot,
            coercedVariableValues, groups, hresult, foldAnnotatedResponseValueChildren,
            concreteAlgebra, ResponseObservation.empty]
      | ok completed =>
          rcases completed with ⟨fields, errors⟩
          rw [hresult] at hfields
          simpa [ResponseWithinListSize, MaxResponseSize.foldAnnotatedResponse,
            TreeSummary.foldAnnotatedResponse, executeQueryAnnotatedWithFuel, hroot,
            coercedVariableValues, groups, hresult, annotatedFieldsResultAdmissible,
            foldAnnotatedResponseValueChildren] using hfields

theorem executeQueryAnnotated_responseWithinListSize
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (hresolvers : ResolversRespectListSize listSize resolvers)
    : ResponseWithinListSize schema listSize
        (executeQueryAnnotated schema resolvers variableValues operation source) := by
  exact executeQueryAnnotatedWithFuel_responseWithinListSize schema listSize operation
    resolvers variableValues (executeQueryFuelBound schema operation) source hresolvers

namespace ExactCases

theorem algebraSoundWithFuel (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
    : annotatedSize schema
        (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source)
      ≤ estimateOperation schema listSize operation := by
  have hrefinement :=
    TreeSummary.ExactCases.Compatible.executeQueryAnnotatedWithFuel_related operation
      resolvers variableValues
      (compatible schema listSize
        (Execution.coerceVariableValues operation variableValues))
      fuel source hschema hoperation
  simpa [ResponseWithinListSize, annotatedSize,
    MaxResponseSize.foldAnnotatedResponse, estimateOperation,
    MaxResponseSize.ExactCases.estimateOperation] using
    hrefinement hadmissible

theorem algebraSound (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotated schema resolvers variableValues operation source))
    : annotatedSize schema
        (executeQueryAnnotated schema resolvers variableValues operation source)
      ≤ estimateOperation schema listSize operation := by
  exact algebraSoundWithFuel schema listSize operation hschema hoperation ObjectRef resolvers
    variableValues (Execution.executeQueryFuelBound schema operation) source hadmissible

theorem soundWithFuel (schema : Schema) (listSize : Nat) (operation : Operation)
    : SoundWithFuel schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source hresolvers
  have hbound := algebraSoundWithFuel schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues fuel source
    (executeQueryAnnotatedWithFuel_responseWithinListSize schema listSize operation
      resolvers variableValues fuel source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotatedWithFuel_toResponse] using hbound

theorem sound (schema : Schema) (listSize : Nat) (operation : Operation)
    : Sound schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source hresolvers
  have hbound := algebraSound schema listSize operation hschema hoperation ObjectRef
    resolvers variableValues source
    (executeQueryAnnotated_responseWithinListSize schema listSize operation resolvers
      variableValues source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotated_toResponse] using hbound

theorem algebraWithVariablesSoundWithFuel
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
    : annotatedSize schema
        (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source)
      ≤ estimateOperationWithVariables schema listSize variableValues operation := by
  have hrefinement :=
    TreeSummary.ExactCases.operationWithVariablesSoundWithFuel
      (fun _values => algebra schema listSize)
      (fun values => compatible schema listSize values) operation hschema hoperation
      ObjectRef resolvers variableValues fuel source
  simpa [ResponseWithinListSize, annotatedSize,
    MaxResponseSize.foldAnnotatedResponse, estimateOperationWithVariables] using
    hrefinement hadmissible

theorem algebraWithVariablesSound
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotated schema resolvers variableValues operation source))
    : annotatedSize schema
        (executeQueryAnnotated schema resolvers variableValues operation source)
      ≤ estimateOperationWithVariables schema listSize variableValues operation := by
  exact algebraWithVariablesSoundWithFuel schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues (Execution.executeQueryFuelBound schema operation)
    source hadmissible

theorem soundWithVariablesWithFuel
    (schema : Schema) (listSize : Nat) (operation : Operation)
    : SoundWithVariablesWithFuel schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source hresolvers
  have hbound := algebraWithVariablesSoundWithFuel schema listSize operation hschema
    hoperation ObjectRef resolvers variableValues fuel source
    (executeQueryAnnotatedWithFuel_responseWithinListSize schema listSize operation
      resolvers variableValues fuel source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotatedWithFuel_toResponse] using hbound

theorem soundWithVariables (schema : Schema) (listSize : Nat) (operation : Operation)
    : SoundWithVariables schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source hresolvers
  have hbound := algebraWithVariablesSound schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues source
    (executeQueryAnnotated_responseWithinListSize schema listSize operation resolvers
      variableValues source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotated_toResponse] using hbound

end ExactCases

namespace Syntactic

theorem algebraSoundWithFuel
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
    : annotatedSize schema
        (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source)
      ≤ estimateOperation schema listSize operation := by
  have hrefinement :=
    _root_.GraphQL.TreeSummary.Syntactic.operationSoundWithFuel
      (fun values => compatible schema listSize values)
      hschema hoperation ObjectRef resolvers variableValues fuel source
  simpa [ResponseWithinListSize, annotatedSize,
    MaxResponseSize.foldAnnotatedResponse, estimateOperation] using
    hrefinement hadmissible

theorem algebraSound
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotated schema resolvers variableValues operation source))
    : annotatedSize schema
        (executeQueryAnnotated schema resolvers variableValues operation source)
      ≤ estimateOperation schema listSize operation := by
  exact algebraSoundWithFuel schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues (Execution.executeQueryFuelBound schema operation)
    source hadmissible

theorem soundWithFuel (schema : Schema) (listSize : Nat) (operation : Operation)
    : SoundWithFuel schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source hresolvers
  have hbound := algebraSoundWithFuel schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues fuel source
    (executeQueryAnnotatedWithFuel_responseWithinListSize schema listSize operation
      resolvers variableValues fuel source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotatedWithFuel_toResponse] using hbound

theorem sound (schema : Schema) (listSize : Nat) (operation : Operation)
    : Sound schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source hresolvers
  have hbound := algebraSound schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues source
    (executeQueryAnnotated_responseWithinListSize schema listSize operation resolvers
      variableValues source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotated_toResponse] using hbound

theorem algebraWithVariablesSoundWithFuel
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
    : annotatedSize schema
        (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
          source)
      ≤ estimateOperationWithVariables schema listSize variableValues operation := by
  have hrefinement :=
    _root_.GraphQL.TreeSummary.Syntactic.operationWithVariablesSoundWithFuel
      (concrete := concreteAlgebra schema)
      (fun _values => algebra schema listSize)
      (fun values => compatible schema listSize values) operation hschema hoperation
      ObjectRef resolvers variableValues fuel source
  simpa [ResponseWithinListSize, annotatedSize,
    MaxResponseSize.foldAnnotatedResponse, estimateOperationWithVariables] using
    hrefinement hadmissible

theorem algebraWithVariablesSound
    (schema : Schema) (listSize : Nat) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (hadmissible
      : ResponseWithinListSize schema listSize
          (executeQueryAnnotated schema resolvers variableValues operation source))
    : annotatedSize schema
        (executeQueryAnnotated schema resolvers variableValues operation source)
      ≤ estimateOperationWithVariables schema listSize variableValues operation := by
  exact algebraWithVariablesSoundWithFuel schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues (Execution.executeQueryFuelBound schema operation)
    source hadmissible

theorem soundWithVariablesWithFuel
    (schema : Schema) (listSize : Nat) (operation : Operation)
    : SoundWithVariablesWithFuel schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source hresolvers
  have hbound := algebraWithVariablesSoundWithFuel schema listSize operation hschema
    hoperation ObjectRef resolvers variableValues fuel source
    (executeQueryAnnotatedWithFuel_responseWithinListSize schema listSize operation
      resolvers variableValues fuel source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotatedWithFuel_toResponse] using hbound

theorem soundWithVariables (schema : Schema) (listSize : Nat) (operation : Operation)
    : SoundWithVariables schema listSize operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source hresolvers
  have hbound := algebraWithVariablesSound schema listSize operation hschema hoperation
    ObjectRef resolvers variableValues source
    (executeQueryAnnotated_responseWithinListSize schema listSize operation resolvers
      variableValues source hresolvers)
  rw [← actualSize_toResponse_eq_annotatedSize schema] at hbound
  simpa [executeQueryAnnotated_toResponse] using hbound

end Syntactic

end MaxResponseSize
end TreeSummary
end GraphQL
