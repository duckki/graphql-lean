import GraphQL.Algorithms.ExecutionUngroupedUncached
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Final
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Recursive
import Proofs.GraphQL.Execution.Data
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Semantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Variables
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.BoolCaseWrappers
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Semantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterReadiness
import Proofs.GraphQL.Theories.NormalForm.Shared.Execution

/-!
Bool-case execution lemmas for the ungrouped execution algorithm.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

variable {ObjectRef : Type}

theorem lookupResponseField?_eq_none_of_not_mem {responseName : Name}
    : ∀ fields : List (Name × Execution.ResponseValue),
        responseName ∉ fields.map Prod.fst
        -> lookupResponseField? responseName fields = none
  | [], _hnotMem => by
      rfl
  | (fieldResponseName, response) :: rest, hnotMem => by
      have hhead : fieldResponseName ≠ responseName := by
        intro heq
        exact hnotMem (by simp [heq])
      have htail : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotMem (by simp [hmem])
      have hfalse : (fieldResponseName == responseName) = false := by
        cases hmatch : fieldResponseName == responseName
        · rfl
        · exact False.elim (hhead (beq_iff_eq.mp hmatch))
      simp [lookupResponseField?, hfalse,
        lookupResponseField?_eq_none_of_not_mem rest htail]

theorem responseObjectField?_eq_none_of_not_mem
    {responseName : Name} {fields : List (Name × Execution.ResponseValue)}
    : responseName ∉ fields.map Prod.fst
      -> responseObjectField? responseName (Execution.ResponseValue.object fields)
          = none := by
  intro hnotMem
  exact lookupResponseField?_eq_none_of_not_mem fields hnotMem

theorem mergeResponseField_eq_append_of_not_mem
    {responseName : Name} (incoming : Execution.ResponseValue)
    : ∀ fields : List (Name × Execution.ResponseValue),
        responseName ∉ fields.map Prod.fst
        -> mergeResponseField responseName incoming fields
            = fields ++ [(responseName, incoming)]
  | [], _hnotMem => by
      simp [mergeResponseField]
  | (fieldResponseName, existing) :: rest, hnotMem => by
      have hhead : fieldResponseName ≠ responseName := by
        intro heq
        exact hnotMem (by simp [heq])
      have htail : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotMem (by simp [hmem])
      have hfalse : (fieldResponseName == responseName) = false := by
        cases hmatch : fieldResponseName == responseName
        · rfl
        · exact False.elim (hhead (beq_iff_eq.mp hmatch))
      simp [mergeResponseField, hfalse,
        mergeResponseField_eq_append_of_not_mem incoming rest htail]

theorem mergeResponseFieldIntoObject_eq_append_of_not_mem
    {responseName : Name} (incoming : Execution.ResponseValue)
    {fields : List (Name × Execution.ResponseValue)}
    : responseName ∉ fields.map Prod.fst
      -> mergeResponseFieldIntoObject responseName incoming
            (Execution.ResponseValue.object fields)
          = Execution.ResponseValue.object (fields ++ [(responseName, incoming)]) := by
  intro hnotMem
  simp [mergeResponseFieldIntoObject,
    mergeResponseField_eq_append_of_not_mem incoming fields hnotMem]

theorem foldlCompleteValues_no_previous_eq_map
    (complete
      : Execution.ResolverValue ObjectRef
        -> Execution.ResponseValue
        -> Execution.ResponseValue)
    : ∀ (values : List (Execution.ResolverValue ObjectRef))
        (acc : List Execution.ResponseValue),
        ((values.foldl
            (fun (state : List Execution.ResponseValue × List Execution.ResponseValue)
                value =>
              (
                complete value
                  (match state.snd with
                    | [] => Execution.ResponseValue.null
                    | previous :: _rest => previous)
                :: state.fst,
                match state.snd with
                | [] => []
                | _previous :: rest => rest
              ))
            (acc, [])).fst).reverse
        = acc.reverse
          ++ values.map
              (fun value =>
                complete value Execution.ResponseValue.null)
  | [], acc => by
      simp
  | value :: rest, acc => by
      simpa [List.append_assoc] using
        foldlCompleteValues_no_previous_eq_map complete rest
          (complete value Execution.ResponseValue.null :: acc)

theorem visitSubfields_append
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    : ∀ (left right : List Selection) output,
        (visitSubfields schema resolvers variableValues depth parentType source
          (left ++ right) output).fst
        = (visitSubfields schema resolvers variableValues depth parentType source
            right
            (visitSubfields schema resolvers variableValues depth parentType
              source left output).fst).fst
  | [], _right, _output => by
      simp [visitSubfields]
  | selection :: rest, right, output => by
      simpa [visitSubfields] using
        visitSubfields_append schema resolvers variableValues depth parentType
          source rest right
          (visitSelection schema resolvers variableValues depth parentType source
            selection output).fst

theorem visitSubfields_wrapWithBoolCase_empty
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    : ∀ boolCase output,
        (visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase boolCase []) output).fst
        = output
  | [], output => by
      simp [NormalForm.wrapWithBoolCase, visitSubfields]
  | (varName, value) :: rest, output => by
      by_cases hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [NormalForm.directiveForBit varName value] = true
      · simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection,
          hallow, visitSubfields_wrapWithBoolCase_empty schema resolvers
            variableValues depth parentType source rest output]
      · have hfalse :
            Execution.selectionDirectivesAllowBool variableValues
              [NormalForm.directiveForBit varName value] = false := by
          cases h :
              Execution.selectionDirectivesAllowBool variableValues
                [NormalForm.directiveForBit varName value]
          · rfl
          · exact False.elim (hallow h)
        simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection,
          hfalse]

theorem visitSubfields_wrapWithBoolCase_empty_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    : ∀ boolCase output,
        visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase boolCase []) output
        = (output, visitOk)
  | [], output => by
      simp [NormalForm.wrapWithBoolCase, visitSubfields]
  | (varName, value) :: rest, output => by
      by_cases hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [NormalForm.directiveForBit varName value] = true
      · simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection,
          hallow, visitSubfields_wrapWithBoolCase_empty_result schema
            resolvers variableValues depth parentType source rest output]
      · have hfalse :
            Execution.selectionDirectivesAllowBool variableValues
              [NormalForm.directiveForBit varName value] = false := by
          cases h :
              Execution.selectionDirectivesAllowBool variableValues
                [NormalForm.directiveForBit varName value]
          · rfl
          · exact False.elim (hallow h)
        simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection,
          hfalse]

theorem visitSubfields_wrapWithBoolCase_cons_allowed
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : Execution.selectionDirectivesAllowBool variableValues
          [NormalForm.directiveForBit varName value]
        = true
      -> (visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase ((varName, value) :: rest) selectionSet)
            output).fst
          = (visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase rest selectionSet) output).fst := by
  intro hallow
  simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection, hallow]

theorem visitSubfields_wrapWithBoolCase_cons_allowed_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : Execution.selectionDirectivesAllowBool variableValues
          [NormalForm.directiveForBit varName value]
        = true
      -> visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase ((varName, value) :: rest) selectionSet) output
          = visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase rest selectionSet) output := by
  intro hallow
  simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection, hallow]

theorem visitSubfields_wrapWithBoolCase_cons_skipped
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : Execution.selectionDirectivesAllowBool variableValues
          [NormalForm.directiveForBit varName value]
        = false
      -> (visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase ((varName, value) :: rest) selectionSet)
            output).fst
          = output := by
  intro hallow
  simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection, hallow]

theorem visitSubfields_wrapWithBoolCase_cons_skipped_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : Execution.selectionDirectivesAllowBool variableValues
          [NormalForm.directiveForBit varName value]
        = false
      -> visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase ((varName, value) :: rest) selectionSet) output
          = (output, visitOk) := by
  intro hallow
  simp [NormalForm.wrapWithBoolCase, visitSubfields, visitSelection, hallow]

theorem visitSubfields_wrapWithBoolCase_cons_mismatch
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : Execution.inputValueBoolean? variableValues (.variable varName) = some (!value)
      -> (visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase ((varName, value) :: rest) selectionSet)
            output).fst
          = output := by
  intro hmismatch
  exact visitSubfields_wrapWithBoolCase_cons_skipped schema resolvers
    variableValues depth parentType source varName value rest selectionSet
    output
    (NormalForm.CompleteNormalization.selectionDirectivesAllowBool_boolCaseBit_of_mismatch
      variableValues varName value hmismatch)

theorem visitSubfields_wrapWithBoolCase_cons_mismatch_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (varName : NormalForm.BoolVar) (value : Bool)
    (rest : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : Execution.inputValueBoolean? variableValues (.variable varName) = some (!value)
      -> visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase ((varName, value) :: rest) selectionSet) output
          = (output, visitOk) := by
  intro hmismatch
  exact visitSubfields_wrapWithBoolCase_cons_skipped_result schema resolvers
    variableValues depth parentType source varName value rest selectionSet
    output
    (NormalForm.CompleteNormalization.selectionDirectivesAllowBool_boolCaseBit_of_mismatch
      variableValues varName value hmismatch)

theorem visitSubfields_wrapWithBoolCase_of_mismatch_pair
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ boolCase (varName : NormalForm.BoolVar) (value : Bool),
        (varName, value) ∈ boolCase
        -> Execution.inputValueBoolean? variableValues (.variable varName) = some (!value)
        -> ∀ output,
            (visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase boolCase selectionSet) output).fst
            = output
  | [], _varName, _value, hpair, _hmismatch, _output => by
      cases hpair
  | (headVar, headValue) :: rest, varName, value, hpair, hmismatch,
      output => by
      simp at hpair
      rcases hpair with hhead | htail
      · have hvar : varName = headVar := hhead.1
        have hvalue : value = headValue := hhead.2
        subst varName
        subst value
        exact visitSubfields_wrapWithBoolCase_cons_mismatch schema resolvers
          variableValues depth parentType source headVar headValue rest selectionSet
          output hmismatch
      · by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues
              [NormalForm.directiveForBit headVar headValue] = true
        · rw [visitSubfields_wrapWithBoolCase_cons_allowed schema resolvers
            variableValues depth parentType source headVar headValue rest
            selectionSet output hallow]
          exact visitSubfields_wrapWithBoolCase_of_mismatch_pair schema
            resolvers variableValues depth parentType source selectionSet rest
            varName value htail hmismatch output
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues
                [NormalForm.directiveForBit headVar headValue] = false := by
            cases h :
                Execution.selectionDirectivesAllowBool variableValues
                  [NormalForm.directiveForBit headVar headValue]
            · rfl
            · exact False.elim (hallow h)
          exact visitSubfields_wrapWithBoolCase_cons_skipped schema resolvers
            variableValues depth parentType source headVar headValue rest
            selectionSet output hfalse

theorem visitSubfields_wrapWithBoolCase_of_mismatch_pair_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ boolCase (varName : NormalForm.BoolVar) (value : Bool),
        (varName, value) ∈ boolCase
        -> Execution.inputValueBoolean? variableValues (.variable varName) = some (!value)
        -> ∀ output,
            visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase boolCase selectionSet) output
            = (output, visitOk)
  | [], _varName, _value, hpair, _hmismatch, _output => by
      cases hpair
  | (headVar, headValue) :: rest, varName, value, hpair, hmismatch,
      output => by
      simp at hpair
      rcases hpair with hhead | htail
      · have hvar : varName = headVar := hhead.1
        have hvalue : value = headValue := hhead.2
        subst varName
        subst value
        exact visitSubfields_wrapWithBoolCase_cons_mismatch_result schema
          resolvers variableValues depth parentType source headVar headValue
          rest selectionSet output hmismatch
      · by_cases hallow :
            Execution.selectionDirectivesAllowBool variableValues
              [NormalForm.directiveForBit headVar headValue] = true
        · rw [visitSubfields_wrapWithBoolCase_cons_allowed_result schema
            resolvers variableValues depth parentType source headVar headValue
            rest selectionSet output hallow]
          exact visitSubfields_wrapWithBoolCase_of_mismatch_pair_result schema
            resolvers variableValues depth parentType source selectionSet rest
            varName value htail hmismatch output
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues
                [NormalForm.directiveForBit headVar headValue] = false := by
            cases h :
                Execution.selectionDirectivesAllowBool variableValues
                  [NormalForm.directiveForBit headVar headValue]
            · rfl
            · exact False.elim (hallow h)
          exact visitSubfields_wrapWithBoolCase_cons_skipped_result schema
            resolvers variableValues depth parentType source headVar headValue
            rest selectionSet output hfalse

theorem visitSubfields_wrapWithBoolCase_of_agrees
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ boolCase,
        (∀ varName value,
          (varName, value) ∈ boolCase
          -> Execution.inputValueBoolean? variableValues (.variable varName) = some value)
        -> ∀ output,
            (visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase boolCase selectionSet) output).fst
            = (visitSubfields schema resolvers variableValues depth parentType source
                selectionSet output).fst
  | [], _hagrees, output => by
      simp [NormalForm.wrapWithBoolCase]
  | (varName, value) :: rest, hagrees, output => by
      have hhead :
          Execution.inputValueBoolean? variableValues (.variable varName) =
            some value :=
        hagrees varName value (by simp)
      have hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [NormalForm.directiveForBit varName value] = true :=
        NormalForm.CompleteNormalization.selectionDirectivesAllowBool_boolCaseBit_of_agrees
          variableValues varName value hhead
      have hrest :
          ∀ restVar restValue, (restVar, restValue) ∈ rest ->
            Execution.inputValueBoolean? variableValues (.variable restVar) =
              some restValue := by
        intro restVar restValue hmem
        exact hagrees restVar restValue (by simp [hmem])
      rw [visitSubfields_wrapWithBoolCase_cons_allowed schema resolvers
        variableValues depth parentType source varName value rest selectionSet
        output hallow]
      exact visitSubfields_wrapWithBoolCase_of_agrees schema resolvers
        variableValues depth parentType source selectionSet rest hrest output

theorem visitSubfields_wrapWithBoolCase_of_agrees_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ boolCase,
        (∀ varName value,
          (varName, value) ∈ boolCase
          -> Execution.inputValueBoolean? variableValues (.variable varName) = some value)
        -> ∀ output,
            visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase boolCase selectionSet) output
            = visitSubfields schema resolvers variableValues depth parentType source
                selectionSet output
  | [], _hagrees, output => by
      simp [NormalForm.wrapWithBoolCase]
  | (varName, value) :: rest, hagrees, output => by
      have hhead :
          Execution.inputValueBoolean? variableValues (.variable varName) =
            some value :=
        hagrees varName value (by simp)
      have hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [NormalForm.directiveForBit varName value] = true :=
        NormalForm.CompleteNormalization.selectionDirectivesAllowBool_boolCaseBit_of_agrees
          variableValues varName value hhead
      have hrest :
          ∀ restVar restValue, (restVar, restValue) ∈ rest ->
            Execution.inputValueBoolean? variableValues (.variable restVar) =
              some restValue := by
        intro restVar restValue hmem
        exact hagrees restVar restValue (by simp [hmem])
      rw [visitSubfields_wrapWithBoolCase_cons_allowed_result schema
        resolvers variableValues depth parentType source varName value rest
        selectionSet output hallow]
      exact visitSubfields_wrapWithBoolCase_of_agrees_result schema resolvers
        variableValues depth parentType source selectionSet rest hrest output

theorem visitSubfields_wrapWithBoolCase_of_variableValuesAgree
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (variables : List NormalForm.BoolVar)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : (∀ varName value,
        (varName, value) ∈ boolCase
        -> varName ∈ variables
            ∧ NormalForm.BoolCase.lookup? boolCase varName = some value)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues boolCase variables
      -> (visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase boolCase selectionSet) output).fst
          = (visitSubfields schema resolvers variableValues depth parentType source
              selectionSet output).fst := by
  intro hcase hagrees
  exact
    visitSubfields_wrapWithBoolCase_of_agrees schema resolvers variableValues
      depth parentType source selectionSet boolCase
      (by
        intro varName value hmem
        rcases hcase varName value hmem with ⟨hvar, hvalue⟩
        exact (hagrees varName hvar).trans hvalue)
      output

theorem visitSubfields_wrapWithBoolCase_of_variableValuesAgree_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (variables : List NormalForm.BoolVar)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : (∀ varName value,
        (varName, value) ∈ boolCase
        -> varName ∈ variables
            ∧ NormalForm.BoolCase.lookup? boolCase varName = some value)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues boolCase variables
      -> visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase boolCase selectionSet) output
          = visitSubfields schema resolvers variableValues depth parentType source
              selectionSet output := by
  intro hcase hagrees
  exact
    visitSubfields_wrapWithBoolCase_of_agrees_result schema resolvers
      variableValues depth parentType source selectionSet boolCase
      (by
        intro varName value hmem
        rcases hcase varName value hmem with ⟨hvar, hvalue⟩
        exact (hagrees varName hvar).trans hvalue)
      output

theorem visitSubfields_wrapWithBoolCase_of_mem_allBoolCases
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (variables : List NormalForm.BoolVar)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : variables.Nodup
      -> boolCase ∈ NormalForm.allBoolCases variables
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues boolCase variables
      -> (visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase boolCase selectionSet) output).fst
          = (visitSubfields schema resolvers variableValues depth parentType source
              selectionSet output).fst := by
  intro hnodup hmem hagrees
  exact
    visitSubfields_wrapWithBoolCase_of_variableValuesAgree schema resolvers
      variableValues depth parentType source variables boolCase
      selectionSet output
      (by
        intro varName value hpair
        exact ⟨
          NormalForm.CompleteNormalization.boolCase_pair_variable_mem_of_allBoolCases
            hmem hpair,
          NormalForm.CompleteNormalization.BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
            hnodup hmem hpair⟩)
      hagrees

theorem visitSubfields_wrapWithBoolCase_of_mem_allBoolCases_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (variables : List NormalForm.BoolVar)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection) (output : Execution.ResponseValue)
    : variables.Nodup
      -> boolCase ∈ NormalForm.allBoolCases variables
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues boolCase variables
      -> visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase boolCase selectionSet) output
          = visitSubfields schema resolvers variableValues depth parentType source
              selectionSet output := by
  intro hnodup hmem hagrees
  exact
    visitSubfields_wrapWithBoolCase_of_variableValuesAgree_result schema
      resolvers variableValues depth parentType source variables boolCase
      selectionSet output
      (by
        intro varName value hpair
        exact ⟨
          NormalForm.CompleteNormalization.boolCase_pair_variable_mem_of_allBoolCases
            hmem hpair,
          NormalForm.CompleteNormalization.BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
            hnodup hmem hpair⟩)
      hagrees

theorem visitSubfields_wrapWithBoolCase_of_nonruntime_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    {runtimeCase candidateCase : NormalForm.BoolCase}
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> candidateCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> candidateCase ≠ runtimeCase
      -> ∀ output,
          (visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase candidateCase selectionSet) output).fst
          = output := by
  intro hruntime hcandidate hagrees hne output
  rcases
      NormalForm.CompleteNormalization.operationBoolVars_case_mismatch_of_ne
        variableValues operation hruntime hcandidate hagrees hne with
    ⟨varName, value, hpair, hmismatch⟩
  exact visitSubfields_wrapWithBoolCase_of_mismatch_pair schema resolvers
    variableValues depth parentType source selectionSet candidateCase varName
    value hpair hmismatch output

theorem visitSubfields_wrapWithBoolCase_of_nonruntime_case_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    {runtimeCase candidateCase : NormalForm.BoolCase}
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> candidateCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> candidateCase ≠ runtimeCase
      -> ∀ output,
          visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.wrapWithBoolCase candidateCase selectionSet) output
          = (output, visitOk) := by
  intro hruntime hcandidate hagrees hne output
  rcases
      NormalForm.CompleteNormalization.operationBoolVars_case_mismatch_of_ne
        variableValues operation hruntime hcandidate hagrees hne with
    ⟨varName, value, hpair, hmismatch⟩
  exact visitSubfields_wrapWithBoolCase_of_mismatch_pair_result schema
    resolvers variableValues depth parentType source selectionSet
    candidateCase varName value hpair hmismatch output

theorem visitSubfields_flatten_boolCaseWrappers_nonruntime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    : ∀ (boolCases : List NormalForm.BoolCase) output,
        runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
        -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
            variableValues runtimeCase
            (NormalForm.operationBoolVars operation)
        -> (∀ candidateCase,
              candidateCase ∈ boolCases
              -> candidateCase
                  ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation))
        -> (∀ candidateCase, candidateCase ∈ boolCases -> candidateCase ≠ runtimeCase)
        -> (visitSubfields schema resolvers variableValues depth parentType source
              (List.flatten
                (boolCases.map
                  (fun boolCase =>
                    NormalForm.wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
              output).fst
            = output
  | [], output, _hruntime, _hagrees, _hall, _hne => by
      simp [visitSubfields]
  | candidateCase :: restCases, output, hruntime, hagrees, hall, hne => by
      have hcandidate :
          candidateCase ∈
            NormalForm.allBoolCases
              (NormalForm.operationBoolVars operation) :=
        hall candidateCase (by simp)
      have hcandidateNe :
          candidateCase ≠ runtimeCase :=
        hne candidateCase (by simp)
      have hhead :
          (visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase candidateCase
                (selectionSetForCase candidateCase)) output).fst
            =
          output :=
        visitSubfields_wrapWithBoolCase_of_nonruntime_case
          schema resolvers variableValues operation depth parentType source
          (selectionSetForCase candidateCase)
          hruntime hcandidate hagrees hcandidateNe output
      have hrest :
          (visitSubfields schema resolvers variableValues depth parentType source
              (List.flatten
                (restCases.map (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase
                    (selectionSetForCase boolCase))))
              output).fst
            =
          output :=
        visitSubfields_flatten_boolCaseWrappers_nonruntime
          schema resolvers variableValues operation depth parentType source
          runtimeCase selectionSetForCase restCases output hruntime hagrees
          (by
            intro boolCase hmem
            exact hall boolCase (by simp [hmem]))
          (by
            intro boolCase hmem
            exact hne boolCase (by simp [hmem]))
      simp only [List.map_cons, List.flatten_cons]
      rw [visitSubfields_append schema resolvers variableValues depth parentType
        source
        (NormalForm.wrapWithBoolCase candidateCase
          (selectionSetForCase candidateCase))
        (List.flatten
          (restCases.map (fun boolCase =>
            NormalForm.wrapWithBoolCase boolCase
              (selectionSetForCase boolCase))))
        output]
      rw [hhead]
      exact hrest

theorem visitSubfields_flatten_boolCaseWrappers_nonruntime_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    : ∀ (boolCases : List NormalForm.BoolCase) output,
        runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
        -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
            variableValues runtimeCase
            (NormalForm.operationBoolVars operation)
        -> (∀ candidateCase,
              candidateCase ∈ boolCases
              -> candidateCase
                  ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation))
        -> (∀ candidateCase, candidateCase ∈ boolCases -> candidateCase ≠ runtimeCase)
        -> visitSubfields schema resolvers variableValues depth parentType source
              (List.flatten
                (boolCases.map
                  (fun boolCase =>
                    NormalForm.wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
              output
            = (output, visitOk)
  | [], output, _hruntime, _hagrees, _hall, _hne => by
      simp [visitSubfields]
  | candidateCase :: restCases, output, hruntime, hagrees, hall, hne => by
      have hcandidate :
          candidateCase ∈
            NormalForm.allBoolCases
              (NormalForm.operationBoolVars operation) :=
        hall candidateCase (by simp)
      have hcandidateNe :
          candidateCase ≠ runtimeCase :=
        hne candidateCase (by simp)
      have hhead :
          visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.wrapWithBoolCase candidateCase
                (selectionSetForCase candidateCase)) output
            =
          (output, visitOk) :=
        visitSubfields_wrapWithBoolCase_of_nonruntime_case_result
          schema resolvers variableValues operation depth parentType source
          (selectionSetForCase candidateCase)
          hruntime hcandidate hagrees hcandidateNe output
      have hrest :
          visitSubfields schema resolvers variableValues depth parentType source
              (List.flatten
                (restCases.map (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase
                    (selectionSetForCase boolCase))))
              output
            =
          (output, visitOk) :=
        visitSubfields_flatten_boolCaseWrappers_nonruntime_result
          schema resolvers variableValues operation depth parentType source
          runtimeCase selectionSetForCase restCases output hruntime hagrees
          (by
            intro boolCase hmem
            exact hall boolCase (by simp [hmem]))
          (by
            intro boolCase hmem
            exact hne boolCase (by simp [hmem]))
      simp only [List.map_cons, List.flatten_cons]
      rw [visitSubfields_append_equivalence schema resolvers variableValues
        depth parentType source
        (NormalForm.wrapWithBoolCase candidateCase
          (selectionSetForCase candidateCase))
        (List.flatten
          (restCases.map (fun boolCase =>
            NormalForm.wrapWithBoolCase boolCase
              (selectionSetForCase boolCase))))
        output]
      rw [hhead]
      simp [hrest]

theorem visitSubfields_flatten_boolCaseWrappers_split_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    (before after : List NormalForm.BoolCase)
    (output : Execution.ResponseValue)
    : NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
        = before ++ runtimeCase :: after
      -> (∀ candidate, candidate ∈ before -> candidate ≠ runtimeCase)
      -> (∀ candidate, candidate ∈ after -> candidate ≠ runtimeCase)
      -> runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> (visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              ((NormalForm.allBoolCases (NormalForm.operationBoolVars operation)).map
                (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
            output).fst
          = (visitSubfields schema resolvers variableValues depth parentType source
              (selectionSetForCase runtimeCase) output).fst := by
  intro hsplit hbeforeNe hafterNe hruntime hagrees
  have hbeforeAll :
      ∀ candidateCase, candidateCase ∈ before ->
        candidateCase ∈
          NormalForm.allBoolCases
            (NormalForm.operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hafterAll :
      ∀ candidateCase, candidateCase ∈ after ->
        candidateCase ∈
          NormalForm.allBoolCases
            (NormalForm.operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hbeforeVisit :
      (visitSubfields schema resolvers variableValues depth parentType source
          (List.flatten
            (before.map (fun boolCase =>
              NormalForm.wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
          output).fst
        =
      output :=
    visitSubfields_flatten_boolCaseWrappers_nonruntime
      schema resolvers variableValues operation depth parentType source
      runtimeCase selectionSetForCase before output hruntime hagrees
      hbeforeAll hbeforeNe
  have hafterVisit :
      ∀ output',
        (visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              (after.map (fun boolCase =>
                NormalForm.wrapWithBoolCase boolCase
                  (selectionSetForCase boolCase))))
            output').fst
          =
        output' := by
    intro output'
    exact visitSubfields_flatten_boolCaseWrappers_nonruntime
      schema resolvers variableValues operation depth parentType source
      runtimeCase selectionSetForCase after output' hruntime hagrees
      hafterAll hafterNe
  have hruntimeVisit :
      (visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase runtimeCase
            (selectionSetForCase runtimeCase))
          output).fst
        =
      (visitSubfields schema resolvers variableValues depth parentType source
          (selectionSetForCase runtimeCase) output).fst :=
    visitSubfields_wrapWithBoolCase_of_mem_allBoolCases schema resolvers
      variableValues depth parentType source
      (NormalForm.operationBoolVars operation) runtimeCase
      (selectionSetForCase runtimeCase) output
      (NormalForm.CompleteNormalization.operationBoolVars_nodup operation)
      hruntime hagrees
  have hafterVisitAt :
      (visitSubfields schema resolvers variableValues depth parentType source
          (List.flatten
            (after.map (fun boolCase =>
              NormalForm.wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
          (visitSubfields schema resolvers variableValues depth parentType
            source (selectionSetForCase runtimeCase) output).fst).fst
        =
      (visitSubfields schema resolvers variableValues depth parentType source
          (selectionSetForCase runtimeCase) output).fst :=
    hafterVisit
      (visitSubfields schema resolvers variableValues depth parentType
        source (selectionSetForCase runtimeCase) output).fst
  rw [hsplit]
  simp only [List.map_append, List.flatten_append, List.map_cons,
    List.flatten_cons]
  rw [visitSubfields_append schema resolvers variableValues depth parentType
    source
    (List.flatten
      (before.map (fun boolCase =>
        NormalForm.wrapWithBoolCase boolCase
          (selectionSetForCase boolCase))))
    (NormalForm.wrapWithBoolCase runtimeCase
      (selectionSetForCase runtimeCase)
      ++ List.flatten
        (after.map (fun boolCase =>
          NormalForm.wrapWithBoolCase boolCase
            (selectionSetForCase boolCase))))
    output]
  rw [hbeforeVisit]
  rw [visitSubfields_append schema resolvers variableValues depth parentType
    source
    (NormalForm.wrapWithBoolCase runtimeCase
      (selectionSetForCase runtimeCase))
    (List.flatten
      (after.map (fun boolCase =>
        NormalForm.wrapWithBoolCase boolCase
          (selectionSetForCase boolCase))))
    output]
  rw [hruntimeVisit]
  exact hafterVisitAt

theorem visitSubfields_flatten_boolCaseWrappers_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    (output : Execution.ResponseValue)
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> (visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              ((NormalForm.allBoolCases (NormalForm.operationBoolVars operation)).map
                (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
            output).fst
          = (visitSubfields schema resolvers variableValues depth parentType source
              (selectionSetForCase runtimeCase) output).fst := by
  intro hruntime hagrees
  rcases
      NormalForm.CompleteNormalization.allBoolCases_operationBoolVars_split
        operation hruntime with
    ⟨before, after, hsplit, hbeforeNe, hafterNe⟩
  exact visitSubfields_flatten_boolCaseWrappers_split_runtime schema
    resolvers variableValues operation depth parentType source runtimeCase
    selectionSetForCase before after output hsplit hbeforeNe hafterNe
    hruntime hagrees

theorem visitSubfields_flatten_boolCaseWrappers_split_runtime_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    (before after : List NormalForm.BoolCase)
    (output : Execution.ResponseValue)
    : NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
        = before ++ runtimeCase :: after
      -> (∀ candidate, candidate ∈ before -> candidate ≠ runtimeCase)
      -> (∀ candidate, candidate ∈ after -> candidate ≠ runtimeCase)
      -> runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              ((NormalForm.allBoolCases (NormalForm.operationBoolVars operation)).map
                (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
            output
          = visitSubfields schema resolvers variableValues depth parentType source
              (selectionSetForCase runtimeCase) output := by
  intro hsplit hbeforeNe hafterNe hruntime hagrees
  have hbeforeAll :
      ∀ candidateCase, candidateCase ∈ before ->
        candidateCase ∈
          NormalForm.allBoolCases
            (NormalForm.operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hafterAll :
      ∀ candidateCase, candidateCase ∈ after ->
        candidateCase ∈
          NormalForm.allBoolCases
            (NormalForm.operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hbeforeVisit :
      visitSubfields schema resolvers variableValues depth parentType source
          (List.flatten
            (before.map (fun boolCase =>
              NormalForm.wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
          output
        =
      (output, visitOk) :=
    visitSubfields_flatten_boolCaseWrappers_nonruntime_result
      schema resolvers variableValues operation depth parentType source
      runtimeCase selectionSetForCase before output hruntime hagrees
      hbeforeAll hbeforeNe
  have hafterVisit :
      ∀ output',
        visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              (after.map (fun boolCase =>
                NormalForm.wrapWithBoolCase boolCase
                  (selectionSetForCase boolCase))))
            output'
          =
        (output', visitOk) := by
    intro output'
    exact visitSubfields_flatten_boolCaseWrappers_nonruntime_result
      schema resolvers variableValues operation depth parentType source
      runtimeCase selectionSetForCase after output' hruntime hagrees
      hafterAll hafterNe
  have hruntimeVisit :
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase runtimeCase
            (selectionSetForCase runtimeCase))
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
          (selectionSetForCase runtimeCase) output :=
    visitSubfields_wrapWithBoolCase_of_mem_allBoolCases_result schema
      resolvers variableValues depth parentType source
      (NormalForm.operationBoolVars operation) runtimeCase
      (selectionSetForCase runtimeCase) output
      (NormalForm.CompleteNormalization.operationBoolVars_nodup operation)
      hruntime hagrees
  rw [hsplit]
  simp only [List.map_append, List.flatten_append, List.map_cons,
    List.flatten_cons]
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    depth parentType source
    (List.flatten
      (before.map (fun boolCase =>
        NormalForm.wrapWithBoolCase boolCase
          (selectionSetForCase boolCase))))
    (NormalForm.wrapWithBoolCase runtimeCase
      (selectionSetForCase runtimeCase)
      ++ List.flatten
        (after.map (fun boolCase =>
          NormalForm.wrapWithBoolCase boolCase
            (selectionSetForCase boolCase))))
    output]
  rw [hbeforeVisit]
  simp
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    depth parentType source
    (NormalForm.wrapWithBoolCase runtimeCase
      (selectionSetForCase runtimeCase))
    (List.flatten
      (after.map (fun boolCase =>
        NormalForm.wrapWithBoolCase boolCase
          (selectionSetForCase boolCase))))
    output]
  rw [hruntimeVisit]
  cases hruntimeResult
        : visitSubfields schema resolvers variableValues depth parentType source
            (selectionSetForCase runtimeCase) output with
  | mk value status =>
      have hafterVisitAt :
          visitSubfields schema resolvers variableValues depth parentType source
              (List.flatten
                (after.map (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase
                    (selectionSetForCase boolCase))))
              value
            =
          (value, visitOk) :=
        hafterVisit value
      simp [hafterVisitAt]

theorem visitSubfields_flatten_boolCaseWrappers_runtime_result
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSetForCase : NormalForm.BoolCase -> List Selection)
    (output : Execution.ResponseValue)
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              ((NormalForm.allBoolCases (NormalForm.operationBoolVars operation)).map
                (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
            output
          = visitSubfields schema resolvers variableValues depth parentType source
              (selectionSetForCase runtimeCase) output := by
  intro hruntime hagrees
  rcases
      NormalForm.CompleteNormalization.allBoolCases_operationBoolVars_split
        operation hruntime with
    ⟨before, after, hsplit, hbeforeNe, hafterNe⟩
  exact visitSubfields_flatten_boolCaseWrappers_split_runtime_result schema
    resolvers variableValues operation depth parentType source runtimeCase
    selectionSetForCase before after output hsplit hbeforeNe hafterNe
    hruntime hagrees

theorem visitSubfields_completeRootBranch_eq_wrapped
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (boolCase : NormalForm.BoolCase)
    (selectionSet : List Selection)
    (output : Execution.ResponseValue)
    : visitSubfields schema resolvers variableValues depth parentType source
        (match selectionSet with
          | [] => []
          | selection :: rest =>
              NormalForm.wrapWithBoolCase boolCase (selection :: rest))
        output
      = visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.wrapWithBoolCase boolCase selectionSet) output := by
  cases selectionSet with
  | nil =>
      rw [visitSubfields_wrapWithBoolCase_empty_result schema resolvers
        variableValues depth parentType source boolCase output]
      simp [visitSubfields]
  | cons selection rest =>
      rfl

theorem visitSubfields_completeNormalizeRootSelectionSet_eq_wrapped
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (variables : List NormalForm.BoolVar)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ∀ output,
        visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.completeNormalizeRootSelectionSet schema variables
            parentType selectionSet)
          output
        = visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              ((NormalForm.allBoolCases variables).map
                (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase
                    (NormalForm.normalizeSelectionSet schema parentType
                      (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)))))
            output := by
  unfold NormalForm.completeNormalizeRootSelectionSet
  induction NormalForm.allBoolCases variables with
  | nil =>
      intro output
      simp [visitSubfields]
  | cons boolCase rest ih =>
      intro output
      simp only [List.map_cons, List.flatten_cons]
      let branchActual :=
        match NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase boolCase selectionSet) with
        | [] => []
        | selection :: rest =>
            NormalForm.wrapWithBoolCase boolCase (selection :: rest)
      let tailActual :=
        List.flatten
          (rest.map (fun boolCase =>
            match NormalForm.normalizeSelectionSet schema parentType
                (NormalForm.filterSelectionSetBoolCase boolCase
                  selectionSet) with
            | [] => []
            | selection :: rest =>
                NormalForm.wrapWithBoolCase boolCase (selection :: rest)))
      let branchWrapped :=
        NormalForm.wrapWithBoolCase boolCase
          (NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase boolCase selectionSet))
      let tailWrapped :=
        List.flatten
          (rest.map (fun boolCase =>
            NormalForm.wrapWithBoolCase boolCase
              (NormalForm.normalizeSelectionSet schema parentType
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet))))
      change
        visitSubfields schema resolvers variableValues depth parentType source
            (branchActual ++ tailActual) output
          =
        visitSubfields schema resolvers variableValues depth parentType source
            (branchWrapped ++ tailWrapped) output
      rw [visitSubfields_append_equivalence schema resolvers variableValues
        depth parentType source branchActual tailActual output]
      rw [visitSubfields_append_equivalence schema resolvers variableValues
        depth parentType source branchWrapped tailWrapped output]
      have hhead :=
        visitSubfields_completeRootBranch_eq_wrapped schema resolvers
          variableValues depth parentType source boolCase
          (NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase boolCase selectionSet))
          output
      have hhead' :
          visitSubfields schema resolvers variableValues depth parentType source
              branchActual output
            =
          visitSubfields schema resolvers variableValues depth parentType source
              branchWrapped output := by
        unfold branchActual branchWrapped
        exact hhead
      rw [hhead']
      have htail :
          visitSubfields schema resolvers variableValues depth parentType source
              tailActual
              (visitSubfields schema resolvers variableValues depth parentType
                source branchWrapped output).fst
            =
          visitSubfields schema resolvers variableValues depth parentType source
              tailWrapped
              (visitSubfields schema resolvers variableValues depth parentType
                source branchWrapped output).fst := by
        unfold tailActual tailWrapped
        exact ih
          (visitSubfields schema resolvers variableValues depth parentType
            source branchWrapped output).fst
      simp only
      rw [htail]

theorem visitSubfields_completeNormalizeRootSelectionSet_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSet : List Selection)
    (output : Execution.ResponseValue)
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.completeNormalizeRootSelectionSet schema
              (NormalForm.operationBoolVars operation) parentType selectionSet)
            output
          = visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.normalizeSelectionSet schema parentType
                (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet))
              output := by
  intro hruntime hagrees
  calc
    visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.completeNormalizeRootSelectionSet schema
            (NormalForm.operationBoolVars operation) parentType selectionSet)
          output
        = visitSubfields schema resolvers variableValues depth parentType source
            (List.flatten
              ((NormalForm.allBoolCases (NormalForm.operationBoolVars operation)).map
                (fun boolCase =>
                  NormalForm.wrapWithBoolCase boolCase
                    (NormalForm.normalizeSelectionSet schema parentType
                      (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)))))
            output :=
      visitSubfields_completeNormalizeRootSelectionSet_eq_wrapped
        schema resolvers variableValues (NormalForm.operationBoolVars operation)
        depth parentType source selectionSet output
    _ = visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet))
          output :=
      visitSubfields_flatten_boolCaseWrappers_runtime_result schema
        resolvers variableValues operation depth parentType source
        runtimeCase
        (fun boolCase =>
          NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase boolCase selectionSet))
        output hruntime hagrees

mutual
  theorem completeValue_filterSelectionSetBoolCase_eq
      (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (operation : Operation) (boolCase : NormalForm.BoolCase)
      (hagrees
        : NormalForm.CompleteNormalization.variableValuesAgreeWithCase
            variableValues boolCase (NormalForm.operationBoolVars operation))
      : ∀ depth parentType selectionSet (value : Execution.ResolverValue ObjectRef)
          previous,
          (∀ varName,
            varName ∈ NormalForm.selectionSetBooleanVariables selectionSet
            -> varName ∈ NormalForm.selectionSetBooleanVariables operation.selectionSet)
          -> completeValue schema resolvers variableValues depth parentType
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
                value previous
              = completeValue schema resolvers variableValues depth parentType
                  selectionSet value previous := by
    intro depth parentType selectionSet value previous hvars
    cases previous with
    | none =>
        cases depth with
        | zero =>
            simp [completeValue]
        | succ depth =>
            cases parentType with
            | named typeName =>
                cases value with
                | null =>
                    simp [completeValue]
                | scalar scalarValue =>
                    simp [completeValue]
                | object runtimeType ref =>
                    by_cases hinclude :
                        schema.typeIncludesObjectBool typeName runtimeType = true
                    · have hvisit :=
                        visitSubfields_filterSelectionSetBoolCase_eq schema
                          resolvers variableValues operation boolCase hagrees
                          depth runtimeType
                          (Execution.ResolverValue.object runtimeType ref)
                          selectionSet (Execution.ResponseValue.object [])
                          hvars
                      simp [completeValue, hinclude, reuseOrCreateObject?,
                        hvisit]
                    · have hfalse :
                        schema.typeIncludesObjectBool typeName runtimeType =
                          false := by
                        cases h :
                            schema.typeIncludesObjectBool typeName runtimeType
                        · rfl
                        · exact False.elim (hinclude h)
                      simp [completeValue, hfalse]
                | list values =>
                    simp [completeValue]
            | list inner =>
                cases value with
                | list values =>
                    have hlist :
                        completeValueList schema resolvers variableValues depth
                            inner
                            (NormalForm.filterSelectionSetBoolCase boolCase
                              selectionSet)
                            values []
                          =
                        completeValueList schema resolvers variableValues depth
                            inner selectionSet values [] := by
                      induction values with
                      | nil =>
                          simp [completeValueList]
                      | cons head tail ih =>
                          have hhead :
                              completeValue schema resolvers variableValues
                                  depth inner
                                  (NormalForm.filterSelectionSetBoolCase
                                    boolCase selectionSet)
                                  head none
                                =
                              completeValue schema resolvers variableValues
                                  depth inner selectionSet head none := by
                            exact
                              completeValue_filterSelectionSetBoolCase_eq schema
                                resolvers variableValues operation boolCase
                                hagrees depth inner selectionSet head none hvars
                          simp [completeValueList, hhead, ih]
                    simp [completeValue, reuseOrCreateList?, hlist]
                | null =>
                    simp [completeValue]
                | scalar scalarValue =>
                    simp [completeValue]
                | object runtimeType ref =>
                    simp [completeValue]
            | nonNull inner =>
                have hrec :=
                  completeValue_filterSelectionSetBoolCase_eq schema resolvers
                    variableValues operation boolCase hagrees (depth + 1) inner
                    selectionSet value none hvars
                simpa [completeValue] using
                  congrArg Execution.nonNullCompletion hrec
    | some previous =>
        cases previous with
        | null =>
            cases depth with
            | zero =>
                simp [completeValue, Execution.outOfFuel]
            | succ depth =>
                simp [completeValue]
        | scalar previousValue =>
            cases depth with
            | zero =>
                simp [completeValue]
            | succ depth =>
                cases parentType with
                | named typeName =>
                    cases value with
                    | null =>
                        simp [completeValue]
                    | scalar scalarValue =>
                        simp [completeValue]
                    | object runtimeType ref =>
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName runtimeType = true
                        · have hvisit :=
                            visitSubfields_filterSelectionSetBoolCase_eq schema
                              resolvers variableValues operation boolCase hagrees
                              depth runtimeType
                              (Execution.ResolverValue.object runtimeType ref)
                              selectionSet (Execution.ResponseValue.object [])
                              hvars
                          simp [completeValue]
                        · have hfalse :
                            schema.typeIncludesObjectBool typeName runtimeType =
                              false := by
                            cases h :
                                schema.typeIncludesObjectBool typeName runtimeType
                            · rfl
                            · exact False.elim (hinclude h)
                          simp [completeValue]
                    | list values =>
                        simp [completeValue]
                | list inner =>
                    cases value with
                    | list values =>
                        have hlist :
                            completeValueList schema resolvers variableValues depth
                                inner
                                (NormalForm.filterSelectionSetBoolCase boolCase
                                  selectionSet)
                                values []
                              =
                            completeValueList schema resolvers variableValues depth
                                inner selectionSet values [] := by
                          induction values with
                          | nil =>
                              simp [completeValueList]
                          | cons head tail ih =>
                              have hhead :
                                  completeValue schema resolvers variableValues
                                      depth inner
                                      (NormalForm.filterSelectionSetBoolCase
                                        boolCase selectionSet)
                                      head none
                                    =
                                  completeValue schema resolvers variableValues
                                      depth inner selectionSet head none := by
                                  exact
                                    completeValue_filterSelectionSetBoolCase_eq
                                      schema resolvers variableValues operation
                                      boolCase hagrees depth inner selectionSet
                                      head none hvars
                              simp [completeValueList, hhead, ih]
                        simp [completeValue]
                    | null =>
                        simp [completeValue]
                    | scalar scalarValue =>
                        simp [completeValue]
                    | object runtimeType ref =>
                        simp [completeValue]
                | nonNull inner =>
                    simp [completeValue]
        | object previousFields =>
            cases depth with
            | zero =>
                simp [completeValue]
            | succ depth =>
                cases parentType with
                | named typeName =>
                    cases value with
                    | null =>
                        simp [completeValue]
                    | scalar scalarValue =>
                        simp [completeValue]
                    | object runtimeType ref =>
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName runtimeType = true
                        · have hvisit :=
                            visitSubfields_filterSelectionSetBoolCase_eq schema
                              resolvers variableValues operation boolCase hagrees
                              depth runtimeType
                              (Execution.ResolverValue.object runtimeType ref)
                              selectionSet (Execution.ResponseValue.object previousFields)
                              hvars
                          simp [completeValue, hinclude,
                            reuseOrCreateObject?, hvisit]
                        · have hfalse :
                            schema.typeIncludesObjectBool typeName runtimeType =
                              false := by
                            cases h :
                                schema.typeIncludesObjectBool typeName runtimeType
                            · rfl
                            · exact False.elim (hinclude h)
                          simp [completeValue, hfalse]
                    | list values =>
                        simp [completeValue]
                | list inner =>
                    cases value with
                    | list values =>
                        have hlist :
                            ∀ previousValues,
                              completeValueList schema resolvers variableValues
                                  depth inner
                                  (NormalForm.filterSelectionSetBoolCase boolCase
                                    selectionSet)
                                  values previousValues
                                =
                              completeValueList schema resolvers variableValues
                                  depth inner selectionSet values previousValues := by
                          intro previousValues
                          induction values generalizing previousValues with
                          | nil =>
                              cases previousValues <;> simp [completeValueList]
                          | cons head tail ih =>
                              cases previousValues with
                              | nil =>
                                  have hhead :
                                      completeValue schema resolvers variableValues
                                          depth inner
                                          (NormalForm.filterSelectionSetBoolCase
                                            boolCase selectionSet)
                                            head none
                                          =
                                        completeValue schema resolvers variableValues
                                            depth inner selectionSet head
                                            none := by
                                      exact
                                        completeValue_filterSelectionSetBoolCase_eq
                                          schema resolvers variableValues
                                          operation boolCase hagrees depth inner
                                          selectionSet head none hvars
                                  simp [completeValueList, hhead, ih []]
                              | cons previous restPrevious =>
                                  have hhead :
                                      completeValue schema resolvers variableValues
                                          depth inner
                                          (NormalForm.filterSelectionSetBoolCase
                                            boolCase selectionSet)
                                            head (some previous)
                                          =
                                        completeValue schema resolvers variableValues
                                            depth inner selectionSet head
                                            (some previous) := by
                                      exact
                                        completeValue_filterSelectionSetBoolCase_eq
                                          schema resolvers variableValues
                                          operation boolCase hagrees depth inner
                                          selectionSet head (some previous)
                                          hvars
                                  simp [completeValueList, hhead, ih restPrevious]
                        simp [completeValue, reuseOrCreateList?]
                    | null =>
                        simp [completeValue]
                    | scalar scalarValue =>
                        simp [completeValue]
                    | object runtimeType ref =>
                        simp [completeValue]
                | nonNull inner =>
                    have hrec :=
                        completeValue_filterSelectionSetBoolCase_eq schema resolvers
                          variableValues operation boolCase hagrees (depth + 1) inner
                          selectionSet value
                          (some (Execution.ResponseValue.object previousFields))
                          hvars
                    simpa [completeValue] using
                      congrArg Execution.nonNullCompletion hrec
        | list previousValues =>
            cases depth with
            | zero =>
                simp [completeValue]
            | succ depth =>
                cases parentType with
                | named typeName =>
                    cases value with
                    | null =>
                        simp [completeValue]
                    | scalar scalarValue =>
                        simp [completeValue]
                    | object runtimeType ref =>
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName runtimeType = true
                        · have hvisit :=
                            visitSubfields_filterSelectionSetBoolCase_eq schema
                              resolvers variableValues operation boolCase hagrees
                              depth runtimeType
                              (Execution.ResolverValue.object runtimeType ref)
                              selectionSet (Execution.ResponseValue.object [])
                              hvars
                          simp [completeValue, hinclude, reuseOrCreateObject?]
                        · have hfalse :
                            schema.typeIncludesObjectBool typeName runtimeType =
                              false := by
                            cases h :
                                schema.typeIncludesObjectBool typeName runtimeType
                            · rfl
                            · exact False.elim (hinclude h)
                          simp [completeValue, hfalse]
                    | list values =>
                        simp [completeValue]
                | list inner =>
                    cases value with
                    | list values =>
                        have hlist :
                            completeValueList schema resolvers variableValues depth
                                inner
                                (NormalForm.filterSelectionSetBoolCase boolCase
                                  selectionSet)
                                values previousValues
                              =
                            completeValueList schema resolvers variableValues depth
                                inner selectionSet values previousValues := by
                          induction values generalizing previousValues with
                          | nil =>
                              cases previousValues <;> simp [completeValueList]
                          | cons head tail ih =>
                              cases previousValues with
                              | nil =>
                                  have hhead :
                                      completeValue schema resolvers variableValues
                                          depth inner
                                          (NormalForm.filterSelectionSetBoolCase
                                            boolCase selectionSet)
                                            head none
                                          =
                                        completeValue schema resolvers variableValues
                                            depth inner selectionSet head
                                            none := by
                                      exact
                                        completeValue_filterSelectionSetBoolCase_eq
                                          schema resolvers variableValues
                                          operation boolCase hagrees depth inner
                                          selectionSet head none hvars
                                  simp [completeValueList, hhead, ih []]
                              | cons previous restPrevious =>
                                  have hhead :
                                      completeValue schema resolvers variableValues
                                          depth inner
                                          (NormalForm.filterSelectionSetBoolCase
                                            boolCase selectionSet)
                                            head (some previous)
                                          =
                                        completeValue schema resolvers variableValues
                                            depth inner selectionSet head
                                            (some previous) := by
                                      exact
                                        completeValue_filterSelectionSetBoolCase_eq
                                          schema resolvers variableValues
                                          operation boolCase hagrees depth inner
                                          selectionSet head (some previous)
                                          hvars
                                  simp [completeValueList, hhead, ih restPrevious]
                        simp [completeValue, reuseOrCreateList?, hlist]
                    | null =>
                        simp [completeValue]
                    | scalar scalarValue =>
                        simp [completeValue]
                    | object runtimeType ref =>
                        simp [completeValue]
                | nonNull inner =>
                    have hrec :=
                        completeValue_filterSelectionSetBoolCase_eq schema resolvers
                          variableValues operation boolCase hagrees (depth + 1) inner
                          selectionSet value
                          (some (Execution.ResponseValue.list previousValues))
                          hvars
                    simpa [completeValue] using
                      congrArg Execution.nonNullCompletion hrec
  termination_by depth parentType selectionSet value previous _hvars =>
    (
      SelectionSet.size selectionSet,
      depth,
      sizeOf parentType,
      sizeOf value,
      sizeOf previous
    )
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [Prod.Lex, SelectionSet.size, Selection.size,
        Nat.succ_eq_add_one]
      try omega
      try (apply Prod.Lex.left; omega)
      try (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; omega)
      try (apply Prod.Lex.right; apply Prod.Lex.left; omega)

  theorem visitSubfields_filterSelectionSetBoolCase_eq
      (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
      (variableValues : Execution.VariableValues)
      (operation : Operation) (boolCase : NormalForm.BoolCase)
      (hagrees
        : NormalForm.CompleteNormalization.variableValuesAgreeWithCase
            variableValues boolCase (NormalForm.operationBoolVars operation))
      : ∀ depth parentType (source : Execution.ResolverValue ObjectRef) selectionSet
          output,
          (∀ varName,
            varName ∈ NormalForm.selectionSetBooleanVariables selectionSet
            -> varName ∈ NormalForm.selectionSetBooleanVariables operation.selectionSet)
          -> visitSubfields schema resolvers variableValues depth parentType source
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
                output
              = visitSubfields schema resolvers variableValues depth parentType source
                  selectionSet output := by
    intro depth parentType source selectionSet output hvars
    cases selectionSet with
    | nil =>
        simp [NormalForm.filterSelectionSetBoolCase, visitSubfields]
    | cons selection rest =>
        have htailVars :
            ∀ varName,
              varName ∈ NormalForm.selectionSetBooleanVariables rest ->
                varName ∈
                  NormalForm.selectionSetBooleanVariables
                    operation.selectionSet := by
          intro varName hmem
          exact hvars varName (by
            simp [NormalForm.selectionSetBooleanVariables, hmem])
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            have hchildVars :
                ∀ varName,
                  varName ∈
                      NormalForm.selectionSetBooleanVariables childSelectionSet ->
                    varName ∈
                      NormalForm.selectionSetBooleanVariables
                        operation.selectionSet := by
              intro varName hmem
              exact hvars varName (by
                simp [NormalForm.selectionSetBooleanVariables,
                  NormalForm.selectionBooleanVariables, hmem])
            have hdirectives :
                NormalForm.directivesAllowIn boolCase directives =
                  Execution.selectionDirectivesAllowBool variableValues
                    directives :=
              NormalForm.CompleteNormalization.directivesAllowInCase_eq_execution_of_field_head
                  variableValues boolCase operation responseName fieldName
                  arguments directives childSelectionSet rest hagrees hvars
            have hchildComplete :
                ∀ completionDepth fieldType value previous,
                  completeValue schema resolvers variableValues
                      completionDepth fieldType
                      (NormalForm.filterSelectionSetBoolCase boolCase
                        childSelectionSet)
                      value previous
                    =
                  completeValue schema resolvers variableValues
                    completionDepth fieldType childSelectionSet value
                    previous := by
              intro completionDepth fieldType value previous
              exact
                completeValue_filterSelectionSetBoolCase_eq schema resolvers
                  variableValues operation boolCase hagrees completionDepth
                  fieldType childSelectionSet value previous hchildVars
            cases hallowCase :
                NormalForm.directivesAllowIn boolCase directives
            · have hskip :
                  Execution.selectionDirectivesAllowBool variableValues
                      directives =
                    false := by
                simpa [hdirectives] using hallowCase
              have htail :=
                visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
                  variableValues operation boolCase hagrees depth parentType
                  source rest output htailVars
              have hheadSkip :
                  visitSelection schema resolvers variableValues depth
                      parentType source
                      (.field responseName fieldName arguments directives
                        childSelectionSet)
                      output =
                    (output, visitOk) := by
                unfold visitSelection
                simp [hskip]
              simpa [NormalForm.filterSelectionSetBoolCase, hallowCase,
                visitSubfields, hheadSkip,
                combineVisitStatus_visitOk_left] using htail
            · have hallow :
                  Execution.selectionDirectivesAllowBool variableValues
                      directives =
                    true := by
                simpa [hdirectives] using hallowCase
              have hhead :
                  visitSelection schema resolvers variableValues depth
                      parentType source
                      (.field responseName fieldName arguments []
                        (NormalForm.filterSelectionSetBoolCase boolCase
                          childSelectionSet))
                      output
                    =
                  visitSelection schema resolvers variableValues depth
                      parentType source
                      (.field responseName fieldName arguments directives
                        childSelectionSet)
                      output := by
                unfold visitSelection
                simp [hallow, selectionDirectivesAllowBool_empty]
                cases hprevious : responseObjectField? responseName output with
                | none =>
                    cases depth <;>
                      simp_all [executeField, executableField, reusablePreviousValue?]
                | some previous =>
                    cases previous <;> cases depth <;>
                      simp_all [executeField, executableField, reusablePreviousValue?]
              have htail :
                  visitSubfields schema resolvers variableValues depth
                      parentType source
                      (NormalForm.filterSelectionSetBoolCase boolCase rest)
                      (visitSelection schema resolvers variableValues depth
                        parentType source
                        (.field responseName fieldName arguments directives
                          childSelectionSet)
                        output).fst
                    =
                  visitSubfields schema resolvers variableValues depth
                      parentType source rest
                      (visitSelection schema resolvers variableValues depth
                        parentType source
                        (.field responseName fieldName arguments directives
                          childSelectionSet)
                        output).fst :=
                visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
                  variableValues operation boolCase hagrees depth parentType
                  source rest
                  (visitSelection schema resolvers variableValues depth
                    parentType source
                    (.field responseName fieldName arguments directives
                      childSelectionSet)
                    output).fst
                  htailVars
              cases childSelectionSet with
              | nil =>
                  have hhead' :
                      visitSelection schema resolvers variableValues depth
                          parentType source
                          (.field responseName fieldName arguments [] [])
                          output
                        =
                      visitSelection schema resolvers variableValues depth
                          parentType source
                          (.field responseName fieldName arguments directives [])
                          output := by
                    simpa [NormalForm.filterSelectionSetBoolCase] using hhead
                  simp [NormalForm.filterSelectionSetBoolCase, hallowCase,
                    visitSubfields, hhead', htail]
              | cons child children =>
                  cases hfiltered
                        : NormalForm.filterSelectionSetBoolCase boolCase
                            (child :: children) with
                  | nil =>
                      have hhead' :
                          visitSelection schema resolvers variableValues depth
                              parentType source
                              (.field responseName fieldName arguments [] [])
                              output
                            =
                          visitSelection schema resolvers variableValues depth
                              parentType source
                              (.field responseName fieldName arguments
                                directives (child :: children))
                              output := by
                        simpa [hfiltered] using hhead
                      simp [NormalForm.filterSelectionSetBoolCase,
                        hallowCase, hfiltered, visitSubfields, hhead', htail]
                  | cons filteredChild filteredChildren =>
                      have hhead' :
                          visitSelection schema resolvers variableValues depth
                              parentType source
                              (.field responseName fieldName arguments []
                                (filteredChild :: filteredChildren))
                              output
                            =
                          visitSelection schema resolvers variableValues depth
                              parentType source
                              (.field responseName fieldName arguments
                                directives (child :: children))
                              output := by
                        simpa [hfiltered] using hhead
                      simp [NormalForm.filterSelectionSetBoolCase,
                        hallowCase, hfiltered, visitSubfields, hhead', htail]
        | inlineFragment typeCondition directives childSelectionSet =>
            have hchildVars :
                ∀ varName,
                  varName ∈
                      NormalForm.selectionSetBooleanVariables childSelectionSet ->
                    varName ∈
                      NormalForm.selectionSetBooleanVariables
                        operation.selectionSet := by
              intro varName hmem
              exact hvars varName (by
                simp [NormalForm.selectionSetBooleanVariables,
                  NormalForm.selectionBooleanVariables, hmem])
            have hdirectives :
                NormalForm.directivesAllowIn boolCase directives =
                  Execution.selectionDirectivesAllowBool variableValues
                    directives :=
              NormalForm.CompleteNormalization.directivesAllowInCase_eq_execution_of_inline_head
                  variableValues boolCase operation typeCondition directives
                  childSelectionSet rest hagrees hvars
            cases hallowCase :
                NormalForm.directivesAllowIn boolCase directives
            · have hskip :
                  Execution.selectionDirectivesAllowBool variableValues
                      directives =
                    false := by
                simpa [hdirectives] using hallowCase
              have htail :=
                visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
                  variableValues operation boolCase hagrees depth parentType
                  source rest output htailVars
              cases typeCondition with
              | none =>
                  simpa [NormalForm.filterSelectionSetBoolCase, hallowCase,
                    visitSubfields, visitSelection, hskip] using htail
              | some typeName =>
                  simpa [NormalForm.filterSelectionSetBoolCase, hallowCase,
                    visitSubfields, visitSelection, hskip] using htail
            · have hallow :
                  Execution.selectionDirectivesAllowBool variableValues
                      directives =
                    true := by
                simpa [hdirectives] using hallowCase
              have hchildVisit :
                  visitSubfields schema resolvers variableValues depth
                      parentType source
                      (NormalForm.filterSelectionSetBoolCase boolCase
                        childSelectionSet)
                      output
                    =
                  visitSubfields schema resolvers variableValues depth
                      parentType source childSelectionSet output :=
                visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
                  variableValues operation boolCase hagrees depth parentType
                  source childSelectionSet output hchildVars
              have htailAfterChild :
                  visitSubfields schema resolvers variableValues depth
                      parentType source
                      (NormalForm.filterSelectionSetBoolCase boolCase rest)
                      (visitSubfields schema resolvers variableValues depth
                        parentType source childSelectionSet output).fst
                    =
                  visitSubfields schema resolvers variableValues depth
                      parentType source rest
                      (visitSubfields schema resolvers variableValues depth
                        parentType source childSelectionSet output).fst :=
                visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
                  variableValues operation boolCase hagrees depth parentType
                  source rest
                  (visitSubfields schema resolvers variableValues depth
                    parentType source childSelectionSet output).fst
                  htailVars
              cases typeCondition with
              | none =>
                  cases hfiltered
                        : NormalForm.filterSelectionSetBoolCase boolCase
                            childSelectionSet with
                  | nil =>
                      have hchildVisitOk :
                          visitSubfields schema resolvers variableValues depth
                              parentType source childSelectionSet output
                            =
                          (output, visitOk) := by
                        simpa [hfiltered, visitSubfields] using hchildVisit.symm
                      have htail :=
                        visitSubfields_filterSelectionSetBoolCase_eq schema
                          resolvers variableValues operation boolCase hagrees
                          depth parentType source rest output htailVars
                      simp [NormalForm.filterSelectionSetBoolCase,
                        hallowCase, hfiltered, visitSubfields, visitSelection,
                        hallow, hchildVisitOk, htail]
                  | cons filteredChild filteredChildren =>
                      have hinlineHead :
                          visitSelection schema resolvers variableValues depth
                              parentType source
                              (.inlineFragment none []
                                (filteredChild :: filteredChildren))
                              output
                            =
                          visitSubfields schema resolvers variableValues depth
                              parentType source childSelectionSet output := by
                        simpa [visitSelection,
                          selectionDirectivesAllowBool_empty, hfiltered] using
                          hchildVisit
                      have horiginalInlineHead :
                          visitSelection schema resolvers variableValues depth
                              parentType source
                              (.inlineFragment none directives
                                childSelectionSet)
                              output
                            =
                          visitSubfields schema resolvers variableValues depth
                              parentType source childSelectionSet output := by
                        simp [visitSelection, hallow]
                      simp [NormalForm.filterSelectionSetBoolCase,
                        hallowCase, hfiltered, visitSubfields,
                        hinlineHead, horiginalInlineHead, htailAfterChild]
              | some typeName =>
                  cases happly :
                      Execution.doesFragmentTypeApplyBool schema parentType source
                        typeName
                  · have htail :=
                        visitSubfields_filterSelectionSetBoolCase_eq schema
                          resolvers variableValues operation boolCase hagrees
                          depth parentType source rest output htailVars
                    cases hfiltered
                          : NormalForm.filterSelectionSetBoolCase boolCase
                              childSelectionSet with
                    | nil =>
                        simp [NormalForm.filterSelectionSetBoolCase,
                          hallowCase, hfiltered, visitSubfields,
                          visitSelection, hallow, happly, htail]
                    | cons filteredChild filteredChildren =>
                        simp [NormalForm.filterSelectionSetBoolCase,
                          hallowCase, hfiltered, visitSubfields,
                          visitSelection, hallow, happly, htail]
                  · cases hfiltered
                          : NormalForm.filterSelectionSetBoolCase boolCase
                              childSelectionSet with
                    | nil =>
                        have hchildVisitOk :
                          visitSubfields schema resolvers variableValues depth
                                parentType source childSelectionSet output
                              =
                            (output, visitOk) := by
                          simpa [hfiltered, visitSubfields] using
                            hchildVisit.symm
                        have htail :=
                          visitSubfields_filterSelectionSetBoolCase_eq schema
                            resolvers variableValues operation boolCase hagrees
                            depth parentType source rest output htailVars
                        simp [NormalForm.filterSelectionSetBoolCase,
                          hallowCase, hfiltered, visitSubfields,
                          visitSelection, hallow, happly, hchildVisitOk, htail]
                    | cons filteredChild filteredChildren =>
                        have hinlineHead :
                            visitSelection schema resolvers variableValues depth
                                parentType source
                                (.inlineFragment (some typeName) []
                                  (filteredChild :: filteredChildren))
                                output
                              =
                            visitSubfields schema resolvers variableValues depth
                                parentType source childSelectionSet output := by
                          simpa [visitSelection,
                            selectionDirectivesAllowBool_empty, happly,
                            hfiltered] using hchildVisit
                        have horiginalInlineHead :
                            visitSelection schema resolvers variableValues depth
                                parentType source
                                (.inlineFragment (some typeName) directives
                                  childSelectionSet)
                                output
                              =
                            visitSubfields schema resolvers variableValues depth
                                parentType source childSelectionSet output := by
                          simp [visitSelection, hallow, happly]
                        simp [NormalForm.filterSelectionSetBoolCase,
                          hallowCase, hfiltered, visitSubfields,
                          hinlineHead, horiginalInlineHead, htailAfterChild]
  termination_by depth parentType source selectionSet output _hvars =>
    (
      SelectionSet.size selectionSet,
      depth,
      sizeOf parentType,
      sizeOf source,
      sizeOf output
    )
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      try simp [SelectionSet.size, Selection.size]
      try omega
      try (apply Prod.Lex.left; omega)
      try (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; omega)
      try (apply Prod.Lex.right; apply Prod.Lex.left; omega)
end

theorem executeRootSelectionSet_eq_of_visitSubfields_eq
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (left right : List Selection)
    : visitSubfields schema resolvers variableValues depth parentType source left
          (Execution.ResponseValue.object [])
        = visitSubfields schema resolvers variableValues depth parentType source right
            (Execution.ResponseValue.object [])
      -> executeRootSelectionSet schema resolvers variableValues depth parentType
            source left
          = executeRootSelectionSet schema resolvers variableValues depth parentType
              source right := by
  intro hvisit
  let toRootResult :
      Execution.ResponseValue × VisitStatus ->
        Execution.Result (List (Name × Execution.ResponseValue)) :=
    fun visited =>
      match visited.snd with
      | Except.error errors => Except.error errors
      | Except.ok (_unit, errors) =>
          match visited.fst with
          | .object fields => Except.ok (fields, errors)
          | _ => Except.error (errors + 1)
  unfold executeRootSelectionSet
  exact congrArg toRootResult hvisit

theorem executeRootSelectionSet_filterSelectionSetBoolCase_eq
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (boolCase : NormalForm.BoolCase)
    (hagrees
      : NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues boolCase (NormalForm.operationBoolVars operation))
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : (∀ varName,
        varName ∈ NormalForm.selectionSetBooleanVariables selectionSet
        -> varName ∈ NormalForm.selectionSetBooleanVariables operation.selectionSet)
      -> executeRootSelectionSet schema resolvers variableValues depth parentType
            source (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
          = executeRootSelectionSet schema resolvers variableValues depth parentType
              source selectionSet := by
  intro hvars
  apply executeRootSelectionSet_eq_of_visitSubfields_eq
  exact
    visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
      variableValues operation boolCase hagrees depth parentType source
      selectionSet (Execution.ResponseValue.object []) hvars

theorem executeRootSelectionSet_completeNormalizeRootSelectionSet_runtime
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSet : List Selection)
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> executeRootSelectionSet schema resolvers variableValues depth parentType
            source
            (NormalForm.completeNormalizeRootSelectionSet schema
              (NormalForm.operationBoolVars operation) parentType selectionSet)
          = executeRootSelectionSet schema resolvers variableValues depth parentType
              source
              (NormalForm.normalizeSelectionSet schema parentType
                (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet)) := by
  intro hruntime hagrees
  apply executeRootSelectionSet_eq_of_visitSubfields_eq
  exact
    visitSubfields_completeNormalizeRootSelectionSet_runtime schema
      resolvers variableValues operation depth parentType source runtimeCase
      selectionSet (Execution.ResponseValue.object []) hruntime hagrees

theorem visitSubfields_completeNormalizeRootSelectionSet_eq_of_filter_normalization
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : NormalForm.BoolCase)
    (selectionSet : List Selection)
    (output : Execution.ResponseValue)
    : runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
      -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
          variableValues runtimeCase
          (NormalForm.operationBoolVars operation)
      -> (∀ varName,
            varName ∈ NormalForm.selectionSetBooleanVariables selectionSet
            -> varName ∈ NormalForm.selectionSetBooleanVariables operation.selectionSet)
      -> visitSubfields schema resolvers variableValues depth parentType source
            (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet)
            output
          = visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.normalizeSelectionSet schema parentType
                (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet))
              output
      -> visitSubfields schema resolvers variableValues depth parentType source
            selectionSet output
          = visitSubfields schema resolvers variableValues depth parentType source
              (NormalForm.completeNormalizeRootSelectionSet schema
                (NormalForm.operationBoolVars operation) parentType selectionSet)
              output := by
  intro hruntime hagrees hvars hnormalized
  have hfilter :
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet)
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
          selectionSet output :=
    visitSubfields_filterSelectionSetBoolCase_eq schema resolvers
      variableValues operation runtimeCase hagrees depth parentType source
      selectionSet output hvars
  have hcomplete :
      visitSubfields schema resolvers variableValues depth parentType source
          (NormalForm.completeNormalizeRootSelectionSet schema
            (NormalForm.operationBoolVars operation) parentType selectionSet)
          output
        =
      visitSubfields schema resolvers variableValues depth parentType source
        (NormalForm.normalizeSelectionSet schema parentType
          (NormalForm.filterSelectionSetBoolCase runtimeCase selectionSet))
        output :=
    visitSubfields_completeNormalizeRootSelectionSet_runtime schema
      resolvers variableValues operation depth parentType source runtimeCase
      selectionSet output hruntime hagrees
  exact hfilter.symm.trans (hnormalized.trans hcomplete.symm)

theorem executeQueryWithFuel_completeNormalizeOperation_eq_of_filter_normalization
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : operationBoolVarsComplete operation
        (Execution.coerceVariableValues operation variableValues)
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues)
                runtimeCase (NormalForm.operationBoolVars operation)
            -> visitSubfields schema resolvers
                  (Execution.coerceVariableValues operation variableValues)
                  depth (operation.rootType schema)
                  source
                  (NormalForm.filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet)
                  (Execution.ResponseValue.object [])
                = visitSubfields schema resolvers
                    (Execution.coerceVariableValues operation variableValues) depth
                    (operation.rootType schema) source
                    (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
                      (NormalForm.filterSelectionSetBoolCase runtimeCase
                        operation.selectionSet))
                    (Execution.ResponseValue.object []))
      -> executeQueryWithFuel schema resolvers variableValues operation depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) depth
              source := by
  intro hcomplete hnormalizeBranch
  rw [executeQueryWithFuel]
  rw [executeQueryWithFuel]
  rw [NormalForm.CompleteNormalization.completeNormalizeOperation_rootSourceAppliesBool]
  cases hroot : Execution.rootSourceAppliesBool schema operation source
  · simp
  · rcases
      NormalForm.CompleteNormalization.operationBoolVarsComplete_caseForVariableValues
        (Execution.coerceVariableValues operation variableValues) operation
        hcomplete with
      ⟨runtimeCase, hruntime, hagrees⟩
    have hvisit :
        visitSubfields schema resolvers
            (Execution.coerceVariableValues operation variableValues) depth
            (operation.rootType schema)
            source operation.selectionSet (Execution.ResponseValue.object [])
          =
        visitSubfields schema resolvers
          (Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema)
          source
          (NormalForm.completeNormalizeRootSelectionSet schema
            (NormalForm.operationBoolVars operation) (operation.rootType schema)
            operation.selectionSet)
          (Execution.ResponseValue.object []) :=
      visitSubfields_completeNormalizeRootSelectionSet_eq_of_filter_normalization
        schema resolvers (Execution.coerceVariableValues operation variableValues)
        operation depth (operation.rootType schema)
        source runtimeCase operation.selectionSet (Execution.ResponseValue.object [])
        hruntime hagrees
        (by
          intro varName hmem
          exact hmem)
        (hnormalizeBranch runtimeCase hruntime hagrees)
    simp only [↓reduceIte]
    simp only [executeRootSelectionSet]
    rw [hvisit]
    simp [Execution.coerceVariableValues, NormalForm.completeNormalizeOperation,
      Operation.rootType, OperationType.rootType]

theorem executeQueryWithFuel_completeNormalizeOperation_eq_of_filter_freshPlanNormalizes
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : operationBoolVarsComplete operation
        (Execution.coerceVariableValues operation variableValues)
      -> (∀ runtimeCase,
            runtimeCase ∈ NormalForm.allBoolCases (NormalForm.operationBoolVars operation)
            -> NormalForm.CompleteNormalization.variableValuesAgreeWithCase
                (Execution.coerceVariableValues operation variableValues)
                runtimeCase (NormalForm.operationBoolVars operation)
            -> SelectionSetFreshPlanNormalizes schema resolvers
                (Execution.coerceVariableValues operation variableValues) depth
                (operation.rootType schema) source
                (NormalForm.filterSelectionSetBoolCase runtimeCase operation.selectionSet)
                (NormalForm.normalizeSelectionSet schema (operation.rootType schema)
                  (NormalForm.filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet)))
      -> executeQueryWithFuel schema resolvers variableValues operation (depth + 1) source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema operation) (depth + 1)
              source := by
  intro hcomplete hnormalizes
  apply executeQueryWithFuel_completeNormalizeOperation_eq_of_filter_normalization
    schema operation resolvers variableValues (depth + 1) source hcomplete
  intro runtimeCase hruntime hagrees
  let normalizes := hnormalizes runtimeCase hruntime hagrees
  have hrawFlat := normalizes.rawFreshFlat.empty
  have hnormalizedFlat := normalizes.normalizedPlan.freshFlat.empty
  unfold VisitSubfieldsFlatCollects at hrawFlat hnormalizedFlat
  rw [hrawFlat, hnormalizedFlat]
  rw [normalizes.collect_eq]
