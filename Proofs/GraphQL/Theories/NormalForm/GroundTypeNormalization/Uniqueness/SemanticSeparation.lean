import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionKeys
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionResponseKeys
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionSuccess

/-!
Semantic-separation lemmas for syntactic uniqueness witnesses.

This module starts with the response-object key mismatch facts used by the
response-name diff constructors. Later probe-execution lemmas can feed concrete
executions into these theorems.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

namespace SemanticSeparation

theorem responseValue_object_left_key_mismatch_not_semanticallyEquivalent
    {left right : List (Name × Execution.ResponseValue)}
    {name : Name}
    : name ∈ left.map Prod.fst
      -> name ∉ right.map Prod.fst
      -> ¬ Execution.ResponseValue.semanticEquivalent (.object left) (.object right) := by
  intro hleftKey hrightNoKey hsem
  exact hrightNoKey
    ((ResponseKeys.ResponseValue.semanticEquivalent_object_mem_fst_iff
      hsem).mp hleftKey)

theorem responseValue_object_right_key_mismatch_not_semanticallyEquivalent
    {left right : List (Name × Execution.ResponseValue)}
    {name : Name}
    : name ∉ left.map Prod.fst
      -> name ∈ right.map Prod.fst
      -> ¬ Execution.ResponseValue.semanticEquivalent (.object left) (.object right) := by
  intro hleftNoKey hrightKey hsem
  exact hleftNoKey
    ((ResponseKeys.ResponseValue.semanticEquivalent_object_mem_fst_iff
      hsem).mpr hrightKey)

theorem responseValue_object_field_value_mismatch_not_semanticallyEquivalent
    {left right : List (Name × Execution.ResponseValue)}
    {name : Name} {leftValue rightValue : Execution.ResponseValue}
    : (left.map Prod.fst).Nodup
      -> (right.map Prod.fst).Nodup
      -> (name, leftValue) ∈ left
      -> (name, rightValue) ∈ right
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ Execution.ResponseValue.semanticEquivalent (.object left) (.object right) := by
  intro hleftNodup hrightNodup hleftMem hrightMem hvalue hsem
  exact hvalue
    (ResponseKeys.ResponseValue.semanticEquivalent_object_field_canonical_eq
      hsem hleftNodup hrightNodup hleftMem hrightMem)

theorem responseValue_semanticEquivalent_singleton_object_field
    {responseName : Name} {left right : Execution.ResponseValue}
    : Execution.ResponseValue.semanticEquivalent
        (.object [(responseName, left)])
        (.object [(responseName, right)])
      -> Execution.ResponseValue.semanticEquivalent left right := by
  intro hsemantic
  have hcanonical :
      Execution.ResponseValue.canonical left =
        Execution.ResponseValue.canonical right :=
    ResponseKeys.ResponseValue.semanticEquivalent_object_field_canonical_eq
      (name := responseName)
      (leftValue := left)
      (rightValue := right)
      hsemantic (by simp) (by simp) (by simp) (by simp)
  simpa [Execution.ResponseValue.semanticEquivalent] using hcanonical

theorem responseValue_singleton_object_not_semanticEquivalent_null
    {responseName : Name} {value : Execution.ResponseValue}
    : ¬ Execution.ResponseValue.semanticEquivalent
          (.object [(responseName, value)]) .null := by
  intro hsemantic
  simp [Execution.ResponseValue.semanticEquivalent,
    Execution.ResponseValue.canonical,
    Execution.ResponseValue.canonicalObjectFields,
    Execution.ResponseValue.sortObjectFieldsByName] at hsemantic

theorem responseValue_object_cons_not_semanticEquivalent_null
    {field : Name × Execution.ResponseValue}
    {fields : List (Name × Execution.ResponseValue)}
    : ¬ Execution.ResponseValue.semanticEquivalent (.object (field :: fields)) .null := by
  intro hsemantic
  rcases field with ⟨responseName, value⟩
  simp [Execution.ResponseValue.semanticEquivalent,
    Execution.ResponseValue.canonical,
    Execution.ResponseValue.canonicalObjectFields,
    Execution.ResponseValue.sortObjectFieldsByName] at hsemantic

theorem responseValue_null_not_semanticEquivalent_object_cons
    {field : Name × Execution.ResponseValue}
    {fields : List (Name × Execution.ResponseValue)}
    : ¬ Execution.ResponseValue.semanticEquivalent .null (.object (field :: fields)) := by
  intro hsemantic
  rcases field with ⟨responseName, value⟩
  simp [Execution.ResponseValue.semanticEquivalent,
    Execution.ResponseValue.canonical,
    Execution.ResponseValue.canonicalObjectFields,
    Execution.ResponseValue.sortObjectFieldsByName] at hsemantic

theorem responseValue_not_semanticEquivalent_null_of_ne {value : Execution.ResponseValue}
    : value ≠ .null -> ¬ Execution.ResponseValue.semanticEquivalent value .null := by
  intro hne hsemantic
  cases value <;>
    simp [Execution.ResponseValue.semanticEquivalent,
      Execution.ResponseValue.canonical] at hsemantic hne

theorem responseValue_null_not_semanticEquivalent_of_ne {value : Execution.ResponseValue}
    : value ≠ .null -> ¬ Execution.ResponseValue.semanticEquivalent .null value := by
  intro hne hsemantic
  cases value <;>
    simp [Execution.ResponseValue.semanticEquivalent,
      Execution.ResponseValue.canonical] at hsemantic hne

theorem responseValue_object_cons_not_semanticEquivalent_empty_object
    {field : Name × Execution.ResponseValue}
    {fields : List (Name × Execution.ResponseValue)}
    : ¬ Execution.ResponseValue.semanticEquivalent (.object (field :: fields))
          (.object []) := by
  intro hsemantic
  have hnameMem :
      field.1 ∈ ([] : List (Name × Execution.ResponseValue)).map Prod.fst :=
    (ResponseKeys.ResponseValue.semanticEquivalent_object_mem_fst_iff
      hsemantic).mp (by simp)
  simp at hnameMem

theorem response_object_left_key_mismatch_not_semanticallyEquivalent
    {left right : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    : name ∈ left.map Prod.fst
      -> name ∉ right.map Prod.fst
      -> ¬ Execution.Response.semanticEquivalent
            ({ data := .object left, errors := leftErrors } : Execution.Response)
            ({ data := .object right, errors := rightErrors } : Execution.Response) := by
  intro hleftKey hrightNoKey hsem
  exact hrightNoKey
    ((ResponseKeys.response_semanticEquivalent_object_mem_fst_iff hsem).mp
      hleftKey)

theorem response_object_right_key_mismatch_not_semanticallyEquivalent
    {left right : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    : name ∉ left.map Prod.fst
      -> name ∈ right.map Prod.fst
      -> ¬ Execution.Response.semanticEquivalent
            ({ data := .object left, errors := leftErrors } : Execution.Response)
            ({ data := .object right, errors := rightErrors } : Execution.Response) := by
  intro hleftNoKey hrightKey hsem
  exact hleftNoKey
    ((ResponseKeys.response_semanticEquivalent_object_mem_fst_iff hsem).mpr
      hrightKey)

theorem response_object_field_value_mismatch_not_semanticallyEquivalent
    {left right : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : (left.map Prod.fst).Nodup
      -> (right.map Prod.fst).Nodup
      -> (name, leftValue) ∈ left
      -> (name, rightValue) ∈ right
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ Execution.Response.semanticEquivalent
            ({ data := .object left, errors := leftErrors } : Execution.Response)
            ({ data := .object right, errors := rightErrors } : Execution.Response) := by
  intro hleftNodup hrightNodup hleftMem hrightMem hvalue hsem
  exact hvalue
    (ResponseKeys.response_semanticEquivalent_object_field_canonical_eq hsem
      hleftNodup hrightNodup hleftMem hrightMem)

theorem responseValue_semanticEquivalent_of_selectionSetsDataEquivalent_object_field
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> (leftFields.map Prod.fst).Nodup
      -> (rightFields.map Prod.fst).Nodup
      -> (name, leftValue) ∈ leftFields
      -> (name, rightValue) ∈ rightFields
      -> selectionSetsDataEquivalent schema parentType left right
      -> Execution.ResponseValue.semanticEquivalent leftValue rightValue := by
  intro hleftResponse hrightResponse hleftNodup hrightNodup hleftMem
    hrightMem hdata
  have hobjectData :
      Execution.ResponseValue.semanticEquivalent (.object leftFields)
        (.object rightFields) := by
    simpa [hleftResponse, hrightResponse] using
      hdata resolvers variableValues fuel source hsource
  exact
    ResponseKeys.ResponseValue.semanticEquivalent_object_field_canonical_eq
      hobjectData hleftNodup hrightNodup hleftMem hrightMem

theorem not_selectionSetsSemanticallyEquivalent_of_left_response_key_mismatch
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> name ∈ leftFields.map Prod.fst
      -> name ∉ rightFields.map Prod.fst
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hleftExec hrightExec hleftKey hrightNoKey hsem
  have hresponses :=
    hsem resolvers variableValues fuel source hsource
  rw [hleftExec, hrightExec] at hresponses
  exact response_object_left_key_mismatch_not_semanticallyEquivalent
    hleftKey hrightNoKey hresponses

theorem not_selectionSetsSemanticallyEquivalent_of_right_response_key_mismatch
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> name ∉ leftFields.map Prod.fst
      -> name ∈ rightFields.map Prod.fst
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hleftExec hrightExec hleftNoKey hrightKey hsem
  have hresponses :=
    hsem resolvers variableValues fuel source hsource
  rw [hleftExec, hrightExec] at hresponses
  exact response_object_right_key_mismatch_not_semanticallyEquivalent
    hleftNoKey hrightKey hresponses

theorem not_selectionSetsSemanticallyEquivalent_of_response_field_value_mismatch
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> (leftFields.map Prod.fst).Nodup
      -> (rightFields.map Prod.fst).Nodup
      -> (name, leftValue) ∈ leftFields
      -> (name, rightValue) ∈ rightFields
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hleftExec hrightExec hleftNodup hrightNodup hleftMem hrightMem
    hvalue hsem
  have hresponses :=
    hsem resolvers variableValues fuel source hsource
  rw [hleftExec, hrightExec] at hresponses
  exact response_object_field_value_mismatch_not_semanticallyEquivalent
    hleftNodup hrightNodup hleftMem hrightMem hvalue hresponses

theorem not_selectionSetsDataEquivalent_of_left_response_key_mismatch
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> name ∈ leftFields.map Prod.fst
      -> name ∉ rightFields.map Prod.fst
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hleftExec hrightExec hleftKey hrightNoKey hdata
  have hresponses :=
    hdata resolvers variableValues fuel source hsource
  rw [hleftExec, hrightExec] at hresponses
  exact responseValue_object_left_key_mismatch_not_semanticallyEquivalent
    hleftKey hrightNoKey hresponses

theorem not_selectionSetsDataEquivalent_of_right_response_key_mismatch
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> name ∉ leftFields.map Prod.fst
      -> name ∈ rightFields.map Prod.fst
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hleftExec hrightExec hleftNoKey hrightKey hdata
  have hresponses :=
    hdata resolvers variableValues fuel source hsource
  rw [hleftExec, hrightExec] at hresponses
  exact responseValue_object_right_key_mismatch_not_semanticallyEquivalent
    hleftNoKey hrightKey hresponses

theorem not_selectionSetsDataEquivalent_of_response_field_value_mismatch
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> (leftFields.map Prod.fst).Nodup
      -> (rightFields.map Prod.fst).Nodup
      -> (name, leftValue) ∈ leftFields
      -> (name, rightValue) ∈ rightFields
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hleftExec hrightExec hleftNodup hrightNodup hleftMem hrightMem
    hvalue hdata
  have hresponses :=
    hdata resolvers variableValues fuel source hsource
  rw [hleftExec, hrightExec] at hresponses
  exact responseValue_object_field_value_mismatch_not_semanticallyEquivalent
    hleftNodup hrightNodup hleftMem hrightMem hvalue hresponses

theorem responseData_not_semanticEquivalent_of_response_field_value_mismatch
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : Execution.executeSelectionSetAsResponse schema leftResolvers variableValues fuel
          parentType leftSource left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema rightResolvers variableValues
            fuel parentType rightSource right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> (leftFields.map Prod.fst).Nodup
      -> (rightFields.map Prod.fst).Nodup
      -> (name, leftValue) ∈ leftFields
      -> (name, rightValue) ∈ rightFields
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel parentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel parentType rightSource right).data := by
  intro hleftExec hrightExec hleftNodup hrightNodup hleftMem hrightMem
    hvalue hresponses
  rw [hleftExec, hrightExec] at hresponses
  exact responseValue_object_field_value_mismatch_not_semanticallyEquivalent
    hleftNodup hrightNodup hleftMem hrightMem hvalue hresponses

theorem responseData_not_semanticEquivalent_of_response_field_value_mismatch_pair
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection}
    {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : Execution.executeSelectionSetAsResponse schema leftResolvers variableValues fuel
          leftParentType leftSource left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema rightResolvers variableValues
            fuel rightParentType rightSource right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> (leftFields.map Prod.fst).Nodup
      -> (rightFields.map Prod.fst).Nodup
      -> (name, leftValue) ∈ leftFields
      -> (name, rightValue) ∈ rightFields
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel rightParentType rightSource right).data := by
  intro hleftExec hrightExec hleftNodup hrightNodup hleftMem hrightMem
    hvalue hresponses
  rw [hleftExec, hrightExec] at hresponses
  exact responseValue_object_field_value_mismatch_not_semanticallyEquivalent
    hleftNodup hrightNodup hleftMem hrightMem hvalue hresponses

theorem responseData_not_semanticEquivalent_of_response_field_value_mismatch_pair_fuels
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection}
    {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
          leftFuel leftParentType leftSource left
        = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema rightResolvers variableValues
            rightFuel rightParentType rightSource right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> (leftFields.map Prod.fst).Nodup
      -> (rightFields.map Prod.fst).Nodup
      -> (name, leftValue) ∈ leftFields
      -> (name, rightValue) ∈ rightFields
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              leftFuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues rightFuel rightParentType rightSource right).data := by
  intro hleftExec hrightExec hleftNodup hrightNodup hleftMem hrightMem
    hvalue hresponses
  rw [hleftExec, hrightExec] at hresponses
  exact responseValue_object_field_value_mismatch_not_semanticallyEquivalent
    hleftNodup hrightNodup hleftMem hrightMem hvalue hresponses

theorem responseName_mem_filterMap_of_field_mem
    {selectionSet : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : Selection.field responseName fieldName arguments directives childSelectionSet
        ∈ selectionSet
      -> responseName ∈ selectionSet.filterMap Selection.responseName? := by
  intro hmem
  exact List.mem_filterMap.mpr
    ⟨Selection.field responseName fieldName arguments directives
        childSelectionSet,
      hmem,
      by simp [Selection.responseName?]⟩

theorem responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {LeftRef RightRef : Type} (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues fuel
                  leftSource responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues fuel
                  rightSource responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel parentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel parentType rightSource right).data := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightNoResponseName hleftFieldOk hrightFieldOk hsemantic
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        leftResolvers variableValues fuel parentType leftSource left
        hleftFree hleftNormal hobject hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        rightResolvers variableValues fuel parentType rightSource right
        hrightFree hrightNormal hobject hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec⟩
  have hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName? :=
    responseName_mem_filterMap_of_field_mem hleftMem
  have hleftCollect :
      responseName ∈
        (Execution.collectFields schema variableValues parentType
          leftSource left).map Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues parentType leftSource responseName hobject hleftNormal
      hleftFree).mpr hleftResponseName
  have hrightCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues parentType
          rightSource right).map Prod.fst := by
    intro hrightCollect
    exact hrightNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues parentType rightSource responseName hobject
        hrightNormal hrightFree).mp hrightCollect)
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema leftResolvers variableValues fuel parentType leftSource left
      hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema rightResolvers variableValues fuel parentType rightSource right
      hrightExec
  have hleftKey : responseName ∈ leftFields.map Prod.fst := by
    rw [hleftResponseKeys]
    exact hleftCollect
  have hrightNoKey : responseName ∉ rightFields.map Prod.fst := by
    intro hrightKey
    rw [hrightResponseKeys] at hrightKey
    exact hrightCollectNo hrightKey
  exact
    (responseValue_object_left_key_mismatch_not_semanticallyEquivalent
      hleftKey hrightNoKey)
      (by simpa [hleftExec, hrightExec] using hsemantic)

theorem responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    {LeftRef RightRef : Type} (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues fuel
                  leftSource responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues fuel
                  rightSource responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel parentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel parentType rightSource right).data := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hrightMem
    hleftNoResponseName hleftFieldOk hrightFieldOk hsemantic
  exact
    responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources
      rightResolvers leftResolvers variableValues fuel rightSource leftSource
      hobject hrightNormal hleftNormal hrightFree hleftFree hrightMem
      hleftNoResponseName hrightFieldOk hleftFieldOk hsemantic.symm

theorem responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues fuel
                  leftSource responseName
                  [{
                    parentType := leftParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues fuel
                  rightSource responseName
                  [{
                    parentType := rightParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel rightParentType rightSource right).data := by
  intro hleftObject hrightObject hleftNormal hrightNormal hleftFree
    hrightFree hleftMem hrightNoResponseName hleftFieldOk hrightFieldOk
    hsemantic
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        leftResolvers variableValues fuel leftParentType leftSource left
        hleftFree hleftNormal hleftObject hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        rightResolvers variableValues fuel rightParentType rightSource right
        hrightFree hrightNormal hrightObject hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec⟩
  have hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName? :=
    responseName_mem_filterMap_of_field_mem hleftMem
  have hleftCollect :
      responseName ∈
        (Execution.collectFields schema variableValues leftParentType
          leftSource left).map Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues leftParentType leftSource responseName hleftObject
      hleftNormal hleftFree).mpr hleftResponseName
  have hrightCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues rightParentType
          rightSource right).map Prod.fst := by
    intro hrightCollect
    exact hrightNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues rightParentType rightSource responseName hrightObject
        hrightNormal hrightFree).mp hrightCollect)
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema leftResolvers variableValues fuel leftParentType leftSource left
      hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema rightResolvers variableValues fuel rightParentType rightSource
      right hrightExec
  have hleftKey : responseName ∈ leftFields.map Prod.fst := by
    rw [hleftResponseKeys]
    exact hleftCollect
  have hrightNoKey : responseName ∉ rightFields.map Prod.fst := by
    intro hrightKey
    rw [hrightResponseKeys] at hrightKey
    exact hrightCollectNo hrightKey
  exact
      (responseValue_object_left_key_mismatch_not_semanticallyEquivalent
        hleftKey hrightNoKey)
      (by simpa [hleftExec, hrightExec] using hsemantic)

theorem responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair_fuels
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues leftFuel
                  leftSource responseName
                  [{
                    parentType := leftParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues rightFuel
                  rightSource responseName
                  [{
                    parentType := rightParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              leftFuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues rightFuel rightParentType rightSource right).data := by
  intro hleftObject hrightObject hleftNormal hrightNormal hleftFree
    hrightFree hleftMem hrightNoResponseName hleftFieldOk hrightFieldOk
    hsemantic
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        leftResolvers variableValues leftFuel leftParentType leftSource left
        hleftFree hleftNormal hleftObject hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        rightResolvers variableValues rightFuel rightParentType rightSource
        right hrightFree hrightNormal hrightObject hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec⟩
  have hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName? :=
    responseName_mem_filterMap_of_field_mem hleftMem
  have hleftCollect :
      responseName ∈
        (Execution.collectFields schema variableValues leftParentType
          leftSource left).map Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues leftParentType leftSource responseName hleftObject
      hleftNormal hleftFree).mpr hleftResponseName
  have hrightCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues rightParentType
          rightSource right).map Prod.fst := by
    intro hrightCollect
    exact hrightNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues rightParentType rightSource responseName hrightObject
        hrightNormal hrightFree).mp hrightCollect)
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema leftResolvers variableValues leftFuel leftParentType leftSource
      left hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema rightResolvers variableValues rightFuel rightParentType
      rightSource right hrightExec
  have hleftKey : responseName ∈ leftFields.map Prod.fst := by
    rw [hleftResponseKeys]
    exact hleftCollect
  have hrightNoKey : responseName ∉ rightFields.map Prod.fst := by
    intro hrightKey
    rw [hrightResponseKeys] at hrightKey
    exact hrightCollectNo hrightKey
  exact
    (responseValue_object_left_key_mismatch_not_semanticallyEquivalent
      hleftKey hrightNoKey)
      (by simpa [hleftExec, hrightExec] using hsemantic)

theorem responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues fuel
                  leftSource responseName
                  [{
                    parentType := leftParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues fuel
                  rightSource responseName
                  [{
                    parentType := rightParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel rightParentType rightSource right).data := by
  intro hleftObject hrightObject hleftNormal hrightNormal hleftFree
    hrightFree hrightMem hleftNoResponseName hleftFieldOk hrightFieldOk
    hsemantic
  exact
    responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair
      rightResolvers leftResolvers variableValues fuel rightSource leftSource
      hrightObject hleftObject hrightNormal hleftNormal hrightFree
      hleftFree hrightMem hleftNoResponseName hrightFieldOk hleftFieldOk
      hsemantic.symm

theorem responseData_not_semanticEquivalent_of_right_responseName_diff_of_field_ok_sources_pair_fuels
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection} {responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet : List Selection} {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues) (leftFuel rightFuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues leftFuel
                  leftSource responseName
                  [{
                    parentType := leftParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues rightFuel
                  rightSource responseName
                  [{
                    parentType := rightParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              leftFuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues rightFuel rightParentType rightSource right).data := by
  intro hleftObject hrightObject hleftNormal hrightNormal hleftFree
    hrightFree hrightMem hleftNoResponseName hleftFieldOk hrightFieldOk
    hsemantic
  exact
    responseData_not_semanticEquivalent_of_left_responseName_diff_of_field_ok_sources_pair_fuels
      rightResolvers leftResolvers variableValues rightFuel leftFuel
      rightSource leftSource hrightObject hleftObject hrightNormal
      hleftNormal hrightFree hleftFree hrightMem hleftNoResponseName
      hrightFieldOk hleftFieldOk hsemantic.symm

theorem not_selectionSetsSemanticallyEquivalent_of_left_responseName_diff
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source left
          = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightNoResponseName hleftExec hrightExec
  have hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName? :=
    responseName_mem_filterMap_of_field_mem hleftMem
  have hleftCollect :
      responseName ∈
        (Execution.collectFields schema variableValues parentType source left).map
          Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues parentType source responseName hobject hleftNormal
      hleftFree).mpr hleftResponseName
  have hrightCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source right).map
          Prod.fst := by
    intro hrightCollect
    exact hrightNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues parentType source responseName hobject hrightNormal
        hrightFree).mp hrightCollect)
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source left hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source right hrightExec
  have hleftKey : responseName ∈ leftFields.map Prod.fst := by
    rw [hleftResponseKeys]
    exact hleftCollect
  have hrightNoKey : responseName ∉ rightFields.map Prod.fst := by
    intro hrightKey
    rw [hrightResponseKeys] at hrightKey
    exact hrightCollectNo hrightKey
  exact not_selectionSetsSemanticallyEquivalent_of_left_response_key_mismatch
    resolvers variableValues fuel source hsource hleftExec hrightExec hleftKey
    hrightNoKey

theorem not_selectionSetsDataEquivalent_of_left_responseName_diff
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source left
          = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightNoResponseName hleftExec hrightExec
  have hleftResponseName :
      responseName ∈ left.filterMap Selection.responseName? :=
    responseName_mem_filterMap_of_field_mem hleftMem
  have hleftCollect :
      responseName ∈
        (Execution.collectFields schema variableValues parentType source left).map
          Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues parentType source responseName hobject hleftNormal
      hleftFree).mpr hleftResponseName
  have hrightCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source right).map
          Prod.fst := by
    intro hrightCollect
    exact hrightNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues parentType source responseName hobject hrightNormal
        hrightFree).mp hrightCollect)
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source left hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source right hrightExec
  have hleftKey : responseName ∈ leftFields.map Prod.fst := by
    rw [hleftResponseKeys]
    exact hleftCollect
  have hrightNoKey : responseName ∉ rightFields.map Prod.fst := by
    intro hrightKey
    rw [hrightResponseKeys] at hrightKey
    exact hrightCollectNo hrightKey
  exact not_selectionSetsDataEquivalent_of_left_response_key_mismatch
    resolvers variableValues fuel source hsource hleftExec hrightExec hleftKey
    hrightNoKey

theorem not_selectionSetsSemanticallyEquivalent_of_right_responseName_diff
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source left
          = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hrightMem
    hleftNoResponseName hleftExec hrightExec
  have hrightResponseName :
      responseName ∈ right.filterMap Selection.responseName? :=
    responseName_mem_filterMap_of_field_mem hrightMem
  have hleftCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source left).map
          Prod.fst := by
    intro hleftCollect
    exact hleftNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues parentType source responseName hobject hleftNormal
        hleftFree).mp hleftCollect)
  have hrightCollect :
      responseName ∈
        (Execution.collectFields schema variableValues parentType source right).map
          Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues parentType source responseName hobject hrightNormal
      hrightFree).mpr hrightResponseName
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source left hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source right hrightExec
  have hleftNoKey : responseName ∉ leftFields.map Prod.fst := by
    intro hleftKey
    rw [hleftResponseKeys] at hleftKey
    exact hleftCollectNo hleftKey
  have hrightKey : responseName ∈ rightFields.map Prod.fst := by
    rw [hrightResponseKeys]
    exact hrightCollect
  exact not_selectionSetsSemanticallyEquivalent_of_right_response_key_mismatch
    resolvers variableValues fuel source hsource hleftExec hrightExec hleftNoKey
    hrightKey

theorem not_selectionSetsDataEquivalent_of_right_responseName_diff
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source left
          = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hrightMem
    hleftNoResponseName hleftExec hrightExec
  have hrightResponseName :
      responseName ∈ right.filterMap Selection.responseName? :=
    responseName_mem_filterMap_of_field_mem hrightMem
  have hleftCollectNo :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source left).map
          Prod.fst := by
    intro hleftCollect
    exact hleftNoResponseName
      ((ExecutionKeys.collectFields_normal_object_key_mem_iff schema
        variableValues parentType source responseName hobject hleftNormal
        hleftFree).mp hleftCollect)
  have hrightCollect :
      responseName ∈
        (Execution.collectFields schema variableValues parentType source right).map
          Prod.fst :=
    (ExecutionKeys.collectFields_normal_object_key_mem_iff schema
      variableValues parentType source responseName hobject hrightNormal
      hrightFree).mpr hrightResponseName
  have hleftResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source left hleftExec
  have hrightResponseKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source right hrightExec
  have hleftNoKey : responseName ∉ leftFields.map Prod.fst := by
    intro hleftKey
    rw [hleftResponseKeys] at hleftKey
    exact hleftCollectNo hleftKey
  have hrightKey : responseName ∈ rightFields.map Prod.fst := by
    rw [hrightResponseKeys]
    exact hrightCollect
  exact not_selectionSetsDataEquivalent_of_right_response_key_mismatch
    resolvers variableValues fuel source hsource hleftExec hrightExec hleftNoKey
    hrightKey

theorem not_selectionSetsSemanticallyEquivalent_of_left_responseName_diff_of_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightNoResponseName hleftFieldOk hrightFieldOk
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source left hleftFree
        hleftNormal hobject hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source right hrightFree
        hrightNormal hobject hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec⟩
  exact not_selectionSetsSemanticallyEquivalent_of_left_responseName_diff
    resolvers variableValues fuel source hsource hobject hleftNormal
    hrightNormal hleftFree hrightFree hleftMem hrightNoResponseName
    hleftExec hrightExec

theorem not_selectionSetsDataEquivalent_of_left_responseName_diff_of_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightNoResponseName hleftFieldOk hrightFieldOk
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source left hleftFree
        hleftNormal hobject hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source right hrightFree
        hrightNormal hobject hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec⟩
  exact not_selectionSetsDataEquivalent_of_left_responseName_diff
    resolvers variableValues fuel source hsource hobject hleftNormal
    hrightNormal hleftFree hrightFree hleftMem hrightNoResponseName
    hleftExec hrightExec

theorem not_selectionSetsSemanticallyEquivalent_of_right_responseName_diff_of_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hrightMem
    hleftNoResponseName hleftFieldOk hrightFieldOk
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source left hleftFree
        hleftNormal hobject hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source right hrightFree
        hrightNormal hobject hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec⟩
  exact not_selectionSetsSemanticallyEquivalent_of_right_responseName_diff
    resolvers variableValues fuel source hsource hobject hleftNormal
    hrightNormal hleftFree hrightFree hrightMem hleftNoResponseName
    hleftExec hrightExec

theorem not_selectionSetsDataEquivalent_of_right_responseName_diff_of_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hrightMem
    hleftNoResponseName hleftFieldOk hrightFieldOk
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source left hleftFree
        hleftNormal hobject hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
        resolvers variableValues fuel parentType source right hrightFree
        hrightNormal hobject hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec⟩
  exact not_selectionSetsDataEquivalent_of_right_responseName_diff
    resolvers variableValues fuel source hsource hobject hleftNormal
    hrightNormal hleftFree hrightFree hrightMem hleftNoResponseName
    hleftExec hrightExec

theorem not_selectionSetsSemanticallyEquivalent_of_responseName_value_diff_of_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftValue rightValue : Execution.ResponseValue}
    {leftTargetErrors rightTargetErrors : Nat}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := leftFieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
          = .ok ([(responseName, leftValue)], leftTargetErrors)
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := rightFieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
          = .ok ([(responseName, rightValue)], rightTargetErrors)
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsSemanticallyEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hleftTarget hrightTarget hvalue hleftFieldOk hrightFieldOk
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues fuel parentType source left
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftValue leftTargetErrors hleftFree
        hleftNormal hobject hleftMem hleftTarget hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues fuel parentType source right
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightValue rightTargetErrors hrightFree
        hrightNormal hobject hrightMem hrightTarget hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source left hleftExec
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source right hrightExec
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source left hleftFree hleftNormal hobject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source right hrightFree hrightNormal hobject
  exact not_selectionSetsSemanticallyEquivalent_of_response_field_value_mismatch
    resolvers variableValues fuel source hsource hleftExec hrightExec
    hleftNodup hrightNodup hleftValueMem hrightValueMem hvalue

theorem not_selectionSetsDataEquivalent_of_responseName_value_diff_of_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftValue rightValue : Execution.ResponseValue}
    {leftTargetErrors rightTargetErrors : Nat}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := leftFieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
          = .ok ([(responseName, leftValue)], leftTargetErrors)
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := rightFieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
          = .ok ([(responseName, rightValue)], rightTargetErrors)
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hleftTarget hrightTarget hvalue hleftFieldOk hrightFieldOk
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues fuel parentType source left
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftValue leftTargetErrors hleftFree
        hleftNormal hobject hleftMem hleftTarget hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues fuel parentType source right
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightValue rightTargetErrors hrightFree
        hrightNormal hobject hrightMem hrightTarget hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source left hleftExec
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source right hrightExec
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source left hleftFree hleftNormal hobject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source right hrightFree hrightNormal hobject
  exact not_selectionSetsDataEquivalent_of_response_field_value_mismatch
    resolvers variableValues fuel source hsource hleftExec hrightExec
    hleftNodup hrightNodup hleftValueMem hrightValueMem hvalue

theorem responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftValue rightValue : Execution.ResponseValue}
    {leftTargetErrors rightTargetErrors : Nat}
    {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Execution.executeField schema leftResolvers variableValues fuel
            leftSource responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := leftFieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
          = .ok ([(responseName, leftValue)], leftTargetErrors)
      -> Execution.executeField schema rightResolvers variableValues fuel
            rightSource responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := rightFieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
          = .ok ([(responseName, rightValue)], rightTargetErrors)
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues fuel
                  leftSource responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues fuel
                  rightSource responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel parentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel parentType rightSource right).data := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hleftTarget hrightTarget hvalue hleftFieldOk hrightFieldOk
    hresponses
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema leftResolvers variableValues fuel parentType leftSource left
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftValue leftTargetErrors hleftFree
        hleftNormal hobject hleftMem hleftTarget hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema rightResolvers variableValues fuel parentType rightSource right
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightValue rightTargetErrors hrightFree
        hrightNormal hobject hrightMem hrightTarget hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema leftResolvers variableValues fuel parentType leftSource left
      hleftExec
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema rightResolvers variableValues fuel parentType rightSource right
      hrightExec
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType leftSource left hleftFree hleftNormal hobject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType rightSource right hrightFree hrightNormal
      hobject
  exact
    responseData_not_semanticEquivalent_of_response_field_value_mismatch_pair
      leftResolvers rightResolvers variableValues fuel leftSource
      rightSource hleftExec hrightExec hleftNodup hrightNodup
      hleftValueMem hrightValueMem hvalue hresponses

theorem responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftValue rightValue : Execution.ResponseValue}
    {leftTargetErrors rightTargetErrors : Nat}
    {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Execution.executeField schema leftResolvers variableValues fuel
            leftSource responseName
            [{
              parentType := leftParentType,
              responseName := responseName,
              fieldName := leftFieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
          = .ok ([(responseName, leftValue)], leftTargetErrors)
      -> Execution.executeField schema rightResolvers variableValues fuel
            rightSource responseName
            [{
              parentType := rightParentType,
              responseName := responseName,
              fieldName := rightFieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
          = .ok ([(responseName, rightValue)], rightTargetErrors)
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues fuel
                  leftSource responseName
                  [{
                    parentType := leftParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues fuel
                  rightSource responseName
                  [{
                    parentType := rightParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              fuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues fuel rightParentType rightSource right).data := by
  intro hleftObject hrightObject hleftNormal hrightNormal hleftFree
    hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalue
    hleftFieldOk hrightFieldOk hresponses
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema leftResolvers variableValues fuel leftParentType leftSource
        left responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftValue leftTargetErrors hleftFree
        hleftNormal hleftObject hleftMem hleftTarget hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema rightResolvers variableValues fuel rightParentType rightSource
        right responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightValue rightTargetErrors hrightFree
        hrightNormal hrightObject hrightMem hrightTarget hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema leftResolvers variableValues fuel leftParentType leftSource left
      hleftExec
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema rightResolvers variableValues fuel rightParentType rightSource
      right hrightExec
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues leftParentType leftSource left hleftFree hleftNormal
      hleftObject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues rightParentType rightSource right hrightFree hrightNormal
      hrightObject
  exact
    responseData_not_semanticEquivalent_of_response_field_value_mismatch_pair
      leftResolvers rightResolvers variableValues fuel leftSource
      rightSource hleftExec hrightExec hleftNodup hrightNodup
      hleftValueMem hrightValueMem hvalue hresponses

theorem responseData_not_semanticEquivalent_of_field_value_diff_of_field_ok_pair_fuels
    {schema : Schema} {leftParentType rightParentType : Name}
    {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftValue rightValue : Execution.ResponseValue}
    {leftTargetErrors rightTargetErrors : Nat}
    {LeftRef RightRef : Type}
    (leftResolvers : Execution.Resolvers LeftRef)
    (rightResolvers : Execution.Resolvers RightRef)
    (variableValues : Execution.VariableValues)
    (leftFuel rightFuel : Nat)
    (leftSource : Execution.ResolverValue LeftRef)
    (rightSource : Execution.ResolverValue RightRef)
    : objectTypeNameBool schema leftParentType = true
      -> objectTypeNameBool schema rightParentType = true
      -> selectionSetNormal schema leftParentType left
      -> selectionSetNormal schema rightParentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Execution.executeField schema leftResolvers variableValues leftFuel
            leftSource responseName
            [{
              parentType := leftParentType,
              responseName := responseName,
              fieldName := leftFieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
          = .ok ([(responseName, leftValue)], leftTargetErrors)
      -> Execution.executeField schema rightResolvers variableValues rightFuel
            rightSource responseName
            [{
              parentType := rightParentType,
              responseName := responseName,
              fieldName := rightFieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
          = .ok ([(responseName, rightValue)], rightTargetErrors)
      -> ¬ Execution.ResponseValue.semanticEquivalent leftValue rightValue
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema leftResolvers variableValues leftFuel
                  leftSource responseName
                  [{
                    parentType := leftParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema rightResolvers variableValues rightFuel
                  rightSource responseName
                  [{
                    parentType := rightParentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema leftResolvers variableValues
              leftFuel leftParentType leftSource left).data
            (Execution.executeSelectionSetAsResponse schema rightResolvers
              variableValues rightFuel rightParentType rightSource right).data := by
  intro hleftObject hrightObject hleftNormal hrightNormal hleftFree
    hrightFree hleftMem hrightMem hleftTarget hrightTarget hvalue
    hleftFieldOk hrightFieldOk hresponses
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema leftResolvers variableValues leftFuel leftParentType
        leftSource left responseName leftFieldName leftArguments
        leftDirectives leftChildSelectionSet leftValue leftTargetErrors
        hleftFree hleftNormal hleftObject hleftMem hleftTarget
        hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema rightResolvers variableValues rightFuel rightParentType
        rightSource right responseName rightFieldName rightArguments
        rightDirectives rightChildSelectionSet rightValue rightTargetErrors
        hrightFree hrightNormal hrightObject hrightMem hrightTarget
        hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema leftResolvers variableValues leftFuel leftParentType leftSource
      left hleftExec
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema rightResolvers variableValues rightFuel rightParentType
      rightSource right hrightExec
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues leftParentType leftSource left hleftFree hleftNormal
      hleftObject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues rightParentType rightSource right hrightFree hrightNormal
      hrightObject
  exact
    responseData_not_semanticEquivalent_of_response_field_value_mismatch_pair_fuels
      leftResolvers rightResolvers variableValues leftFuel rightFuel
      leftSource rightSource hleftExec hrightExec hleftNodup hrightNodup
      hleftValueMem hrightValueMem hvalue hresponses

theorem responseValue_semanticEquivalent_of_selectionSetsDataEquivalent_field_ok
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftValue rightValue : Execution.ResponseValue}
    {leftTargetErrors rightTargetErrors : Nat}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := leftFieldName,
              arguments := leftArguments,
              selectionSet := leftChildSelectionSet
            }]
          = .ok ([(responseName, leftValue)], leftTargetErrors)
      -> Execution.executeField schema resolvers variableValues fuel source
            responseName
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := rightFieldName,
              arguments := rightArguments,
              selectionSet := rightChildSelectionSet
            }]
          = .ok ([(responseName, rightValue)], rightTargetErrors)
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ left
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ right
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues fuel source
                  responseName
                  [{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> selectionSetsDataEquivalent schema parentType left right
      -> Execution.ResponseValue.semanticEquivalent leftValue rightValue := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftMem
    hrightMem hleftTarget hrightTarget hleftFieldOk hrightFieldOk hdata
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues fuel parentType source left
        responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet leftValue leftTargetErrors hleftFree
        hleftNormal hobject hleftMem hleftTarget hleftFieldOk with
    ⟨leftFields, leftErrors, hleftExec, hleftValueMem⟩
  rcases
      ExecutionSuccess.executeSelectionSetAsResponse_object_field_mem_of_field_ok
        schema resolvers variableValues fuel parentType source right
        responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet rightValue rightTargetErrors hrightFree
        hrightNormal hobject hrightMem hrightTarget hrightFieldOk with
    ⟨rightFields, rightErrors, hrightExec, hrightValueMem⟩
  have hleftKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source left hleftExec
  have hrightKeys :=
    ExecutionResponseKeys.executeSelectionSetAsResponse_object_keys_eq_collectFields
      schema resolvers variableValues fuel parentType source right hrightExec
  have hleftNodup : (leftFields.map Prod.fst).Nodup := by
    rw [hleftKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source left hleftFree hleftNormal hobject
  have hrightNodup : (rightFields.map Prod.fst).Nodup := by
    rw [hrightKeys]
    exact ExecutionKeys.collectFields_normal_object_keys_nodup schema
      variableValues parentType source right hrightFree hrightNormal hobject
  exact
    responseValue_semanticEquivalent_of_selectionSetsDataEquivalent_object_field
      resolvers variableValues fuel source hsource hleftExec hrightExec
      hleftNodup hrightNodup hleftValueMem hrightValueMem hdata

theorem responseNames_perm_of_normal_object_semanticallyEquivalent_with_object_responses
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    (hsource
      : ∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    {leftFields rightFields : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source left
          = ({ data := .object leftFields, errors := leftErrors } : Execution.Response)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source right
          = ({ data := .object rightFields, errors := rightErrors } : Execution.Response)
      -> selectionSetsSemanticallyEquivalent schema parentType left right
      -> (left.filterMap Selection.responseName?).Perm
          (right.filterMap Selection.responseName?) := by
  intro hobject hleftNormal hrightNormal hleftFree hrightFree hleftExec
    hrightExec hsem
  apply listPermOfNodupSubsetSubset
  · exact selectionSetNormal_responseNamesNodup hleftNormal
  · exact selectionSetNormal_responseNamesNodup hrightNormal
  · intro responseName hleftResponseName
    rcases selectionSetNormal_field_mem_of_object_responseName_mem
        hleftNormal hobject hleftResponseName with
      ⟨fieldName, arguments, directives, childSelectionSet, hleftMem⟩
    by_cases hrightResponseName :
        responseName ∈ right.filterMap Selection.responseName?
    · exact hrightResponseName
    · exact False.elim
        ((not_selectionSetsSemanticallyEquivalent_of_left_responseName_diff
          resolvers variableValues fuel source hsource hobject hleftNormal
          hrightNormal hleftFree hrightFree hleftMem hrightResponseName
          hleftExec hrightExec) hsem)
  · intro responseName hrightResponseName
    rcases selectionSetNormal_field_mem_of_object_responseName_mem
        hrightNormal hobject hrightResponseName with
      ⟨fieldName, arguments, directives, childSelectionSet, hrightMem⟩
    by_cases hleftResponseName :
        responseName ∈ left.filterMap Selection.responseName?
    · exact hleftResponseName
    · exact False.elim
        ((not_selectionSetsSemanticallyEquivalent_of_right_responseName_diff
          resolvers variableValues fuel source hsource hobject hleftNormal
          hrightNormal hleftFree hrightFree hrightMem hleftResponseName
          hleftExec hrightExec) hsem)

end SemanticSeparation

end GroundTypeNormalization

end NormalForm

end GraphQL
