import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Statements

/-!
Key preservation from field collection through execution results.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

namespace ExecutionResponseKeys

variable {ObjectRef : Type}

theorem executeSelectionSetAsResponse_eq_object_of_executeSelectionSet_ok
    {schema : Schema} {resolvers : Execution.Resolvers ObjectRef}
    {variableValues : Execution.VariableValues}
    {fuel : Nat} {parentType : Name}
    {source : Execution.ResolverValue ObjectRef}
    {selectionSet : List Selection}
    {fields : List (Name × Execution.ResponseValue)}
    {errors : Nat}
    : Execution.executeSelectionSet schema resolvers variableValues fuel
          parentType source selectionSet
        = .ok (fields, errors)
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source selectionSet
          = ({ data := .object fields, errors := errors } : Execution.Response) := by
  intro hok
  simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse, hok]

theorem executeSelectionSetAsResponse_eq_null_of_executeSelectionSet_error
    {schema : Schema} {resolvers : Execution.Resolvers ObjectRef}
    {variableValues : Execution.VariableValues}
    {fuel : Nat} {parentType : Name}
    {source : Execution.ResolverValue ObjectRef}
    {selectionSet : List Selection}
    {errors : Nat}
    : Execution.executeSelectionSet schema resolvers variableValues fuel
          parentType source selectionSet
        = .error errors
      -> Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            parentType source selectionSet
          = ({ data := .null, errors := errors } : Execution.Response) := by
  intro herror
  simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse, herror]

theorem executeField_ok_keys
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (responseName : Name) (fields : List Execution.ExecutableField)
    {outputFields : List (Name × Execution.ResponseValue)}
    {errors : Nat}
    : Execution.executeField schema resolvers variableValues fuel source
          responseName fields
        = .ok (outputFields, errors)
      -> outputFields.map Prod.fst = [responseName] := by
  intro hok
  cases fields with
  | nil =>
      simp [Execution.executeField] at hok
  | cons field rest =>
      cases fuel with
      | zero =>
          simp [Execution.executeField, Execution.outOfFuel] at hok
      | succ fuel' =>
          cases hlookup :
              schema.lookupField field.parentType field.fieldName with
          | none =>
              simp [Execution.executeField, hlookup] at hok
          | some fieldDefinition =>
              cases hresolve :
                  resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
              | none =>
                  cases hhandled :
                      Execution.handleFieldError fieldDefinition.outputType with
                  | error fieldErrors =>
                      simp [Execution.executeField, hlookup, hresolve,
                        Execution.singleFieldResult,
                        hhandled] at hok
                  | ok handled =>
                      rcases handled with ⟨responseValue, fieldErrors⟩
                      simp [Execution.executeField, hlookup, hresolve,
                        Execution.singleFieldResult,
                        hhandled] at hok
                      exact hok.1 ▸ rfl
              | some resolved =>
                  cases hcomplete :
                      Execution.completeValue schema resolvers variableValues
                        fuel' fieldDefinition.outputType (field :: rest)
                        resolved with
                  | error completeErrors =>
                      simp [Execution.executeField, hlookup, hresolve,
                        Execution.singleFieldResult, hcomplete] at hok
                  | ok completed =>
                      rcases completed with ⟨responseValue, childErrors⟩
                      simp [Execution.executeField, hlookup, hresolve,
                        Execution.singleFieldResult, hcomplete] at hok
                      exact hok.1 ▸ rfl

theorem executeCollectedFields_ok_keys
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    : ∀ (groups : List (Name × List Execution.ExecutableField))
          (outputFields : List (Name × Execution.ResponseValue))
          (errors : Nat),
        Execution.executeCollectedFields schema resolvers variableValues fuel
            source groups
          = .ok (outputFields, errors)
        -> outputFields.map Prod.fst = groups.map Prod.fst
  | [], outputFields, errors, hok => by
      simp [Execution.executeCollectedFields] at hok
      exact hok.1 ▸ rfl
  | (responseName, fields) :: rest, outputFields, errors, hok => by
      cases hhead :
          Execution.executeField schema resolvers variableValues fuel source
            responseName fields with
      | error headErrors =>
          cases htail :
              Execution.executeCollectedFields schema resolvers variableValues
                fuel source rest with
          | error tailErrors =>
              simp [Execution.executeCollectedFields, hhead, htail,
                Execution.Result.combine] at hok
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [Execution.executeCollectedFields, hhead, htail,
                Execution.Result.combine] at hok
      | ok headResult =>
          rcases headResult with ⟨headFields, headErrors⟩
          cases htail :
              Execution.executeCollectedFields schema resolvers variableValues
                fuel source rest with
          | error tailErrors =>
              simp [Execution.executeCollectedFields, hhead, htail,
                Execution.Result.combine] at hok
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [Execution.executeCollectedFields, hhead, htail,
                Execution.Result.combine] at hok
              rcases hok with ⟨houtputFields, _herrors⟩
              have hheadKeys :
                  headFields.map Prod.fst = [responseName] :=
                executeField_ok_keys schema resolvers variableValues fuel
                  source responseName fields hhead
              have htailKeys :
                  tailFields.map Prod.fst = rest.map Prod.fst :=
                executeCollectedFields_ok_keys schema resolvers variableValues
                  fuel source rest tailFields tailErrors htail
              rw [← houtputFields]
              simp [List.map_append, hheadKeys, htailKeys]

theorem executeSelectionSetAsResponse_object_keys_eq_collectFields
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    {fields : List (Name × Execution.ResponseValue)}
    {errors : Nat}
    : Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
          parentType source selectionSet
        = ({ data := .object fields, errors := errors } : Execution.Response)
      -> fields.map Prod.fst
          = (Execution.collectFields schema variableValues parentType source
              selectionSet).map
              Prod.fst := by
  intro hresponse
  cases hresult :
      Execution.executeSelectionSet schema resolvers variableValues fuel
        parentType source selectionSet with
  | error executionErrors =>
      simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        hresult] at hresponse
  | ok result =>
      rcases result with ⟨outputFields, outputErrors⟩
      simp [Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
        hresult] at hresponse
      unfold Execution.executeSelectionSet Execution.executeRootSelectionSet
        at hresult
      have hkeys := executeCollectedFields_ok_keys schema resolvers variableValues
        fuel source
        (Execution.collectFields schema variableValues parentType source
          selectionSet) outputFields outputErrors hresult
      simpa [hresponse.1] using hkeys

end ExecutionResponseKeys

end GroundTypeNormalization

end NormalForm

end GraphQL
