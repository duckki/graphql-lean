import GraphQL.IncrementalDelivery.Correctness

/-! Proof-only response-field decomposition. The public collector performs lookup and
response insertion inline; ExecuteField itself returns a completed value. This equation
preserves the existing induction boundary without adding an execution-layer wrapper.
-/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

def executeResponseField (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (responseName : Name)
    (fields : List ExecutableField) (path : ResponsePath := [])
    (deferUsageSet : List Nat := []) (deferMap : DeferMap := [])
    : StateM Nat (Completion (List (Name × ResponseValue))) := do
  match fuel, fields with
  | 0, _ | _, [] => return .error 1
  | fuel + 1, field :: _ =>
      match schema.lookupField parentType field.fieldName with
      | none => return .error 1
      | some definition =>
          let failed : Completion (List (Name × ResponseValue)) :=
            {
              result :=
                singleFieldResult responseName (handleFieldError definition.outputType)
            }
          match coerceArgumentValues schema variables definition.arguments
                  field.arguments with
          | .error => return failed
          | .success arguments =>
              match resolveFieldValue resolvers parentType field.fieldName arguments
                      source with
              | none => return failed
              | some resolved =>
                  let completed ←
                    completeValue schema resolvers variables fuel definition.outputType
                      fields resolved (path ++ [.field responseName]) deferUsageSet
                      deferMap true
                  return completed.map (fun value => [(responseName, value)])

/-- The collector factors through the field helper; witness: fuel/group/lookup case
analysis.
-/
theorem executeCollectedFields_eq (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (deferUsageSet : List Nat) (deferMap : DeferMap)
    : executeCollectedFields schema resolvers variables fuel parentType source fields
        path deferUsageSet deferMap
      = (do
          match fields with
          | [] => return .pure []
          | (responseName, group) :: rest =>
              let head ←
                executeResponseField schema resolvers variables fuel parentType source
                  responseName group path deferUsageSet deferMap
              let tail ←
                executeCollectedFields schema resolvers variables fuel parentType source
                  rest path deferUsageSet deferMap
              return Completion.combine List.append head tail) := by
  cases fields with
  | nil => simp only [executeCollectedFields]
  | cons entry rest =>
      rcases entry with ⟨name, group⟩
      cases fuel with
      | zero =>
          cases group with
          | nil => simp only [executeCollectedFields, executeResponseField]
          | cons field fields =>
              cases hd : schema.lookupField parentType field.fieldName <;>
                simp [executeCollectedFields, executeResponseField, executeField, hd,
                  Completion.map, Completion.error]
      | succ fuel =>
          cases group with
          | nil => simp only [executeCollectedFields, executeResponseField]
          | cons field fields =>
              cases hd : schema.lookupField parentType field.fieldName with
              | none => simp only [executeCollectedFields, executeResponseField, hd]
              | some definition =>
                  simp only [executeCollectedFields, executeResponseField, hd, executeField]
                  cases ha
                        : coerceArgumentValues schema variables definition.arguments
                            field.arguments with
                  | error =>
                      cases definition.outputType <;>
                        simp [handleFieldError, singleFieldResult, Completion.map,
                          Completion.error]
                  | success arguments =>
                      cases hr
                            : resolveFieldValue resolvers parentType field.fieldName
                                arguments source with
                      | none =>
                          cases definition.outputType <;>
                            simp [hr, handleFieldError, singleFieldResult, Completion.map,
                              Completion.error]
                      | some resolved => simp [hr]

/-- Empty collection returns an empty pure result, by unfolding the collector. -/
theorem executeCollectedFields_nil (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (path : ResponsePath)
    (deferUsageSet : List Nat) (deferMap : DeferMap)
    : executeCollectedFields schema resolvers variables fuel parentType source []
        path deferUsageSet deferMap
      = pure (.pure []) := by
  simp only [executeCollectedFields]

/-- Nonempty collection combines head and tail results, by executeCollectedFields_eq. -/
theorem executeCollectedFields_cons (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (responseName : Name)
    (group : List ExecutableField) (rest : CollectedFieldsMap) (path : ResponsePath)
    (deferUsageSet : List Nat) (deferMap : DeferMap)
    : executeCollectedFields schema resolvers variables fuel parentType source
        ((responseName, group) :: rest) path deferUsageSet deferMap
      = (do
          let head ←
            executeResponseField schema resolvers variables fuel parentType source
              responseName group path deferUsageSet deferMap
          let tail ←
            executeCollectedFields schema resolvers variables fuel parentType source
              rest path deferUsageSet deferMap
          return Completion.combine List.append head tail) :=
  executeCollectedFields_eq ..

end GraphQL.IncrementalDelivery.Semantics
