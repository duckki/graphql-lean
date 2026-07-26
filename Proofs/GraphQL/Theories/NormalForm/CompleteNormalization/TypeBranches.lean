import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes

/-!
Proof-facing import boundary for per-type Boolean branch wrappers.

The executable definitions live in `GraphQL.NormalForm` because
`filterSelectionSetBoolCase` and `normalizeBoolCaseForType` live with the public
normalizer definitions.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

private theorem selection_size_pos (selection : Selection) : 0 < selection.size := by
  cases selection <;> simp [Selection.size] <;> omega

private theorem selectionSet_size_tail_lt_cons
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]
  exact Nat.lt_add_of_pos_left (selection_size_pos selection)

private theorem selectionSet_size_child_lt_cons_field
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.field responseName fieldName arguments directives selectionSet
            :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_child_lt_cons_inline
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.inlineFragment typeCondition directives selectionSet :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

def staticCollectForGround
    (schema : Schema) (variables : List BoolVar)
    (lookupParent groundType : Name) (boolCase : BoolCase)
    : List Selection -> List Selection
  | [] => []
  | selection :: rest =>
      let collectedRest :=
        staticCollectForGround schema variables lookupParent groundType boolCase rest
      match selection with
      | .field responseName fieldName arguments directives selectionSet =>
          if directivesAllowIn boolCase directives then
            match schema.lookupField lookupParent fieldName with
            | none =>
                let normalizedSelectionSet :=
                  staticCollectForGround schema variables lookupParent
                    lookupParent boolCase selectionSet
                .field responseName fieldName arguments [] normalizedSelectionSet
                :: collectedRest
            | some fieldDefinition =>
                let returnType := fieldDefinition.outputType.namedType
                let normalizedSelectionSet :=
                  normalizeBoolCaseForType schema boolCase returnType selectionSet
                .field responseName fieldName arguments [] normalizedSelectionSet
                :: collectedRest
          else
            collectedRest
      | .inlineFragment none directives selectionSet =>
          if directivesAllowIn boolCase directives then
            staticCollectForGround schema variables lookupParent
              groundType boolCase selectionSet
            ++ collectedRest
          else
            collectedRest
      | .inlineFragment (some typeCondition) directives selectionSet =>
          if directivesAllowIn boolCase directives
              && schema.typeIncludesObjectBool typeCondition groundType then
            staticCollectForGround schema variables typeCondition
              groundType boolCase selectionSet
            ++ collectedRest
          else
            collectedRest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact selectionSet_size_tail_lt_cons selection rest
    | exact selectionSet_size_child_lt_cons_field responseName fieldName
        arguments directives selectionSet rest
    | exact selectionSet_size_child_lt_cons_inline none directives
        selectionSet rest
    | exact selectionSet_size_child_lt_cons_inline (some typeCondition)
        directives selectionSet rest

def normalizeSelectionSetIn
    (schema : Schema) (variables : List BoolVar)
    (boolCase : BoolCase) (parentType : Name)
    (selectionSet : List Selection)
    : List Selection :=
  staticCollectForGround schema variables parentType parentType boolCase selectionSet

def boolCaseBranchesForGround
    (schema : Schema) (groundType : Name)
    (variables : List BoolVar)
    (selectionSet : List Selection)
    : List Selection :=
  List.flatten
    ((allBoolCases variables).map
      (fun boolCase =>
        wrapWithBoolCase boolCase
          (staticCollectForGround schema variables groundType groundType
            boolCase selectionSet)))

def normalizeForType
    (schema : Schema) (variables : List BoolVar) (returnType : Name)
    (selectionSet : List Selection)
    : List Selection :=
  if leafTypeNameBool schema returnType then
    []
  else
    List.flatten
      ((allBoolCases variables).map
        (fun boolCase =>
          wrapWithBoolCase boolCase
            (normalizeBoolCaseForType schema boolCase returnType selectionSet)))

end CompleteNormalization

end NormalForm

end GraphQL
