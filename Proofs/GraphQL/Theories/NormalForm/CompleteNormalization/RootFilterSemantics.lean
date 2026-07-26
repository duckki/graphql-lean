import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterExecution
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.BoolCaseRuntime

/-!
Root Boolean-case selection facts for the current complete normalizer.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem collectFields_wrapWithBoolCase_empty
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    : ∀ boolCase,
        Execution.collectFields schema variableValues parentType source
          (wrapWithBoolCase boolCase [])
        = []
  | [] => by
      simp [wrapWithBoolCase, Execution.collectFields]
  | (varName, value) :: rest => by
      cases hallow :
          Execution.selectionDirectivesAllowBool variableValues
            [directiveForBit varName value]
      · exact collectFields_wrapWithBoolCase_cons_skipped schema
          variableValues parentType source varName value rest []
          hallow
      · exact
          (collectFields_wrapWithBoolCase_cons_allowed schema
            variableValues parentType source varName value rest []
            hallow).trans
            (collectFields_wrapWithBoolCase_empty schema variableValues
              parentType source rest)

theorem collectFields_completeRootBranch_eq_wrapped
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase) (selectionSet : List Selection)
    : Execution.collectFields schema variableValues parentType source
        (match selectionSet with
          | [] => []
          | selection :: rest => wrapWithBoolCase boolCase (selection :: rest))
      = Execution.collectFields schema variableValues parentType source
          (wrapWithBoolCase boolCase selectionSet) := by
  cases selectionSet with
  | nil =>
      simpa [Execution.collectFields] using
        (collectFields_wrapWithBoolCase_empty schema variableValues
          parentType source boolCase).symm
  | cons selection rest =>
      rfl

theorem collectFields_completeNormalizeRootSelectionSet_eq_wrapped
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.collectFields schema variableValues parentType source
        (completeNormalizeRootSelectionSet schema variables parentType selectionSet)
      = Execution.collectFields schema variableValues parentType source
          (List.flatten
            ((allBoolCases variables).map
              (fun boolCase =>
                wrapWithBoolCase boolCase
                  (normalizeSelectionSet schema parentType
                    (filterSelectionSetBoolCase boolCase selectionSet))))) := by
  unfold completeNormalizeRootSelectionSet
  induction allBoolCases variables with
  | nil =>
      simp [Execution.collectFields]
  | cons boolCase rest ih =>
      simp [List.flatten_cons]
      rw [collectFields_append]
      rw [collectFields_append]
      have hhead :=
        collectFields_completeRootBranch_eq_wrapped schema variableValues
          parentType source boolCase
          (normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase boolCase selectionSet))
      have htailStep :=
        congrArg
          (fun tail =>
            Execution.mergeExecutableGroups
              (Execution.collectFields schema variableValues parentType source
                (match normalizeSelectionSet schema parentType
                    (filterSelectionSetBoolCase boolCase selectionSet) with
                | [] => []
                | selection :: rest =>
                    wrapWithBoolCase boolCase (selection :: rest)))
              tail)
          ih
      have hheadStep :=
        congrArg
          (fun head =>
            Execution.mergeExecutableGroups head
              (Execution.collectFields schema variableValues parentType source
                (List.map
                    (fun boolCase =>
                      wrapWithBoolCase boolCase
                        (normalizeSelectionSet schema parentType
                          (filterSelectionSetBoolCase boolCase selectionSet)))
                    rest).flatten))
          hhead
      exact htailStep.trans hheadStep

theorem executeSelectionSet_completeNormalizeRootSelectionSet_runtime
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : BoolCase) (selectionSet : List Selection)
    : runtimeCase ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues runtimeCase
          (operationBoolVars operation)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (completeNormalizeRootSelectionSet schema
              (operationBoolVars operation) parentType selectionSet)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (normalizeSelectionSet schema parentType
                (filterSelectionSetBoolCase runtimeCase selectionSet)) := by
    intro hruntime hagrees
    apply executeSelectionSet_eq_of_collectFields_eq
    calc
      Execution.collectFields schema variableValues parentType source
          (completeNormalizeRootSelectionSet schema
            (operationBoolVars operation) parentType selectionSet)
        =
      Execution.collectFields schema variableValues parentType source
          (List.flatten ((allBoolCases (operationBoolVars operation)).map
            (fun boolCase =>
              wrapWithBoolCase boolCase
                (normalizeSelectionSet schema parentType
                  (filterSelectionSetBoolCase boolCase selectionSet))))) :=
        collectFields_completeNormalizeRootSelectionSet_eq_wrapped schema
          variableValues (operationBoolVars operation) parentType source
          selectionSet
      _ =
      Execution.collectFields schema variableValues parentType source
          (normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase runtimeCase selectionSet)) :=
        collectFields_flatten_boolCaseWrappers_runtime schema variableValues
          operation parentType source runtimeCase
          (fun boolCase =>
            normalizeSelectionSet schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet))
          hruntime hagrees

end CompleteNormalization

end NormalForm

end GraphQL
