import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.StaticMergeReadiness

/-!
Runtime selection facts for generated boolCase-wrapper branches.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem collectFields_flatten_boolCaseWrappers_nonruntime
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : BoolCase)
    (selectionSetForCase : BoolCase -> List Selection)
    : ∀ boolCases : List BoolCase,
        runtimeCase ∈ allBoolCases (operationBoolVars operation)
        -> variableValuesAgreeWithCase variableValues runtimeCase
            (operationBoolVars operation)
        -> (∀ candidateCase,
              candidateCase ∈ boolCases
              -> candidateCase ∈ allBoolCases (operationBoolVars operation))
        -> (∀ candidateCase, candidateCase ∈ boolCases -> candidateCase ≠ runtimeCase)
        -> Execution.collectFields schema variableValues parentType source
              (List.flatten
                (boolCases.map
                  (fun boolCase =>
                    wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
            = []
  | [], _hruntime, _hagrees, _hall, _hne => by
      simp [Execution.collectFields]
  | candidateCase :: restCases, hruntime, hagrees, hall, hne => by
      have hcandidate :
          candidateCase ∈
            allBoolCases
              (operationBoolVars operation) :=
        hall candidateCase (by simp)
      have hcandidateNe :
          candidateCase ≠ runtimeCase :=
        hne candidateCase (by simp)
      have hhead :
          Execution.collectFields schema variableValues parentType source
              (wrapWithBoolCase candidateCase
                (selectionSetForCase candidateCase))
            =
          [] :=
        collectFields_wrapWithBoolCase_of_nonruntime_case
          schema variableValues operation parentType source
          (selectionSetForCase candidateCase)
          hruntime hcandidate hagrees hcandidateNe
      have hrest :
          Execution.collectFields schema variableValues parentType source
              (List.flatten
                (restCases.map (fun boolCase =>
                  wrapWithBoolCase boolCase
                    (selectionSetForCase boolCase))))
            =
          [] :=
        collectFields_flatten_boolCaseWrappers_nonruntime
          schema variableValues operation parentType source runtimeCase
          selectionSetForCase restCases hruntime hagrees
          (by
            intro boolCase hmem
            exact hall boolCase (by simp [hmem]))
          (by
            intro boolCase hmem
            exact hne boolCase (by simp [hmem]))
      simpa using
        (collectFields_append_left_nil schema variableValues parentType source
          (wrapWithBoolCase candidateCase
            (selectionSetForCase candidateCase))
          (List.flatten
            (restCases.map (fun boolCase =>
              wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
          hhead).trans hrest

theorem collectFields_flatten_boolCaseWrappers_split_runtime
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : BoolCase)
    (selectionSetForCase : BoolCase -> List Selection)
    (before after : List BoolCase)
    : allBoolCases (operationBoolVars operation) = before ++ runtimeCase :: after
      -> (∀ candidate, candidate ∈ before -> candidate ≠ runtimeCase)
      -> (∀ candidate, candidate ∈ after -> candidate ≠ runtimeCase)
      -> runtimeCase ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues runtimeCase
          (operationBoolVars operation)
      -> Execution.collectFields schema variableValues parentType source
            (List.flatten
              ((allBoolCases (operationBoolVars operation)).map
                (fun boolCase =>
                  wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
          = Execution.collectFields schema variableValues parentType source
              (selectionSetForCase runtimeCase) := by
  intro hsplit hbeforeNe hafterNe hruntime hagrees
  have hbeforeAll :
      ∀ candidateCase, candidateCase ∈ before ->
        candidateCase ∈
          allBoolCases (operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hafterAll :
      ∀ candidateCase, candidateCase ∈ after ->
        candidateCase ∈
          allBoolCases (operationBoolVars operation) := by
    intro candidate hmem
    rw [hsplit]
    simp [hmem]
  have hbeforeCollect :
      Execution.collectFields schema variableValues parentType source
          (List.flatten
            (before.map (fun boolCase =>
              wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
        =
      [] :=
    collectFields_flatten_boolCaseWrappers_nonruntime schema variableValues
      operation parentType source runtimeCase selectionSetForCase
      before hruntime hagrees hbeforeAll hbeforeNe
  have hafterCollect :
      Execution.collectFields schema variableValues parentType source
          (List.flatten
            (after.map (fun boolCase =>
              wrapWithBoolCase boolCase
                (selectionSetForCase boolCase))))
        =
      [] :=
    collectFields_flatten_boolCaseWrappers_nonruntime schema variableValues
      operation parentType source runtimeCase selectionSetForCase
      after hruntime hagrees hafterAll hafterNe
  have hruntimeCollect :
      Execution.collectFields schema variableValues parentType source
          (wrapWithBoolCase runtimeCase
            (selectionSetForCase runtimeCase))
        =
      Execution.collectFields schema variableValues parentType source
        (selectionSetForCase runtimeCase) :=
    collectFields_wrapWithBoolCase_of_mem_allBoolCases schema
      variableValues parentType source
      (operationBoolVars operation) runtimeCase
      (selectionSetForCase runtimeCase)
      (operationBoolVars_nodup operation) hruntime hagrees
  rw [hsplit]
  simp [List.map_append, List.flatten_append]
  rw [collectFields_append_left_nil schema variableValues parentType source
    (List.flatten
      (before.map (fun boolCase =>
        wrapWithBoolCase boolCase
          (selectionSetForCase boolCase))))
    (wrapWithBoolCase runtimeCase
      (selectionSetForCase runtimeCase)
      ++ List.flatten
        (after.map (fun boolCase =>
          wrapWithBoolCase boolCase
            (selectionSetForCase boolCase)))) hbeforeCollect]
  rw [collectFields_append_right_nil schema variableValues parentType source
    (wrapWithBoolCase runtimeCase
      (selectionSetForCase runtimeCase))
    (List.flatten
      (after.map (fun boolCase =>
        wrapWithBoolCase boolCase
          (selectionSetForCase boolCase)))) hafterCollect]
  exact hruntimeCollect

theorem collectFields_flatten_boolCaseWrappers_runtime
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : BoolCase)
    (selectionSetForCase : BoolCase -> List Selection)
    : runtimeCase ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues runtimeCase
          (operationBoolVars operation)
      -> Execution.collectFields schema variableValues parentType source
            (List.flatten
              ((allBoolCases (operationBoolVars operation)).map
                (fun boolCase =>
                  wrapWithBoolCase boolCase (selectionSetForCase boolCase))))
          = Execution.collectFields schema variableValues parentType source
              (selectionSetForCase runtimeCase) := by
  intro hruntime hagrees
  rcases
      allBoolCases_operationBoolVars_split operation
        hruntime with
    ⟨before, after, hsplit, hbeforeNe, hafterNe⟩
  exact collectFields_flatten_boolCaseWrappers_split_runtime schema
    variableValues operation parentType source runtimeCase
    selectionSetForCase before after hsplit hbeforeNe hafterNe hruntime
    hagrees

theorem collectFields_boolCaseBranchesForGround_runtime
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : BoolCase)
    (selectionSet : List Selection)
    : runtimeCase ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues runtimeCase
          (operationBoolVars operation)
      -> Execution.collectFields schema variableValues groundType source
            (boolCaseBranchesForGround schema groundType
              (operationBoolVars operation) selectionSet)
          = Execution.collectFields schema variableValues groundType source
              (staticCollectForGround schema
                (operationBoolVars operation) groundType groundType
                runtimeCase selectionSet) := by
  intro hruntime hagrees
  unfold boolCaseBranchesForGround
  exact collectFields_flatten_boolCaseWrappers_runtime schema variableValues
    operation groundType source runtimeCase
    (fun boolCase =>
      staticCollectForGround schema
        (operationBoolVars operation) groundType groundType
        boolCase selectionSet)
    hruntime hagrees

theorem executeSelectionSet_boolCaseBranchesForGround_runtime
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (runtimeCase : BoolCase)
    (selectionSet : List Selection)
    : runtimeCase ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues runtimeCase
          (operationBoolVars operation)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            groundType source
            (boolCaseBranchesForGround schema groundType
              (operationBoolVars operation) selectionSet)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              groundType source
              (staticCollectForGround schema
                (operationBoolVars operation) groundType groundType
                runtimeCase selectionSet) := by
    intro hruntime hagrees
    apply executeSelectionSet_eq_of_collectFields_eq
    exact collectFields_boolCaseBranchesForGround_runtime schema
      variableValues operation groundType source runtimeCase selectionSet
      hruntime hagrees

end CompleteNormalization

end NormalForm

end GraphQL
