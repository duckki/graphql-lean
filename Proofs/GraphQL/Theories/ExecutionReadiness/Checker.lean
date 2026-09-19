import Proofs.GraphQL.Theories.ExecutionReadiness.ArgumentDefaults
import Proofs.GraphQL.Theories.SelectionConditions.Runtime

/-! Soundness and completeness of the static execution-error checker on feasible paths. -/

namespace GraphQL.ExecutionReadiness

open Execution SelectionConditions

theorem nonNullNonListOutputTypeInhabitedBool_iff (schema : Schema) (typeRef : TypeRef)
    : nonNullNonListOutputTypeInhabitedBool schema typeRef = true
      ↔ nonNullNonListOutputTypeInhabited schema typeRef := by
  cases typeRef with
  | named name =>
      simp [nonNullNonListOutputTypeInhabitedBool, nonNullNonListOutputTypeInhabited]
  | list inner =>
      simp [nonNullNonListOutputTypeInhabitedBool, nonNullNonListOutputTypeInhabited]
  | nonNull inner =>
      cases inner with
      | named name =>
          simp [nonNullNonListOutputTypeInhabitedBool, nonNullNonListOutputTypeInhabited]
      | list inner =>
          simp [nonNullNonListOutputTypeInhabitedBool, nonNullNonListOutputTypeInhabited]
      | nonNull inner =>
          exact nonNullNonListOutputTypeInhabitedBool_iff schema (.nonNull inner)

theorem withDirectives?_exists_of_allows (values : VariableValues)
    (condition : List BooleanLiteral) (directives : List DirectiveApplication)
    (hcondition : booleanConditionAllows values condition = true)
    (hdirectives : selectionDirectivesAllowBool values directives = true)
    : ∃ nextCondition,
        withDirectives? condition directives = some nextCondition
        ∧ booleanConditionAllows values nextCondition = true := by
  cases hliterals : literalsForDirectives directives with
  | none =>
      have h := literalsForDirectives_none_not_allows values directives hliterals
      simp [hdirectives] at h
  | some literals =>
      have hliteralAllows : booleanConditionAllows values literals = true := by
        rw [← literalsForDirectives_some_allows values directives literals hliterals]
        exact hdirectives
      have hcombined : booleanConditionAllows values (condition ++ literals) = true := by
        rw [booleanConditionAllows_append, hcondition, hliteralAllows]
        rfl
      cases hcanonical : canonicalBooleanCondition (condition ++ literals) with
      | none =>
          have h := canonicalBooleanCondition_none_not_allows values _ hcanonical
          simp [hcombined] at h
      | some nextCondition =>
          refine ⟨nextCondition, by simp [withDirectives?, hliterals, hcanonical], ?_⟩
          rw [← canonicalBooleanCondition_some_allows values _ _ hcanonical]
          exact hcombined

theorem Result.errorCount_add (left right : Result)
    : (left.add right).errorCount = left.errorCount + right.errorCount := by
  simp only [Result.add, Result.errorCount]
  omega

private theorem errorCount_foldl_eq_zero {α : Type} (items : List α) (f : α -> Result)
    (initial : Result)
    (hzero
      : (items.foldl (fun result item => result.add (f item)) initial).errorCount = 0)
    : initial.errorCount = 0 ∧ ∀ item, item ∈ items -> (f item).errorCount = 0 := by
  induction items generalizing initial with
  | nil => exact ⟨hzero, by simp⟩
  | cons head rest ih =>
      obtain ⟨hhead, hrest⟩ := ih (initial.add (f head)) hzero
      rw [Result.errorCount_add, Nat.add_eq_zero_iff] at hhead
      exact ⟨hhead.1, fun item hmem => (List.mem_cons.mp hmem).elim
        (fun heq => heq ▸ hhead.2) (hrest item)⟩

mutual
  theorem checkSelection_sound (schema : Schema) (values : VariableValues)
      (runtimeType : Name) (condition : List BooleanLiteral) (selection : Selection)
      (hcondition : booleanConditionAllows values condition = true)
      (hzero : (checkSelection schema runtimeType condition selection).errorCount = 0)
      : selectionCompositeFieldTypesInhabited schema values runtimeType selection
        ∧ selectionCoercibleInPossibleTypes schema values runtimeType selection := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        by_cases hdirectives : selectionDirectivesAllowBool values directives = true
        · obtain ⟨nextCondition, hnext, hnextAllows⟩ :=
            withDirectives?_exists_of_allows values condition directives hcondition hdirectives
          simp only [checkSelection, hnext] at hzero
          cases hlookup : schema.lookupField runtimeType fieldName with
          | none =>
              simp [selectionCompositeFieldTypesInhabited, selectionCoercibleInPossibleTypes,
                hlookup]
          | some definition =>
              simp only [hlookup] at hzero
              obtain ⟨hlocal, hchildren⟩ := errorCount_foldl_eq_zero _ _ _ hzero
              have hdefaults : omittedNonNullArgumentsHaveDefaultsBool
                  definition.arguments arguments = true := by
                by_cases h : omittedNonNullArgumentsHaveDefaultsBool
                    definition.arguments arguments = true
                · exact h
                · simp [Result.errorCount, h] at hlocal
              have hchildReady := fun childType hmember =>
                checkSelectionSet_sound schema values childType nextCondition children
                  hnextAllows (hchildren childType hmember)
              constructor
              · unfold selectionCompositeFieldTypesInhabited
                intro _ actual hactual hcomposite
                rw [hlookup] at hactual
                cases Option.some.inj hactual
                constructor
                · apply (nonNullNonListOutputTypeInhabitedBool_iff schema _).mp
                  by_cases h : nonNullNonListOutputTypeInhabitedBool schema
                      definition.outputType = true
                  · exact h
                  · simp [Result.errorCount, hdefaults, hcomposite, h] at hlocal
                · intro childType hmember
                  exact (hchildReady childType
                    (by simpa [Schema.typeIncludesObjectBool] using hmember)).1
              · intro _
                rw [hlookup]
                exact ⟨(omittedNonNullArgumentsHaveDefaultsBool_iff _ _).mp hdefaults,
                  fun childType hmember => (hchildReady childType hmember).2⟩
        · simp [selectionCompositeFieldTypesInhabited, selectionCoercibleInPossibleTypes,
            hdirectives]
    | inlineFragment typeCondition directives children =>
        cases typeCondition with
        | none =>
            by_cases hdirectives : selectionDirectivesAllowBool values directives = true
            · obtain ⟨nextCondition, hnext, hnextAllows⟩ :=
                withDirectives?_exists_of_allows values condition directives hcondition hdirectives
              have hchildZero :
                  (checkSelectionSet schema runtimeType nextCondition children).errorCount = 0 := by
                simpa [checkSelection, hnext] using hzero
              have hchild := checkSelectionSet_sound schema values runtimeType nextCondition
                children hnextAllows hchildZero
              constructor
              · unfold selectionCompositeFieldTypesInhabited
                exact fun _ => hchild.1
              · exact fun _ => hchild.2
            · simp [selectionCompositeFieldTypesInhabited, selectionCoercibleInPossibleTypes,
                hdirectives]
        | some typeName =>
            by_cases htype : schema.typeIncludesObjectBool typeName runtimeType = true
            · by_cases hdirectives : selectionDirectivesAllowBool values directives = true
              · obtain ⟨nextCondition, hnext, hnextAllows⟩ :=
                  withDirectives?_exists_of_allows values condition directives
                    hcondition hdirectives
                have hchildZero :
                    (checkSelectionSet schema runtimeType nextCondition children).errorCount
                      = 0 := by
                  simpa [checkSelection, htype, hnext] using hzero
                have hchild := checkSelectionSet_sound schema values runtimeType nextCondition
                  children hnextAllows hchildZero
                constructor
                · unfold selectionCompositeFieldTypesInhabited
                  exact fun _ _ => hchild.1
                · exact fun _ _ => hchild.2
              · simp [selectionCompositeFieldTypesInhabited, selectionCoercibleInPossibleTypes,
                  hdirectives]
            · simp [selectionCompositeFieldTypesInhabited, selectionCoercibleInPossibleTypes, htype]

  theorem checkSelectionSet_sound (schema : Schema) (values : VariableValues)
      (runtimeType : Name) (condition : List BooleanLiteral) (selections : List Selection)
      (hcondition : booleanConditionAllows values condition = true)
      (hzero : (checkSelectionSet schema runtimeType condition selections).errorCount = 0)
      : selectionSetCompositeFieldTypesInhabited schema values runtimeType selections
        ∧ selectionSetCoercibleInPossibleTypes schema values runtimeType selections := by
    cases selections with
    | nil =>
        simp [selectionSetCompositeFieldTypesInhabited, selectionSetCoercibleInPossibleTypes]
    | cons head rest =>
        simp only [checkSelectionSet, Result.errorCount_add, Nat.add_eq_zero_iff] at hzero
        have hhead := checkSelection_sound schema values runtimeType condition head
          hcondition hzero.1
        have hrest := checkSelectionSet_sound schema values runtimeType condition rest
          hcondition hzero.2
        constructor
        · unfold selectionSetCompositeFieldTypesInhabited
          intro selection hmem
          have htail := hrest.1
          unfold selectionSetCompositeFieldTypesInhabited at htail
          exact (List.mem_cons.mp hmem).elim (fun heq => heq ▸ hhead.1) (htail selection)
        · exact ⟨hhead.2, hrest.2⟩
end

end ExecutionReadiness

theorem checkExecutionError_sound {schema : Schema} {operation : Operation}
    : CheckExecutionErrorSound schema operation := by
  intro hzero
  have hready := fun values => ExecutionReadiness.checkSelectionSet_sound schema values
    (operation.rootType schema) [] operation.selectionSet (by rfl) hzero
  exact ⟨fun values => (hready values).1, fun values => (hready values).2⟩

theorem checkExecutionError_isSuccess_sound {schema : Schema} {operation : Operation}
    (hsuccess : (checkExecutionError schema operation).isSuccess = true)
    : operationCompositeFieldTypesInhabited schema operation
      ∧ operationCoercibleInPossibleTypes schema operation := by
  apply checkExecutionError_sound
  simpa [ExecutionReadiness.Result.isSuccess] using hsuccess

namespace ExecutionReadiness

open Execution SelectionConditions

theorem withDirectives?_some_allows (values : VariableValues)
    {condition nextCondition : List BooleanLiteral}
    {directives : List DirectiveApplication}
    (hnext : withDirectives? condition directives = some nextCondition)
    : booleanConditionAllows values nextCondition
      = (booleanConditionAllows values condition
          && selectionDirectivesAllowBool values directives) := by
  cases hliterals : literalsForDirectives directives with
  | none => simp [withDirectives?, hliterals] at hnext
  | some literals =>
      simp only [withDirectives?, hliterals] at hnext
      rw [← canonicalBooleanCondition_some_allows values _ _ hnext,
        booleanConditionAllows_append,
        ← literalsForDirectives_some_allows values directives literals hliterals]

theorem withDirectives?_some_satisfiable {condition nextCondition : List BooleanLiteral}
    {directives : List DirectiveApplication}
    (hnext : withDirectives? condition directives = some nextCondition)
    : ∃ values, booleanConditionAllows values nextCondition = true := by
  cases hliterals : literalsForDirectives directives with
  | none => simp [withDirectives?, hliterals] at hnext
  | some literals =>
      simp only [withDirectives?, hliterals] at hnext
      exact canonicalBooleanCondition_some_satisfiable hnext

private theorem errorCount_foldl_eq_zero_of {α : Type} (items : List α) (f : α -> Result)
    (initial : Result) (hinitial : initial.errorCount = 0)
    (hitems : ∀ item, item ∈ items -> (f item).errorCount = 0)
    : (items.foldl (fun result item => result.add (f item)) initial).errorCount = 0 := by
  induction items generalizing initial with
  | nil => exact hinitial
  | cons head rest ih =>
      apply ih (initial.add (f head))
      · rw [Result.errorCount_add, hinitial, hitems head (by simp)]
      · exact fun item hmember => hitems item (by simp [hmember])

private theorem composite_of_possibleType (schema : Schema) (typeRef : TypeRef)
    {runtimeType : Name}
    (hmember : runtimeType ∈ schema.getPossibleTypes typeRef.namedType)
    : typeRef.isCompositeBool schema = true := by
  unfold Schema.getPossibleTypes at hmember
  unfold TypeRef.isCompositeBool
  cases hlookup : schema.lookupType typeRef.namedType with
  | none => simp [hlookup] at hmember
  | some definition => cases definition <;> simp [hlookup] at hmember ⊢

mutual
  theorem checkSelection_complete (schema : Schema) (runtimeType : Name)
      (condition : List BooleanLiteral) (selection : Selection)
      (hready
        : ∀ values,
            booleanConditionAllows values condition = true
            -> selectionCompositeFieldTypesInhabited schema values runtimeType selection
                ∧ selectionCoercibleInPossibleTypes schema values runtimeType selection)
      : (checkSelection schema runtimeType condition selection).errorCount = 0 := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        cases hnext : withDirectives? condition directives with
        | none => simp [checkSelection, hnext, Result.errorCount]
        | some nextCondition =>
            cases hlookup : schema.lookupField runtimeType fieldName with
            | none => simp [checkSelection, hnext, hlookup, Result.errorCount]
            | some definition =>
                have hfield values (hvalues : booleanConditionAllows values nextCondition = true) :=
                  hready values ((Bool.and_eq_true_iff.mp
                    ((withDirectives?_some_allows values hnext).symm.trans hvalues)).1)
                have hdirectives values
                    (hvalues : booleanConditionAllows values nextCondition = true) :=
                  (Bool.and_eq_true_iff.mp
                    ((withDirectives?_some_allows values hnext).symm.trans hvalues)).2
                obtain ⟨values, hvalues⟩ := withDirectives?_some_satisfiable hnext
                have hdefaults := (hfield values hvalues).2 (hdirectives values hvalues)
                simp only [hlookup] at hdefaults
                have hdefaultsBool := (omittedNonNullArgumentsHaveDefaultsBool_iff _ _).mpr
                  hdefaults.1
                simp only [checkSelection, hnext, hlookup]
                apply errorCount_foldl_eq_zero_of
                · by_cases hcomposite : definition.outputType.isCompositeBool schema = true
                  · have hinhabited := (hfield values hvalues).1
                    unfold selectionCompositeFieldTypesInhabited at hinhabited
                    have houtput := (nonNullNonListOutputTypeInhabitedBool_iff schema _).mpr
                      (hinhabited (hdirectives values hvalues) definition hlookup hcomposite).1
                    simp [Result.errorCount, hdefaultsBool, hcomposite, houtput]
                  · simp [Result.errorCount, hdefaultsBool, hcomposite]
                · intro childType hmember
                  apply checkSelectionSet_complete schema childType nextCondition children
                  intro childValues hchildValues
                  obtain ⟨hinhabited, hcoercible⟩ := hfield childValues hchildValues
                  have hallowed := hdirectives childValues hchildValues
                  unfold selectionCompositeFieldTypesInhabited at hinhabited
                  have hcoercible := hcoercible hallowed
                  simp only [hlookup] at hcoercible
                  exact ⟨(hinhabited hallowed definition hlookup
                    (composite_of_possibleType schema _ hmember)).2 childType
                      (by simpa [Schema.typeIncludesObjectBool] using hmember),
                    hcoercible.2 childType hmember⟩
    | inlineFragment typeCondition directives children =>
        by_cases htype : typeCondition.any
            (fun typeName => !schema.typeIncludesObjectBool typeName runtimeType) = true
        · simp [checkSelection, htype, Result.errorCount]
        · cases hnext : withDirectives? condition directives with
          | none => simp [checkSelection, htype, hnext, Result.errorCount]
          | some nextCondition =>
              simp only [checkSelection, htype, Bool.false_eq_true, ite_false, hnext]
              apply checkSelectionSet_complete schema runtimeType nextCondition children
              intro values hvalues
              rw [withDirectives?_some_allows values hnext, Bool.and_eq_true] at hvalues
              obtain ⟨hinhabited, hcoercible⟩ := hready values hvalues.1
              cases typeCondition with
              | none =>
                  unfold selectionCompositeFieldTypesInhabited at hinhabited
                  exact ⟨hinhabited hvalues.2, hcoercible hvalues.2⟩
              | some typeName =>
                  have happlicable : schema.typeIncludesObjectBool typeName runtimeType = true := by
                    simpa using htype
                  unfold selectionCompositeFieldTypesInhabited at hinhabited
                  exact ⟨
                    hinhabited hvalues.2 happlicable,
                    hcoercible hvalues.2 happlicable
                  ⟩

  theorem checkSelectionSet_complete (schema : Schema) (runtimeType : Name)
      (condition : List BooleanLiteral) (selections : List Selection)
      (hready
        : ∀ values,
            booleanConditionAllows values condition = true
            -> selectionSetCompositeFieldTypesInhabited schema values runtimeType
                  selections
                ∧ selectionSetCoercibleInPossibleTypes schema values runtimeType
                    selections)
      : (checkSelectionSet schema runtimeType condition selections).errorCount = 0 := by
    cases selections with
    | nil => rfl
    | cons head rest =>
        simp only [checkSelectionSet, Result.errorCount_add, Nat.add_eq_zero_iff]
        constructor
        · apply checkSelection_complete schema runtimeType condition head
          intro values hvalues
          obtain ⟨hinhabited, hcoercible⟩ := hready values hvalues
          unfold selectionSetCompositeFieldTypesInhabited at hinhabited
          exact ⟨hinhabited head (by simp), hcoercible.1⟩
        · apply checkSelectionSet_complete schema runtimeType condition rest
          intro values hvalues
          obtain ⟨hinhabited, hcoercible⟩ := hready values hvalues
          unfold selectionSetCompositeFieldTypesInhabited at hinhabited ⊢
          exact ⟨fun selection hmem => hinhabited selection (by simp [hmem]), hcoercible.2⟩
end

end ExecutionReadiness

theorem checkExecutionError_complete {schema : Schema} {operation : Operation}
    : CheckExecutionErrorComplete schema operation := by
  intro hready
  apply ExecutionReadiness.checkSelectionSet_complete
  exact fun values _ => ⟨hready.1 values, hready.2 values⟩

theorem checkExecutionError_isSuccess_complete {schema : Schema} {operation : Operation}
    (hready
      : operationCompositeFieldTypesInhabited schema operation
        ∧ operationCoercibleInPossibleTypes schema operation)
    : (checkExecutionError schema operation).isSuccess = true := by
  simpa [ExecutionReadiness.Result.isSuccess] using checkExecutionError_complete hready

theorem checkExecutionError_errorCount_eq_zero_iff {schema : Schema}
    {operation : Operation}
    : (checkExecutionError schema operation).errorCount = 0
      ↔ operationCompositeFieldTypesInhabited schema operation
        ∧ operationCoercibleInPossibleTypes schema operation :=
  ⟨checkExecutionError_sound, checkExecutionError_complete⟩

end GraphQL
