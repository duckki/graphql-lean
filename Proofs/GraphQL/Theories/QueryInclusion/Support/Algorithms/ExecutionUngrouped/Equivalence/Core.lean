import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngroupedUncached
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.QueryInclusion.Support.SchemaWellFormedness.PossibleTypes

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Algorithms.ExecutionUngroupedUncached.Eager

open GraphQL.Execution
open GraphQL.Execution

def resultErrorCount {α : Type} : Result α -> Nat
  | .error errors => errors
  | .ok (_value, errors) => errors

def ErrorPresenceEquivalent (ungrouped spec : Nat) : Prop :=
  (spec = 0 -> ungrouped = 0) ∧ (0 < spec -> 0 < ungrouped)

theorem ErrorPresenceEquivalent.trans {left middle right : Nat}
    : ErrorPresenceEquivalent left middle
      -> ErrorPresenceEquivalent middle right
      -> ErrorPresenceEquivalent left right := by
  intro hleft hmiddle
  exact ⟨
    fun hrightZero => hleft.1 (hmiddle.1 hrightZero),
    fun hrightPositive => hleft.2 (hmiddle.2 hrightPositive)
  ⟩

theorem ErrorPresenceEquivalent.symm {left right : Nat}
    : ErrorPresenceEquivalent left right -> ErrorPresenceEquivalent right left := by
  intro h
  constructor
  · intro hleftZero
    by_cases hrightZero : right = 0
    · exact hrightZero
    · have hrightPositive : 0 < right := Nat.pos_of_ne_zero hrightZero
      have hleftPositive : 0 < left := h.2 hrightPositive
      omega
  · intro hleftPositive
    by_cases hrightZero : right = 0
    · have hleftZero : left = 0 := h.1 hrightZero
      omega
    · exact Nat.pos_of_ne_zero hrightZero

def ResultDataAndErrorPresenceEquivalent {α : Type} [Inhabited α]
    (ungrouped spec : Result α)
    : Prop :=
  GraphQL.Execution.Result.getD default ungrouped
    = GraphQL.Execution.Result.getD default spec
  ∧ (resultErrorCount spec = 0 -> resultErrorCount ungrouped = 0)
  ∧ (0 < resultErrorCount spec -> 0 < resultErrorCount ungrouped)

theorem ResultDataAndErrorPresenceEquivalent.trans
    {α : Type} [Inhabited α] {left middle right : Result α}
    : ResultDataAndErrorPresenceEquivalent left middle
      -> ResultDataAndErrorPresenceEquivalent middle right
      -> ResultDataAndErrorPresenceEquivalent left right := by
  intro hleft hmiddle
  rcases hleft with ⟨hleftData, hleftZero, hleftPositive⟩
  rcases hmiddle with ⟨hmiddleData, hmiddleZero, hmiddlePositive⟩
  exact ⟨
    hleftData.trans hmiddleData,
    fun hrightZero => hleftZero (hmiddleZero hrightZero),
    fun hrightPositive => hleftPositive (hmiddlePositive hrightPositive)
  ⟩

def ResponseValueResultAlignedEquivalent (ungrouped spec : Result ResponseValue) : Prop :=
  match ungrouped, spec with
  | .error ungroupedErrors, .error specErrors =>
      ErrorPresenceEquivalent ungroupedErrors specErrors
  | .ok (ungroupedValue, ungroupedErrors), .ok (specValue, specErrors) =>
      ungroupedValue = specValue ∧ ErrorPresenceEquivalent ungroupedErrors specErrors
  | _, _ => False

theorem ResponseValueResultAlignedEquivalent.trans
    {left middle right : Result ResponseValue}
    : ResponseValueResultAlignedEquivalent left middle
      -> ResponseValueResultAlignedEquivalent middle right
      -> ResponseValueResultAlignedEquivalent left right := by
  intro hleft hmiddle
  cases left <;> cases middle <;> cases right <;>
    simp [ResponseValueResultAlignedEquivalent] at hleft hmiddle ⊢
  · exact ErrorPresenceEquivalent.trans hleft hmiddle
  · rcases hleft with ⟨hleftValue, hleftErrors⟩
    rcases hmiddle with ⟨hmiddleValue, hmiddleErrors⟩
    exact ⟨
      hleftValue.trans hmiddleValue,
      ErrorPresenceEquivalent.trans hleftErrors hmiddleErrors
    ⟩

theorem ResponseValueResultAlignedEquivalent.symm {left right : Result ResponseValue}
    : ResponseValueResultAlignedEquivalent left right
      -> ResponseValueResultAlignedEquivalent right left := by
  intro h
  cases left <;> cases right <;>
    simp [ResponseValueResultAlignedEquivalent] at h ⊢
  · exact ErrorPresenceEquivalent.symm h
  · rcases h with ⟨hvalue, herrors⟩
    exact ⟨hvalue.symm, ErrorPresenceEquivalent.symm herrors⟩

def rootSelectionResultData (result : Result (List (Name × ResponseValue)))
    : ResponseValue :=
  match result with
  | .error _errors => .null
  | .ok (fields, _errors) => .object fields

def RootSelectionResultDataAndErrorPresenceEquivalent
    (ungrouped spec : Result (List (Name × ResponseValue)))
    : Prop :=
  rootSelectionResultData ungrouped = rootSelectionResultData spec
  ∧ ErrorPresenceEquivalent (resultErrorCount ungrouped) (resultErrorCount spec)

def RootSelectionResultAlignedEquivalent
    (ungrouped spec : Result (List (Name × ResponseValue)))
    : Prop :=
  match ungrouped, spec with
  | .error ungroupedErrors, .error specErrors =>
      ErrorPresenceEquivalent ungroupedErrors specErrors
  | .ok (ungroupedFields, ungroupedErrors), .ok (specFields, specErrors) =>
      ungroupedFields = specFields ∧ ErrorPresenceEquivalent ungroupedErrors specErrors
  | _, _ => False

theorem RootSelectionResultAlignedEquivalent.trans
    {left middle right : Result (List (Name × ResponseValue))}
    : RootSelectionResultAlignedEquivalent left middle
      -> RootSelectionResultAlignedEquivalent middle right
      -> RootSelectionResultAlignedEquivalent left right := by
  intro hleft hmiddle
  cases left <;> cases middle <;> cases right <;>
    simp [RootSelectionResultAlignedEquivalent] at hleft hmiddle ⊢
  · exact ErrorPresenceEquivalent.trans hleft hmiddle
  · rcases hleft with ⟨hleftFields, hleftErrors⟩
    rcases hmiddle with ⟨hmiddleFields, hmiddleErrors⟩
    exact ⟨
      hleftFields.trans hmiddleFields,
      ErrorPresenceEquivalent.trans hleftErrors hmiddleErrors
    ⟩

theorem RootSelectionResultDataAndErrorPresenceEquivalent.trans
    {left middle right : Result (List (Name × ResponseValue))}
    : RootSelectionResultDataAndErrorPresenceEquivalent left middle
      -> RootSelectionResultDataAndErrorPresenceEquivalent middle right
      -> RootSelectionResultDataAndErrorPresenceEquivalent left right := by
  intro hleft hmiddle
  exact ⟨hleft.1.trans hmiddle.1, ErrorPresenceEquivalent.trans hleft.2 hmiddle.2⟩

def PairKeysNodup {α : Type} (fields : List (Name × α)) : Prop :=
  (fields.map Prod.fst).Nodup

theorem PairKeysNodup.tail {α : Type} {head : Name × α} {rest : List (Name × α)}
    : PairKeysNodup (head :: rest) -> PairKeysNodup rest := by
  intro hnodup
  rcases head with ⟨_, _⟩
  unfold PairKeysNodup at hnodup ⊢
  exact (List.nodup_cons.mp hnodup).2

def ExecutableFieldsFieldValidationMergeCompatible (fields : List ExecutableField)
    : Prop :=
  ∀ first later,
    first ∈ fields
    -> later ∈ fields
    -> first.fieldName = later.fieldName
        ∧ Argument.argumentsEquivalent first.arguments later.arguments

def ScopedFieldRuntimeApplies
    (schema : Schema) (runtimeType : Name)
    (field : FieldMerge.ScopedField)
    : Prop :=
  schema.typeIncludesObjectBool field.parentType runtimeType = true

def ScopedParentRuntimeApplies (schema : Schema) (runtimeType parentType : Name) : Prop :=
  schema.typeIncludesObjectBool parentType runtimeType = true

theorem ScopedFieldRuntimeApplies.mergeIdentityCondition
    (schema : Schema) (runtimeType : Name)
    (first later : FieldMerge.ScopedField)
    : ScopedFieldRuntimeApplies schema runtimeType first
      -> ScopedFieldRuntimeApplies schema runtimeType later
      -> first.parentType = later.parentType
          ∨ ¬ schema.objectType first.parentType
          ∨ ¬ schema.objectType later.parentType := by
  intro hfirst hlater
  by_cases hfirstObject : schema.objectType first.parentType
  · by_cases hlaterObject : schema.objectType later.parentType
    · have hfirstRuntime :
          runtimeType = first.parentType :=
        object_typeIncludesObjectBool_eq_self schema hfirstObject
          hfirst
      have hlaterRuntime :
          runtimeType = later.parentType :=
        object_typeIncludesObjectBool_eq_self schema hlaterObject
          hlater
      exact Or.inl (hfirstRuntime.symm.trans hlaterRuntime)
    · exact Or.inr (Or.inr hlaterObject)
  · exact Or.inr (Or.inl hfirstObject)

def ScopedFieldMatchesExecutable
    (parentType : Name)
    (scopedField : FieldMerge.ScopedField)
    (executableField : ExecutableField)
    : Prop :=
  scopedField.parentType = parentType
  ∧ scopedField.fieldName = executableField.fieldName
  ∧ scopedField.arguments = executableField.arguments
  ∧ scopedField.selectionSet = executableField.selectionSet

def ScopedFieldMatchesExecutableIdentity
    (scopedField : FieldMerge.ScopedField)
    (executableField : ExecutableField)
    : Prop :=
  scopedField.fieldName = executableField.fieldName
  ∧ scopedField.arguments = executableField.arguments
  ∧ scopedField.selectionSet = executableField.selectionSet

def ExecutableFieldsScopedBy
    (parentType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields
    -> ∃ scopedField,
        scopedField ∈ scopedFields
        ∧ ScopedFieldMatchesExecutable parentType scopedField field

def ExecutableFieldsIdentityScopedBy
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : Prop :=
  ∀ field,
    field ∈ fields
    -> ∃ scopedField,
        scopedField ∈ scopedFields
        ∧ ScopedFieldMatchesExecutableIdentity scopedField field

theorem ScopedFieldMatchesExecutable.identity
    {parentType : Name}
    {scopedField : FieldMerge.ScopedField}
    {executableField : ExecutableField}
    : ScopedFieldMatchesExecutable parentType scopedField executableField
      -> ScopedFieldMatchesExecutableIdentity scopedField executableField := by
  intro hmatch
  exact hmatch.2

theorem ExecutableFieldsScopedBy.identity
    (parentType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : ExecutableFieldsScopedBy parentType scopedFields fields
      -> ExecutableFieldsIdentityScopedBy scopedFields fields := by
  intro hscoped field hfield
  rcases hscoped field hfield with
    ⟨scopedField, hscopedMem, hmatch⟩
  exact ⟨scopedField, hscopedMem,
    ScopedFieldMatchesExecutable.identity (parentType := parentType) hmatch⟩

def ExecutableFieldsResolveStable
    {ObjectIdentity : Type} (schema : Schema)
    (resolvers : Resolvers ObjectIdentity) (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity) (fields : List ExecutableField)
    : Prop :=
  ∀ parentType first later,
    first ∈ fields
    -> later ∈ fields
    -> resolveFieldValueByName schema resolvers variableValues parentType
          first.fieldName first.arguments source
        = resolveFieldValueByName schema resolvers variableValues parentType
            later.fieldName later.arguments source

theorem ExecutableFieldsResolveStable.tail
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (fields : List ExecutableField)
    : ExecutableFieldsResolveStable schema resolvers variableValues source
        (field :: fields)
      -> ExecutableFieldsResolveStable schema resolvers variableValues source fields := by
  intro hstable parentType first later hfirst hlater
  exact hstable parentType first later (by simp [hfirst]) (by simp [hlater])

def CollectedGroupsFieldsNonempty (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields, (responseName, fields) ∈ groups -> fields ≠ []

theorem CollectedGroupsFieldsNonempty_nil : CollectedGroupsFieldsNonempty [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsFieldsNonempty_singleton
    (responseName : Name) (fields : List ExecutableField)
    : fields ≠ [] -> CollectedGroupsFieldsNonempty [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hgroup :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hgroup
  exact hfields

theorem CollectedGroupsFieldsNonempty_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    : CollectedGroupsFieldsNonempty (group :: groups)
      -> CollectedGroupsFieldsNonempty groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsFieldsNonempty_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : group.snd ≠ []
      -> CollectedGroupsFieldsNonempty groups
      -> CollectedGroupsFieldsNonempty
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      simpa [GraphQL.Execution.addExecutableGroup]
        using CollectedGroupsFieldsNonempty_singleton groupName groupFields hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have hcurrentNonempty : currentFields ≠ [] :=
          hgroups currentName currentFields (by simp)
        have happendNonempty : currentFields ++ groupFields ≠ [] := by
          cases currentFields with
          | nil => exact False.elim (hcurrentNonempty rfl)
          | cons _ _ => simp
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · have hfields :
              fields = currentFields ++ groupFields := by
            simpa using hhead.2
          subst fields
          exact happendNonempty
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · have hfields : fields = currentFields := by
            simpa using hhead.2
          subst fields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsFieldsNonempty_tail hgroups)
            responseName fields htail

theorem CollectedGroupsFieldsNonempty_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : CollectedGroupsFieldsNonempty left
      -> CollectedGroupsFieldsNonempty right
      -> CollectedGroupsFieldsNonempty
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      exact ih (GraphQL.Execution.addExecutableGroup group left)
        (CollectedGroupsFieldsNonempty_addExecutableGroup group left
          (hright group.fst group.snd (by simp)) hleft)
        (CollectedGroupsFieldsNonempty_tail hright)

mutual
  theorem collectSelection_fieldsNonempty
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selection : Selection)
      : CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsFieldsNonempty_singleton responseName
            [{ fieldName := fieldName
               arguments := arguments
               selectionSet := selectionSet }]
            (by simp)
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsFieldsNonempty_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_fieldsNonempty schema variableValues
                parentType source selectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsFieldsNonempty_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_fieldsNonempty schema variableValues
                  parentType source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsFieldsNonempty_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsFieldsNonempty_nil]

  theorem collectFields_fieldsNonempty
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields,
          CollectedGroupsFieldsNonempty_nil]
    | cons selection rest =>
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsFieldsNonempty_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues parentType
            source selection)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
          (collectSelection_fieldsNonempty schema variableValues parentType
            source selection)
          (collectFields_fieldsNonempty schema variableValues parentType source
            rest)
end

def CollectedGroupsFieldValidationMergeCompatible
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ExecutableFieldsFieldValidationMergeCompatible fields

end GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
