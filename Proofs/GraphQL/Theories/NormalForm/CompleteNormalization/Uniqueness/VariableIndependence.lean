import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.StemExecution
import Proofs.GraphQL.Execution.ArgumentCoercion

/-!
Variable-environment independence for directive-free execution.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

def executableFieldListDirectiveFree (fields : List Execution.ExecutableField) : Prop :=
  ∀ field, field ∈ fields -> selectionSetDirectiveFree field.selectionSet

def executableGroupsDirectiveFree (groups : List (Name × List Execution.ExecutableField))
    : Prop :=
  ∀ group, group ∈ groups -> executableFieldListDirectiveFree group.2

theorem resolveFieldValue_eq_of_argumentCoercionEquivalent
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.argumentCoercionEquivalent schema leftValues rightValues)
    (fieldDefinition : FieldDefinition)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : Execution.ResolverValue ObjectRef)
    : Execution.resolveFieldValue schema resolvers leftValues fieldDefinition
        parentType fieldName arguments source
      = Execution.resolveFieldValue schema resolvers rightValues fieldDefinition
          parentType fieldName arguments source := by
  exact resolvers.resolve_argumentsEquivalent parentType fieldName
    _ _ source (hequivalent fieldDefinition.arguments arguments)

theorem executableFieldListDirectiveFree_append
    {left right : List Execution.ExecutableField}
    : executableFieldListDirectiveFree left
      -> executableFieldListDirectiveFree right
      -> executableFieldListDirectiveFree (left ++ right) := by
  intro hleft hright field hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hleft field hmem
  · exact hright field hmem

theorem executableGroupsDirectiveFree_addExecutableGroup
    {group : Name × List Execution.ExecutableField}
    {groups : List (Name × List Execution.ExecutableField)}
    : executableFieldListDirectiveFree group.2
      -> executableGroupsDirectiveFree groups
      -> executableGroupsDirectiveFree (Execution.addExecutableGroup group groups) := by
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro candidate hmem
      simp [Execution.addExecutableGroup] at hmem
      subst candidate
      exact hgroup
  | cons head rest ih =>
      rcases head with ⟨responseName, fields⟩
      cases hsame : responseName == group.fst
      · intro candidate hmem
        simp [Execution.addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | hrest
        · subst candidate
          exact hgroups (responseName, fields) (by simp)
        · exact ih (by
            intro restGroup hrestMem
            exact hgroups restGroup (by simp [hrestMem])) candidate hrest
      · intro candidate hmem
        simp [Execution.addExecutableGroup, hsame] at hmem
        rcases hmem with hhead | hrest
        · subst candidate
          exact executableFieldListDirectiveFree_append
            (hgroups (responseName, fields) (by simp)) hgroup
        · exact hgroups candidate (by simp [hrest])

theorem executableGroupsDirectiveFree_mergeExecutableGroups
    {left right : List (Name × List Execution.ExecutableField)}
    : executableGroupsDirectiveFree left
      -> executableGroupsDirectiveFree right
      -> executableGroupsDirectiveFree (Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  unfold Execution.mergeExecutableGroups
  induction right generalizing left with
  | nil => simpa using hleft
  | cons group rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact executableGroupsDirectiveFree_addExecutableGroup
          (hright group (by simp)) hleft
      · intro candidate hmem
        exact hright candidate (by simp [hmem])

mutual
  theorem collectSelection_eq_of_directiveFree
      (schema : Schema) (leftValues rightValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.ResolverValue ObjectRef)
      : ∀ selection,
          selectionDirectiveFree selection
          -> Execution.collectSelection schema leftValues parentType source selection
              = Execution.collectSelection schema rightValues parentType source selection
    | .field responseName fieldName arguments directives selectionSet, hfree => by
        rcases hfree with ⟨hdirectives, _hchildren⟩
        subst directives
        simp [Execution.collectSelection,
          Execution.selectionDirectivesAllowBool]
    | .inlineFragment none directives selectionSet, hfree => by
        rcases hfree with ⟨hdirectives, hchildren⟩
        subst directives
        simp only [Execution.collectSelection,
          Execution.selectionDirectivesAllowBool, List.all_nil, if_true]
        exact collectFields_eq_of_directiveFree schema leftValues rightValues
          parentType source selectionSet hchildren
    | .inlineFragment (some typeCondition) directives selectionSet, hfree => by
        rcases hfree with ⟨hdirectives, hchildren⟩
        subst directives
        simp only [Execution.collectSelection,
          Execution.selectionDirectivesAllowBool, List.all_nil, if_true]
        cases htype : Execution.doesFragmentTypeApplyBool schema parentType
            source typeCondition
        · simp
        · simp only [if_true]
          exact collectFields_eq_of_directiveFree schema leftValues rightValues
            parentType source selectionSet hchildren

  theorem collectFields_eq_of_directiveFree
      (schema : Schema) (leftValues rightValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.ResolverValue ObjectRef)
      : ∀ selectionSet,
          selectionSetDirectiveFree selectionSet
          -> Execution.collectFields schema leftValues parentType source selectionSet
              = Execution.collectFields schema rightValues parentType source selectionSet
    | [], _hfree => rfl
    | selection :: rest, hfree => by
        rw [Execution.collectFields, Execution.collectFields]
        rw [collectSelection_eq_of_directiveFree schema leftValues rightValues
          parentType source selection hfree.1]
        rw [collectFields_eq_of_directiveFree schema leftValues rightValues
          parentType source rest hfree.2]
end

mutual
  theorem collectSelection_executableGroupsDirectiveFree
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.ResolverValue ObjectRef)
      : ∀ selection,
          selectionDirectiveFree selection
          -> executableGroupsDirectiveFree
              (Execution.collectSelection schema variableValues parentType source
                selection)
    | .field responseName fieldName arguments directives selectionSet, hfree => by
        rcases hfree with ⟨hdirectives, hchildren⟩
        subst directives
        intro group hgroup field hfield
        simp [Execution.collectSelection,
          Execution.selectionDirectivesAllowBool] at hgroup
        subst group
        simp at hfield
        subst field
        exact hchildren
    | .inlineFragment none directives selectionSet, hfree => by
        rcases hfree with ⟨hdirectives, hchildren⟩
        subst directives
        simpa [Execution.collectSelection,
          Execution.selectionDirectivesAllowBool] using
          collectFields_executableGroupsDirectiveFree schema variableValues
            parentType source selectionSet hchildren
    | .inlineFragment (some typeCondition) directives selectionSet, hfree => by
        rcases hfree with ⟨hdirectives, hchildren⟩
        subst directives
        simp only [Execution.collectSelection,
          Execution.selectionDirectivesAllowBool, List.all_nil, if_true]
        cases htype : Execution.doesFragmentTypeApplyBool schema parentType
            source typeCondition
        · simp [executableGroupsDirectiveFree]
        · simpa using
            collectFields_executableGroupsDirectiveFree schema variableValues
              parentType source selectionSet hchildren

  theorem collectFields_executableGroupsDirectiveFree
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name) (source : Execution.ResolverValue ObjectRef)
      : ∀ selectionSet,
          selectionSetDirectiveFree selectionSet
          -> executableGroupsDirectiveFree
              (Execution.collectFields schema variableValues parentType source
                selectionSet)
    | [], _hfree => by
        simp [Execution.collectFields, executableGroupsDirectiveFree]
    | selection :: rest, hfree => by
        rw [Execution.collectFields]
        exact executableGroupsDirectiveFree_mergeExecutableGroups
          (collectSelection_executableGroupsDirectiveFree schema variableValues
            parentType source selection hfree.1)
          (collectFields_executableGroupsDirectiveFree schema variableValues
            parentType source rest hfree.2)
end

theorem collectSubfields_eq_of_directiveFree
    (schema : Schema) (leftValues rightValues : Execution.VariableValues)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    : ∀ fields : List Execution.ExecutableField,
        executableFieldListDirectiveFree fields
        -> Execution.collectSubfields schema leftValues objectType objectValue fields
            = Execution.collectSubfields schema rightValues objectType objectValue fields
  | [], _hfree => rfl
  | field :: rest, hfree => by
      rw [Execution.collectSubfields, Execution.collectSubfields]
      rw [collectFields_eq_of_directiveFree schema leftValues rightValues
        objectType objectValue field.selectionSet (hfree field (by simp))]
      rw [collectSubfields_eq_of_directiveFree schema leftValues rightValues
        objectType objectValue rest (by
          intro candidate hmem
          exact hfree candidate (by simp [hmem]))]

theorem collectSubfields_executableGroupsDirectiveFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    : ∀ fields : List Execution.ExecutableField,
        executableFieldListDirectiveFree fields
        -> executableGroupsDirectiveFree
            (Execution.collectSubfields schema variableValues objectType objectValue
              fields)
  | [], _hfree => by
      simp [Execution.collectSubfields, executableGroupsDirectiveFree]
  | field :: rest, hfree => by
      rw [Execution.collectSubfields]
      exact executableGroupsDirectiveFree_mergeExecutableGroups
        (collectFields_executableGroupsDirectiveFree schema variableValues
          objectType objectValue field.selectionSet (hfree field (by simp)))
        (collectSubfields_executableGroupsDirectiveFree schema variableValues
          objectType objectValue rest (by
            intro candidate hmem
            exact hfree candidate (by simp [hmem])))

def executionVariableValuesIndependentAtFuel
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (leftValues rightValues : Execution.VariableValues) (fuel : Nat)
    : Prop :=
  (∀ source groups,
    executableGroupsDirectiveFree groups
    -> Execution.executeCollectedFields schema resolvers leftValues fuel source groups
        = Execution.executeCollectedFields schema resolvers rightValues fuel source
            groups)
  ∧ (∀ fieldType fields value,
      executableFieldListDirectiveFree fields
      -> Execution.completeValue schema resolvers leftValues fuel fieldType fields value
          = Execution.completeValue schema resolvers rightValues fuel fieldType fields
              value)
  ∧ (∀ itemType fields values,
      executableFieldListDirectiveFree fields
      -> Execution.completeValueList schema resolvers leftValues fuel itemType
            fields values
          = Execution.completeValueList schema resolvers rightValues fuel itemType
              fields values)

theorem executionVariableValuesIndependentAtFuel_all
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (leftValues rightValues : Execution.VariableValues)
    (hresolve
      : ∀ fieldDefinition parentType fieldName arguments source,
          Execution.resolveFieldValue schema resolvers leftValues fieldDefinition
            parentType fieldName arguments source
          = Execution.resolveFieldValue schema resolvers rightValues fieldDefinition
              parentType fieldName arguments source)
    : ∀ fuel,
        executionVariableValuesIndependentAtFuel schema resolvers leftValues
          rightValues fuel := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro source groups hfree
        induction groups with
        | nil => simp [Execution.executeCollectedFields]
        | cons group rest ih =>
            rcases group with ⟨responseName, fields⟩
            have hrestFree : executableGroupsDirectiveFree rest := by
              intro candidate hmem
              exact hfree candidate (by simp [hmem])
            cases fields with
            | nil =>
                simp [Execution.executeCollectedFields,
                  Execution.executeField, ih hrestFree]
            | cons field fields =>
                simp [Execution.executeCollectedFields,
                  Execution.executeField, Execution.outOfFuel,
                  ih hrestFree]
      · intro fieldType fields value _hfree
        simp [Execution.completeValue]
      · intro itemType fields values hfree
        induction values with
        | nil => simp [Execution.completeValueList]
        | cons value rest ih =>
            simp [Execution.completeValueList, Execution.completeValue,
              Execution.outOfFuel, ih]
  | succ fuel ih =>
      rcases ih with ⟨hexecute, hcomplete, hcompleteList⟩
      have hcompleteCurrent : ∀ fieldType fields value,
          executableFieldListDirectiveFree fields ->
            Execution.completeValue schema resolvers leftValues (fuel + 1)
                fieldType fields value
              =
            Execution.completeValue schema resolvers rightValues (fuel + 1)
                fieldType fields value := by
        intro fieldType
        induction fieldType with
        | named typeName =>
            intro fields value hfieldsFree
            cases value with
            | null => simp [Execution.completeValue]
            | scalar scalarValue => simp [Execution.completeValue]
            | list values => simp [Execution.completeValue]
            | object runtimeType ref =>
                simp only [Execution.completeValue]
                cases hinclude :
                    schema.typeIncludesObjectBool typeName runtimeType
                · simp
                · simp only [if_true]
                  let source : Execution.ResolverValue ObjectRef :=
                    .object runtimeType ref
                  have hcollect :
                      Execution.collectSubfields schema leftValues runtimeType
                          source fields
                        =
                      Execution.collectSubfields schema rightValues runtimeType
                          source fields :=
                    collectSubfields_eq_of_directiveFree schema leftValues
                      rightValues runtimeType source fields hfieldsFree
                  have hgroupsFree :
                      executableGroupsDirectiveFree
                        (Execution.collectSubfields schema leftValues runtimeType
                          source fields) :=
                    collectSubfields_executableGroupsDirectiveFree schema
                      leftValues runtimeType source fields hfieldsFree
                  change Execution.catchBubbleAsNull
                      Execution.ResponseValue.object
                        (Execution.executeCollectedFields schema resolvers
                          leftValues fuel source
                          (Execution.collectSubfields schema leftValues
                            runtimeType source fields))
                    =
                    Execution.catchBubbleAsNull Execution.ResponseValue.object
                      (Execution.executeCollectedFields schema resolvers
                        rightValues fuel source
                        (Execution.collectSubfields schema rightValues
                          runtimeType source fields))
                  rw [← hcollect]
                  rw [hexecute source _ hgroupsFree]
        | list inner =>
            intro fields value hfieldsFree
            cases value with
            | null => simp [Execution.completeValue]
            | scalar scalarValue => simp [Execution.completeValue]
            | object runtimeType ref => simp [Execution.completeValue]
            | list values =>
                simp only [Execution.completeValue]
                rw [hcompleteList inner fields values hfieldsFree]
        | nonNull inner ihType =>
            intro fields value hfieldsFree
            simp only [Execution.completeValue]
            rw [ihType fields value hfieldsFree]
      have hcompleteListCurrent : ∀ itemType fields values,
          executableFieldListDirectiveFree fields ->
            Execution.completeValueList schema resolvers leftValues (fuel + 1)
                itemType fields values
              =
            Execution.completeValueList schema resolvers rightValues (fuel + 1)
                itemType fields values := by
        intro itemType fields values hfieldsFree
        induction values with
        | nil => simp [Execution.completeValueList]
        | cons value rest ihValues =>
            simp only [Execution.completeValueList]
            rw [hcompleteCurrent itemType fields value hfieldsFree]
            rw [ihValues]
      have hexecuteCurrent : ∀ source groups,
          executableGroupsDirectiveFree groups ->
            Execution.executeCollectedFields schema resolvers leftValues
                (fuel + 1) source groups
              =
            Execution.executeCollectedFields schema resolvers rightValues
                (fuel + 1) source groups := by
        intro source groups hgroupsFree
        induction groups with
        | nil => simp [Execution.executeCollectedFields]
        | cons group rest ihGroups =>
            rcases group with ⟨responseName, fields⟩
            have hfieldsFree :=
              hgroupsFree (responseName, fields) (by simp)
            have hrestFree : executableGroupsDirectiveFree rest := by
              intro candidate hmem
              exact hgroupsFree candidate (by simp [hmem])
            have hfield :
                Execution.executeField schema resolvers leftValues (fuel + 1)
                    source responseName fields
                  =
                Execution.executeField schema resolvers rightValues (fuel + 1)
                    source responseName fields := by
              cases fields with
              | nil => simp [Execution.executeField]
              | cons field restFields =>
                  simp only [Execution.executeField]
                  cases hlookup :
                      schema.lookupField field.parentType field.fieldName
                  · simp
                  · rename_i fieldDefinition
                    simp only
                    rw [hresolve fieldDefinition field.parentType field.fieldName
                      field.arguments source]
                    cases hresolved : Execution.resolveFieldValue schema resolvers
                        rightValues fieldDefinition field.parentType field.fieldName
                        field.arguments source
                    · simp
                    · rename_i resolved
                      simp only
                      rw [hcomplete fieldDefinition.outputType
                        (field :: restFields) resolved hfieldsFree]
            simp only [Execution.executeCollectedFields]
            rw [hfield]
            rw [ihGroups hrestFree]
      exact ⟨hexecuteCurrent, hcompleteCurrent, hcompleteListCurrent⟩

theorem executeSelectionSet_eq_of_directiveFree_variableValues
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (leftValues rightValues : Execution.VariableValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : (∀ fieldDefinition callParentType fieldName arguments callSource,
        Execution.resolveFieldValue schema resolvers leftValues fieldDefinition
          callParentType fieldName arguments callSource
        = Execution.resolveFieldValue schema resolvers rightValues fieldDefinition
            callParentType fieldName arguments callSource)
      -> selectionSetDirectiveFree selectionSet
      -> Execution.executeSelectionSet schema resolvers leftValues fuel parentType
            source selectionSet
          = Execution.executeSelectionSet schema resolvers rightValues fuel parentType
              source selectionSet := by
  intro hresolve hfree
  have hcollect := collectFields_eq_of_directiveFree schema leftValues
    rightValues parentType source selectionSet hfree
  have hgroupsFree := collectFields_executableGroupsDirectiveFree schema
    leftValues parentType source selectionSet hfree
  have hexecute :=
    (executionVariableValuesIndependentAtFuel_all schema resolvers leftValues
      rightValues hresolve fuel).1 source
      (Execution.collectFields schema leftValues parentType source selectionSet)
      hgroupsFree
  simp only [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
  rw [← hcollect]
  exact hexecute

private theorem inputValue_staticBoolean?_eq_of_equivalent
    {left right : InputValue} (hequivalent : left.equivalent right)
    : left.staticBoolean? = right.staticBoolean? := by
  have hcanonical :=
    Execution.inputValue_canonical_eq_of_equivalent hequivalent
  cases left <;> cases right <;>
    simp [InputValue.staticBoolean?, InputValue.canonical] at hcanonical ⊢
  exact hcanonical

theorem inputValueBoolean?_eq_of_variableValuesCoercionEquivalent
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    (value : InputValue)
    : Execution.inputValueBoolean? leftValues value
      = Execution.inputValueBoolean? rightValues value := by
  cases value <;> try rfl
  rename_i name
  have hlookup := hequivalent.1 name
  cases hleft : Execution.lookupVariableValue? leftValues name with
  | none =>
      cases hright : Execution.lookupVariableValue? rightValues name with
      | none => simp [Execution.inputValueBoolean?, hleft, hright]
      | some right => simp [hleft, hright] at hlookup
  | some left =>
      cases hright : Execution.lookupVariableValue? rightValues name with
      | none => simp [hleft, hright] at hlookup
      | some right =>
          simp [hleft, hright] at hlookup
          simpa [Execution.inputValueBoolean?, hleft, hright] using
            inputValue_staticBoolean?_eq_of_equivalent hlookup

theorem directiveAllowsSelectionBool_eq_of_variableValuesCoercionEquivalent
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    (directive : DirectiveApplication)
    : Execution.directiveAllowsSelectionBool leftValues directive
      = Execution.directiveAllowsSelectionBool rightValues directive := by
  cases directive <;>
    simp only [Execution.directiveAllowsSelectionBool,
      inputValueBoolean?_eq_of_variableValuesCoercionEquivalent hequivalent]

theorem selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    : ∀ directives,
        Execution.selectionDirectivesAllowBool leftValues directives
        = Execution.selectionDirectivesAllowBool rightValues directives
  | [] => rfl
  | directive :: rest => by
      simp only [Execution.selectionDirectivesAllowBool, List.all_cons]
      rw [directiveAllowsSelectionBool_eq_of_variableValuesCoercionEquivalent
        hequivalent directive]
      change (Execution.directiveAllowsSelectionBool rightValues directive &&
          Execution.selectionDirectivesAllowBool leftValues rest) =
        (Execution.directiveAllowsSelectionBool rightValues directive &&
          Execution.selectionDirectivesAllowBool rightValues rest)
      rw [selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent
        hequivalent rest]

mutual
  theorem collectSelection_eq_of_variableValuesCoercionEquivalent
      (schema : Schema) {leftValues rightValues : Execution.VariableValues}
      (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
      (parentType : Name) (source : Execution.ResolverValue ObjectRef)
      : ∀ selection,
          Execution.collectSelection schema leftValues parentType source selection
          = Execution.collectSelection schema rightValues parentType source selection
    | .field responseName fieldName arguments directives selectionSet => by
        simp only [Execution.collectSelection]
        rw [selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent
          hequivalent directives]
    | .inlineFragment none directives selectionSet => by
        simp only [Execution.collectSelection]
        rw [selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent
          hequivalent directives]
        split <;> rename_i hallowed
        · exact collectFields_eq_of_variableValuesCoercionEquivalent schema
            hequivalent parentType source selectionSet
        · rfl
    | .inlineFragment (some typeCondition) directives selectionSet => by
        simp only [Execution.collectSelection]
        rw [selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent
          hequivalent directives]
        split <;> rename_i hallowed
        · split <;> rename_i happlies
          · exact collectFields_eq_of_variableValuesCoercionEquivalent schema
              hequivalent parentType source selectionSet
          · rfl
        · rfl

  theorem collectFields_eq_of_variableValuesCoercionEquivalent
      (schema : Schema) {leftValues rightValues : Execution.VariableValues}
      (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
      (parentType : Name) (source : Execution.ResolverValue ObjectRef)
      : ∀ selectionSet,
          Execution.collectFields schema leftValues parentType source selectionSet
          = Execution.collectFields schema rightValues parentType source selectionSet
    | [] => rfl
    | selection :: rest => by
        rw [Execution.collectFields, Execution.collectFields]
        rw [collectSelection_eq_of_variableValuesCoercionEquivalent schema
          hequivalent parentType source selection]
        rw [collectFields_eq_of_variableValuesCoercionEquivalent schema
          hequivalent parentType source rest]
end

theorem collectSubfields_eq_of_variableValuesCoercionEquivalent
    (schema : Schema) {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    (objectType : Name) (objectValue : Execution.ResolverValue ObjectRef)
    : ∀ fields : List Execution.ExecutableField,
        Execution.collectSubfields schema leftValues objectType objectValue fields
        = Execution.collectSubfields schema rightValues objectType objectValue fields
  | [] => rfl
  | field :: rest => by
      rw [Execution.collectSubfields, Execution.collectSubfields]
      rw [collectFields_eq_of_variableValuesCoercionEquivalent schema hequivalent
        objectType objectValue field.selectionSet]
      rw [collectSubfields_eq_of_variableValuesCoercionEquivalent schema hequivalent
        objectType objectValue rest]

def executionVariableValuesEquivalentAtFuel
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (leftValues rightValues : Execution.VariableValues) (fuel : Nat)
    : Prop :=
  (∀ source groups,
    Execution.executeCollectedFields schema resolvers leftValues fuel source groups
    = Execution.executeCollectedFields schema resolvers rightValues fuel source groups)
  ∧ (∀ fieldType fields value,
      Execution.completeValue schema resolvers leftValues fuel fieldType fields value
      = Execution.completeValue schema resolvers rightValues fuel fieldType fields value)
  ∧ ∀ itemType fields values,
      Execution.completeValueList schema resolvers leftValues fuel itemType fields values
      = Execution.completeValueList schema resolvers rightValues fuel itemType fields
          values

theorem executionVariableValuesEquivalentAtFuel_all
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    : ∀ fuel,
        executionVariableValuesEquivalentAtFuel schema resolvers leftValues
          rightValues fuel := by
  intro fuel
  have hresolve : ∀ fieldDefinition parentType fieldName arguments source,
      Execution.resolveFieldValue schema resolvers leftValues fieldDefinition
          parentType fieldName arguments source =
        Execution.resolveFieldValue schema resolvers rightValues fieldDefinition
          parentType fieldName arguments source :=
    fun fieldDefinition parentType fieldName arguments source =>
      resolveFieldValue_eq_of_argumentCoercionEquivalent schema resolvers
        (Execution.argumentCoercionEquivalent_of_variableValuesCoercionEquivalent
          schema hequivalent)
        fieldDefinition parentType fieldName arguments source
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro source groups
        induction groups with
        | nil => simp [Execution.executeCollectedFields]
        | cons group rest ih =>
            rcases group with ⟨responseName, fields⟩
            cases fields with
            | nil =>
                simp [Execution.executeCollectedFields,
                  Execution.executeField, ih]
            | cons field fields =>
                simp [Execution.executeCollectedFields,
                  Execution.executeField, Execution.outOfFuel, ih]
      · intro fieldType fields value
        simp [Execution.completeValue]
      · intro itemType fields values
        induction values with
        | nil => simp [Execution.completeValueList]
        | cons value rest ih =>
            simp [Execution.completeValueList, Execution.completeValue,
              Execution.outOfFuel, ih]
  | succ fuel ih =>
      rcases ih with ⟨hexecute, hcomplete, hcompleteList⟩
      have hcompleteCurrent : ∀ fieldType fields value,
          Execution.completeValue schema resolvers leftValues (fuel + 1)
              fieldType fields value =
            Execution.completeValue schema resolvers rightValues (fuel + 1)
              fieldType fields value := by
        intro fieldType
        induction fieldType with
        | named typeName =>
            intro fields value
            cases value with
            | null => simp [Execution.completeValue]
            | scalar scalarValue => simp [Execution.completeValue]
            | list values => simp [Execution.completeValue]
            | object runtimeType ref =>
                simp only [Execution.completeValue]
                cases hinclude :
                    schema.typeIncludesObjectBool typeName runtimeType
                · simp
                · simp only [if_true]
                  let source : Execution.ResolverValue ObjectRef :=
                    .object runtimeType ref
                  have hcollect :=
                    collectSubfields_eq_of_variableValuesCoercionEquivalent
                      schema hequivalent runtimeType source fields
                  change Execution.catchBubbleAsNull
                      Execution.ResponseValue.object
                        (Execution.executeCollectedFields schema resolvers
                          leftValues fuel source
                          (Execution.collectSubfields schema leftValues
                            runtimeType source fields)) =
                    Execution.catchBubbleAsNull Execution.ResponseValue.object
                      (Execution.executeCollectedFields schema resolvers
                        rightValues fuel source
                        (Execution.collectSubfields schema rightValues
                          runtimeType source fields))
                  rw [← hcollect]
                  rw [hexecute source]
        | list inner =>
            intro fields value
            cases value with
            | null => simp [Execution.completeValue]
            | scalar scalarValue => simp [Execution.completeValue]
            | object runtimeType ref => simp [Execution.completeValue]
            | list values =>
                simp only [Execution.completeValue]
                rw [hcompleteList inner fields values]
        | nonNull inner ihType =>
            intro fields value
            simp only [Execution.completeValue]
            rw [ihType fields value]
      have hcompleteListCurrent : ∀ itemType fields values,
          Execution.completeValueList schema resolvers leftValues (fuel + 1)
              itemType fields values =
            Execution.completeValueList schema resolvers rightValues (fuel + 1)
              itemType fields values := by
        intro itemType fields values
        induction values with
        | nil => simp [Execution.completeValueList]
        | cons value rest ihValues =>
            simp only [Execution.completeValueList]
            rw [hcompleteCurrent itemType fields value]
            rw [ihValues]
      have hexecuteCurrent : ∀ source groups,
          Execution.executeCollectedFields schema resolvers leftValues
              (fuel + 1) source groups =
            Execution.executeCollectedFields schema resolvers rightValues
              (fuel + 1) source groups := by
        intro source groups
        induction groups with
        | nil => simp [Execution.executeCollectedFields]
        | cons group rest ihGroups =>
            rcases group with ⟨responseName, fields⟩
            have hfield :
                Execution.executeField schema resolvers leftValues (fuel + 1)
                    source responseName fields =
                  Execution.executeField schema resolvers rightValues (fuel + 1)
                    source responseName fields := by
              cases fields with
              | nil => simp [Execution.executeField]
              | cons field restFields =>
                  simp only [Execution.executeField]
                  cases hlookup :
                      schema.lookupField field.parentType field.fieldName
                  · simp
                  · rename_i fieldDefinition
                    simp only
                    rw [hresolve fieldDefinition field.parentType field.fieldName
                      field.arguments source]
                    cases hresolved : Execution.resolveFieldValue schema resolvers
                        rightValues fieldDefinition field.parentType field.fieldName
                        field.arguments source
                    · simp
                    · rename_i resolved
                      simp only
                      rw [hcomplete fieldDefinition.outputType
                        (field :: restFields) resolved]
            simp only [Execution.executeCollectedFields]
            rw [hfield]
            rw [ihGroups]
      exact ⟨hexecuteCurrent, hcompleteCurrent, hcompleteListCurrent⟩

theorem executeSelectionSet_eq_of_variableValuesCoercionEquivalent
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    (fuel : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.executeSelectionSet schema resolvers leftValues fuel parentType
        source selectionSet
      = Execution.executeSelectionSet schema resolvers rightValues fuel parentType
          source selectionSet := by
  have hcollect := collectFields_eq_of_variableValuesCoercionEquivalent schema
    hequivalent parentType source selectionSet
  have hexecute :=
    (executionVariableValuesEquivalentAtFuel_all schema resolvers hequivalent fuel).1
      source (Execution.collectFields schema leftValues parentType source selectionSet)
  simp only [Execution.executeSelectionSet, Execution.executeRootSelectionSet]
  rw [← hcollect]
  exact hexecute

end CompleteNormalization

end NormalForm

end GraphQL
