import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.StaticFieldGroups

/-!
Source static-collection field and inline-fragment execution cases.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem collectFields_staticCollectForGround_field_skipped_case
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = false
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent source rest
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.collectFields schema variableValues lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hskip hrest
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_field_head
      variableValues boolCase operation responseName fieldName arguments
      directives selectionSet rest hagrees hsourceVars
  have hexecSkip :
      Execution.selectionDirectivesAllowBool variableValues directives =
        false := by
    rw [← hdirectiveEq]
    exact hskip
  rw [staticCollectForGround_field_skipped schema
    (operationBoolVars operation) lookupParent groundType
    responseName fieldName boolCase arguments directives selectionSet rest
    hskip]
  rw [collectFields_field_directives_skipped_eq schema variableValues
    lookupParent source responseName fieldName arguments directives
    selectionSet rest hexecSkip]
  exact hrest

theorem collectFields_staticCollectForGround_inline_none_skipped_case
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment none directives selectionSet :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = false
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent source rest
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment none directives selectionSet :: rest))
          = Execution.collectFields schema variableValues lookupParent source
              (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hagrees hsourceVars hskip hrest
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation none directives selectionSet rest
      hagrees hsourceVars
  have hexecSkip :
      Execution.selectionDirectivesAllowBool variableValues directives =
        false := by
    rw [← hdirectiveEq]
    exact hskip
  rw [staticCollectForGround_inline_none_skipped schema
    (operationBoolVars operation) lookupParent groundType
    boolCase directives selectionSet rest hskip]
  rw [collectFields_inlineFragment_none_directives_skipped_eq schema
    variableValues lookupParent source directives selectionSet rest hexecSkip]
  exact hrest

theorem collectFields_staticCollectForGround_inline_none_allowed_case
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment none directives selectionSet :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase selectionSet)
          = Execution.collectFields schema variableValues lookupParent source selectionSet
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent source rest
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment none directives selectionSet :: rest))
          = Execution.collectFields schema variableValues lookupParent source
              (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hagrees hsourceVars hallow hselection hrest
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation none directives selectionSet rest
      hagrees hsourceVars
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  rw [staticCollectForGround_inline_none_allowed schema
    (operationBoolVars operation) lookupParent groundType
    boolCase directives selectionSet rest hallow]
  rw [collectFields_append]
  rw [hselection, hrest]
  rw [collectFields_inlineFragment_none_directives_allowed_flatten schema
    variableValues lookupParent source directives selectionSet rest
    hexecAllow]
  rw [collectFields_append]

theorem collectFields_staticCollectForGround_inline_some_skipped_case
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment (some typeCondition) directives selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> (directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType)
          = false
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              rest
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest))
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hskip hrest
  have hbranchEq :=
    inlineSomeBranchAllowInCase_eq_execution_of_inline_head schema
      variableValues boolCase operation groundType typeCondition directives
      selectionSet rest hagrees hsourceVars
  have hexecSkip :
      (Execution.selectionDirectivesAllowBool variableValues directives
        && schema.typeIncludesObjectBool typeCondition groundType) = false := by
    rw [← hbranchEq]
    exact hskip
  rw [staticCollectForGround_inline_some_skipped schema
    (operationBoolVars operation) lookupParent groundType
    typeCondition boolCase directives selectionSet rest hskip]
  rw [collectFields_inlineFragment_some_directives_skipped_eq_object schema
    variableValues lookupParent groundType typeCondition ref directives
    selectionSet rest hexecSkip]
  exact hrest

theorem collectFields_staticCollectForGround_inline_some_allowed_case
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment (some typeCondition) directives selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> schema.typeIncludesObjectBool typeCondition groundType = true
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) typeCondition
              groundType boolCase selectionSet)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              selectionSet
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              rest
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest))
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hallow hincludes hselection hrest
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation (some typeCondition) directives
      selectionSet rest hagrees hsourceVars
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  rw [staticCollectForGround_inline_some_allowed schema
    (operationBoolVars operation) lookupParent groundType
    typeCondition boolCase directives selectionSet rest hallow hincludes]
  rw [collectFields_append]
  rw [hselection, hrest]
  rw [collectFields_inlineFragment_some_directives_allowed_flatten_object
    schema variableValues lookupParent groundType typeCondition
      ref directives selectionSet rest hexecAllow hincludes]
  rw [collectFields_append]

theorem executeSelectionSet_staticCollectForGround_field_skipped_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = false
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent source rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
    intro hagrees hsourceVars hskip hrest
    apply executeSelectionSet_eq_of_collectFields_eq
    exact collectFields_staticCollectForGround_field_skipped_case
      schema variableValues operation lookupParent groundType source boolCase
      responseName fieldName arguments directives selectionSet rest hagrees
      hsourceVars hskip hrest

theorem executeSelectionSet_staticCollectForGround_field_skipped_execution_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hskip hrest
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_field_head
      variableValues boolCase operation responseName fieldName arguments
      directives selectionSet rest hagrees hsourceVars
  have hexecSkip :
      Execution.selectionDirectivesAllowBool variableValues directives =
        false := by
    rw [← hdirectiveEq]
    exact hskip
  rw [staticCollectForGround_field_skipped schema
    (operationBoolVars operation) lookupParent groundType
    responseName fieldName boolCase arguments directives selectionSet rest
    hskip]
  exact hrest.trans
    (executeSelectionSet_field_directives_skipped_eq schema resolvers
      variableValues depth lookupParent source responseName fieldName
      arguments directives selectionSet rest hexecSkip).symm

theorem executeSelectionSet_staticCollectForGround_inline_none_skipped_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment none directives selectionSet :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = false
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent source rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment none directives selectionSet :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.inlineFragment none directives selectionSet :: rest) := by
    intro hagrees hsourceVars hskip hrest
    apply executeSelectionSet_eq_of_collectFields_eq
    exact collectFields_staticCollectForGround_inline_none_skipped_case
      schema variableValues operation lookupParent groundType source boolCase
      directives selectionSet rest hagrees hsourceVars hskip hrest

theorem executeSelectionSet_staticCollectForGround_inline_none_skipped_execution_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment none directives selectionSet :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment none directives selectionSet :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hagrees hsourceVars hskip hrest
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation none directives selectionSet rest
      hagrees hsourceVars
  have hexecSkip :
      Execution.selectionDirectivesAllowBool variableValues directives =
        false := by
    rw [← hdirectiveEq]
    exact hskip
  rw [staticCollectForGround_inline_none_skipped schema
    (operationBoolVars operation) lookupParent groundType
    boolCase directives selectionSet rest hskip]
  exact hrest.trans
    (executeSelectionSet_inlineFragment_none_directives_skipped_eq schema
      resolvers variableValues depth lookupParent source directives
      selectionSet rest hexecSkip).symm

theorem executeSelectionSet_staticCollectForGround_inline_none_allowed_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment none directives selectionSet :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase selectionSet)
          = Execution.collectFields schema variableValues lookupParent source selectionSet
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent source rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment none directives selectionSet :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.inlineFragment none directives selectionSet :: rest) := by
    intro hagrees hsourceVars hallow hselection hrest
    apply executeSelectionSet_eq_of_collectFields_eq
    exact collectFields_staticCollectForGround_inline_none_allowed_case
      schema variableValues operation lookupParent groundType source boolCase
      directives selectionSet rest hagrees hsourceVars hallow hselection hrest

theorem executeSelectionSet_staticCollectForGround_inline_none_allowed_flatten_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment none directives selectionSet :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase (selectionSet ++ rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source (selectionSet ++ rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment none directives selectionSet :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hagrees hsourceVars hallow hflatten
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation none directives selectionSet rest
      hagrees hsourceVars
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  rw [staticCollectForGround_inline_none_allowed schema
    (operationBoolVars operation) lookupParent groundType
    boolCase directives selectionSet rest hallow]
  rw [← staticCollectForGround_append schema
    (operationBoolVars operation) lookupParent groundType
    boolCase selectionSet rest]
  exact hflatten.trans
    (executeSelectionSet_inlineFragment_none_directives_allowed_flatten schema
      resolvers variableValues depth lookupParent source directives
      selectionSet rest hexecAllow).symm

theorem executeSelectionSet_staticCollectForGround_inline_some_skipped_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment (some typeCondition) directives selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> (directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType)
          = false
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest) := by
    intro hagrees hsourceVars hskip hrest
    apply executeSelectionSet_eq_of_collectFields_eq
    simpa [] using
      collectFields_staticCollectForGround_inline_some_skipped_case
      schema variableValues operation lookupParent groundType typeCondition
        ref boolCase directives selectionSet rest hagrees hsourceVars hskip
      hrest

theorem executeSelectionSet_staticCollectForGround_inline_some_skipped_execution_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment (some typeCondition) directives selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> (directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType)
          = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hskip hrest
  have hbranchEq :=
    inlineSomeBranchAllowInCase_eq_execution_of_inline_head schema
      variableValues boolCase operation groundType typeCondition directives
      selectionSet rest hagrees hsourceVars
  have hexecSkip :
      (Execution.selectionDirectivesAllowBool variableValues directives
        && schema.typeIncludesObjectBool typeCondition groundType) = false := by
    rw [← hbranchEq]
    exact hskip
  rw [staticCollectForGround_inline_some_skipped schema
    (operationBoolVars operation) lookupParent groundType
    typeCondition boolCase directives selectionSet rest hskip]
  exact hrest.trans
    (executeSelectionSet_inlineFragment_some_directives_skipped_eq_object
      schema resolvers variableValues depth lookupParent groundType
      typeCondition ref directives selectionSet rest hexecSkip).symm

theorem executeSelectionSet_staticCollectForGround_inline_some_allowed_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment (some typeCondition) directives selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> schema.typeIncludesObjectBool typeCondition groundType = true
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) typeCondition
              groundType boolCase selectionSet)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              selectionSet
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase rest)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              rest
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest) := by
    intro hagrees hsourceVars hallow hincludes hselection hrest
    apply executeSelectionSet_eq_of_collectFields_eq
    simpa [] using
      collectFields_staticCollectForGround_inline_some_allowed_case
      schema variableValues operation lookupParent groundType typeCondition
        ref boolCase directives selectionSet rest hagrees hsourceVars
      hallow hincludes hselection hrest

theorem executeSelectionSet_staticCollectForGround_inline_some_allowed_flatten_case
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (depth : Nat)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (boolCase : BoolCase)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment (some typeCondition) directives selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> schema.typeIncludesObjectBool typeCondition groundType = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
                (operationBoolVars operation) typeCondition
                groundType boolCase selectionSet
              ++ staticCollectForGround schema
                  (operationBoolVars operation) lookupParent
                  groundType boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (selectionSet ++ rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (Selection.inlineFragment (some typeCondition) directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hallow hincludes hflatten
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation (some typeCondition) directives
      selectionSet rest hagrees hsourceVars
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  rw [staticCollectForGround_inline_some_allowed schema
    (operationBoolVars operation) lookupParent groundType
    typeCondition boolCase directives selectionSet rest hallow hincludes]
  exact hflatten.trans
    (executeSelectionSet_inlineFragment_some_directives_allowed_flatten_object
      schema resolvers variableValues depth lookupParent groundType
      typeCondition ref directives selectionSet rest hexecAllow
      hincludes).symm

end CompleteNormalization

end NormalForm

end GraphQL
