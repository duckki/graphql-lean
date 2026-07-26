import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FieldDirectiveExecution

/-!
Inline-fragment directive execution cases for complete normalization static collection.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem collectFields_inlineFragment_none_directives_allowed_flatten
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment none directives selectionSet :: rest)
          = Execution.collectFields schema variableValues parentType source
              (selectionSet ++ rest) := by
  intro hallow
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, hallow]
  rw [collectFields_append]

theorem collectFields_inlineFragment_none_directives_skipped_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = false
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment none directives selectionSet :: rest)
          = Execution.collectFields schema variableValues parentType source rest := by
  intro hskip
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, hskip]
  exact GroundTypeNormalization.mergeExecutableGroups_nil_left_collectFields_eq
    schema variableValues parentType source rest

theorem executeSelectionSet_inlineFragment_none_directives_allowed_flatten
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment none directives selectionSet :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source (selectionSet ++ rest) := by
  intro hallow
  apply executeSelectionSet_eq_of_collectFields_eq
  exact collectFields_inlineFragment_none_directives_allowed_flatten schema
    variableValues parentType source directives selectionSet rest hallow

theorem executeSelectionSet_inlineFragment_none_directives_skipped_eq
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment none directives selectionSet :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source rest := by
  intro hskip
  apply executeSelectionSet_eq_of_collectFields_eq
  exact collectFields_inlineFragment_none_directives_skipped_eq schema
    variableValues parentType source directives selectionSet rest hskip

theorem collectFields_inlineFragment_some_directives_allowed_flatten_object
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> schema.typeIncludesObjectBool typeCondition groundType = true
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (selectionSet ++ rest) := by
  intro hallow hincludes
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, hallow,
    Execution.doesFragmentTypeApplyBool, Execution.runtimeObjectType?,
    hincludes]
  rw [collectFields_append]

theorem collectFields_inlineFragment_some_directives_allowed_flatten
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (typeCondition : Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.collectFields schema variableValues parentType source
              (selectionSet ++ rest) := by
  intro hallow happly
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, hallow, happly]
  rw [collectFields_append]

theorem executeSelectionSet_inlineFragment_some_directives_allowed_flatten_object
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> schema.typeIncludesObjectBool typeCondition groundType = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (selectionSet ++ rest) := by
  intro hallow hincludes
  apply executeSelectionSet_eq_of_collectFields_eq
  simpa [] using
    collectFields_inlineFragment_some_directives_allowed_flatten_object
    schema variableValues lookupParent groundType typeCondition ref
    directives selectionSet rest hallow hincludes

theorem executeSelectionSet_inlineFragment_some_directives_allowed_flatten
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (typeCondition : Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : Execution.selectionDirectivesAllowBool variableValues directives = true
      -> Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source (selectionSet ++ rest) := by
  intro hallow happly
  apply executeSelectionSet_eq_of_collectFields_eq
  exact collectFields_inlineFragment_some_directives_allowed_flatten schema
    variableValues parentType source typeCondition directives selectionSet rest
    hallow happly

theorem collectFields_inlineFragment_some_directives_skipped_eq_object
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (Execution.selectionDirectivesAllowBool variableValues directives
          && schema.typeIncludesObjectBool typeCondition groundType)
        = false
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.collectFields schema variableValues lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              rest := by
  intro hskip
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection, Execution.doesFragmentTypeApplyBool,
    Execution.runtimeObjectType?]
  cases hallow :
      Execution.selectionDirectivesAllowBool variableValues directives
  · simp
    exact GroundTypeNormalization.mergeExecutableGroups_nil_left_collectFields_eq
      schema variableValues lookupParent
      (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) rest
  · have hincludes :
        schema.typeIncludesObjectBool typeCondition groundType = false := by
      simpa [hallow] using hskip
    simp [hincludes]
    exact GroundTypeNormalization.mergeExecutableGroups_nil_left_collectFields_eq
      schema variableValues lookupParent
      (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) rest

theorem collectFields_inlineFragment_some_directives_skipped_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (typeCondition : Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (Execution.selectionDirectivesAllowBool variableValues directives
          && Execution.doesFragmentTypeApplyBool schema parentType source typeCondition)
        = false
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.collectFields schema variableValues parentType source rest := by
  intro hskip
  rw [GroundTypeNormalization.collectFields_cons]
  simp [Execution.collectSelection]
  cases hallow :
      Execution.selectionDirectivesAllowBool variableValues directives
  · simp
    exact GroundTypeNormalization.mergeExecutableGroups_nil_left_collectFields_eq
      schema variableValues parentType source rest
  · have happly :
        Execution.doesFragmentTypeApplyBool schema parentType source
          typeCondition = false := by
      simpa [hallow] using hskip
    simp [happly]
    exact GroundTypeNormalization.mergeExecutableGroups_nil_left_collectFields_eq
      schema variableValues parentType source rest

theorem executeSelectionSet_inlineFragment_some_directives_skipped_eq_object
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (lookupParent groundType typeCondition : Name)
    (ref : ObjectRef)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (Execution.selectionDirectivesAllowBool variableValues directives
          && schema.typeIncludesObjectBool typeCondition groundType)
        = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              rest := by
  intro hskip
  apply executeSelectionSet_eq_of_collectFields_eq
  simpa [] using
    collectFields_inlineFragment_some_directives_skipped_eq_object schema
    variableValues lookupParent groundType typeCondition ref directives
    selectionSet rest hskip

theorem executeSelectionSet_inlineFragment_some_directives_skipped_eq
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (typeCondition : Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (Execution.selectionDirectivesAllowBool variableValues directives
          && Execution.doesFragmentTypeApplyBool schema parentType source typeCondition)
        = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) directives selectionSet
              :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source rest := by
  intro hskip
  apply executeSelectionSet_eq_of_collectFields_eq
  exact collectFields_inlineFragment_some_directives_skipped_eq schema
    variableValues parentType source typeCondition directives selectionSet rest
    hskip

end CompleteNormalization

end NormalForm

end GraphQL
