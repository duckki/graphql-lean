import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection.SingleFieldGroup

/-!
Executable-field and executable-group wrappers for single-field groups.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

theorem AppendAllowedFieldState.of_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendAllowedFieldState schema resolvers variableValues (depth + 1)
        parentType source left responseName fieldName arguments directives
        selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendAllowedFieldState.of_guarded_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendAllowedFieldState schema resolvers variableValues (depth + 1)
        parentType source left responseName fieldName arguments directives
        selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendAllowedFieldState.of_contained_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendAllowedFieldState schema resolvers variableValues (depth + 1)
        parentType source left responseName fieldName arguments directives
        selectionSet depth := by
  refine
    { depth_eq := rfl
      allowed := hallowed
      rightEquivalent := ?_
      namesDisjoint := hdisjoint }
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      [.field responseName fieldName arguments directives selectionSet]
      (executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments directives selectionSet resolved hallowed hresolve
        hchildren)

theorem AppendSelectionState.field_allowed_of_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendSelectionState schema resolvers variableValues (depth + 1)
        parentType source left
        (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_states hallowed hresolve hchildren hdisjoint)

theorem AppendSelectionState.field_allowed_of_guarded_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendSelectionState schema resolvers variableValues (depth + 1)
        parentType source left
        (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_guarded_child_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendSelectionState.field_allowed_of_contained_child_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := selectionSet
                  }
                initial := .object []
              })
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendSelectionState schema resolvers variableValues (depth + 1)
        parentType source left
        (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_contained_child_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendAllowedFieldState.of_child_selectionSet_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> AppendSelectionSetState schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) [] selectionSet)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendAllowedFieldState schema resolvers variableValues (depth + 1)
        parentType source left responseName fieldName arguments directives
        selectionSet depth :=
  AppendAllowedFieldState.of_child_states hallowed hresolve (by
      intro childDepth runtimeType identity hlt
      exact stateEquivalent_of_selectionSet_state
        (hchildren childDepth runtimeType identity hlt)) hdisjoint

theorem AppendSelectionState.field_allowed_of_child_selectionSet_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> AppendSelectionSetState schema resolvers variableValues childDepth
              runtimeType (.object runtimeType identity) [] selectionSet)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendSelectionState schema resolvers variableValues (depth + 1)
        parentType source left
        (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_selectionSet_states hallowed hresolve
      hchildren hdisjoint)

theorem AppendAllowedFieldState.of_child_prefix_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> AppendSelectionSetPrefixState schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity) []
              selectionSet)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendAllowedFieldState schema resolvers variableValues (depth + 1)
        parentType source left responseName fieldName arguments directives
        selectionSet depth :=
  AppendAllowedFieldState.of_child_states hallowed hresolve (by
      intro childDepth runtimeType identity hlt
      exact stateEquivalent_of_selectionSet_prefix_state
        (hchildren childDepth runtimeType identity hlt)) hdisjoint

theorem AppendSelectionState.field_allowed_of_child_prefix_states
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> AppendSelectionSetPrefixState schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity) []
              selectionSet)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [.field responseName fieldName arguments directives selectionSet]))
    : AppendSelectionState schema resolvers variableValues (depth + 1)
        parentType source left
        (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed
    (AppendAllowedFieldState.of_child_prefix_states hallowed hresolve hchildren hdisjoint)

theorem AppendSelectionState.field_allowed_of_child_prefix_states_fresh
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection} {resolved : ResolverValue ObjectIdentity}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hresolve : resolvers.resolve parentType fieldName arguments source = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> AppendSelectionSetPrefixState schema resolvers variableValues
              childDepth runtimeType (.object runtimeType identity) []
              selectionSet)
    (hfresh
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source left).map
            Prod.fst)
    : AppendSelectionState schema resolvers variableValues (depth + 1)
        parentType source left
        (.field responseName fieldName arguments directives selectionSet) :=
  AppendSelectionState.field_allowed_of_child_prefix_states hallowed hresolve
    hchildren
    (executableGroupNamesDisjoint_single_field_of_responseName_fresh schema
      variableValues parentType source left responseName fieldName arguments
      directives selectionSet hallowed hfresh)

theorem executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_guarded_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_eq_spec_of_contained_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem
    executeRootSelectionSet_executableFieldSelections_single_aligned_of_contained_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) field.selectionSet)
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                field.selectionSet))
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source (executableFieldSelections [field]))
        (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field])) := by
  cases field with
  | mk fieldParent responseName fieldName arguments selectionSet =>
      dsimp [executableFieldSelections, executableFieldSelection] at hparent hresolve hchildren ⊢
      subst fieldParent
      exact executeRootSelectionSet_single_field_succ_aligned_of_contained_child_states
        schema resolvers variableValues depth parentType source responseName
        fieldName arguments [] selectionSet resolved rfl hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
    schema resolvers variableValues depth parentType source field resolved
    hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecAlignedEquivalent_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> RootSelectionResultAlignedEquivalent
              (executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (.object runtimeType identity) field.selectionSet)
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues childDepth runtimeType (.object runtimeType identity)
                field.selectionSet))
    : ExecutableFieldsFlatSpecAlignedEquivalent schema resolvers variableValues
        (depth + 1) parentType source [field] := by
  unfold ExecutableFieldsFlatSpecAlignedEquivalent
  exact
    executeRootSelectionSet_executableFieldSelections_single_aligned_of_contained_child_states
      schema resolvers variableValues depth parentType source field resolved
      hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_collected_single_field_group_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (hgroup : (responseName, [field]) ∈ groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [field] := by
  have hgroupParents : ExecutableFieldsParent parentType [field] :=
    hparents responseName [field] hgroup
  have hparent : field.parentType = parentType :=
    hgroupParents field (by simp)
  exact ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    schema resolvers variableValues depth parentType source field
    (resolvers.resolve field.parentType field.fieldName field.arguments source)
    hparent rfl hchildren

theorem ExecutableGroupsFlatSpecEquivalent_single_field_group_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType responseName : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    (hparent : field.parentType = parentType)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, [field])] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact ExecutableFieldsFlatSpecEquivalent_single_of_child_states
    schema resolvers variableValues depth parentType source field
    (resolvers.resolve field.parentType field.fieldName field.arguments source)
    hparent rfl hchildren

theorem executeRootSelectionSet_executableFieldSelections_group_eq_spec_of_merged_complete
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (_hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hungrouped
      : executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source (executableFieldSelections (field :: fields))
        = GraphQL.Execution.executeField schema resolvers variableValues
            (depth + 1) source responseName (field :: fields))
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections (field :: fields))
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          (executableFieldSelections (field :: fields)) := by
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source
          (executableFieldSelections (field :: fields)) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, field :: fields)] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field fields hresponse hparent
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, field :: fields)] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName (field :: fields) := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName (field :: fields) <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hungrouped.trans (hspecRoot.trans hspecField).symm

theorem
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field])
      = GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] := by
  have hroot :=
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_child_states
      schema resolvers variableValues depth parentType source field resolved
      hparent hresolve hchildren
  have hresponseGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.responseName = responseName := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hresponse
  have hparentGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.parentType = parentType := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hparent
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, [field])] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field [] hresponseGroup hparentGroup
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, [field])] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field] := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hroot.trans (hspecRoot.trans hspecField)

theorem
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_contained_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field])
      = GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] := by
  have hroot :=
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_contained_child_states
      schema resolvers variableValues depth parentType source field resolved
      hparent hresolve hchildren
  have hresponseGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.responseName = responseName := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hresponse
  have hparentGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.parentType = parentType := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hparent
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, [field])] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field [] hresponseGroup hparentGroup
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, [field])] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field] := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hroot.trans (hspecRoot.trans hspecField)

theorem
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_guarded_child_states
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source (executableFieldSelections [field])
      = GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] := by
  have hroot :=
    executeRootSelectionSet_executableFieldSelections_single_eq_spec_of_guarded_child_states
      schema resolvers variableValues depth parentType source field resolved
      hparent hresolve hchildren
  have hresponseGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.responseName = responseName := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hresponse
  have hparentGroup :
      ∀ candidate, candidate ∈ [field] ->
        candidate.parentType = parentType := by
    intro candidate hmem
    have hcandidate : candidate = field := by
      simpa using hmem
    rw [hcandidate]
    exact hparent
  have hspecRoot :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (depth + 1) parentType source (executableFieldSelections [field]) =
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
        (depth + 1) source [(responseName, [field])] :=
    specExecuteRootSelectionSet_executableFieldSelections_same_group schema
      resolvers variableValues (depth + 1) parentType source responseName
      field [] hresponseGroup hparentGroup
  have hspecField :
      GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          (depth + 1) source [(responseName, [field])] =
      GraphQL.Execution.executeField schema resolvers variableValues
        (depth + 1) source responseName [field] := by
    cases hfield :
        GraphQL.Execution.executeField schema resolvers variableValues
          (depth + 1) source responseName [field] <;>
      simp [GraphQL.Execution.executeCollectedFields, Result.combine,
        GraphQL.Execution.Result.combine, hfield]
  exact hroot.trans (hspecRoot.trans hspecField)

theorem ExecutableFieldsMergedComplete_single_of_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedComplete_single_of_guarded_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_guarded_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsMergedComplete_single_of_contained_child_states
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse : field.responseName = responseName)
    (hparent : field.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hchildren
      : ∀ childDepth runtimeType (identity : ObjectIdentity),
          childDepth < depth
          -> ValueContainsObject resolved runtimeType identity
          -> schema.typeIncludesObjectBool
                ((schema.fieldReturnType? field.parentType field.fieldName).getD
                  field.fieldName)
                runtimeType
              = true
          -> ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := childDepth
                    parentType := runtimeType
                    source := .object runtimeType identity
                    selectionSet := field.selectionSet
                  }
                initial := .object []
              })
    : ExecutableFieldsMergedComplete schema resolvers variableValues depth
        parentType source responseName field [] resolved := by
  unfold ExecutableFieldsMergedComplete
  exact
    executeRootSelectionSet_executableFieldSelections_single_eq_merged_complete_of_contained_child_states
      schema resolvers variableValues depth parentType source responseName
      field resolved hresponse hparent hresolve hchildren

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hungrouped
      : executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source (executableFieldSelections (field :: fields))
        = GraphQL.Execution.executeField schema resolvers variableValues
            (depth + 1) source responseName (field :: fields))
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source (field :: fields) := by
  unfold ExecutableFieldsFlatSpecEquivalent
  exact executeRootSelectionSet_executableFieldSelections_group_eq_spec_of_merged_complete
    schema resolvers variableValues depth parentType source responseName field
    fields resolved hresponse hparent hresolve hungrouped

theorem ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hmerged
      : ExecutableFieldsMergedComplete schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    : ExecutableFieldsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source (field :: fields) := by
  unfold ExecutableFieldsMergedComplete at hmerged
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hungrouped
      : executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source (executableFieldSelections (field :: fields))
        = GraphQL.Execution.executeField schema resolvers variableValues
            (depth + 1) source responseName (field :: fields))
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hungrouped

theorem ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_mergedComplete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField) (resolved : Option (ResolverValue ObjectIdentity))
    (hresponse
      : ∀ candidate, candidate ∈ field :: fields -> candidate.responseName = responseName)
    (hparent
      : ∀ candidate, candidate ∈ field :: fields -> candidate.parentType = parentType)
    (hresolve
      : resolvers.resolve field.parentType field.fieldName field.arguments source
        = resolved)
    (hmerged
      : ExecutableFieldsMergedComplete schema resolvers variableValues depth
          parentType source responseName field fields resolved)
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] := by
  unfold ExecutableGroupsFlatSpecEquivalent
  simp [collectedExecutableFields]
  exact
    ExecutableFieldsFlatSpecEquivalent_nonempty_group_of_mergedComplete
      schema resolvers variableValues depth parentType source responseName
      field fields resolved hresponse hparent hresolve hmerged

theorem ExecutableGroupsFlatSpecEquivalent_collected_nonempty_group_of_merged_complete
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    (hgroup : (responseName, field :: fields) ∈ groups)
    (hresponses : CollectedGroupsResponseName groups)
    (hparents : CollectedGroupsParent parentType groups)
    (hungrouped
      : executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source (executableFieldSelections (field :: fields))
        = GraphQL.Execution.executeField schema resolvers variableValues
            (depth + 1) source responseName (field :: fields))
    : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
        (depth + 1) parentType source [(responseName, field :: fields)] := by
  have hgroupResponses :
      ExecutableFieldsResponseName responseName (field :: fields) :=
    hresponses responseName (field :: fields) hgroup
  have hgroupParents :
      ExecutableFieldsParent parentType (field :: fields) :=
    hparents responseName (field :: fields) hgroup
  exact
    ExecutableGroupsFlatSpecEquivalent_nonempty_single_group_of_merged_complete
      schema resolvers variableValues depth parentType source responseName
      field fields
      (resolvers.resolve field.parentType field.fieldName field.arguments source)
      hgroupResponses hgroupParents rfl hungrouped

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
