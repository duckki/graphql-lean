import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection

/-!
Append-selection state witnesses and query-level wrappers.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

structure AppendAllowedFieldState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection) (childDepth : Nat)
    : Prop where
  depth_eq : depth = childDepth + 1
  allowed : selectionDirectivesAllowBool variableValues directives = true
  rightEquivalent
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet :=
                [.field responseName fieldName arguments directives selectionSet]
            }
          initial := .object []
        }
  namesDisjoint
    : GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet])

def AppendSelectionState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    : Selection -> Prop
  | .field responseName fieldName arguments directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false
      ∨ ∃ childDepth,
          AppendAllowedFieldState schema resolvers variableValues depth parentType
            source left responseName fieldName arguments directives selectionSet
            childDepth
  | .inlineFragment none directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false
      ∨ selectionDirectivesAllowBool variableValues directives = true
        ∧ ExecutionStateEquivalent
            {
              window :=
                {
                  schema := schema
                  resolvers := resolvers
                  variableValues := variableValues
                  depth := depth
                  parentType := parentType
                  source := source
                  selectionSet := left ++ selectionSet
                }
              initial := .object []
            }
  | .inlineFragment (some typeCondition) directives selectionSet =>
      selectionDirectivesAllowBool variableValues directives = false
      ∨ (selectionDirectivesAllowBool variableValues directives = true
          ∧ doesFragmentTypeApplyBool schema parentType source typeCondition = false)
      ∨ (selectionDirectivesAllowBool variableValues directives = true
          ∧ doesFragmentTypeApplyBool schema parentType source typeCondition = true
          ∧ ExecutionStateEquivalent
              {
                window :=
                  {
                    schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := depth
                    parentType := parentType
                    source := source
                    selectionSet := left ++ selectionSet
                  }
                initial := .object []
              })

theorem AppendSelectionState.field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : AppendSelectionState schema resolvers variableValues depth parentType
        source left
        (.field responseName fieldName arguments directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.field_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth childDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hstate
      : AppendAllowedFieldState schema resolvers variableValues depth parentType
          source left responseName fieldName arguments directives selectionSet
          childDepth)
    : AppendSelectionState schema resolvers variableValues depth parentType
        source left
        (.field responseName fieldName arguments directives selectionSet) := by
  simp [AppendSelectionState]
  exact Or.inr ⟨childDepth, hstate⟩

theorem AppendSelectionState.inline_none_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : AppendSelectionState schema resolvers variableValues depth parentType
        source left (.inlineFragment none directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hbody
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet
              }
            initial := .object []
          })
    : AppendSelectionState schema resolvers variableValues depth parentType
        source left (.inlineFragment none directives selectionSet) := by
  simp [AppendSelectionState, hallowed, hbody]

theorem AppendSelectionState.inline_some_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : AppendSelectionState schema resolvers variableValues depth parentType
        source left
        (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hblocked]

theorem AppendSelectionState.inline_some_not_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    : AppendSelectionState schema resolvers variableValues depth parentType
        source left
        (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hallowed, hnotApply]

theorem AppendSelectionState.inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    (hbody
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet
              }
            initial := .object []
          })
    : AppendSelectionState schema resolvers variableValues depth parentType
        source left
        (.inlineFragment (some typeCondition) directives selectionSet) := by
  simp [AppendSelectionState, hallowed, happly, hbody]

theorem stateEquivalent_of_append_single_selection_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} (selection : Selection)
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hselection
      : AppendSelectionState schema resolvers variableValues depth parentType
          source left selection)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := left ++ [selection]
            }
          initial := .object []
        } := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simp [AppendSelectionState] at hselection
      rcases hselection with hblocked | hrest
      · exact stateEquivalent_of_append_single_field_blocked hleft hblocked
      · rcases hrest with ⟨childDepth, hstep⟩
        cases hstep.depth_eq
        exact stateEquivalent_of_append_single_field_of_disjoint hleft
          hstep.rightEquivalent hstep.namesDisjoint hstep.allowed
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          simp [AppendSelectionState] at hselection
          rcases hselection with hblocked | hallowedBody
          · exact stateEquivalent_of_append_single_inline_none_blocked hleft
              hblocked
          · rcases hallowedBody with ⟨hallowed, hbody⟩
            exact stateEquivalent_of_append_single_inline_none_allowed hbody
              hallowed
      | some typeCondition =>
          simp [AppendSelectionState] at hselection
          rcases hselection with hblocked | hnotApplyStep | happlyStep
          · exact stateEquivalent_of_append_single_inline_some_blocked hleft
              hblocked
          · rcases hnotApplyStep with ⟨hallowed, hnotApply⟩
            exact stateEquivalent_of_append_single_inline_some_not_apply hleft
              hallowed hnotApply
          · rcases happlyStep with ⟨hallowed, happly, hbody⟩
            exact stateEquivalent_of_append_single_inline_some_apply hbody
              hallowed happly

def AppendSelectionSetState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List Selection -> List Selection -> Prop
  | _left, [] => True
  | left, selection :: rest =>
      AppendSelectionState schema resolvers variableValues depth parentType
        source left selection
      ∧ AppendSelectionSetState schema resolvers variableValues depth parentType
          source (left ++ [selection]) rest

theorem AppendSelectionSetState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    : AppendSelectionSetState schema resolvers variableValues depth parentType
        source left [] := by
  simp [AppendSelectionSetState]

theorem AppendSelectionSetState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection} {rest : List Selection}
    (hselection
      : AppendSelectionState schema resolvers variableValues depth parentType
          source left selection)
    (hrest
      : AppendSelectionSetState schema resolvers variableValues depth parentType
          source (left ++ [selection]) rest)
    : AppendSelectionSetState schema resolvers variableValues depth parentType
        source left (selection :: rest) := by
  exact ⟨hselection, hrest⟩

def AppendSelectionSetPrefixState
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    : Prop :=
  ∀ prefixSelections selection suffix,
    selectionSet = prefixSelections ++ selection :: suffix
    -> AppendSelectionState schema resolvers variableValues depth parentType
        source (left ++ prefixSelections) selection

theorem AppendSelectionSetPrefixState.nil
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    : AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source left [] := by
  intro prefixSelections selection suffix hselectionSet
  have hlength := congrArg List.length hselectionSet
  simp at hlength

theorem AppendSelectionSetPrefixState.singleton
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hselection
      : AppendSelectionState schema resolvers variableValues depth parentType
          source left selection)
    : AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source left [selection] := by
  intro prefixSelections nextSelection suffix hselectionSet
  cases prefixSelections with
  | nil =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, rfl⟩
      simpa using hselection
  | cons _head _tail =>
      have hlength := congrArg List.length hselectionSet
      simp at hlength

theorem AppendSelectionSetPrefixState.cons
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    {rest : List Selection}
    (hselection
      : AppendSelectionState schema resolvers variableValues depth parentType
          source left selection)
    (hrest
      : AppendSelectionSetPrefixState schema resolvers variableValues depth
          parentType source (left ++ [selection]) rest)
    : AppendSelectionSetPrefixState schema resolvers variableValues depth
        parentType source left (selection :: rest) := by
  intro prefixSelections nextSelection suffix hselectionSet
  cases prefixSelections with
  | nil =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, _hrest⟩
      simpa using hselection
  | cons head tail =>
      simp at hselectionSet
      rcases hselectionSet with ⟨rfl, hrestSet⟩
      have hstep := hrest tail nextSelection suffix hrestSet
      simpa [List.append_assoc] using hstep

theorem AppendSelectionSetState.of_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ∀ (left selectionSet : List Selection),
        AppendSelectionSetPrefixState schema resolvers variableValues depth
          parentType source left selectionSet
        -> AppendSelectionSetState schema resolvers variableValues depth parentType
            source left selectionSet
  | _left, [], _hstate => by
      exact AppendSelectionSetState.nil
  | left, selection :: rest, hstate => by
      apply AppendSelectionSetState.cons
      · simpa using hstate [] selection rest rfl
      · apply AppendSelectionSetState.of_prefix_state
        intro prefixSelections tailSelection suffix htail
        have hselectionSet :
            selection :: rest =
              (selection :: prefixSelections) ++ tailSelection :: suffix := by
          simp [htail]
        have hstep :=
          hstate (selection :: prefixSelections) tailSelection suffix hselectionSet
        simpa [List.append_assoc] using hstep

theorem AppendSelectionSetState.append
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ∀ (left middle right : List Selection),
        AppendSelectionSetState schema resolvers variableValues depth parentType
          source left middle
        -> AppendSelectionSetState schema resolvers variableValues depth parentType
            source (left ++ middle) right
        -> AppendSelectionSetState schema resolvers variableValues depth parentType
            source left (middle ++ right)
  | _left, [], right, _hmiddle, hright => by
      simpa using hright
  | left, selection :: rest, right, hmiddle, hright => by
      rcases hmiddle with ⟨hselection, hrest⟩
      apply AppendSelectionSetState.cons hselection
      apply AppendSelectionSetState.append (left ++ [selection]) rest right hrest
      simpa [List.append_assoc] using hright

theorem stateEquivalent_of_append_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    : ∀ (left right : List Selection),
        ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          }
        -> AppendSelectionSetState schema resolvers variableValues depth parentType
            source left right
        -> ExecutionStateEquivalent
            {
              window :=
                {
                  schema := schema
                  resolvers := resolvers
                  variableValues := variableValues
                  depth := depth
                  parentType := parentType
                  source := source
                  selectionSet := left ++ right
                }
              initial := .object []
            }
  | left, [], hleft, _hstate => by
      simpa using hleft
  | left, selection :: rest, hleft, hstate => by
      simp [AppendSelectionSetState] at hstate
      rcases hstate with ⟨hselection, hrest⟩
      have hfirst :
          ExecutionStateEquivalent
            { window :=
              { schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ [selection] }
              initial := .object [] } :=
        stateEquivalent_of_append_single_selection_state selection hleft
          hselection
      have htail :=
        stateEquivalent_of_append_selectionSet_state
          (left ++ [selection]) rest hfirst hrest
      simpa [List.append_assoc] using htail

theorem stateEquivalent_of_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate
      : AppendSelectionSetState schema resolvers variableValues depth parentType
          source [] selectionSet)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } := by
  simpa using
    stateEquivalent_of_append_selectionSet_state
      ([] : List Selection) selectionSet
      (emptySelectionStateEquivalent schema resolvers variableValues depth
        parentType source (.object []))
      hstate

theorem stateEquivalent_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate
      : AppendSelectionSetPrefixState schema resolvers variableValues depth
          parentType source [] selectionSet)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } :=
  stateEquivalent_of_selectionSet_state
    (AppendSelectionSetState.of_prefix_state [] selectionSet hstate)

theorem executeRootSelectionSet_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate
      : AppendSelectionSetState schema resolvers variableValues depth parentType
          source [] selectionSet)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    {
      schema := schema
      resolvers := resolvers
      variableValues := variableValues
      depth := depth
      parentType := parentType
      source := source
      selectionSet := selectionSet
    }
    (stateEquivalent_of_selectionSet_state hstate)

theorem executeRootSelectionSet_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    (hstate
      : AppendSelectionSetPrefixState schema resolvers variableValues depth
          parentType source [] selectionSet)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source selectionSet :=
  executeRootSelectionSet_eq_spec_of_selectionSet_state
    (AppendSelectionSetState.of_prefix_state [] selectionSet hstate)

theorem executeQueryWithFuel_eq_spec_of_root_fields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hfields
      : executeRootSelectionSet schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            depth (operation.rootType schema) source operation.selectionSet)
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source := by
  rw [executeQueryWithFuel, GraphQL.Execution.executeQueryWithFuel, hroot,
    hfields]

theorem executeQueryWithFuel_eq_spec_of_root_false
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = false)
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source := by
  rw [executeQueryWithFuel, GraphQL.Execution.executeQueryWithFuel, hroot]
  simp

theorem executeQueryWithFuel_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := depth
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact
    executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
      { schema := schema
        resolvers := resolvers
        variableValues :=
          GraphQL.Execution.coerceVariableValues operation variableValues
        depth := depth
        parentType := (operation.rootType schema)
        source := source
        selectionSet := operation.selectionSet }
      hstate

theorem executeQueryWithFuel_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate
      : AppendSelectionSetState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source [] operation.selectionSet)
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source :=
  executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation depth source hroot
    (stateEquivalent_of_selectionSet_state hstate)

theorem executeQueryWithFuel_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate
      : AppendSelectionSetPrefixState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source [] operation.selectionSet)
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source :=
  executeQueryWithFuel_eq_spec_of_selectionSet_state schema resolvers
    variableValues operation depth source hroot
    (AppendSelectionSetState.of_prefix_state [] operation.selectionSet hstate)

theorem executeQueryWithFuel_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hflat
      : executeRootSelectionSet schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            depth (operation.rootType schema) source
            (executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  (operation.rootType schema) source operation.selectionSet))))
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact executeRootSelectionSet_eq_spec_of_flattened_collectFields_eq schema
    resolvers (GraphQL.Execution.coerceVariableValues operation variableValues)
    depth (operation.rootType schema) source
    operation.selectionSet hflat

theorem executeQueryWithFuel_eq_spec_of_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hflatSpec
      : ExecutableFieldsFlatSpecEquivalent schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              (operation.rootType schema) source operation.selectionSet)))
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact executeRootSelectionSet_eq_spec_of_flatCollects_and_flatSpecEquivalent
    schema resolvers
    (GraphQL.Execution.coerceVariableValues operation variableValues)
    depth (operation.rootType schema) source
    operation.selectionSet hdirect hflatSpec

theorem executeQueryWithFuel_eq_spec_of_group_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hgroups
      : ExecutableGroupsFlatSpecEquivalent schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source
          (GraphQL.Execution.collectFields schema
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            (operation.rootType schema)
            source operation.selectionSet))
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source := by
  apply executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers
    variableValues operation depth source hroot
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers
      (GraphQL.Execution.coerceVariableValues operation variableValues)
      depth (operation.rootType schema) source
      operation.selectionSet hdirect hgroups

theorem executeQueryWithFuel_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (depth : Nat) (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues) depth
          (operation.rootType schema) source operation.selectionSet (.object []))
    : executeQueryWithFuel schema resolvers variableValues operation depth source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source := by
  apply executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation depth source hroot
  exact stateEquivalent_of_exact_empty_group schema resolvers
    (GraphQL.Execution.coerceVariableValues operation variableValues)
    depth (operation.rootType schema) source operation.selectionSet hcollect hdirect

theorem executeQuery_eq_spec_of_root_fields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hfields
      : executeRootSelectionSet schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source operation.selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            (GraphQL.Execution.executeQueryFuelBound operation)
            (operation.rootType schema) source operation.selectionSet)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryWithFuel_eq_spec_of_root_fields_eq schema resolvers variableValues
    operation (GraphQL.Execution.executeQueryFuelBound operation) source hroot
    hfields

theorem executeQuery_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues :=
                  GraphQL.Execution.coerceVariableValues operation variableValues
                depth := GraphQL.Execution.executeQueryFuelBound operation
                parentType := (operation.rootType schema)
                source := source
                selectionSet := operation.selectionSet
              }
            initial := .object []
          })
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryWithFuel_eq_spec_of_state_equivalent schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryFuelBound operation)
    source hroot hstate

theorem executeQuery_eq_spec_of_selectionSet_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate
      : AppendSelectionSetState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source [] operation.selectionSet)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryWithFuel_eq_spec_of_selectionSet_state schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryFuelBound operation)
    source hroot hstate

theorem executeQuery_eq_spec_of_selectionSet_prefix_state
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hstate
      : AppendSelectionSetPrefixState schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source [] operation.selectionSet)
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact
    executeQueryWithFuel_eq_spec_of_selectionSet_prefix_state schema resolvers
      variableValues operation (GraphQL.Execution.executeQueryFuelBound operation)
      source hroot hstate

theorem executeQuery_eq_spec_of_flattened_collectFields_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hflat
      : executeRootSelectionSet schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source operation.selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            (GraphQL.Execution.executeQueryFuelBound operation)
            (operation.rootType schema) source
            (executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema
                  (GraphQL.Execution.coerceVariableValues operation variableValues)
                  (operation.rootType schema) source operation.selectionSet))))
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryWithFuel_eq_spec_of_flattened_collectFields_eq schema
    resolvers variableValues operation
    (GraphQL.Execution.executeQueryFuelBound operation) source hroot hflat

theorem executeQuery_eq_spec_of_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hflatSpec
      : ExecutableFieldsFlatSpecEquivalent schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema
              (GraphQL.Execution.coerceVariableValues operation variableValues)
              (operation.rootType schema) source operation.selectionSet)))
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryWithFuel_eq_spec_of_flat_predicates schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryFuelBound operation)
    source hroot hdirect hflatSpec

theorem executeQuery_eq_spec_of_group_flat_predicates
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source operation.selectionSet (.object []))
    (hgroups
      : ExecutableGroupsFlatSpecEquivalent schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source
          (GraphQL.Execution.collectFields schema
            (GraphQL.Execution.coerceVariableValues operation variableValues)
            (operation.rootType schema)
            source operation.selectionSet))
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryWithFuel_eq_spec_of_group_flat_predicates schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryFuelBound operation)
    source hroot hdirect hgroups

theorem executeQuery_eq_spec_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectIdentity)
    (hroot : rootSourceAppliesBool schema operation source = true)
    (hcollect
      : GraphQL.Execution.collectFields schema
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (operation.rootType schema)
          source operation.selectionSet
        = [])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers
          (GraphQL.Execution.coerceVariableValues operation variableValues)
          (GraphQL.Execution.executeQueryFuelBound operation)
          (operation.rootType schema) source operation.selectionSet (.object []))
    : executeQuery schema resolvers variableValues operation source
      = GraphQL.Execution.executeQuery schema resolvers variableValues operation
          source := by
  unfold executeQuery GraphQL.Execution.executeQuery
  exact executeQueryWithFuel_eq_spec_of_exact_empty_group schema resolvers
    variableValues operation (GraphQL.Execution.executeQueryFuelBound operation)
    source hroot hcollect hdirect
end ExecutionUngrouped
end Algorithms

end GraphQL
