import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList

/-!
Fresh-prefix visit witnesses for group-list selection sets.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance groupListFreshPrefixesResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

def VisitSubfieldsFlatCollectsFreshPrefixes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Prop :=
  ∀ fields,
    (∀ field,
      field
        ∈ collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)
      -> field.responseName ∉ fields.map Prod.fst)
    -> VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
        source selectionSet (.object fields)

theorem VisitSubfieldsFlatCollectsFreshPrefixes.empty
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {selectionSet : List Selection}
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source selectionSet
      -> VisitSubfieldsFlatCollects schema resolvers variableValues depth parentType
          source selectionSet (.object []) := by
  intro hfresh
  exact hfresh [] (by simp)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_nil
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source [] := by
  intro fields _hfresh
  exact VisitSubfieldsFlatCollects_nil schema resolvers variableValues depth
    parentType source (.object fields)

theorem VisitSubfieldsFlatCollectsFreshPrefixes.of_allOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues depth
        parentType source selectionSet
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source selectionSet := by
  intro hflat fields _hfresh
  exact hflat (.object fields)

theorem
    VisitSubfieldsFlatCollectsFreshPrefixes_executableFieldSelections_collectedCollectFields
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (selectionSet : List Selection)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) := by
  intro fields _hfresh
  exact
    VisitSubfieldsFlatCollects_executableFieldSelections_collectedCollectFields
      schema resolvers variableValues depth parentType source selectionSet
      (.object fields)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_executableFieldSelections_same_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (fields : List ExecutableField)
    (hresponse : ∀ field, field ∈ fields -> field.responseName = responseName)
    (hparent : ∀ field, field ∈ fields -> field.parentType = parentType)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source (executableFieldSelections fields) :=
  VisitSubfieldsFlatCollectsFreshPrefixes.of_allOutputs schema resolvers
    variableValues depth parentType source (executableFieldSelections fields)
    (by
      intro output
      exact VisitSubfieldsFlatCollects_executableFieldSelections_same_group
        schema resolvers variableValues depth parentType source responseName
        fields output hresponse hparent)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection)
    (hbody
      : match selection with
        | .field _responseName _fieldName _arguments _directives _selectionSet =>
            True
        | .inlineFragment none directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers
                variableValues depth parentType source selectionSet
        | .inlineFragment (some typeCondition) directives selectionSet =>
            selectionDirectivesAllowBool variableValues directives = true
            -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
            -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers
                variableValues depth parentType source selectionSet)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source [selection] := by
  intro fields hfresh
  apply VisitSubfieldsFlatCollects_single schema resolvers variableValues depth
    parentType source selection (.object fields)
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      exact trivial
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          intro hallowed
          apply hbody hallowed fields
          intro field hfield
          apply hfresh field
          simpa [GraphQL.Execution.collectFields,
            GraphQL.Execution.collectSelection,
            GraphQL.Execution.mergeExecutableGroups, hallowed] using hfield
      | some typeCondition =>
          intro hallowed happly
          apply hbody hallowed happly fields
          intro field hfield
          apply hfresh field
          simpa [GraphQL.Execution.collectFields,
            GraphQL.Execution.collectSelection,
            GraphQL.Execution.mergeExecutableGroups, hallowed, happly] using
            hfield

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        [.field responseName fieldName arguments directives selectionSet] := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_single
  trivial

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hbody
      : selectionDirectivesAllowBool variableValues directives = true
        -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
            depth parentType source selectionSet)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        [.inlineFragment none directives selectionSet] := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_single
  exact hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (hbody
      : selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
            depth parentType source selectionSet)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        [.inlineFragment (some typeCondition) directives selectionSet] := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_single
  exact hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues directives = true
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source (selectionSet ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hallows hflat fields hfresh
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (selectionSet ++ rest)) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source selectionSet rest (ResponseValue.object fields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues directives = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source rest
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hskip hflat fields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (selectionDirectivesAllowBool variableValues directives = true
        -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
            depth parentType source (selectionSet ++ rest))
      -> (selectionDirectivesAllowBool variableValues directives = false
          -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
              depth parentType source rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.inlineFragment none directives selectionSet :: rest) := by
  intro hallowed hskipped
  by_cases hallows : selectionDirectivesAllowBool variableValues directives = true
  · exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_allowed
        schema resolvers variableValues depth parentType source directives
        selectionSet rest hallows (hallowed hallows)
  · have hskip : selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_cons_skipped
        schema resolvers variableValues depth parentType source directives
        selectionSet rest hskip (hskipped hskip)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_allowed_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues directives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source (selectionSet ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.inlineFragment (some typeCondition) directives selectionSet
            :: rest) := by
  intro hallows happly hflat fields hfresh
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (selectionSet ++ rest)) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, happly,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source selectionSet rest (ResponseValue.object fields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, happly,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues directives = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source rest
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.inlineFragment (some typeCondition) directives selectionSet
            :: rest) := by
  intro hskip hflat fields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues directives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source rest
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.inlineFragment (some typeCondition) directives selectionSet
            :: rest) := by
  intro hallows hnotApply hflat fields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest) ->
        field.responseName ∉ fields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
      hfield
  have hbody := hflat fields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
    hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
            depth parentType source (selectionSet ++ rest))
      -> (selectionDirectivesAllowBool variableValues directives = false
          -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
              depth parentType source rest)
      -> (selectionDirectivesAllowBool variableValues directives = true
          -> doesFragmentTypeApplyBool schema parentType source typeCondition = false
          -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
              depth parentType source rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.inlineFragment (some typeCondition) directives selectionSet
            :: rest) := by
  intro hallowedApply hskipped hnotApply
  by_cases hallows : selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · exact
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_allowed_apply
          schema resolvers variableValues depth parentType source typeCondition
          directives selectionSet rest hallows happly
          (hallowedApply hallows happly)
    · have hdoesNotApply :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases h :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      exact
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_not_apply
          schema resolvers variableValues depth parentType source typeCondition
          directives selectionSet rest hallows hdoesNotApply
          (hnotApply hallows hdoesNotApply)
  · have hskip : selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_cons_skipped
        schema resolvers variableValues depth parentType source typeCondition
        directives selectionSet rest hskip (hskipped hskip)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_none_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = true
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
                fieldSelectionSet
              :: inlineSelectionSet
            ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: Selection.inlineFragment none inlineDirectives inlineSelectionSet
            :: rest) := by
  intro hallows hflat prefixFields hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet ::
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
        fieldSelectionSet :: inlineSelectionSet)
      rest (ResponseValue.object prefixFields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_none_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: Selection.inlineFragment none inlineDirectives inlineSelectionSet
            :: rest) := by
  intro hskip hflat prefixFields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet :: rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_some_cons_allowed_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName typeCondition : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
                fieldSelectionSet
              :: inlineSelectionSet
            ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: Selection.inlineFragment (some typeCondition) inlineDirectives
                inlineSelectionSet
            :: rest) := by
  intro hallows happly hflat prefixFields hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet ::
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, happly,
      GraphQL.NormalForm.collectFields_append] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
      (Selection.field responseName fieldName arguments fieldDirectives
        fieldSelectionSet :: inlineSelectionSet)
      rest (ResponseValue.object prefixFields)] at hbody
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, happly,
    GraphQL.NormalForm.collectFields_append] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_some_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName typeCondition : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: Selection.inlineFragment (some typeCondition) inlineDirectives
                inlineSelectionSet
            :: rest) := by
  intro hskip hflat prefixFields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet :: rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil] using hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_inline_some_cons_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName typeCondition : Name) (arguments : List Argument)
    (fieldDirectives inlineDirectives : List DirectiveApplication)
    (fieldSelectionSet inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (Selection.field responseName fieldName arguments fieldDirectives
              fieldSelectionSet
            :: Selection.inlineFragment (some typeCondition) inlineDirectives
                inlineSelectionSet
            :: rest) := by
  intro hallows hnotApply hflat prefixFields hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (Selection.field responseName fieldName arguments
                  fieldDirectives fieldSelectionSet :: rest)) ->
        executable.responseName ∉ prefixFields.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
      hfield
  have hbody := hflat prefixFields hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil] using
    hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues directives = true
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ executableFieldSelections
                [executableField parentType responseName fieldName arguments selectionSet]
            ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hallows hflat prefixOutput hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++
                executableFieldSelections
                  [executableField parentType responseName fieldName
                    arguments selectionSet] ++
                rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      executableFieldSelections, executableFieldSelection, executableField,
      selectionDirectivesAllowBool_empty,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
    (executableFieldSelections prefixFields ++
      executableFieldSelections
        [executableField parentType responseName fieldName arguments
          selectionSet])
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (executableFieldSelections
      [executableField parentType responseName fieldName arguments
        selectionSet])
    (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.field responseName fieldName arguments directives selectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  cases depth with
  | zero =>
      simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows,
        executableFieldSelections, executableFieldSelection, executableField,
        selectionDirectivesAllowBool_empty,
        GraphQL.NormalForm.collectFields_append, List.append_assoc,
        outOfFuel, combineVisitStatus_error_one_left_rotate] using hbody
  | succ depth' =>
      simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, hallows,
        executableFieldSelections, executableFieldSelection, executableField,
        selectionDirectivesAllowBool_empty,
        GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_field_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues directives = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hskip hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.field responseName fieldName arguments directives selectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  cases depth <;>
    simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_allowed
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = true
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields ++ inlineSelectionSet ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ Selection.inlineFragment none inlineDirectives inlineSelectionSet
                :: rest) := by
  intro hallows hflat prefixOutput hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
    (executableFieldSelections prefixFields ++ inlineSelectionSet)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    inlineSelectionSet (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_none_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ Selection.inlineFragment none inlineDirectives inlineSelectionSet
                :: rest) := by
  intro hskip hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment none inlineDirectives inlineSelectionSet ::
      rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_allowed_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (typeCondition : Name)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields ++ inlineSelectionSet ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ Selection.inlineFragment (some typeCondition) inlineDirectives
                  inlineSelectionSet
                :: rest) := by
  intro hallows happly hflat prefixOutput hfresh
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections prefixFields ++
                inlineSelectionSet ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, happly,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source
    (executableFieldSelections prefixFields ++ inlineSelectionSet)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    inlineSelectionSet (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment (some typeCondition) inlineDirectives
      inlineSelectionSet :: rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, happly,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_skipped
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (typeCondition : Name)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ Selection.inlineFragment (some typeCondition) inlineDirectives
                  inlineSelectionSet
                :: rest) := by
  intro hskip hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hskip, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment (some typeCondition) inlineDirectives
      inlineSelectionSet :: rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hskip, hmergeNil,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_prefix_inline_some_cons_not_apply
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (prefixFields : List ExecutableField)
    (typeCondition : Name)
    (inlineDirectives : List DirectiveApplication)
    (inlineSelectionSet rest : List Selection)
    : selectionDirectivesAllowBool variableValues inlineDirectives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = false
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields ++ rest)
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source
          (executableFieldSelections prefixFields
            ++ Selection.inlineFragment (some typeCondition) inlineDirectives
                  inlineSelectionSet
                :: rest) := by
  intro hallows hnotApply hflat prefixOutput hfresh
  have hmergeNil :
      GraphQL.Execution.mergeExecutableGroups []
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rest)
        =
      GraphQL.Execution.collectFields schema variableValues parentType source
        rest :=
    GraphQL.NormalForm.mergeExecutableGroups_nil_left_of_namesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rest)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source rest)
  have hflatFields :
      ∀ executable,
        executable ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections prefixFields ++ rest)) ->
        executable.responseName ∉ prefixOutput.map Prod.fst := by
    intro executable hfield
    apply hfresh executable
    simpa [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil,
      GraphQL.NormalForm.collectFields_append, List.append_assoc] using hfield
  have hbody := hflat prefixOutput hflatFields
  unfold VisitSubfieldsFlatCollects at hbody ⊢
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    rest (ResponseValue.object prefixOutput)] at hbody
  rw [visitSubfields_append_equivalence schema resolvers variableValues depth
    parentType source (executableFieldSelections prefixFields)
    (Selection.inlineFragment (some typeCondition) inlineDirectives
      inlineSelectionSet :: rest) (ResponseValue.object prefixOutput)]
  simpa [visitSubfields, visitSelection, GraphQL.Execution.collectFields,
    GraphQL.Execution.collectSelection, hallows, hnotApply, hmergeNil,
    GraphQL.NormalForm.collectFields_append, List.append_assoc] using hbody

theorem VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List Selection)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    (hleft
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source left)
    (hright
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source right)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source (left ++ right) := by
  intro prefixFields hfresh
  have hrightNodup :
      GraphQL.NormalForm.executableGroupNamesNodup
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right) :=
    GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source right
  have hflatAppend :
      collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (left ++ right)) =
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source left) ++
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source right) := by
    rw [GraphQL.NormalForm.collectFields_append]
    exact
      collectedExecutableFields_mergeExecutableGroups_eq_append_of_namesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left)
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right)
        hdisjoint hrightNodup
  have hleftFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left) ->
        field.responseName ∉ prefixFields.map Prod.fst := by
    intro field hmem
    apply hfresh field
    rw [hflatAppend]
    exact List.mem_append_left _ hmem
  let leftFlatSelections :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left))
  obtain ⟨suffixFields, hsuffixFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source leftFlatSelections []
  let suffixStatus :=
    (visitSubfields schema resolvers variableValues depth parentType source
      leftFlatSelections (.object [])).snd
  have hsuffix :
      visitSubfields schema resolvers variableValues depth parentType source
        leftFlatSelections (.object []) =
      (.object suffixFields, suffixStatus) :=
    Prod.ext hsuffixFields rfl
  have hleftPrefix :
      visitSubfields schema resolvers variableValues depth parentType source
        leftFlatSelections (.object prefixFields) =
      (.object (prefixFields ++ suffixFields), suffixStatus) := by
    simpa [leftFlatSelections] using
      visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
        variableValues depth parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source left))
        prefixFields [] suffixFields suffixStatus hleftFresh
        (by simpa [leftFlatSelections] using hsuffix)
  have hrightFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source right) ->
        field.responseName ∉ (prefixFields ++ suffixFields).map Prod.fst := by
    intro field hmem hname
    have hrightName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source right).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source right)
        (collectFields_responseName schema variableValues parentType source
          right)
        field hmem
    have hcombined :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (left ++ right)) := by
      rw [hflatAppend]
      exact List.mem_append_right _ hmem
    simp [List.map_append] at hname
    rcases hname with hprefix | hsuffixMem
    · have hprefixName : field.responseName ∈ prefixFields.map Prod.fst := by
        simpa [List.mem_map] using hprefix
      exact hfresh field hcombined hprefixName
    · have hleftName :
          field.responseName ∈
            (GraphQL.Execution.collectFields schema variableValues parentType
              source left).map Prod.fst :=
        visitSubfields_flattened_empty_key_mem_collectFields schema resolvers
          variableValues depth parentType source left suffixFields
          field.responseName
          (by simpa [leftFlatSelections] using hsuffixFields)
          (by simpa [List.mem_map] using hsuffixMem)
      exact hdisjoint field.responseName hleftName hrightName
  apply VisitSubfieldsFlatCollects_append_of_namesDisjoint schema resolvers
    variableValues depth parentType source left right (.object prefixFields)
    hdisjoint hrightNodup
  · simpa [VisitSubfieldsRawFlatCollects, VisitSubfieldsFlatCollects] using
      hleft prefixFields hleftFresh
  · have hrightFlat := hright (prefixFields ++ suffixFields) hrightFresh
    simpa [VisitSubfieldsRawFlatCollects, VisitSubfieldsFlatCollects,
      leftFlatSelections, hleftPrefix] using hrightFlat

theorem VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection) (rest : List Selection)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType
            source [selection])
          (GraphQL.Execution.collectFields schema variableValues parentType source rest))
    (hselection
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source [selection])
    (hrest
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source rest)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source (selection :: rest) := by
  simpa using
    VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint schema
      resolvers variableValues depth parentType source [selection] rest
      hdisjoint hselection hrest

theorem VisitSubfieldsFlatCollectsFreshPrefixes_field_cons_of_responseName_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (hfresh
      : selectionDirectivesAllowBool variableValues directives = true
        -> responseName
            ∉ (GraphQL.Execution.collectFields schema variableValues parentType
                source rest).map
                Prod.fst)
    (hrest
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          depth parentType source rest)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        depth parentType source
        (.field responseName fieldName arguments directives selectionSet :: rest) := by
  apply VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint
  · intro candidate hleft hright
    by_cases hallowed :
        selectionDirectivesAllowBool variableValues directives = true
    · simp [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
        hallowed] at hleft
      subst candidate
      exact hfresh hallowed hright
    · have hblocked :
          selectionDirectivesAllowBool variableValues directives = false := by
        cases h :
            selectionDirectivesAllowBool variableValues directives
        · rfl
        · exact False.elim (hallowed h)
      simp [GraphQL.Execution.collectFields,
        GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
        hblocked] at hleft
  · apply VisitSubfieldsFlatCollectsFreshPrefixes_single
    trivial
  · exact hrest

def SelectionSetCollectFieldsHeadDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List Selection -> Prop
  | [] => True
  | selection :: rest =>
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [selection])
        (GraphQL.Execution.collectFields schema variableValues parentType source rest)
      ∧ SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType source rest

theorem SelectionSetCollectFieldsHeadDisjoint_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ left right,
        SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType source left
        -> SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
            source right
        -> GraphQL.NormalForm.executableGroupNamesDisjoint
            (GraphQL.Execution.collectFields schema variableValues parentType source left)
            (GraphQL.Execution.collectFields schema variableValues parentType source
              right)
        -> SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
            source (left ++ right)
  | [], right, _hleft, hright, _hdisjoint => by
      simpa [SelectionSetCollectFieldsHeadDisjoint] using hright
  | selection :: rest, right, hleft, hright, hdisjoint => by
      rcases hleft with ⟨hheadRest, hrest⟩
      constructor
      · intro responseName hhead htail
        have htailParts :
            responseName ∈
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest).map Prod.fst
              ∨
            responseName ∈
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source right).map Prod.fst := by
          have htailMerge :
              responseName ∈
                (GraphQL.Execution.mergeExecutableGroups
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest)
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source right)).map Prod.fst := by
            simpa [GraphQL.NormalForm.collectFields_append] using htail
          exact
            (mergeExecutableGroups_key_mem
              (GraphQL.Execution.collectFields schema variableValues
                parentType source rest)
              (GraphQL.Execution.collectFields schema variableValues
                parentType source right)
              responseName).mp htailMerge
        rcases htailParts with hrestName | hrightName
        · exact hheadRest responseName hhead hrestName
        · apply hdisjoint responseName
          · rw [show selection :: rest = [selection] ++ rest by rfl]
            rw [GraphQL.NormalForm.collectFields_append]
            exact
              (mergeExecutableGroups_key_mem
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source [selection])
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest)
                responseName).mpr (Or.inl hhead)
          · exact hrightName
      · exact
          SelectionSetCollectFieldsHeadDisjoint_append_of_namesDisjoint schema
            variableValues parentType source rest right hrest hright
            (by
              intro responseName hrestName hrightName
              apply hdisjoint responseName
              · rw [show selection :: rest = [selection] ++ rest by rfl]
                rw [GraphQL.NormalForm.collectFields_append]
                exact
                  (mergeExecutableGroups_key_mem
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source [selection])
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source rest)
                    responseName).mpr (Or.inr hrestName)
              · exact hrightName)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ selectionSet,
        SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source selectionSet
        -> (∀ selection,
              selection ∈ selectionSet
              -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers
                  variableValues depth parentType source [selection])
        -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
            depth parentType source selectionSet
  | [], _hdisjoint, _hsingle =>
      VisitSubfieldsFlatCollectsFreshPrefixes_nil schema resolvers
        variableValues depth parentType source
  | selection :: rest, hdisjoint, hsingle => by
      rcases hdisjoint with ⟨hheadDisjoint, hrestDisjoint⟩
      apply VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint
        schema resolvers variableValues depth parentType source selection rest
        hheadDisjoint
      · exact hsingle selection (by simp)
      · exact
          VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjoint schema
            resolvers variableValues depth parentType source rest
            hrestDisjoint
            (by
              intro candidate hcandidate
              exact hsingle candidate (by simp [hcandidate]))

mutual
  def SelectionCollectFieldsHeadDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : Selection -> Prop
    | .field _responseName _fieldName _arguments _directives _selectionSet =>
        True
    | .inlineFragment _typeCondition _directives selectionSet =>
        SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet

  def SelectionSetCollectFieldsHeadDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : Prop :=
    SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
      source selectionSet
    ∧ ∀ selection,
        selection ∈ selectionSet
        -> SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
            source selection
end

mutual
  theorem VisitSubfieldsFlatCollectsFreshPrefixes_single_of_headDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ selection,
          SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
            source selection
          -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
              depth parentType source [selection]
    | .field responseName fieldName arguments directives selectionSet, _htree =>
        VisitSubfieldsFlatCollectsFreshPrefixes_field_single schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet
    | .inlineFragment none directives selectionSet, htree =>
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
          resolvers variableValues depth parentType source directives
          selectionSet
          (by
            intro _hallowed
            exact
              VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree
                schema resolvers variableValues depth parentType source
                selectionSet
                (by
                  simpa [SelectionCollectFieldsHeadDisjointTree] using htree))
    | .inlineFragment (some typeCondition) directives selectionSet, htree =>
        VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
          resolvers variableValues depth parentType source typeCondition
          directives selectionSet
          (by
            intro _hallowed _happly
            exact
              VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree
                schema resolvers variableValues depth parentType source
                selectionSet
                (by
                  simpa [SelectionCollectFieldsHeadDisjointTree] using htree))

  theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ selectionSet,
          SelectionSetCollectFieldsHeadDisjointTree schema variableValues
            parentType source selectionSet
          -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
              depth parentType source selectionSet
    | selectionSet, htree => by
        have htree' :
            SelectionSetCollectFieldsHeadDisjoint schema variableValues
                parentType source selectionSet
              ∧ ∀ selection, selection ∈ selectionSet ->
                  SelectionCollectFieldsHeadDisjointTree schema variableValues
                    parentType source selection := by
          simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree
        rcases htree' with ⟨hdisjoint, hchildren⟩
        exact VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjoint schema
          resolvers variableValues depth parentType source selectionSet
          hdisjoint
          (by
            intro selection hselection
            exact
              VisitSubfieldsFlatCollectsFreshPrefixes_single_of_headDisjointTree
                schema resolvers variableValues depth parentType source
                selection (hchildren selection hselection))
end

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
