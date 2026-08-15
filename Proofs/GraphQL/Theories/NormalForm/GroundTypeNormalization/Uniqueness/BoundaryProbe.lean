import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ExecutionSuccess
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ProbeTags
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Projection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.TaggedObservable

/-!
Boundary probes for composite field-head differences.

`fieldPairProbeResolvers` can tag a target field by its field head, but for
abstract composite returns it chooses the target runtime by searching the root
selection set.  For field-head separators we often already have a concrete
runtime from the selected child.  This resolver lets the parent target choose
that runtime explicitly, while preserving the existing tagged child behaviour.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

noncomputable def fieldPairRuntimeProbeResolve
    (schema : Schema) (childRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue (Option FieldPairProbeTag))
    : Option (Execution.ResolverValue (Option FieldPairProbeTag)) := by
  classical
  exact
    match source with
    | .object _ (some tag) =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            some
              (fieldPairProbeHeadResolverValue schema childRootSelectionSet
                parentType fieldName arguments tag fieldDefinition.outputType)
    | .object _ none =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            if fieldProbeTarget targetParent leftField leftArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime leftRuntime
                  (some FieldPairProbeTag.left) fieldDefinition.outputType)
            else if fieldProbeTarget targetParent rightField rightArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime rightRuntime
                  (some FieldPairProbeTag.right) fieldDefinition.outputType)
            else
              none
    | _ => none

noncomputable def fieldPairRuntimeProbeResolvers
    (schema : Schema) (childRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    : Execution.Resolvers (Option FieldPairProbeTag) where
  resolve parentType fieldName arguments source :=
    fieldPairRuntimeProbeResolve schema childRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime parentType fieldName arguments source
  resolve_argumentsEquivalent := by
    intro parentType fieldName firstArguments laterArguments source
      harguments
    classical
    cases hlookup : schema.lookupField parentType fieldName with
    | none =>
        cases source <;> simp [fieldPairRuntimeProbeResolve, hlookup]
    | some fieldDefinition =>
        cases source with
        | null =>
            simp [fieldPairRuntimeProbeResolve]
        | scalar value =>
            simp [fieldPairRuntimeProbeResolve]
        | list values =>
            simp [fieldPairRuntimeProbeResolve]
        | object runtimeType sourceTag =>
            cases sourceTag with
            | some tag =>
                have hvalue :=
                  fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent
                    schema childRootSelectionSet parentType fieldName tag
                    harguments fieldDefinition.outputType
                simp [fieldPairRuntimeProbeResolve, hlookup, hvalue]
            | none =>
                have hleftIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    leftField leftArguments parentType fieldName firstArguments
                    laterArguments harguments
                have hrightIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    rightField rightArguments parentType fieldName
                    firstArguments laterArguments harguments
                by_cases hfirstLeft :
                    fieldProbeTarget targetParent leftField leftArguments
                      parentType fieldName firstArguments
                · have hlaterLeft :
                      fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments :=
                    hleftIff.mp hfirstLeft
                  simp [fieldPairRuntimeProbeResolve, hlookup, hfirstLeft,
                    hlaterLeft]
                · have hlaterLeft :
                      ¬ fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments := by
                    intro hlater
                    exact hfirstLeft (hleftIff.mpr hlater)
                  by_cases hfirstRight :
                      fieldProbeTarget targetParent rightField rightArguments
                        parentType fieldName firstArguments
                  · have hlaterRight :
                        fieldProbeTarget targetParent rightField rightArguments
                          parentType fieldName laterArguments :=
                      hrightIff.mp hfirstRight
                    simp [fieldPairRuntimeProbeResolve, hlookup, hfirstLeft,
                      hlaterLeft, hfirstRight, hlaterRight]
                  · have hlaterRight :
                        ¬ fieldProbeTarget targetParent rightField
                          rightArguments parentType fieldName
                          laterArguments := by
                      intro hlater
                      exact hfirstRight (hrightIff.mpr hlater)
                    simp [fieldPairRuntimeProbeResolve, hlookup, hfirstLeft,
                      hlaterLeft, hfirstRight, hlaterRight]

def fieldPairSideRuntimeProbeRoot
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    : FieldPairProbeTag -> List Selection
  | .left => leftChildRootSelectionSet
  | .right => rightChildRootSelectionSet
  | .filler => leftChildRootSelectionSet

noncomputable def fieldPairSideRuntimeProbeResolve
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue (Option FieldPairProbeTag))
    : Option (Execution.ResolverValue (Option FieldPairProbeTag)) := by
  classical
  exact
    match source with
    | .object _ (some tag) =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            some
              (fieldPairProbeHeadResolverValue schema
                (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                  rightChildRootSelectionSet tag)
                parentType fieldName arguments tag fieldDefinition.outputType)
    | .object _ none =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            if fieldProbeTarget targetParent leftField leftArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime leftRuntime
                  (some FieldPairProbeTag.left) fieldDefinition.outputType)
            else if fieldProbeTarget targetParent rightField rightArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime rightRuntime
                  (some FieldPairProbeTag.right) fieldDefinition.outputType)
            else
              none
    | _ => none

noncomputable def fieldPairSideRuntimeProbeResolvers
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    : Execution.Resolvers (Option FieldPairProbeTag) where
  resolve parentType fieldName arguments source :=
    fieldPairSideRuntimeProbeResolve schema leftChildRootSelectionSet
      rightChildRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime parentType
      fieldName arguments source
  resolve_argumentsEquivalent := by
    intro parentType fieldName firstArguments laterArguments source
      harguments
    classical
    cases hlookup : schema.lookupField parentType fieldName with
    | none =>
        cases source <;> simp [fieldPairSideRuntimeProbeResolve, hlookup]
    | some fieldDefinition =>
        cases source with
        | null =>
            simp [fieldPairSideRuntimeProbeResolve]
        | scalar value =>
            simp [fieldPairSideRuntimeProbeResolve]
        | list values =>
            simp [fieldPairSideRuntimeProbeResolve]
        | object runtimeType sourceTag =>
            cases sourceTag with
            | some tag =>
                have hvalue :=
                  fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent
                    schema
                    (fieldPairSideRuntimeProbeRoot
                      leftChildRootSelectionSet rightChildRootSelectionSet
                      tag)
                    parentType fieldName tag harguments
                    fieldDefinition.outputType
                simp [fieldPairSideRuntimeProbeResolve, hlookup, hvalue]
            | none =>
                have hleftIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    leftField leftArguments parentType fieldName firstArguments
                    laterArguments harguments
                have hrightIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    rightField rightArguments parentType fieldName
                    firstArguments laterArguments harguments
                by_cases hfirstLeft :
                    fieldProbeTarget targetParent leftField leftArguments
                      parentType fieldName firstArguments
                · have hlaterLeft :
                      fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments :=
                    hleftIff.mp hfirstLeft
                  simp [fieldPairSideRuntimeProbeResolve, hlookup, hfirstLeft,
                    hlaterLeft]
                · have hlaterLeft :
                      ¬ fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments := by
                    intro hlater
                    exact hfirstLeft (hleftIff.mpr hlater)
                  by_cases hfirstRight :
                      fieldProbeTarget targetParent rightField rightArguments
                        parentType fieldName firstArguments
                  · have hlaterRight :
                        fieldProbeTarget targetParent rightField rightArguments
                          parentType fieldName laterArguments :=
                      hrightIff.mp hfirstRight
                    simp [fieldPairSideRuntimeProbeResolve, hlookup,
                      hfirstLeft, hlaterLeft, hfirstRight, hlaterRight]
                  · have hlaterRight :
                        ¬ fieldProbeTarget targetParent rightField
                          rightArguments parentType fieldName
                          laterArguments := by
                      intro hlater
                      exact hfirstRight (hrightIff.mpr hlater)
                    simp [fieldPairSideRuntimeProbeResolve, hlookup,
                      hfirstLeft, hlaterLeft, hfirstRight, hlaterRight]

theorem fieldPairSideRuntimeProbeResolvers_left_root
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : Execution.CoercedArgument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
            rightChildRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime).resolve
            targetParent leftField arguments (.object targetParent none)
          = some
              (objectProbeResolverValueWithRuntime leftRuntime
                (some FieldPairProbeTag.left) fieldDefinition.outputType) := by
  intro harguments hlookup
  classical
  have htarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        leftField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairSideRuntimeProbeResolvers, fieldPairSideRuntimeProbeResolve,
    hlookup, htarget]

theorem fieldPairSideRuntimeProbeResolvers_right_root_of_not_left
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField arguments
      -> Execution.CoercedArgument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
            rightChildRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime).resolve
            targetParent rightField arguments (.object targetParent none)
          = some
              (objectProbeResolverValueWithRuntime rightRuntime
                (some FieldPairProbeTag.right) fieldDefinition.outputType) := by
  intro hnotLeft harguments hlookup
  classical
  have hright :
      fieldProbeTarget targetParent rightField rightArguments targetParent
        rightField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairSideRuntimeProbeResolvers, fieldPairSideRuntimeProbeResolve,
    hlookup, hnotLeft, hright]

theorem fieldPairSideRuntimeProbeResolvers_tagged_object_left
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
            rightChildRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime).resolve
            parentType fieldName arguments
            (.object runtimeType (some FieldPairProbeTag.left))
          = some
              (fieldPairProbeHeadResolverValue schema leftChildRootSelectionSet
                parentType fieldName arguments FieldPairProbeTag.left
                fieldDefinition.outputType) := by
  intro hlookup
  simp [fieldPairSideRuntimeProbeResolvers, fieldPairSideRuntimeProbeResolve,
    fieldPairSideRuntimeProbeRoot, hlookup]

theorem fieldPairSideRuntimeProbeResolvers_tagged_object_right
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
            rightChildRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime).resolve
            parentType fieldName arguments
            (.object runtimeType (some FieldPairProbeTag.right))
          = some
              (fieldPairProbeHeadResolverValue schema rightChildRootSelectionSet
                parentType fieldName arguments FieldPairProbeTag.right
                fieldDefinition.outputType) := by
  intro hlookup
  simp [fieldPairSideRuntimeProbeResolvers, fieldPairSideRuntimeProbeResolve,
    fieldPairSideRuntimeProbeRoot, hlookup]

theorem fieldPairSideRuntimeProbeResolvers_tagged_object
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
            rightChildRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime).resolve
            parentType fieldName arguments (.object runtimeType (some tag))
          = some
              (fieldPairProbeHeadResolverValue schema
                (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                  rightChildRootSelectionSet tag)
                parentType fieldName arguments tag fieldDefinition.outputType) := by
  intro hlookup
  cases tag <;>
    simp [fieldPairSideRuntimeProbeResolvers,
      fieldPairSideRuntimeProbeResolve, fieldPairSideRuntimeProbeRoot,
      hlookup]

inductive FieldPairPathLocalProbeRef where
  | root
  | target (tag : FieldPairProbeTag) (selectionSet : List Selection)
  | filler

private def mergeFieldChildOptions
    : Option (List Selection) -> Option (List Selection) -> Option (List Selection)
  | none, none => none
  | some left, none => some left
  | none, some right => some right
  | some left, some right => some (left ++ right)

noncomputable def firstFieldChildByHead?
    {ArgumentType : Type} (targetField : Name) (targetArguments : List ArgumentType)
    : List Selection -> Option (List Selection)
  | [] => none
  | Selection.field _responseName fieldName _arguments _directives childSelectionSet
    :: rest =>
      let restFound := firstFieldChildByHead? targetField targetArguments rest
      if fieldName == targetField then
        mergeFieldChildOptions (some childSelectionSet) restFound
      else
        restFound
  | Selection.inlineFragment _typeCondition _directives childSelectionSet :: rest =>
      mergeFieldChildOptions
        (firstFieldChildByHead? targetField targetArguments childSelectionSet)
        (firstFieldChildByHead? targetField targetArguments rest)
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

def runtimePrunedSelectionSet (schema : Schema) (runtimeType : Name)
    : List Selection -> List Selection
  | [] => []
  | Selection.field responseName fieldName arguments directives childSelectionSet
    :: rest =>
      Selection.field responseName fieldName arguments directives childSelectionSet
      :: runtimePrunedSelectionSet schema runtimeType rest
  | Selection.inlineFragment none _directives childSelectionSet :: rest =>
      runtimePrunedSelectionSet schema runtimeType childSelectionSet
      ++ runtimePrunedSelectionSet schema runtimeType rest
  | Selection.inlineFragment (some typeCondition) _directives childSelectionSet :: rest =>
      if schema.typeIncludesObjectBool typeCondition runtimeType then
        runtimePrunedSelectionSet schema runtimeType childSelectionSet
        ++ runtimePrunedSelectionSet schema runtimeType rest
      else
        runtimePrunedSelectionSet schema runtimeType rest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem runtimePrunedSelectionSet_eq_self_of_allFields
    (schema : Schema) (runtimeType : Name)
    {selectionSet : List Selection}
    : selectionsAllFields selectionSet
      -> runtimePrunedSelectionSet schema runtimeType selectionSet = selectionSet := by
  intro hallFields
  induction selectionSet with
  | nil =>
      simp [runtimePrunedSelectionSet]
  | cons selection rest ih =>
      have hhead : Selection.isField selection :=
        hallFields selection (by simp)
      have htail : selectionsAllFields rest := by
        intro tailSelection htailMem
        exact hallFields tailSelection (by simp [htailMem])
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [runtimePrunedSelectionSet, ih htail]
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hhead

noncomputable def firstFieldChildByHeadAtRuntime?
    {ArgumentType : Type}
    (schema : Schema) (currentRuntimeType childRuntimeType targetField : Name)
    (targetArguments : List ArgumentType)
    : List Selection -> Option (List Selection)
  | [] => none
  | Selection.field _responseName fieldName _arguments _directives childSelectionSet
    :: rest =>
      let restFound :=
        firstFieldChildByHeadAtRuntime? schema currentRuntimeType
          childRuntimeType targetField targetArguments rest
      if fieldName == targetField then
        mergeFieldChildOptions
          (some (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet))
          restFound
      else
        restFound
  | Selection.inlineFragment none _directives childSelectionSet :: rest =>
      mergeFieldChildOptions
        (firstFieldChildByHeadAtRuntime? schema currentRuntimeType
          childRuntimeType targetField targetArguments childSelectionSet)
        (firstFieldChildByHeadAtRuntime? schema currentRuntimeType
          childRuntimeType targetField targetArguments rest)
  | Selection.inlineFragment (some typeCondition) _directives childSelectionSet :: rest =>
      let restFound :=
        firstFieldChildByHeadAtRuntime? schema currentRuntimeType
          childRuntimeType targetField targetArguments rest
      if schema.typeIncludesObjectBool typeCondition currentRuntimeType then
        mergeFieldChildOptions
          (firstFieldChildByHeadAtRuntime? schema currentRuntimeType
            childRuntimeType targetField targetArguments childSelectionSet)
          restFound
      else
        restFound
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private def selectionSetMembersOption : List (List Selection) -> Option (List Selection)
  | [] => none
  | members => some (List.flatten members)

private theorem mergeFieldChildOptions_membersOption (left right : List (List Selection))
    : mergeFieldChildOptions (selectionSetMembersOption left)
        (selectionSetMembersOption right)
      = selectionSetMembersOption (left ++ right) := by
  cases left <;> cases right <;>
    simp [selectionSetMembersOption, mergeFieldChildOptions]

private theorem mergeFieldChildOptions_some_membersOption
    (childSelectionSet : List Selection)
    (members : List (List Selection))
    : mergeFieldChildOptions (some childSelectionSet) (selectionSetMembersOption members)
      = selectionSetMembersOption (childSelectionSet :: members) := by
  cases members <;> simp [selectionSetMembersOption, mergeFieldChildOptions]

noncomputable def fieldChildMembersByHeadAtRuntime
    {ArgumentType : Type}
    (schema : Schema) (currentRuntimeType childRuntimeType targetField : Name)
    (targetArguments : List ArgumentType)
    : List Selection -> List (List Selection)
  | [] => []
  | Selection.field _responseName fieldName _arguments _directives childSelectionSet
    :: rest =>
      let restMembers :=
        fieldChildMembersByHeadAtRuntime schema currentRuntimeType
          childRuntimeType targetField targetArguments rest
      if fieldName == targetField then
        runtimePrunedSelectionSet schema childRuntimeType childSelectionSet :: restMembers
      else
        restMembers
  | Selection.inlineFragment none _directives childSelectionSet :: rest =>
      fieldChildMembersByHeadAtRuntime schema currentRuntimeType
        childRuntimeType targetField targetArguments childSelectionSet
      ++ fieldChildMembersByHeadAtRuntime schema currentRuntimeType
          childRuntimeType targetField targetArguments rest
  | Selection.inlineFragment (some typeCondition) _directives childSelectionSet :: rest =>
      let restMembers :=
        fieldChildMembersByHeadAtRuntime schema currentRuntimeType
          childRuntimeType targetField targetArguments rest
      if schema.typeIncludesObjectBool typeCondition currentRuntimeType then
        fieldChildMembersByHeadAtRuntime schema currentRuntimeType
          childRuntimeType targetField targetArguments childSelectionSet
        ++ restMembers
      else
        restMembers
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

private theorem firstFieldChildByHeadAtRuntime?_eq_fieldChildMembersByHeadAtRuntime
    {ArgumentType : Type}
    (schema : Schema)
    (currentRuntimeType childRuntimeType targetField : Name)
    (targetArguments : List ArgumentType)
    : ∀ selectionSet,
        firstFieldChildByHeadAtRuntime? schema currentRuntimeType
          childRuntimeType targetField targetArguments selectionSet
        = selectionSetMembersOption
            (fieldChildMembersByHeadAtRuntime schema currentRuntimeType
              childRuntimeType targetField targetArguments selectionSet)
  | [] => by
      simp [firstFieldChildByHeadAtRuntime?,
        fieldChildMembersByHeadAtRuntime, selectionSetMembersOption]
  | Selection.field responseName fieldName arguments directives
      childSelectionSet :: rest => by
      classical
      have hrest :=
        firstFieldChildByHeadAtRuntime?_eq_fieldChildMembersByHeadAtRuntime
          schema currentRuntimeType childRuntimeType targetField
          targetArguments rest
      by_cases hfield : fieldName == targetField
      · simp [firstFieldChildByHeadAtRuntime?,
          fieldChildMembersByHeadAtRuntime, hfield, hrest,
          mergeFieldChildOptions_some_membersOption]
      · simp [firstFieldChildByHeadAtRuntime?,
          fieldChildMembersByHeadAtRuntime, hfield, hrest]
  | Selection.inlineFragment none directives childSelectionSet :: rest => by
      classical
      have hchild :=
        firstFieldChildByHeadAtRuntime?_eq_fieldChildMembersByHeadAtRuntime
          schema currentRuntimeType childRuntimeType targetField
          targetArguments childSelectionSet
      have hrest :=
        firstFieldChildByHeadAtRuntime?_eq_fieldChildMembersByHeadAtRuntime
          schema currentRuntimeType childRuntimeType targetField
          targetArguments rest
      simp [firstFieldChildByHeadAtRuntime?,
        fieldChildMembersByHeadAtRuntime, hchild, hrest,
        mergeFieldChildOptions_membersOption]
  | Selection.inlineFragment (some typeCondition) directives childSelectionSet ::
      rest => by
      classical
      have hchild :=
        firstFieldChildByHeadAtRuntime?_eq_fieldChildMembersByHeadAtRuntime
          schema currentRuntimeType childRuntimeType targetField
          targetArguments childSelectionSet
      have hrest :=
        firstFieldChildByHeadAtRuntime?_eq_fieldChildMembersByHeadAtRuntime
          schema currentRuntimeType childRuntimeType targetField
          targetArguments rest
      by_cases hincludes :
          schema.typeIncludesObjectBool typeCondition currentRuntimeType
      · simp [firstFieldChildByHeadAtRuntime?,
          fieldChildMembersByHeadAtRuntime, hincludes, hchild, hrest,
          mergeFieldChildOptions_membersOption]
      · simp [firstFieldChildByHeadAtRuntime?,
          fieldChildMembersByHeadAtRuntime, hincludes, hrest]
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem firstFieldChildByHeadAtRuntime?_eq_of_argumentsEquivalent
    (schema : Schema) (currentRuntimeType childRuntimeType targetField : Name)
    {firstArguments laterArguments : Execution.CoercedArguments}
    (hequivalent
      : Execution.CoercedArgument.argumentsEquivalent firstArguments laterArguments)
    : ∀ selectionSet,
        firstFieldChildByHeadAtRuntime? schema currentRuntimeType
          childRuntimeType targetField firstArguments selectionSet
        = firstFieldChildByHeadAtRuntime? schema currentRuntimeType
            childRuntimeType targetField laterArguments selectionSet
  | [] => by
      simp [firstFieldChildByHeadAtRuntime?]
  | Selection.field responseName fieldName arguments directives
      childSelectionSet :: rest => by
      classical
      have hrest :=
        firstFieldChildByHeadAtRuntime?_eq_of_argumentsEquivalent schema
          currentRuntimeType childRuntimeType targetField hequivalent rest
      simp [firstFieldChildByHeadAtRuntime?, hrest]
  | Selection.inlineFragment none directives childSelectionSet :: rest => by
      classical
      have hchild :=
        firstFieldChildByHeadAtRuntime?_eq_of_argumentsEquivalent schema
          currentRuntimeType childRuntimeType targetField hequivalent
          childSelectionSet
      have hrest :=
        firstFieldChildByHeadAtRuntime?_eq_of_argumentsEquivalent schema
          currentRuntimeType childRuntimeType targetField hequivalent rest
      simp [firstFieldChildByHeadAtRuntime?, hchild, hrest]
  | Selection.inlineFragment (some typeCondition) directives childSelectionSet ::
      rest => by
      classical
      have hchild :=
        firstFieldChildByHeadAtRuntime?_eq_of_argumentsEquivalent schema
          currentRuntimeType childRuntimeType targetField hequivalent
          childSelectionSet
      have hrest :=
        firstFieldChildByHeadAtRuntime?_eq_of_argumentsEquivalent schema
          currentRuntimeType childRuntimeType targetField hequivalent rest
      by_cases hincludes :
          schema.typeIncludesObjectBool typeCondition currentRuntimeType
      · simp [firstFieldChildByHeadAtRuntime?, hincludes, hchild, hrest]
      · simp [firstFieldChildByHeadAtRuntime?, hincludes, hrest]
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

noncomputable def fieldPairPathLocalNextSelectionSet
    {ArgumentType : Type}
    (schema : Schema) (currentRuntimeType childRuntimeType fieldName : Name)
    (arguments : List ArgumentType) (currentSelectionSet : List Selection)
    : List Selection :=
  (firstFieldChildByHeadAtRuntime? schema currentRuntimeType childRuntimeType
    fieldName arguments currentSelectionSet).getD
    []

theorem fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime
    {ArgumentType : Type}
    (schema : Schema) (currentRuntimeType childRuntimeType fieldName : Name)
    (arguments : List ArgumentType) (currentSelectionSet : List Selection)
    : fieldPairPathLocalNextSelectionSet schema currentRuntimeType
        childRuntimeType fieldName arguments currentSelectionSet
      = List.flatten
          (fieldChildMembersByHeadAtRuntime schema currentRuntimeType
            childRuntimeType fieldName arguments currentSelectionSet) := by
  unfold fieldPairPathLocalNextSelectionSet
  rw [firstFieldChildByHeadAtRuntime?_eq_fieldChildMembersByHeadAtRuntime
    schema currentRuntimeType childRuntimeType fieldName arguments
    currentSelectionSet]
  cases
      fieldChildMembersByHeadAtRuntime schema currentRuntimeType
        childRuntimeType fieldName arguments currentSelectionSet <;>
    simp [selectionSetMembersOption]

theorem fieldPairPathLocalNextSelectionSet_eq_of_argumentsEquivalent
    (schema : Schema) (currentRuntimeType childRuntimeType fieldName : Name)
    {firstArguments laterArguments : Execution.CoercedArguments}
    (hequivalent
      : Execution.CoercedArgument.argumentsEquivalent firstArguments laterArguments)
    (currentSelectionSet : List Selection)
    : fieldPairPathLocalNextSelectionSet schema currentRuntimeType
        childRuntimeType fieldName firstArguments currentSelectionSet
      = fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType fieldName laterArguments currentSelectionSet := by
  unfold fieldPairPathLocalNextSelectionSet
  rw [firstFieldChildByHeadAtRuntime?_eq_of_argumentsEquivalent schema
    currentRuntimeType childRuntimeType fieldName hequivalent
    currentSelectionSet]

theorem firstFieldChildByHeadAtRuntime?_eq_of_arguments
    {FirstArgumentType LaterArgumentType : Type}
    (schema : Schema) (currentRuntimeType childRuntimeType fieldName : Name)
    (firstArguments : List FirstArgumentType) (laterArguments : List LaterArgumentType)
    : ∀ currentSelectionSet,
        firstFieldChildByHeadAtRuntime? schema currentRuntimeType childRuntimeType
          fieldName firstArguments currentSelectionSet
        = firstFieldChildByHeadAtRuntime? schema currentRuntimeType
            childRuntimeType fieldName laterArguments currentSelectionSet
  | [] => by simp [firstFieldChildByHeadAtRuntime?]
  | Selection.field responseName candidateFieldName arguments directives
      childSelectionSet :: rest => by
      have hrest := firstFieldChildByHeadAtRuntime?_eq_of_arguments schema
        currentRuntimeType childRuntimeType fieldName firstArguments laterArguments rest
      simp [firstFieldChildByHeadAtRuntime?, hrest]
  | Selection.inlineFragment none directives childSelectionSet :: rest => by
      have hchild := firstFieldChildByHeadAtRuntime?_eq_of_arguments schema
        currentRuntimeType childRuntimeType fieldName firstArguments laterArguments
        childSelectionSet
      have hrest := firstFieldChildByHeadAtRuntime?_eq_of_arguments schema
        currentRuntimeType childRuntimeType fieldName firstArguments laterArguments rest
      simp [firstFieldChildByHeadAtRuntime?, hchild, hrest]
  | Selection.inlineFragment (some typeCondition) directives childSelectionSet ::
      rest => by
      have hchild := firstFieldChildByHeadAtRuntime?_eq_of_arguments schema
        currentRuntimeType childRuntimeType fieldName firstArguments laterArguments
        childSelectionSet
      have hrest := firstFieldChildByHeadAtRuntime?_eq_of_arguments schema
        currentRuntimeType childRuntimeType fieldName firstArguments laterArguments rest
      simp [firstFieldChildByHeadAtRuntime?, hchild, hrest]
termination_by currentSelectionSet => SelectionSet.size currentSelectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem fieldPairPathLocalNextSelectionSet_eq_of_arguments
    {FirstArgumentType LaterArgumentType : Type}
    (schema : Schema) (currentRuntimeType childRuntimeType fieldName : Name)
    (firstArguments : List FirstArgumentType) (laterArguments : List LaterArgumentType)
    (currentSelectionSet : List Selection)
    : fieldPairPathLocalNextSelectionSet schema currentRuntimeType
        childRuntimeType fieldName firstArguments currentSelectionSet
      = fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType fieldName laterArguments currentSelectionSet := by
  unfold fieldPairPathLocalNextSelectionSet
  rw [firstFieldChildByHeadAtRuntime?_eq_of_arguments schema currentRuntimeType
    childRuntimeType fieldName firstArguments laterArguments currentSelectionSet]

theorem firstFieldChildByHead?_eq_of_argumentsEquivalent
    (targetField : Name) {firstArguments laterArguments : Execution.CoercedArguments}
    : Execution.CoercedArgument.argumentsEquivalent firstArguments laterArguments
      -> ∀ selectionSet,
          firstFieldChildByHead? targetField firstArguments selectionSet
          = firstFieldChildByHead? targetField laterArguments selectionSet
  | hequivalent, [] => by
      simp [firstFieldChildByHead?]
  | hequivalent,
      Selection.field responseName fieldName arguments directives
        childSelectionSet :: rest => by
      classical
      have hrest :=
        firstFieldChildByHead?_eq_of_argumentsEquivalent targetField
          hequivalent rest
      simp [firstFieldChildByHead?, hrest]
  | hequivalent,
      Selection.inlineFragment typeCondition directives childSelectionSet ::
        rest => by
      classical
      have hchild :=
        firstFieldChildByHead?_eq_of_argumentsEquivalent targetField
          hequivalent childSelectionSet
      have hrest :=
        firstFieldChildByHead?_eq_of_argumentsEquivalent targetField
          hequivalent rest
      simp [firstFieldChildByHead?, hchild, hrest]
termination_by _ selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [SelectionSet.size, Selection.size]
    omega

theorem firstFieldChildByHead?_field_mem_append_context
    {targetField responseName : Name}
    {targetArguments : Execution.CoercedArguments} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> ∃ mergedSelectionSet pref suff,
          firstFieldChildByHead? targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ mergedSelectionSet = pref ++ childSelectionSet ++ suff := by
  intro hmem
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      cases head with
      | field headResponseName headFieldName headArguments headDirectives
          headChildSelectionSet =>
          classical
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            have hfield : targetField == targetField := by
              simp
            cases hrest : firstFieldChildByHead? targetField targetArguments rest with
            | none =>
                refine ⟨childSelectionSet, [], [], ?_, by simp⟩
                simp [firstFieldChildByHead?, hrest,
                  mergeFieldChildOptions]
            | some restMerged =>
                refine ⟨childSelectionSet ++ restMerged, [], restMerged, ?_, by simp⟩
                simp [firstFieldChildByHead?, hrest,
                  mergeFieldChildOptions]
          · rcases ih htail with
              ⟨restMerged, pref, suff, hrestMerged, hcontext⟩
            by_cases hfield : headFieldName == targetField
            · refine ⟨
                headChildSelectionSet ++ restMerged,
                headChildSelectionSet ++ pref,
                suff,
                ?_,
                ?_
              ⟩
              · simp [firstFieldChildByHead?, hfield, hrestMerged,
                  mergeFieldChildOptions]
              · rw [hcontext]
                simp [List.append_assoc]
            · refine ⟨restMerged, pref, suff, ?_, hcontext⟩
              simp [firstFieldChildByHead?, hfield, hrestMerged]
      | inlineFragment typeCondition headDirectives headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · rcases ih htail with
              ⟨restMerged, pref, suff, hrestMerged, hcontext⟩
            cases hchild
                  : firstFieldChildByHead? targetField targetArguments
                      headChildSelectionSet with
            | none =>
                refine ⟨restMerged, pref, suff, ?_, hcontext⟩
                simp [firstFieldChildByHead?, hchild, hrestMerged,
                  mergeFieldChildOptions]
            | some childMerged =>
                refine ⟨childMerged ++ restMerged, childMerged ++ pref, suff, ?_, ?_⟩
                · simp [firstFieldChildByHead?, hchild, hrestMerged,
                    mergeFieldChildOptions]
                · rw [hcontext]
                  simp [List.append_assoc]

theorem firstFieldChildByHeadAtRuntime?_field_mem_append_context
    {TargetArgumentType : Type}
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments : List TargetArgumentType} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> ∃ mergedSelectionSet pref suff,
          firstFieldChildByHeadAtRuntime? schema currentRuntimeType
              childRuntimeType targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ mergedSelectionSet
            = pref
              ++ runtimePrunedSelectionSet schema childRuntimeType childSelectionSet
              ++ suff := by
  intro hmem
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      cases head with
      | field headResponseName headFieldName headArguments headDirectives
          headChildSelectionSet =>
          classical
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            have hfield : targetField == targetField := by
              simp
            cases hrest
                  : firstFieldChildByHeadAtRuntime? schema currentRuntimeType
                      childRuntimeType targetField targetArguments rest with
            | none =>
                refine ⟨
                  runtimePrunedSelectionSet schema childRuntimeType childSelectionSet,
                  [],
                  [],
                  ?_,
                  by simp
                ⟩
                simp [firstFieldChildByHeadAtRuntime?, hrest,
                  mergeFieldChildOptions]
            | some restMerged =>
                refine ⟨
                  runtimePrunedSelectionSet schema childRuntimeType childSelectionSet
                  ++ restMerged,
                  [],
                  restMerged,
                  ?_,
                  by simp
                ⟩
                simp [firstFieldChildByHeadAtRuntime?, hrest,
                  mergeFieldChildOptions]
          · rcases ih htail with
              ⟨restMerged, pref, suff, hrestMerged, hcontext⟩
            by_cases hfield : headFieldName == targetField
            · refine ⟨
                runtimePrunedSelectionSet schema childRuntimeType headChildSelectionSet
                ++ restMerged,
                runtimePrunedSelectionSet schema childRuntimeType headChildSelectionSet
                ++ pref,
                suff,
                ?_,
                ?_
              ⟩
              · simp [firstFieldChildByHeadAtRuntime?, hfield,
                  hrestMerged, mergeFieldChildOptions]
              · rw [hcontext]
                simp [List.append_assoc]
            · refine ⟨restMerged, pref, suff, ?_, hcontext⟩
              simp [firstFieldChildByHeadAtRuntime?, hfield, hrestMerged]
      | inlineFragment typeCondition headDirectives headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · rcases ih htail with
              ⟨restMerged, pref, suff, hrestMerged, hcontext⟩
            cases typeCondition with
            | none =>
                cases hchild
                      : firstFieldChildByHeadAtRuntime? schema currentRuntimeType
                          childRuntimeType targetField targetArguments
                          headChildSelectionSet with
                | none =>
                    refine ⟨restMerged, pref, suff, ?_, hcontext⟩
                    simp [firstFieldChildByHeadAtRuntime?, hchild,
                      hrestMerged, mergeFieldChildOptions]
                | some childMerged =>
                    refine ⟨childMerged ++ restMerged, childMerged ++ pref, suff, ?_, ?_⟩
                    · simp [firstFieldChildByHeadAtRuntime?, hchild,
                        hrestMerged, mergeFieldChildOptions]
                    · rw [hcontext]
                      simp [List.append_assoc]
            | some typeCondition =>
                by_cases hincludes :
                    schema.typeIncludesObjectBool typeCondition
                      currentRuntimeType
                · cases hchild
                        : firstFieldChildByHeadAtRuntime? schema currentRuntimeType
                            childRuntimeType targetField targetArguments
                            headChildSelectionSet with
                  | none =>
                      refine ⟨restMerged, pref, suff, ?_, hcontext⟩
                      simp [firstFieldChildByHeadAtRuntime?, hincludes,
                        hchild, hrestMerged, mergeFieldChildOptions]
                  | some childMerged =>
                      refine ⟨
                        childMerged ++ restMerged,
                        childMerged ++ pref,
                        suff,
                        ?_,
                        ?_
                      ⟩
                      · simp [firstFieldChildByHeadAtRuntime?, hincludes,
                          hchild, hrestMerged, mergeFieldChildOptions]
                      · rw [hcontext]
                        simp [List.append_assoc]
                · refine ⟨restMerged, pref, suff, ?_, hcontext⟩
                  simp [firstFieldChildByHeadAtRuntime?, hincludes,
                    hrestMerged]

noncomputable def fieldPairPathLocalProbeHeadResolverValue
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName : Name) (arguments : Execution.CoercedArguments)
    (tag : FieldPairProbeTag)
    : TypeRef -> Execution.ResolverValue FieldPairPathLocalProbeRef
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName
            (FieldPairPathLocalProbeRef.target tag
              (fieldPairPathLocalNextSelectionSet schema parentType
                typeName fieldName arguments currentSelectionSet))
        else
          match abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType currentSelectionSet with
          | some runtimeType =>
              .object runtimeType
                (FieldPairPathLocalProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet))
          | none =>
              .object typeName (FieldPairPathLocalProbeRef.target tag [])
      else
        .scalar tag.scalar
  | .list inner =>
      .list
        [fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
          parentType fieldName arguments tag inner]
  | .nonNull inner =>
      fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
        parentType fieldName arguments tag inner

theorem fieldPairPathLocalProbeHeadResolverValue_eq_of_argumentsEquivalent
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName : Name)
    {firstArguments laterArguments : Execution.CoercedArguments}
    (tag : FieldPairProbeTag)
    : Execution.CoercedArgument.argumentsEquivalent firstArguments laterArguments
      -> ∀ outputType,
          fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
            parentType fieldName firstArguments tag outputType
          = fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
              parentType fieldName laterArguments tag outputType
  | hequivalent, .named typeName => by
      have hnext :
          ∀ runtimeType,
            fieldPairPathLocalNextSelectionSet schema parentType runtimeType
              fieldName firstArguments currentSelectionSet =
            fieldPairPathLocalNextSelectionSet schema parentType runtimeType
              fieldName laterArguments currentSelectionSet := by
        intro runtimeType
        exact
          fieldPairPathLocalNextSelectionSet_eq_of_argumentsEquivalent
            schema parentType runtimeType fieldName hequivalent
            currentSelectionSet
      by_cases hcomposite :
          (TypeRef.named typeName).isCompositeBool schema
      · by_cases hobject : objectTypeNameBool schema typeName
        · simp [fieldPairPathLocalProbeHeadResolverValue, hcomposite,
            hobject, hnext]
        · simp [fieldPairPathLocalProbeHeadResolverValue, hcomposite,
            hobject, hnext]
      · simp [fieldPairPathLocalProbeHeadResolverValue, hcomposite]
  | hequivalent, .list inner => by
      have hinner :=
        fieldPairPathLocalProbeHeadResolverValue_eq_of_argumentsEquivalent
          schema currentSelectionSet parentType fieldName tag hequivalent inner
      simp [fieldPairPathLocalProbeHeadResolverValue, hinner]
  | hequivalent, .nonNull inner => by
      exact
        fieldPairPathLocalProbeHeadResolverValue_eq_of_argumentsEquivalent
          schema currentSelectionSet parentType fieldName tag hequivalent inner

theorem fieldPairPathLocalProbeHeadResolverValue_eq_of_arguments (schema : Schema)
    (currentSelectionSet : List Selection) (parentType fieldName : Name)
    (firstArguments laterArguments : Execution.CoercedArguments) (tag : FieldPairProbeTag)
    : ∀ outputType,
        fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
          parentType fieldName firstArguments tag outputType
        = fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
            parentType fieldName laterArguments tag outputType
  | .named typeName => by
      have hnext : ∀ runtimeType,
          fieldPairPathLocalNextSelectionSet schema parentType runtimeType
              fieldName firstArguments currentSelectionSet =
            fieldPairPathLocalNextSelectionSet schema parentType runtimeType
              fieldName laterArguments currentSelectionSet := by
        intro runtimeType
        exact fieldPairPathLocalNextSelectionSet_eq_of_arguments schema
          parentType runtimeType fieldName firstArguments laterArguments
          currentSelectionSet
      simp [fieldPairPathLocalProbeHeadResolverValue, hnext]
  | .list inner => by
      simp [fieldPairPathLocalProbeHeadResolverValue,
        fieldPairPathLocalProbeHeadResolverValue_eq_of_arguments schema
          currentSelectionSet parentType fieldName firstArguments laterArguments
          tag inner]
  | .nonNull inner =>
      fieldPairPathLocalProbeHeadResolverValue_eq_of_arguments schema
        currentSelectionSet parentType fieldName firstArguments laterArguments
        tag inner

theorem fieldPairPathLocalProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName : Name) (arguments : Execution.CoercedArguments)
    (tag : FieldPairProbeTag)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = false
        -> fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
              parentType fieldName arguments tag outputType
            = leafProbeResolverValue outputType tag.scalar
  | .named typeName, hleaf => by
      have hleafNamed :
          (TypeRef.named typeName).isCompositeBool schema = false := by
        simpa [TypeRef.namedType] using hleaf
      simp [fieldPairPathLocalProbeHeadResolverValue, leafProbeResolverValue,
        hleafNamed]
  | .list inner, hleaf => by
      have hinner :=
        fieldPairPathLocalProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
          schema currentSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hleaf)
      simp [fieldPairPathLocalProbeHeadResolverValue, leafProbeResolverValue,
        hinner]
  | .nonNull inner, hleaf => by
      exact
        fieldPairPathLocalProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
          schema currentSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hleaf)

theorem
    fieldPairPathLocalProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (currentSelectionSet : List Selection) (parentType fieldName : Name)
    (arguments : Execution.CoercedArguments) (tag : FieldPairProbeTag)
    : ∀ outputType,
        objectTypeNameBool schema outputType.namedType = true
        -> fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
              parentType fieldName arguments tag outputType
            = objectProbeResolverValueWithRuntime outputType.namedType
                (FieldPairPathLocalProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    outputType.namedType fieldName arguments currentSelectionSet))
                outputType
  | .named typeName, hobject => by
      have hobjectNamed :
          objectTypeNameBool schema typeName = true := by
        simpa [TypeRef.namedType] using hobject
      have hcomposite :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        unfold objectTypeNameBool at hobjectNamed
        unfold TypeRef.isCompositeBool TypeRef.namedType
        cases hlookup : schema.lookupType typeName with
        | none =>
            simp [hlookup] at hobjectNamed
        | some typeDefinition =>
            cases typeDefinition <;> simp [hlookup] at hobjectNamed ⊢
      simp [fieldPairPathLocalProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType, hcomposite,
        hobjectNamed]
  | .list inner, hobject => by
      have hinner :=
        fieldPairPathLocalProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hobject)
      simpa [fieldPairPathLocalProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType] using hinner
  | .nonNull inner, hobject => by
      exact
        fieldPairPathLocalProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hobject)

theorem
    fieldPairPathLocalProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (arguments : Execution.CoercedArguments)
    (tag : FieldPairProbeTag)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = true
        -> objectTypeNameBool schema outputType.namedType = false
        -> abstractRuntimeForFieldDeep? schema parentType fieldName
              parentType currentSelectionSet
            = some runtimeType
        -> fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
              parentType fieldName arguments tag outputType
            = objectProbeResolverValueWithRuntime runtimeType
                (FieldPairPathLocalProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet))
                outputType
  | .named typeName, hcomposite, hnonObject, hruntime => by
      have hcompositeNamed :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        simpa [TypeRef.namedType] using hcomposite
      have hnonObjectNamed :
          objectTypeNameBool schema typeName = false := by
        simpa [TypeRef.namedType] using hnonObject
      simp [fieldPairPathLocalProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, hcompositeNamed,
        hnonObjectNamed, hruntime]
  | .list inner, hcomposite, hnonObject, hruntime => by
      have hinner :=
        fieldPairPathLocalProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName runtimeType
          arguments tag inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject) hruntime
      simpa [fieldPairPathLocalProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType] using hinner
  | .nonNull inner, hcomposite, hnonObject, hruntime => by
      exact
        fieldPairPathLocalProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
          schema currentSelectionSet parentType fieldName runtimeType
          arguments tag inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject) hruntime

theorem fieldPairPathLocalProbeHeadResolverValue_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (currentSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (arguments : Execution.CoercedArguments)
    (tag : FieldPairProbeTag) (outputType : TypeRef)
    : ((objectTypeNameBool schema outputType.namedType = true
          ∧ runtimeType = outputType.namedType)
        ∨ ((TypeRef.named outputType.namedType).isCompositeBool schema = true
            ∧ objectTypeNameBool schema outputType.namedType = false
            ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                parentType currentSelectionSet
              = some runtimeType))
      -> fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
            parentType fieldName arguments tag outputType
          = objectProbeResolverValueWithRuntime runtimeType
              (FieldPairPathLocalProbeRef.target tag
                (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
                  fieldName arguments currentSelectionSet))
              outputType := by
  intro hcase
  rcases hcase with hobject | habstract
  · rcases hobject with ⟨hobject, hruntime⟩
    subst runtimeType
    exact
      fieldPairPathLocalProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
        schema currentSelectionSet parentType fieldName arguments tag
        outputType hobject
  · exact
      fieldPairPathLocalProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
        schema currentSelectionSet parentType fieldName runtimeType arguments
        tag outputType habstract.1 habstract.2.1 habstract.2.2

noncomputable def fieldPairPathLocalProbeResolve
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime parentType fieldName : Name)
    (arguments : Execution.CoercedArguments)
    (source : Execution.ResolverValue FieldPairPathLocalProbeRef)
    : Option (Execution.ResolverValue FieldPairPathLocalProbeRef) := by
  classical
  exact
    match source with
    | .object _ (FieldPairPathLocalProbeRef.target tag currentSelectionSet) =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            some
              (fieldPairPathLocalProbeHeadResolverValue schema
                currentSelectionSet parentType fieldName arguments tag
                fieldDefinition.outputType)
    | .object _ FieldPairPathLocalProbeRef.root =>
        match schema.lookupField parentType fieldName with
        | none => none
        | some fieldDefinition =>
            if fieldProbeTarget targetParent leftField leftArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime leftRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                    leftInitialSelectionSet)
                  fieldDefinition.outputType)
            else if fieldProbeTarget targetParent rightField rightArguments
                parentType fieldName arguments then
              some
                (objectProbeResolverValueWithRuntime rightRuntime
                  (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                    rightInitialSelectionSet)
                  fieldDefinition.outputType)
            else
              none
    | .object _ FieldPairPathLocalProbeRef.filler => none
    | _ => none

noncomputable def fieldPairPathLocalProbeResolvers
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    : Execution.Resolvers FieldPairPathLocalProbeRef where
  resolve parentType fieldName arguments source :=
    fieldPairPathLocalProbeResolve schema leftInitialSelectionSet
      rightInitialSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime parentType
      fieldName arguments source
  resolve_argumentsEquivalent := by
    intro parentType fieldName firstArguments laterArguments source
      harguments
    classical
    cases hlookup : schema.lookupField parentType fieldName with
    | none =>
        cases source <;>
          simp [fieldPairPathLocalProbeResolve, hlookup]
    | some fieldDefinition =>
        cases source with
        | null =>
            simp [fieldPairPathLocalProbeResolve]
        | scalar value =>
            simp [fieldPairPathLocalProbeResolve]
        | list values =>
            simp [fieldPairPathLocalProbeResolve]
        | object runtimeType ref =>
            cases ref with
            | root =>
                have hleftIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    leftField leftArguments parentType fieldName
                    firstArguments laterArguments harguments
                have hrightIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    rightField rightArguments parentType fieldName
                    firstArguments laterArguments harguments
                by_cases hfirstLeft :
                    fieldProbeTarget targetParent leftField leftArguments
                      parentType fieldName firstArguments
                · have hlaterLeft :
                      fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments :=
                    hleftIff.mp hfirstLeft
                  simp [fieldPairPathLocalProbeResolve, hlookup, hfirstLeft,
                    hlaterLeft]
                · have hlaterLeft :
                      ¬ fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments := by
                    intro hlater
                    exact hfirstLeft (hleftIff.mpr hlater)
                  by_cases hfirstRight :
                      fieldProbeTarget targetParent rightField rightArguments
                        parentType fieldName firstArguments
                  · have hlaterRight :
                        fieldProbeTarget targetParent rightField
                          rightArguments parentType fieldName
                          laterArguments :=
                      hrightIff.mp hfirstRight
                    simp [fieldPairPathLocalProbeResolve, hlookup,
                      hfirstLeft, hlaterLeft, hfirstRight, hlaterRight]
                  · have hlaterRight :
                        ¬ fieldProbeTarget targetParent rightField
                          rightArguments parentType fieldName
                          laterArguments := by
                      intro hlater
                      exact hfirstRight (hrightIff.mpr hlater)
                    simp [fieldPairPathLocalProbeResolve, hlookup,
                      hfirstLeft, hlaterLeft, hfirstRight, hlaterRight]
            | target tag currentSelectionSet =>
                have hvalue :=
                  fieldPairPathLocalProbeHeadResolverValue_eq_of_argumentsEquivalent
                    schema currentSelectionSet parentType fieldName tag
                    harguments fieldDefinition.outputType
                simp [fieldPairPathLocalProbeResolve, hlookup, hvalue]
            | filler =>
                simp [fieldPairPathLocalProbeResolve]

theorem fieldPairPathLocalProbeResolvers_left_root
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : Execution.CoercedArgument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime).resolve
            targetParent leftField arguments
            (.object targetParent FieldPairPathLocalProbeRef.root)
          = some
              (objectProbeResolverValueWithRuntime leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)
                fieldDefinition.outputType) := by
  intro harguments hlookup
  classical
  have htarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        leftField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairPathLocalProbeResolvers, fieldPairPathLocalProbeResolve,
    hlookup, htarget]

theorem fieldPairPathLocalProbeResolvers_right_root_of_not_left
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField arguments
      -> Execution.CoercedArgument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
            rightInitialSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime).resolve
            targetParent rightField arguments
            (.object targetParent FieldPairPathLocalProbeRef.root)
          = some
              (objectProbeResolverValueWithRuntime rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)
                fieldDefinition.outputType) := by
  intro hnotLeft harguments hlookup
  classical
  have hright :
      fieldProbeTarget targetParent rightField rightArguments targetParent
        rightField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairPathLocalProbeResolvers, fieldPairPathLocalProbeResolve,
    hlookup, hnotLeft, hright]

theorem fieldPairPathLocalProbeResolvers_tagged_object
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> Execution.coerceAndResolveFieldValue schema
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues fieldDefinition parentType fieldName arguments
            (.object runtimeType
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
          = some
              (fieldPairPathLocalProbeHeadResolverValue schema currentSelectionSet
                parentType fieldName
                (Execution.coercedArgumentsForField schema variableValues
                  parentType fieldName arguments)
                tag fieldDefinition.outputType) := by
  intro hlookup hcoercion
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨coercedArguments, hcoercionResult⟩
  simp [fieldPairPathLocalProbeResolvers, fieldPairPathLocalProbeResolve,
    Execution.resolveFieldValue, hlookup, hcoercionResult,
    Execution.coercedArgumentsForField]

theorem executeField_fieldPairPathLocalProbe_tagged_object_leaf (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues (fuel + 1)
            (.object sourceRuntimeType
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  leafProbeResponseValue fieldDefinition.outputType tag.scalar
                )],
                0
              ) := by
  intro hlookup hcoercion hfuel hleaf
  have hresolve :
      Execution.coerceAndResolveFieldValue schema
        (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime)
        variableValues fieldDefinition parentType fieldName arguments
        (.object sourceRuntimeType
          (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
      =
      some
        (leafProbeResolverValue
          (ObjectRef := FieldPairPathLocalProbeRef)
          fieldDefinition.outputType tag.scalar) := by
    rw [fieldPairPathLocalProbeResolvers_tagged_object schema
      leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet variableValues
      targetParent leftField rightField parentType fieldName
      sourceRuntimeType leftArguments rightArguments arguments leftRuntime
      rightRuntime tag fieldDefinition hlookup hcoercion]
    rw [fieldPairPathLocalProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
      schema currentSelectionSet parentType fieldName
      (Execution.coercedArgumentsForField schema variableValues parentType
        fieldName arguments)
      tag
      fieldDefinition.outputType hleaf]
  exact
    executeField_leafProbe_singleton_of_resolve_fuel_ge schema
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      variableValues fuel
      (.object sourceRuntimeType
        (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition tag.scalar hlookup hresolve hfuel hleaf

theorem executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1)
            (projectionTargetResolverValue
              (.object sourceRuntimeType
                (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  leafProbeResponseValue fieldDefinition.outputType tag.scalar
                )],
                0
              ) := by
  intro hlookup hcoercion hfuel hleaf
  let base :=
    fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime
  have hprojection :=
    executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues targetParent leftField
      rightField leftArguments rightArguments (fuel + 1)
      (.object sourceRuntimeType
        (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
      responseName
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := childSelectionSet
      }]
  have hbase :=
    executeField_fieldPairPathLocalProbe_tagged_object_leaf
      schema leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet variableValues fuel targetParent leftField
      rightField parentType fieldName sourceRuntimeType responseName
      leftArguments rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition hlookup hcoercion hfuel hleaf
  simpa [base, hbase] using hprojection

theorem executeField_fieldPairPathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType currentSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues (fuel + 1)
            (.object sourceRuntimeType
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                    rightInitialSelectionSet targetParent leftField rightField
                    leftArguments rightArguments leftRuntime rightRuntime)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType
                  (.object runtimeType
                    (FieldPairPathLocalProbeRef.target tag
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        runtimeType fieldName
                        (Execution.coercedArgumentsForField schema variableValues
                          parentType fieldName arguments) currentSelectionSet)))
                  childSelectionSet)) := by
  intro hlookup hcoercion hruntime hinclude hfuel
  have hresolve :
      Execution.coerceAndResolveFieldValue schema
        (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
          rightInitialSelectionSet targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime)
        variableValues fieldDefinition parentType fieldName arguments
        (.object sourceRuntimeType
          (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
      =
      some
        (objectProbeResolverValueWithRuntime runtimeType
          (FieldPairPathLocalProbeRef.target tag
            (fieldPairPathLocalNextSelectionSet schema parentType
              runtimeType fieldName
              (Execution.coercedArgumentsForField schema variableValues
                parentType fieldName arguments)
              currentSelectionSet))
          fieldDefinition.outputType) := by
    rw [fieldPairPathLocalProbeResolvers_tagged_object schema
      leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet variableValues
      targetParent leftField rightField parentType fieldName
      sourceRuntimeType leftArguments rightArguments arguments leftRuntime
      rightRuntime tag fieldDefinition hlookup hcoercion]
    rw [fieldPairPathLocalProbeHeadResolverValue_eq_objectProbeResolverValueWithRuntime
      schema currentSelectionSet parentType fieldName runtimeType
      (Execution.coercedArgumentsForField schema variableValues parentType
        fieldName arguments)
      tag fieldDefinition.outputType hruntime]
  exact
    executeField_objectProbeWithRuntime_response_of_fuel_ge schema
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      variableValues fuel
      (.object sourceRuntimeType
        (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition runtimeType
      (FieldPairPathLocalProbeRef.target tag
        (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
          fieldName
          (Execution.coercedArgumentsForField schema variableValues parentType
            fieldName arguments)
          currentSelectionSet))
      hlookup hresolve hinclude hfuel

theorem
    executeField_fieldPairPathLocalProbe_tagged_object_objectProbe_ok_of_child_response
    (schema : Schema)
    (leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (responseFields : List (Name × Execution.ResponseValue))
    (childErrors : Nat)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType currentSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (.object runtimeType
              (FieldPairPathLocalProbeRef.target tag
                (fieldPairPathLocalNextSelectionSet schema parentType
                  runtimeType fieldName
                  (Execution.coercedArgumentsForField schema variableValues
                    parentType fieldName arguments) currentSelectionSet)))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              variableValues (fuel + 1)
              (.object sourceRuntimeType
                (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hlookup hcoercion hruntime hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairPathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
      schema leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet variableValues fuel targetParent leftField
      rightField parentType fieldName sourceRuntimeType responseName
      leftArguments rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition runtimeType hlookup hcoercion hruntime
      hinclude hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

theorem
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition) (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType currentSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1)
            (projectionTargetResolverValue
              (.object sourceRuntimeType
                (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairPathLocalProbeRef.target tag
                        (fieldPairPathLocalNextSelectionSet schema parentType
                          runtimeType fieldName arguments currentSelectionSet))))
                  childSelectionSet)) := by
  intro hlookup hcoercion hruntime hinclude hfuel
  rw [fieldPairPathLocalNextSelectionSet_eq_of_arguments schema parentType runtimeType
    fieldName arguments
      (Execution.coercedArgumentsForField schema variableValues parentType fieldName
        arguments) currentSelectionSet]
  let base :=
    fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime
  have hprojection :=
    executeField_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues targetParent leftField
      rightField leftArguments rightArguments (fuel + 1)
      (.object sourceRuntimeType
        (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
      responseName
      [{
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := childSelectionSet
      }]
  have hbase :=
    executeField_fieldPairPathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
      schema leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet variableValues fuel targetParent leftField
      rightField parentType fieldName sourceRuntimeType responseName
      leftArguments rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition runtimeType hlookup hcoercion hruntime
      hinclude hfuel
  have hchildProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet base variableValues
      (fuel - leafProbeFuel fieldDefinition.outputType) targetParent leftField
      rightField leftArguments rightArguments runtimeType
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target tag
          (fieldPairPathLocalNextSelectionSet schema parentType runtimeType
            fieldName
            (Execution.coercedArgumentsForField schema variableValues parentType
              fieldName arguments)
            currentSelectionSet)))
      childSelectionSet
  simpa [base, hbase, hchildProjection] using hprojection

theorem
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_ok_of_child_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition) (runtimeType : Name)
    (responseFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType currentSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target tag
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    runtimeType fieldName arguments currentSelectionSet))))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                  rightInitialSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hlookup hcoercion hruntime hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet
      currentSelectionSet variableValues fuel targetParent leftField
      rightField parentType fieldName sourceRuntimeType responseName
      leftArguments rightArguments arguments leftRuntime rightRuntime tag
      childSelectionSet fieldDefinition runtimeType hlookup hcoercion hruntime
      hinclude hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

theorem
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (selectionSet : List Selection)
    : (∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
        -> ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            ∧ (Execution.coerceArgumentValues schema variableValues
                fieldDefinition.arguments arguments).isSuccess
              = true
            ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
            ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                  = false
                ∨ ∃ childRuntimeType responseFields childErrors,
                    (((objectTypeNameBool schema fieldDefinition.outputType.namedType
                            = true
                          ∧ childRuntimeType = fieldDefinition.outputType.namedType)
                        ∨ ((TypeRef.named
                                fieldDefinition.outputType.namedType).isCompositeBool
                                schema
                              = true
                            ∧ objectTypeNameBool schema
                                fieldDefinition.outputType.namedType
                              = false
                            ∧ abstractRuntimeForFieldDeep? schema parentType
                                fieldName parentType currentSelectionSet
                              = some childRuntimeType))
                      ∧ schema.typeIncludesObjectBool
                          fieldDefinition.outputType.namedType childRuntimeType
                        = true
                      ∧ Execution.executeSelectionSetAsResponse schema
                          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                            (fieldPairPathLocalProbeResolvers schema
                              leftInitialSelectionSet rightInitialSelectionSet
                              targetParent leftField rightField leftArguments
                              rightArguments leftRuntime rightRuntime)
                            targetParent leftField rightField leftArguments
                            rightArguments)
                          variableValues
                          (fuel - leafProbeFuel fieldDefinition.outputType)
                          childRuntimeType
                          (projectionTargetResolverValue
                            (.object childRuntimeType
                              (FieldPairPathLocalProbeRef.target tag
                                (fieldPairPathLocalNextSelectionSet schema
                                  parentType childRuntimeType fieldName
                                  arguments currentSelectionSet))))
                          childSelectionSet
                        = ({
                              data := Execution.ResponseValue.object responseFields,
                              errors := childErrors
                            }
                            : Execution.Response))))
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                  (fieldPairPathLocalProbeResolvers schema
                    leftInitialSelectionSet rightInitialSelectionSet
                    targetParent leftField rightField leftArguments
                    rightArguments leftRuntime rightRuntime)
                  targetParent leftField rightField leftArguments
                  rightArguments)
                variableValues (fuel + 1)
                (projectionTargetResolverValue
                  (.object sourceRuntimeType
                    (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
                responseName
                [{
                  parentType := parentType
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hchildren responseName fieldName arguments directives
    childSelectionSet hmem
  rcases hchildren responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hcoercion, hfuel, hleafOrChild⟩
  rcases hleafOrChild with hleaf | hchild
  · refine ⟨leafProbeResponseValue fieldDefinition.outputType tag.scalar, 0, ?_⟩
    exact
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_leaf
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType fieldName
        sourceRuntimeType responseName leftArguments rightArguments
        arguments leftRuntime rightRuntime tag childSelectionSet
        fieldDefinition hlookup hcoercion hfuel hleaf
  · rcases hchild with
      ⟨childRuntimeType, responseFields, childErrors, hruntime, hinclude,
        hchildResponse⟩
    rcases
        executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_ok_of_child_response
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet currentSelectionSet variableValues fuel
          targetParent leftField rightField parentType fieldName
          sourceRuntimeType responseName leftArguments rightArguments
          arguments leftRuntime rightRuntime tag childSelectionSet
          fieldDefinition childRuntimeType responseFields childErrors hlookup
          hcoercion hruntime hinclude hfuel hchildResponse with
      ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
    exact ⟨responseValue, fieldErrors, hexecute⟩

theorem
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_of_field_children
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (selectionSet : List Selection)
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
                ∧ (Execution.coerceArgumentValues schema variableValues
                    fieldDefinition.arguments arguments).isSuccess
                  = true
                ∧ leafProbeFuel fieldDefinition.outputType ≤ fuel
                ∧ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                        schema
                      = false
                    ∨ ∃ childRuntimeType responseFields childErrors,
                        (((objectTypeNameBool schema fieldDefinition.outputType.namedType
                                = true
                              ∧ childRuntimeType = fieldDefinition.outputType.namedType)
                            ∨ ((TypeRef.named
                                    fieldDefinition.outputType.namedType).isCompositeBool
                                    schema
                                  = true
                                ∧ objectTypeNameBool schema
                                    fieldDefinition.outputType.namedType
                                  = false
                                ∧ abstractRuntimeForFieldDeep? schema parentType
                                    fieldName parentType currentSelectionSet
                                  = some childRuntimeType))
                          ∧ schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntimeType
                            = true
                          ∧ Execution.executeSelectionSetAsResponse schema
                              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                                (fieldPairPathLocalProbeResolvers schema
                                  leftInitialSelectionSet rightInitialSelectionSet
                                  targetParent leftField rightField leftArguments
                                  rightArguments leftRuntime rightRuntime)
                                targetParent leftField rightField leftArguments
                                rightArguments)
                              variableValues
                              (fuel - leafProbeFuel fieldDefinition.outputType)
                              childRuntimeType
                              (projectionTargetResolverValue
                                (.object childRuntimeType
                                  (FieldPairPathLocalProbeRef.target tag
                                    (fieldPairPathLocalNextSelectionSet schema
                                      parentType childRuntimeType fieldName
                                      arguments currentSelectionSet))))
                              childSelectionSet
                            = ({
                                  data := Execution.ResponseValue.object responseFields,
                                  errors := childErrors
                                }
                                : Execution.Response))))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema
                leftInitialSelectionSet rightInitialSelectionSet
                targetParent leftField rightField leftArguments
                rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) parentType
            (projectionTargetResolverValue
              (.object sourceRuntimeType
                (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
            selectionSet
          = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
              : Execution.Response) := by
  intro hfree hnormal hobject hchildren
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  have hfieldOk :
      ∀ responseName fieldName arguments directives childSelectionSet,
        Selection.field responseName fieldName arguments directives
            childSelectionSet ∈ selectionSet ->
          ∃ responseValue fieldErrors,
            Execution.executeField schema resolvers variableValues (fuel + 1)
              (projectionTargetResolverValue
                (.object sourceRuntimeType
                  (FieldPairPathLocalProbeRef.target tag
                    currentSelectionSet)))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            =
            .ok ([(responseName, responseValue)], fieldErrors) := by
    exact
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet currentSelectionSet variableValues fuel
        targetParent leftField rightField parentType sourceRuntimeType
        leftArguments rightArguments leftRuntime rightRuntime tag
        selectionSet hchildren
  simpa [resolvers] using
    ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
      resolvers variableValues (fuel + 1) parentType
      (projectionTargetResolverValue
        (.object sourceRuntimeType
          (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
      selectionSet hfree hnormal hobject hfieldOk

theorem fieldPairRuntimeProbeResolvers_left_root
    (schema : Schema) (childRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : Execution.CoercedArgument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime).resolve
            targetParent leftField arguments (.object targetParent none)
          = some
              (objectProbeResolverValueWithRuntime leftRuntime
                (some FieldPairProbeTag.left) fieldDefinition.outputType) := by
  intro harguments hlookup
  classical
  have htarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        leftField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairRuntimeProbeResolvers, fieldPairRuntimeProbeResolve,
    hlookup, htarget]

theorem fieldPairRuntimeProbeResolvers_right_root_of_not_left
    (schema : Schema) (childRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField arguments
      -> Execution.CoercedArgument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime).resolve
            targetParent rightField arguments (.object targetParent none)
          = some
              (objectProbeResolverValueWithRuntime rightRuntime
                (some FieldPairProbeTag.right) fieldDefinition.outputType) := by
  intro hnotLeft harguments hlookup
  classical
  have hright :
      fieldProbeTarget targetParent rightField rightArguments targetParent
        rightField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairRuntimeProbeResolvers, fieldPairRuntimeProbeResolve,
    hlookup, hnotLeft, hright]

theorem fieldPairRuntimeProbeResolvers_tagged_object
    (schema : Schema) (childRootSelectionSet : List Selection)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime).resolve
            parentType fieldName arguments (.object runtimeType (some tag))
          = some
              (fieldPairProbeHeadResolverValue schema childRootSelectionSet
                parentType fieldName arguments tag fieldDefinition.outputType) := by
  intro hlookup
  simp [fieldPairRuntimeProbeResolvers, fieldPairRuntimeProbeResolve,
    hlookup]

theorem executeField_fieldPairRuntimeProbe_left_root_objectProbe_response
    (schema : Schema) (childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> Execution.executeField schema
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    variableValues fuel
                    (.object leftRuntime (some FieldPairProbeTag.left))
                    (Execution.collectFields schema variableValues leftRuntime
                      (.object leftRuntime (some FieldPairProbeTag.left))
                      childSelectionSet)))) := by
  intro harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hcoercedArguments :
      Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments
        = _coercedArguments :=
    Execution.coercedArgumentsForField_eq_of_success schema variableValues
      targetParent leftField arguments fieldDefinition _coercedArguments
      hlookup hcoercionResult
  have hresolve :
      Execution.coerceAndResolveFieldValue schema
        (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime)
        variableValues fieldDefinition targetParent leftField arguments
        (.object targetParent none)
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (some FieldPairProbeTag.left) fieldDefinition.outputType) :=
    by
      simpa [Execution.resolveFieldValue, hcoercionResult,
        Execution.coercedArgumentsForField, hlookup] using
        fieldPairRuntimeProbeResolvers_left_root schema childRootSelectionSet
          targetParent leftField rightField leftArguments rightArguments
          (Execution.coercedArgumentsForField schema variableValues targetParent
            leftField arguments)
          leftRuntime rightRuntime fieldDefinition harguments hlookup
  exact
    executeField_objectProbeWithRuntime_response schema
      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel (.object targetParent none) responseName
      targetParent leftField arguments childSelectionSet fieldDefinition
      leftRuntime (some FieldPairProbeTag.left) hlookup hresolve hinclude

theorem executeField_fieldPairRuntimeProbe_right_root_objectProbe_response_of_not_left
    (schema : Schema) (childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> Execution.executeField schema
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    variableValues fuel
                    (.object rightRuntime (some FieldPairProbeTag.right))
                    (Execution.collectFields schema variableValues rightRuntime
                      (.object rightRuntime (some FieldPairProbeTag.right))
                      childSelectionSet)))) := by
  intro hnotLeft harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hresolve :
      Execution.coerceAndResolveFieldValue schema
        (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime)
        variableValues fieldDefinition targetParent rightField arguments
        (.object targetParent none)
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (some FieldPairProbeTag.right) fieldDefinition.outputType) :=
    by
      simpa [Execution.resolveFieldValue, hcoercionResult,
        Execution.coercedArgumentsForField, hlookup] using
        fieldPairRuntimeProbeResolvers_right_root_of_not_left schema
          childRootSelectionSet targetParent leftField rightField leftArguments
          rightArguments
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          leftRuntime rightRuntime fieldDefinition hnotLeft harguments hlookup
  exact
    executeField_objectProbeWithRuntime_response schema
      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel (.object targetParent none) responseName
      targetParent rightField arguments childSelectionSet fieldDefinition
      rightRuntime (some FieldPairProbeTag.right) hlookup hresolve hinclude

theorem projectionTargetResolverValue_objectProbeResolverValueWithRuntime
    {ObjectRef : Type} (runtimeType : Name) (ref : ObjectRef)
    (typeRef : TypeRef)
    : projectionTargetResolverValue
        (objectProbeResolverValueWithRuntime runtimeType ref typeRef)
      = objectProbeResolverValueWithRuntime runtimeType
          (ProjectionResolverRef.target ref) typeRef := by
  induction typeRef with
  | named typeName =>
      simp [projectionTargetResolverValue, projectionResolverValue,
        objectProbeResolverValueWithRuntime]
  | list inner ih =>
      simpa [projectionTargetResolverValue, projectionResolverValue,
        objectProbeResolverValueWithRuntime] using ih
  | nonNull inner ih =>
      simpa [objectProbeResolverValueWithRuntime] using ih

theorem executeField_fieldPairOrDeepSuccess_runtimeProbe_left_root_response
    (schema : Schema) (rootSelectionSet childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                        targetParent leftField rightField leftArguments
                        rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object leftRuntime (some FieldPairProbeTag.left)))
                    (Execution.collectFields schema variableValues leftRuntime
                      (projectionTargetResolverValue
                        (.object leftRuntime (some FieldPairProbeTag.left)))
                      childSelectionSet)))) := by
  intro harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hcoercedArguments :
      Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments
        = _coercedArguments :=
    Execution.coercedArgumentsForField_eq_of_success schema variableValues
      targetParent leftField arguments fieldDefinition _coercedArguments
      hlookup hcoercionResult
  let base :=
    fieldPairRuntimeProbeResolvers schema childRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent leftField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            leftField arguments)
          (.object targetParent (none : Option FieldPairProbeTag))
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (some FieldPairProbeTag.left) fieldDefinition.outputType) :=
    fieldPairRuntimeProbeResolvers_left_root schema childRootSelectionSet
      targetParent leftField rightField leftArguments rightArguments
      (Execution.coercedArgumentsForField schema variableValues targetParent
        leftField arguments)
      leftRuntime rightRuntime fieldDefinition harguments hlookup
  have hresolve :
      Execution.coerceAndResolveFieldValue schema resolvers variableValues
          fieldDefinition targetParent leftField arguments
          (projectionRootResolverValue
            (.object targetParent (none : Option FieldPairProbeTag)))
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (ProjectionResolverRef.target (some FieldPairProbeTag.left))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_left_root schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        (.object targetParent (none : Option FieldPairProbeTag))
        harguments
    simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
      hcoercionResult,
      ← hcoercedArguments, resolvers]
    rw [hroot, hbase]
    simp [projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent (none : Option FieldPairProbeTag)))
      responseName targetParent leftField arguments childSelectionSet
      fieldDefinition leftRuntime
      (ProjectionResolverRef.target (some FieldPairProbeTag.left))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem executeField_fieldPairOrDeepSuccess_runtimeProbe_right_root_response_of_not_left
    (schema : Schema) (rootSelectionSet childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                        targetParent leftField rightField leftArguments
                        rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object rightRuntime (some FieldPairProbeTag.right)))
                    (Execution.collectFields schema variableValues rightRuntime
                      (projectionTargetResolverValue
                        (.object rightRuntime (some FieldPairProbeTag.right)))
                      childSelectionSet)))) := by
  intro hnotLeft harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hcoercedArguments :
      Execution.coercedArgumentsForField schema variableValues targetParent
          rightField arguments
        = _coercedArguments :=
    Execution.coercedArgumentsForField_eq_of_success schema variableValues
      targetParent rightField arguments fieldDefinition _coercedArguments
      hlookup hcoercionResult
  let base :=
    fieldPairRuntimeProbeResolvers schema childRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          (.object targetParent (none : Option FieldPairProbeTag))
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (some FieldPairProbeTag.right) fieldDefinition.outputType) :=
    fieldPairRuntimeProbeResolvers_right_root_of_not_left schema
      childRootSelectionSet targetParent leftField rightField leftArguments
      rightArguments
      (Execution.coercedArgumentsForField schema variableValues targetParent
        rightField arguments)
      leftRuntime rightRuntime fieldDefinition
      hnotLeft harguments hlookup
  have hresolve :
      Execution.coerceAndResolveFieldValue schema resolvers variableValues
          fieldDefinition targetParent rightField arguments
          (projectionRootResolverValue
            (.object targetParent (none : Option FieldPairProbeTag)))
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (ProjectionResolverRef.target (some FieldPairProbeTag.right))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_right_root schema rootSelectionSet
        base targetParent leftField rightField leftArguments rightArguments
        (Execution.coercedArgumentsForField schema variableValues targetParent
          rightField arguments)
        (.object targetParent (none : Option FieldPairProbeTag))
        harguments
    simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
      hcoercionResult,
      ← hcoercedArguments, resolvers]
    rw [hroot, hbase]
    simp [
      projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent (none : Option FieldPairProbeTag)))
      responseName targetParent rightField arguments childSelectionSet
      fieldDefinition rightRuntime
      (ProjectionResolverRef.target (some FieldPairProbeTag.right))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem
    executeField_fieldPairOrDeepSuccess_runtimeProbe_left_root_ok_of_child_object_response
    (schema : Schema) (rootSelectionSet childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime (some FieldPairProbeTag.left)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro harguments hlookup hcoercion hinclude hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues fuel
          (projectionTargetResolverValue
            (.object leftRuntime (some FieldPairProbeTag.left)))
          (Execution.collectFields schema variableValues leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime (some FieldPairProbeTag.left)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  rw [
    executeField_fieldPairOrDeepSuccess_runtimeProbe_left_root_response
      schema rootSelectionSet childRootSelectionSet variableValues fuel
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition harguments hlookup hcoercion hinclude]
  simp [hchildRaw, hwrapped, Execution.singleFieldResult]

theorem
    executeField_fieldPairOrDeepSuccess_runtimeProbe_right_root_ok_of_child_object_response
    (schema : Schema) (rootSelectionSet childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues fuel rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime (some FieldPairProbeTag.right)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotLeft harguments hlookup hcoercion hinclude hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues fuel
          (projectionTargetResolverValue
            (.object rightRuntime (some FieldPairProbeTag.right)))
          (Execution.collectFields schema variableValues rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime (some FieldPairProbeTag.right)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  rw [
    executeField_fieldPairOrDeepSuccess_runtimeProbe_right_root_response_of_not_left
      schema rootSelectionSet childRootSelectionSet variableValues fuel
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition hnotLeft harguments hlookup hcoercion hinclude]
  simp [hchildRaw, hwrapped, Execution.singleFieldResult]

theorem
    executeField_fieldPairOrDeepSuccess_runtimeProbe_left_root_ok_of_child_object_response_fuel_ge
    (schema : Schema) (rootSelectionSet childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime (some FieldPairProbeTag.left)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro harguments hlookup hcoercion hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_runtimeProbe_left_root_ok_of_child_object_response
      schema rootSelectionSet childRootSelectionSet variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition childFields childErrors harguments hlookup hcoercion hinclude
      hchildResponse
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hfuelEq] using hfield

theorem
    executeField_fieldPairOrDeepSuccess_runtimeProbe_right_root_ok_of_child_object_response_fuel_ge
    (schema : Schema) (rootSelectionSet childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime (some FieldPairProbeTag.right)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                targetParent leftField rightField leftArguments rightArguments
                leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotLeft harguments hlookup hcoercion hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_runtimeProbe_right_root_ok_of_child_object_response
      schema rootSelectionSet childRootSelectionSet variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition childFields childErrors hnotLeft harguments hlookup
      hcoercion hinclude hchildResponse
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hfuelEq] using hfield

theorem executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_left_root_response
    (schema : Schema)
    (rootSelectionSet leftChildRootSelectionSet rightChildRootSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                rightChildRootSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSideRuntimeProbeResolvers schema
                        leftChildRootSelectionSet rightChildRootSelectionSet
                        targetParent leftField rightField leftArguments
                        rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object leftRuntime (some FieldPairProbeTag.left)))
                    (Execution.collectFields schema variableValues leftRuntime
                      (projectionTargetResolverValue
                        (.object leftRuntime (some FieldPairProbeTag.left)))
                      childSelectionSet)))) := by
  intro harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hcoercedArguments :
      Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments
        = _coercedArguments :=
    Execution.coercedArgumentsForField_eq_of_success schema variableValues
      targetParent leftField arguments fieldDefinition _coercedArguments
      hlookup hcoercionResult
  let base :=
    fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
      rightChildRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent leftField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            leftField arguments)
          (.object targetParent (none : Option FieldPairProbeTag))
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (some FieldPairProbeTag.left) fieldDefinition.outputType) :=
    fieldPairSideRuntimeProbeResolvers_left_root schema
      leftChildRootSelectionSet rightChildRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments
      (Execution.coercedArgumentsForField schema variableValues targetParent
        leftField arguments)
      leftRuntime
      rightRuntime fieldDefinition harguments hlookup
  have hresolve :
      Execution.coerceAndResolveFieldValue schema resolvers variableValues
          fieldDefinition targetParent leftField arguments
          (projectionRootResolverValue
            (.object targetParent (none : Option FieldPairProbeTag)))
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (ProjectionResolverRef.target (some FieldPairProbeTag.left))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_left_root schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        (.object targetParent (none : Option FieldPairProbeTag))
        harguments
    simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
      hcoercionResult,
      ← hcoercedArguments, resolvers]
    rw [hroot, hbase]
    simp [
      projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent (none : Option FieldPairProbeTag)))
      responseName targetParent leftField arguments childSelectionSet
      fieldDefinition leftRuntime
      (ProjectionResolverRef.target (some FieldPairProbeTag.left))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem
    executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_right_root_response_of_not_left
    (schema : Schema)
    (rootSelectionSet leftChildRootSelectionSet rightChildRootSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                rightChildRootSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairSideRuntimeProbeResolvers schema
                        leftChildRootSelectionSet rightChildRootSelectionSet
                        targetParent leftField rightField leftArguments
                        rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object rightRuntime (some FieldPairProbeTag.right)))
                    (Execution.collectFields schema variableValues rightRuntime
                      (projectionTargetResolverValue
                        (.object rightRuntime (some FieldPairProbeTag.right)))
                      childSelectionSet)))) := by
  intro hnotLeft harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hcoercedArguments :
      Execution.coercedArgumentsForField schema variableValues targetParent
          rightField arguments
        = _coercedArguments :=
    Execution.coercedArgumentsForField_eq_of_success schema variableValues
      targetParent rightField arguments fieldDefinition _coercedArguments
      hlookup hcoercionResult
  let base :=
    fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
      rightChildRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          (.object targetParent (none : Option FieldPairProbeTag))
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (some FieldPairProbeTag.right) fieldDefinition.outputType) :=
    fieldPairSideRuntimeProbeResolvers_right_root_of_not_left schema
      leftChildRootSelectionSet rightChildRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments
      (Execution.coercedArgumentsForField schema variableValues targetParent
        rightField arguments)
      leftRuntime
      rightRuntime fieldDefinition hnotLeft harguments hlookup
  have hresolve :
      Execution.coerceAndResolveFieldValue schema resolvers variableValues
          fieldDefinition targetParent rightField arguments
          (projectionRootResolverValue
            (.object targetParent (none : Option FieldPairProbeTag)))
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (ProjectionResolverRef.target (some FieldPairProbeTag.right))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_right_root schema rootSelectionSet
        base targetParent leftField rightField leftArguments rightArguments
        (Execution.coercedArgumentsForField schema variableValues targetParent
          rightField arguments)
        (.object targetParent (none : Option FieldPairProbeTag))
        harguments
    simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
      hcoercionResult,
      ← hcoercedArguments, resolvers]
    rw [hroot, hbase]
    simp [
      projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent (none : Option FieldPairProbeTag)))
      responseName targetParent rightField arguments childSelectionSet
      fieldDefinition rightRuntime
      (ProjectionResolverRef.target (some FieldPairProbeTag.right))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem executeField_fieldPairOrDeepSuccess_pathLocalProbe_left_root_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairPathLocalProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object leftRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                          leftInitialSelectionSet)))
                    (Execution.collectFields schema variableValues leftRuntime
                      (projectionTargetResolverValue
                        (.object leftRuntime
                          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                            leftInitialSelectionSet)))
                      childSelectionSet)))) := by
  intro harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hcoercedArguments :
      Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments
        = _coercedArguments :=
    Execution.coercedArgumentsForField_eq_of_success schema variableValues
      targetParent leftField arguments fieldDefinition _coercedArguments
      hlookup hcoercionResult
  let base :=
    fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent leftField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            leftField arguments)
          (.object targetParent FieldPairPathLocalProbeRef.root)
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
            leftInitialSelectionSet) fieldDefinition.outputType) :=
    fieldPairPathLocalProbeResolvers_left_root schema leftInitialSelectionSet
      rightInitialSelectionSet targetParent leftField rightField
      leftArguments rightArguments
      (Execution.coercedArgumentsForField schema variableValues targetParent
        leftField arguments)
      leftRuntime rightRuntime
      fieldDefinition harguments hlookup
  have hresolve :
      Execution.coerceAndResolveFieldValue schema resolvers variableValues
          fieldDefinition targetParent leftField arguments
          (projectionRootResolverValue
            (.object targetParent FieldPairPathLocalProbeRef.root))
      =
      some
        (objectProbeResolverValueWithRuntime leftRuntime
          (ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
              leftInitialSelectionSet))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_left_root schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        (.object targetParent FieldPairPathLocalProbeRef.root)
        harguments
    simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
      hcoercionResult,
      ← hcoercedArguments, resolvers]
    rw [hroot, hbase]
    simp [
      projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent FieldPairPathLocalProbeRef.root))
      responseName targetParent leftField arguments childSelectionSet
      fieldDefinition leftRuntime
      (ProjectionResolverRef.target
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
          leftInitialSelectionSet))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_response_of_not_left
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument)
    (leftRuntime rightRuntime : Name) (childSelectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairPathLocalProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                        rightInitialSelectionSet targetParent leftField rightField
                        leftArguments rightArguments leftRuntime rightRuntime)
                      targetParent leftField rightField leftArguments
                      rightArguments)
                    variableValues fuel
                    (projectionTargetResolverValue
                      (.object rightRuntime
                        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                          rightInitialSelectionSet)))
                    (Execution.collectFields schema variableValues rightRuntime
                      (projectionTargetResolverValue
                        (.object rightRuntime
                          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                            rightInitialSelectionSet)))
                      childSelectionSet)))) := by
  intro hnotLeft harguments hlookup hcoercion hinclude
  rcases
      Execution.ArgumentCoercionResult.exists_success_of_isSuccess hcoercion with
    ⟨_coercedArguments, hcoercionResult⟩
  have hcoercedArguments :
      Execution.coercedArgumentsForField schema variableValues targetParent
          rightField arguments
        = _coercedArguments :=
    Execution.coercedArgumentsForField_eq_of_success schema variableValues
      targetParent rightField arguments fieldDefinition _coercedArguments
      hlookup hcoercionResult
  let base :=
    fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
      rightInitialSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base
      targetParent leftField rightField leftArguments rightArguments
  have hbase :
      base.resolve targetParent rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          (.object targetParent FieldPairPathLocalProbeRef.root)
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
            rightInitialSelectionSet) fieldDefinition.outputType) :=
    fieldPairPathLocalProbeResolvers_right_root_of_not_left schema
      leftInitialSelectionSet rightInitialSelectionSet targetParent leftField
      rightField leftArguments rightArguments
      (Execution.coercedArgumentsForField schema variableValues targetParent
        rightField arguments)
      leftRuntime
      rightRuntime fieldDefinition hnotLeft harguments hlookup
  have hresolve :
      Execution.coerceAndResolveFieldValue schema resolvers variableValues
          fieldDefinition targetParent rightField arguments
          (projectionRootResolverValue
            (.object targetParent FieldPairPathLocalProbeRef.root))
      =
      some
        (objectProbeResolverValueWithRuntime rightRuntime
          (ProjectionResolverRef.target
            (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
              rightInitialSelectionSet))
          fieldDefinition.outputType) := by
    have hroot :=
      fieldPairOrDeepSuccessResolvers_right_root schema rootSelectionSet base
        targetParent leftField rightField leftArguments rightArguments
        (Execution.coercedArgumentsForField schema variableValues targetParent
          rightField arguments)
        (.object targetParent FieldPairPathLocalProbeRef.root)
        harguments
    simp only [Execution.coerceAndResolveFieldValue, Execution.resolveFieldValue,
      hcoercionResult,
      ← hcoercedArguments, resolvers]
    rw [hroot, hbase]
    simp [
      projectionTargetResolverValue_objectProbeResolverValueWithRuntime]
  have hfield :=
    executeField_objectProbeWithRuntime_response schema resolvers
      variableValues fuel
      (projectionRootResolverValue
        (.object targetParent FieldPairPathLocalProbeRef.root))
      responseName targetParent rightField arguments childSelectionSet
      fieldDefinition rightRuntime
      (ProjectionResolverRef.target
        (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
          rightInitialSelectionSet))
      hlookup hresolve hinclude
  simpa [base, resolvers, projectionTargetResolverValue,
    projectionResolverValue] using hfield

theorem
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_left_root_ok_of_child_object_response_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairPathLocalProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro harguments hlookup hcoercion hinclude hfuel hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          (projectionTargetResolverValue
            (.object leftRuntime
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                leftInitialSelectionSet)))
          (Execution.collectFields schema variableValues leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                  leftInitialSelectionSet)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_left_root_response
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition harguments hlookup hcoercion hinclude
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hchildRaw, hwrapped, Execution.singleFieldResult, hfuelEq]
    using hfield

theorem
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_ok_of_child_object_response_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent FieldPairPathLocalProbeRef.root))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotLeft harguments hlookup hcoercion hinclude hfuel hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          (projectionTargetResolverValue
            (.object rightRuntime
              (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                rightInitialSelectionSet)))
          (Execution.collectFields schema variableValues rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime
                (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                  rightInitialSelectionSet)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_response_of_not_left
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition hnotLeft harguments hlookup hcoercion hinclude
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hchildRaw, hwrapped, Execution.singleFieldResult, hfuelEq]
    using hfield

theorem
    executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_left_root_ok_of_child_object_response_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftChildRootSelectionSet rightChildRootSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : Execution.CoercedArgument.argumentsEquivalent
        (Execution.coercedArgumentsForField schema variableValues targetParent
          leftField arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType leftRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                rightChildRootSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime (some FieldPairProbeTag.left)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                rightChildRootSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro harguments hlookup hcoercion hinclude hfuel hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSideRuntimeProbeResolvers schema
              leftChildRootSelectionSet rightChildRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          (projectionTargetResolverValue
            (.object leftRuntime (some FieldPairProbeTag.left)))
          (Execution.collectFields schema variableValues leftRuntime
            (projectionTargetResolverValue
              (.object leftRuntime (some FieldPairProbeTag.left)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_left_root_response
      schema rootSelectionSet leftChildRootSelectionSet
      rightChildRootSelectionSet variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition harguments hlookup hcoercion hinclude
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hchildRaw, hwrapped, Execution.singleFieldResult, hfuelEq]
    using hfield

theorem
    executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_right_root_ok_of_child_object_response_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftChildRootSelectionSet rightChildRootSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (arguments : List Argument) (leftRuntime rightRuntime : Name)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (childFields : List (Name × Execution.ResponseValue)) (childErrors : Nat)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
      -> Execution.CoercedArgument.argumentsEquivalent
          (Execution.coercedArgumentsForField schema variableValues targetParent
            rightField arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments).isSuccess
          = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ parentFuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                rightChildRootSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel - leafProbeFuel fieldDefinition.outputType)
            rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime (some FieldPairProbeTag.right)))
            childSelectionSet
          = ({ data := Execution.ResponseValue.object childFields, errors := childErrors }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                rightChildRootSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (parentFuel + 1)
            (projectionRootResolverValue
              (.object targetParent (none : Option FieldPairProbeTag)))
            responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hnotLeft harguments hlookup hcoercion hinclude hfuel hchildResponse
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType childFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, _hresponseNonNull⟩
  refine ⟨responseValue, fieldErrors, ?_⟩
  have hchildRaw :
      Execution.selectionSetResultToResponse
        (Execution.executeCollectedFields schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSideRuntimeProbeResolvers schema
              leftChildRootSelectionSet rightChildRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues
          (parentFuel - leafProbeFuel fieldDefinition.outputType)
          (projectionTargetResolverValue
            (.object rightRuntime (some FieldPairProbeTag.right)))
          (Execution.collectFields schema variableValues rightRuntime
            (projectionTargetResolverValue
              (.object rightRuntime (some FieldPairProbeTag.right)))
            childSelectionSet))
      =
      ({ data := Execution.ResponseValue.object childFields,
         errors := childErrors } :
        Execution.Response) := by
    simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet] using hchildResponse
  have hfield :=
    executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_right_root_response_of_not_left
      schema rootSelectionSet leftChildRootSelectionSet
      rightChildRootSelectionSet variableValues
      (parentFuel - leafProbeFuel fieldDefinition.outputType)
      targetParent leftField rightField responseName leftArguments
      rightArguments arguments leftRuntime rightRuntime childSelectionSet
      fieldDefinition hnotLeft harguments hlookup hcoercion hinclude
  have hfuelEq :
      parentFuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      parentFuel + 1 := by
    omega
  simpa [hchildRaw, hwrapped, Execution.singleFieldResult, hfuelEq]
    using hfield

theorem selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_pathLocalProbe_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (leftFieldDefinition rightFieldDefinition : FieldDefinition)
    (selectionSet : List Selection)
    : schema.lookupField targetParent leftField = some leftFieldDefinition
      -> schema.lookupField targetParent rightField = some rightFieldDefinition
      -> schema.typeIncludesObjectBool
            leftFieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool
            rightFieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel
      -> selectionSetArgumentCoercionSucceeds schema variableValues targetParent
          selectionSet
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName leftField arguments directives childSelectionSet
              ∈ selectionSet
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  targetParent leftField arguments)
                leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.left
                        leftInitialSelectionSet)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName rightField arguments directives childSelectionSet
              ∈ selectionSet
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  targetParent rightField arguments)
                rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime
                      (FieldPairPathLocalProbeRef.target FieldPairProbeTag.right
                        rightInitialSelectionSet)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ¬ fieldPairProjectionTarget targetParent leftField rightField
                  leftArguments rightArguments targetParent fieldName
                  (Execution.coercedArgumentsForField schema variableValues
                    targetParent fieldName arguments)
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object targetParent FieldPairPathLocalProbeRef.root))
                  responseName
                  [{
                    parentType := targetParent
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
              rightInitialSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (parentFuel + 1) targetParent
          (projectionRootResolverValue
            (.object targetParent FieldPairPathLocalProbeRef.root))
          selectionSet := by
  intro hleftLookup hrightLookup hleftInclude hrightInclude hleftFuel
    hrightFuel hcoercion hleftChildResponse hrightChildResponse hother
  intro responseName fieldName arguments directives childSelectionSet hmem
  by_cases hleftTarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        fieldName (Execution.coercedArgumentsForField schema variableValues
          targetParent fieldName arguments)
  · rcases hleftTarget with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    rcases
        hleftChildResponse responseName arguments directives
          childSelectionSet hmem harguments with
      ⟨childFields, childErrors, hchildResponse⟩
    have hleftCoercion :=
      hcoercion responseName leftField arguments directives childSelectionSet
        hmem leftFieldDefinition hleftLookup
    exact
      executeField_fieldPairOrDeepSuccess_pathLocalProbe_left_root_ok_of_child_object_response_fuel_ge
        schema rootSelectionSet leftInitialSelectionSet
        rightInitialSelectionSet variableValues parentFuel targetParent
        leftField rightField responseName leftArguments rightArguments
        arguments leftRuntime rightRuntime childSelectionSet
        leftFieldDefinition childFields childErrors harguments hleftLookup
        hleftCoercion hleftInclude hleftFuel hchildResponse
  · by_cases hrightTarget :
        fieldProbeTarget targetParent rightField rightArguments targetParent
          fieldName (Execution.coercedArgumentsForField schema variableValues
            targetParent fieldName arguments)
    · rcases hrightTarget with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget targetParent leftField leftArguments
            targetParent rightField
            (Execution.coercedArgumentsForField schema variableValues
              targetParent rightField arguments) := by
        intro htarget
        exact hleftTarget htarget
      rcases
          hrightChildResponse responseName arguments directives
            childSelectionSet hmem harguments with
        ⟨childFields, childErrors, hchildResponse⟩
      have hrightCoercion :=
        hcoercion responseName rightField arguments directives childSelectionSet
          hmem rightFieldDefinition hrightLookup
      exact
        executeField_fieldPairOrDeepSuccess_pathLocalProbe_right_root_ok_of_child_object_response_fuel_ge
          schema rootSelectionSet leftInitialSelectionSet
          rightInitialSelectionSet variableValues parentFuel targetParent
          leftField rightField responseName leftArguments rightArguments
          arguments leftRuntime rightRuntime childSelectionSet
          rightFieldDefinition childFields childErrors hnotLeft
          harguments hrightLookup hrightCoercion hrightInclude hrightFuel
          hchildResponse
    · have hnotProjection :
          ¬ fieldPairProjectionTarget targetParent leftField rightField
            leftArguments rightArguments targetParent fieldName
            (Execution.coercedArgumentsForField schema variableValues
              targetParent fieldName arguments) := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact hleftTarget ⟨rfl, hleft.1, hleft.2⟩
        · exact hrightTarget ⟨rfl, hright.1, hright.2⟩
      exact
        hother responseName fieldName arguments directives childSelectionSet
          hmem hnotProjection

theorem selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_sideRuntimeProbe_of_field_cases
    (schema : Schema)
    (rootSelectionSet leftChildRootSelectionSet rightChildRootSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (leftFieldDefinition rightFieldDefinition : FieldDefinition)
    (selectionSet : List Selection)
    : schema.lookupField targetParent leftField = some leftFieldDefinition
      -> schema.lookupField targetParent rightField = some rightFieldDefinition
      -> schema.typeIncludesObjectBool
            leftFieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool
            rightFieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel
      -> selectionSetArgumentCoercionSucceeds schema variableValues targetParent
          selectionSet
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName leftField arguments directives childSelectionSet
              ∈ selectionSet
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  targetParent leftField arguments)
                leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSideRuntimeProbeResolvers schema
                      leftChildRootSelectionSet rightChildRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime (some FieldPairProbeTag.left)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName rightField arguments directives childSelectionSet
              ∈ selectionSet
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  targetParent rightField arguments)
                rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSideRuntimeProbeResolvers schema
                      leftChildRootSelectionSet rightChildRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime (some FieldPairProbeTag.right)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ¬ fieldPairProjectionTarget targetParent leftField rightField
                  leftArguments rightArguments targetParent fieldName
                  (Execution.coercedArgumentsForField schema variableValues
                    targetParent fieldName arguments)
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairSideRuntimeProbeResolvers schema
                      leftChildRootSelectionSet rightChildRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object targetParent (none : Option FieldPairProbeTag)))
                  responseName
                  [{
                    parentType := targetParent
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
              rightChildRootSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (parentFuel + 1) targetParent
          (projectionRootResolverValue
            (.object targetParent (none : Option FieldPairProbeTag)))
          selectionSet := by
  intro hleftLookup hrightLookup hleftInclude hrightInclude hleftFuel
    hrightFuel hcoercion hleftChildResponse hrightChildResponse hother
  intro responseName fieldName arguments directives childSelectionSet hmem
  by_cases hleftTarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        fieldName (Execution.coercedArgumentsForField schema variableValues
          targetParent fieldName arguments)
  · rcases hleftTarget with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    rcases
        hleftChildResponse responseName arguments directives
          childSelectionSet hmem harguments with
      ⟨childFields, childErrors, hchildResponse⟩
    have hleftCoercion :=
      hcoercion responseName leftField arguments directives childSelectionSet
        hmem leftFieldDefinition hleftLookup
    exact
      executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_left_root_ok_of_child_object_response_fuel_ge
        schema rootSelectionSet leftChildRootSelectionSet
        rightChildRootSelectionSet variableValues parentFuel targetParent
        leftField rightField responseName leftArguments rightArguments
        arguments leftRuntime rightRuntime childSelectionSet
        leftFieldDefinition childFields childErrors harguments hleftLookup
        hleftCoercion hleftInclude hleftFuel hchildResponse
  · by_cases hrightTarget :
        fieldProbeTarget targetParent rightField rightArguments targetParent
          fieldName (Execution.coercedArgumentsForField schema variableValues
            targetParent fieldName arguments)
    · rcases hrightTarget with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget targetParent leftField leftArguments
            targetParent rightField
            (Execution.coercedArgumentsForField schema variableValues
              targetParent rightField arguments) := by
        intro htarget
        exact hleftTarget htarget
      rcases
          hrightChildResponse responseName arguments directives
            childSelectionSet hmem harguments with
        ⟨childFields, childErrors, hchildResponse⟩
      have hrightCoercion :=
        hcoercion responseName rightField arguments directives childSelectionSet
          hmem rightFieldDefinition hrightLookup
      exact
        executeField_fieldPairOrDeepSuccess_sideRuntimeProbe_right_root_ok_of_child_object_response_fuel_ge
          schema rootSelectionSet leftChildRootSelectionSet
          rightChildRootSelectionSet variableValues parentFuel targetParent
          leftField rightField responseName leftArguments rightArguments
          arguments leftRuntime rightRuntime childSelectionSet
          rightFieldDefinition childFields childErrors hnotLeft
          harguments hrightLookup hrightCoercion hrightInclude hrightFuel
          hchildResponse
    · have hnotProjection :
          ¬ fieldPairProjectionTarget targetParent leftField rightField
            leftArguments rightArguments targetParent fieldName
            (Execution.coercedArgumentsForField schema variableValues
              targetParent fieldName arguments) := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact hleftTarget ⟨rfl, hleft.1, hleft.2⟩
        · exact hrightTarget ⟨rfl, hright.1, hright.2⟩
      exact
        hother responseName fieldName arguments directives childSelectionSet
          hmem hnotProjection

theorem selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_runtimeProbe_of_field_cases
    (schema : Schema) (rootSelectionSet childRootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (parentFuel : Nat)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (leftFieldDefinition rightFieldDefinition : FieldDefinition)
    (selectionSet : List Selection)
    : schema.lookupField targetParent leftField = some leftFieldDefinition
      -> schema.lookupField targetParent rightField = some rightFieldDefinition
      -> schema.typeIncludesObjectBool
            leftFieldDefinition.outputType.namedType leftRuntime
          = true
      -> schema.typeIncludesObjectBool
            rightFieldDefinition.outputType.namedType rightRuntime
          = true
      -> leafProbeFuel leftFieldDefinition.outputType ≤ parentFuel
      -> leafProbeFuel rightFieldDefinition.outputType ≤ parentFuel
      -> selectionSetArgumentCoercionSucceeds schema variableValues targetParent
          selectionSet
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName leftField arguments directives childSelectionSet
              ∈ selectionSet
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  targetParent leftField arguments)
                leftArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel leftFieldDefinition.outputType)
                  leftRuntime
                  (projectionTargetResolverValue
                    (.object leftRuntime (some FieldPairProbeTag.left)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName arguments directives childSelectionSet,
            Selection.field responseName rightField arguments directives childSelectionSet
              ∈ selectionSet
            -> Execution.CoercedArgument.argumentsEquivalent
                (Execution.coercedArgumentsForField schema variableValues
                  targetParent rightField arguments)
                rightArguments
            -> ∃ childFields childErrors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues
                  (parentFuel - leafProbeFuel rightFieldDefinition.outputType)
                  rightRuntime
                  (projectionTargetResolverValue
                    (.object rightRuntime (some FieldPairProbeTag.right)))
                  childSelectionSet
                = ({
                      data := Execution.ResponseValue.object childFields,
                      errors := childErrors
                    }
                    : Execution.Response))
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ¬ fieldPairProjectionTarget targetParent leftField rightField
                  leftArguments rightArguments targetParent fieldName
                  (Execution.coercedArgumentsForField schema variableValues
                    targetParent fieldName arguments)
            -> ∃ responseValue fieldErrors,
                Execution.executeField schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                      targetParent leftField rightField leftArguments
                      rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments
                    rightArguments)
                  variableValues (parentFuel + 1)
                  (projectionRootResolverValue
                    (.object targetParent (none : Option FieldPairProbeTag)))
                  responseName
                  [{
                    parentType := targetParent
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := childSelectionSet
                  }]
                = .ok ([(responseName, responseValue)], fieldErrors))
      -> selectionSetFieldsExecuteOk schema
          (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues (parentFuel + 1) targetParent
          (projectionRootResolverValue
            (.object targetParent (none : Option FieldPairProbeTag)))
          selectionSet := by
  intro hleftLookup hrightLookup hleftInclude hrightInclude hleftFuel
    hrightFuel hcoercion hleftChildResponse hrightChildResponse hother
  intro responseName fieldName arguments directives childSelectionSet hmem
  by_cases hleftTarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        fieldName (Execution.coercedArgumentsForField schema variableValues
          targetParent fieldName arguments)
  · rcases hleftTarget with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    rcases
        hleftChildResponse responseName arguments directives
          childSelectionSet hmem harguments with
      ⟨childFields, childErrors, hchildResponse⟩
    have hleftCoercion :=
      hcoercion responseName leftField arguments directives childSelectionSet
        hmem leftFieldDefinition hleftLookup
    exact
      executeField_fieldPairOrDeepSuccess_runtimeProbe_left_root_ok_of_child_object_response_fuel_ge
        schema rootSelectionSet childRootSelectionSet variableValues
        parentFuel targetParent leftField rightField responseName
        leftArguments rightArguments arguments leftRuntime rightRuntime
        childSelectionSet leftFieldDefinition childFields childErrors
        harguments hleftLookup hleftCoercion hleftInclude hleftFuel
        hchildResponse
  · by_cases hrightTarget :
        fieldProbeTarget targetParent rightField rightArguments targetParent
          fieldName (Execution.coercedArgumentsForField schema variableValues
            targetParent fieldName arguments)
    · rcases hrightTarget with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget targetParent leftField leftArguments
            targetParent rightField
            (Execution.coercedArgumentsForField schema variableValues
              targetParent rightField arguments) := by
        intro htarget
        exact hleftTarget htarget
      rcases
          hrightChildResponse responseName arguments directives
            childSelectionSet hmem harguments with
        ⟨childFields, childErrors, hchildResponse⟩
      have hrightCoercion :=
        hcoercion responseName rightField arguments directives childSelectionSet
          hmem rightFieldDefinition hrightLookup
      exact
        executeField_fieldPairOrDeepSuccess_runtimeProbe_right_root_ok_of_child_object_response_fuel_ge
          schema rootSelectionSet childRootSelectionSet variableValues
          parentFuel targetParent leftField rightField responseName
          leftArguments rightArguments arguments leftRuntime rightRuntime
          childSelectionSet rightFieldDefinition childFields childErrors
          hnotLeft harguments hrightLookup hrightCoercion
          hrightInclude hrightFuel hchildResponse
    · have hnotProjection :
          ¬ fieldPairProjectionTarget targetParent leftField rightField
            leftArguments rightArguments targetParent fieldName
            (Execution.coercedArgumentsForField schema variableValues
              targetParent fieldName arguments) := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact hleftTarget ⟨rfl, hleft.1, hleft.2⟩
        · exact hrightTarget ⟨rfl, hright.1, hright.2⟩
      exact
        hother responseName fieldName arguments directives childSelectionSet
          hmem hnotProjection

mutual
  theorem executeCollectedFields_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
      (schema : Schema) (childRootSelectionSet : List Selection)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : Execution.CoercedArguments)
      (leftRuntime rightRuntime : Name)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (runtimeType : Name) (tag : FieldPairProbeTag)
          (fields : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues fuel (.object runtimeType (some tag)) fields
          = Execution.executeCollectedFields schema
              (fieldPairProbeResolvers schema childRootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues fuel (.object runtimeType (some tag)) fields
    | fuel, runtimeType, tag, [] => by
        simp [Execution.executeCollectedFields]
    | fuel, runtimeType, tag, (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          executeField_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
            schema childRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            variableValues fuel runtimeType tag responseName fields,
          executeCollectedFields_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
            schema childRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            variableValues fuel runtimeType tag rest]

  theorem executeField_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
      (schema : Schema) (childRootSelectionSet : List Selection)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : Execution.CoercedArguments)
      (leftRuntime rightRuntime : Name)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (runtimeType : Name) (tag : FieldPairProbeTag)
          (responseName : Name) (fields : List Execution.ExecutableField),
          Execution.executeField schema
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues fuel (.object runtimeType (some tag)) responseName
            fields
          = Execution.executeField schema
              (fieldPairProbeResolvers schema childRootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues fuel (.object runtimeType (some tag)) responseName
              fields
    | fuel, runtimeType, tag, responseName, [] => by
        simp [Execution.executeField]
    | 0, runtimeType, tag, responseName, field :: fields => by
        simp [Execution.executeField]
    | fuel + 1, runtimeType, tag, responseName, field :: fields => by
        cases hlookup :
            schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, hlookup, fieldPairProbeResolvers]
        | some fieldDefinition =>
            have hruntimeResolve :=
              fieldPairRuntimeProbeResolvers_tagged_object schema
                childRootSelectionSet targetParent leftField rightField
                field.parentType field.fieldName runtimeType leftArguments
                rightArguments
                (Execution.coercedArgumentsForField schema variableValues
                  field.parentType field.fieldName field.arguments)
                leftRuntime rightRuntime tag
                fieldDefinition hlookup
            have hprobeResolve :=
              fieldPairProbeResolvers_tagged_object schema childRootSelectionSet
                targetParent leftField rightField field.parentType
                field.fieldName runtimeType leftArguments rightArguments
                (Execution.coercedArgumentsForField schema variableValues
                  field.parentType field.fieldName field.arguments)
                tag fieldDefinition hlookup
            cases hcoercionResult :
                Execution.coerceArgumentValues schema variableValues
                  fieldDefinition.arguments field.arguments with
            | error =>
                simp [Execution.executeField, Execution.resolveFieldValue,
                  hlookup, hcoercionResult]
            | success coercedArguments =>
                have hcoercedArguments :
                    Execution.coercedArgumentsForField schema variableValues
                        field.parentType field.fieldName field.arguments
                      = coercedArguments :=
                  Execution.coercedArgumentsForField_eq_of_success schema
                    variableValues field.parentType field.fieldName
                    field.arguments fieldDefinition coercedArguments hlookup
                    hcoercionResult
                rw [hcoercedArguments] at hruntimeResolve hprobeResolve
                simp [Execution.executeField, Execution.resolveFieldValue,
                  hlookup, hcoercionResult, hruntimeResolve, hprobeResolve,
                  completeValue_fieldPairRuntimeProbe_resolverValue_eq_fieldPairProbe
                    schema childRootSelectionSet targetParent leftField
                    rightField leftArguments rightArguments leftRuntime
                    rightRuntime variableValues fuel fieldDefinition.outputType
                    (field :: fields) field.parentType field.fieldName
                    coercedArguments tag]

  theorem completeValue_fieldPairRuntimeProbe_resolverValue_eq_fieldPairProbe
      (schema : Schema) (childRootSelectionSet : List Selection)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : Execution.CoercedArguments)
      (leftRuntime rightRuntime : Name)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
          (fields : List Execution.ExecutableField)
          (parentType fieldName : Name) (arguments : Execution.CoercedArguments)
          (tag : FieldPairProbeTag),
          Execution.completeValue schema
            (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments
              leftRuntime rightRuntime)
            variableValues fuel fieldType fields
            (fieldPairProbeHeadResolverValue schema childRootSelectionSet
              parentType fieldName arguments tag fieldType)
          = Execution.completeValue schema
              (fieldPairProbeResolvers schema childRootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues fuel fieldType fields
              (fieldPairProbeHeadResolverValue schema childRootSelectionSet
                parentType fieldName arguments tag fieldType)
    | 0, fieldType, fields, parentType, fieldName, arguments, tag => by
        simp [Execution.completeValue, Execution.outOfFuel]
    | fuel + 1, .nonNull inner, fields, parentType, fieldName, arguments,
        tag => by
        simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
          completeValue_fieldPairRuntimeProbe_resolverValue_eq_fieldPairProbe
            schema childRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            variableValues (fuel + 1) inner fields parentType fieldName
            arguments tag]
    | fuel + 1, .list inner, fields, parentType, fieldName, arguments,
        tag => by
        simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
          Execution.completeValueList, Execution.catchBubbleAsNull,
          completeValue_fieldPairRuntimeProbe_resolverValue_eq_fieldPairProbe
            schema childRootSelectionSet targetParent leftField rightField
            leftArguments rightArguments leftRuntime rightRuntime
            variableValues fuel inner fields parentType fieldName arguments
            tag]
    | fuel + 1, .named typeName, fields, parentType, fieldName, arguments,
        tag => by
        by_cases hcomposite :
            (TypeRef.named typeName).isCompositeBool schema = true
        · by_cases hobject : objectTypeNameBool schema typeName = true
          · by_cases hinclude :
                schema.typeIncludesObjectBool typeName typeName = true
            · simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                hcomposite, hobject, hinclude,
                executeCollectedFields_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
                  schema childRootSelectionSet targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime variableValues fuel typeName tag]
            · have hincludeFalse :
                  schema.typeIncludesObjectBool typeName typeName = false := by
                cases h : schema.typeIncludesObjectBool typeName typeName
                · rfl
                · contradiction
              simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                hcomposite, hobject, hincludeFalse]
          · have hobjectFalse :
                objectTypeNameBool schema typeName = false := by
              cases h : objectTypeNameBool schema typeName
              · rfl
              · contradiction
            cases hruntime :
                abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType childRootSelectionSet with
            | none =>
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName typeName = true
                · simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hinclude,
                    executeCollectedFields_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
                      schema childRootSelectionSet targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime variableValues fuel typeName tag]
                · have hincludeFalse :
                      schema.typeIncludesObjectBool typeName typeName =
                        false := by
                    cases h : schema.typeIncludesObjectBool typeName typeName
                    · rfl
                    · contradiction
                  simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hincludeFalse]
            | some runtimeType =>
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName runtimeType = true
                · simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hinclude,
                    executeCollectedFields_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
                      schema childRootSelectionSet targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime variableValues fuel runtimeType tag]
                · have hincludeFalse :
                      schema.typeIncludesObjectBool typeName runtimeType =
                        false := by
                    cases h :
                        schema.typeIncludesObjectBool typeName runtimeType
                    · rfl
                    · contradiction
                  simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hincludeFalse]
        · have hcompositeFalse :
              (TypeRef.named typeName).isCompositeBool schema = false := by
            cases h : (TypeRef.named typeName).isCompositeBool schema
            · rfl
            · contradiction
          simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
            hcompositeFalse]
end

theorem executeSelectionSetAsResponse_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
    (schema : Schema) (childRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType runtimeType : Name) (tag : FieldPairProbeTag)
    (selectionSet : List Selection)
    : Execution.executeSelectionSetAsResponse schema
        (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
          targetParent leftField rightField leftArguments rightArguments
          leftRuntime rightRuntime)
        variableValues fuel parentType (.object runtimeType (some tag))
        selectionSet
      = Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema childRootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues fuel parentType (.object runtimeType (some tag))
          selectionSet := by
  simp [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
    Execution.executeRootSelectionSet]
  rw [
    executeCollectedFields_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
      schema childRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime variableValues
      fuel runtimeType tag
      (Execution.collectFields schema variableValues parentType
        (.object runtimeType (some tag)) selectionSet)]

mutual
  theorem executeCollectedFields_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
      (schema : Schema)
      (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : Execution.CoercedArguments)
      (leftRuntime rightRuntime : Name)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (runtimeType : Name) (tag : FieldPairProbeTag)
          (fields : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema
            (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
              rightChildRootSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues fuel (.object runtimeType (some tag)) fields
          = Execution.executeCollectedFields schema
              (fieldPairProbeResolvers schema
                (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                  rightChildRootSelectionSet tag)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues fuel (.object runtimeType (some tag)) fields
    | fuel, runtimeType, tag, [] => by
        simp [Execution.executeCollectedFields]
    | fuel, runtimeType, tag, (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          executeField_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
            schema leftChildRootSelectionSet rightChildRootSelectionSet
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime variableValues fuel runtimeType tag
            responseName fields,
          executeCollectedFields_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
            schema leftChildRootSelectionSet rightChildRootSelectionSet
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime variableValues fuel runtimeType tag rest]

  theorem executeField_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
      (schema : Schema)
      (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : Execution.CoercedArguments)
      (leftRuntime rightRuntime : Name)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (runtimeType : Name) (tag : FieldPairProbeTag)
          (responseName : Name) (fields : List Execution.ExecutableField),
          Execution.executeField schema
            (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
              rightChildRootSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues fuel (.object runtimeType (some tag)) responseName
            fields
          = Execution.executeField schema
              (fieldPairProbeResolvers schema
                (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                  rightChildRootSelectionSet tag)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues fuel (.object runtimeType (some tag)) responseName
              fields
    | fuel, runtimeType, tag, responseName, [] => by
        simp [Execution.executeField]
    | 0, runtimeType, tag, responseName, field :: fields => by
        simp [Execution.executeField]
    | fuel + 1, runtimeType, tag, responseName, field :: fields => by
        cases hlookup :
            schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, hlookup, fieldPairProbeResolvers]
        | some fieldDefinition =>
            have hsideResolve :=
              fieldPairSideRuntimeProbeResolvers_tagged_object schema
                leftChildRootSelectionSet rightChildRootSelectionSet
                targetParent leftField rightField field.parentType
                field.fieldName runtimeType leftArguments rightArguments
                (Execution.coercedArgumentsForField schema variableValues
                  field.parentType field.fieldName field.arguments)
                leftRuntime rightRuntime tag fieldDefinition
                hlookup
            have hprobeResolve :=
              fieldPairProbeResolvers_tagged_object schema
                (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                  rightChildRootSelectionSet tag)
                targetParent leftField rightField field.parentType
                field.fieldName runtimeType leftArguments rightArguments
                (Execution.coercedArgumentsForField schema variableValues
                  field.parentType field.fieldName field.arguments)
                tag fieldDefinition hlookup
            cases hcoercionResult :
                Execution.coerceArgumentValues schema variableValues
                  fieldDefinition.arguments field.arguments with
            | error =>
                simp [Execution.executeField, Execution.resolveFieldValue,
                  hlookup, hcoercionResult]
            | success coercedArguments =>
                have hcoercedArguments :
                    Execution.coercedArgumentsForField schema variableValues
                        field.parentType field.fieldName field.arguments
                      = coercedArguments :=
                  Execution.coercedArgumentsForField_eq_of_success schema
                    variableValues field.parentType field.fieldName
                    field.arguments fieldDefinition coercedArguments hlookup
                    hcoercionResult
                rw [hcoercedArguments] at hsideResolve hprobeResolve
                simp [Execution.executeField, Execution.resolveFieldValue,
                  hlookup, hcoercionResult, hsideResolve, hprobeResolve,
                  completeValue_fieldPairSideRuntimeProbe_resolverValue_eq_fieldPairProbe
                    schema leftChildRootSelectionSet rightChildRootSelectionSet
                    targetParent leftField rightField leftArguments rightArguments
                    leftRuntime rightRuntime variableValues fuel
                    fieldDefinition.outputType (field :: fields)
                    field.parentType field.fieldName coercedArguments tag]

  theorem completeValue_fieldPairSideRuntimeProbe_resolverValue_eq_fieldPairProbe
      (schema : Schema)
      (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
      (targetParent leftField rightField : Name)
      (leftArguments rightArguments : Execution.CoercedArguments)
      (leftRuntime rightRuntime : Name)
      (variableValues : Execution.VariableValues)
      : ∀ (fuel : Nat) (fieldType : TypeRef)
          (fields : List Execution.ExecutableField)
          (parentType fieldName : Name) (arguments : Execution.CoercedArguments)
          (tag : FieldPairProbeTag),
          Execution.completeValue schema
            (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
              rightChildRootSelectionSet targetParent leftField rightField
              leftArguments rightArguments leftRuntime rightRuntime)
            variableValues fuel fieldType fields
            (fieldPairProbeHeadResolverValue schema
              (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                rightChildRootSelectionSet tag)
              parentType fieldName arguments tag fieldType)
          = Execution.completeValue schema
              (fieldPairProbeResolvers schema
                (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                  rightChildRootSelectionSet tag)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues fuel fieldType fields
              (fieldPairProbeHeadResolverValue schema
                (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                  rightChildRootSelectionSet tag)
                parentType fieldName arguments tag fieldType)
    | 0, fieldType, fields, parentType, fieldName, arguments, tag => by
        simp [Execution.completeValue, Execution.outOfFuel]
    | fuel + 1, .nonNull inner, fields, parentType, fieldName, arguments,
        tag => by
        simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
          completeValue_fieldPairSideRuntimeProbe_resolverValue_eq_fieldPairProbe
            schema leftChildRootSelectionSet rightChildRootSelectionSet
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime variableValues (fuel + 1) inner fields
            parentType fieldName arguments tag]
    | fuel + 1, .list inner, fields, parentType, fieldName, arguments,
        tag => by
        simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
          Execution.completeValueList, Execution.catchBubbleAsNull,
          completeValue_fieldPairSideRuntimeProbe_resolverValue_eq_fieldPairProbe
            schema leftChildRootSelectionSet rightChildRootSelectionSet
            targetParent leftField rightField leftArguments rightArguments
            leftRuntime rightRuntime variableValues fuel inner fields
            parentType fieldName arguments tag]
    | fuel + 1, .named typeName, fields, parentType, fieldName, arguments,
        tag => by
        by_cases hcomposite :
            (TypeRef.named typeName).isCompositeBool schema = true
        · by_cases hobject : objectTypeNameBool schema typeName = true
          · by_cases hinclude :
                schema.typeIncludesObjectBool typeName typeName = true
            · simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                hcomposite, hobject, hinclude,
                executeCollectedFields_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
                  schema leftChildRootSelectionSet
                  rightChildRootSelectionSet targetParent leftField
                  rightField leftArguments rightArguments leftRuntime
                  rightRuntime variableValues fuel typeName tag]
            · have hincludeFalse :
                  schema.typeIncludesObjectBool typeName typeName = false := by
                cases h : schema.typeIncludesObjectBool typeName typeName
                · rfl
                · contradiction
              simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                hcomposite, hobject, hincludeFalse]
          · have hobjectFalse :
                objectTypeNameBool schema typeName = false := by
              cases h : objectTypeNameBool schema typeName
              · rfl
              · contradiction
            cases hruntime :
                abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType
                  (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
                    rightChildRootSelectionSet tag) with
            | none =>
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName typeName = true
                · simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hinclude,
                    executeCollectedFields_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
                      schema leftChildRootSelectionSet
                      rightChildRootSelectionSet targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime variableValues fuel typeName tag]
                · have hincludeFalse :
                      schema.typeIncludesObjectBool typeName typeName =
                        false := by
                    cases h : schema.typeIncludesObjectBool typeName typeName
                    · rfl
                    · contradiction
                  simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hincludeFalse]
            | some runtimeType =>
                by_cases hinclude :
                    schema.typeIncludesObjectBool typeName runtimeType = true
                · simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hinclude,
                    executeCollectedFields_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
                      schema leftChildRootSelectionSet
                      rightChildRootSelectionSet targetParent leftField
                      rightField leftArguments rightArguments leftRuntime
                      rightRuntime variableValues fuel runtimeType tag]
                · have hincludeFalse :
                      schema.typeIncludesObjectBool typeName runtimeType =
                        false := by
                    cases h :
                        schema.typeIncludesObjectBool typeName runtimeType
                    · rfl
                    · contradiction
                  simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
                    hcomposite, hobjectFalse, hruntime, hincludeFalse]
        · have hcompositeFalse :
              (TypeRef.named typeName).isCompositeBool schema = false := by
            cases h : (TypeRef.named typeName).isCompositeBool schema
            · rfl
            · contradiction
          simp [Execution.completeValue, fieldPairProbeHeadResolverValue,
            hcompositeFalse]
end

theorem executeSelectionSetAsResponse_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
    (schema : Schema)
    (leftChildRootSelectionSet rightChildRootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : Execution.CoercedArguments)
    (leftRuntime rightRuntime : Name)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType runtimeType : Name) (tag : FieldPairProbeTag)
    (selectionSet : List Selection)
    : Execution.executeSelectionSetAsResponse schema
        (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
          rightChildRootSelectionSet targetParent leftField rightField
          leftArguments rightArguments leftRuntime rightRuntime)
        variableValues fuel parentType (.object runtimeType (some tag))
        selectionSet
      = Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema
            (fieldPairSideRuntimeProbeRoot leftChildRootSelectionSet
              rightChildRootSelectionSet tag)
            targetParent leftField rightField leftArguments rightArguments)
          variableValues fuel parentType (.object runtimeType (some tag))
          selectionSet := by
  simp [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
    Execution.executeRootSelectionSet]
  rw [
    executeCollectedFields_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
      schema leftChildRootSelectionSet rightChildRootSelectionSet
      targetParent leftField rightField leftArguments rightArguments
      leftRuntime rightRuntime variableValues fuel runtimeType tag
      (Execution.collectFields schema variableValues parentType
        (.object runtimeType (some tag)) selectionSet)]

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_runtimeProbe_taggedWitness
    {schema : Schema} {rootSelectionSet childRootSelectionSet : List Selection}
    {variableValues : Execution.VariableValues} {fuel : Nat}
    {parentType runtimeType targetParent leftField rightField : Name}
    {leftArguments rightArguments : Execution.CoercedArguments}
    {selectionSet : List Selection} (leftRuntime rightRuntime : Name)
    : taggedSelectionSetResponseDiffWitness schema childRootSelectionSet
        variableValues fuel parentType runtimeType targetParent leftField
        rightField leftArguments rightArguments selectionSet
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues fuel runtimeType
              (projectionTargetResolverValue
                (.object runtimeType (some FieldPairProbeTag.left)))
              selectionSet).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues fuel runtimeType
              (projectionTargetResolverValue
                (.object runtimeType (some FieldPairProbeTag.right)))
              selectionSet).data := by
  intro hwitness hsemantic
  have hraw :
      ¬ Execution.ResponseValue.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema childRootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues fuel runtimeType
          (.object runtimeType (some FieldPairProbeTag.left))
          selectionSet).data
        (Execution.executeSelectionSetAsResponse schema
          (fieldPairProbeResolvers schema childRootSelectionSet targetParent
            leftField rightField leftArguments rightArguments)
          variableValues fuel runtimeType
          (.object runtimeType (some FieldPairProbeTag.right))
          selectionSet).data :=
    responseData_not_semanticEquivalent_of_taggedSelectionSetResponseDiffWitness
      hwitness
  have hleftProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel targetParent leftField rightField leftArguments
      rightArguments runtimeType
      (.object runtimeType (some FieldPairProbeTag.left)) selectionSet
  have hrightProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues fuel targetParent leftField rightField leftArguments
      rightArguments runtimeType
      (.object runtimeType (some FieldPairProbeTag.right)) selectionSet
  have hleftTagged :=
    executeSelectionSetAsResponse_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
      schema childRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime variableValues
      fuel runtimeType runtimeType FieldPairProbeTag.left selectionSet
  have hrightTagged :=
    executeSelectionSetAsResponse_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
      schema childRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime variableValues
      fuel runtimeType runtimeType FieldPairProbeTag.right selectionSet
  exact hraw (by
    simpa [hleftProjection, hrightProjection, hleftTagged, hrightTagged]
      using hsemantic)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_runtimeProbe_taggedPair
    {schema : Schema} {rootSelectionSet childRootSelectionSet : List Selection}
    {variableValues : Execution.VariableValues} {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntime rightRuntime targetParent
      leftField rightField
      : Name}
    {leftArguments rightArguments : Execution.CoercedArguments}
    {left right : List Selection}
    : ¬ Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema childRootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues leftFuel leftParentType
            (.object leftRuntime (some FieldPairProbeTag.left))
            left).data
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema childRootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues rightFuel rightParentType
            (.object rightRuntime (some FieldPairProbeTag.right))
            right).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues leftFuel leftParentType
              (projectionTargetResolverValue
                (.object leftRuntime (some FieldPairProbeTag.left)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
                  targetParent leftField rightField leftArguments rightArguments
                  leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues rightFuel rightParentType
              (projectionTargetResolverValue
                (.object rightRuntime (some FieldPairProbeTag.right)))
              right).data := by
  intro hraw hsemantic
  have hleftProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues leftFuel targetParent leftField rightField leftArguments
      rightArguments leftParentType
      (.object leftRuntime (some FieldPairProbeTag.left)) left
  have hrightProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairRuntimeProbeResolvers schema childRootSelectionSet
        targetParent leftField rightField leftArguments rightArguments
        leftRuntime rightRuntime)
      variableValues rightFuel targetParent leftField rightField
      leftArguments rightArguments rightParentType
      (.object rightRuntime (some FieldPairProbeTag.right)) right
  have hleftTagged :=
    executeSelectionSetAsResponse_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
      schema childRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime variableValues
      leftFuel leftParentType leftRuntime FieldPairProbeTag.left left
  have hrightTagged :=
    executeSelectionSetAsResponse_fieldPairRuntimeProbe_tagged_eq_fieldPairProbe
      schema childRootSelectionSet targetParent leftField rightField
      leftArguments rightArguments leftRuntime rightRuntime variableValues
      rightFuel rightParentType rightRuntime FieldPairProbeTag.right right
  exact hraw (by
    simpa [hleftProjection, hrightProjection, hleftTagged, hrightTagged]
      using hsemantic)

theorem
    responseData_not_semanticEquivalent_of_fieldPairOrDeepSuccess_sideRuntimeProbe_taggedPair
    {schema : Schema}
    {rootSelectionSet leftChildRootSelectionSet rightChildRootSelectionSet
      : List Selection}
    {variableValues : Execution.VariableValues} {leftFuel rightFuel : Nat}
    {leftParentType rightParentType leftRuntime rightRuntime targetParent
      leftField rightField
      : Name}
    {leftArguments rightArguments : Execution.CoercedArguments}
    {left right : List Selection}
    : ¬ Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema leftChildRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments)
            variableValues leftFuel leftParentType
            (.object leftRuntime (some FieldPairProbeTag.left))
            left).data
          (Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rightChildRootSelectionSet
              targetParent leftField rightField leftArguments rightArguments)
            variableValues rightFuel rightParentType
            (.object rightRuntime (some FieldPairProbeTag.right))
            right).data
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                  rightChildRootSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues leftFuel leftParentType
              (projectionTargetResolverValue
                (.object leftRuntime (some FieldPairProbeTag.left)))
              left).data
            (Execution.executeSelectionSetAsResponse schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
                  rightChildRootSelectionSet targetParent leftField rightField
                  leftArguments rightArguments leftRuntime rightRuntime)
                targetParent leftField rightField leftArguments rightArguments)
              variableValues rightFuel rightParentType
              (projectionTargetResolverValue
                (.object rightRuntime (some FieldPairProbeTag.right)))
              right).data := by
  intro hraw hsemantic
  have hleftProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
        rightChildRootSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      variableValues leftFuel targetParent leftField rightField leftArguments
      rightArguments leftParentType
      (.object leftRuntime (some FieldPairProbeTag.left)) left
  have hrightProjection :=
    executeSelectionSetAsResponse_fieldPairOrDeepSuccessResolvers_projectionTargetResolverValue
      schema rootSelectionSet
      (fieldPairSideRuntimeProbeResolvers schema leftChildRootSelectionSet
        rightChildRootSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      variableValues rightFuel targetParent leftField rightField
      leftArguments rightArguments rightParentType
      (.object rightRuntime (some FieldPairProbeTag.right)) right
  have hleftTagged :=
    executeSelectionSetAsResponse_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
      schema leftChildRootSelectionSet rightChildRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime variableValues leftFuel leftParentType leftRuntime
      FieldPairProbeTag.left left
  have hrightTagged :=
    executeSelectionSetAsResponse_fieldPairSideRuntimeProbe_tagged_eq_fieldPairProbe
      schema leftChildRootSelectionSet rightChildRootSelectionSet targetParent
      leftField rightField leftArguments rightArguments leftRuntime
      rightRuntime variableValues rightFuel rightParentType rightRuntime
      FieldPairProbeTag.right right
  exact hraw (by
    simpa [hleftProjection, hrightProjection, hleftTagged, hrightTagged,
      fieldPairSideRuntimeProbeRoot] using hsemantic)

end GroundTypeNormalization

end NormalForm

end GraphQL
