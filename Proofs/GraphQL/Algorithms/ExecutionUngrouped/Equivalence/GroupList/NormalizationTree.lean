import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.FreshPlanNormalizes

/-!
Normalization-tree witnesses for group-list fresh plans.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance groupListNormalizationTreeResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

inductive SelectionSetFreshPlanNormalizationTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List Selection -> List Selection -> Prop where
  | nil
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source [] []
  | ofNormalizes {raw normalized : List Selection}
    (normalization
      : SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source raw normalized)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source raw normalized
  | ofPlan {selectionSet : List Selection}
    (plan
      : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source selectionSet)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet
  | ofHeadDisjointTree {selectionSet : List Selection}
    (tree
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet
  | executableFieldSelectionsResponseNamesNodup
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source (executableFieldSelections fields)
        (executableFieldSelections fields)
  | appendDisjoint {rawLeft rawRight normalizedLeft normalizedRight : List Selection}
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source rawLeft normalizedLeft
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source rawRight normalizedRight
      -> GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            rawLeft)
          (GraphQL.Execution.collectFields schema variableValues parentType source
            rawRight)
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source (rawLeft ++ rawRight)
          (normalizedLeft ++ normalizedRight)
  | consDisjoint
    {selection : Selection} {rest normalizedSelection normalizedRest : List Selection}
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source [selection] normalizedSelection
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source rest normalizedRest
      -> GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [selection])
          (GraphQL.Execution.collectFields schema variableValues parentType source rest)
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source (selection :: rest)
          (normalizedSelection ++ normalizedRest)
  | field (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet]
        [.field responseName fieldName arguments directives selectionSet]
  | fieldSkipped (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : selectionDirectivesAllowBool variableValues directives = false
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.field responseName fieldName arguments directives selectionSet] []
  | inlineFragmentNone (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    : (selectionDirectivesAllowBool variableValues directives = true
        -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
            completionDepth parentType source rawChild normalizedChild)
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment none directives rawChild]
          [.inlineFragment none directives normalizedChild]
  | inlineFragmentNoneFlatten (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    : selectionDirectivesAllowBool variableValues directives = true
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source rawChild normalizedChild
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment none directives rawChild] normalizedChild
  | inlineFragmentNoneSkipped (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : selectionDirectivesAllowBool variableValues directives = false
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment none directives selectionSet] []
  | inlineFragmentSome (typeCondition : Name)
    (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    : (selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
            completionDepth parentType source rawChild normalizedChild)
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment (some typeCondition) directives rawChild]
          [.inlineFragment (some typeCondition) directives normalizedChild]
  | inlineFragmentSomeFlatten (typeCondition : Name)
    (directives : List DirectiveApplication)
    {rawChild normalizedChild : List Selection}
    : selectionDirectivesAllowBool variableValues directives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source rawChild normalizedChild
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment (some typeCondition) directives rawChild]
          normalizedChild
  | inlineFragmentSomeSkipped (typeCondition : Name)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : selectionDirectivesAllowBool variableValues directives = false
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment (some typeCondition) directives selectionSet] []
  | inlineFragmentSomeDoesNotApply (typeCondition : Name)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : selectionDirectivesAllowBool variableValues directives = true
      -> doesFragmentTypeApplyBool schema parentType source typeCondition = false
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment (some typeCondition) directives selectionSet] []
  | executableFieldSinglePrefixDuplicateFreshMiddle
    (first later : ExecutableField) (middle : List ExecutableField)
    : later.responseName = first.responseName
      -> (∃ fieldDefinition,
            schema.lookupField parentType later.fieldName = some fieldDefinition)
      -> (∀ field,
            field ∈ [first] ++ (middle ++ [later]) -> field.parentType = parentType)
      -> (middle.map (fun field => field.responseName)).Nodup
      -> later.responseName ∉ middle.map (fun field => field.responseName)
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          (executableFieldSelections ([first] ++ (middle ++ [later])))
          (executableFieldSelections ([first] ++ [later] ++ middle))
  | duplicateFieldBlockNormalize
    (first later : ExecutableField) (middle suffix : List Selection)
    : later.responseName = first.responseName
      -> (∃ fieldDefinition,
            schema.lookupField parentType later.fieldName = some fieldDefinition)
      -> first.responseName
          ∉ (GraphQL.Execution.collectFields schema variableValues parentType
              source middle).map
              Prod.fst
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source middle
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later])
            ++ suffix)
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)
  | duplicateFieldBlockNormalizeHeadDisjointMiddle
    (first later : ExecutableField) (middle suffix : List Selection)
    : later.responseName = first.responseName
      -> (∃ fieldDefinition,
            schema.lookupField parentType later.fieldName = some fieldDefinition)
      -> first.responseName
          ∉ (GraphQL.Execution.collectFields schema variableValues parentType
              source middle).map
              Prod.fst
      -> SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source middle
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later])
            ++ suffix)
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)
  | duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix
    (first later : ExecutableField) (middle suffix : List Selection)
    : later.responseName = first.responseName
      -> ExecutableFieldsParent parentType [first, later]
      -> (∃ fieldDefinition,
            schema.lookupField parentType later.fieldName = some fieldDefinition)
      -> first.responseName
          ∉ (GraphQL.Execution.collectFields schema variableValues parentType
              source middle).map
              Prod.fst
      -> GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later]))
          (GraphQL.Execution.collectFields schema variableValues parentType source suffix)
      -> SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source middle
      -> SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source suffix
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          ((executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later])
            ++ suffix)
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)

namespace SelectionSetFreshPlanNormalizationTree

theorem normalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw normalized : List Selection}
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source raw normalized
      -> SelectionSetFreshPlanNormalizes schema resolvers variableValues
          completionDepth parentType source raw normalized := by
  intro tree
  induction tree with
  | nil =>
      exact SelectionSetFreshPlanNormalizes.nil schema resolvers variableValues
        completionDepth parentType source
  | ofNormalizes normalization =>
      exact normalization
  | ofPlan plan =>
      exact SelectionSetFreshPlanNormalizes.of_plan plan
  | ofHeadDisjointTree tree =>
      exact SelectionSetFreshPlanNormalizes.of_headDisjointTree schema
        resolvers variableValues completionDepth parentType source tree
  | executableFieldSelectionsResponseNamesNodup fields hnodup hparents =>
      exact
        SelectionSetFreshPlanNormalizes.of_executableFieldSelections_responseNamesNodup
          schema resolvers variableValues completionDepth parentType source
          fields hnodup hparents
  | appendDisjoint left right hdisjoint ihleft ihright =>
      exact SelectionSetFreshPlanNormalizes.appendDisjoint ihleft ihright
        hdisjoint
  | consDisjoint head tail hdisjoint ihhead ihtail =>
      exact SelectionSetFreshPlanNormalizes.consDisjoint ihhead ihtail
        hdisjoint
  | field responseName fieldName arguments directives selectionSet =>
      exact SelectionSetFreshPlanNormalizes.field schema resolvers
        variableValues completionDepth parentType source responseName fieldName
        arguments directives selectionSet
  | fieldSkipped responseName fieldName arguments directives selectionSet
      hskip =>
      exact SelectionSetFreshPlanNormalizes.fieldSkipped responseName fieldName
        arguments directives selectionSet hskip
  | inlineFragmentNone directives child ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentNone directives
        (fun hallows => ihchild hallows)
  | inlineFragmentNoneFlatten directives hallows child ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentNoneFlatten
        directives hallows ihchild
  | inlineFragmentNoneSkipped directives selectionSet hskip =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentNoneSkipped directives
        selectionSet hskip
  | inlineFragmentSome typeCondition directives child ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSome typeCondition
        directives (fun hallows happly => ihchild hallows happly)
  | inlineFragmentSomeFlatten typeCondition directives hallows happly child
      ihchild =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSomeFlatten
        typeCondition directives hallows happly ihchild
  | inlineFragmentSomeSkipped typeCondition directives selectionSet hskip =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSomeSkipped
        typeCondition directives selectionSet hskip
  | inlineFragmentSomeDoesNotApply typeCondition directives selectionSet
      hallows hnotApply =>
      exact SelectionSetFreshPlanNormalizes.inlineFragmentSomeDoesNotApply
        typeCondition directives selectionSet hallows hnotApply
  | executableFieldSinglePrefixDuplicateFreshMiddle first later middle
      hsameResponse hlaterLookup hparents hmiddleNodup hnotMiddle =>
      exact
        SelectionSetFreshPlanNormalizes.executableFieldSinglePrefixDuplicateFreshMiddle
          first later middle hsameResponse hlaterLookup hparents hmiddleNodup
          hnotMiddle
  | duplicateFieldBlockNormalize first later middle suffix hsameResponse
      hlaterLookup hnotMiddle hmiddle hnormalized =>
      exact SelectionSetFreshPlanNormalizes.duplicateFieldBlockNormalize schema
        resolvers variableValues completionDepth parentType source first later
        middle suffix hsameResponse hlaterLookup hnotMiddle hmiddle
        hnormalized
  | duplicateFieldBlockNormalizeHeadDisjointMiddle first later middle suffix
      hsameResponse hlaterLookup hnotMiddle hmiddle hnormalized =>
      exact
        SelectionSetFreshPlanNormalizes.duplicateFieldBlockNormalizeHeadDisjointMiddle
          schema resolvers variableValues completionDepth parentType source
          first later middle suffix hsameResponse hlaterLookup hnotMiddle hmiddle
          hnormalized
  | duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix first later middle
      suffix hsameResponse hparents hlaterLookup hnotMiddle hdisjoint hmiddle
      hsuffix =>
      exact
        SelectionSetFreshPlanNormalizes.duplicateFieldBlockNormalizeHeadDisjointMiddleSuffix
          schema resolvers variableValues completionDepth parentType source
          first later middle suffix hsameResponse hparents hlaterLookup
          hnotMiddle hdisjoint hmiddle hsuffix

theorem of_derivation
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {selectionSet : List Selection}
    (derivation
      : FreshPrefixSelectionDerivation schema variableValues parentType source
          selectionSet)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source selectionSet selectionSet :=
  .ofPlan
    (FreshPrefixSelectionPlan.of_derivation schema resolvers variableValues
      completionDepth parentType source derivation)

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)))
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) :=
  .ofPlan
    (FreshPrefixSelectionPlan.of_collectedCollectFields schema resolvers
      variableValues completionDepth parentType source selectionSet)

theorem of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source selectionSet selectionSet :=
  fun hall hfree hnodup =>
    .ofPlan
      (FreshPrefixSelectionPlan.of_allFields_directiveFree_responseNamesNodup
        schema resolvers variableValues completionDepth parentType source
        selectionSet hall hfree hnodup)

theorem of_allFields_directiveFree_normal
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.selectionSetNormal schema parentType selectionSet
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source selectionSet selectionSet := by
  intro hall hfree hnormal
  have hnodup : NormalForm.responseNamesNodup selectionSet := by
    have hnonRedundant : NormalForm.selectionSetNonRedundant selectionSet :=
      hnormal.2
    unfold NormalForm.selectionSetNonRedundant at hnonRedundant
    exact hnonRedundant.1
  exact
    of_allFields_directiveFree_responseNamesNodup schema resolvers
      variableValues completionDepth parentType source selectionSet hall hfree
      hnodup

theorem of_rawFreshFlat_collectedCollectFields
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw : List Selection}
    (hrawFreshFlat
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source raw)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source raw
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source raw))) :=
  .ofNormalizes
    (SelectionSetFreshPlanNormalizes.of_rawFreshFlat_collectedCollectFields hrawFreshFlat)

theorem fieldAllowedDropDirectives
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallows : selectionDirectivesAllowBool variableValues directives = true)
    : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
        completionDepth parentType source
        [.field responseName fieldName arguments directives selectionSet]
        [.field responseName fieldName arguments [] selectionSet] :=
  .ofNormalizes
    (SelectionSetFreshPlanNormalizes.fieldAllowedDropDirectives responseName
      fieldName arguments directives selectionSet hallows)

theorem of_normalizeSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionSetDirectiveFree selectionSet
      -> SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          (NormalForm.normalizeSelectionSet schema parentType selectionSet)
          (NormalForm.normalizeSelectionSet schema parentType selectionSet) :=
  fun hfree =>
    .ofNormalizes
      (SelectionSetFreshPlanNormalizes.of_normalizeSelectionSet schema
        resolvers variableValues completionDepth parentType source
        selectionSet hfree)

theorem exists_fieldExecutable
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : ∃ normalizedSelectionSet,
        SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.field responseName fieldName arguments directives selectionSet]
          normalizedSelectionSet := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · exact
      ⟨[.field responseName fieldName arguments [] selectionSet],
        fieldAllowedDropDirectives responseName fieldName arguments
          directives selectionSet hallows⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      ⟨[], .fieldSkipped responseName fieldName arguments directives
        selectionSet hskip⟩

theorem exists_allFields_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ selectionSet,
        NormalForm.selectionsAllFields selectionSet
        -> NormalForm.responseNamesNodup selectionSet
        -> ∃ normalizedSelectionSet,
            SelectionSetFreshPlanNormalizationTree schema resolvers
              variableValues completionDepth parentType source selectionSet
              normalizedSelectionSet
  | [], _hall, _hnodup => by
      exact ⟨[], .nil⟩
  | selection :: rest, hall, hnodup => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hnodupCons :
              (responseName :: rest.filterMap Selection.responseName?).Nodup := by
            simpa [NormalForm.responseNamesNodup, Selection.responseName?]
              using hnodup
          have hresponseFresh :
              responseName ∉ rest.filterMap Selection.responseName? :=
            (List.nodup_cons.mp hnodupCons).1
          have hrestNodup : NormalForm.responseNamesNodup rest := by
            simpa [NormalForm.responseNamesNodup] using
              (List.nodup_cons.mp hnodupCons).2
          rcases
              exists_allFields_responseNamesNodup schema resolvers
                variableValues completionDepth parentType source rest
                hrestAll hrestNodup with
            ⟨normalizedRest, hrestTree⟩
          by_cases hallows :
              selectionDirectivesAllowBool variableValues directives = true
          · have hheadTree :
                SelectionSetFreshPlanNormalizationTree schema resolvers
                  variableValues completionDepth parentType source
                  [.field responseName fieldName arguments directives
                    selectionSet]
                  [.field responseName fieldName arguments [] selectionSet] :=
              fieldAllowedDropDirectives responseName fieldName arguments
                directives selectionSet hallows
            have hrestFree :
                NormalForm.selectionSetResponseNameFree schema parentType
                  responseName rest :=
              FreshPrefixSelectionDerivation.selectionSetResponseNameFree_of_allFields_responseNamesNodup
                schema parentType responseName rest hrestAll hresponseFresh
            have hrestNotMem :
                responseName ∉
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest).map Prod.fst :=
              FreshPrefixSelectionDerivation.collectFields_responseName_not_mem_of_allFields_responseNameFree
                schema variableValues parentType source responseName rest
                hrestAll hrestFree
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    [.field responseName fieldName arguments directives
                      selectionSet])
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest) := by
              intro candidate hleft hright
              have hleftEq : candidate = responseName := by
                simpa [GraphQL.Execution.collectFields,
                  GraphQL.Execution.collectSelection,
                  GraphQL.Execution.mergeExecutableGroups, hallows] using hleft
              exact hrestNotMem (by simpa [hleftEq] using hright)
            exact
              ⟨[.field responseName fieldName arguments [] selectionSet]
                  ++ normalizedRest,
                .consDisjoint hheadTree hrestTree hdisjoint⟩
          · have hskip :
                selectionDirectivesAllowBool variableValues directives =
                  false := by
              cases h :
                  selectionDirectivesAllowBool variableValues directives
              · rfl
              · contradiction
            have hheadTree :
                SelectionSetFreshPlanNormalizationTree schema resolvers
                  variableValues completionDepth parentType source
                  [.field responseName fieldName arguments directives
                    selectionSet] [] :=
              .fieldSkipped responseName fieldName arguments directives
                selectionSet hskip
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    [.field responseName fieldName arguments directives
                      selectionSet])
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest) := by
              intro candidate hleft _hright
              simp [GraphQL.Execution.collectFields,
                GraphQL.Execution.collectSelection,
                GraphQL.Execution.mergeExecutableGroups, hskip] at hleft
            exact
              ⟨normalizedRest,
                by
                  simpa using
                    (SelectionSetFreshPlanNormalizationTree.consDisjoint
                      hheadTree hrestTree hdisjoint)⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem exists_allFields_directiveFree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> executionSelectionSetLookupValid schema parentType selectionSet
      -> ∃ normalizedSelectionSet,
          SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
            completionDepth parentType source selectionSet
            normalizedSelectionSet := by
  intro hall hfree hlookupValid
  rcases
      SelectionSetFreshPlanNormalizes.exists_allFields_directiveFree schema
        resolvers variableValues completionDepth parentType source selectionSet
        hall hfree hlookupValid with
    ⟨normalizedSelectionSet, hnormalization⟩
  exact ⟨normalizedSelectionSet, .ofNormalizes hnormalization⟩

theorem exists_inlineFragmentNone
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (child
      : selectionDirectivesAllowBool variableValues directives = true
        -> ∃ normalizedChild,
            SelectionSetFreshPlanNormalizationTree schema resolvers
              variableValues completionDepth parentType source selectionSet
              normalizedChild)
    : ∃ normalizedSelectionSet,
        SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment none directives selectionSet]
          normalizedSelectionSet := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · rcases child hallows with ⟨normalizedChild, hchild⟩
    exact ⟨normalizedChild, .inlineFragmentNoneFlatten directives hallows hchild⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact ⟨[], .inlineFragmentNoneSkipped directives selectionSet hskip⟩

theorem exists_inlineFragmentSome
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    (typeCondition : Name) (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (child
      : selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> ∃ normalizedChild,
            SelectionSetFreshPlanNormalizationTree schema resolvers
              variableValues completionDepth parentType source selectionSet
              normalizedChild)
    : ∃ normalizedSelectionSet,
        SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source
          [.inlineFragment (some typeCondition) directives selectionSet]
          normalizedSelectionSet := by
  by_cases hallows :
      selectionDirectivesAllowBool variableValues directives = true
  · by_cases happly :
        doesFragmentTypeApplyBool schema parentType source typeCondition = true
    · rcases child hallows happly with ⟨normalizedChild, hchild⟩
      exact
        ⟨normalizedChild,
          .inlineFragmentSomeFlatten typeCondition directives hallows happly
            hchild⟩
    · have hnotApply :
          doesFragmentTypeApplyBool schema parentType source typeCondition =
            false := by
        cases h :
            doesFragmentTypeApplyBool schema parentType source typeCondition
        · rfl
        · contradiction
      exact
        ⟨[],
          .inlineFragmentSomeDoesNotApply typeCondition directives selectionSet
            hallows hnotApply⟩
  · have hskip :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases h :
          selectionDirectivesAllowBool variableValues directives
      · rfl
      · contradiction
    exact
      ⟨[], .inlineFragmentSomeSkipped typeCondition directives selectionSet hskip⟩

theorem transNormalizes
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {raw middle normalized : List Selection}
    (left
      : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source raw middle)
    (right
      : SelectionSetFreshPlanNormalizationTree schema resolvers variableValues
          completionDepth parentType source middle normalized)
    : SelectionSetFreshPlanNormalizes schema resolvers variableValues
        completionDepth parentType source raw normalized :=
  SelectionSetFreshPlanNormalizes.trans left.normalizes right.normalizes

end SelectionSetFreshPlanNormalizationTree

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_allOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollects schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++ executableFieldSelections [later])
        (.object []) := by
  obtain ⟨suffix, hsuffix⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)))
      []
  exact
    VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
      schema resolvers variableValues completionDepth parentType source first
      later middle
        (executeField schema resolvers variableValues completionDepth source
          none
          (executableField parentType first.responseName first.fieldName
            first.arguments first.selectionSet))
        (executeField schema resolvers variableValues completionDepth source
          (some
            (executeField schema resolvers variableValues completionDepth source
              none
              (executableField parentType first.responseName first.fieldName
                first.arguments first.selectionSet)))
          (executableField parentType later.responseName later.fieldName
            later.arguments later.selectionSet))
      suffix hsameResponse hlaterLookup hnotMiddle rfl rfl hsuffix
      (hmiddle _)

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
