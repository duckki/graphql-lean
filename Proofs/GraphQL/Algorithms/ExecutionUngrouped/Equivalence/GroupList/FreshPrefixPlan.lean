import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.DuplicateFieldMiddle

/-!
Fresh-prefix selection plans for group-list selection sets.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance groupListFreshPrefixPlanResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

inductive FreshPrefixSelectionPlan
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List Selection -> Prop where
  | nil
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source []
  | appendDisjoint (left right : List Selection)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source left
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source right
      -> GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right)
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source (left ++ right)
  | sameGroup (responseName : Name) (fields : List ExecutableField)
    : (∀ field, field ∈ fields -> field.responseName = responseName)
      -> (∀ field, field ∈ fields -> field.parentType = parentType)
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source (executableFieldSelections fields)
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
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          ((executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later])
            ++ suffix)
  | consDisjoint (selection : Selection) (rest : List Selection)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source [selection]
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source rest
      -> GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [selection])
          (GraphQL.Execution.collectFields schema variableValues parentType source rest)
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source (selection :: rest)
  | duplicateFieldBlock (first later : ExecutableField) (middle suffix : List Selection)
    : later.responseName = first.responseName
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
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source middle
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source suffix
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          (executableFieldSelections [first]
            ++ middle
            ++ executableFieldSelections [later]
            ++ suffix)

inductive FreshPrefixSelectionDerivation
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : List Selection -> Prop where
  | nil : FreshPrefixSelectionDerivation schema variableValues parentType source []
  | appendDisjoint (left right : List Selection)
    : FreshPrefixSelectionDerivation schema variableValues parentType source left
      -> FreshPrefixSelectionDerivation schema variableValues parentType source right
      -> GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right)
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          (left ++ right)
  | sameGroup (responseName : Name) (fields : List ExecutableField)
    : (∀ field, field ∈ fields -> field.responseName = responseName)
      -> (∀ field, field ∈ fields -> field.parentType = parentType)
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          (executableFieldSelections fields)
  | inlineFragmentNone (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : (selectionDirectivesAllowBool variableValues directives = true
        -> FreshPrefixSelectionDerivation schema variableValues parentType source
            selectionSet)
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          [.inlineFragment none directives selectionSet]
  | inlineFragmentSome (typeCondition : Name)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    : (selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> FreshPrefixSelectionDerivation schema variableValues parentType source
            selectionSet)
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          [.inlineFragment (some typeCondition) directives selectionSet]
  | duplicateFieldBlockNormalize
    (first later : ExecutableField) (middle suffix : List Selection)
    : later.responseName = first.responseName
      -> (∃ fieldDefinition,
            schema.lookupField parentType later.fieldName = some fieldDefinition)
      -> first.responseName
          ∉ (GraphQL.Execution.collectFields schema variableValues parentType
              source middle).map
              Prod.fst
      -> FreshPrefixSelectionDerivation schema variableValues parentType source middle
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          ((executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later])
            ++ suffix)
  | consHeadDisjoint (selection : Selection) (rest : List Selection)
    : SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
        source selection
      -> FreshPrefixSelectionDerivation schema variableValues parentType source rest
      -> GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            [selection])
          (GraphQL.Execution.collectFields schema variableValues parentType source rest)
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          (selection :: rest)
  | duplicateFieldBlock (first later : ExecutableField) (middle suffix : List Selection)
    : later.responseName = first.responseName
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
      -> FreshPrefixSelectionDerivation schema variableValues parentType source middle
      -> FreshPrefixSelectionDerivation schema variableValues parentType source suffix
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          (executableFieldSelections [first]
            ++ middle
            ++ executableFieldSelections [later]
            ++ suffix)

namespace FreshPrefixSelectionDerivation

theorem single_of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection)
    (htree
      : SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
          source selection)
    : FreshPrefixSelectionDerivation schema variableValues parentType source
        [selection] :=
  .consHeadDisjoint selection [] htree .nil (by
      intro responseName _hleft hright
      simp [GraphQL.Execution.collectFields] at hright)

theorem of_headDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ selectionSet,
        SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source selectionSet
        -> (∀ selection,
              selection ∈ selectionSet
              -> SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
                  source selection)
        -> FreshPrefixSelectionDerivation schema variableValues parentType source
            selectionSet
  | [], _hdisjoint, _hchildren => .nil
  | selection :: rest, hdisjoint, hchildren => by
      rcases hdisjoint with ⟨hheadDisjoint, hrestDisjoint⟩
      exact .consHeadDisjoint selection rest
        (hchildren selection (by simp))
        (of_headDisjoint schema variableValues parentType source rest
          hrestDisjoint
          (by
            intro candidate hcandidate
            exact hchildren candidate (by simp [hcandidate])))
        hheadDisjoint

theorem of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (htree
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet)
    : FreshPrefixSelectionDerivation schema variableValues parentType source
        selectionSet := by
  have htree' :
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source selectionSet
        ∧ ∀ selection, selection ∈ selectionSet ->
            SelectionCollectFieldsHeadDisjointTree schema variableValues
              parentType source selection := by
    simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree
  rcases htree' with ⟨hdisjoint, hchildren⟩
  exact of_headDisjoint schema variableValues parentType source selectionSet
    hdisjoint hchildren

theorem duplicateFieldBlock_of_headDisjointTrees
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later]))
          (GraphQL.Execution.collectFields schema variableValues parentType source
            suffix))
    (hmiddle
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
          source middle)
    (hsuffix
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
          source suffix)
    : FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]
          ++ suffix) :=
  .duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
    hnotMiddle hdisjoint
    (of_headDisjointTree schema variableValues parentType source middle hmiddle)
    (of_headDisjointTree schema variableValues parentType source suffix hsuffix)

theorem duplicateFieldPair_of_headDisjointMiddle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
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
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
          source middle)
    : FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]) := by
  simpa using
    duplicateFieldBlock_of_headDisjointTrees schema variableValues parentType
      source first later middle [] hsameResponse hlaterLookup hnotMiddle
      (by
        intro responseName _hleft hright
        simp [GraphQL.Execution.collectFields] at hright)
      hmiddle
      (by
        simp [SelectionSetCollectFieldsHeadDisjointTree,
          SelectionSetCollectFieldsHeadDisjoint])

def singletonExecutableGroups : List ExecutableField -> List (Name × List ExecutableField)
  | [] => []
  | field :: rest =>
      (field.responseName, [field]) :: singletonExecutableGroups rest

theorem collectedExecutableFields_singletonExecutableGroups
    : ∀ fields, collectedExecutableFields (singletonExecutableGroups fields) = fields
  | [] => by
      simp [singletonExecutableGroups, collectedExecutableFields]
  | field :: rest => by
      simp [singletonExecutableGroups, collectedExecutableFields,
        collectedExecutableFields_singletonExecutableGroups rest]

theorem singletonExecutableGroups_mem_cons
    : ∀ {fields : List ExecutableField} {responseName : Name}
          {field : ExecutableField} {fieldsTail : List ExecutableField},
        (responseName, field :: fieldsTail) ∈ singletonExecutableGroups fields
        -> field ∈ fields ∧ fieldsTail = []
  | [], _responseName, _field, _fieldsTail, hmem => by
      simp [singletonExecutableGroups] at hmem
  | head :: rest, responseName, field, fieldsTail, hmem => by
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        cases fieldsTail with
        | nil =>
            simp at hfields
            subst field
            exact ⟨by simp, rfl⟩
        | cons tailHead tailRest =>
            simp at hfields
      · rcases singletonExecutableGroups_mem_cons htail with
          ⟨hfield, hfieldsTail⟩
        exact ⟨by simp [hfield], hfieldsTail⟩

theorem singletonExecutableGroups_map_fst
    : ∀ fields,
        (singletonExecutableGroups fields).map Prod.fst
        = fields.map (fun field => field.responseName)
  | [] => by
      simp [singletonExecutableGroups]
  | field :: rest => by
      simp [singletonExecutableGroups, singletonExecutableGroups_map_fst rest]

theorem pairKeysNodup_singletonExecutableGroups {fields : List ExecutableField}
    : (fields.map (fun field => field.responseName)).Nodup
      -> PairKeysNodup (singletonExecutableGroups fields) := by
  intro hnodup
  simpa [PairKeysNodup, singletonExecutableGroups_map_fst] using hnodup

theorem collectedGroupsFieldsNonempty_singletonExecutableGroups
    (fields : List ExecutableField)
    : CollectedGroupsFieldsNonempty (singletonExecutableGroups fields) := by
  intro responseName groupFields hmem
  induction fields with
  | nil =>
      simp [singletonExecutableGroups] at hmem
  | cons field rest ih =>
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponse, hfields⟩
        simp [hfields]
      · exact ih htail

theorem collectedGroupsResponseName_singletonExecutableGroups
    (fields : List ExecutableField)
    : CollectedGroupsResponseName (singletonExecutableGroups fields) := by
  intro responseName groupFields hmem
  induction fields generalizing responseName groupFields with
  | nil =>
      simp [singletonExecutableGroups] at hmem
  | cons field rest ih =>
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponse, hfields⟩
        subst responseName
        subst groupFields
        intro candidate hcandidate
        have hcandidateEq : candidate = field := by
          simpa using hcandidate
        subst candidate
        rfl
      · exact ih responseName groupFields htail

theorem collectedGroupsParent_singletonExecutableGroups
    {parentType : Name} {fields : List ExecutableField}
    : ExecutableFieldsParent parentType fields
      -> CollectedGroupsParent parentType (singletonExecutableGroups fields) := by
  intro hparents responseName groupFields hmem
  induction fields generalizing responseName groupFields with
  | nil =>
      simp [singletonExecutableGroups] at hmem
  | cons field rest ih =>
      simp [singletonExecutableGroups] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨_hresponse, hfields⟩
        subst groupFields
        intro candidate hcandidate
        have hcandidateEq : candidate = field := by
          simpa using hcandidate
        subst candidate
        exact hparents field (by simp)
      · exact ih
          (by
            intro restField hrestField
            exact hparents restField (by simp [hrestField]))
          responseName groupFields htail

theorem ExecutableFieldsParent_collectedExecutableFields {parentType : Name}
    : ∀ {groups : List (Name × List ExecutableField)},
        CollectedGroupsParent parentType groups
        -> ExecutableFieldsParent parentType (collectedExecutableFields groups)
  | [], _hparents => by
      intro field hfield
      simp [collectedExecutableFields] at hfield
  | (responseName, fields) :: rest, hparents => by
      intro field hfield
      simp [collectedExecutableFields] at hfield
      rcases hfield with hfield | hfield
      · exact hparents responseName fields (by simp) field hfield
      · exact
          ExecutableFieldsParent_collectedExecutableFields
            (CollectedGroupsParent_tail hparents) field hfield

theorem collectFields_executableFieldSelections_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField) (responseName : Name)
    : responseName
        ∈ (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections fields)).map
            Prod.fst
      ↔ responseName ∈ fields.map (fun field => field.responseName) := by
  induction fields with
  | nil =>
      simp [executableFieldSelections, GraphQL.Execution.collectFields]
  | cons field rest ih =>
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection field) =
            [(field.responseName,
              [executableField parentType field.responseName field.fieldName
                field.arguments field.selectionSet])] := by
        simp [executableFieldSelection, executableField,
          GraphQL.Execution.collectSelection, selectionDirectivesAllowBool_empty]
      simp only [executableFieldSelections, List.map_cons,
        GraphQL.Execution.collectFields]
      rw [hhead]
      rw [mergeExecutableGroups_key_mem]
      constructor
      · intro hmem
        rcases hmem with hheadMem | htailMem
        · have hheadEq : responseName = field.responseName := by
            simpa using hheadMem
          simp [hheadEq]
        · have htail : responseName ∈ rest.map (fun field => field.responseName) :=
            ih.mp htailMem
          simp [htail]
      · intro hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hheadMem | htailMem
        · left
          simp [hheadMem]
        · right
          exact ih.mpr htailMem

theorem executableFields_first_responseName_split (responseName : Name)
    : ∀ fields : List ExecutableField,
        responseName ∈ fields.map (fun field => field.responseName)
        -> ∃ middle later suffix,
            fields = middle ++ later :: suffix
            ∧ later.responseName = responseName
            ∧ responseName ∉ middle.map (fun field => field.responseName)
  | [], hmem => by
      simp at hmem
  | field :: rest, hmem => by
      by_cases hfield : field.responseName = responseName
      · exact ⟨[], field, rest, by simp, hfield, by simp⟩
      · have hrest :
            responseName ∈ rest.map (fun field => field.responseName) := by
          simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · exact False.elim (hfield hhead.symm)
          · exact htail
        rcases executableFields_first_responseName_split responseName rest
          hrest with
          ⟨middle, later, suffix, hsplit, hlater, hnotMiddle⟩
        refine ⟨field :: middle, later, suffix, ?_, hlater, ?_⟩
        · simp [hsplit]
        · intro hmemMiddle
          simp only [List.map_cons, List.mem_cons] at hmemMiddle
          rcases hmemMiddle with hhead | hmiddle
          · exact hfield hhead.symm
          · exact hnotMiddle hmiddle

theorem executableFieldConsFresh
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField) (rest : List ExecutableField)
    (hfresh : field.responseName ∉ rest.map (fun field => field.responseName))
    (hrest
      : FreshPrefixSelectionDerivation schema variableValues parentType source
          (executableFieldSelections rest))
    : FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections (field :: rest)) := by
  simpa [executableFieldSelections] using
    FreshPrefixSelectionDerivation.consHeadDisjoint
      (schema := schema) (variableValues := variableValues)
      (parentType := parentType) (source := source)
      (selection := executableFieldSelection field)
      (rest := executableFieldSelections rest)
      (by simp [executableFieldSelection,
        SelectionCollectFieldsHeadDisjointTree])
      hrest
      (by
        intro responseName hhead htail
        have hheadEq : responseName = field.responseName := by
          simpa [GraphQL.Execution.collectFields,
            GraphQL.Execution.collectSelection,
            GraphQL.Execution.mergeExecutableGroups,
            executableFieldSelection, executableField,
            selectionDirectivesAllowBool_empty] using hhead
        have htailName :
            responseName ∈ rest.map (fun field => field.responseName) :=
          (collectFields_executableFieldSelections_key_mem schema
            variableValues parentType source rest responseName).mp htail
        exact hfresh (by simpa [hheadEq] using htailName))

theorem of_collectedGroups
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        PairKeysNodup groups
        -> CollectedGroupsFieldsNonempty groups
        -> CollectedGroupsResponseName groups
        -> CollectedGroupsParent parentType groups
        -> FreshPrefixSelectionDerivation schema variableValues parentType source
            (executableFieldSelections (collectedExecutableFields groups))
  | [], _hnodup, _hnonempty, _hresponses, _hparents => by
      simpa [collectedExecutableFields, executableFieldSelections] using
        (FreshPrefixSelectionDerivation.nil
          (schema := schema) (variableValues := variableValues)
          (parentType := parentType) (source := source))
  | (responseName, fields) :: rest, hnodup, hnonempty, hresponses, hparents =>
      by
        have hrestNodup : PairKeysNodup rest :=
          PairKeysNodup.tail hnodup
        have hrestNonempty : CollectedGroupsFieldsNonempty rest :=
          CollectedGroupsFieldsNonempty_tail hnonempty
        have hrestResponses : CollectedGroupsResponseName rest :=
          CollectedGroupsResponseName_tail hresponses
        have hrestParents : CollectedGroupsParent parentType rest :=
          CollectedGroupsParent_tail hparents
        have hfieldsNonempty : fields ≠ [] :=
          hnonempty responseName fields (by simp)
        cases fields with
        | nil =>
            exact False.elim (hfieldsNonempty rfl)
        | cons field fieldsTail =>
            have hheadResponse :
                ExecutableFieldsResponseName responseName
                  (field :: fieldsTail) :=
              hresponses responseName (field :: fieldsTail) (by simp)
            have hheadParent :
                ExecutableFieldsParent parentType (field :: fieldsTail) :=
              hparents responseName (field :: fieldsTail) (by simp)
            have hheadCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
                [(responseName, field :: fieldsTail)] :=
              collectFields_executableFieldSelections_same_group schema
                variableValues parentType source responseName
                (field :: fieldsTail) hheadResponse hheadParent
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) =
                rest :=
              collectFields_executableFieldSelections_collectedExecutableFields
                schema variableValues parentType source rest hrestNodup
                hrestNonempty hrestResponses hrestParents
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
              intro candidate hleft hright
              rw [hheadCollect] at hleft
              rw [hrestCollect] at hright
              exact
                executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
                  hnodup candidate hleft hright
            have hhead :
                FreshPrefixSelectionDerivation schema variableValues parentType
                  source (executableFieldSelections (field :: fieldsTail)) :=
              .sameGroup responseName (field :: fieldsTail) hheadResponse
                hheadParent
            have htail :
                FreshPrefixSelectionDerivation schema variableValues parentType
                  source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) :=
              of_collectedGroups schema variableValues parentType source rest
                hrestNodup hrestNonempty hrestResponses hrestParents
            simpa [collectedExecutableFields, executableFieldSelections] using
              FreshPrefixSelectionDerivation.appendDisjoint
                (schema := schema) (variableValues := variableValues)
                (parentType := parentType) (source := source)
                (executableFieldSelections (field :: fieldsTail))
                (executableFieldSelections (collectedExecutableFields rest))
                hhead htail hdisjoint

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) :=
  of_collectedGroups schema variableValues parentType source
    (GraphQL.Execution.collectFields schema variableValues parentType source selectionSet)
    (PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet))
    (collectFields_fieldsNonempty schema variableValues parentType source selectionSet)
    (collectFields_responseName schema variableValues parentType source selectionSet)
    (collectFields_parent schema variableValues parentType source selectionSet)

theorem of_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    : FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections fields) := by
  simpa [collectedExecutableFields_singletonExecutableGroups] using
    of_collectedGroups schema variableValues parentType source
      (singletonExecutableGroups fields)
      (pairKeysNodup_singletonExecutableGroups hnodup)
      (collectedGroupsFieldsNonempty_singletonExecutableGroups fields)
      (collectedGroupsResponseName_singletonExecutableGroups fields)
      (collectedGroupsParent_singletonExecutableGroups hparents)

theorem collectFields_executableFieldSelections_singletonExecutableGroups
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    : GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections fields)
      = singletonExecutableGroups fields := by
  simpa [collectedExecutableFields_singletonExecutableGroups] using
    collectFields_executableFieldSelections_collectedExecutableFields schema
      variableValues parentType source (singletonExecutableGroups fields)
      (pairKeysNodup_singletonExecutableGroups hnodup)
      (collectedGroupsFieldsNonempty_singletonExecutableGroups fields)
      (collectedGroupsResponseName_singletonExecutableGroups fields)
      (collectedGroupsParent_singletonExecutableGroups hparents)

theorem collectFields_executableFieldSelections_mem_cons
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {fields : List ExecutableField}
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    {responseName : Name} {field : ExecutableField}
    {fieldsTail : List ExecutableField}
    (hgroup
      : (responseName, field :: fieldsTail)
        ∈ GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections fields))
    : field ∈ fields ∧ fieldsTail = [] := by
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields) =
        singletonExecutableGroups fields :=
    collectFields_executableFieldSelections_singletonExecutableGroups schema
      variableValues parentType source fields hnodup hparents
  have hgroupSingle :
      (responseName, field :: fieldsTail) ∈
        singletonExecutableGroups fields := by
    rwa [hcollect] at hgroup
  exact singletonExecutableGroups_mem_cons hgroupSingle

theorem collectFields_executableFieldSelections_prefix_empty
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    {fields : List ExecutableField}
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    {responseName : Name} {field : ExecutableField}
    {fieldsTail prefixTail : List ExecutableField}
    (hgroup
      : (responseName, field :: fieldsTail)
        ∈ GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections fields))
    (hprefix : ∀ candidate, candidate ∈ prefixTail -> candidate ∈ fieldsTail)
    : field ∈ fields ∧ fieldsTail = [] ∧ prefixTail = [] := by
  rcases
      collectFields_executableFieldSelections_mem_cons schema variableValues
        parentType source hnodup hparents hgroup with
    ⟨hfield, hfieldsTail⟩
  have hprefixTail : prefixTail = [] := by
    cases prefixTail with
    | nil => rfl
    | cons head tail =>
        have hhead : head ∈ fieldsTail := hprefix head (by simp)
        simp [hfieldsTail] at hhead
  exact ⟨hfield, hfieldsTail, hprefixTail⟩

def executableFieldOfSelection (parentType : Name) : Selection -> ExecutableField
  | .field responseName fieldName arguments _directives selectionSet =>
      {
        parentType := parentType
        responseName := responseName
        fieldName := fieldName
        arguments := arguments
        selectionSet := selectionSet
      }
  | .inlineFragment _typeCondition _directives _selectionSet =>
      {
        parentType := parentType
        responseName := ""
        fieldName := ""
        arguments := []
        selectionSet := []
      }

theorem executableFieldSelections_map_executableFieldOfSelection (parentType : Name)
    : ∀ selectionSet,
        NormalForm.selectionsAllFields selectionSet
        -> NormalForm.selectionSetDirectiveFree selectionSet
        -> executableFieldSelections
              (selectionSet.map (executableFieldOfSelection parentType))
            = selectionSet
  | [], _hall, _hfree => by
      simp [executableFieldSelections]
  | selection :: rest, hall, hfree => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have hrestFree : NormalForm.selectionSetDirectiveFree rest := by
        simpa [NormalForm.selectionSetDirectiveFree] using hfree.2
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          have hdirectives : directives = [] := by
            simpa [NormalForm.selectionSetDirectiveFree,
              NormalForm.selectionDirectiveFree] using hfree.1.1
          subst directives
          have hrestEq :
              List.map
                  (executableFieldSelection ∘
                    executableFieldOfSelection parentType) rest =
                rest := by
            simpa [executableFieldSelections, List.map_map,
              Function.comp_def] using
              executableFieldSelections_map_executableFieldOfSelection
                parentType rest hrestAll hrestFree
          simp [executableFieldSelections, executableFieldSelection,
            executableFieldOfSelection, hrestEq]
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem responseNames_map_executableFieldOfSelection (parentType : Name)
    : ∀ selectionSet,
        NormalForm.selectionsAllFields selectionSet
        -> selectionSet.filterMap Selection.responseName?
            = (selectionSet.map
                (fun selection =>
                  (executableFieldOfSelection parentType selection).responseName))
  | [], _hall => by
      simp
  | selection :: rest, hall => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          simp [Selection.responseName?, executableFieldOfSelection,
            responseNames_map_executableFieldOfSelection parentType rest
              hrestAll]
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem responseNamesNodup_map_executableFieldOfSelection
    (parentType : Name) (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> (selectionSet.map
            (fun selection =>
              (executableFieldOfSelection parentType selection).responseName)).Nodup := by
  intro hall hnodup
  have hnames :=
    responseNames_map_executableFieldOfSelection parentType selectionSet hall
  simpa [NormalForm.responseNamesNodup, hnames] using hnodup

theorem executableFieldsParent_map_executableFieldOfSelection
    (parentType : Name) (selectionSet : List Selection)
    : ExecutableFieldsParent parentType
        (selectionSet.map (executableFieldOfSelection parentType)) := by
  intro field hfield
  rcases List.mem_map.mp hfield with ⟨selection, _hselection, hfieldEq⟩
  subst field
  cases selection <;> rfl

theorem collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> ∀ {responseName : Name} {field : ExecutableField}
            {fieldsTail prefixTail : List ExecutableField},
          (responseName, field :: fieldsTail)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fieldsTail)
          -> fieldsTail = [] ∧ prefixTail = [] := by
  intro hall hfree hnodup responseName field fieldsTail prefixTail hgroup
    hprefix
  let fields := selectionSet.map (executableFieldOfSelection parentType)
  have hselectionSet :
      executableFieldSelections fields = selectionSet := by
    exact executableFieldSelections_map_executableFieldOfSelection parentType
      selectionSet hall hfree
  have hfieldsNodup :
      (fields.map (fun field => field.responseName)).Nodup := by
    simpa [fields, List.map_map, Function.comp_def] using
      responseNamesNodup_map_executableFieldOfSelection parentType
        selectionSet hall hnodup
  have hparents : ExecutableFieldsParent parentType fields := by
    simpa [fields] using
      executableFieldsParent_map_executableFieldOfSelection parentType
        selectionSet
  have hgroup' :
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields) := by
    simpa [hselectionSet] using hgroup
  rcases
      collectFields_executableFieldSelections_prefix_empty schema
        variableValues parentType source hfieldsNodup hparents hgroup'
        hprefix with
    ⟨_hfield, hfieldsTail, hprefixTail⟩
  exact ⟨hfieldsTail, hprefixTail⟩

theorem collectFields_allFields_directiveFree_responseNamesNodup_field_mem_prefix_empty
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> ∀ {responseName : Name} {field : ExecutableField}
            {fieldsTail prefixTail : List ExecutableField},
          (responseName, field :: fieldsTail)
            ∈ GraphQL.Execution.collectFields schema variableValues parentType source
                selectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fieldsTail)
          -> field ∈ selectionSet.map (executableFieldOfSelection parentType)
              ∧ fieldsTail = []
              ∧ prefixTail = [] := by
  intro hall hfree hnodup responseName field fieldsTail prefixTail hgroup
    hprefix
  let fields := selectionSet.map (executableFieldOfSelection parentType)
  have hselectionSet :
      executableFieldSelections fields = selectionSet := by
    exact executableFieldSelections_map_executableFieldOfSelection parentType
      selectionSet hall hfree
  have hfieldsNodup :
      (fields.map (fun field => field.responseName)).Nodup := by
    simpa [fields, List.map_map, Function.comp_def] using
      responseNamesNodup_map_executableFieldOfSelection parentType
        selectionSet hall hnodup
  have hparents : ExecutableFieldsParent parentType fields := by
    simpa [fields] using
      executableFieldsParent_map_executableFieldOfSelection parentType
        selectionSet
  have hgroup' :
      (responseName, field :: fieldsTail) ∈
        GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections fields) := by
    simpa [hselectionSet] using hgroup
  rcases
      collectFields_executableFieldSelections_prefix_empty schema
        variableValues parentType source hfieldsNodup hparents hgroup'
        hprefix with
    ⟨hfield, hfieldsTail, hprefixTail⟩
  exact ⟨by simpa [fields] using hfield, hfieldsTail, hprefixTail⟩

theorem fieldMerge_collectFields_parent_of_allFields (schema : Schema) (parentType : Name)
    : ∀ selectionSet scopedField,
        NormalForm.selectionsAllFields selectionSet
        -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
        -> scopedField.parentType = parentType
  | [], scopedField, _hall, hmem => by
      simp [FieldMerge.collectFields] at hmem
  | selection :: rest, scopedField, hall, hmem => by
      have hselectionField : Selection.isField selection :=
        hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          cases hlookup : schema.lookupField parentType fieldName with
          | none =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              exact
                fieldMerge_collectFields_parent_of_allFields schema
                  parentType rest scopedField hrestAll hmem
          | some fieldDefinition =>
              simp [FieldMerge.collectFields, hlookup] at hmem
              rcases hmem with hhead | htail
              · subst scopedField
                rfl
              · exact
                  fieldMerge_collectFields_parent_of_allFields schema
                    parentType rest scopedField hrestAll htail
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hselectionField

theorem selectionSetResponseNameFree_of_allFields_responseNamesNodup
    (schema : Schema) (parentType responseName : Name)
    : ∀ selectionSet,
        NormalForm.selectionsAllFields selectionSet
        -> responseName ∉ selectionSet.filterMap Selection.responseName?
        -> NormalForm.selectionSetResponseNameFree schema parentType
            responseName selectionSet
  | [], _hall, _hnotMem => by
      exact NormalForm.selectionSetResponseNameFree_nil schema parentType
        responseName
  | selection :: rest, hall, hnotMem => by
      have hheadField : Selection.isField selection := hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have hrestNotMem :
          responseName ∉ rest.filterMap Selection.responseName? := by
        intro hmem
        exact hnotMem (by
          cases selection <;> simp [Selection.responseName?, hmem])
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hfieldNe : fieldResponseName ≠ responseName := by
            intro heq
            exact hnotMem (by simp [Selection.responseName?, heq])
          apply NormalForm.selectionSetResponseNameFree_cons
          · simpa [NormalForm.selectionResponseNameFree] using hfieldNe
          · exact
              selectionSetResponseNameFree_of_allFields_responseNamesNodup
                schema parentType responseName rest hrestAll hrestNotMem
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem collectFields_responseName_not_mem_of_allFields_responseNameFree
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name)
    : ∀ selectionSet,
        NormalForm.selectionsAllFields selectionSet
        -> NormalForm.selectionSetResponseNameFree schema parentType responseName
            selectionSet
        -> responseName
            ∉ (GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet).map
                Prod.fst
  | [], _hall, _hfree => by
      simp [GraphQL.Execution.collectFields]
  | selection :: rest, hall, hfree => by
      have hheadField : Selection.isField selection := hall selection (by simp)
      have hrestAll : NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      have hrestFree :
          NormalForm.selectionSetResponseNameFree schema parentType
            responseName rest :=
        NormalForm.selectionSetResponseNameFree_tail hfree
      have htailNotMem :
          responseName ∉
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rest).map Prod.fst :=
        collectFields_responseName_not_mem_of_allFields_responseNameFree
          schema variableValues parentType source responseName rest hrestAll
          hrestFree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hheadFree := NormalForm.selectionSetResponseNameFree_head hfree
          have hfieldNe : fieldResponseName ≠ responseName := by
            simpa [NormalForm.selectionResponseNameFree] using hheadFree
          by_cases hallows :
              selectionDirectivesAllowBool variableValues directives = true
          · intro hmem
            have hparts :
                responseName = fieldResponseName ∨
                responseName ∈
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest).map Prod.fst := by
              have hmemMerge :
                  responseName ∈
                    (GraphQL.Execution.mergeExecutableGroups
                      (GraphQL.Execution.collectSelection schema
                        variableValues parentType source
                        (.field fieldResponseName fieldName arguments
                          directives selectionSet))
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source rest)).map Prod.fst := by
                simpa [GraphQL.Execution.collectFields] using hmem
              have hpartsRaw :=
                (mergeExecutableGroups_key_mem
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType source
                    (.field fieldResponseName fieldName arguments directives
                      selectionSet))
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest)
                  responseName).mp hmemMerge
              rcases hpartsRaw with hhead | htail
              · left
                simpa [GraphQL.Execution.collectSelection, hallows] using hhead
              · exact Or.inr htail
            rcases hparts with hhead | htail
            · exact hfieldNe hhead.symm
            · exact htailNotMem htail
          · have hskip :
                selectionDirectivesAllowBool variableValues directives =
                  false := by
              cases h :
                  selectionDirectivesAllowBool variableValues directives
              · rfl
              · contradiction
            intro hmem
            have hmemMerge :
                responseName ∈
                  (GraphQL.Execution.mergeExecutableGroups
                    (GraphQL.Execution.collectSelection schema variableValues
                      parentType source
                      (.field fieldResponseName fieldName arguments
                        directives selectionSet))
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source rest)).map Prod.fst := by
              simpa [GraphQL.Execution.collectFields] using hmem
            have hpartsRaw :=
              (mergeExecutableGroups_key_mem
                (GraphQL.Execution.collectSelection schema variableValues
                  parentType source
                  (.field fieldResponseName fieldName arguments directives
                    selectionSet))
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest)
                responseName).mp hmemMerge
            rcases hpartsRaw with hhead | htail
            · simp [GraphQL.Execution.collectSelection, hskip] at hhead
            · exact htailNotMem htail
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

theorem scopedField_outputType_eq_fieldReturnType_of_identity_match
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selectionSet : List Selection)
    (scopedField : FieldMerge.ScopedField)
    (field : ExecutableField)
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
      -> field.parentType = scopedField.parentType
      -> ScopedFieldMatchesExecutableIdentity scopedField field
      -> scopedField.outputType.namedType
          = ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName) := by
  intro hvalid hscopedMem hparent hmatch
  rcases hmatch with
    ⟨_hresponseName, hfieldName, _harguments, _hselectionSet⟩
  rcases
      GraphQL.NormalForm.collectFields_scoped_mem_fieldSelectionSetValid
        schema variableDefinitions parentType selectionSet scopedField hvalid
        hscopedMem with
    ⟨fieldDefinition, hlookup, houtput, _hfieldSelectionSet⟩
  have hreturn :
      ((schema.fieldReturnType? field.parentType field.fieldName).getD
        field.fieldName) = fieldDefinition.outputType.namedType := by
    simp [Schema.fieldReturnType?, hparent, ← hfieldName, hlookup]
  rw [hreturn]
  exact (congrArg TypeRef.namedType houtput).symm

theorem of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> FreshPrefixSelectionDerivation schema variableValues parentType source
          selectionSet := by
  intro hall hfree hnodup
  let fields := selectionSet.map (executableFieldOfSelection parentType)
  have hselectionSet :
      executableFieldSelections fields = selectionSet := by
    exact executableFieldSelections_map_executableFieldOfSelection parentType
      selectionSet hall hfree
  have hfieldsNodup :
      (fields.map (fun field => field.responseName)).Nodup := by
    simpa [fields, List.map_map, Function.comp_def] using
      responseNamesNodup_map_executableFieldOfSelection parentType selectionSet
        hall hnodup
  have hparents : ExecutableFieldsParent parentType fields := by
    simpa [fields] using
      executableFieldsParent_map_executableFieldOfSelection parentType
        selectionSet
  have hderivation :
      FreshPrefixSelectionDerivation schema variableValues parentType source
        (executableFieldSelections fields) :=
    of_executableFieldSelections_responseNamesNodup schema variableValues
      parentType source fields hfieldsNodup hparents
  rwa [hselectionSet] at hderivation

theorem
    selectionSetCollectFieldsHeadDisjointTree_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type} (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
        source (executableFieldSelections fields) := by
  have htree :
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source (executableFieldSelections fields)
        ∧ ∀ selection, selection ∈ executableFieldSelections fields ->
            SelectionCollectFieldsHeadDisjointTree schema variableValues
              parentType source selection := by
    constructor
    · induction fields with
      | nil =>
          simp [executableFieldSelections, SelectionSetCollectFieldsHeadDisjoint]
      | cons field rest ih =>
          simp [executableFieldSelections, SelectionSetCollectFieldsHeadDisjoint]
          constructor
          · intro responseName hleft hright
            have hheadParent : field.parentType = parentType :=
              hparents field (by simp)
            have hrestParents : ExecutableFieldsParent parentType rest := by
              intro restField hrestField
              exact hparents restField (by simp [hrestField])
            have hrestNodup :
                (rest.map (fun field => field.responseName)).Nodup := by
              simpa using (List.nodup_cons.mp hnodup).2
            have hheadCollect :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source (executableFieldSelections [field]) =
                  singletonExecutableGroups [field] :=
              collectFields_executableFieldSelections_singletonExecutableGroups
                schema variableValues parentType source [field]
                (by simp)
                (ExecutableFieldsParent_singleton parentType field hheadParent)
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source (executableFieldSelections rest) =
                  singletonExecutableGroups rest :=
              collectFields_executableFieldSelections_singletonExecutableGroups
                schema variableValues parentType source rest hrestNodup
                hrestParents
            have hheadCollect' :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source [executableFieldSelection field] =
                  singletonExecutableGroups [field] := by
              simpa [executableFieldSelections] using hheadCollect
            have hrestCollect' :
                GraphQL.Execution.collectFields schema variableValues parentType
                    source (List.map executableFieldSelection rest) =
                  singletonExecutableGroups rest := by
              simpa [executableFieldSelections] using hrestCollect
            rw [hheadCollect'] at hleft
            rw [hrestCollect'] at hright
            have hleftEq : responseName = field.responseName := by
              simpa [singletonExecutableGroups] using hleft
            have hrightMem :
                responseName ∈ rest.map (fun field => field.responseName) := by
              simpa [singletonExecutableGroups_map_fst] using hright
            exact (List.nodup_cons.mp hnodup).1 (by
              simpa [hleftEq] using hrightMem)
          · exact ih (by simpa using (List.nodup_cons.mp hnodup).2)
              (by
                intro restField hrestField
                exact hparents restField (by simp [hrestField]))
    · intro selection hselection
      rcases List.mem_map.mp hselection with ⟨field, _hfield, hselectionEq⟩
      cases hselectionEq
      simp [executableFieldSelection, SelectionCollectFieldsHeadDisjointTree]
  simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree

end FreshPrefixSelectionDerivation

theorem collectFields_executableFieldSelections_single_prefix_duplicate_fresh_middle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List ExecutableField)
    (hsameResponse : later.responseName = first.responseName)
    (hmiddleNodup : (middle.map (fun field => field.responseName)).Nodup)
    (hmiddleParents : ∀ field, field ∈ middle -> field.parentType = parentType)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    : GraphQL.Execution.collectFields schema variableValues parentType source
        (executableFieldSelections ([first] ++ (middle ++ [later])))
      = GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ([first] ++ [later] ++ middle)) := by
  have hnotMiddleCollect :
      first.responseName ∉
        (GraphQL.Execution.collectFields schema variableValues parentType
          source (executableFieldSelections middle)).map Prod.fst := by
    intro hmem
    have hfieldMem :
        first.responseName ∈ middle.map (fun field => field.responseName) :=
      (FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_key_mem
        schema variableValues parentType source middle first.responseName).mp
        hmem
    exact hnotMiddle (by simpa [hsameResponse] using hfieldMem)
  have hmiddleCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections middle) =
        FreshPrefixSelectionDerivation.singletonExecutableGroups middle :=
    FreshPrefixSelectionDerivation.collectFields_executableFieldSelections_singletonExecutableGroups
      schema variableValues parentType source middle hmiddleNodup hmiddleParents
  have hdup :=
    collectFields_duplicate_field_middle_append_eq_collected_middle schema
      variableValues parentType source first later
      (executableFieldSelections middle) [] hsameResponse hnotMiddleCollect
  rw [hmiddleCollect] at hdup
  simpa [executableFieldSelections, List.append_assoc,
    FreshPrefixSelectionDerivation.collectedExecutableFields_singletonExecutableGroups]
    using hdup

namespace FreshPrefixSelectionPlan

theorem freshFlat
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity} {selectionSet}
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source selectionSet
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source selectionSet := by
  intro plan
  induction plan with
  | nil =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_nil schema resolvers
        variableValues (completionDepth + 1) parentType source
  | appendDisjoint left right hleft hright hdisjoint ihleft ihright =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint
        schema resolvers variableValues (completionDepth + 1) parentType source
        left right hdisjoint ihleft ihright
  | sameGroup responseName fields hresponse hparent =>
      exact
        VisitSubfieldsFlatCollectsFreshPrefixes_executableFieldSelections_same_group
          schema resolvers variableValues (completionDepth + 1) parentType
          source responseName fields hresponse hparent
  | duplicateFieldBlockNormalize first later middle suffix hsameResponse
      hlaterLookup hnotMiddle hmiddle hnormalized ihmiddle ihnormalized =>
      exact
        VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_normalized
          schema resolvers variableValues completionDepth parentType source
          first later middle suffix hsameResponse hlaterLookup hnotMiddle
          ihmiddle ihnormalized
  | consDisjoint selection rest hselection hrest hdisjoint ihrest =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_cons_of_namesDisjoint schema
        resolvers variableValues (completionDepth + 1) parentType source
        selection rest hdisjoint hselection ihrest
  | duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
      hnotMiddle hdisjoint hmiddle hsuffix ihmiddle ihsuffix =>
      exact VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
        schema resolvers variableValues completionDepth parentType source first
        later middle suffix hsameResponse hlaterLookup hnotMiddle hdisjoint
        ihmiddle ihsuffix

theorem single_of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selection : Selection)
    (htree
      : SelectionCollectFieldsHeadDisjointTree schema variableValues parentType
          source selection)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source [selection] :=
  .consDisjoint selection []
    (VisitSubfieldsFlatCollectsFreshPrefixes_single_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source
      selection htree)
    .nil
    (by
      intro responseName _hleft hright
      simp [GraphQL.Execution.collectFields] at hright)

theorem of_headDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ selectionSet,
        SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source selectionSet
        -> (∀ selection,
              selection ∈ selectionSet
              -> FreshPrefixSelectionPlan schema resolvers variableValues
                  completionDepth parentType source [selection])
        -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
            parentType source selectionSet
  | [], _hdisjoint, _hsingle => .nil
  | selection :: rest, hdisjoint, hsingle => by
      rcases hdisjoint with ⟨hheadDisjoint, hrestDisjoint⟩
      exact .consDisjoint selection rest
        (freshFlat (hsingle selection (by simp)))
        (of_headDisjoint schema resolvers variableValues completionDepth
          parentType source rest hrestDisjoint
          (by
            intro candidate hcandidate
            exact hsingle candidate (by simp [hcandidate])))
        hheadDisjoint

theorem of_headDisjointTree
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (htree
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source selectionSet)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source selectionSet := by
  have htree' :
      SelectionSetCollectFieldsHeadDisjoint schema variableValues parentType
          source selectionSet
        ∧ ∀ selection, selection ∈ selectionSet ->
            SelectionCollectFieldsHeadDisjointTree schema variableValues
              parentType source selection := by
    simpa [SelectionSetCollectFieldsHeadDisjointTree] using htree
  rcases htree' with ⟨hdisjoint, hchildren⟩
  exact of_headDisjoint schema resolvers variableValues completionDepth
    parentType source selectionSet hdisjoint
    (by
      intro selection hselection
      exact single_of_headDisjointTree schema resolvers variableValues
        completionDepth parentType source selection
        (hchildren selection hselection))

theorem duplicateFieldBlock_of_headDisjointTrees
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later]))
          (GraphQL.Execution.collectFields schema variableValues parentType source
            suffix))
    (hmiddle
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
          source middle)
    (hsuffix
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
          source suffix)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]
          ++ suffix) :=
  .duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
    hnotMiddle hdisjoint
    (of_headDisjointTree schema resolvers variableValues completionDepth
      parentType source middle hmiddle)
    (of_headDisjointTree schema resolvers variableValues completionDepth
      parentType source suffix hsuffix)

theorem duplicateFieldPair_of_headDisjointMiddle
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
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
          source middle)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]) := by
  simpa using
    duplicateFieldBlock_of_headDisjointTrees schema resolvers variableValues
      completionDepth parentType source first later middle [] hsameResponse
      hlaterLookup hnotMiddle
      (by
        intro responseName _hleft hright
        simp [GraphQL.Execution.collectFields] at hright)
      hmiddle
      (by
        simp [SelectionSetCollectFieldsHeadDisjointTree,
          SelectionSetCollectFieldsHeadDisjoint])

theorem of_collectedGroups
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        PairKeysNodup groups
        -> CollectedGroupsFieldsNonempty groups
        -> CollectedGroupsResponseName groups
        -> CollectedGroupsParent parentType groups
        -> FreshPrefixSelectionPlan schema resolvers variableValues
            completionDepth parentType source
            (executableFieldSelections (collectedExecutableFields groups))
  | [], _hnodup, _hnonempty, _hresponses, _hparents => by
      simpa [collectedExecutableFields, executableFieldSelections] using
        (FreshPrefixSelectionPlan.nil
          (schema := schema) (resolvers := resolvers)
          (variableValues := variableValues)
          (completionDepth := completionDepth)
          (parentType := parentType) (source := source))
  | (responseName, fields) :: rest, hnodup, hnonempty, hresponses, hparents =>
      by
        have hrestNodup : PairKeysNodup rest :=
          PairKeysNodup.tail hnodup
        have hrestNonempty : CollectedGroupsFieldsNonempty rest :=
          CollectedGroupsFieldsNonempty_tail hnonempty
        have hrestResponses : CollectedGroupsResponseName rest :=
          CollectedGroupsResponseName_tail hresponses
        have hrestParents : CollectedGroupsParent parentType rest :=
          CollectedGroupsParent_tail hparents
        have hfieldsNonempty : fields ≠ [] :=
          hnonempty responseName fields (by simp)
        cases fields with
        | nil =>
            exact False.elim (hfieldsNonempty rfl)
        | cons field fieldsTail =>
            have hheadResponse :
                ExecutableFieldsResponseName responseName
                  (field :: fieldsTail) :=
              hresponses responseName (field :: fieldsTail) (by simp)
            have hheadParent :
                ExecutableFieldsParent parentType (field :: fieldsTail) :=
              hparents responseName (field :: fieldsTail) (by simp)
            have hheadCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections (field :: fieldsTail)) =
                [(responseName, field :: fieldsTail)] :=
              collectFields_executableFieldSelections_same_group schema
                variableValues parentType source responseName
                (field :: fieldsTail) hheadResponse hheadParent
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) =
                rest :=
              collectFields_executableFieldSelections_collectedExecutableFields
                schema variableValues parentType source rest hrestNodup
                hrestNonempty hrestResponses hrestParents
            have hdisjoint :
                GraphQL.NormalForm.executableGroupNamesDisjoint
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections (field :: fieldsTail)))
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source
                    (executableFieldSelections
                      (collectedExecutableFields rest))) := by
              intro candidate hleft hright
              rw [hheadCollect] at hleft
              rw [hrestCollect] at hright
              exact
                executableGroupNamesDisjoint_singleton_tail_of_pairKeysNodup
                  hnodup candidate hleft hright
            have hhead :
                FreshPrefixSelectionPlan schema resolvers variableValues
                  completionDepth parentType source
                  (executableFieldSelections (field :: fieldsTail)) :=
              .sameGroup responseName (field :: fieldsTail) hheadResponse
                hheadParent
            have htail :
                FreshPrefixSelectionPlan schema resolvers variableValues
                  completionDepth parentType source
                  (executableFieldSelections
                    (collectedExecutableFields rest)) :=
              of_collectedGroups schema resolvers variableValues completionDepth
                parentType source rest hrestNodup hrestNonempty
                hrestResponses hrestParents
            simpa [collectedExecutableFields, executableFieldSelections] using
              FreshPrefixSelectionPlan.appendDisjoint
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth)
                (parentType := parentType) (source := source)
                (executableFieldSelections (field :: fieldsTail))
                (executableFieldSelections (collectedExecutableFields rest))
                hhead htail hdisjoint

theorem of_collectedCollectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) :=
  of_collectedGroups schema resolvers variableValues completionDepth parentType
    source
    (GraphQL.Execution.collectFields schema variableValues parentType source selectionSet)
    (PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet))
    (collectFields_fieldsNonempty schema variableValues parentType source selectionSet)
    (collectFields_responseName schema variableValues parentType source selectionSet)
    (collectFields_parent schema variableValues parentType source selectionSet)

theorem duplicateFieldBlockNormalizePlan_of_headDisjointSuffix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hparents : ExecutableFieldsParent parentType [first, later])
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later]))
          (GraphQL.Execution.collectFields schema variableValues parentType source
            suffix))
    (hsuffix
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues parentType
          source suffix)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source
        ((executableFieldSelections [first, later]
            ++ executableFieldSelections
                (collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    source middle)))
          ++ suffix) := by
  let collectedMiddle :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle))
  let normalizedBlock := executableFieldSelections [first, later] ++
    collectedMiddle
  have hpairResponses :
      ExecutableFieldsResponseName first.responseName [first, later] := by
    intro field hfield
    simp at hfield
    rcases hfield with hfield | hfield
    · subst field
      rfl
    · subst field
      exact hsameResponse
  have hpairCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first, later]) =
        [(first.responseName, [first, later])] :=
    collectFields_executableFieldSelections_same_group schema variableValues
      parentType source first.responseName [first, later] hpairResponses
      hparents
  have hmiddleCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle =
        GraphQL.Execution.collectFields schema variableValues parentType source
          middle := by
    dsimp [collectedMiddle]
    exact
      collectFields_executableFieldSelections_collectedExecutableFields schema
        variableValues parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (PairKeysNodup_of_executableGroupNamesNodup
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)
          (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
            parentType source middle))
        (collectFields_fieldsNonempty schema variableValues parentType source
          middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        (collectFields_parent schema variableValues parentType source middle)
  have hpairMiddleDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first, later]))
        (GraphQL.Execution.collectFields schema variableValues parentType source
          collectedMiddle) := by
    intro responseName hleft hright
    rw [hpairCollect] at hleft
    rw [hmiddleCollect] at hright
    simp at hleft
    exact hnotMiddle (by simpa [hleft] using hright)
  have hnormalizedBlockPlan :
      FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source normalizedBlock :=
    FreshPrefixSelectionPlan.appendDisjoint
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues)
      (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      (executableFieldSelections [first, later])
      collectedMiddle
      (.sameGroup first.responseName [first, later] hpairResponses hparents)
      (of_collectedCollectFields schema resolvers variableValues
        completionDepth parentType source middle)
      hpairMiddleDisjoint
  have hblockCollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections [first] ++ middle ++
            executableFieldSelections [later]) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    have hcollect :=
      collectFields_duplicate_field_middle_append_eq_collected_middle schema
        variableValues parentType source first later middle [] hsameResponse
        hnotMiddle
    simpa [normalizedBlock, collectedMiddle] using hcollect
  have hblockSuffixDisjoint :
      GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          suffix) := by
    intro responseName hleft hright
    exact hdisjoint responseName (by rwa [hblockCollect]) hright
  exact
    FreshPrefixSelectionPlan.appendDisjoint
      (schema := schema) (resolvers := resolvers)
      (variableValues := variableValues)
      (completionDepth := completionDepth)
      (parentType := parentType) (source := source)
      normalizedBlock suffix hnormalizedBlockPlan
      (of_headDisjointTree schema resolvers variableValues completionDepth
        parentType source suffix hsuffix)
      hblockSuffixDisjoint

theorem of_derivation
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    : ∀ {selectionSet},
        FreshPrefixSelectionDerivation schema variableValues parentType source
          selectionSet
        -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
            parentType source selectionSet
  | _, FreshPrefixSelectionDerivation.nil => .nil
  | _, FreshPrefixSelectionDerivation.appendDisjoint left right hleft hright
        hdisjoint =>
      .appendDisjoint left right
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hleft)
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hright)
        hdisjoint
  | _, FreshPrefixSelectionDerivation.sameGroup responseName fields hresponse
        hparent =>
      .sameGroup responseName fields hresponse hparent
  | _, FreshPrefixSelectionDerivation.inlineFragmentNone directives
        selectionSet hselectionSet =>
      .consDisjoint (.inlineFragment none directives selectionSet) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_none_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          directives selectionSet
          (by
            intro hallowed
            exact freshFlat
              (of_derivation schema resolvers variableValues completionDepth
                parentType source (hselectionSet hallowed))))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)
  | _, FreshPrefixSelectionDerivation.inlineFragmentSome typeCondition
        directives selectionSet hselectionSet =>
      .consDisjoint
        (.inlineFragment (some typeCondition) directives selectionSet) []
        (VisitSubfieldsFlatCollectsFreshPrefixes_inline_some_single schema
          resolvers variableValues (completionDepth + 1) parentType source
          typeCondition directives selectionSet
          (by
            intro hallowed happly
            exact freshFlat
              (of_derivation schema resolvers variableValues completionDepth
                parentType source (hselectionSet hallowed happly))))
        .nil
        (by
          intro responseName _hleft hright
          simp [GraphQL.Execution.collectFields] at hright)
  | _, FreshPrefixSelectionDerivation.duplicateFieldBlockNormalize first later
        middle suffix hsameResponse hlaterLookup hnotMiddle hmiddle hnormalized =>
      .duplicateFieldBlockNormalize first later middle suffix hsameResponse
        hlaterLookup hnotMiddle
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hmiddle)
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hnormalized)
  | _, FreshPrefixSelectionDerivation.consHeadDisjoint selection rest hselection
        hrest hdisjoint =>
      .consDisjoint selection rest
        (freshFlat
          (single_of_headDisjointTree schema resolvers variableValues
            completionDepth parentType source selection hselection))
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hrest)
        hdisjoint
  | _, FreshPrefixSelectionDerivation.duplicateFieldBlock first later middle
        suffix hsameResponse hlaterLookup hnotMiddle hdisjoint hmiddle hsuffix =>
      .duplicateFieldBlock first later middle suffix hsameResponse hlaterLookup
        hnotMiddle hdisjoint
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hmiddle)
        (of_derivation schema resolvers variableValues completionDepth
          parentType source hsuffix)

theorem of_executableFieldSelections_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    (hnodup : (fields.map (fun field => field.responseName)).Nodup)
    (hparents : ExecutableFieldsParent parentType fields)
    : FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
        parentType source (executableFieldSelections fields) :=
  of_derivation schema resolvers variableValues completionDepth parentType source
    (FreshPrefixSelectionDerivation.of_executableFieldSelections_responseNamesNodup
      schema variableValues parentType source fields hnodup hparents)

theorem of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source selectionSet :=
  fun hall hfree hnodup =>
    of_derivation schema resolvers variableValues completionDepth parentType
      source
      (FreshPrefixSelectionDerivation.of_allFields_directiveFree_responseNamesNodup
        schema variableValues parentType source selectionSet hall hfree hnodup)

theorem of_normalizeSelectionSet
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionSetDirectiveFree selectionSet
      -> FreshPrefixSelectionPlan schema resolvers variableValues completionDepth
          parentType source
          (NormalForm.normalizeSelectionSet schema parentType selectionSet) := by
  intro hfree
  exact
    of_allFields_directiveFree_responseNamesNodup schema resolvers
      variableValues completionDepth parentType source
      (NormalForm.normalizeSelectionSet schema parentType selectionSet)
      (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
        schema parentType selectionSet)
      (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
        schema parentType selectionSet hfree)
      (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
        schema parentType selectionSet)

end FreshPrefixSelectionPlan

theorem
    VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_responseNamesNodup
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.responseNamesNodup selectionSet
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source selectionSet :=
  fun hall hfree hnodup =>
    (FreshPrefixSelectionPlan.of_allFields_directiveFree_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source
      selectionSet hall hfree hnodup).freshFlat

theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_normal
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.selectionSetNormal schema parentType selectionSet
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source selectionSet := by
  intro hall hfree hnormal
  have hnodup : NormalForm.responseNamesNodup selectionSet := by
    have hnonRedundant : NormalForm.selectionSetNonRedundant selectionSet :=
      hnormal.2
    unfold NormalForm.selectionSetNonRedundant at hnonRedundant
    exact hnonRedundant.1
  exact
    VisitSubfieldsFlatCollectsFreshPrefixes_of_allFields_directiveFree_responseNamesNodup
      schema resolvers variableValues completionDepth parentType source
      selectionSet hall hfree hnodup
end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
