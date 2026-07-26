import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ResponseKeys
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SyntaxDiff

/-!
Field-collection key facts for uniqueness semantic separation.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

namespace ExecutionKeys

variable {ObjectRef : Type}

theorem mem_map_fst_addExecutableGroup_iff
    (name : Name) (group : Name × List (Execution.ExecutableField))
    : ∀ groups : List (Name × List (Execution.ExecutableField)),
        (name ∈ (Execution.addExecutableGroup group groups).map Prod.fst
          ↔ name = group.1 ∨ name ∈ groups.map Prod.fst)
  | [] => by
      simp [Execution.addExecutableGroup]
  | candidate :: rest => by
      by_cases hsame : (candidate.1 == group.1) = true
      · have hcandidateGroup : candidate.1 = group.1 :=
          beq_iff_eq.mp hsame
        simp [Execution.addExecutableGroup, hcandidateGroup]
      · simp [Execution.addExecutableGroup, hsame,
          mem_map_fst_addExecutableGroup_iff name group rest]
        constructor
        · intro h
          rcases h with hcandidate | hgroup | hrest
          · exact Or.inr (Or.inl hcandidate)
          · exact Or.inl hgroup
          · exact Or.inr (Or.inr hrest)
        · intro h
          rcases h with hgroup | hcandidate | hrest
          · exact Or.inr (Or.inl hgroup)
          · exact Or.inl hcandidate
          · exact Or.inr (Or.inr hrest)

theorem mem_map_fst_mergeExecutableGroups_iff (name : Name)
    : ∀ left right : List (Name × List (Execution.ExecutableField)),
        (name ∈ (Execution.mergeExecutableGroups left right).map Prod.fst
          ↔ name ∈ left.map Prod.fst ∨ name ∈ right.map Prod.fst)
  | left, [] => by
      simp [Execution.mergeExecutableGroups]
  | left, group :: rest => by
      change
        name ∈
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup group left) rest).map Prod.fst
          ↔ name ∈ left.map Prod.fst
            ∨ name ∈ (group :: rest).map Prod.fst
      have hrec :
          name ∈
              (Execution.mergeExecutableGroups
                (Execution.addExecutableGroup group left) rest).map Prod.fst
            ↔ name ∈
                (Execution.addExecutableGroup group left).map Prod.fst
              ∨ name ∈ rest.map Prod.fst :=
        mem_map_fst_mergeExecutableGroups_iff name
          (Execution.addExecutableGroup group left) rest
      have hadd :
          name ∈ (Execution.addExecutableGroup group left).map Prod.fst
            ↔ name = group.1 ∨ name ∈ left.map Prod.fst :=
        mem_map_fst_addExecutableGroup_iff name group left
      constructor
      · intro h
        rcases hrec.mp h with haddMem | hrest
        · rcases hadd.mp haddMem with hgroup | hleft
          · exact Or.inr (by simp [hgroup])
          · exact Or.inl hleft
        · exact Or.inr (by simp [hrest])
      · intro h
        rcases h with hleft | hgroupRest
        · exact hrec.mpr (Or.inl (hadd.mpr (Or.inr hleft)))
        · have hgroupOrRest :
              name = group.1 ∨ name ∈ rest.map Prod.fst := by
            simpa using hgroupRest
          rcases hgroupOrRest with hgroup | hrest
          · exact hrec.mpr (Or.inl (hadd.mpr (Or.inl hgroup)))
          · exact hrec.mpr (Or.inr hrest)

theorem selectionDirectivesAllowBool_nil (variableValues : Execution.VariableValues)
    : Execution.selectionDirectivesAllowBool variableValues [] = true := by
  rfl

theorem collectFields_allFields_directiveFree_key_mem_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (name : Name)
    : ∀ selectionSet : List Selection,
        selectionsAllFields selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> (name
              ∈ (Execution.collectFields schema variableValues parentType source
                  selectionSet).map
                  Prod.fst
            ↔ name ∈ selectionSet.filterMap Selection.responseName?)
  | [], _hallFields, _hfree => by
      simp [Execution.collectFields]
  | selection :: rest, hallFields, hfree => by
      have htailAll : selectionsAllFields rest :=
        selectionsAllFields_tail hallFields
      have htailFree : selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have htail :
          name ∈
              (Execution.collectFields schema variableValues parentType source
                rest).map Prod.fst
            ↔ name ∈ rest.filterMap Selection.responseName? :=
        collectFields_allFields_directiveFree_key_mem_iff schema variableValues
          parentType source name rest htailAll htailFree
      have hselectionField : Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hheadFree : directives = [] := by
            have hselectionFree : selectionDirectiveFree
                (Selection.field responseName fieldName arguments directives
                  childSelectionSet) :=
              selectionSetDirectiveFree_head hfree
            simpa [selectionDirectiveFree] using hselectionFree.1
          subst directives
          simp [Execution.collectFields, Execution.collectSelection,
            selectionDirectivesAllowBool_nil,
            mem_map_fst_mergeExecutableGroups_iff, htail,
            Selection.responseName?]
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField

theorem collectFields_normal_object_key_mem_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (name : Name) {selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> (name
            ∈ (Execution.collectFields schema variableValues parentType source
                selectionSet).map
                Prod.fst
          ↔ name ∈ selectionSet.filterMap Selection.responseName?) := by
  intro hobject hnormal hfree
  exact collectFields_allFields_directiveFree_key_mem_iff schema
    variableValues parentType source name selectionSet
    (selectionSetNormal_allFields_of_object hnormal hobject) hfree

theorem collectFields_normal_object_field_head
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (childSelectionSet rest : List Selection)
    : selectionSetDirectiveFree
        (Selection.field responseName fieldName arguments [] childSelectionSet :: rest)
      -> selectionSetNormal schema parentType
          (Selection.field responseName fieldName arguments [] childSelectionSet :: rest)
      -> objectTypeNameBool schema parentType = true
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments [] childSelectionSet
              :: rest)
          = (
              responseName,
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }]
            )
            :: Execution.collectFields schema variableValues parentType source rest := by
  intro hfree hnormal hobject
  have hrestFree : selectionSetDirectiveFree rest :=
    selectionSetDirectiveFree_tail hfree
  have hrestNormal : selectionSetNormal schema parentType rest :=
    selectionSetNormal_tail hnormal
  have hnames :
      (responseName :: rest.filterMap Selection.responseName?).Nodup := by
    simpa [responseNamesNodup, Selection.responseName?] using
      selectionSetNormal_responseNamesNodup hnormal
  have hnotRest : responseName ∉ rest.filterMap Selection.responseName? :=
    (List.nodup_cons.mp hnames).1
  have hnotCollect :
      responseName ∉
        (Execution.collectFields schema variableValues parentType source
          rest).map Prod.fst := by
    intro hcollect
    exact hnotRest
      ((collectFields_normal_object_key_mem_iff schema variableValues
        parentType source responseName hobject hrestNormal hrestFree).mp
        hcollect)
  exact
    collectFields_field_noDirectives_cons_of_responseName_not_mem schema
      variableValues parentType source responseName fieldName arguments
      childSelectionSet rest hnotCollect

theorem collectFields_normal_object_keys_eq_responseNames
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    : ∀ selectionSet : List Selection,
        selectionSetDirectiveFree selectionSet
        -> selectionSetNormal schema parentType selectionSet
        -> objectTypeNameBool schema parentType = true
        -> (Execution.collectFields schema variableValues parentType source
              selectionSet).map
              Prod.fst
            = selectionSet.filterMap Selection.responseName?
  | [], _hfree, _hnormal, _hobject => by
      simp [Execution.collectFields]
  | selection :: rest, hfree, hnormal, hobject => by
      have hallFields :
          selectionsAllFields (selection :: rest) :=
        selectionSetNormal_allFields_of_object hnormal hobject
      have hselectionField :
          Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hdirectives : directives = [] :=
            (selectionSetDirectiveFree_head hfree).1
          subst directives
          have hcollect :
              Execution.collectFields schema variableValues parentType source
                (Selection.field responseName fieldName arguments []
                  childSelectionSet :: rest)
              =
              (responseName, [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := childSelectionSet
              }])
                :: Execution.collectFields schema variableValues parentType
                  source rest :=
            collectFields_normal_object_field_head schema variableValues
              parentType source responseName fieldName arguments
              childSelectionSet rest hfree hnormal hobject
          have htail :
              (Execution.collectFields schema variableValues parentType
                source rest).map Prod.fst
              =
              rest.filterMap Selection.responseName? :=
            collectFields_normal_object_keys_eq_responseNames schema
              variableValues parentType source rest
              (selectionSetDirectiveFree_tail hfree)
              (selectionSetNormal_tail hnormal)
              hobject
          simp [hcollect, htail, Selection.responseName?]
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField

theorem collectFields_normal_object_keys_nodup
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> ((Execution.collectFields schema variableValues parentType source
            selectionSet).map
            Prod.fst).Nodup := by
  intro hfree hnormal hobject
  rw [collectFields_normal_object_keys_eq_responseNames schema variableValues
    parentType source selectionSet hfree hnormal hobject]
  exact selectionSetNormal_responseNamesNodup hnormal

end ExecutionKeys

end GroundTypeNormalization

end NormalForm

end GraphQL
