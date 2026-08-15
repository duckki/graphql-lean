import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Semantics.BoolCaseExecution
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection.GroupPrefix

/-!
Generated-field and field-normality lemmas for ungrouped execution.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

variable {ObjectRef : Type}

theorem responseNamesNodup_tail {selection : Selection} {selectionSet : List Selection}
    : NormalForm.responseNamesNodup (selection :: selectionSet)
      -> NormalForm.responseNamesNodup selectionSet := by
  intro hnodup
  unfold NormalForm.responseNamesNodup at hnodup ⊢
  cases selection with
  | field responseName fieldName arguments directives subselections =>
      exact hnodup.tail
  | inlineFragment typeCondition directives subselections =>
      change (selectionSet.filterMap Selection.responseName?).Nodup
      exact hnodup

theorem inlineFragmentTypeConditionsNodup_tail
    {selection : Selection} {selectionSet : List Selection}
    : NormalForm.inlineFragmentTypeConditionsNodup (selection :: selectionSet)
      -> NormalForm.inlineFragmentTypeConditionsNodup selectionSet := by
  intro hnodup
  unfold NormalForm.inlineFragmentTypeConditionsNodup at hnodup ⊢
  cases selection with
  | field responseName fieldName arguments directives subselections =>
      change (selectionSet.filterMap NormalForm.inlineFragmentTypeCondition?).Nodup
      exact hnodup
  | inlineFragment typeCondition directives subselections =>
      cases typeCondition with
      | none =>
          change (selectionSet.filterMap NormalForm.inlineFragmentTypeCondition?).Nodup
          exact hnodup
      | some typeCondition =>
          change List.Pairwise (fun x1 x2 => ¬ x1 = x2)
            (List.filterMap NormalForm.inlineFragmentTypeCondition?
              selectionSet)
          simpa [NormalForm.inlineFragmentTypeCondition?] using hnodup.tail

theorem selectionSetNonRedundant_tail
    {selection : Selection} {selectionSet : List Selection}
    : NormalForm.selectionSetNonRedundant (selection :: selectionSet)
      -> NormalForm.selectionSetNonRedundant selectionSet := by
  intro hnonRedundant
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant ⊢
  exact ⟨responseNamesNodup_tail hnonRedundant.1,
    inlineFragmentTypeConditionsNodup_tail hnonRedundant.2.1,
    fun selection hselection =>
      hnonRedundant.2.2 selection
        (List.mem_cons_of_mem _ hselection)⟩

theorem selectionSetGroundTyped_tail
    {schema : Schema} {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : NormalForm.selectionSetGroundTyped schema parentType (selection :: selectionSet)
      -> NormalForm.selectionSetGroundTyped schema parentType selectionSet := by
  intro hground
  unfold NormalForm.selectionSetGroundTyped at hground ⊢
  constructor
  · cases hobject : NormalForm.objectTypeNameBool schema parentType <;>
      simp [hobject] at hground ⊢
    all_goals
      intro candidate hcandidate
      exact hground.1 candidate (List.mem_cons_of_mem _ hcandidate)
  · intro candidate hcandidate
    exact hground.2 candidate (List.mem_cons_of_mem _ hcandidate)

theorem selectionSetNormal_tail
    {schema : Schema} {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : NormalForm.selectionSetNormal schema parentType (selection :: selectionSet)
      -> NormalForm.selectionSetNormal schema parentType selectionSet := by
  intro hnormal
  exact ⟨selectionSetGroundTyped_tail hnormal.1,
    selectionSetNonRedundant_tail hnormal.2⟩

theorem selectionSetNormal_field_child
    {schema : Schema} {parentType : Name}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet rest : List Selection}
    : NormalForm.selectionSetNormal schema parentType
        (Selection.field responseName fieldName arguments directives selectionSet :: rest)
      -> NormalForm.selectionSetNormal schema
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          selectionSet := by
  intro hnormal
  unfold NormalForm.selectionSetNormal at hnormal
  rcases hnormal with ⟨hground, hnonRedundant⟩
  unfold NormalForm.selectionSetGroundTyped at hground
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant
  have hselectionGround :
      NormalForm.selectionGroundTyped schema parentType
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    exact hground.2 _ (by simp)
  have hselectionNonRedundant :
      NormalForm.selectionNonRedundant
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    exact hnonRedundant.2.2 _ (by simp)
  unfold NormalForm.selectionGroundTyped at hselectionGround
  unfold NormalForm.selectionNonRedundant at hselectionNonRedundant
  rcases hselectionGround with ⟨returnType, hreturn, hchildGround⟩
  simpa [hreturn, NormalForm.selectionSetNormal] using
    (⟨hchildGround, hselectionNonRedundant⟩ :
      NormalForm.selectionSetNormal schema returnType selectionSet)

theorem selectionSetNormal_inline_child
    {schema : Schema} {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {selectionSet rest : List Selection}
    : NormalForm.selectionSetNormal schema parentType
        (Selection.inlineFragment (some typeCondition) directives selectionSet :: rest)
      -> NormalForm.selectionSetNormal schema typeCondition selectionSet := by
  intro hnormal
  unfold NormalForm.selectionSetNormal at hnormal
  rcases hnormal with ⟨hground, hnonRedundant⟩
  unfold NormalForm.selectionSetGroundTyped at hground
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant
  have hselectionGround :
      NormalForm.selectionGroundTyped schema parentType
        (Selection.inlineFragment (some typeCondition) directives selectionSet) := by
    exact hground.2 _ (by simp)
  have hselectionNonRedundant :
      NormalForm.selectionNonRedundant
        (Selection.inlineFragment (some typeCondition) directives selectionSet) := by
    exact hnonRedundant.2.2 _ (by simp)
  unfold NormalForm.selectionGroundTyped at hselectionGround
  unfold NormalForm.selectionNonRedundant at hselectionNonRedundant
  exact ⟨hselectionGround.2, hselectionNonRedundant⟩

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
      have hrestAll :
          NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate (List.mem_cons_of_mem selection hcandidate)
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          have hrestNotMem :
              responseName ∉ rest.filterMap Selection.responseName? := by
            intro hmem
            exact hnotMem (by
              simp [Selection.responseName?, hmem])
          have hfieldNe : fieldResponseName ≠ responseName := by
            intro heq
            exact hnotMem (by simp [Selection.responseName?, heq])
          apply NormalForm.selectionSetResponseNameFree_cons
          · simpa [NormalForm.selectionResponseNameFree] using hfieldNe
          · exact selectionSetResponseNameFree_of_allFields_responseNamesNodup
              schema parentType responseName rest hrestAll hrestNotMem
      | inlineFragment typeCondition directives selectionSet =>
          simp [Selection.isField] at hheadField

def outputNamesFreeForSelectionSet
    (schema : Schema) (parentType : Name)
    (outputFields : List (Name × Execution.ResponseValue))
    (selectionSet : List Selection)
    : Prop :=
  ∀ responseName,
    responseName ∈ outputFields.map Prod.fst
    -> NormalForm.selectionSetResponseNameFree schema parentType responseName selectionSet

theorem outputNamesFreeForSelectionSet_nil
    (schema : Schema) (parentType : Name)
    (selectionSet : List Selection)
    : outputNamesFreeForSelectionSet schema parentType [] selectionSet := by
  intro responseName hmem
  simp at hmem

theorem outputNamesFreeForSelectionSet_tail
    {schema : Schema} {parentType : Name}
    {selection : Selection} {selectionSet : List Selection}
    {outputFields : List (Name × Execution.ResponseValue)}
    : outputNamesFreeForSelectionSet schema parentType outputFields
        (selection :: selectionSet)
      -> outputNamesFreeForSelectionSet schema parentType outputFields selectionSet := by
  intro hfree responseName hmem
  exact NormalForm.selectionSetResponseNameFree_tail
    (hfree responseName hmem)

theorem outputNamesFreeForSelectionSet_cons_output
    {schema : Schema} {parentType responseName : Name}
    {response : Execution.ResponseValue}
    {outputFields : List (Name × Execution.ResponseValue)}
    {selectionSet : List Selection}
    : outputNamesFreeForSelectionSet schema parentType outputFields selectionSet
      -> NormalForm.selectionSetResponseNameFree schema parentType responseName
          selectionSet
      -> outputNamesFreeForSelectionSet schema parentType
          (outputFields ++ [(responseName, response)]) selectionSet := by
  intro houtput hresponse candidate hmem
  have hcases :
      candidate ∈ outputFields.map Prod.fst ∨ candidate = responseName := by
    simpa using hmem
  cases hcases with
  | inl hprefix =>
      exact houtput candidate hprefix
  | inr hcandidate =>
      subst candidate
      exact hresponse

theorem responseName_not_mem_output_of_field_head_outputNamesFree
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet rest : List Selection}
    {outputFields : List (Name × Execution.ResponseValue)}
    : outputNamesFreeForSelectionSet schema parentType outputFields
        (Selection.field responseName fieldName arguments directives selectionSet :: rest)
      -> responseName ∉ outputFields.map Prod.fst := by
  intro houtput hmem
  have hfree := houtput responseName hmem
  have hhead :=
    NormalForm.selectionSetResponseNameFree_head hfree
  simp [NormalForm.selectionResponseNameFree] at hhead

theorem collectFields_responseName_not_mem_of_allFields_responseNameFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName : Name)
    : ∀ selectionSet,
        NormalForm.selectionsAllFields selectionSet
        -> NormalForm.selectionSetDirectiveFree selectionSet
        -> NormalForm.selectionSetResponseNameFree schema parentType responseName
            selectionSet
        -> responseName
            ∉ (Execution.collectFields schema variableValues parentType source
                selectionSet).map
                Prod.fst
  | [], _hall, _hfree, _hresponseFree => by
      simp [Execution.collectFields]
  | Selection.field fieldResponseName fieldName arguments directives
      selectionSet :: rest,
      hall, hfree, hresponseFree => by
      have hheadFree := NormalForm.selectionSetDirectiveFree_head hfree
      have htailFree := NormalForm.selectionSetDirectiveFree_tail hfree
      have htailAll :
          NormalForm.selectionsAllFields rest := by
        intro candidate hcandidate
        exact hall candidate
          (List.mem_cons_of_mem
            (Selection.field fieldResponseName fieldName arguments
              directives selectionSet) hcandidate)
      have htailResponseFree :
          NormalForm.selectionSetResponseNameFree schema parentType
            responseName rest :=
        NormalForm.selectionSetResponseNameFree_tail hresponseFree
      have hfieldNe : fieldResponseName ≠ responseName := by
        have hheadResponseFree :=
          NormalForm.selectionSetResponseNameFree_head hresponseFree
        simpa [NormalForm.selectionResponseNameFree] using hheadResponseFree
      have hdirectives : directives = [] := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.1
      subst directives
      rw [NormalForm.GroundTypeNormalization.collectFields_field_noDirectives]
      intro hmem
      have hcases :=
        (NormalForm.GroundTypeNormalization.mergeExecutableGroups_mem_responseName
          [(fieldResponseName, [{
            parentType := parentType,
            responseName := fieldResponseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }])]
          (Execution.collectFields schema variableValues parentType source
            rest)
          responseName).mp hmem
      cases hcases with
      | inl hhead =>
          simp at hhead
          exact hfieldNe hhead.symm
      | inr htail =>
          exact
            collectFields_responseName_not_mem_of_allFields_responseNameFree
              schema variableValues parentType source responseName
              rest htailAll htailFree htailResponseFree htail
  | Selection.inlineFragment typeCondition directives selectionSet :: rest,
      hall, _hfree, _hresponseFree => by
      have hheadField :
          Selection.isField
            (Selection.inlineFragment typeCondition directives selectionSet) :=
        hall _ (by simp)
      simp [Selection.isField] at hheadField

theorem visitSubfields_possibleTypeNormalizations_not_mem_eq_self
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> NormalForm.objectTypeNameBool schema objectType = true)
      -> runtimeType ∉ possibleTypes
      -> ∀ output,
          (visitSubfields schema resolvers variableValues
            depth runtimeType (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema possibleTypes selectionSet)
            output).fst
          = output := by
  intro hobjects hnotin output
  induction possibleTypes with
  | nil =>
      simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
        visitSubfields]
  | cons objectType rest ih =>
      have hobject :
          NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hne : objectType ≠ runtimeType := by
        intro heq
        subst objectType
        exact hnotin (by simp)
      have hrestNotin : runtimeType ∉ rest := by
        intro hmem
        exact hnotin (by simp [hmem])
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      cases hnormalized
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
            hnormalized] using ih hrestObjects hrestNotin
      | cons selection restNormalized =>
          have hskip :
              Execution.doesFragmentTypeApplyBool schema runtimeType
                  (Execution.ResolverValue.object runtimeType ref) objectType =
                false :=
            NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
              schema (ref := ref) hobject hne
          have htail :
              (visitSubfields schema resolvers variableValues depth runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet)
                  output).fst = output :=
            ih hrestObjects hrestNotin
          simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
            hnormalized, visitSubfields, visitSelection, hskip] using htail

theorem visitSubfields_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat)
    (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> NormalForm.objectTypeNameBool schema objectType = true)
      -> possibleTypes.Nodup
      -> runtimeType ∈ possibleTypes
      -> ∀ output,
          (visitSubfields schema resolvers variableValues
            depth runtimeType (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema possibleTypes selectionSet)
            output).fst
          = (visitSubfields schema resolvers variableValues
              depth runtimeType (Execution.ResolverValue.object runtimeType ref)
              (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
              output).fst := by
  intro hobjects hnodup hmem output
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject :
          NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      cases hnormalized
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have htail :
                (visitSubfields schema resolvers variableValues depth runtimeType
                    (Execution.ResolverValue.object runtimeType ref)
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet)
                    output).fst = output :=
              visitSubfields_possibleTypeNormalizations_not_mem_eq_self
                schema resolvers variableValues depth runtimeType ref rest
                selectionSet hrestObjects hrestNotin output
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized, visitSubfields] using htail
          · have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using
              ih hrestObjects hrestNodup hrestMem
      | cons selection restNormalized =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hobjectRuntime :
                NormalForm.objectTypeNameBool schema runtimeType = true :=
              hobject
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                    (Execution.ResolverValue.object runtimeType ref)
                    runtimeType =
                  true :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
                schema (ref := ref) hobjectRuntime
            have htail :
                ∀ output',
                  (visitSubfields schema resolvers variableValues depth
                      runtimeType (Execution.ResolverValue.object runtimeType ref)
                      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                        schema rest selectionSet)
                      output').fst = output' :=
              visitSubfields_possibleTypeNormalizations_not_mem_eq_self
                schema resolvers variableValues depth runtimeType ref rest
                selectionSet hrestObjects hrestNotin
            have htailAt :
                (visitSubfields schema resolvers variableValues depth runtimeType
                    (Execution.ResolverValue.object runtimeType ref)
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet)
                    (visitSubfields schema resolvers variableValues depth
                      runtimeType
                      (Execution.ResolverValue.object runtimeType ref)
                      (selection :: restNormalized) output).fst).fst =
                  (visitSubfields schema resolvers variableValues depth
                    runtimeType
                    (Execution.ResolverValue.object runtimeType ref)
                    (selection :: restNormalized) output).fst :=
              htail
                (visitSubfields schema resolvers variableValues depth
                  runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  (selection :: restNormalized) output).fst
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized, visitSubfields, visitSelection, happly,
              selectionDirectivesAllowBool_empty] using htailAt
          · have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                    (Execution.ResolverValue.object runtimeType ref) objectType =
                  false :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                schema (ref := ref) hobject heq
            have htail :
                (visitSubfields schema resolvers variableValues depth runtimeType
                    (Execution.ResolverValue.object runtimeType ref)
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet)
                    output).fst =
                  (visitSubfields schema resolvers variableValues depth runtimeType
                    (Execution.ResolverValue.object runtimeType ref)
                    (NormalForm.normalizeSelectionSet schema runtimeType
                      selectionSet)
                    output).fst :=
              ih hrestObjects hrestNodup hrestMem
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized, visitSubfields, visitSelection, hskip] using htail

theorem executeSelectionSet_possibleTypeNormalizations_runtime_normalized_branch
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> NormalForm.objectTypeNameBool schema objectType = true)
      -> possibleTypes.Nodup
      -> runtimeType ∈ possibleTypes
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            runtimeType (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
              possibleTypes selectionSet)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              runtimeType (Execution.ResolverValue.object runtimeType ref)
              (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hobjects hnodup hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      cases hnormalized
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hrestEq :
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (Execution.ResolverValue.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (Execution.ResolverValue.object runtimeType ref)
                  [] := by
              simpa using
                NormalForm.GroundTypeNormalization.executeSelectionSet_append_possibleTypeNormalizations_not_mem
                  schema resolvers variableValues depth runtimeType
                  (ref := ref) rest selectionSet [] hrestObjects hrestNotin
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using hrestEq
          · have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hhead =>
                  exact False.elim (heq hhead.symm)
              | inr htail =>
                  exact htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using ih hrestObjects hrestNodup hrestMem
      | cons selection restNormalized =>
          rw [show
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema (objectType :: rest) selectionSet =
                Selection.inlineFragment (some objectType) []
                    (selection :: restNormalized)
                  ::
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet by
            simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized]]
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (Execution.ResolverValue.object runtimeType ref) runtimeType =
                  true :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
                schema (ref := ref) hobject
            rw [
              NormalForm.GroundTypeNormalization.executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                schema resolvers variableValues depth runtimeType runtimeType
                (Execution.ResolverValue.object runtimeType ref)
                (selection :: restNormalized)
                (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet)
                (by simpa using happly)]
            rw [
              NormalForm.GroundTypeNormalization.executeSelectionSet_append_possibleTypeNormalizations_not_mem
                schema resolvers variableValues depth runtimeType (ref := ref)
                rest selectionSet (selection :: restNormalized) hrestObjects
                hrestNotin]
            simp [hnormalized]
          · have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (Execution.ResolverValue.object runtimeType ref) objectType =
                  false :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                schema (ref := ref) hobject heq
            rw [
              NormalForm.GroundTypeNormalization.executeSelectionSet_inlineFragment_some_directiveFree_skip
                schema resolvers variableValues depth runtimeType objectType
                (Execution.ResolverValue.object runtimeType ref)
                (selection :: restNormalized)
                (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet)
                (by simpa using hskip)]
            have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hhead =>
                  exact False.elim (heq hhead.symm)
              | inr htail =>
                  exact htail
            exact ih hrestObjects hrestNodup hrestMem

theorem visitSubfields_possibleTypeNormalizations_eq_spec_of_runtime_normalized
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> NormalForm.objectTypeNameBool schema objectType = true)
      -> possibleTypes.Nodup
      -> runtimeType ∈ possibleTypes
      -> (visitSubfields schema resolvers variableValues depth runtimeType
            (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
            (Execution.ResponseValue.object [])).fst
          = Execution.ResponseValue.object
              (Execution.Result.getD []
                (Execution.executeSelectionSet schema resolvers variableValues depth
                  runtimeType (Execution.ResolverValue.object runtimeType ref)
                  (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)))
      -> (visitSubfields schema resolvers variableValues depth runtimeType
            (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
              possibleTypes selectionSet)
            (Execution.ResponseValue.object [])).fst
          = Execution.ResponseValue.object
              (Execution.Result.getD []
                (Execution.executeSelectionSet schema resolvers variableValues depth
                  runtimeType (Execution.ResolverValue.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
                    possibleTypes selectionSet))) := by
  intro hobjects hnodup hmem hnormalized
  have hvisit :=
    visitSubfields_possibleTypeNormalizations_runtime_branch schema resolvers
      variableValues depth runtimeType (ref := ref) possibleTypes
      selectionSet hobjects hnodup hmem
  have hexec :=
    executeSelectionSet_possibleTypeNormalizations_runtime_normalized_branch
      schema resolvers variableValues depth runtimeType (ref := ref)
      possibleTypes selectionSet hobjects hnodup hmem
  rw [hvisit, hnormalized, hexec]

theorem visitSubfields_getPossibleTypesNormalizations_eq_spec_of_runtime_normalized
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (childType runtimeType : Name)
    (ref : ObjectRef)
    (selectionSet : List Selection)
    : schema.typeIncludesObjectBool childType runtimeType = true
      -> (visitSubfields schema resolvers variableValues depth runtimeType
            (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
            (Execution.ResponseValue.object [])).fst
          = Execution.ResponseValue.object
              (Execution.Result.getD []
                (Execution.executeSelectionSet schema resolvers variableValues depth
                  runtimeType (Execution.ResolverValue.object runtimeType ref)
                  (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)))
      -> (visitSubfields schema resolvers variableValues depth runtimeType
            (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
              (schema.getPossibleTypes childType) selectionSet)
            (Execution.ResponseValue.object [])).fst
          = Execution.ResponseValue.object
              (Execution.Result.getD []
                (Execution.executeSelectionSet schema resolvers variableValues depth
                  runtimeType (Execution.ResolverValue.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
                    (schema.getPossibleTypes childType) selectionSet))) := by
  intro hinclude hnormalized
  have hmem : runtimeType ∈ schema.getPossibleTypes childType :=
    List.contains_iff_mem.mp hinclude
  have hobjects :
      ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
        NormalForm.objectTypeNameBool schema objectType = true := by
    intro objectType hobjectType
    exact NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
      schema
      (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
        hschema childType objectType hobjectType)
  exact
    visitSubfields_possibleTypeNormalizations_eq_spec_of_runtime_normalized
      schema resolvers variableValues depth runtimeType (ref := ref)
      (schema.getPossibleTypes childType) selectionSet hobjects
      (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType)
      hmem hnormalized

theorem visitSubfields_normalizedFieldSubselections_eq_spec_of_runtime
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (depth : Nat) (childType runtimeType : Name)
    (ref : ObjectRef)
    (selectionSet : List Selection)
    : schema.typeIncludesObjectBool childType runtimeType = true
      -> (visitSubfields schema resolvers variableValues depth runtimeType
            (Execution.ResolverValue.object runtimeType ref)
            (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
            (Execution.ResponseValue.object [])).fst
          = Execution.ResponseValue.object
              (Execution.Result.getD []
                (Execution.executeSelectionSet schema resolvers variableValues depth
                  runtimeType (Execution.ResolverValue.object runtimeType ref)
                  (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)))
      -> (visitSubfields schema resolvers variableValues depth runtimeType
            (Execution.ResolverValue.object runtimeType ref)
            (if NormalForm.objectTypeNameBool schema childType then
                NormalForm.normalizeSelectionSet schema childType selectionSet
              else
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
                  (schema.getPossibleTypes childType) selectionSet)
            (Execution.ResponseValue.object [])).fst
          = Execution.ResponseValue.object
              (Execution.Result.getD []
                (Execution.executeSelectionSet schema resolvers variableValues depth
                  runtimeType (Execution.ResolverValue.object runtimeType ref)
                  (if NormalForm.objectTypeNameBool schema childType then
                      NormalForm.normalizeSelectionSet schema childType selectionSet
                    else
                      NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                        schema (schema.getPossibleTypes childType) selectionSet))) := by
  intro hinclude hnormalized
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hruntimeEq : runtimeType = childType :=
      NormalForm.GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
        schema hobject hinclude
    subst runtimeType
    simpa [hobject] using hnormalized
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    simpa [hfalse] using
      visitSubfields_getPossibleTypesNormalizations_eq_spec_of_runtime_normalized
        schema resolvers variableValues hschema depth childType runtimeType
        (ref := ref) selectionSet hinclude hnormalized

def generatedNormalizedFieldChild
    (schema : Schema) (childType : Name)
    (childSelectionSet : List Selection)
    : Prop :=
  ∃ sourceSelectionSet,
    NormalForm.selectionSetDirectiveFree sourceSelectionSet
    ∧ childSelectionSet
      = if NormalForm.objectTypeNameBool schema childType then
          NormalForm.normalizeSelectionSet schema childType sourceSelectionSet
        else
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet

theorem generatedNormalizedFieldChild_selectionSetDirectiveFree
    (schema : Schema) (childType : Name)
    (childSelectionSet : List Selection)
    : generatedNormalizedFieldChild schema childType childSelectionSet
      -> NormalForm.selectionSetDirectiveFree childSelectionSet := by
  intro hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType
            sourceSelectionSet := by
      simpa [hobject] using hchild
    simpa [hchildEq, NormalForm.selectionSetNormal] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
        schema childType sourceSelectionSet hsourceFree
  · have hfalse :
        NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    simpa [hchildEq] using
      NormalForm.GroundTypeNormalization.selectionSetDirectiveFree_possibleTypeNormalizations
        schema (schema.getPossibleTypes childType)
        (selectionSet := sourceSelectionSet)
        (fun objectType _hobjectType =>
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
            schema objectType sourceSelectionSet hsourceFree)

theorem generatedNormalizedFieldChild_selectionSetNormal
    (schema : Schema) (childType : Name)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> NormalForm.selectionSetNormal schema childType childSelectionSet := by
  intro hschema hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, _hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType
            sourceSelectionSet := by
      simpa [hobject] using hchild
    simpa [hchildEq] using
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal
        schema hschema childType sourceSelectionSet
        hobject
  · have hfalse :
        NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    have hground :
        NormalForm.selectionSetGroundTyped schema childType
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.possibleTypeNormalizations_groundTyped
        schema childType (schema.getPossibleTypes childType) sourceSelectionSet
        hfalse
        (fun objectType hobjectType =>
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema childType objectType hobjectType)
        (fun objectType hobjectType =>
          List.contains_iff_mem.mpr hobjectType)
        (fun objectType hobjectType =>
          NormalForm.GroundTypeNormalization.normalizeSelectionSet_groundTyped
            schema hschema objectType sourceSelectionSet
            (NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
              schema
              (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema childType objectType hobjectType)))
    have hnonRedundant :
        NormalForm.selectionSetNonRedundant
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.possibleTypeNormalizations_nonRedundant
        schema (schema.getPossibleTypes childType) sourceSelectionSet
        (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
          childType)
        (fun objectType hobjectType =>
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_normal
            schema hschema objectType sourceSelectionSet
            (NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
              schema
              (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                hschema childType objectType hobjectType))).2)
    simpa [hchildEq, NormalForm.selectionSetNormal] using
      (⟨hground, hnonRedundant⟩ :
        NormalForm.selectionSetNormal schema childType
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet))

theorem collectFields_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> NormalForm.objectTypeNameBool schema objectType = true)
      -> possibleTypes.Nodup
      -> runtimeType ∈ possibleTypes
      -> GraphQL.Execution.collectFields schema variableValues runtimeType
            (.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
              possibleTypes selectionSet)
          = GraphQL.Execution.collectFields schema variableValues runtimeType
              (.object runtimeType ref)
              (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hobjects hnodup hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      cases hnormalized
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) = [] :=
              NormalForm.GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
                schema variableValues runtimeType (ref := ref) rest
                selectionSet hrestObjects hrestNotin
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized, GraphQL.Execution.collectFields] using hrestCollect
          · have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using ih hrestObjects hrestNodup hrestMem
      | cons selection restNormalized =>
          rw [show
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema (objectType :: rest) selectionSet =
                Selection.inlineFragment (some objectType) []
                  (selection :: restNormalized)
                  :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet by
            simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized]]
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hrestCollect :
                GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) = [] :=
              NormalForm.GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
                schema variableValues runtimeType (ref := ref) rest
                selectionSet hrestObjects hrestNotin
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                    (.object runtimeType ref) runtimeType =
                  true :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
                schema (ref := ref) hobject
            rw [NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_apply_flatten
              schema variableValues runtimeType runtimeType
              (.object runtimeType ref) (selection :: restNormalized)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema rest selectionSet) happly]
            rw [GraphQL.NormalForm.collectFields_append]
            rw [hrestCollect]
            simp [hnormalized, GraphQL.Execution.mergeExecutableGroups_nil_right]
          · have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                    (.object runtimeType ref) objectType =
                  false :=
              NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                schema (ref := ref) hobject heq
            rw [NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
              schema variableValues runtimeType objectType
              (.object runtimeType ref) (selection :: restNormalized)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema rest selectionSet) hskip]
            have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            exact ih hrestObjects hrestNodup hrestMem

theorem selectionSetLookupValid_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : runtimeType ∈ possibleTypes
      -> NormalForm.selectionSetLookupValid schema runtimeType
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            possibleTypes selectionSet)
      -> NormalForm.selectionSetLookupValid schema runtimeType
          (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      intro hlookup
      cases hnormalized
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            simpa [hnormalized] using
              NormalForm.selectionSetLookupValid_nil schema runtimeType
          · have htailLookup :
                NormalForm.selectionSetLookupValid schema runtimeType
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) := by
              simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized] using hlookup
            exact ih htail htailLookup
      | cons selection normalizedRest =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            have hlookupFn :
                ∀ candidate,
                  candidate ∈
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema (runtimeType :: rest) selectionSet ->
                    NormalForm.selectionLookupValid schema runtimeType
                      candidate := by
              simpa [NormalForm.selectionSetLookupValid] using hlookup
            have hheadLookup :
                NormalForm.selectionSetLookupValid schema runtimeType
                  (selection :: normalizedRest) := by
              have hfirst :
                  NormalForm.selectionLookupValid schema runtimeType
                    (Selection.inlineFragment (some runtimeType) []
                      (selection :: normalizedRest)) := by
                exact hlookupFn
                  (Selection.inlineFragment (some runtimeType) []
                    (selection :: normalizedRest))
                  (by
                    simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                      hnormalized])
              simpa [NormalForm.selectionLookupValid] using hfirst
            simpa [hnormalized] using hheadLookup
          · have hlookupFn :
                ∀ candidate,
                  candidate ∈
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema (objectType :: rest) selectionSet ->
                    NormalForm.selectionLookupValid schema runtimeType
                      candidate := by
              simpa [NormalForm.selectionSetLookupValid] using hlookup
            have htailLookup :
              NormalForm.selectionSetLookupValid schema runtimeType
                (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema rest selectionSet) := by
              simp [NormalForm.selectionSetLookupValid]
              intro candidate hcandidate
              have hcandidateFull :
                  candidate ∈
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema (objectType :: rest) selectionSet := by
                rw [show
                    NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                        schema (objectType :: rest) selectionSet =
                      Selection.inlineFragment (some objectType) []
                        (selection :: normalizedRest)
                        :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                          schema rest selectionSet by
                  simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                    hnormalized]]
                exact List.mem_cons_of_mem
                  (Selection.inlineFragment (some objectType) []
                    (selection :: normalizedRest)) hcandidate
              exact hlookupFn candidate
                hcandidateFull
            exact ih htail htailLookup

theorem fieldMerge_collectFields_possibleTypeNormalizations_runtime_branch_mem
    (schema : Schema) (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection)
    (scopedField : FieldMerge.ScopedField)
    : runtimeType ∈ possibleTypes
      -> scopedField
          ∈ FieldMerge.collectFields schema runtimeType
              (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
      -> scopedField
          ∈ FieldMerge.collectFields schema runtimeType
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
                possibleTypes selectionSet) := by
  intro hmem hscoped
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      cases hnormalized
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            simp [hnormalized, FieldMerge.collectFields] at hscoped
          · have htailMem :
                scopedField ∈
                  FieldMerge.collectFields schema runtimeType
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) :=
              ih htail
            simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using htailMem
      | cons selection normalizedRest =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            rw [show
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema (runtimeType :: rest) selectionSet =
                  Selection.inlineFragment (some runtimeType) []
                    (selection :: normalizedRest)
                    :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet by
              simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized]]
            simp [FieldMerge.collectFields]
            exact Or.inl (by
              simpa [hnormalized] using hscoped)
          · have htailMem :
                scopedField ∈
                  FieldMerge.collectFields schema runtimeType
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) :=
              ih htail
            rw [show
                NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema (objectType :: rest) selectionSet =
                  Selection.inlineFragment (some objectType) []
                    (selection :: normalizedRest)
                    :: NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet by
              simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized]]
            simp [FieldMerge.collectFields]
            exact Or.inr htailMem

theorem fieldsInSetCanMerge_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : runtimeType ∈ possibleTypes
      -> FieldMerge.fieldsInSetCanMerge schema runtimeType
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            possibleTypes selectionSet)
      -> FieldMerge.fieldsInSetCanMerge schema runtimeType
          (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hmem hmerge
  apply FieldMerge.fieldsInSetCanMerge_mono schema runtimeType
    (NormalForm.normalizeSelectionSet schema runtimeType selectionSet)
    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
      possibleTypes selectionSet)
    hmerge
  intro scopedField hscoped
  exact
    fieldMerge_collectFields_possibleTypeNormalizations_runtime_branch_mem
      schema runtimeType possibleTypes selectionSet scopedField hmem hscoped

theorem selectionSetValidInPossibleTypes_possibleTypeNormalizations_runtime_branch
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (runtimeType : Name)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType, objectType ∈ possibleTypes -> schema.objectType objectType)
      -> runtimeType ∈ possibleTypes
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions runtimeType
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            possibleTypes selectionSet)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions runtimeType
          (NormalForm.normalizeSelectionSet schema runtimeType selectionSet) := by
  intro hobjects hmem
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      intro himplementation
      have hrestObjects :
          ∀ candidate, candidate ∈ rest -> schema.objectType candidate := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      cases hnormalized
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            simp [hnormalized, Validation.selectionSetValidInPossibleTypes]
          · have htailImplementation :
                Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions runtimeType
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) := by
              simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized] using himplementation
            exact ih hrestObjects htail htailImplementation
      | cons selection normalizedRest =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst objectType
            have hparts :
                Validation.selectionValidInPossibleTypes schema
                    variableDefinitions runtimeType
                    (Selection.inlineFragment (some runtimeType) []
                      (selection :: normalizedRest))
                  ∧
                  Validation.selectionSetValidInPossibleTypes schema
                    variableDefinitions runtimeType
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) := by
              simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized,
                Validation.selectionSetValidInPossibleTypes] using
                himplementation
            have hheadImplementation :
                Validation.selectionValidInPossibleTypes schema
                  variableDefinitions runtimeType
                  (Selection.inlineFragment (some runtimeType) []
                    (selection :: normalizedRest)) :=
              hparts.1
            have hoverlap :
                schema.typesOverlapBool runtimeType runtimeType = true :=
              NormalForm.object_typesOverlapBool_self schema
                (hobjects runtimeType (by simp))
            have hbranch :
                ∀ objectType,
                  objectType ∈ schema.getPossibleTypes runtimeType ->
                    Validation.selectionSetValidInPossibleTypes schema
                      variableDefinitions objectType
                      (selection :: normalizedRest) := by
              simpa [Validation.selectionValidInPossibleTypes] using
                hheadImplementation hoverlap
            have hruntimePossible :
                runtimeType ∈ schema.getPossibleTypes runtimeType :=
              List.contains_iff_mem.mp
                (NormalForm.object_typeIncludesObjectBool_self schema
                  (hobjects runtimeType (by simp)))
            simpa [hnormalized] using hbranch runtimeType hruntimePossible
          · have htailImplementation :
                Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions runtimeType
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet) := by
              have hparts :
                  Validation.selectionValidInPossibleTypes schema
                      variableDefinitions runtimeType
                      (Selection.inlineFragment (some objectType) []
                        (selection :: normalizedRest))
                    ∧
                    Validation.selectionSetValidInPossibleTypes schema
                      variableDefinitions runtimeType
                      (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                        schema rest selectionSet) := by
                simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
                  hnormalized,
                  Validation.selectionSetValidInPossibleTypes] using
                  himplementation
              exact hparts.2
            exact ih hrestObjects htail htailImplementation

theorem freshPrefixSelectionDerivation_possibleTypeNormalizations_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes
        -> NormalForm.objectTypeNameBool schema objectType = true)
      -> possibleTypes.Nodup
      -> (∀ objectType,
            objectType ∈ possibleTypes
            -> objectType = runtimeType
            -> FreshPrefixSelectionDerivation schema variableValues runtimeType
                (.object runtimeType ref)
                (NormalForm.normalizeSelectionSet schema objectType selectionSet))
      -> FreshPrefixSelectionDerivation schema variableValues runtimeType
          (.object runtimeType ref)
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            possibleTypes selectionSet) := by
  intro hobjects hnodup hnormalized
  induction possibleTypes with
  | nil =>
      simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations]
      exact FreshPrefixSelectionDerivation.nil
  | cons objectType rest ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hobject : NormalForm.objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            NormalForm.objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestDerivation :
          FreshPrefixSelectionDerivation schema variableValues runtimeType
            (.object runtimeType ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema rest selectionSet) :=
        ih hrestObjects hparts.2
          (fun candidate hcandidate heq =>
            hnormalized candidate
              (List.mem_cons_of_mem objectType hcandidate) heq)
      cases hnormalizedSet
            : NormalForm.normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simpa [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
            hnormalizedSet] using hrestDerivation
      | cons selection restSelection =>
          have hhead :
              FreshPrefixSelectionDerivation schema variableValues runtimeType
                (.object runtimeType ref)
                [Selection.inlineFragment (some objectType) []
                  (selection :: restSelection)] :=
            FreshPrefixSelectionDerivation.inlineFragmentSome objectType []
              (selection :: restSelection)
              (by
                intro _hallow happly
                by_cases heq : objectType = runtimeType
                · subst objectType
                  simpa [hnormalizedSet] using
                    hnormalized runtimeType (by simp) rfl
                · have hskip :
                      Execution.doesFragmentTypeApplyBool schema runtimeType
                          (.object runtimeType ref) objectType =
                        false :=
                    NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                      schema (ref := ref) hobject heq
                  rw [hskip] at happly
                  contradiction)
          have hdisjoint :
              GraphQL.NormalForm.executableGroupNamesDisjoint
                (GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  [Selection.inlineFragment (some objectType) []
                    (selection :: restSelection)])
                (GraphQL.Execution.collectFields schema variableValues
                  runtimeType (.object runtimeType ref)
                  (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet)) := by
            by_cases heq : objectType = runtimeType
            · subst objectType
              have hrestNotin : runtimeType ∉ rest := hparts.1
              have hrestCollect :
                  GraphQL.Execution.collectFields schema variableValues
                    runtimeType (.object runtimeType ref)
                    (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                      schema rest selectionSet) = [] :=
                NormalForm.GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
                  schema variableValues runtimeType (ref := ref) rest
                  selectionSet hrestObjects hrestNotin
              intro responseName _hleft hright
              rw [hrestCollect] at hright
              simp at hright
            · have hheadCollect :
                  GraphQL.Execution.collectFields schema variableValues
                    runtimeType (.object runtimeType ref)
                    [Selection.inlineFragment (some objectType) []
                      (selection :: restSelection)] = [] := by
                rw [NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
                  schema variableValues runtimeType objectType
                  (.object runtimeType ref) (selection :: restSelection) []]
                · simp [GraphQL.Execution.collectFields]
                · exact
                  NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                    schema (ref := ref) hobject heq
              intro responseName hleft _hright
              rw [hheadCollect] at hleft
              simp at hleft
          rw [show
              NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                  schema (objectType :: rest) selectionSet =
                [Selection.inlineFragment (some objectType) []
                  (selection :: restSelection)] ++
                  NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                    schema rest selectionSet by
            simp [NormalForm.GroundTypeNormalization.possibleTypeNormalizations,
              hnormalizedSet]]
          exact
            FreshPrefixSelectionDerivation.appendDisjoint
              [Selection.inlineFragment (some objectType) []
                (selection :: restSelection)]
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema rest selectionSet)
              hhead hrestDerivation hdisjoint

theorem freshPrefixSelectionDerivation_generatedNormalizedFieldChild_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> FreshPrefixSelectionDerivation schema variableValues childRuntime
          (.object childRuntime ref) childSelectionSet := by
  intro hschema hinclude hgenerated
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    rw [hchild]
    simp [hobject]
    exact
      FreshPrefixSelectionDerivation.of_allFields_directiveFree_responseNamesNodup
        schema variableValues childType (.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childType sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childType sourceSelectionSet)
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    rw [hchild]
    simp [hfalse]
    apply freshPrefixSelectionDerivation_possibleTypeNormalizations_runtime
      schema variableValues childRuntime ref (schema.getPossibleTypes childType)
      sourceSelectionSet
    · intro objectType hobjectType
      exact NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType schema
        (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
          childType objectType hobjectType)
    · exact
        SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
          childType
    · intro objectType _hobjectType heq
      subst objectType
      exact
        FreshPrefixSelectionDerivation.of_allFields_directiveFree_responseNamesNodup
          schema variableValues childRuntime (.object childRuntime ref)
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet)
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
            schema childRuntime sourceSelectionSet)
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
            schema childRuntime sourceSelectionSet hsourceFree)
          (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
            schema childRuntime sourceSelectionSet)

theorem generatedNormalizedFieldChild_of_collectFields_field_layer
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (hall : NormalForm.selectionsAllFields selectionSet)
    (hfree : NormalForm.selectionSetDirectiveFree selectionSet)
    (hnodup : NormalForm.responseNamesNodup selectionSet)
    (hchildren
      : ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> generatedNormalizedFieldChild schema
              ((schema.fieldReturnType? parentType fieldName).getD fieldName)
              childSelectionSet)
    : ∀ {responseName : Name} {field : Execution.ExecutableField}
        {fields prefixTail : List Execution.ExecutableField},
        (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet
        -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
        -> generatedNormalizedFieldChild schema
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            field.selectionSet := by
  intro responseName field fields prefixTail hgroup hprefix
  rcases
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_field_mem_prefix_empty
        schema variableValues parentType source selectionSet hall hfree hnodup
        hgroup hprefix with
    ⟨hfieldMem, _hfields, _hprefixTail⟩
  rcases List.mem_map.mp hfieldMem with
    ⟨selection, hselectionMem, hfieldEq⟩
  have hselectionField : Selection.isField selection :=
    hall selection hselectionMem
  cases selection with
  | field selectionResponseName selectionFieldName selectionArguments
      selectionDirectives selectionSet =>
      have hfieldEq' :
          field =
            FreshPrefixSelectionDerivation.executableFieldOfSelection
              parentType
              (Selection.field selectionResponseName selectionFieldName
                selectionArguments selectionDirectives selectionSet) :=
        hfieldEq.symm
      subst field
      exact
        hchildren selectionResponseName selectionFieldName selectionArguments
          selectionDirectives selectionSet hselectionMem
  | inlineFragment typeCondition directives selectionSet =>
      simp [Selection.isField] at hselectionField

theorem normalizeSelectionSet_field_child_generated (schema : Schema)
    : ∀ parentType selectionSet responseName fieldName arguments directives
        childSelectionSet,
        NormalForm.selectionSetDirectiveFree selectionSet
        -> Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ NormalForm.normalizeSelectionSet schema parentType selectionSet
        -> generatedNormalizedFieldChild schema
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
            childSelectionSet := by
  intro parentType selectionSet
  induction parentType, selectionSet
    using NormalForm.normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro responseName fieldName arguments directives childSelectionSet _hfree
        hmem
      simp [NormalForm.normalizeSelectionSet] at hmem
  | case2 parentType rest responseName fieldName arguments directives
      selectionSet hlookup hrest =>
      intro targetResponseName targetFieldName targetArguments
        targetDirectives childSelectionSet hfree hmem
      have hrestFree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.withoutFieldSelectionsWithResponseName schema responseName
              rest) :=
        NormalForm.withoutFieldSelectionsWithResponseName_directiveFree schema
          responseName rest (NormalForm.selectionSetDirectiveFree_tail hfree)
      exact hrest targetResponseName targetFieldName targetArguments
        targetDirectives childSelectionSet hrestFree
        (by
          simpa [NormalForm.normalizeSelectionSet, hlookup] using hmem)
  | case3 parentType rest responseName fieldName arguments directives
      selectionSet fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro targetResponseName targetFieldName targetArguments
        targetDirectives childSelectionSet hfree hmem
      have hheadFree :
          NormalForm.selectionDirectiveFree
            (Selection.field responseName fieldName arguments directives
              selectionSet) :=
        NormalForm.selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.1
      subst directives
      have hrestFree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.withoutFieldSelectionsWithResponseName schema responseName
              rest) :=
        NormalForm.withoutFieldSelectionsWithResponseName_directiveFree schema
          responseName rest (NormalForm.selectionSetDirectiveFree_tail hfree)
      have hmergedFree :
          NormalForm.selectionSetDirectiveFree mergedSubselections := by
        simpa [matching, mergedSubselections] using
          NormalForm.selectionSetDirectiveFree_fieldHead_merged schema
            parentType responseName fieldName arguments selectionSet rest hfree
      simp [NormalForm.normalizeSelectionSet, hlookup,
        NormalForm.normalizedField] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with ⟨hresponse, hfield, harguments,
          hdirectives, hchild⟩
        subst targetResponseName
        subst targetFieldName
        subst targetArguments
        subst targetDirectives
        subst childSelectionSet
        have hreturnEq :
            ((schema.fieldReturnType? parentType fieldName).getD fieldName)
              =
            returnType := by
          simp [Schema.fieldReturnType?, hlookup, returnType]
        refine ⟨mergedSubselections, hmergedFree, ?_⟩
        rw [hreturnEq]
        simp [returnType, mergedSubselections, matching,
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations]
        rfl
      · exact hrest targetResponseName targetFieldName targetArguments
          targetDirectives childSelectionSet hrestFree htail
  | case4 parentType rest directives selectionSet happend =>
      intro responseName fieldName arguments targetDirectives childSelectionSet
        hfree hmem
      have hheadFree :
          NormalForm.selectionDirectiveFree
            (Selection.inlineFragment none directives selectionSet) :=
        NormalForm.selectionSetDirectiveFree_head hfree
      have hselectionFree :
          NormalForm.selectionSetDirectiveFree selectionSet := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.2
      have htailFree :
          NormalForm.selectionSetDirectiveFree rest :=
        NormalForm.selectionSetDirectiveFree_tail hfree
      have happendFree :
          NormalForm.selectionSetDirectiveFree (selectionSet ++ rest) :=
        NormalForm.selectionSetDirectiveFree_append hselectionFree htailFree
      exact happend responseName fieldName arguments targetDirectives
        childSelectionSet happendFree
        (by simpa [NormalForm.normalizeSelectionSet] using hmem)
  | case5 parentType rest typeCondition directives selectionSet hoverlap
      hrest happend =>
      intro responseName fieldName arguments targetDirectives childSelectionSet
        hfree hmem
      have hheadFree :
          NormalForm.selectionDirectiveFree
            (Selection.inlineFragment (some typeCondition) directives
              selectionSet) :=
        NormalForm.selectionSetDirectiveFree_head hfree
      have hselectionFree :
          NormalForm.selectionSetDirectiveFree selectionSet := by
        simpa [NormalForm.selectionDirectiveFree] using hheadFree.2
      have htailFree :
          NormalForm.selectionSetDirectiveFree rest :=
        NormalForm.selectionSetDirectiveFree_tail hfree
      have happendFree :
          NormalForm.selectionSetDirectiveFree (selectionSet ++ rest) :=
        NormalForm.selectionSetDirectiveFree_append hselectionFree htailFree
      exact happend responseName fieldName arguments targetDirectives
        childSelectionSet happendFree
        (by simpa [NormalForm.normalizeSelectionSet, hoverlap] using hmem)
  | case6 parentType rest typeCondition directives selectionSet hoverlap
      hrest =>
      intro responseName fieldName arguments targetDirectives childSelectionSet
        hfree hmem
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      have htailFree :
          NormalForm.selectionSetDirectiveFree rest :=
        NormalForm.selectionSetDirectiveFree_tail hfree
      exact hrest responseName fieldName arguments targetDirectives
        childSelectionSet htailFree
        (by simpa [NormalForm.normalizeSelectionSet, hfalse] using hmem)

theorem generatedNormalizedFieldChild_of_generatedNormalizedFieldChild_collectFields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> ∀ {responseName : Name} {field : Execution.ExecutableField}
            {fields prefixTail : List Execution.ExecutableField},
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues childRuntime
                (.object childRuntime ref) childSelectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> generatedNormalizedFieldChild schema
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              field.selectionSet := by
  intro hschema hinclude hgenerated responseName field fields prefixTail hgroup
    hprefix
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType sourceSelectionSet := by
      simpa [hobject] using hchild
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childType
            (.object childType ref)
            (NormalForm.normalizeSelectionSet schema childType
              sourceSelectionSet) := by
      simpa [hchildEq] using hgroup
    exact
      generatedNormalizedFieldChild_of_collectFields_field_layer
        schema variableValues childType (.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childType sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childType sourceSelectionSet)
        (fun responseName fieldName arguments directives grandchildSelectionSet
            hmem =>
          normalizeSelectionSet_field_child_generated schema childType
            sourceSelectionSet responseName fieldName arguments directives
            grandchildSelectionSet hsourceFree hmem)
        hgroup' hprefix
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    have hpossibleMem : childRuntime ∈ schema.getPossibleTypes childType :=
      List.contains_iff_mem.mp hinclude
    have hobjects :
        ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
          NormalForm.objectTypeNameBool schema objectType = true := by
      intro objectType hobjectType
      exact
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
          schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema childType objectType hobjectType)
    have hpossibleNodup :
        (schema.getPossibleTypes childType).Nodup :=
      SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType
    have hcollect :
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) := by
      have hgroupPossible :
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues childRuntime
              (.object childRuntime ref)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema (schema.getPossibleTypes childType)
                sourceSelectionSet) := by
        simpa [hchildEq] using hgroup
      simpa [hcollect] using hgroupPossible
    exact
      generatedNormalizedFieldChild_of_collectFields_field_layer
        schema variableValues childRuntime (.object childRuntime ref)
        (NormalForm.normalizeSelectionSet schema childRuntime
          sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childRuntime sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childRuntime sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childRuntime sourceSelectionSet)
        (fun responseName fieldName arguments directives grandchildSelectionSet
            hmem =>
          normalizeSelectionSet_field_child_generated schema childRuntime
            sourceSelectionSet responseName fieldName arguments directives
            grandchildSelectionSet hsourceFree hmem)
        hgroup' hprefix

theorem collectFields_generatedNormalizedFieldChild_prefix_empty
    (schema : Schema) (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> ∀ {responseName : Name} {field : Execution.ExecutableField}
            {fields prefixTail : List Execution.ExecutableField},
          (responseName, field :: fields)
            ∈ GraphQL.Execution.collectFields schema variableValues childRuntime
                (.object childRuntime ref) childSelectionSet
          -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
          -> fields = [] ∧ prefixTail = [] := by
  intro hschema hinclude hgenerated responseName field fields prefixTail hgroup
    hprefix
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType sourceSelectionSet := by
      simpa [hobject] using hchild
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childType
            (.object childType ref)
            (NormalForm.normalizeSelectionSet schema childType
              sourceSelectionSet) := by
      simpa [hchildEq] using hgroup
    exact
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
        schema variableValues childType (.object childType ref)
        (NormalForm.normalizeSelectionSet schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childType sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childType sourceSelectionSet)
        hgroup' hprefix
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    have hpossibleMem : childRuntime ∈ schema.getPossibleTypes childType :=
      List.contains_iff_mem.mp hinclude
    have hobjects :
        ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
          NormalForm.objectTypeNameBool schema objectType = true := by
      intro objectType hobjectType
      exact
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
          schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema childType objectType hobjectType)
    have hpossibleNodup :
        (schema.getPossibleTypes childType).Nodup :=
      SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType
    have hcollect :
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) := by
      have hgroupPossible :
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues childRuntime
              (.object childRuntime ref)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema (schema.getPossibleTypes childType)
                sourceSelectionSet) := by
        simpa [hchildEq] using hgroup
      simpa [hcollect] using hgroupPossible
    exact
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
        schema variableValues childRuntime (.object childRuntime ref)
        (NormalForm.normalizeSelectionSet schema childRuntime sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childRuntime sourceSelectionSet)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_directiveFree
          schema childRuntime sourceSelectionSet hsourceFree)
        (NormalForm.GroundTypeNormalization.normalizeSelectionSet_responseNamesNodup
          schema childRuntime sourceSelectionSet)
        hgroup' hprefix

theorem collectFields_fieldNormal_childLocalFacts_object
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues)
    (parentType runtimeType : Name)
    (ref : ObjectRef)
    (selectionSet : List Selection)
    (responseName childRuntime : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType parentType
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> NormalForm.selectionSetLookupValid schema parentType selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> NormalForm.selectionsAllFields selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType
              (.object runtimeType ref) selectionSet
      -> schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            childRuntime
          = true
      -> NormalForm.selectionSetLookupValid schema childRuntime field.selectionSet
          ∧ Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions childRuntime field.selectionSet
          ∧ (∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType field.selectionSet) := by
  intro hschema hparentRuntime hvalid hlookupValid himplementation hmerge
    hall hgroup hinclude
  have hcompatible :
      ∀ candidate, candidate ∈ field :: ([] : List Execution.ExecutableField) ->
        ∀ scopedField,
          scopedField ∈ FieldMerge.collectFields schema parentType
            selectionSet ->
          ScopedFieldMatchesExecutableIdentity scopedField candidate ->
          ScopedFieldRuntimeApplies schema runtimeType scopedField ->
            schema.typeIncludesObjectBool scopedField.outputType.namedType
              childRuntime = true := by
    intro candidate hcandidate scopedField hscopedMem hmatch _hruntime
    have hcandidateEq : candidate = field := by
      simpa using hcandidate
    subst candidate
    have hparents :
        CollectedGroupsParent parentType
          (GraphQL.Execution.collectFields schema variableValues parentType
            (.object runtimeType ref) selectionSet) :=
      collectFields_parent schema variableValues parentType
        (.object runtimeType ref) selectionSet
    have hfieldParent : field.parentType = parentType :=
      hparents responseName (field :: fields) hgroup field (by simp)
    have hscopedParent : scopedField.parentType = parentType :=
      FreshPrefixSelectionDerivation.fieldMerge_collectFields_parent_of_allFields
        schema parentType selectionSet scopedField hall hscopedMem
    have hparent : field.parentType = scopedField.parentType :=
      hfieldParent.trans hscopedParent.symm
    have houtput :
        scopedField.outputType.namedType =
          ((schema.fieldReturnType? field.parentType field.fieldName).getD
            field.fieldName) :=
      FreshPrefixSelectionDerivation.scopedField_outputType_eq_fieldReturnType_of_identity_match
        schema variableDefinitions parentType selectionSet scopedField field
        hvalid hscopedMem hparent hmatch
    simpa [houtput] using hinclude
  rcases
      collectFields_group_prefix_mergedFieldSelectionSet_childLocalFacts_object
        schema variableDefinitions variableValues parentType parentType
        runtimeType ref selectionSet responseName childRuntime field fields
        ([] : List Execution.ExecutableField) hschema hparentRuntime hvalid
        hlookupValid himplementation hmerge hall hgroup
        (by
          intro candidate hcandidate
          cases hcandidate)
        hcompatible with
    ⟨hchildLookup, hchildImplementation, hchildMerge⟩
  exact ⟨
    by simpa [GraphQL.Execution.mergedFieldSelectionSet] using hchildLookup,
    by simpa [GraphQL.Execution.mergedFieldSelectionSet] using
      hchildImplementation,
    by
      intro objectType
      simpa [GraphQL.Execution.mergedFieldSelectionSet] using
        hchildMerge objectType⟩

theorem collectFields_generatedNormalizedFieldChild_childLocalFacts
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues)
    (childType childRuntime : Name) (ref : ObjectRef)
    (childSelectionSet : List Selection)
    (responseName grandchildRuntime : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.typeIncludesObjectBool childType childRuntime = true
      -> generatedNormalizedFieldChild schema childType childSelectionSet
      -> NormalForm.selectionSetLookupValid schema childRuntime childSelectionSet
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          childRuntime childSelectionSet
      -> (∀ objectType,
            FieldMerge.fieldsInSetCanMerge schema objectType childSelectionSet)
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues childRuntime
              (.object childRuntime ref) childSelectionSet
      -> schema.typeIncludesObjectBool
            ((schema.fieldReturnType? field.parentType field.fieldName).getD
              field.fieldName)
            grandchildRuntime
          = true
      -> NormalForm.selectionSetLookupValid schema grandchildRuntime field.selectionSet
          ∧ Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions grandchildRuntime field.selectionSet
          ∧ (∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType field.selectionSet) := by
  intro hschema hinclude hgenerated hlookupValid himplementation hmerge
    hgroup hgrandchild
  have hchildObject : schema.objectType childRuntime :=
    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
      childType childRuntime (List.contains_iff_mem.mp hinclude)
  have hparentRuntime : ScopedParentRuntimeApplies schema childRuntime childRuntime :=
    NormalForm.object_typeIncludesObjectBool_self schema hchildObject
  rcases hgenerated with ⟨sourceSelectionSet, hsourceFree, hchild⟩
  by_cases hobject : NormalForm.objectTypeNameBool schema childType = true
  · have hobjectType :
        schema.objectType childType :=
      NormalForm.objectType_of_objectTypeNameBool_eq_true schema hobject
    have hruntimeEq : childRuntime = childType :=
      object_typeIncludesObjectBool_eq_self schema hobjectType hinclude
    subst childRuntime
    have hchildEq :
        childSelectionSet =
          NormalForm.normalizeSelectionSet schema childType sourceSelectionSet := by
      simpa [hobject] using hchild
    have hall :
        NormalForm.selectionsAllFields childSelectionSet := by
      simpa [hchildEq] using
        NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
          schema childType sourceSelectionSet
    have hvalid :
        Validation.selectionSetValid schema variableDefinitions childType
          childSelectionSet :=
      NormalForm.GroundTypeNormalization.selectionSetValid_of_allFields_validInPossibleTypes
        schema variableDefinitions childType childSelectionSet hall
        himplementation
    exact
      collectFields_fieldNormal_childLocalFacts_object schema
        variableDefinitions variableValues childType childType ref
        childSelectionSet responseName grandchildRuntime field fields hschema
        hparentRuntime hvalid hlookupValid himplementation (hmerge childType)
        hall hgroup hgrandchild
  · have hfalse : NormalForm.objectTypeNameBool schema childType = false := by
      cases hmatch : NormalForm.objectTypeNameBool schema childType
      · rfl
      · contradiction
    have hchildEq :
        childSelectionSet =
          NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet := by
      simpa [hfalse] using hchild
    have hpossibleMem : childRuntime ∈ schema.getPossibleTypes childType :=
      List.contains_iff_mem.mp hinclude
    have hobjects :
        ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
          NormalForm.objectTypeNameBool schema objectType = true := by
      intro objectType hobjectType
      exact
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
          schema
          (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
            hschema childType objectType hobjectType)
    have hobjectTypes :
        ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
          schema.objectType objectType := by
      intro objectType hobjectType
      exact
        SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
          childType objectType hobjectType
    have hpossibleNodup :
        (schema.getPossibleTypes childType).Nodup :=
      SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
        childType
    have hcollect :
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
              schema (schema.getPossibleTypes childType) sourceSelectionSet)
          =
        GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) :=
      collectFields_possibleTypeNormalizations_runtime_branch schema
        variableValues childRuntime ref (schema.getPossibleTypes childType)
        sourceSelectionSet hobjects hpossibleNodup hpossibleMem
    have hgroup' :
        (responseName, field :: fields) ∈
          GraphQL.Execution.collectFields schema variableValues childRuntime
            (.object childRuntime ref)
            (NormalForm.normalizeSelectionSet schema childRuntime
              sourceSelectionSet) := by
      have hgroupPossible :
          (responseName, field :: fields) ∈
            GraphQL.Execution.collectFields schema variableValues childRuntime
              (.object childRuntime ref)
              (NormalForm.GroundTypeNormalization.possibleTypeNormalizations
                schema (schema.getPossibleTypes childType)
                sourceSelectionSet) := by
        simpa [hchildEq] using hgroup
      simpa [hcollect] using hgroupPossible
    have hlookupPossible :
        NormalForm.selectionSetLookupValid schema childRuntime
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) := by
      simpa [hchildEq] using hlookupValid
    have hlookupBranch :
        NormalForm.selectionSetLookupValid schema childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      selectionSetLookupValid_possibleTypeNormalizations_runtime_branch
        schema childRuntime (schema.getPossibleTypes childType)
        sourceSelectionSet hpossibleMem hlookupPossible
    have himplementationPossible :
        Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions childRuntime
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) := by
      simpa [hchildEq] using himplementation
    have himplementationBranch :
        Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      selectionSetValidInPossibleTypes_possibleTypeNormalizations_runtime_branch
        schema variableDefinitions childRuntime
        (schema.getPossibleTypes childType) sourceSelectionSet hobjectTypes
        hpossibleMem himplementationPossible
    have hmergePossible :
        FieldMerge.fieldsInSetCanMerge schema childRuntime
          (NormalForm.GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes childType) sourceSelectionSet) := by
      simpa [hchildEq] using hmerge childRuntime
    have hmergeBranch :
        FieldMerge.fieldsInSetCanMerge schema childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      fieldsInSetCanMerge_possibleTypeNormalizations_runtime_branch schema
        childRuntime (schema.getPossibleTypes childType) sourceSelectionSet
        hpossibleMem hmergePossible
    have hall :
        NormalForm.selectionsAllFields
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.normalizeSelectionSet_allFields
        schema childRuntime sourceSelectionSet
    have hvalid :
        Validation.selectionSetValid schema variableDefinitions childRuntime
          (NormalForm.normalizeSelectionSet schema childRuntime
            sourceSelectionSet) :=
      NormalForm.GroundTypeNormalization.selectionSetValid_of_allFields_validInPossibleTypes
        schema variableDefinitions childRuntime
        (NormalForm.normalizeSelectionSet schema childRuntime
          sourceSelectionSet) hall himplementationBranch
    exact
      collectFields_fieldNormal_childLocalFacts_object schema
        variableDefinitions variableValues childRuntime childRuntime ref
        (NormalForm.normalizeSelectionSet schema childRuntime
          sourceSelectionSet)
        responseName grandchildRuntime field fields hschema hparentRuntime
        hvalid hlookupBranch himplementationBranch hmergeBranch hall hgroup'
        hgrandchild

theorem executableFieldsFieldValidationMergeCompatible_singleton
    (field : Execution.ExecutableField)
    : ExecutableFieldsFieldValidationMergeCompatible [field] := by
  intro first later hfirst hlater _hresponse
  have hfirstEq : first = field := by
    simpa using hfirst
  have hlaterEq : later = field := by
    simpa using hlater
  subst first
  subst later
  exact ⟨rfl, NormalForm.GroundTypeNormalization.argumentsEquivalent_refl
    field.arguments⟩

theorem executableFieldsResolveStable_singleton
    (resolvers : Execution.Resolvers ObjectRef)
    (source : Execution.ResolverValue ObjectRef)
    (field : Execution.ExecutableField)
    : ExecutableFieldsResolveStable resolvers source [field] := by
  intro first later hfirst hlater _hresponse
  have hfirstEq : first = field := by
    simpa using hfirst
  have hlaterEq : later = field := by
    simpa using hlater
  subst first
  subst later
  rfl

theorem selectionDirectiveFree_of_mem {selection : Selection}
    : ∀ {selectionSet : List Selection},
        NormalForm.selectionSetDirectiveFree selectionSet
        -> selection ∈ selectionSet
        -> NormalForm.selectionDirectiveFree selection
  | [], _hfree, hmem => by
      simp at hmem
  | head :: rest, hfree, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        exact NormalForm.selectionSetDirectiveFree_head hfree
      · exact selectionDirectiveFree_of_mem
          (NormalForm.selectionSetDirectiveFree_tail hfree) htail

theorem selectionSetDirectiveFree_field_child_of_mem
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : NormalForm.selectionSetDirectiveFree selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> NormalForm.selectionSetDirectiveFree childSelectionSet := by
  intro hfree hmem
  have hselectionFree :
      NormalForm.selectionDirectiveFree
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    selectionDirectiveFree_of_mem hfree hmem
  simpa [NormalForm.selectionDirectiveFree] using hselectionFree.2

theorem selectionSetNormal_field_child_of_mem
    {schema : Schema} {parentType : Name}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : NormalForm.selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> NormalForm.selectionSetNormal schema
          ((schema.fieldReturnType? parentType fieldName).getD fieldName)
          childSelectionSet := by
  intro hnormal hmem
  rcases hnormal with ⟨hground, hnonRedundant⟩
  have hselectionGround :
      NormalForm.selectionGroundTyped schema parentType
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    by
      unfold NormalForm.selectionSetGroundTyped at hground
      exact hground.2 _ hmem
  have hselectionNonRedundant :
      NormalForm.selectionNonRedundant
        (Selection.field responseName fieldName arguments directives
          childSelectionSet) :=
    by
      unfold NormalForm.selectionSetNonRedundant at hnonRedundant
      exact hnonRedundant.2.2 _ hmem
  unfold NormalForm.selectionGroundTyped at hselectionGround
  unfold NormalForm.selectionNonRedundant at hselectionNonRedundant
  rcases hselectionGround with ⟨returnType, hreturn, hchildGround⟩
  simpa [hreturn, NormalForm.selectionSetNormal] using
    (⟨hchildGround, hselectionNonRedundant⟩ :
      NormalForm.selectionSetNormal schema returnType childSelectionSet)

theorem allFieldsNormal_responseNamesNodup
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : NormalForm.selectionSetNormal schema parentType selectionSet
      -> NormalForm.responseNamesNodup selectionSet := by
  intro hnormal
  rcases hnormal with ⟨_hground, hnonRedundant⟩
  unfold NormalForm.selectionSetNonRedundant at hnonRedundant
  exact hnonRedundant.1

theorem collectedGroupsFieldValidationMergeCompatible_of_allFieldsNormal
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.selectionSetNormal schema parentType selectionSet
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet) := by
  intro hall hfree hnormal responseName fields hgroup
  have hnodup : NormalForm.responseNamesNodup selectionSet :=
    allFieldsNormal_responseNamesNodup hnormal
  have hnonempty :
      CollectedGroupsFieldsNonempty
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) :=
    collectFields_fieldsNonempty schema variableValues parentType source
      selectionSet
  cases fields with
  | nil =>
      exact False.elim (hnonempty responseName [] hgroup rfl)
  | cons field fieldsTail =>
      have htail :
          fieldsTail = [] :=
        (FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
          schema variableValues parentType source selectionSet hall hfree
          hnodup hgroup
          (show ∀ candidate : Execution.ExecutableField,
              candidate ∈ ([] : List Execution.ExecutableField) ->
                candidate ∈ fieldsTail from
            by
              intro candidate hmem
              simp at hmem)).1
      subst fieldsTail
      exact executableFieldsFieldValidationMergeCompatible_singleton field

theorem executionCollectedFieldInvariant_of_allFieldsNormal
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.selectionSetNormal schema parentType selectionSet
      -> ExecutionCollectedFieldInvariant
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
  intro hall hfree hnormal
  have hnodup : NormalForm.responseNamesNodup selectionSet :=
    allFieldsNormal_responseNamesNodup hnormal
  constructor
  · exact PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet)
  · intro responseName fields hgroup
    have hnonempty :
        CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet) :=
      collectFields_fieldsNonempty schema variableValues parentType source
        selectionSet
    cases fields with
    | nil =>
        exact False.elim (hnonempty responseName [] hgroup rfl)
    | cons field fieldsTail =>
        have htail :
            fieldsTail = [] :=
          (FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_prefix_empty
            schema variableValues parentType source selectionSet hall hfree
            hnodup hgroup
            (show ∀ candidate : Execution.ExecutableField,
                candidate ∈ ([] : List Execution.ExecutableField) ->
                  candidate ∈ fieldsTail from
              by
                intro candidate hmem
                simp at hmem)).1
        subst fieldsTail
        exact executableFieldsResolveStable_singleton resolvers source field

theorem collectedFieldGroupLocalAppendInvariant_of_allFieldsNormal
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (childReady : Name -> List Selection -> Prop)
    (hchild
      : ∀ childDepth childType runtimeType (ref : ObjectRef) childSelectionSet,
          childDepth < depth + 1
          -> schema.typeIncludesObjectBool childType runtimeType = true
          -> childReady childType childSelectionSet
          -> NormalForm.selectionSetNormal schema childType childSelectionSet
          -> NormalForm.selectionSetDirectiveFree childSelectionSet
          -> executeRootSelectionSet schema resolvers variableValues childDepth
                runtimeType (Execution.ResolverValue.object runtimeType ref)
                childSelectionSet
              = Execution.executeRootSelectionSet schema resolvers variableValues
                  childDepth runtimeType
                  (Execution.ResolverValue.object runtimeType ref)
                  childSelectionSet)
    : NormalForm.selectionsAllFields selectionSet
      -> NormalForm.selectionSetDirectiveFree selectionSet
      -> NormalForm.selectionSetNormal schema parentType selectionSet
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> childReady
                ((schema.fieldReturnType? parentType fieldName).getD fieldName)
                childSelectionSet)
      -> CollectedFieldGroupLocalAppendInvariant schema resolvers variableValues
          depth
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet) := by
  intro hall hfree hnormal hchildren
  have hnodup : NormalForm.responseNamesNodup selectionSet :=
    allFieldsNormal_responseNamesNodup hnormal
  constructor
  intro responseName field fields prefixTail hgroup hprefix childDepth
    runtimeType identity hlt hincludes
  rcases
      FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_field_mem_prefix_empty
        schema variableValues parentType source selectionSet hall hfree
        hnodup hgroup hprefix with
    ⟨hfieldMem, hfields, hprefixTail⟩
  subst fields
  subst prefixTail
  apply stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues childDepth runtimeType (.object runtimeType identity)
    (GraphQL.Execution.mergedFieldSelectionSet (field :: []))
  rcases List.mem_map.mp hfieldMem with
    ⟨selection, hselectionMem, hfieldEq⟩
  have hselectionField : Selection.isField selection :=
    hall selection hselectionMem
  cases selection with
  | field selectionResponseName selectionFieldName selectionArguments
      selectionDirectives childSelectionSet =>
      have hfieldEq' :
          field =
            FreshPrefixSelectionDerivation.executableFieldOfSelection
              parentType
              (Selection.field selectionResponseName selectionFieldName
                selectionArguments selectionDirectives childSelectionSet) :=
        hfieldEq.symm
      subst field
      have hready :
          childReady
            ((schema.fieldReturnType? parentType selectionFieldName).getD
              selectionFieldName)
            childSelectionSet :=
        hchildren selectionResponseName selectionFieldName selectionArguments
          selectionDirectives childSelectionSet hselectionMem
      have hnormalChild :
          NormalForm.selectionSetNormal schema
            ((schema.fieldReturnType? parentType selectionFieldName).getD
              selectionFieldName)
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem hnormal hselectionMem
      have hfreeChild :
          NormalForm.selectionSetDirectiveFree childSelectionSet :=
        selectionSetDirectiveFree_field_child_of_mem hfree hselectionMem
      simpa [FreshPrefixSelectionDerivation.executableFieldOfSelection,
        GraphQL.Execution.mergedFieldSelectionSet] using
        hchild childDepth
          ((schema.fieldReturnType? parentType selectionFieldName).getD
            selectionFieldName)
          runtimeType identity childSelectionSet
          (Nat.lt_of_lt_of_le hlt (Nat.le_succ depth))
          hincludes hready hnormalChild hfreeChild
  | inlineFragment typeCondition directives childSelectionSet =>
      simp [Selection.isField] at hselectionField
  · intro responseName field fields prefixTail later hgroup hprefix hlater
      childDepth runtimeType identity hlt
    rcases
        FreshPrefixSelectionDerivation.collectFields_allFields_directiveFree_responseNamesNodup_field_mem_prefix_empty
          schema variableValues parentType source selectionSet hall hfree
          hnodup hgroup hprefix with
      ⟨_hfieldMem, hfields, _hprefixTail⟩
    subst fields
    simp at hlater
