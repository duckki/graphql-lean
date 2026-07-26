import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.SemanticSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ObjectChildLift
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Projection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ProbeTags
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DeepSuccess

/-!
Data-separation witnesses for syntactic normal-form differences.

This module assembles the existing probe resolvers, deep-success readiness, and
semantic-separation lemmas into the second half of the uniqueness implication:
normal syntactic differences can be observed semantically.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem not_selectionSetsDataEquivalent_of_responseData_counterexample
    {ObjectRef : Type} {schema : Schema} {parentType : Name}
    {left right : List Selection}
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (source : Execution.ResolverValue ObjectRef)
    : (∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel parentType source left).data
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel parentType source right).data
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hsource hnot hdata
  exact hnot (hdata resolvers variableValues fuel source hsource)

theorem abstractRuntimeForFieldDeep?_framed_promote_some_of_include
    {schema : Schema}
    {rootParent targetParent targetField runtimeType : Name}
    {selectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : abstractRuntimeForFieldDeep? schema targetParent targetField rootParent selectionSet
        = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true
      -> ∃ framedRuntimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
              targetParent
              [Selection.inlineFragment (some rootParent) [] selectionSet]
            = some framedRuntimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType framedRuntimeType
            = true := by
  intro hruntime hinclude
  exact
    ⟨runtimeType,
      by simp [abstractRuntimeForFieldDeep?, hruntime],
      hinclude⟩

theorem abstractRuntimeForFieldDeep?_append_some_left_exists
    {schema : Schema}
    {targetParent targetField currentParent runtimeType : Name}
    {left right : List Selection}
    : abstractRuntimeForFieldDeep? schema targetParent targetField currentParent left
        = some runtimeType
      -> ∃ appendedRuntimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            currentParent (left ++ right)
          = some appendedRuntimeType := by
  intro hleft
  induction left generalizing currentParent runtimeType with
  | nil =>
      simp [abstractRuntimeForFieldDeep?] at hleft
  | cons head tail ih =>
      cases head with
      | field responseName fieldName arguments directives childSelectionSet =>
          cases hmatch :
              (currentParent == targetParent && fieldName == targetField)
          · cases hrest :
                abstractRuntimeForFieldDeep? schema targetParent targetField
                  currentParent tail with
            | none =>
                cases hlookup : schema.lookupField currentParent fieldName with
                | none =>
                    simp [abstractRuntimeForFieldDeep?, hmatch, hrest,
                      hlookup] at hleft
                | some fieldDefinition =>
                    have hchild :
                        abstractRuntimeForFieldDeep? schema targetParent
                          targetField fieldDefinition.outputType.namedType
                          childSelectionSet = some runtimeType := by
                      simpa [abstractRuntimeForFieldDeep?, hmatch, hrest,
                        hlookup] using hleft
                    cases happendedRest :
                        abstractRuntimeForFieldDeep? schema targetParent
                          targetField currentParent (tail ++ right) with
                    | none =>
                        exact
                          ⟨runtimeType,
                            by
                              simp [abstractRuntimeForFieldDeep?, hmatch,
                                happendedRest, hlookup, hchild]⟩
                    | some appendedRuntimeType =>
                        exact
                          ⟨appendedRuntimeType,
                            by
                              simp [abstractRuntimeForFieldDeep?, hmatch,
                                happendedRest]⟩
            | some restRuntimeType =>
                rcases ih hrest with ⟨tailRuntimeType, htailRuntime⟩
                exact
                  ⟨tailRuntimeType,
                    by
                      simp [abstractRuntimeForFieldDeep?, hmatch,
                        htailRuntime]⟩
          · cases hfirst :
                firstInlineFragmentTypeCondition? childSelectionSet with
            | none =>
                cases hrest :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField currentParent tail with
                | none =>
                    cases hlookup :
                        schema.lookupField currentParent fieldName with
                    | none =>
                        simp [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                          hrest, hlookup] at hleft
                    | some fieldDefinition =>
                        have hchild :
                            abstractRuntimeForFieldDeep? schema targetParent
                              targetField
                              fieldDefinition.outputType.namedType
                              childSelectionSet = some runtimeType := by
                          simpa [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                            hrest, hlookup] using hleft
                        cases happendedRest :
                            abstractRuntimeForFieldDeep? schema targetParent
                              targetField currentParent (tail ++ right) with
                        | none =>
                            exact
                              ⟨runtimeType,
                                by
                                  simp [abstractRuntimeForFieldDeep?, hmatch,
                                    hfirst, happendedRest, hlookup, hchild]⟩
                        | some appendedRuntimeType =>
                            exact
                              ⟨appendedRuntimeType,
                                by
                                  simp [abstractRuntimeForFieldDeep?, hmatch,
                                    hfirst, happendedRest]⟩
                | some restRuntimeType =>
                    rcases ih hrest with ⟨tailRuntimeType, htailRuntime⟩
                    exact
                      ⟨tailRuntimeType,
                        by
                          simp [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                            htailRuntime]⟩
            | some firstRuntimeType =>
                exact
                  ⟨firstRuntimeType,
                    by
                      simp [abstractRuntimeForFieldDeep?, hmatch, hfirst]⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          cases hrest :
              abstractRuntimeForFieldDeep? schema targetParent targetField
                currentParent tail
          · cases typeCondition with
            | none =>
                have hchild :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField currentParent childSelectionSet =
                        some runtimeType := by
                  simpa [abstractRuntimeForFieldDeep?, hrest] using hleft
                cases happendedRest :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField currentParent (tail ++ right) with
                | none =>
                    exact
                      ⟨runtimeType,
                        by
                          simp [abstractRuntimeForFieldDeep?, happendedRest,
                            hchild]⟩
                | some appendedRuntimeType =>
                    exact
                      ⟨appendedRuntimeType,
                        by
                          simp [abstractRuntimeForFieldDeep?,
                            happendedRest]⟩
            | some typeCondition =>
                have hchild :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField typeCondition childSelectionSet =
                        some runtimeType := by
                  simpa [abstractRuntimeForFieldDeep?, hrest] using hleft
                cases happendedRest :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField currentParent (tail ++ right) with
                | none =>
                    exact
                      ⟨runtimeType,
                        by
                          simp [abstractRuntimeForFieldDeep?, happendedRest,
                            hchild]⟩
                | some appendedRuntimeType =>
                    exact
                      ⟨appendedRuntimeType,
                        by
                          simp [abstractRuntimeForFieldDeep?,
                            happendedRest]⟩
          · rcases ih hrest with ⟨tailRuntimeType, htailRuntime⟩
            exact
              ⟨tailRuntimeType,
                by
                  cases typeCondition <;>
                    simp [abstractRuntimeForFieldDeep?, htailRuntime]⟩

theorem abstractRuntimeForFieldDeep?_append_some_right_exists
    {schema : Schema}
    {targetParent targetField currentParent runtimeType : Name}
    {left right : List Selection}
    : abstractRuntimeForFieldDeep? schema targetParent targetField currentParent right
        = some runtimeType
      -> ∃ appendedRuntimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            currentParent (left ++ right)
          = some appendedRuntimeType := by
  intro hright
  induction left generalizing currentParent with
  | nil =>
      exact ⟨runtimeType, by simpa using hright⟩
  | cons head tail ih =>
      cases head with
      | field responseName fieldName arguments directives childSelectionSet =>
          cases hmatch :
              (currentParent == targetParent && fieldName == targetField)
          · rcases ih hright (currentParent := currentParent) with
              ⟨tailRuntimeType, htailRuntime⟩
            exact
              ⟨tailRuntimeType,
                by
                  simp [abstractRuntimeForFieldDeep?, hmatch,
                    htailRuntime]⟩
          · cases hfirst :
                firstInlineFragmentTypeCondition? childSelectionSet with
            | some firstRuntimeType =>
                exact
                  ⟨firstRuntimeType,
                    by
                      simp [abstractRuntimeForFieldDeep?, hmatch, hfirst]⟩
            | none =>
                rcases ih hright (currentParent := currentParent) with
                  ⟨tailRuntimeType, htailRuntime⟩
                exact
                  ⟨tailRuntimeType,
                    by
                      simp [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                        htailRuntime]⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          rcases ih hright (currentParent := currentParent) with
            ⟨tailRuntimeType, htailRuntime⟩
          exact
            ⟨tailRuntimeType,
              by
                cases typeCondition <;>
                  simp [abstractRuntimeForFieldDeep?, htailRuntime]⟩

theorem abstractRuntimeForFieldHeadDeep?_framed_promote_some_of_include
    {schema : Schema}
    {rootParent targetParent targetField runtimeType : Name}
    {targetArguments : List Argument}
    {selectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments rootParent selectionSet
        = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true
      -> ∃ framedRuntimeType,
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
              targetArguments targetParent
              [Selection.inlineFragment (some rootParent) [] selectionSet]
            = some framedRuntimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType framedRuntimeType
            = true := by
  intro hruntime hinclude
  exact
    ⟨runtimeType,
      by simp [abstractRuntimeForFieldHeadDeep?, hruntime],
      hinclude⟩

theorem abstractRuntimeForFieldHeadDeep?_append_some_left_exists
    {schema : Schema}
    {targetParent targetField currentParent runtimeType : Name}
    {targetArguments : List Argument}
    {left right : List Selection}
    : abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments currentParent left
        = some runtimeType
      -> ∃ appendedRuntimeType,
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent (left ++ right)
          = some appendedRuntimeType := by
  intro hleft
  induction left generalizing currentParent runtimeType with
  | nil =>
      simp [abstractRuntimeForFieldHeadDeep?] at hleft
  | cons head tail ih =>
      classical
      cases head with
      | field responseName fieldName arguments directives childSelectionSet =>
          cases hcurrent :
              (if currentParent = targetParent
                  ∧ fieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments targetArguments then
                firstInlineFragmentTypeCondition? childSelectionSet
              else
                none) with
          | some currentRuntimeType =>
              exact
                ⟨currentRuntimeType,
                  by
                    simp [abstractRuntimeForFieldHeadDeep?, hcurrent]⟩
          | none =>
              cases hrest :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments currentParent tail with
              | some restRuntimeType =>
                  rcases ih hrest with ⟨tailRuntimeType, htailRuntime⟩
                  exact
                    ⟨tailRuntimeType,
                      by
                        simp [abstractRuntimeForFieldHeadDeep?, hcurrent,
                          htailRuntime]⟩
              | none =>
                  cases hlookup : schema.lookupField currentParent fieldName with
                  | none =>
                      simp [abstractRuntimeForFieldHeadDeep?, hcurrent,
                        hrest, hlookup] at hleft
                  | some fieldDefinition =>
                      have hchild :
                          abstractRuntimeForFieldHeadDeep? schema
                            targetParent targetField targetArguments
                            fieldDefinition.outputType.namedType
                            childSelectionSet = some runtimeType := by
                        simpa [abstractRuntimeForFieldHeadDeep?, hcurrent,
                          hrest, hlookup] using hleft
                      cases happendedRest :
                          abstractRuntimeForFieldHeadDeep? schema
                            targetParent targetField targetArguments
                            currentParent (tail ++ right) with
                      | none =>
                          exact
                            ⟨runtimeType,
                              by
                                simp [abstractRuntimeForFieldHeadDeep?,
                                  hcurrent, happendedRest, hlookup,
                                  hchild]⟩
                      | some appendedRuntimeType =>
                          exact
                            ⟨appendedRuntimeType,
                              by
                                simp [abstractRuntimeForFieldHeadDeep?,
                                  hcurrent, happendedRest]⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          cases hrest :
              abstractRuntimeForFieldHeadDeep? schema targetParent targetField
                targetArguments currentParent tail
          · cases typeCondition with
            | none =>
                have hchild :
                    abstractRuntimeForFieldHeadDeep? schema targetParent
                      targetField targetArguments currentParent
                      childSelectionSet = some runtimeType := by
                  simpa [abstractRuntimeForFieldHeadDeep?, hrest] using hleft
                cases happendedRest :
                    abstractRuntimeForFieldHeadDeep? schema targetParent
                      targetField targetArguments currentParent
                      (tail ++ right) with
                | none =>
                    exact
                      ⟨runtimeType,
                        by
                          simp [abstractRuntimeForFieldHeadDeep?,
                            happendedRest, hchild]⟩
                | some appendedRuntimeType =>
                    exact
                      ⟨appendedRuntimeType,
                        by
                          simp [abstractRuntimeForFieldHeadDeep?,
                            happendedRest]⟩
            | some typeCondition =>
                have hchild :
                    abstractRuntimeForFieldHeadDeep? schema targetParent
                      targetField targetArguments typeCondition
                      childSelectionSet = some runtimeType := by
                  simpa [abstractRuntimeForFieldHeadDeep?, hrest] using hleft
                cases happendedRest :
                    abstractRuntimeForFieldHeadDeep? schema targetParent
                      targetField targetArguments currentParent
                      (tail ++ right) with
                | none =>
                    exact
                      ⟨runtimeType,
                        by
                          simp [abstractRuntimeForFieldHeadDeep?,
                            happendedRest, hchild]⟩
                | some appendedRuntimeType =>
                    exact
                      ⟨appendedRuntimeType,
                        by
                          simp [abstractRuntimeForFieldHeadDeep?,
                            happendedRest]⟩
          · rcases ih hrest with ⟨tailRuntimeType, htailRuntime⟩
            exact
              ⟨tailRuntimeType,
                by
                  cases typeCondition <;>
                    simp [abstractRuntimeForFieldHeadDeep?, htailRuntime]⟩

theorem abstractRuntimeForFieldHeadDeep?_append_some_right_exists
    {schema : Schema}
    {targetParent targetField currentParent runtimeType : Name}
    {targetArguments : List Argument}
    {left right : List Selection}
    : abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments currentParent right
        = some runtimeType
      -> ∃ appendedRuntimeType,
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent (left ++ right)
          = some appendedRuntimeType := by
  intro hright
  induction left generalizing currentParent with
  | nil =>
      exact ⟨runtimeType, by simpa using hright⟩
  | cons head tail ih =>
      classical
      cases head with
      | field responseName fieldName arguments directives childSelectionSet =>
          cases hcurrent :
              (if currentParent = targetParent
                  ∧ fieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments targetArguments then
                firstInlineFragmentTypeCondition? childSelectionSet
              else
                none) with
          | some currentRuntimeType =>
              exact
                ⟨currentRuntimeType,
                  by
                    simp [abstractRuntimeForFieldHeadDeep?, hcurrent]⟩
          | none =>
              rcases ih hright (currentParent := currentParent) with
                ⟨tailRuntimeType, htailRuntime⟩
              exact
                ⟨tailRuntimeType,
                  by
                    simp [abstractRuntimeForFieldHeadDeep?, hcurrent,
                      htailRuntime]⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          rcases ih hright (currentParent := currentParent) with
            ⟨tailRuntimeType, htailRuntime⟩
          exact
            ⟨tailRuntimeType,
              by
                cases typeCondition <;>
                  simp [abstractRuntimeForFieldHeadDeep?, htailRuntime]⟩

theorem abstractRuntimeForFieldHeadDeep?_append_some_include_of_valid_normal_or_right
    {schema : Schema}
    {leftVariableDefinitions : List VariableDefinition}
    {currentParent targetParent targetField runtimeType : Name}
    {targetArguments : List Argument}
    {left right : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions currentParent left
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema currentParent left
      -> (∀ rightRuntimeType,
            abstractRuntimeForFieldHeadDeep? schema targetParent targetField
                targetArguments currentParent right
              = some rightRuntimeType
            -> schema.typeIncludesObjectBool
                  targetFieldDefinition.outputType.namedType rightRuntimeType
                = true)
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent (left ++ right)
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hleftValid hleftFree hleftNormal hrightInclude htargetLookup
    htargetComposite htargetNonObject happendedRuntime
  induction left generalizing currentParent runtimeType with
  | nil =>
      exact hrightInclude runtimeType (by
        simpa [abstractRuntimeForFieldHeadDeep?] using happendedRuntime)
  | cons head tail ih =>
      classical
      cases head with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hheadMem :
              Selection.field responseName fieldName arguments directives
                  childSelectionSet ∈
                Selection.field responseName fieldName arguments directives
                  childSelectionSet :: tail := by
            simp
          cases hcurrent :
              (if currentParent = targetParent
                  ∧ fieldName = targetField
                  ∧ Argument.argumentsEquivalent arguments targetArguments then
                firstInlineFragmentTypeCondition? childSelectionSet
              else
                none) with
          | some headRuntimeType =>
              by_cases hcondition :
                  currentParent = targetParent
                    ∧ fieldName = targetField
                    ∧ Argument.argumentsEquivalent arguments targetArguments
              · have hfirst :
                    firstInlineFragmentTypeCondition? childSelectionSet =
                      some headRuntimeType := by
                  simpa [hcondition] using hcurrent
                have hheadLookup :
                    schema.lookupField currentParent fieldName =
                      some targetFieldDefinition := by
                  simpa [hcondition.1, hcondition.2.1] using htargetLookup
                rcases
                    firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                      hleftValid hleftNormal hheadMem hheadLookup
                      htargetComposite htargetNonObject with
                  ⟨candidateRuntimeType, hcandidateRuntime,
                    hcandidateInclude⟩
                have hcandidateEq :
                    candidateRuntimeType = headRuntimeType := by
                  rw [hfirst] at hcandidateRuntime
                  exact (Option.some.inj hcandidateRuntime).symm
                have hruntimeEq : headRuntimeType = runtimeType := by
                  simpa [abstractRuntimeForFieldHeadDeep?, hcondition,
                    hfirst] using happendedRuntime
                subst candidateRuntimeType
                subst runtimeType
                exact hcandidateInclude
              · simp [hcondition] at hcurrent
          | none =>
              cases hrestAppend :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments currentParent
                    (tail ++ right) with
              | some restRuntimeType =>
                  have hruntimeEq : restRuntimeType = runtimeType := by
                    simpa [abstractRuntimeForFieldHeadDeep?, hcurrent,
                      hrestAppend] using happendedRuntime
                  subst runtimeType
                  exact
                    ih (Validation.selectionSetValid_tail hleftValid)
                      (selectionSetDirectiveFree_tail hleftFree)
                      (selectionSetNormal_tail hleftNormal) hrightInclude
                      hrestAppend
              | none =>
                  cases hlookup : schema.lookupField currentParent fieldName with
                  | none =>
                      simp [abstractRuntimeForFieldHeadDeep?, hcurrent,
                        hrestAppend, hlookup] at happendedRuntime
                  | some fieldDefinition =>
                      have hchildRuntime :
                          abstractRuntimeForFieldHeadDeep? schema
                            targetParent targetField targetArguments
                            fieldDefinition.outputType.namedType
                            childSelectionSet = some runtimeType := by
                        simpa [abstractRuntimeForFieldHeadDeep?, hcurrent,
                          hrestAppend, hlookup] using happendedRuntime
                      have hchildNonempty : childSelectionSet ≠ [] := by
                        intro hnil
                        simp [hnil, abstractRuntimeForFieldHeadDeep?] at hchildRuntime
                      have hchildValid :
                          Validation.selectionSetValid schema
                            leftVariableDefinitions
                            fieldDefinition.outputType.namedType
                            childSelectionSet :=
                        selectionSetValid_field_child_of_mem_lookup hleftValid
                          hheadMem hchildNonempty hlookup
                      have hchildFree :
                          selectionSetDirectiveFree childSelectionSet :=
                        selectionSetDirectiveFree_field_child_of_mem hleftFree
                          hheadMem
                      have hchildNormal :
                          selectionSetNormal schema
                            fieldDefinition.outputType.namedType
                            childSelectionSet :=
                        selectionSetNormal_field_child_of_mem_lookup
                          hleftNormal hheadMem hlookup
                      exact
                        abstractRuntimeForFieldHeadDeep?_some_include_of_valid_normal
                          hchildValid hchildFree hchildNormal htargetLookup
                          htargetComposite htargetNonObject hchildRuntime
      | inlineFragment typeCondition directives childSelectionSet =>
          cases typeCondition with
          | none =>
              have hheadMem :
                  Selection.inlineFragment none directives childSelectionSet ∈
                    Selection.inlineFragment none directives
                      childSelectionSet :: tail := by
                simp
              have hground :
                  selectionGroundTyped schema currentParent
                    (Selection.inlineFragment none directives
                      childSelectionSet) := by
                have hsetGround :
                    selectionSetGroundTyped schema currentParent
                      (Selection.inlineFragment none directives
                        childSelectionSet :: tail) :=
                  hleftNormal.1
                unfold selectionSetGroundTyped at hsetGround
                exact hsetGround.2 _ hheadMem
              simp [selectionGroundTyped] at hground
          | some typeCondition =>
              have hheadMem :
                  Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet ∈
                    Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet :: tail := by
                simp
              cases hrestAppend :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments currentParent
                    (tail ++ right) with
              | some restRuntimeType =>
                  have hruntimeEq : restRuntimeType = runtimeType := by
                    simpa [abstractRuntimeForFieldHeadDeep?, hrestAppend]
                      using happendedRuntime
                  subst runtimeType
                  exact
                    ih (Validation.selectionSetValid_tail hleftValid)
                      (selectionSetDirectiveFree_tail hleftFree)
                      (selectionSetNormal_tail hleftNormal) hrightInclude
                      hrestAppend
              | none =>
                  have hchildRuntime :
                      abstractRuntimeForFieldHeadDeep? schema targetParent
                        targetField targetArguments typeCondition
                        childSelectionSet = some runtimeType := by
                    simpa [abstractRuntimeForFieldHeadDeep?, hrestAppend]
                      using happendedRuntime
                  have hchildValid :
                      Validation.selectionSetValid schema
                        leftVariableDefinitions typeCondition
                        childSelectionSet :=
                    selectionSetValid_inlineFragment_some_child_of_mem
                      hleftValid hheadMem
                  have hchildFree :
                      selectionSetDirectiveFree childSelectionSet :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hleftFree hheadMem
                  have hchildNormal :
                      selectionSetNormal schema typeCondition
                        childSelectionSet :=
                    (selectionSetNormal_inlineFragment_child_of_mem
                      hleftNormal hheadMem).2
                  exact
                    abstractRuntimeForFieldHeadDeep?_some_include_of_valid_normal
                      hchildValid hchildFree hchildNormal htargetLookup
                      htargetComposite htargetNonObject hchildRuntime

theorem abstractRuntimeForFieldHeadDeep?_join_some_include_of_valid_normal_members
    {schema : Schema}
    {currentParent targetParent targetField runtimeType : Name}
    {targetArguments : List Argument}
    {members : List (List Selection)}
    {targetFieldDefinition : FieldDefinition}
    : (∀ selectionSet,
        selectionSet ∈ members
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions
              currentParent selectionSet
            ∧ selectionSetDirectiveFree selectionSet
            ∧ selectionSetNormal schema currentParent selectionSet)
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent (List.flatten members)
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hmembers htargetLookup htargetComposite htargetNonObject hruntime
  induction members generalizing runtimeType with
  | nil =>
      simp [abstractRuntimeForFieldHeadDeep?] at hruntime
  | cons selectionSet rest ih =>
      rcases hmembers selectionSet (by simp) with
        ⟨variableDefinitions, hvalid, hfree, hnormal⟩
      have hrestMembers :
          ∀ restSelectionSet,
            restSelectionSet ∈ rest ->
              ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions
                  currentParent restSelectionSet
                ∧ selectionSetDirectiveFree restSelectionSet
                ∧ selectionSetNormal schema currentParent restSelectionSet := by
        intro restSelectionSet hmem
        exact hmembers restSelectionSet
          (List.mem_cons_of_mem selectionSet hmem)
      exact
        abstractRuntimeForFieldHeadDeep?_append_some_include_of_valid_normal_or_right
          (schema := schema)
          (leftVariableDefinitions := variableDefinitions)
          (currentParent := currentParent)
          (targetParent := targetParent) (targetField := targetField)
          (targetArguments := targetArguments)
          (runtimeType := runtimeType) (left := selectionSet)
          (right := List.flatten rest)
          (targetFieldDefinition := targetFieldDefinition)
          hvalid hfree hnormal
          (by
            intro rightRuntimeType hrightRuntime
            exact ih hrestMembers hrightRuntime)
          htargetLookup htargetComposite htargetNonObject
          (by simpa [List.flatten_cons] using hruntime)

theorem abstractRuntimeForFieldHeadDeep?_member_framed_promote_some_of_valid_normal_members
    {schema : Schema} {currentParent targetParent targetField targetRuntimeType : Name}
    {targetArguments : List Argument} {selectionSet : List Selection}
    {members : List (List Selection)} {targetFieldDefinition : FieldDefinition}
    : (∀ memberSelectionSet,
        memberSelectionSet ∈ members
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions
              currentParent memberSelectionSet
            ∧ selectionSetDirectiveFree memberSelectionSet
            ∧ selectionSetNormal schema currentParent memberSelectionSet)
      -> selectionSet ∈ members
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent selectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldHeadDeep? schema targetParent targetField
              targetArguments targetParent
              [Selection.inlineFragment (some currentParent) [] (List.flatten members)]
            = some runtimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hmembers hmem htargetLookup htargetComposite htargetNonObject
    hlocalRuntime
  have hconcatRuntimeExists :
      ∃ concatRuntimeType,
        abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments currentParent (List.flatten members) =
            some concatRuntimeType := by
    induction members with
    | nil =>
        simp at hmem
    | cons head rest ih =>
        simp at hmem
        rcases hmem with hhead | htail
        · subst selectionSet
          exact
            abstractRuntimeForFieldHeadDeep?_append_some_left_exists
              (schema := schema) (targetParent := targetParent)
              (targetField := targetField)
              (targetArguments := targetArguments)
              (currentParent := currentParent)
              (left := head) (right := List.flatten rest)
              hlocalRuntime
        · have hrestMembers :
              ∀ memberSelectionSet,
                memberSelectionSet ∈ rest ->
                  ∃ variableDefinitions,
                    Validation.selectionSetValid schema variableDefinitions
                      currentParent memberSelectionSet
                    ∧ selectionSetDirectiveFree memberSelectionSet
                    ∧ selectionSetNormal schema currentParent
                      memberSelectionSet := by
            intro memberSelectionSet hmember
            exact hmembers memberSelectionSet
              (List.mem_cons_of_mem head hmember)
          rcases ih hrestMembers htail with
            ⟨restRuntimeType, hrestRuntime⟩
          exact
            abstractRuntimeForFieldHeadDeep?_append_some_right_exists
              (schema := schema) (targetParent := targetParent)
              (targetField := targetField)
              (targetArguments := targetArguments)
              (currentParent := currentParent)
              (left := head) (right := List.flatten rest)
              hrestRuntime
  rcases hconcatRuntimeExists with
    ⟨concatRuntimeType, hconcatRuntime⟩
  have hinclude :
      schema.typeIncludesObjectBool
        targetFieldDefinition.outputType.namedType concatRuntimeType = true :=
    abstractRuntimeForFieldHeadDeep?_join_some_include_of_valid_normal_members
      (schema := schema) (currentParent := currentParent)
      (targetParent := targetParent) (targetField := targetField)
      (targetArguments := targetArguments)
      (runtimeType := concatRuntimeType) (members := members)
      (targetFieldDefinition := targetFieldDefinition)
      hmembers htargetLookup htargetComposite htargetNonObject
      hconcatRuntime
  exact
    abstractRuntimeForFieldHeadDeep?_framed_promote_some_of_include
      hconcatRuntime hinclude

theorem abstractRuntimeForFieldDeep?_append_some_include_of_valid_normal
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {currentParent targetParent targetField runtimeType : Name}
    {left right : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions currentParent left
      -> Validation.selectionSetValid schema rightVariableDefinitions currentParent right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema currentParent left
      -> selectionSetNormal schema currentParent right
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField
            currentParent (left ++ right)
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal
    htargetLookup htargetComposite htargetNonObject happendedRuntime
  induction left generalizing currentParent runtimeType with
  | nil =>
      exact
        abstractRuntimeForFieldDeep?_some_include_of_valid_normal
          hrightValid hrightFree hrightNormal htargetLookup
          htargetComposite htargetNonObject (by
            simpa [abstractRuntimeForFieldDeep?] using happendedRuntime)
  | cons head tail ih =>
      cases head with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hheadMem :
              Selection.field responseName fieldName arguments directives
                  childSelectionSet ∈
                Selection.field responseName fieldName arguments directives
                  childSelectionSet :: tail := by
            simp
          cases hmatch :
              (currentParent == targetParent && fieldName == targetField)
          · cases hrestAppend :
                abstractRuntimeForFieldDeep? schema targetParent targetField
                  currentParent (tail ++ right) with
            | some restRuntimeType =>
                have hruntimeEq : restRuntimeType = runtimeType := by
                  simpa [abstractRuntimeForFieldDeep?, hmatch, hrestAppend]
                    using happendedRuntime
                subst runtimeType
                exact
                  ih (Validation.selectionSetValid_tail hleftValid)
                    hrightValid (selectionSetDirectiveFree_tail hleftFree)
                    (selectionSetNormal_tail hleftNormal) hrightNormal
                    hrestAppend
            | none =>
                cases hlookup : schema.lookupField currentParent fieldName with
                | none =>
                    simp [abstractRuntimeForFieldDeep?, hmatch, hrestAppend,
                      hlookup] at happendedRuntime
                | some fieldDefinition =>
                    have hchildRuntime :
                        abstractRuntimeForFieldDeep? schema targetParent
                          targetField fieldDefinition.outputType.namedType
                          childSelectionSet = some runtimeType := by
                      simpa [abstractRuntimeForFieldDeep?, hmatch,
                        hrestAppend, hlookup] using happendedRuntime
                    have hchildNonempty : childSelectionSet ≠ [] := by
                      intro hnil
                      simp [hnil, abstractRuntimeForFieldDeep?] at hchildRuntime
                    have hchildValid :
                        Validation.selectionSetValid schema
                          leftVariableDefinitions
                          fieldDefinition.outputType.namedType
                          childSelectionSet :=
                      selectionSetValid_field_child_of_mem_lookup hleftValid
                        hheadMem hchildNonempty hlookup
                    have hchildFree :
                        selectionSetDirectiveFree childSelectionSet :=
                      selectionSetDirectiveFree_field_child_of_mem hleftFree
                        hheadMem
                    have hchildNormal :
                        selectionSetNormal schema
                          fieldDefinition.outputType.namedType
                          childSelectionSet :=
                      selectionSetNormal_field_child_of_mem_lookup
                        hleftNormal hheadMem hlookup
                    exact
                      abstractRuntimeForFieldDeep?_some_include_of_valid_normal
                        hchildValid hchildFree hchildNormal htargetLookup
                        htargetComposite htargetNonObject hchildRuntime
          · cases hfirst :
                firstInlineFragmentTypeCondition? childSelectionSet with
            | some headRuntimeType =>
                have hparts :
                    currentParent = targetParent ∧ fieldName = targetField := by
                  simpa using hmatch
                have hheadLookup :
                    schema.lookupField currentParent fieldName =
                      some targetFieldDefinition := by
                  simpa [hparts.1, hparts.2] using htargetLookup
                rcases
                    firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                      hleftValid hleftNormal hheadMem hheadLookup
                      htargetComposite htargetNonObject with
                  ⟨candidateRuntimeType, hcandidateRuntime,
                    hcandidateInclude⟩
                have hcandidateEq :
                    candidateRuntimeType = headRuntimeType := by
                  rw [hfirst] at hcandidateRuntime
                  exact (Option.some.inj hcandidateRuntime).symm
                have hruntimeEq : headRuntimeType = runtimeType := by
                  simpa [abstractRuntimeForFieldDeep?, hmatch, hfirst]
                    using happendedRuntime
                subst candidateRuntimeType
                subst runtimeType
                exact hcandidateInclude
            | none =>
                cases hrestAppend :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField currentParent (tail ++ right) with
                | some restRuntimeType =>
                    have hruntimeEq : restRuntimeType = runtimeType := by
                      simpa [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                        hrestAppend] using happendedRuntime
                    subst runtimeType
                    exact
                      ih (Validation.selectionSetValid_tail hleftValid)
                        hrightValid (selectionSetDirectiveFree_tail hleftFree)
                        (selectionSetNormal_tail hleftNormal) hrightNormal
                        hrestAppend
                | none =>
                    cases hlookup :
                        schema.lookupField currentParent fieldName with
                    | none =>
                        simp [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                          hrestAppend, hlookup] at happendedRuntime
                    | some fieldDefinition =>
                        have hchildRuntime :
                            abstractRuntimeForFieldDeep? schema targetParent
                              targetField
                              fieldDefinition.outputType.namedType
                              childSelectionSet = some runtimeType := by
                          simpa [abstractRuntimeForFieldDeep?, hmatch,
                            hfirst, hrestAppend, hlookup] using
                            happendedRuntime
                        have hchildNonempty : childSelectionSet ≠ [] := by
                          intro hnil
                          simp [hnil, abstractRuntimeForFieldDeep?] at hchildRuntime
                        have hchildValid :
                            Validation.selectionSetValid schema
                              leftVariableDefinitions
                              fieldDefinition.outputType.namedType
                              childSelectionSet :=
                          selectionSetValid_field_child_of_mem_lookup
                            hleftValid hheadMem hchildNonempty hlookup
                        have hchildFree :
                            selectionSetDirectiveFree childSelectionSet :=
                          selectionSetDirectiveFree_field_child_of_mem
                            hleftFree hheadMem
                        have hchildNormal :
                            selectionSetNormal schema
                              fieldDefinition.outputType.namedType
                              childSelectionSet :=
                          selectionSetNormal_field_child_of_mem_lookup
                            hleftNormal hheadMem hlookup
                        exact
                          abstractRuntimeForFieldDeep?_some_include_of_valid_normal
                            hchildValid hchildFree hchildNormal
                            htargetLookup htargetComposite
                            htargetNonObject hchildRuntime
      | inlineFragment typeCondition directives childSelectionSet =>
          cases typeCondition with
          | none =>
              have hheadMem :
                  Selection.inlineFragment none directives childSelectionSet ∈
                    Selection.inlineFragment none directives
                      childSelectionSet :: tail := by
                simp
              have hground :
                  selectionGroundTyped schema currentParent
                    (Selection.inlineFragment none directives
                      childSelectionSet) := by
                have hsetGround :
                    selectionSetGroundTyped schema currentParent
                      (Selection.inlineFragment none directives
                        childSelectionSet :: tail) :=
                  hleftNormal.1
                unfold selectionSetGroundTyped at hsetGround
                exact hsetGround.2 _ hheadMem
              simp [selectionGroundTyped] at hground
          | some typeCondition =>
              have hheadMem :
                  Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet ∈
                    Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet :: tail := by
                simp
              cases hrestAppend :
                  abstractRuntimeForFieldDeep? schema targetParent targetField
                    currentParent (tail ++ right) with
              | some restRuntimeType =>
                  have hruntimeEq : restRuntimeType = runtimeType := by
                    simpa [abstractRuntimeForFieldDeep?, hrestAppend] using
                      happendedRuntime
                  subst runtimeType
                  exact
                    ih (Validation.selectionSetValid_tail hleftValid)
                      hrightValid (selectionSetDirectiveFree_tail hleftFree)
                      (selectionSetNormal_tail hleftNormal) hrightNormal
                      hrestAppend
              | none =>
                  have hchildRuntime :
                      abstractRuntimeForFieldDeep? schema targetParent
                        targetField typeCondition childSelectionSet =
                          some runtimeType := by
                    simpa [abstractRuntimeForFieldDeep?, hrestAppend] using
                      happendedRuntime
                  have hchildNonempty : childSelectionSet ≠ [] := by
                    intro hnil
                    simp [hnil, abstractRuntimeForFieldDeep?] at hchildRuntime
                  have hchildValid :
                      Validation.selectionSetValid schema
                        leftVariableDefinitions typeCondition
                        childSelectionSet :=
                    selectionSetValid_inlineFragment_some_child_of_mem
                      hleftValid hheadMem
                  have hchildFree :
                      selectionSetDirectiveFree childSelectionSet :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hleftFree hheadMem
                  have hchildNormal :
                      selectionSetNormal schema typeCondition
                        childSelectionSet :=
                    (selectionSetNormal_inlineFragment_child_of_mem
                      hleftNormal hheadMem).2
                  exact
                    abstractRuntimeForFieldDeep?_some_include_of_valid_normal
                      hchildValid hchildFree hchildNormal htargetLookup
                      htargetComposite htargetNonObject hchildRuntime

theorem abstractRuntimeForFieldDeep?_append_some_include_of_valid_normal_or_right
    {schema : Schema}
    {leftVariableDefinitions : List VariableDefinition}
    {currentParent targetParent targetField runtimeType : Name}
    {left right : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions currentParent left
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema currentParent left
      -> (∀ rightRuntimeType,
            abstractRuntimeForFieldDeep? schema targetParent targetField
                currentParent right
              = some rightRuntimeType
            -> schema.typeIncludesObjectBool
                  targetFieldDefinition.outputType.namedType rightRuntimeType
                = true)
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField
            currentParent (left ++ right)
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hleftValid hleftFree hleftNormal hrightInclude htargetLookup
    htargetComposite htargetNonObject happendedRuntime
  induction left generalizing currentParent runtimeType with
  | nil =>
      exact hrightInclude runtimeType (by
        simpa [abstractRuntimeForFieldDeep?] using happendedRuntime)
  | cons head tail ih =>
      cases head with
      | field responseName fieldName arguments directives childSelectionSet =>
          have hheadMem :
              Selection.field responseName fieldName arguments directives
                  childSelectionSet ∈
                Selection.field responseName fieldName arguments directives
                  childSelectionSet :: tail := by
            simp
          cases hmatch :
              (currentParent == targetParent && fieldName == targetField)
          · cases hrestAppend :
                abstractRuntimeForFieldDeep? schema targetParent targetField
                  currentParent (tail ++ right) with
            | some restRuntimeType =>
                have hruntimeEq : restRuntimeType = runtimeType := by
                  simpa [abstractRuntimeForFieldDeep?, hmatch, hrestAppend]
                    using happendedRuntime
                subst runtimeType
                exact
                  ih (Validation.selectionSetValid_tail hleftValid)
                    (selectionSetDirectiveFree_tail hleftFree)
                    (selectionSetNormal_tail hleftNormal) hrightInclude
                    hrestAppend
            | none =>
                cases hlookup : schema.lookupField currentParent fieldName with
                | none =>
                    simp [abstractRuntimeForFieldDeep?, hmatch, hrestAppend,
                      hlookup] at happendedRuntime
                | some fieldDefinition =>
                    have hchildRuntime :
                        abstractRuntimeForFieldDeep? schema targetParent
                          targetField fieldDefinition.outputType.namedType
                          childSelectionSet = some runtimeType := by
                      simpa [abstractRuntimeForFieldDeep?, hmatch,
                        hrestAppend, hlookup] using happendedRuntime
                    have hchildNonempty : childSelectionSet ≠ [] := by
                      intro hnil
                      simp [hnil, abstractRuntimeForFieldDeep?] at hchildRuntime
                    have hchildValid :
                        Validation.selectionSetValid schema
                          leftVariableDefinitions
                          fieldDefinition.outputType.namedType
                          childSelectionSet :=
                      selectionSetValid_field_child_of_mem_lookup hleftValid
                        hheadMem hchildNonempty hlookup
                    have hchildFree :
                        selectionSetDirectiveFree childSelectionSet :=
                      selectionSetDirectiveFree_field_child_of_mem hleftFree
                        hheadMem
                    have hchildNormal :
                        selectionSetNormal schema
                          fieldDefinition.outputType.namedType
                          childSelectionSet :=
                      selectionSetNormal_field_child_of_mem_lookup
                        hleftNormal hheadMem hlookup
                    exact
                      abstractRuntimeForFieldDeep?_some_include_of_valid_normal
                        hchildValid hchildFree hchildNormal htargetLookup
                        htargetComposite htargetNonObject hchildRuntime
          · cases hfirst :
                firstInlineFragmentTypeCondition? childSelectionSet with
            | some headRuntimeType =>
                have hparts :
                    currentParent = targetParent ∧ fieldName = targetField := by
                  simpa using hmatch
                have hheadLookup :
                    schema.lookupField currentParent fieldName =
                      some targetFieldDefinition := by
                  simpa [hparts.1, hparts.2] using htargetLookup
                rcases
                    firstInlineFragmentTypeCondition?_some_of_valid_normal_abstract_field_mem_lookup
                      hleftValid hleftNormal hheadMem hheadLookup
                      htargetComposite htargetNonObject with
                  ⟨candidateRuntimeType, hcandidateRuntime,
                    hcandidateInclude⟩
                have hcandidateEq :
                    candidateRuntimeType = headRuntimeType := by
                  rw [hfirst] at hcandidateRuntime
                  exact (Option.some.inj hcandidateRuntime).symm
                have hruntimeEq : headRuntimeType = runtimeType := by
                  simpa [abstractRuntimeForFieldDeep?, hmatch, hfirst]
                    using happendedRuntime
                subst candidateRuntimeType
                subst runtimeType
                exact hcandidateInclude
            | none =>
                cases hrestAppend :
                    abstractRuntimeForFieldDeep? schema targetParent
                      targetField currentParent (tail ++ right) with
                | some restRuntimeType =>
                    have hruntimeEq : restRuntimeType = runtimeType := by
                      simpa [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                        hrestAppend] using happendedRuntime
                    subst runtimeType
                    exact
                      ih (Validation.selectionSetValid_tail hleftValid)
                        (selectionSetDirectiveFree_tail hleftFree)
                        (selectionSetNormal_tail hleftNormal) hrightInclude
                        hrestAppend
                | none =>
                    cases hlookup :
                        schema.lookupField currentParent fieldName with
                    | none =>
                        simp [abstractRuntimeForFieldDeep?, hmatch, hfirst,
                          hrestAppend, hlookup] at happendedRuntime
                    | some fieldDefinition =>
                        have hchildRuntime :
                            abstractRuntimeForFieldDeep? schema targetParent
                              targetField
                              fieldDefinition.outputType.namedType
                              childSelectionSet = some runtimeType := by
                          simpa [abstractRuntimeForFieldDeep?, hmatch,
                            hfirst, hrestAppend, hlookup] using
                            happendedRuntime
                        have hchildNonempty : childSelectionSet ≠ [] := by
                          intro hnil
                          simp [hnil, abstractRuntimeForFieldDeep?] at hchildRuntime
                        have hchildValid :
                            Validation.selectionSetValid schema
                              leftVariableDefinitions
                              fieldDefinition.outputType.namedType
                              childSelectionSet :=
                          selectionSetValid_field_child_of_mem_lookup
                            hleftValid hheadMem hchildNonempty hlookup
                        have hchildFree :
                            selectionSetDirectiveFree childSelectionSet :=
                          selectionSetDirectiveFree_field_child_of_mem
                            hleftFree hheadMem
                        have hchildNormal :
                            selectionSetNormal schema
                              fieldDefinition.outputType.namedType
                              childSelectionSet :=
                          selectionSetNormal_field_child_of_mem_lookup
                            hleftNormal hheadMem hlookup
                        exact
                          abstractRuntimeForFieldDeep?_some_include_of_valid_normal
                            hchildValid hchildFree hchildNormal
                            htargetLookup htargetComposite
                            htargetNonObject hchildRuntime
      | inlineFragment typeCondition directives childSelectionSet =>
          cases typeCondition with
          | none =>
              have hheadMem :
                  Selection.inlineFragment none directives childSelectionSet ∈
                    Selection.inlineFragment none directives
                      childSelectionSet :: tail := by
                simp
              have hground :
                  selectionGroundTyped schema currentParent
                    (Selection.inlineFragment none directives
                      childSelectionSet) := by
                have hsetGround :
                    selectionSetGroundTyped schema currentParent
                      (Selection.inlineFragment none directives
                        childSelectionSet :: tail) :=
                  hleftNormal.1
                unfold selectionSetGroundTyped at hsetGround
                exact hsetGround.2 _ hheadMem
              simp [selectionGroundTyped] at hground
          | some typeCondition =>
              have hheadMem :
                  Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet ∈
                    Selection.inlineFragment (some typeCondition) directives
                      childSelectionSet :: tail := by
                simp
              cases hrestAppend :
                  abstractRuntimeForFieldDeep? schema targetParent targetField
                    currentParent (tail ++ right) with
              | some restRuntimeType =>
                  have hruntimeEq : restRuntimeType = runtimeType := by
                    simpa [abstractRuntimeForFieldDeep?, hrestAppend] using
                      happendedRuntime
                  subst runtimeType
                  exact
                    ih (Validation.selectionSetValid_tail hleftValid)
                      (selectionSetDirectiveFree_tail hleftFree)
                      (selectionSetNormal_tail hleftNormal) hrightInclude
                      hrestAppend
              | none =>
                  have hchildRuntime :
                      abstractRuntimeForFieldDeep? schema targetParent
                        targetField typeCondition childSelectionSet =
                          some runtimeType := by
                    simpa [abstractRuntimeForFieldDeep?, hrestAppend] using
                      happendedRuntime
                  have hchildNonempty : childSelectionSet ≠ [] := by
                    intro hnil
                    simp [hnil, abstractRuntimeForFieldDeep?] at hchildRuntime
                  have hchildValid :
                      Validation.selectionSetValid schema
                        leftVariableDefinitions typeCondition
                        childSelectionSet :=
                    selectionSetValid_inlineFragment_some_child_of_mem
                      hleftValid hheadMem
                  have hchildFree :
                      selectionSetDirectiveFree childSelectionSet :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hleftFree hheadMem
                  have hchildNormal :
                      selectionSetNormal schema typeCondition
                        childSelectionSet :=
                    (selectionSetNormal_inlineFragment_child_of_mem
                      hleftNormal hheadMem).2
                  exact
                    abstractRuntimeForFieldDeep?_some_include_of_valid_normal
                      hchildValid hchildFree hchildNormal htargetLookup
                      htargetComposite htargetNonObject hchildRuntime

theorem abstractRuntimeForFieldDeep?_join_some_include_of_valid_normal_members
    {schema : Schema}
    {currentParent targetParent targetField runtimeType : Name}
    {members : List (List Selection)}
    {targetFieldDefinition : FieldDefinition}
    : (∀ selectionSet,
        selectionSet ∈ members
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions
              currentParent selectionSet
            ∧ selectionSetDirectiveFree selectionSet
            ∧ selectionSetNormal schema currentParent selectionSet)
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField
            currentParent (List.flatten members)
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hmembers htargetLookup htargetComposite htargetNonObject hruntime
  induction members generalizing runtimeType with
  | nil =>
      simp [abstractRuntimeForFieldDeep?] at hruntime
  | cons selectionSet rest ih =>
      rcases hmembers selectionSet (by simp) with
        ⟨variableDefinitions, hvalid, hfree, hnormal⟩
      have hrestMembers :
          ∀ restSelectionSet,
            restSelectionSet ∈ rest ->
              ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions
                  currentParent restSelectionSet
                ∧ selectionSetDirectiveFree restSelectionSet
                ∧ selectionSetNormal schema currentParent restSelectionSet := by
        intro restSelectionSet hmem
        exact hmembers restSelectionSet (List.mem_cons_of_mem selectionSet hmem)
      exact
        abstractRuntimeForFieldDeep?_append_some_include_of_valid_normal_or_right
          (schema := schema)
          (leftVariableDefinitions := variableDefinitions)
          (currentParent := currentParent)
          (targetParent := targetParent) (targetField := targetField)
          (runtimeType := runtimeType) (left := selectionSet)
          (right := List.flatten rest)
          (targetFieldDefinition := targetFieldDefinition)
          hvalid hfree hnormal
          (by
            intro rightRuntimeType hrightRuntime
            exact ih hrestMembers hrightRuntime)
          htargetLookup htargetComposite htargetNonObject
          (by simpa [List.flatten_cons] using hruntime)

theorem abstractRuntimeForFieldDeep?_member_framed_promote_some_of_valid_normal_members
    {schema : Schema}
    {currentParent targetParent targetField targetRuntimeType : Name}
    {selectionSet : List Selection} {members : List (List Selection)}
    {targetFieldDefinition : FieldDefinition}
    : (∀ memberSelectionSet,
        memberSelectionSet ∈ members
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions
              currentParent memberSelectionSet
            ∧ selectionSetDirectiveFree memberSelectionSet
            ∧ selectionSetNormal schema currentParent memberSelectionSet)
      -> selectionSet ∈ members
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField
            currentParent selectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
              targetParent
              [Selection.inlineFragment (some currentParent) [] (List.flatten members)]
            = some runtimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hmembers hmem htargetLookup htargetComposite htargetNonObject
    hlocalRuntime
  have hconcatRuntimeExists :
      ∃ concatRuntimeType,
        abstractRuntimeForFieldDeep? schema targetParent targetField
          currentParent (List.flatten members) = some concatRuntimeType := by
    induction members with
    | nil =>
        simp at hmem
    | cons head rest ih =>
        simp at hmem
        rcases hmem with hhead | htail
        · subst selectionSet
          exact
            abstractRuntimeForFieldDeep?_append_some_left_exists
              (schema := schema) (targetParent := targetParent)
              (targetField := targetField) (currentParent := currentParent)
              (left := head) (right := List.flatten rest)
              hlocalRuntime
        · have hrestMembers :
              ∀ memberSelectionSet,
                memberSelectionSet ∈ rest ->
                  ∃ variableDefinitions,
                    Validation.selectionSetValid schema variableDefinitions
                      currentParent memberSelectionSet
                    ∧ selectionSetDirectiveFree memberSelectionSet
                    ∧ selectionSetNormal schema currentParent
                      memberSelectionSet := by
            intro memberSelectionSet hmember
            exact hmembers memberSelectionSet
              (List.mem_cons_of_mem head hmember)
          rcases ih hrestMembers htail with
            ⟨restRuntimeType, hrestRuntime⟩
          exact
            abstractRuntimeForFieldDeep?_append_some_right_exists
              (schema := schema) (targetParent := targetParent)
              (targetField := targetField) (currentParent := currentParent)
              (left := head) (right := List.flatten rest)
              hrestRuntime
  rcases hconcatRuntimeExists with
    ⟨concatRuntimeType, hconcatRuntime⟩
  have hinclude :
      schema.typeIncludesObjectBool
        targetFieldDefinition.outputType.namedType concatRuntimeType = true :=
    abstractRuntimeForFieldDeep?_join_some_include_of_valid_normal_members
      (schema := schema) (currentParent := currentParent)
      (targetParent := targetParent) (targetField := targetField)
      (runtimeType := concatRuntimeType) (members := members)
      (targetFieldDefinition := targetFieldDefinition)
      hmembers htargetLookup htargetComposite htargetNonObject
      hconcatRuntime
  exact
    abstractRuntimeForFieldDeep?_framed_promote_some_of_include
      hconcatRuntime hinclude

theorem abstractRuntimeForFieldDeep?_append_left_promote_some_of_valid_normal
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {currentParent targetParent targetField targetRuntimeType : Name}
    {left right : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions currentParent left
      -> Validation.selectionSetValid schema rightVariableDefinitions currentParent right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema currentParent left
      -> selectionSetNormal schema currentParent right
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField currentParent left
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
              currentParent (left ++ right)
            = some runtimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal
    htargetLookup htargetComposite htargetNonObject hlocalRuntime
  rcases
      abstractRuntimeForFieldDeep?_append_some_left_exists
        (right := right) hlocalRuntime with
    ⟨runtimeType, happendedRuntime⟩
  exact
    ⟨runtimeType, happendedRuntime,
      abstractRuntimeForFieldDeep?_append_some_include_of_valid_normal
        hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal htargetLookup htargetComposite htargetNonObject
        happendedRuntime⟩

theorem abstractRuntimeForFieldDeep?_append_right_promote_some_of_valid_normal
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {currentParent targetParent targetField targetRuntimeType : Name}
    {left right : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions currentParent left
      -> Validation.selectionSetValid schema rightVariableDefinitions currentParent right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema currentParent left
      -> selectionSetNormal schema currentParent right
      -> schema.lookupField targetParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldDeep? schema targetParent targetField currentParent right
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
              currentParent (left ++ right)
            = some runtimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal
    htargetLookup htargetComposite htargetNonObject hlocalRuntime
  rcases
      abstractRuntimeForFieldDeep?_append_some_right_exists
        (left := left) hlocalRuntime with
    ⟨runtimeType, happendedRuntime⟩
  exact
    ⟨runtimeType, happendedRuntime,
      abstractRuntimeForFieldDeep?_append_some_include_of_valid_normal
        hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal htargetLookup htargetComposite htargetNonObject
        happendedRuntime⟩

theorem left_selectionSet_deepFieldReadyWithRef_append_framed_of_valid_normal
    {ObjectRef : Type}
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> ∀ leftResponseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet,
          Selection.field leftResponseName leftFieldName leftArguments
              leftDirectives leftChildSelectionSet
            ∈ left
          -> ∃ fieldDefinition,
              schema.lookupField parentType leftFieldName = some fieldDefinition
              ∧ leafProbeFuel fieldDefinition.outputType
                ≤ selectionSetDeepProbeFuel schema parentType (left ++ right)
              ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  objectRef variableValues
                  (selectionSetDeepProbeFuel schema parentType (left ++ right)
                    - leafProbeFuel fieldDefinition.outputType)
                  parentType leftResponseName leftFieldName leftArguments
                  leftChildSelectionSet fieldDefinition := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject
  have hfuel :
      selectionSetDeepProbeFuel schema parentType left
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
    selectionSetDeepProbeFuel_le_append_left schema parentType left right
  have hpromote :
      ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
        schema.lookupField targetParent targetField =
          some targetFieldDefinition ->
        (TypeRef.named
            targetFieldDefinition.outputType.namedType).isCompositeBool
          schema = true ->
        objectTypeNameBool schema
            targetFieldDefinition.outputType.namedType = false ->
        abstractRuntimeForFieldDeep? schema targetParent targetField
          parentType left = some targetRuntimeType ->
        ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            targetParent
            [Selection.inlineFragment (some parentType) [] (left ++ right)] =
              some runtimeType
            ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType =
              true := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      htargetLookup htargetComposite htargetNonObject hlocalRuntime
    rcases
        abstractRuntimeForFieldDeep?_append_left_promote_some_of_valid_normal
          hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal htargetLookup htargetComposite htargetNonObject
          hlocalRuntime with
      ⟨appendRuntimeType, happendRuntime, hinclude⟩
    exact
      abstractRuntimeForFieldDeep?_framed_promote_some_of_include
        (rootParent := parentType)
        (targetFieldDefinition := targetFieldDefinition)
        happendRuntime hinclude
  intro leftResponseName leftFieldName leftArguments leftDirectives
    leftChildSelectionSet hmem
  exact
    deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
      schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
      objectRef variableValues hschema (SelectionSet.size left + 1)
      parentType leftVariableDefinitions left
      (selectionSetDeepProbeFuel schema parentType (left ++ right))
      (by omega) hfuel hleftValid hleftFree hleftNormal hobject hpromote
      leftResponseName leftFieldName leftArguments leftDirectives
      leftChildSelectionSet hmem

theorem right_selectionSet_deepFieldReadyWithRef_append_framed_of_valid_normal
    {ObjectRef : Type}
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> ∀ rightResponseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet,
          Selection.field rightResponseName rightFieldName rightArguments
              rightDirectives rightChildSelectionSet
            ∈ right
          -> ∃ fieldDefinition,
              schema.lookupField parentType rightFieldName = some fieldDefinition
              ∧ leafProbeFuel fieldDefinition.outputType
                ≤ selectionSetDeepProbeFuel schema parentType (left ++ right)
              ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  objectRef variableValues
                  (selectionSetDeepProbeFuel schema parentType (left ++ right)
                    - leafProbeFuel fieldDefinition.outputType)
                  parentType rightResponseName rightFieldName rightArguments
                  rightChildSelectionSet fieldDefinition := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject
  have hfuel :
      selectionSetDeepProbeFuel schema parentType right
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
    selectionSetDeepProbeFuel_le_append_right schema parentType left right
  have hpromote :
      ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
        schema.lookupField targetParent targetField =
          some targetFieldDefinition ->
        (TypeRef.named
            targetFieldDefinition.outputType.namedType).isCompositeBool
          schema = true ->
        objectTypeNameBool schema
            targetFieldDefinition.outputType.namedType = false ->
        abstractRuntimeForFieldDeep? schema targetParent targetField
          parentType right = some targetRuntimeType ->
        ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            targetParent
            [Selection.inlineFragment (some parentType) [] (left ++ right)] =
              some runtimeType
            ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType =
              true := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      htargetLookup htargetComposite htargetNonObject hlocalRuntime
    rcases
        abstractRuntimeForFieldDeep?_append_right_promote_some_of_valid_normal
          hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal htargetLookup htargetComposite htargetNonObject
          hlocalRuntime with
      ⟨appendRuntimeType, happendRuntime, hinclude⟩
    exact
      abstractRuntimeForFieldDeep?_framed_promote_some_of_include
        (rootParent := parentType)
        (targetFieldDefinition := targetFieldDefinition)
        happendRuntime hinclude
  intro rightResponseName rightFieldName rightArguments rightDirectives
    rightChildSelectionSet hmem
  exact
    deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
      schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
      objectRef variableValues hschema (SelectionSet.size right + 1)
      parentType rightVariableDefinitions right
      (selectionSetDeepProbeFuel schema parentType (left ++ right))
      (by omega) hfuel hrightValid hrightFree hrightNormal hobject hpromote
      rightResponseName rightFieldName rightArguments rightDirectives
      rightChildSelectionSet hmem

theorem selectionSet_deepSuccessFieldOk_framed_of_valid_normal_members
    {ObjectRef : Type}
    {schema : Schema} {parentType : Name}
    {members : List (List Selection)} {selectionSet : List Selection}
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef) (fuel : Nat)
    : SchemaWellFormedness.schemaWellFormed schema
      -> (∀ memberSelectionSet,
            memberSelectionSet ∈ members
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  memberSelectionSet
                ∧ selectionSetDirectiveFree memberSelectionSet
                ∧ selectionSetNormal schema parentType memberSelectionSet)
      -> selectionSet ∈ members
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType (List.flatten members) ≤ fuel
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ selectionSet
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (deepSelectionSetSuccessResolversWithRef schema
                  [Selection.inlineFragment (some parentType) [] (List.flatten members)]
                  objectRef)
                variableValues (fuel + 1) source responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hmembers hmember hobject hfuel responseName fieldName
    arguments directives childSelectionSet hmem
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  rcases hmembers selectionSet hmember with
    ⟨variableDefinitions, hvalid, hfree, hnormal⟩
  have hselectionFuel :
      selectionSetDeepProbeFuel schema parentType selectionSet ≤ fuel := by
    have hlocal :=
      selectionSetDeepProbeFuel_le_flatten_member schema parentType
        (members := members) (selectionSet := selectionSet) hmember
    omega
  have hpromote :
      ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
        schema.lookupField targetParent targetField =
          some targetFieldDefinition ->
        (TypeRef.named
            targetFieldDefinition.outputType.namedType).isCompositeBool
          schema = true ->
        objectTypeNameBool schema
            targetFieldDefinition.outputType.namedType = false ->
        abstractRuntimeForFieldDeep? schema targetParent targetField
          parentType selectionSet = some targetRuntimeType ->
        ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            targetParent rootSelectionSet =
              some runtimeType
            ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType =
              true := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      htargetLookup htargetComposite htargetNonObject hlocalRuntime
    exact
      abstractRuntimeForFieldDeep?_member_framed_promote_some_of_valid_normal_members
        (schema := schema) (currentParent := parentType)
        (targetParent := targetParent) (targetField := targetField)
        (targetRuntimeType := targetRuntimeType)
        (selectionSet := selectionSet) (members := members)
        (targetFieldDefinition := targetFieldDefinition)
        hmembers hmember htargetLookup htargetComposite htargetNonObject
        hlocalRuntime
  rcases
      deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
        schema rootSelectionSet objectRef variableValues hschema
        (SelectionSet.size selectionSet + 1) parentType variableDefinitions
        selectionSet fuel (by omega) hselectionFuel hvalid hfree hnormal
        hobject hpromote responseName fieldName arguments directives
        childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hleafFuel, hready⟩
  rcases
      executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
        schema rootSelectionSet objectRef variableValues fuel source
        responseName parentType fieldName arguments childSelectionSet
        fieldDefinition hlookup hleafFuel hready with
    ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
  exact ⟨responseValue, fieldErrors, hexecute⟩

theorem left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
    {ObjectRef : Type}
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef) (fuel : Nat)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType (left ++ right) ≤ fuel
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ left
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (deepSelectionSetSuccessResolversWithRef schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  objectRef)
                variableValues (fuel + 1) source responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hfuel responseName fieldName arguments directives
    childSelectionSet hmem
  have hleftFuel :
      selectionSetDeepProbeFuel schema parentType left ≤ fuel := by
    have happend :=
      selectionSetDeepProbeFuel_le_append_left schema parentType left right
    omega
  have hpromote :
      ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
        schema.lookupField targetParent targetField =
          some targetFieldDefinition ->
        (TypeRef.named
            targetFieldDefinition.outputType.namedType).isCompositeBool
          schema = true ->
        objectTypeNameBool schema
            targetFieldDefinition.outputType.namedType = false ->
        abstractRuntimeForFieldDeep? schema targetParent targetField
          parentType left = some targetRuntimeType ->
        ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            targetParent
            [Selection.inlineFragment (some parentType) [] (left ++ right)] =
              some runtimeType
            ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType =
              true := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      htargetLookup htargetComposite htargetNonObject hlocalRuntime
    rcases
        abstractRuntimeForFieldDeep?_append_left_promote_some_of_valid_normal
          hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal htargetLookup htargetComposite htargetNonObject
          hlocalRuntime with
      ⟨appendRuntimeType, happendRuntime, hinclude⟩
    exact
      abstractRuntimeForFieldDeep?_framed_promote_some_of_include
        (rootParent := parentType)
        (targetFieldDefinition := targetFieldDefinition)
        happendRuntime hinclude
  rcases
      deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
        schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
        objectRef variableValues hschema (SelectionSet.size left + 1)
        parentType leftVariableDefinitions left fuel
        (by omega) hleftFuel hleftValid hleftFree hleftNormal hobject
        hpromote responseName fieldName arguments directives
        childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hleafFuel, hready⟩
  rcases
      executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
        schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
        objectRef variableValues fuel source responseName parentType
        fieldName arguments childSelectionSet fieldDefinition hlookup
        hleafFuel hready with
    ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
  exact ⟨responseValue, fieldErrors, hexecute⟩

theorem right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
    {ObjectRef : Type}
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef) (fuel : Nat)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> selectionSetDeepProbeFuel schema parentType (left ++ right) ≤ fuel
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ right
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (deepSelectionSetSuccessResolversWithRef schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  objectRef)
                variableValues (fuel + 1) source responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hfuel responseName fieldName arguments directives
    childSelectionSet hmem
  have hrightFuel :
      selectionSetDeepProbeFuel schema parentType right ≤ fuel := by
    have happend :=
      selectionSetDeepProbeFuel_le_append_right schema parentType left right
    omega
  have hpromote :
      ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
        schema.lookupField targetParent targetField =
          some targetFieldDefinition ->
        (TypeRef.named
            targetFieldDefinition.outputType.namedType).isCompositeBool
          schema = true ->
        objectTypeNameBool schema
            targetFieldDefinition.outputType.namedType = false ->
        abstractRuntimeForFieldDeep? schema targetParent targetField
          parentType right = some targetRuntimeType ->
        ∃ runtimeType,
          abstractRuntimeForFieldDeep? schema targetParent targetField
            targetParent
            [Selection.inlineFragment (some parentType) [] (left ++ right)] =
              some runtimeType
            ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType =
              true := by
    intro targetParent targetField targetRuntimeType targetFieldDefinition
      htargetLookup htargetComposite htargetNonObject hlocalRuntime
    rcases
        abstractRuntimeForFieldDeep?_append_right_promote_some_of_valid_normal
          hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal htargetLookup htargetComposite htargetNonObject
          hlocalRuntime with
      ⟨appendRuntimeType, happendRuntime, hinclude⟩
    exact
      abstractRuntimeForFieldDeep?_framed_promote_some_of_include
        (rootParent := parentType)
        (targetFieldDefinition := targetFieldDefinition)
        happendRuntime hinclude
  rcases
      deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
        schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
        objectRef variableValues hschema (SelectionSet.size right + 1)
        parentType rightVariableDefinitions right fuel
        (by omega) hrightFuel hrightValid hrightFree hrightNormal hobject
        hpromote responseName fieldName arguments directives
        childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hleafFuel, hready⟩
  rcases
      executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
        schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
        objectRef variableValues fuel source responseName parentType
        fieldName arguments childSelectionSet fieldDefinition hlookup
        hleafFuel hready with
    ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
  exact ⟨responseValue, fieldErrors, hexecute⟩

theorem left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
    {ObjectRef : Type}
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ left
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (deepSelectionSetSuccessResolversWithRef schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  objectRef)
                variableValues
                (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
                source responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject responseName fieldName arguments directives
    childSelectionSet hmem
  rcases
      left_selectionSet_deepFieldReadyWithRef_append_framed_of_valid_normal
        objectRef variableValues hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hobject responseName fieldName
        arguments directives childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hfuel, hready⟩
  rcases
      executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
        schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
        objectRef variableValues
        (selectionSetDeepProbeFuel schema parentType (left ++ right))
        source responseName parentType fieldName arguments childSelectionSet
        fieldDefinition hlookup hfuel hready with
    ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
  exact ⟨responseValue, fieldErrors, hexecute⟩

theorem right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
    {ObjectRef : Type}
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (objectRef : ObjectRef) (variableValues : Execution.VariableValues)
    (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ right
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (deepSelectionSetSuccessResolversWithRef schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  objectRef)
                variableValues
                (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
                source responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject responseName fieldName arguments directives
    childSelectionSet hmem
  rcases
      right_selectionSet_deepFieldReadyWithRef_append_framed_of_valid_normal
        objectRef variableValues hschema hleftValid hrightValid hleftFree
        hrightFree hleftNormal hrightNormal hobject responseName fieldName
        arguments directives childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hfuel, hready⟩
  rcases
      executeField_deepSelectionSetSuccessWithRef_fieldDefinition_ok_of_ready_fuel_ge
        schema [Selection.inlineFragment (some parentType) [] (left ++ right)]
        objectRef variableValues
        (selectionSetDeepProbeFuel schema parentType (left ++ right))
        source responseName parentType fieldName arguments childSelectionSet
        fieldDefinition hlookup hfuel hready with
    ⟨responseValue, fieldErrors, hexecute, _hnonNull⟩
  exact ⟨responseValue, fieldErrors, hexecute⟩

theorem left_selectionSet_fieldPairProbeProjectionFieldOk_append_framed_leaf_targets
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (variableValues : Execution.VariableValues)
    (leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> (∀ fieldDefinition,
            schema.lookupField parentType leftField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ fieldDefinition,
            schema.lookupField parentType rightField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ arguments,
            Argument.argumentsEquivalent arguments rightArguments
            -> ¬ fieldProbeTarget parentType leftField leftArguments parentType
                  rightField arguments)
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ left
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  (fieldPairProbeResolvers schema
                    [Selection.inlineFragment (some parentType) [] (left ++ right)]
                    parentType leftField rightField leftArguments rightArguments)
                  parentType leftField rightField leftArguments rightArguments)
                variableValues
                (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
                (projectionRootResolverValue
                  (.object parentType (none : Option FieldPairProbeTag)))
                responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftLeaf hrightLeaf hrightNotLeft responseName
    fieldName arguments directives childSelectionSet hmem
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let base :=
    fieldPairProbeResolvers schema rootSelectionSet parentType leftField
      rightField leftArguments rightArguments
  rcases selectionSetValid_field_lookup_of_mem hleftValid hmem with
    ⟨fieldDefinition, hlookup, _hargsValid, _hfieldSelectionValid⟩
  have hmemAppend :
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ left ++ right := by
    exact List.mem_append_left right hmem
  by_cases htargetLeft :
      fieldProbeTarget parentType leftField leftArguments parentType fieldName
        arguments
  · rcases htargetLeft with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    have hleaf := hleftLeaf fieldDefinition hlookup
    have hfuel :
        leafProbeFuel fieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hmemAppend hlookup
    refine
      ⟨leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.left.scalar, 0, ?_⟩
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet base variableValues parentType leftField
      rightField responseName leftArguments rightArguments arguments
      (.object parentType (none : Option FieldPairProbeTag))
      childSelectionSet harguments
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues (selectionSetDeepProbeFuel schema parentType
          (left ++ right)) parentType leftField rightField responseName
        leftArguments rightArguments arguments childSelectionSet
        fieldDefinition harguments hlookup hfuel hleaf
  · by_cases htargetRight :
        fieldProbeTarget parentType rightField rightArguments parentType
          fieldName arguments
    · rcases htargetRight with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget parentType leftField leftArguments parentType
            rightField arguments :=
        hrightNotLeft arguments harguments
      have hleaf := hrightLeaf fieldDefinition hlookup
      have hfuel :
          leafProbeFuel fieldDefinition.outputType
            ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
        leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
          parentType hmemAppend hlookup
      refine
        ⟨leafProbeResponseValue fieldDefinition.outputType
            FieldPairProbeTag.right.scalar, 0, ?_⟩
      rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
        schema rootSelectionSet base variableValues parentType leftField
        rightField responseName leftArguments rightArguments arguments
        (.object parentType (none : Option FieldPairProbeTag))
        childSelectionSet harguments
        (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
      exact
        executeField_fieldPairProbe_right_root_leaf_of_not_left schema
          rootSelectionSet variableValues
          (selectionSetDeepProbeFuel schema parentType (left ++ right))
          parentType leftField rightField responseName leftArguments
          rightArguments arguments childSelectionSet fieldDefinition hnotLeft
          harguments hlookup hfuel hleaf
    · have hnotProjection :
          ¬ fieldPairProjectionTarget parentType leftField rightField
            leftArguments rightArguments parentType fieldName arguments := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact htargetLeft ⟨rfl, hleft.1, hleft.2⟩
        · exact htargetRight ⟨rfl, hright.1, hright.2⟩
      rcases
          left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
            (ProjectionResolverRef.filler :
              ProjectionResolverRef (Option FieldPairProbeTag))
            variableValues
            (.object parentType
              (ProjectionResolverRef.root
                (none : Option FieldPairProbeTag)))
            hschema hleftValid hrightValid hleftFree hrightFree
            hleftNormal hrightNormal hobject responseName fieldName
            arguments directives childSelectionSet hmem with
        ⟨responseValue, fieldErrors, hdeep⟩
      refine ⟨responseValue, fieldErrors, ?_⟩
      simp only [projectionRootResolverValue, projectionResolverValue]
      rw [executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
        schema rootSelectionSet base variableValues parentType leftField
        rightField parentType fieldName parentType responseName
        leftArguments rightArguments arguments
        (none : Option FieldPairProbeTag) childSelectionSet hnotProjection
        (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
      exact hdeep

theorem right_selectionSet_fieldPairProbeProjectionFieldOk_append_framed_leaf_targets
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    (variableValues : Execution.VariableValues)
    (leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> (∀ fieldDefinition,
            schema.lookupField parentType leftField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ fieldDefinition,
            schema.lookupField parentType rightField = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ arguments,
            Argument.argumentsEquivalent arguments rightArguments
            -> ¬ fieldProbeTarget parentType leftField leftArguments parentType
                  rightField arguments)
      -> ∀ responseName fieldName arguments directives childSelectionSet,
          Selection.field responseName fieldName arguments directives childSelectionSet
            ∈ right
          -> ∃ responseValue fieldErrors,
              Execution.executeField schema
                (fieldPairOrDeepSuccessResolvers schema
                  [Selection.inlineFragment (some parentType) [] (left ++ right)]
                  (fieldPairProbeResolvers schema
                    [Selection.inlineFragment (some parentType) [] (left ++ right)]
                    parentType leftField rightField leftArguments rightArguments)
                  parentType leftField rightField leftArguments rightArguments)
                variableValues
                (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
                (projectionRootResolverValue
                  (.object parentType (none : Option FieldPairProbeTag)))
                responseName
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              = .ok ([(responseName, responseValue)], fieldErrors) := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftLeaf hrightLeaf hrightNotLeft responseName
    fieldName arguments directives childSelectionSet hmem
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let base :=
    fieldPairProbeResolvers schema rootSelectionSet parentType leftField
      rightField leftArguments rightArguments
  rcases selectionSetValid_field_lookup_of_mem hrightValid hmem with
    ⟨fieldDefinition, hlookup, _hargsValid, _hfieldSelectionValid⟩
  have hmemAppend :
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ left ++ right := by
    exact List.mem_append_right left hmem
  by_cases htargetLeft :
      fieldProbeTarget parentType leftField leftArguments parentType fieldName
        arguments
  · rcases htargetLeft with ⟨_hparent, hfield, harguments⟩
    subst fieldName
    have hleaf := hleftLeaf fieldDefinition hlookup
    have hfuel :
        leafProbeFuel fieldDefinition.outputType
          ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
      leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
        parentType hmemAppend hlookup
    refine
      ⟨leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.left.scalar, 0, ?_⟩
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet base variableValues parentType leftField
      rightField responseName leftArguments rightArguments arguments
      (.object parentType (none : Option FieldPairProbeTag))
      childSelectionSet harguments
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues (selectionSetDeepProbeFuel schema parentType
          (left ++ right)) parentType leftField rightField responseName
        leftArguments rightArguments arguments childSelectionSet
        fieldDefinition harguments hlookup hfuel hleaf
  · by_cases htargetRight :
        fieldProbeTarget parentType rightField rightArguments parentType
          fieldName arguments
    · rcases htargetRight with ⟨_hparent, hfield, harguments⟩
      subst fieldName
      have hnotLeft :
          ¬ fieldProbeTarget parentType leftField leftArguments parentType
            rightField arguments :=
        hrightNotLeft arguments harguments
      have hleaf := hrightLeaf fieldDefinition hlookup
      have hfuel :
          leafProbeFuel fieldDefinition.outputType
            ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
        leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
          parentType hmemAppend hlookup
      refine
        ⟨leafProbeResponseValue fieldDefinition.outputType
            FieldPairProbeTag.right.scalar, 0, ?_⟩
      rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
        schema rootSelectionSet base variableValues parentType leftField
        rightField responseName leftArguments rightArguments arguments
        (.object parentType (none : Option FieldPairProbeTag))
        childSelectionSet harguments
        (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
      exact
        executeField_fieldPairProbe_right_root_leaf_of_not_left schema
          rootSelectionSet variableValues
          (selectionSetDeepProbeFuel schema parentType (left ++ right))
          parentType leftField rightField responseName leftArguments
          rightArguments arguments childSelectionSet fieldDefinition hnotLeft
          harguments hlookup hfuel hleaf
    · have hnotProjection :
          ¬ fieldPairProjectionTarget parentType leftField rightField
            leftArguments rightArguments parentType fieldName arguments := by
        intro hprojection
        rcases hprojection with ⟨_hparent, htarget⟩
        rcases htarget with hleft | hright
        · exact htargetLeft ⟨rfl, hleft.1, hleft.2⟩
        · exact htargetRight ⟨rfl, hright.1, hright.2⟩
      rcases
          right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
            (ProjectionResolverRef.filler :
              ProjectionResolverRef (Option FieldPairProbeTag))
            variableValues
            (.object parentType
              (ProjectionResolverRef.root
                (none : Option FieldPairProbeTag)))
            hschema hleftValid hrightValid hleftFree hrightFree
            hleftNormal hrightNormal hobject responseName fieldName
            arguments directives childSelectionSet hmem with
        ⟨responseValue, fieldErrors, hdeep⟩
      refine ⟨responseValue, fieldErrors, ?_⟩
      simp only [projectionRootResolverValue, projectionResolverValue]
      rw [executeField_fieldPairOrDeepSuccessResolvers_other_root_eq_deepSuccessWithRef
        schema rootSelectionSet base variableValues parentType leftField
        rightField parentType fieldName parentType responseName
        leftArguments rightArguments arguments
        (none : Option FieldPairProbeTag) childSelectionSet hnotProjection
        (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
      exact hdeep

theorem not_selectionSetsDataEquivalent_of_valid_normal_object_arguments_diff_leaf
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> (∀ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hleafOfLookup hargumentsDiff
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  let base :=
    fieldPairProbeResolvers schema rootSelectionSet parentType fieldName
      fieldName leftArguments rightArguments
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base parentType
      fieldName fieldName leftArguments rightArguments
  let fuel := selectionSetDeepProbeFuel schema parentType (left ++ right) + 1
  let source : Execution.ResolverValue
      (ProjectionResolverRef (Option FieldPairProbeTag)) :=
    projectionRootResolverValue
      (.object parentType (none : Option FieldPairProbeTag))
  rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
    ⟨fieldDefinition, hlookup, _hargsValid, _hfieldSelectionValid⟩
  have hleaf := hleafOfLookup fieldDefinition hlookup
  have hleftMemAppend :
      Selection.field responseName fieldName leftArguments leftDirectives
        leftChildSelectionSet ∈ left ++ right := by
    exact List.mem_append_left right hleftMem
  have hrightMemAppend :
      Selection.field responseName fieldName rightArguments rightDirectives
        rightChildSelectionSet ∈ left ++ right := by
    exact List.mem_append_right left hrightMem
  have hleftFuel :
      leafProbeFuel fieldDefinition.outputType
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
    leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
      parentType hleftMemAppend hlookup
  have hrightFuel :
      leafProbeFuel fieldDefinition.outputType
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
    leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
      parentType hrightMemAppend hlookup
  have hrightNotLeft :
      ∀ arguments,
        Argument.argumentsEquivalent arguments rightArguments ->
          ¬ fieldProbeTarget parentType fieldName leftArguments parentType
            fieldName arguments := by
    intro arguments hrightArgs hleftTarget
    rcases hleftTarget with ⟨_hparent, _hfield, hleftArgs⟩
    exact hargumentsDiff
      (argumentsEquivalent_trans (FieldMerge.argumentsEquivalent_symm hleftArgs)
        hrightArgs)
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    exact
      ⟨parentType,
        ProjectionResolverRef.root (none : Option FieldPairProbeTag),
        by simp [source, projectionRootResolverValue, projectionResolverValue],
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  have hleftTarget :
      Execution.executeField schema resolvers variableValues fuel source
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, source, fuel]
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet base variableValues parentType fieldName
      fieldName responseName leftArguments rightArguments leftArguments
      (.object parentType (none : Option FieldPairProbeTag))
      leftChildSelectionSet (argumentsEquivalent_refl_forSyntaxDiff
        leftArguments)
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues (selectionSetDeepProbeFuel schema parentType
          (left ++ right)) parentType fieldName fieldName responseName
        leftArguments rightArguments leftArguments leftChildSelectionSet
        fieldDefinition (argumentsEquivalent_refl_forSyntaxDiff
          leftArguments) hlookup hleftFuel hleaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues fuel source
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue fieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, source, fuel]
    rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
      schema rootSelectionSet base variableValues parentType fieldName
      fieldName responseName leftArguments rightArguments rightArguments
      (.object parentType (none : Option FieldPairProbeTag))
      rightChildSelectionSet (argumentsEquivalent_refl_forSyntaxDiff
        rightArguments)
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
    exact
      executeField_fieldPairProbe_right_root_leaf_of_not_left schema
        rootSelectionSet variableValues
        (selectionSetDeepProbeFuel schema parentType (left ++ right))
        parentType fieldName fieldName responseName leftArguments
        rightArguments rightArguments rightChildSelectionSet fieldDefinition
        (hrightNotLeft rightArguments
          (argumentsEquivalent_refl_forSyntaxDiff rightArguments))
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hlookup
        hrightFuel hleaf
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_responseName_value_diff_of_field_ok
      resolvers variableValues fuel source hsource hobject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftTarget
      hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne
        fieldDefinition.outputType (by simp [FieldPairProbeTag.scalar]))
      (left_selectionSet_fieldPairProbeProjectionFieldOk_append_framed_leaf_targets
        variableValues fieldName fieldName leftArguments rightArguments
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hobject hleafOfLookup hleafOfLookup hrightNotLeft)
      (right_selectionSet_fieldPairProbeProjectionFieldOk_append_framed_leaf_targets
        variableValues fieldName fieldName leftArguments rightArguments
        hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hobject hleafOfLookup hleafOfLookup hrightNotLeft)

theorem not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_leaf
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> (∀ fieldDefinition,
            schema.lookupField parentType leftFieldName = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> (∀ fieldDefinition,
            schema.lookupField parentType rightFieldName = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = false)
      -> leftFieldName ≠ rightFieldName
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightMem hleftLeafOfLookup
    hrightLeafOfLookup hfieldDiff
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  let base :=
    fieldPairProbeResolvers schema rootSelectionSet parentType leftFieldName
      rightFieldName leftArguments rightArguments
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet base parentType
      leftFieldName rightFieldName leftArguments rightArguments
  let fuel := selectionSetDeepProbeFuel schema parentType (left ++ right) + 1
  let source : Execution.ResolverValue
      (ProjectionResolverRef (Option FieldPairProbeTag)) :=
    projectionRootResolverValue
      (.object parentType (none : Option FieldPairProbeTag))
  rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
    ⟨leftFieldDefinition, hleftLookup, _hleftArgsValid,
      _hleftFieldSelectionValid⟩
  rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
    ⟨rightFieldDefinition, hrightLookup, _hrightArgsValid,
      _hrightFieldSelectionValid⟩
  have hleftLeaf := hleftLeafOfLookup leftFieldDefinition hleftLookup
  have hrightLeaf := hrightLeafOfLookup rightFieldDefinition hrightLookup
  have hleftMemAppend :
      Selection.field responseName leftFieldName leftArguments leftDirectives
        leftChildSelectionSet ∈ left ++ right := by
    exact List.mem_append_left right hleftMem
  have hrightMemAppend :
      Selection.field responseName rightFieldName rightArguments rightDirectives
        rightChildSelectionSet ∈ left ++ right := by
    exact List.mem_append_right left hrightMem
  have hleftFuel :
      leafProbeFuel leftFieldDefinition.outputType
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
    leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
      parentType hleftMemAppend hleftLookup
  have hrightFuel :
      leafProbeFuel rightFieldDefinition.outputType
        ≤ selectionSetDeepProbeFuel schema parentType (left ++ right) :=
    leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
      parentType hrightMemAppend hrightLookup
  have hrightNotLeft :
      ∀ arguments,
        Argument.argumentsEquivalent arguments rightArguments ->
          ¬ fieldProbeTarget parentType leftFieldName leftArguments
            parentType rightFieldName arguments := by
    intro arguments _hrightArgs hleftTarget
    exact hfieldDiff hleftTarget.2.1.symm
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    exact
      ⟨parentType,
        ProjectionResolverRef.root (none : Option FieldPairProbeTag),
        by simp [source, projectionRootResolverValue, projectionResolverValue],
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  have hleftTarget :
      Execution.executeField schema resolvers variableValues fuel source
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := leftFieldName,
          arguments := leftArguments,
          selectionSet := leftChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue leftFieldDefinition.outputType
          FieldPairProbeTag.left.scalar)], 0) := by
    dsimp [resolvers, source, fuel]
    rw [executeField_fieldPairOrDeepSuccessResolvers_left_root
      schema rootSelectionSet base variableValues parentType leftFieldName
      rightFieldName responseName leftArguments rightArguments leftArguments
      (.object parentType (none : Option FieldPairProbeTag))
      leftChildSelectionSet (argumentsEquivalent_refl_forSyntaxDiff
        leftArguments)
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
    exact
      executeField_fieldPairProbe_left_root_leaf schema rootSelectionSet
        variableValues (selectionSetDeepProbeFuel schema parentType
          (left ++ right)) parentType leftFieldName rightFieldName
        responseName leftArguments rightArguments leftArguments
        leftChildSelectionSet leftFieldDefinition
        (argumentsEquivalent_refl_forSyntaxDiff leftArguments) hleftLookup
        hleftFuel hleftLeaf
  have hrightTarget :
      Execution.executeField schema resolvers variableValues fuel source
        responseName
        [{
          parentType := parentType,
          responseName := responseName,
          fieldName := rightFieldName,
          arguments := rightArguments,
          selectionSet := rightChildSelectionSet
        }]
      =
      .ok ([(responseName,
        leafProbeResponseValue rightFieldDefinition.outputType
          FieldPairProbeTag.right.scalar)], 0) := by
    dsimp [resolvers, source, fuel]
    rw [executeField_fieldPairOrDeepSuccessResolvers_right_root
      schema rootSelectionSet base variableValues parentType leftFieldName
      rightFieldName responseName leftArguments rightArguments rightArguments
      (.object parentType (none : Option FieldPairProbeTag))
      rightChildSelectionSet (argumentsEquivalent_refl_forSyntaxDiff
        rightArguments)
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)]
    exact
      executeField_fieldPairProbe_right_root_leaf_of_not_left schema
        rootSelectionSet variableValues
        (selectionSetDeepProbeFuel schema parentType (left ++ right))
        parentType leftFieldName rightFieldName responseName leftArguments
        rightArguments rightArguments rightChildSelectionSet
        rightFieldDefinition
        (hrightNotLeft rightArguments
          (argumentsEquivalent_refl_forSyntaxDiff rightArguments))
        (argumentsEquivalent_refl_forSyntaxDiff rightArguments) hrightLookup
        hrightFuel hrightLeaf
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_responseName_value_diff_of_field_ok
      resolvers variableValues fuel source hsource hobject hleftNormal
      hrightNormal hleftFree hrightFree hleftMem hrightMem hleftTarget
      hrightTarget
      (leafProbeResponseValue_not_semanticEquivalent_of_ne_any
        leftFieldDefinition.outputType rightFieldDefinition.outputType
        (by simp [FieldPairProbeTag.scalar]))
      (left_selectionSet_fieldPairProbeProjectionFieldOk_append_framed_leaf_targets
        variableValues leftFieldName rightFieldName leftArguments
        rightArguments hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hobject hleftLeafOfLookup
        hrightLeafOfLookup hrightNotLeft)
      (right_selectionSet_fieldPairProbeProjectionFieldOk_append_framed_leaf_targets
        variableValues leftFieldName rightFieldName leftArguments
        rightArguments hschema hleftValid hrightValid hleftFree hrightFree
        hleftNormal hrightNormal hobject hleftLeafOfLookup
        hrightLeafOfLookup hrightNotLeft)

theorem not_selectionSetsDataEquivalent_of_object_child_diff_singleton
    {schema : Schema}
    {parentType returnType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> Argument.argumentsEquivalent leftArguments rightArguments
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName leftArguments [] leftChildSelectionSet]
      -> selectionSetDirectiveFree
          [Selection.field responseName fieldName rightArguments []
            rightChildSelectionSet]
      -> selectionSetNormal schema parentType
          [Selection.field responseName fieldName leftArguments [] leftChildSelectionSet]
      -> selectionSetNormal schema parentType
          [Selection.field responseName fieldName rightArguments []
            rightChildSelectionSet]
      -> objectTypeNameBool schema parentType = true
      -> objectTypeNameBool schema returnType = true
      -> ¬ selectionSetsDataEquivalent schema returnType
            leftChildSelectionSet rightChildSelectionSet
      -> ¬ selectionSetsDataEquivalent schema parentType
            [Selection.field responseName fieldName leftArguments []
              leftChildSelectionSet]
            [Selection.field responseName fieldName rightArguments []
              rightChildSelectionSet] := by
  intro hschema hlookup hreturnType harguments hleftFree hrightFree
    hleftNormal hrightNormal hparentObject hreturnObject hchildNot
    hparentData
  apply hchildNot
  intro ObjectRef base variableValues fuel source hsource
  rcases hsource with ⟨runtimeType, ref, hsourceEq, hinclude⟩
  subst source
  have hruntimeEq : runtimeType = returnType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
      hreturnObject hinclude
  subst runtimeType
  have hruntimeObject :
      objectTypeNameBool schema returnType = true := hreturnObject
  have hfieldInclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        returnType = true := by
    simpa [hreturnType] using
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hreturnObject
  have hchildAtRuntime :
      selectionSetsDataEquivalent schema returnType
        leftChildSelectionSet rightChildSelectionSet :=
    selectionSetsDataEquivalent_object_child_of_parent_empty_tail
      [Selection.inlineFragment (some parentType) []
        [Selection.field responseName fieldName leftArguments []
          leftChildSelectionSet,
         Selection.field responseName fieldName rightArguments []
          rightChildSelectionSet]]
      parentType responseName fieldName leftArguments rightArguments
      leftChildSelectionSet rightChildSelectionSet fieldDefinition
      returnType harguments hlookup hleftFree hrightFree hleftNormal
      hrightNormal hparentObject hruntimeObject hfieldInclude hparentData
  exact
    hchildAtRuntime base variableValues fuel (.object returnType ref)
      ⟨returnType, ref, rfl,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema
          hruntimeObject⟩

theorem not_selectionSetsDataEquivalent_of_object_child_diff_split_context_ok
    {schema : Schema}
    (rootSelectionSet : List Selection)
    {parentType returnType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> Argument.argumentsEquivalent leftArguments rightArguments
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> objectTypeNameBool schema returnType = true
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
              (variableValues : Execution.VariableValues) (fuel : Nat)
              (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            -> ∃ leftPrefixFields leftPrefixErrors rightPrefixFields
                  rightPrefixErrors leftSuffixFields leftSuffixErrors
                  rightSuffixFields rightSuffixErrors,
                Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base parentType fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      parentType fieldName fieldName leftArguments rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    parentType
                    (projectionRootResolverValue
                      (.object parentType (none : Option ObjectRef)))
                    leftPref
                  = .ok (leftPrefixFields, leftPrefixErrors)
                ∧ Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base parentType fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      parentType fieldName fieldName leftArguments rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    parentType
                    (projectionRootResolverValue
                      (.object parentType (none : Option ObjectRef)))
                    rightPref
                  = .ok (rightPrefixFields, rightPrefixErrors)
                ∧ Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base parentType fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      parentType fieldName fieldName leftArguments rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    parentType
                    (projectionRootResolverValue
                      (.object parentType (none : Option ObjectRef)))
                    leftSuffix
                  = .ok (leftSuffixFields, leftSuffixErrors)
                ∧ Execution.executeSelectionSet schema
                    (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                      (parentObjectProbeFieldResolvers base parentType fieldName
                        childRuntimeType ref fieldDefinition.outputType)
                      parentType fieldName fieldName leftArguments rightArguments)
                    variableValues
                    (fuel + leafProbeFuel fieldDefinition.outputType + 1)
                    parentType
                    (projectionRootResolverValue
                      (.object parentType (none : Option ObjectRef)))
                    rightSuffix
                  = .ok (rightSuffixFields, rightSuffixErrors))
      -> ¬ selectionSetsDataEquivalent schema returnType
            leftChildSelectionSet rightChildSelectionSet
      -> ¬ selectionSetsDataEquivalent schema parentType
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix) := by
  intro _hschema hlookup hreturnType harguments hleftFree hrightFree
    hleftNormal hrightNormal hparentObject hreturnObject hcontext
    hchildNot hparentData
  apply hchildNot
  have hfieldInclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        returnType = true := by
    simpa [hreturnType] using
      typeIncludesObjectBool_self_of_objectTypeNameBool schema hreturnObject
  intro ObjectRef base variableValues fuel source hsource
  exact
    selectionSetsDataEquivalent_object_child_of_parent_split_context_ok
      rootSelectionSet parentType responseName fieldName leftArguments
      rightArguments leftChildSelectionSet rightChildSelectionSet leftPref
      rightPref leftSuffix rightSuffix fieldDefinition returnType harguments
      hlookup hleftFree hrightFree hleftNormal hrightNormal hparentObject
      hreturnObject hfieldInclude hcontext hparentData base variableValues
      fuel source hsource

theorem not_selectionSetsDataEquivalent_of_object_child_responseData_diff_concrete_fieldsExecuteOk
    {ObjectRef : Type} {schema : Schema} (rootSelectionSet : List Selection)
    (base : Execution.Resolvers ObjectRef) (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent responseName fieldName : Name)
    (leftArguments rightArguments : List Argument)
    (leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection)
    (fieldDefinition : FieldDefinition) (runtimeType : Name) (ref : ObjectRef)
    : schema.lookupField targetParent fieldName = some fieldDefinition
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema targetParent
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema targetParent
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema targetParent = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> selectionSetFieldsExecuteOk schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base targetParent fieldName
                runtimeType ref fieldDefinition.outputType)
              targetParent fieldName fieldName leftArguments rightArguments)
            variableValues
            (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            targetParent
            (projectionRootResolverValue (.object targetParent (none : Option ObjectRef)))
            leftPref
          ∧ selectionSetFieldsExecuteOk schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base targetParent fieldName
                  runtimeType ref fieldDefinition.outputType)
                targetParent fieldName fieldName leftArguments rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              targetParent
              (projectionRootResolverValue
                (.object targetParent (none : Option ObjectRef)))
              rightPref
          ∧ selectionSetFieldsExecuteOk schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base targetParent fieldName
                  runtimeType ref fieldDefinition.outputType)
                targetParent fieldName fieldName leftArguments rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              targetParent
              (projectionRootResolverValue
                (.object targetParent (none : Option ObjectRef)))
              leftSuffix
          ∧ selectionSetFieldsExecuteOk schema
              (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                (parentObjectProbeFieldResolvers base targetParent fieldName
                  runtimeType ref fieldDefinition.outputType)
                targetParent fieldName fieldName leftArguments rightArguments)
              variableValues
              (fuel + leafProbeFuel fieldDefinition.outputType + 1)
              targetParent
              (projectionRootResolverValue
                (.object targetParent (none : Option ObjectRef)))
              rightSuffix
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema base variableValues fuel
              runtimeType (.object runtimeType ref) leftChildSelectionSet).data
            (Execution.executeSelectionSetAsResponse schema base variableValues fuel
              runtimeType (.object runtimeType ref) rightChildSelectionSet).data
      -> ¬ selectionSetsDataEquivalent schema targetParent
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix) := by
  intro hlookup hleftFree hrightFree hleftNormal hrightNormal hobject
    hfieldInclude hfieldsOk hchildNot
  apply
    not_selectionSetsDataEquivalent_of_object_child_responseData_diff_split_context_ok
      rootSelectionSet base variableValues fuel targetParent responseName
      fieldName leftArguments rightArguments leftChildSelectionSet
      rightChildSelectionSet leftPref rightPref leftSuffix rightSuffix
      fieldDefinition runtimeType ref hlookup hleftFree hrightFree
      hleftNormal hrightNormal hobject hfieldInclude
  · exact
      object_child_split_context_ok_of_concrete_fieldsExecuteOk
        rootSelectionSet base variableValues fuel runtimeType ref hleftFree
        hrightFree hleftNormal hrightNormal hobject hfieldsOk
  · exact hchildNot

theorem responseData_not_semanticEquivalent_of_valid_normal_abstract_left_typeCondition_diff_runtime
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet ∈ left
      -> typeCondition ∉ right.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (deepSelectionSetSuccessResolversWithRef schema
                [Selection.inlineFragment (some parentType) [] (left ++ right)]
                PUnit.unit)
              [] (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
              typeCondition (.object typeCondition PUnit.unit) left).data
            (Execution.executeSelectionSetAsResponse schema
              (deepSelectionSetSuccessResolversWithRef schema
                [Selection.inlineFragment (some parentType) [] (left ++ right)]
                PUnit.unit)
              [] (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
              typeCondition (.object typeCondition PUnit.unit) right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hnonObject hleftMem hrightNoTypeCondition
  have hdirectives : directives = [] :=
    selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
      hleftFree hleftMem
  subst directives
  have hleftMemNil :
      Selection.inlineFragment (some typeCondition) [] childSelectionSet ∈
        left := hleftMem
  rcases selectionSetNormal_inlineFragment_child_of_mem hleftNormal
      hleftMemNil with
    ⟨htypeObject, _hinclude, _hchildNormal⟩
  have htypeObjectBool :
      objectTypeNameBool schema typeCondition = true :=
    objectTypeNameBool_eq_true_of_objectType_forNormality schema
      htypeObject
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  let objectRef : PUnit := PUnit.unit
  let fuel := selectionSetDeepProbeFuel schema parentType (left ++ right)
  let resolvers :=
    deepSelectionSetSuccessResolversWithRef schema rootSelectionSet objectRef
  let source : Execution.ResolverValue PUnit :=
    .object typeCondition objectRef
  have hleftAppendMem :
      Selection.inlineFragment (some typeCondition) [] childSelectionSet ∈
        left ++ right :=
    List.mem_append_left right hleftMemNil
  have hbodyFuel :
      selectionSetDeepProbeFuel schema typeCondition childSelectionSet ≤
        fuel := by
    dsimp [fuel]
    exact
      selectionSetDeepProbeFuel_inlineFragment_some_mem schema parentType
        (left ++ right) typeCondition [] childSelectionSet hleftAppendMem
  have hleftBodyReady :
      ∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
          bodyChildSelectionSet,
        Selection.field bodyResponseName bodyFieldName bodyArguments
            bodyDirectives bodyChildSelectionSet ∈ childSelectionSet ->
          ∃ bodyFieldDefinition,
            schema.lookupField typeCondition bodyFieldName =
              some bodyFieldDefinition
              ∧ leafProbeFuel bodyFieldDefinition.outputType ≤ fuel
              ∧ deepFieldSelectionSetExecutionReadyWithRef schema
                rootSelectionSet objectRef variableValues
                (fuel - leafProbeFuel bodyFieldDefinition.outputType)
                typeCondition bodyResponseName bodyFieldName bodyArguments
                bodyChildSelectionSet bodyFieldDefinition := by
    intro bodyResponseName bodyFieldName bodyArguments bodyDirectives
      bodyChildSelectionSet hbodyFieldMem
    have hbodyValid :
        Validation.selectionSetValid schema leftVariableDefinitions
          typeCondition childSelectionSet :=
      selectionSetValid_inlineFragment_some_child_of_mem hleftValid
        hleftMemNil
    have hbodyFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_inlineFragment_child_of_mem hleftFree
        hleftMemNil
    have hbodyNormal :
        selectionSetNormal schema typeCondition childSelectionSet :=
      (selectionSetNormal_inlineFragment_child_of_mem hleftNormal
        hleftMemNil).2
    rcases selectionSetValid_field_lookup_of_mem hbodyValid
        hbodyFieldMem with
      ⟨bodyFieldDefinition, hbodyLookup, _hbodyArguments,
        _hbodyFieldSelectionValid⟩
    have hleafFuel :
        leafProbeFuel bodyFieldDefinition.outputType ≤ fuel := by
      have hfieldFuel :=
        leafProbeFuel_le_selectionSetDeepProbeFuel_of_field_mem schema
          typeCondition (selectionSet := childSelectionSet)
          (responseName := bodyResponseName)
          (fieldName := bodyFieldName)
          (arguments := bodyArguments)
          (directives := bodyDirectives)
          (childSelectionSet := bodyChildSelectionSet)
          (fieldDefinition := bodyFieldDefinition)
          hbodyFieldMem hbodyLookup
      omega
    have hpromote :
        ∀ targetParent targetField targetRuntimeType targetFieldDefinition,
          schema.lookupField targetParent targetField =
            some targetFieldDefinition ->
          (TypeRef.named
              targetFieldDefinition.outputType.namedType).isCompositeBool
            schema = true ->
          objectTypeNameBool schema
              targetFieldDefinition.outputType.namedType = false ->
          abstractRuntimeForFieldDeep? schema targetParent targetField
            typeCondition childSelectionSet = some targetRuntimeType ->
          ∃ runtimeType,
            abstractRuntimeForFieldDeep? schema targetParent targetField
              targetParent rootSelectionSet = some runtimeType
              ∧ schema.typeIncludesObjectBool
                targetFieldDefinition.outputType.namedType runtimeType =
                  true := by
      intro targetParent targetField targetRuntimeType targetFieldDefinition
        htargetLookup htargetComposite htargetNonObject hlocalRuntime
      rcases
          abstractRuntimeForFieldDeep?_inlineFragment_child_promote_some_of_valid_normal
            hleftValid hleftFree hleftNormal hleftMemNil htargetLookup
            htargetComposite htargetNonObject hlocalRuntime with
        ⟨leftRuntimeType, hleftRuntime, _hleftInclude⟩
      rcases
          abstractRuntimeForFieldDeep?_append_left_promote_some_of_valid_normal
            hleftValid hrightValid hleftFree hrightFree hleftNormal
            hrightNormal htargetLookup htargetComposite htargetNonObject
            hleftRuntime with
        ⟨_appendedRuntimeType, happendedRuntime, happendedInclude⟩
      exact
        abstractRuntimeForFieldDeep?_framed_promote_some_of_include
          (rootParent := parentType)
          (targetFieldDefinition := targetFieldDefinition)
          happendedRuntime happendedInclude
    exact
      deepFieldSelectionSetReadyWithRef_of_valid_normal_object_promoted_fuel_ge_size
        schema rootSelectionSet objectRef variableValues hschema
        (SelectionSet.size childSelectionSet + 1)
        typeCondition leftVariableDefinitions childSelectionSet fuel
        (by omega) hbodyFuel hbodyValid hbodyFree hbodyNormal
        htypeObjectBool hpromote bodyResponseName bodyFieldName
        bodyArguments bodyDirectives bodyChildSelectionSet hbodyFieldMem
  rcases
      executeSelectionSetAsResponse_deepSelectionSetSuccessWithRef_abstract_matching_inlineFragment_nonempty
        schema rootSelectionSet objectRef variableValues fuel hnonObject
        htypeObjectBool hleftFree hleftNormal hleftMemNil
        (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
          hleftValid hleftMemNil)
        hleftBodyReady with
    ⟨leftResponseField, leftResponseFields, leftErrors, hleftResponse⟩
  have hrightCollect :
      Execution.collectFields schema variableValues typeCondition source
        right = [] :=
    collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
      schema variableValues (normalParentType := parentType)
      (executionParentType := typeCondition) (runtimeType := typeCondition)
      objectRef hnonObject hrightFree hrightNormal hrightNoTypeCondition
  have hrightResponse :
      Execution.executeSelectionSetAsResponse schema resolvers variableValues (fuel + 1)
        typeCondition source right =
      ({ data := Execution.ResponseValue.object [], errors := 0 } :
        Execution.Response) := by
    simp [resolvers, source, Execution.executeSelectionSetAsResponse,
      Execution.selectionSetResultToResponse, Execution.executeSelectionSet,
      Execution.executeRootSelectionSet, hrightCollect,
      Execution.executeCollectedFields]
  intro hsemantic
  have hleftRight :
      Execution.ResponseValue.semanticEquivalent
        (Execution.ResponseValue.object
          (leftResponseField :: leftResponseFields))
        (Execution.ResponseValue.object []) := by
    simpa [rootSelectionSet, variableValues, objectRef, fuel, resolvers,
      source, hleftResponse, hrightResponse] using hsemantic
  exact
    SemanticSeparation.responseValue_object_cons_not_semanticEquivalent_empty_object
      hleftRight

theorem responseData_not_semanticEquivalent_of_valid_normal_abstract_right_typeCondition_diff_runtime
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} {typeCondition : Name}
    {directives : List DirectiveApplication} {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ right
      -> typeCondition ∉ left.filterMap inlineFragmentTypeCondition?
      -> ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema
              (deepSelectionSetSuccessResolversWithRef schema
                [Selection.inlineFragment (some parentType) [] (right ++ left)]
                PUnit.unit)
              [] (selectionSetDeepProbeFuel schema parentType (right ++ left) + 1)
              typeCondition (.object typeCondition PUnit.unit) left).data
            (Execution.executeSelectionSetAsResponse schema
              (deepSelectionSetSuccessResolversWithRef schema
                [Selection.inlineFragment (some parentType) [] (right ++ left)]
                PUnit.unit)
              [] (selectionSetDeepProbeFuel schema parentType (right ++ left) + 1)
              typeCondition (.object typeCondition PUnit.unit) right).data := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hnonObject hrightMem hleftNoTypeCondition hsemantic
  have hswapped :=
    responseData_not_semanticEquivalent_of_valid_normal_abstract_left_typeCondition_diff_runtime
      (schema := schema)
      (leftVariableDefinitions := rightVariableDefinitions)
      (rightVariableDefinitions := leftVariableDefinitions)
      (parentType := parentType)
      (left := right) (right := left)
      (typeCondition := typeCondition) (directives := directives)
      (childSelectionSet := childSelectionSet)
      hschema hrightValid hleftValid hrightFree hleftFree hrightNormal
      hleftNormal hnonObject hrightMem hleftNoTypeCondition
  exact hswapped (by
    simpa [Execution.ResponseValue.semanticEquivalent] using
      (Eq.symm (by
        simpa [Execution.ResponseValue.semanticEquivalent] using
          hsemantic)))

theorem not_selectionSetsDataEquivalent_of_valid_normal_object_left_responseName_diff
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hleftMem hrightNoResponseName
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  let source : Execution.ResolverValue PUnit :=
    .object parentType PUnit.unit
  let resolvers :=
    deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
      PUnit.unit
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    exact
      ⟨parentType, PUnit.unit, rfl,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_left_responseName_diff_of_field_ok
      resolvers variableValues
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
      source hsource hobject hleftNormal hrightNormal hleftFree hrightFree
      hleftMem hrightNoResponseName
      (by
        intro responseName fieldName arguments directives childSelectionSet
          hmem
        exact
          left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
            PUnit.unit variableValues source hschema hleftValid hrightValid
            hleftFree hrightFree hleftNormal hrightNormal hobject
            responseName fieldName arguments directives childSelectionSet
            hmem)
      (by
        intro responseName fieldName arguments directives childSelectionSet
          hmem
        exact
          right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
            PUnit.unit variableValues source hschema hleftValid hrightValid
            hleftFree hrightFree hleftNormal hrightNormal hobject
            responseName fieldName arguments directives childSelectionSet
            hmem)

theorem not_selectionSetsDataEquivalent_of_valid_normal_object_right_responseName_diff
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hobject hrightMem hleftNoResponseName
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (left ++ right)]
  let variableValues : Execution.VariableValues := []
  let source : Execution.ResolverValue PUnit :=
    .object parentType PUnit.unit
  let resolvers :=
    deepSelectionSetSuccessResolversWithRef schema rootSelectionSet
      PUnit.unit
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true := by
    exact
      ⟨parentType, PUnit.unit, rfl,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  exact
    SemanticSeparation.not_selectionSetsDataEquivalent_of_right_responseName_diff_of_field_ok
      resolvers variableValues
      (selectionSetDeepProbeFuel schema parentType (left ++ right) + 1)
      source hsource hobject hleftNormal hrightNormal hleftFree hrightFree
      hrightMem hleftNoResponseName
      (by
        intro responseName fieldName arguments directives childSelectionSet
          hmem
        exact
          left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
            PUnit.unit variableValues source hschema hleftValid hrightValid
            hleftFree hrightFree hleftNormal hrightNormal hobject
            responseName fieldName arguments directives childSelectionSet
            hmem)
      (by
        intro responseName fieldName arguments directives childSelectionSet
          hmem
        exact
          right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal
            PUnit.unit variableValues source hschema hleftValid hrightValid
            hleftFree hrightFree hleftNormal hrightNormal hobject
            responseName fieldName arguments directives childSelectionSet
            hmem)

end GroundTypeNormalization

end NormalForm

end GraphQL
