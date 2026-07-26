import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.BoundaryProbe
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DataSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DiffObservable
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedRuntime
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedTrace

/-!
Path-local runtime, support, and response-path context for focused probes.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def PathLocalCurrentRuntimeSound (schema : Schema) (current : Name × List Selection)
    : Prop :=
  ∀ targetParent targetField runtimeType targetArguments
      (targetFieldDefinition : FieldDefinition),
    schema.lookupField targetParent targetField = some targetFieldDefinition
    -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
        = true
    -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
    -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
          targetArguments current.1 current.2
        = some runtimeType
    -> schema.typeIncludesObjectBool
          targetFieldDefinition.outputType.namedType runtimeType
        = true

def PathLocalSelectionSetHeadReady (schema : Schema)
    (parentType : Name) (currentSelectionSet selectionSet : List Selection)
    : Prop :=
  ∀ responseName fieldName arguments directives childSelectionSet
      (fieldDefinition : FieldDefinition),
    Selection.field responseName fieldName arguments directives childSelectionSet
      ∈ selectionSet
    -> schema.lookupField parentType fieldName = some fieldDefinition
    -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema = true
    -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
    -> ∃ runtimeType,
        abstractRuntimeForFieldHeadDeep? schema parentType fieldName
            arguments parentType currentSelectionSet
          = some runtimeType
        ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true

def PathLocalSupportValidNormal (schema : Schema)
    (parentType : Name) (currentSelectionSet : List Selection)
    : Prop :=
  ∃ members : List (List Selection),
    currentSelectionSet = List.flatten members
    ∧ ∀ memberSelectionSet,
        memberSelectionSet ∈ members
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions
              parentType memberSelectionSet
            ∧ selectionSetDirectiveFree memberSelectionSet
            ∧ selectionSetNormal schema parentType memberSelectionSet

def PathLocalSelectionSetCurrentContext
    (selectionSet currentSelectionSet : List Selection)
    : Prop :=
  ∃ pref suff : List Selection, currentSelectionSet = pref ++ selectionSet ++ suff

theorem PathLocalCurrentRuntimeSound.of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> PathLocalCurrentRuntimeSound schema (parentType, selectionSet) := by
  intro hvalid hfree hnormal targetParent targetField runtimeType
    targetArguments targetFieldDefinition hlookup hcomposite hnonObject
    hruntime
  exact
    abstractRuntimeForFieldHeadDeep?_some_include_of_valid_normal
      hvalid hfree hnormal hlookup hcomposite hnonObject hruntime

theorem PathLocalSelectionSetHeadReady.of_valid_normal_self
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> PathLocalSelectionSetHeadReady schema parentType selectionSet selectionSet := by
  intro hvalid hnormal responseName fieldName arguments directives
    childSelectionSet fieldDefinition hmem hlookup hcomposite hnonObject
  exact
    abstractRuntimeForFieldHeadDeep?_some_of_valid_normal_abstract_mem_lookup
      hvalid hnormal hmem hlookup hcomposite hnonObject

theorem abstractRuntimeForFieldHeadDeep?_member_flatten_promote_some_of_valid_normal_members
    {schema : Schema} {currentParent targetField targetRuntimeType : Name}
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
      -> schema.lookupField currentParent targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldHeadDeep? schema currentParent targetField
            targetArguments currentParent selectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldHeadDeep? schema currentParent targetField
              targetArguments currentParent (List.flatten members)
            = some runtimeType
          ∧ schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hmembers hmem htargetLookup htargetComposite htargetNonObject
    hlocalRuntime
  have hconcatRuntimeExists :
      ∃ concatRuntimeType,
        abstractRuntimeForFieldHeadDeep? schema currentParent targetField
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
              (schema := schema) (targetParent := currentParent)
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
              (schema := schema) (targetParent := currentParent)
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
      (targetParent := currentParent) (targetField := targetField)
      (targetArguments := targetArguments)
      (runtimeType := concatRuntimeType) (members := members)
      (targetFieldDefinition := targetFieldDefinition)
      hmembers htargetLookup htargetComposite htargetNonObject
      hconcatRuntime
  exact ⟨concatRuntimeType, hconcatRuntime, hinclude⟩

theorem abstractRuntimeForFieldHeadDeep?_member_flatten_some
    {schema : Schema}
    {currentParent targetField targetRuntimeType : Name}
    {targetArguments : List Argument}
    {selectionSet : List Selection} {members : List (List Selection)}
    : selectionSet ∈ members
      -> abstractRuntimeForFieldHeadDeep? schema currentParent targetField
            targetArguments currentParent selectionSet
          = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldHeadDeep? schema currentParent targetField
            targetArguments currentParent (List.flatten members)
          = some runtimeType := by
  intro hmem hlocalRuntime
  induction members with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      simp at hmem
      rcases hmem with hhead | htail
      · subst selectionSet
        exact
          abstractRuntimeForFieldHeadDeep?_append_some_left_exists
            (schema := schema) (targetParent := currentParent)
            (targetField := targetField)
            (targetArguments := targetArguments)
            (currentParent := currentParent)
            (left := head) (right := List.flatten rest)
            hlocalRuntime
      · rcases ih htail with ⟨restRuntimeType, hrestRuntime⟩
        exact
          abstractRuntimeForFieldHeadDeep?_append_some_right_exists
            (schema := schema) (targetParent := currentParent)
            (targetField := targetField)
            (targetArguments := targetArguments)
            (currentParent := currentParent)
            (left := head) (right := List.flatten rest)
            hrestRuntime

theorem PathLocalSelectionSetHeadReady.member_flatten_of_sound
    {schema : Schema} {currentParent : Name}
    {selectionSet : List Selection} {members : List (List Selection)}
    : PathLocalCurrentRuntimeSound schema (currentParent, List.flatten members)
      -> selectionSet ∈ members
      -> PathLocalSelectionSetHeadReady schema currentParent selectionSet selectionSet
      -> PathLocalSelectionSetHeadReady schema currentParent
          (List.flatten members) selectionSet := by
  intro hsound hmember hlocalReady responseName fieldName arguments
    directives childSelectionSet fieldDefinition hfieldMem hlookup
    hcomposite hnonObject
  rcases
      hlocalReady responseName fieldName arguments directives
        childSelectionSet fieldDefinition hfieldMem hlookup hcomposite
        hnonObject with
    ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
  rcases
      abstractRuntimeForFieldHeadDeep?_member_flatten_some
        (schema := schema) (currentParent := currentParent)
        (targetField := fieldName) (targetArguments := arguments)
        (selectionSet := selectionSet) (members := members)
        hmember hlocalRuntime with
    ⟨runtimeType, hruntime⟩
  exact
    ⟨runtimeType, hruntime,
      hsound currentParent fieldName runtimeType arguments fieldDefinition
        hlookup hcomposite hnonObject hruntime⟩

theorem PathLocalSelectionSetHeadReady.selection_in_member_flatten_of_sound
    {schema : Schema} {currentParent : Name}
    {memberRoot selectionSet : List Selection}
    {members : List (List Selection)}
    : PathLocalCurrentRuntimeSound schema (currentParent, List.flatten members)
      -> memberRoot ∈ members
      -> PathLocalSelectionSetHeadReady schema currentParent memberRoot selectionSet
      -> PathLocalSelectionSetHeadReady schema currentParent
          (List.flatten members) selectionSet := by
  intro hsound hmember hlocalReady responseName fieldName arguments
    directives childSelectionSet fieldDefinition hfieldMem hlookup
    hcomposite hnonObject
  rcases
      hlocalReady responseName fieldName arguments directives
        childSelectionSet fieldDefinition hfieldMem hlookup hcomposite
        hnonObject with
    ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
  rcases
      abstractRuntimeForFieldHeadDeep?_member_flatten_some
        (schema := schema) (currentParent := currentParent)
        (targetField := fieldName) (targetArguments := arguments)
        (selectionSet := memberRoot) (members := members)
        hmember hlocalRuntime with
    ⟨runtimeType, hruntime⟩
  exact
    ⟨runtimeType, hruntime,
      hsound currentParent fieldName runtimeType arguments fieldDefinition
        hlookup hcomposite hnonObject hruntime⟩

theorem abstractRuntimeForFieldHeadDeep?_append_context_some
    {schema : Schema}
    {currentParent targetField targetRuntimeType : Name}
    {targetArguments : List Argument}
    {pref selectionSet suff : List Selection}
    : abstractRuntimeForFieldHeadDeep? schema currentParent targetField
          targetArguments currentParent selectionSet
        = some targetRuntimeType
      -> ∃ runtimeType,
          abstractRuntimeForFieldHeadDeep? schema currentParent targetField
            targetArguments currentParent (pref ++ selectionSet ++ suff)
          = some runtimeType := by
  intro hlocalRuntime
  rcases
      abstractRuntimeForFieldHeadDeep?_append_some_left_exists
        (schema := schema) (targetParent := currentParent)
        (targetField := targetField)
        (targetArguments := targetArguments)
        (currentParent := currentParent)
        (left := selectionSet) (right := suff)
        hlocalRuntime with
    ⟨rightRuntimeType, hrightRuntime⟩
  rcases
      abstractRuntimeForFieldHeadDeep?_append_some_right_exists
        (schema := schema) (targetParent := currentParent)
        (targetField := targetField)
        (targetArguments := targetArguments)
        (currentParent := currentParent)
        (left := pref) (right := selectionSet ++ suff)
        hrightRuntime with
    ⟨runtimeType, hruntime⟩
  exact ⟨runtimeType, by simpa [List.append_assoc] using hruntime⟩

theorem PathLocalSelectionSetHeadReady.append_context_of_sound
    {schema : Schema} {currentParent : Name}
    {pref selectionSet suff : List Selection}
    : PathLocalCurrentRuntimeSound schema (currentParent, pref ++ selectionSet ++ suff)
      -> PathLocalSelectionSetHeadReady schema currentParent selectionSet selectionSet
      -> PathLocalSelectionSetHeadReady schema currentParent
          (pref ++ selectionSet ++ suff) selectionSet := by
  intro hsound hlocalReady responseName fieldName arguments directives
    childSelectionSet fieldDefinition hfieldMem hlookup hcomposite
    hnonObject
  rcases
      hlocalReady responseName fieldName arguments directives
        childSelectionSet fieldDefinition hfieldMem hlookup hcomposite
        hnonObject with
    ⟨localRuntimeType, hlocalRuntime, _hlocalInclude⟩
  rcases
      abstractRuntimeForFieldHeadDeep?_append_context_some
        (schema := schema) (currentParent := currentParent)
        (targetField := fieldName) (targetArguments := arguments)
        (pref := pref) (selectionSet := selectionSet) (suff := suff)
        hlocalRuntime with
    ⟨runtimeType, hruntime⟩
  exact
    ⟨runtimeType, hruntime,
      hsound currentParent fieldName runtimeType arguments fieldDefinition
        hlookup hcomposite hnonObject hruntime⟩

theorem PathLocalSelectionSetCurrentContext.self {selectionSet : List Selection}
    : PathLocalSelectionSetCurrentContext selectionSet selectionSet := by
  exact ⟨[], [], by simp⟩

theorem PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name}
    {selectionSet currentSelectionSet : List Selection}
    : PathLocalCurrentRuntimeSound schema (parentType, currentSelectionSet)
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> PathLocalSelectionSetHeadReady schema parentType currentSelectionSet
          selectionSet := by
  intro hsound hcontext hvalid hnormal
  rcases hcontext with ⟨pref, suff, hcurrent⟩
  subst currentSelectionSet
  exact
    PathLocalSelectionSetHeadReady.append_context_of_sound
      (by simpa using hsound)
      (PathLocalSelectionSetHeadReady.of_valid_normal_self hvalid hnormal)

theorem PathLocalSelectionSetCurrentContext.trans {inner middle outer : List Selection}
    : PathLocalSelectionSetCurrentContext inner middle
      -> PathLocalSelectionSetCurrentContext middle outer
      -> PathLocalSelectionSetCurrentContext inner outer := by
  intro hinner houter
  rcases hinner with ⟨innerPref, innerSuff, hmiddle⟩
  rcases houter with ⟨outerPref, outerSuff, houterEq⟩
  subst middle
  subst outer
  refine
    ⟨outerPref ++ innerPref, innerSuff ++ outerSuff, ?_⟩
  simp [List.append_assoc]

theorem abstractRuntimeForFieldHeadDeep?_append_some_include_of_sound
    {schema : Schema}
    {currentParent targetParent targetField runtimeType : Name}
    {targetArguments : List Argument}
    {left right : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : (∀ leftRuntimeType,
        abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent left
          = some leftRuntimeType
        -> schema.typeIncludesObjectBool
              targetFieldDefinition.outputType.namedType leftRuntimeType
            = true)
      -> (∀ rightRuntimeType,
            abstractRuntimeForFieldHeadDeep? schema targetParent targetField
                targetArguments currentParent right
              = some rightRuntimeType
            -> schema.typeIncludesObjectBool
                  targetFieldDefinition.outputType.namedType rightRuntimeType
                = true)
      -> abstractRuntimeForFieldHeadDeep? schema targetParent targetField
            targetArguments currentParent (left ++ right)
          = some runtimeType
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType runtimeType
          = true := by
  intro hleftInclude hrightInclude happendedRuntime
  induction left generalizing currentParent runtimeType with
  | nil =>
      exact hrightInclude runtimeType
        (by simpa [abstractRuntimeForFieldHeadDeep?] using happendedRuntime)
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
          | some headRuntimeType =>
              have hleftRuntime :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments currentParent
                    (Selection.field responseName fieldName arguments
                      directives childSelectionSet :: tail) =
                    some headRuntimeType := by
                simp [abstractRuntimeForFieldHeadDeep?, hcurrent]
              have hruntimeEq : headRuntimeType = runtimeType := by
                simpa [abstractRuntimeForFieldHeadDeep?, hcurrent] using
                  happendedRuntime
              subst runtimeType
              exact hleftInclude headRuntimeType hleftRuntime
          | none =>
              cases happTail :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments currentParent
                    (tail ++ right) with
              | some tailRuntimeType =>
                  have hruntimeEq : tailRuntimeType = runtimeType := by
                    simpa [abstractRuntimeForFieldHeadDeep?, hcurrent,
                      happTail] using happendedRuntime
                  subst runtimeType
                  have htailInclude :
                      ∀ tailRuntimeType,
                        abstractRuntimeForFieldHeadDeep? schema targetParent
                            targetField targetArguments currentParent tail =
                          some tailRuntimeType ->
                        schema.typeIncludesObjectBool
                            targetFieldDefinition.outputType.namedType
                            tailRuntimeType =
                          true := by
                    intro tailRuntimeType htailRuntime
                    exact
                      hleftInclude tailRuntimeType
                        (by
                          simp [abstractRuntimeForFieldHeadDeep?, hcurrent,
                            htailRuntime])
                  exact ih htailInclude hrightInclude happTail
              | none =>
                  cases hlookupHead :
                      schema.lookupField currentParent fieldName with
                  | none =>
                      simp [abstractRuntimeForFieldHeadDeep?, hcurrent,
                        happTail, hlookupHead] at happendedRuntime
                  | some fieldDefinition =>
                      cases htailAlone :
                          abstractRuntimeForFieldHeadDeep? schema
                            targetParent targetField targetArguments
                            currentParent tail with
                      | some tailRuntimeType =>
                          rcases
                              abstractRuntimeForFieldHeadDeep?_append_some_left_exists
                                (schema := schema)
                                (targetParent := targetParent)
                                (targetField := targetField)
                                (targetArguments := targetArguments)
                                (currentParent := currentParent)
                                (left := tail) (right := right)
                                htailAlone with
                            ⟨appendedRuntimeType, happended⟩
                          rw [happTail] at happended
                          cases happended
                      | none =>
                          have hchildRuntime :
                              abstractRuntimeForFieldHeadDeep? schema
                                targetParent targetField targetArguments
                                fieldDefinition.outputType.namedType
                                childSelectionSet =
                              some runtimeType := by
                            simpa [abstractRuntimeForFieldHeadDeep?,
                              hcurrent, happTail, hlookupHead] using
                              happendedRuntime
                          have hchildInclude :
                              ∀ childRuntimeType,
                                abstractRuntimeForFieldHeadDeep? schema
                                    targetParent targetField targetArguments
                                    fieldDefinition.outputType.namedType
                                    childSelectionSet =
                                  some childRuntimeType ->
                                schema.typeIncludesObjectBool
                                    targetFieldDefinition.outputType.namedType
                                    childRuntimeType =
                                  true := by
                            intro childRuntimeType hchildRuntime
                            exact
                              hleftInclude childRuntimeType
                                (by
                                  simp [abstractRuntimeForFieldHeadDeep?,
                                    hcurrent, htailAlone, hlookupHead,
                                    hchildRuntime])
                          exact hchildInclude runtimeType hchildRuntime
      | inlineFragment typeCondition directives childSelectionSet =>
          cases happTail :
              abstractRuntimeForFieldHeadDeep? schema targetParent targetField
                targetArguments currentParent (tail ++ right) with
          | some tailRuntimeType =>
              have hruntimeEq : tailRuntimeType = runtimeType := by
                cases typeCondition <;>
                  simpa [abstractRuntimeForFieldHeadDeep?, happTail] using
                    happendedRuntime
              subst runtimeType
              have htailInclude :
                  ∀ tailRuntimeType,
                    abstractRuntimeForFieldHeadDeep? schema targetParent
                        targetField targetArguments currentParent tail =
                      some tailRuntimeType ->
                    schema.typeIncludesObjectBool
                        targetFieldDefinition.outputType.namedType
                        tailRuntimeType =
                      true := by
                intro tailRuntimeType htailRuntime
                exact
                  hleftInclude tailRuntimeType
                    (by
                      cases typeCondition <;>
                        simp [abstractRuntimeForFieldHeadDeep?,
                          htailRuntime])
              exact ih htailInclude hrightInclude happTail
          | none =>
              cases htailAlone :
                  abstractRuntimeForFieldHeadDeep? schema targetParent
                    targetField targetArguments currentParent tail with
              | some tailRuntimeType =>
                  rcases
                      abstractRuntimeForFieldHeadDeep?_append_some_left_exists
                        (schema := schema) (targetParent := targetParent)
                        (targetField := targetField)
                        (targetArguments := targetArguments)
                        (currentParent := currentParent)
                        (left := tail) (right := right) htailAlone with
                    ⟨appendedRuntimeType, happended⟩
                  rw [happTail] at happended
                  cases happended
              | none =>
                  cases typeCondition with
                  | none =>
                      have hchildRuntime :
                          abstractRuntimeForFieldHeadDeep? schema
                            targetParent targetField targetArguments
                            currentParent childSelectionSet =
                          some runtimeType := by
                        simpa [abstractRuntimeForFieldHeadDeep?, happTail]
                          using happendedRuntime
                      have hchildInclude :
                          ∀ childRuntimeType,
                            abstractRuntimeForFieldHeadDeep? schema
                                targetParent targetField targetArguments
                                currentParent childSelectionSet =
                              some childRuntimeType ->
                            schema.typeIncludesObjectBool
                                targetFieldDefinition.outputType.namedType
                                childRuntimeType =
                              true := by
                        intro childRuntimeType hchildRuntime
                        exact
                          hleftInclude childRuntimeType
                            (by
                              simp [abstractRuntimeForFieldHeadDeep?,
                                htailAlone, hchildRuntime])
                      exact hchildInclude runtimeType hchildRuntime
                  | some typeCondition =>
                      have hchildRuntime :
                          abstractRuntimeForFieldHeadDeep? schema
                            targetParent targetField targetArguments
                            typeCondition childSelectionSet =
                          some runtimeType := by
                        simpa [abstractRuntimeForFieldHeadDeep?, happTail]
                          using happendedRuntime
                      have hchildInclude :
                          ∀ childRuntimeType,
                            abstractRuntimeForFieldHeadDeep? schema
                                targetParent targetField targetArguments
                                typeCondition childSelectionSet =
                              some childRuntimeType ->
                            schema.typeIncludesObjectBool
                                targetFieldDefinition.outputType.namedType
                                childRuntimeType =
                              true := by
                        intro childRuntimeType hchildRuntime
                        exact
                          hleftInclude childRuntimeType
                            (by
                              simp [abstractRuntimeForFieldHeadDeep?,
                                htailAlone, hchildRuntime])
                      exact hchildInclude runtimeType hchildRuntime

theorem PathLocalCurrentRuntimeSound.append
    {schema : Schema} {currentParent : Name}
    {left right : List Selection}
    : PathLocalCurrentRuntimeSound schema (currentParent, left)
      -> PathLocalCurrentRuntimeSound schema (currentParent, right)
      -> PathLocalCurrentRuntimeSound schema (currentParent, left ++ right) := by
  intro hleft hright targetParent targetField runtimeType targetArguments
    targetFieldDefinition hlookup hcomposite hnonObject hruntime
  exact
    abstractRuntimeForFieldHeadDeep?_append_some_include_of_sound
      (schema := schema) (currentParent := currentParent)
      (targetParent := targetParent) (targetField := targetField)
      (targetArguments := targetArguments) (runtimeType := runtimeType)
      (left := left) (right := right)
      (targetFieldDefinition := targetFieldDefinition)
      (fun leftRuntimeType hleftRuntime =>
        hleft targetParent targetField leftRuntimeType targetArguments
          targetFieldDefinition hlookup hcomposite hnonObject hleftRuntime)
      (fun rightRuntimeType hrightRuntime =>
        hright targetParent targetField rightRuntimeType targetArguments
          targetFieldDefinition hlookup hcomposite hnonObject hrightRuntime)
      hruntime

theorem PathLocalCurrentRuntimeSound.flatten
    {schema : Schema} {currentParent : Name}
    {members : List (List Selection)}
    : (∀ memberSelectionSet,
        memberSelectionSet ∈ members
        -> PathLocalCurrentRuntimeSound schema (currentParent, memberSelectionSet))
      -> PathLocalCurrentRuntimeSound schema (currentParent, List.flatten members) := by
  intro hmembers
  induction members with
  | nil =>
      intro targetParent targetField runtimeType targetArguments
        targetFieldDefinition _hlookup _hcomposite _hnonObject hruntime
      simp [abstractRuntimeForFieldHeadDeep?] at hruntime
  | cons member rest ih =>
      have hmember :
          PathLocalCurrentRuntimeSound schema (currentParent, member) :=
        hmembers member (by simp)
      have hrest :
          PathLocalCurrentRuntimeSound schema
            (currentParent, List.flatten rest) :=
        ih (by
          intro restMember hrestMem
          exact hmembers restMember
            (List.mem_cons_of_mem member hrestMem))
      simpa [List.flatten_cons] using
        (PathLocalCurrentRuntimeSound.append hmember hrest)

theorem PathLocalCurrentRuntimeSound.append_valid_normal_left
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentParent : Name} {left right : List Selection}
    : Validation.selectionSetValid schema variableDefinitions currentParent left
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema currentParent left
      -> PathLocalCurrentRuntimeSound schema (currentParent, right)
      -> PathLocalCurrentRuntimeSound schema (currentParent, left ++ right) := by
  intro hleftValid hleftFree hleftNormal hrightSound targetParent
    targetField runtimeType targetArguments targetFieldDefinition hlookup
    hcomposite hnonObject hruntime
  exact
    abstractRuntimeForFieldHeadDeep?_append_some_include_of_valid_normal_or_right
      hleftValid hleftFree hleftNormal
      (by
        intro rightRuntime hrightRuntime
        exact
          hrightSound targetParent targetField rightRuntime
            targetArguments targetFieldDefinition hlookup hcomposite
            hnonObject hrightRuntime)
      hlookup hcomposite hnonObject hruntime

theorem PathLocalCurrentRuntimeSound.flatten_valid_normal_members
    {schema : Schema} {currentParent : Name}
    {members : List (List Selection)}
    : (∀ memberSelectionSet,
        memberSelectionSet ∈ members
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions
              currentParent memberSelectionSet
            ∧ selectionSetDirectiveFree memberSelectionSet
            ∧ selectionSetNormal schema currentParent memberSelectionSet)
      -> PathLocalCurrentRuntimeSound schema (currentParent, List.flatten members) := by
  intro hmembers targetParent targetField runtimeType targetArguments
    targetFieldDefinition hlookup hcomposite hnonObject hruntime
  exact
    abstractRuntimeForFieldHeadDeep?_join_some_include_of_valid_normal_members
      (schema := schema) (currentParent := currentParent)
      (targetParent := targetParent) (targetField := targetField)
      (targetArguments := targetArguments) (runtimeType := runtimeType)
      (members := members) (targetFieldDefinition := targetFieldDefinition)
      hmembers hlookup hcomposite hnonObject hruntime

theorem PathLocalSupportValidNormal.of_valid_normal_self
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> PathLocalSupportValidNormal schema parentType selectionSet := by
  intro hvalid hfree hnormal
  refine ⟨[selectionSet], by simp, ?_⟩
  intro memberSelectionSet hmember
  simp at hmember
  subst memberSelectionSet
  exact ⟨variableDefinitions, hvalid, hfree, hnormal⟩

theorem PathLocalSupportValidNormal.sound
    {schema : Schema} {parentType : Name}
    {currentSelectionSet : List Selection}
    : PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> PathLocalCurrentRuntimeSound schema (parentType, currentSelectionSet) := by
  intro hsupport
  rcases hsupport with ⟨members, hcurrent, hmembers⟩
  subst currentSelectionSet
  exact
    PathLocalCurrentRuntimeSound.flatten_valid_normal_members hmembers

theorem pathLocalCompositeFieldRuntime_of_valid_normal_support_context
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet currentSelectionSet childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ runtimeType,
          (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ runtimeType = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                      fieldName arguments parentType currentSelectionSet
                    = some runtimeType))
            ∧ schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType runtimeType
              = true) := by
  intro hvalid hnormal hsupport hcontext hmem hlookup hcomposite
  by_cases hobject :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true
  · exact
      ⟨fieldDefinition.outputType.namedType, Or.inl ⟨hobject, rfl⟩,
        typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject⟩
  · have hnonObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          false := by
      cases h :
          objectTypeNameBool schema fieldDefinition.outputType.namedType
      · rfl
      · exact False.elim (hobject h)
    have hready :
        PathLocalSelectionSetHeadReady schema parentType
          currentSelectionSet selectionSet :=
      PathLocalSelectionSetCurrentContext.headReady_of_valid_normal
        hsupport.sound hcontext hvalid hnormal
    rcases
        hready responseName fieldName arguments directives childSelectionSet
          fieldDefinition hmem hlookup hcomposite hnonObject with
      ⟨runtimeType, hruntime, hinclude⟩
    exact
      ⟨runtimeType, Or.inr ⟨hcomposite, hnonObject, hruntime⟩,
        hinclude⟩

theorem PathLocalSupportValidNormal.allFields_of_object
    {schema : Schema} {parentType : Name}
    {currentSelectionSet : List Selection}
    : PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> objectTypeNameBool schema parentType = true
      -> selectionsAllFields currentSelectionSet := by
  intro hsupport hobject selection hselectionMem
  rcases hsupport with ⟨members, hcurrent, hmembers⟩
  subst currentSelectionSet
  rcases List.mem_flatten.mp hselectionMem with
    ⟨memberSelectionSet, hmember, hselectionInMember⟩
  rcases hmembers memberSelectionSet hmember with
    ⟨_variableDefinitions, _hvalid, _hfree, hnormal⟩
  exact
    selectionSetNormal_allFields_of_object hnormal hobject selection
      hselectionInMember

theorem PathLocalSupportValidNormal.append_valid_normal_left
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType left
      -> selectionSetDirectiveFree left
      -> selectionSetNormal schema parentType left
      -> PathLocalSupportValidNormal schema parentType right
      -> PathLocalSupportValidNormal schema parentType (left ++ right) := by
  intro hleftValid hleftFree hleftNormal hrightSupport
  rcases hrightSupport with ⟨rightMembers, hright, hrightMembers⟩
  subst right
  refine ⟨left :: rightMembers, by simp, ?_⟩
  intro memberSelectionSet hmember
  rcases List.mem_cons.mp hmember with hleft | hrightMember
  · subst memberSelectionSet
    exact ⟨variableDefinitions, hleftValid, hleftFree, hleftNormal⟩
  · exact hrightMembers memberSelectionSet hrightMember

theorem PathLocalSupportValidNormal.append
    {schema : Schema} {parentType : Name}
    {left right : List Selection}
    : PathLocalSupportValidNormal schema parentType left
      -> PathLocalSupportValidNormal schema parentType right
      -> PathLocalSupportValidNormal schema parentType (left ++ right) := by
  intro hleftSupport hrightSupport
  rcases hleftSupport with ⟨leftMembers, hleft, hleftMembers⟩
  rcases hrightSupport with ⟨rightMembers, hright, hrightMembers⟩
  subst left
  subst right
  refine ⟨leftMembers ++ rightMembers, by simp, ?_⟩
  intro memberSelectionSet hmember
  rcases List.mem_append.mp hmember with hleftMember | hrightMember
  · exact hleftMembers memberSelectionSet hleftMember
  · exact hrightMembers memberSelectionSet hrightMember

theorem PathLocalSupportValidNormal.flatten
    {schema : Schema} {parentType : Name}
    {members : List (List Selection)}
    : (∀ memberSelectionSet,
        memberSelectionSet ∈ members
        -> PathLocalSupportValidNormal schema parentType memberSelectionSet)
      -> PathLocalSupportValidNormal schema parentType (List.flatten members) := by
  intro hmembers
  induction members with
  | nil =>
      refine ⟨[], by simp, ?_⟩
      intro memberSelectionSet hmember
      simp at hmember
  | cons memberSelectionSet rest ih =>
      simp [List.flatten]
      exact
        PathLocalSupportValidNormal.append
          (hmembers memberSelectionSet (by simp))
          (ih (by
            intro restMember hrestMember
            exact hmembers restMember (List.mem_cons_of_mem _ hrestMember)))

theorem PathLocalSupportValidNormal.runtimePruned_of_valid_normal_runtime
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType runtimeType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> schema.typeIncludesObjectBool parentType runtimeType = true
      -> objectTypeNameBool schema runtimeType = true
      -> PathLocalSupportValidNormal schema runtimeType
          (runtimePrunedSelectionSet schema runtimeType selectionSet) := by
  revert parentType runtimeType variableDefinitions
  induction selectionSet with
  | nil =>
      intro variableDefinitions parentType runtimeType _hvalid _hfree
        _hnormal _hinclude _hruntimeObject
      refine ⟨[], by simp [runtimePrunedSelectionSet], ?_⟩
      intro memberSelectionSet hmember
      simp at hmember
  | cons selection rest ih =>
      intro variableDefinitions parentType runtimeType hvalid hfree hnormal
        hinclude hruntimeObject
      by_cases hparentObject : objectTypeNameBool schema parentType = true
      · have hruntimeEq : runtimeType = parentType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hparentObject hinclude
        subst runtimeType
        have hallFields :
            selectionsAllFields (selection :: rest) :=
          selectionSetNormal_allFields_of_object hnormal hparentObject
        have hpruned :
            runtimePrunedSelectionSet schema parentType (selection :: rest) =
              selection :: rest :=
          runtimePrunedSelectionSet_eq_self_of_allFields schema parentType
            hallFields
        rw [hpruned]
        exact
          PathLocalSupportValidNormal.of_valid_normal_self hvalid hfree
            hnormal
      · have htailValid :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        have htailFree : selectionSetDirectiveFree rest :=
          selectionSetDirectiveFree_tail hfree
        have htailNormal : selectionSetNormal schema parentType rest :=
          selectionSetNormal_tail hnormal
        have htailSupport :
            PathLocalSupportValidNormal schema runtimeType
              (runtimePrunedSelectionSet schema runtimeType rest) :=
          ih htailValid htailFree htailNormal hinclude hruntimeObject
        have hparentObjectFalse :
            objectTypeNameBool schema parentType = false := by
          cases h : objectTypeNameBool schema parentType
          · rfl
          · exact False.elim (hparentObject h)
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            have hallInline :
                selectionsAllInlineFragments
                  (Selection.field responseName fieldName arguments
                    directives childSelectionSet :: rest) :=
              selectionSetNormal_allInlineFragments_of_abstract hnormal
                hparentObjectFalse
            have hheadInline :
                Selection.isInlineFragment
                  (Selection.field responseName fieldName arguments
                    directives childSelectionSet) :=
              hallInline
                (Selection.field responseName fieldName arguments directives
                  childSelectionSet) (by simp)
            simp [Selection.isInlineFragment] at hheadInline
        | inlineFragment typeCondition directives childSelectionSet =>
            cases typeCondition with
            | none =>
                have hselectionGround :
                    selectionGroundTyped schema parentType
                      (Selection.inlineFragment none directives
                        childSelectionSet) := by
                  have hground := hnormal.1
                  unfold selectionSetGroundTyped at hground
                  exact hground.2
                    (Selection.inlineFragment none directives
                      childSelectionSet) (by simp)
                simp [selectionGroundTyped] at hselectionGround
            | some typeCondition =>
                by_cases hincludes :
                    schema.typeIncludesObjectBool typeCondition runtimeType
                · have hchildNormalFacts :=
                    selectionSetNormal_inlineFragment_child_of_mem hnormal
                      (by simp :
                        Selection.inlineFragment (some typeCondition)
                            directives childSelectionSet ∈
                          Selection.inlineFragment (some typeCondition)
                            directives childSelectionSet :: rest)
                  have hheadMem :
                      Selection.inlineFragment (some typeCondition)
                          directives childSelectionSet ∈
                        Selection.inlineFragment (some typeCondition)
                          directives childSelectionSet :: rest := by
                    simp
                  have htypeConditionObjectBool :
                      objectTypeNameBool schema typeCondition = true :=
                    objectTypeNameBool_eq_true_of_objectType_base schema
                      hchildNormalFacts.1
                  have hruntimeEqTypeCondition :
                      runtimeType = typeCondition :=
                    typeIncludesObjectBool_eq_of_objectTypeNameBool_true
                      schema htypeConditionObjectBool hincludes
                  subst runtimeType
                  have hchildValid :
                      Validation.selectionSetValid schema variableDefinitions
                        typeCondition childSelectionSet :=
                    selectionSetValid_inlineFragment_some_child_of_mem hvalid
                      hheadMem
                  have hchildFree :
                      selectionSetDirectiveFree childSelectionSet :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hfree hheadMem
                  have hchildNormal :
                      selectionSetNormal schema typeCondition
                        childSelectionSet :=
                    hchildNormalFacts.2
                  have hchildAllFields :
                      selectionsAllFields childSelectionSet :=
                    selectionSetNormal_allFields_of_object hchildNormal
                      htypeConditionObjectBool
                  have hchildPruned :
                      runtimePrunedSelectionSet schema typeCondition
                          childSelectionSet =
                        childSelectionSet :=
                    runtimePrunedSelectionSet_eq_self_of_allFields schema
                      typeCondition hchildAllFields
                  simp [runtimePrunedSelectionSet, hincludes, hchildPruned]
                  exact
                    PathLocalSupportValidNormal.append_valid_normal_left
                      hchildValid hchildFree hchildNormal htailSupport
                · simpa [runtimePrunedSelectionSet, hincludes] using
                    htailSupport

theorem PathLocalCurrentRuntimeSound.runtimePruned_of_valid_normal_runtime
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType runtimeType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> schema.typeIncludesObjectBool parentType runtimeType = true
      -> objectTypeNameBool schema runtimeType = true
      -> PathLocalCurrentRuntimeSound schema
          (runtimeType, runtimePrunedSelectionSet schema runtimeType selectionSet) := by
  revert parentType runtimeType variableDefinitions
  induction selectionSet with
  | nil =>
      intro variableDefinitions parentType runtimeType _hvalid _hfree
        _hnormal _hinclude _hruntimeObject
      intro targetParent targetField runtimeType' targetArguments
        targetFieldDefinition _hlookup _hcomposite _hnonObject hruntime
      simp [runtimePrunedSelectionSet, abstractRuntimeForFieldHeadDeep?]
        at hruntime
  | cons selection rest ih =>
      intro variableDefinitions parentType runtimeType hvalid hfree hnormal
        hinclude hruntimeObject
      by_cases hparentObject : objectTypeNameBool schema parentType = true
      · have hruntimeEq : runtimeType = parentType :=
          typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
            hparentObject hinclude
        subst runtimeType
        have hallFields :
            selectionsAllFields (selection :: rest) :=
          selectionSetNormal_allFields_of_object hnormal hparentObject
        have hpruned :
            runtimePrunedSelectionSet schema parentType (selection :: rest) =
              selection :: rest :=
          runtimePrunedSelectionSet_eq_self_of_allFields schema parentType
            hallFields
        rw [hpruned]
        exact
          PathLocalCurrentRuntimeSound.of_valid_normal hvalid hfree hnormal
      · have htailValid :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        have htailFree : selectionSetDirectiveFree rest :=
          selectionSetDirectiveFree_tail hfree
        have htailNormal : selectionSetNormal schema parentType rest :=
          selectionSetNormal_tail hnormal
        have htailSound :
            PathLocalCurrentRuntimeSound schema
              (runtimeType, runtimePrunedSelectionSet schema runtimeType
                rest) :=
          ih htailValid htailFree htailNormal hinclude hruntimeObject
        have hparentObjectFalse :
            objectTypeNameBool schema parentType = false := by
          cases h : objectTypeNameBool schema parentType
          · rfl
          · exact False.elim (hparentObject h)
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            have hallInline :
                selectionsAllInlineFragments
                  (Selection.field responseName fieldName arguments
                    directives childSelectionSet :: rest) :=
              selectionSetNormal_allInlineFragments_of_abstract hnormal
                hparentObjectFalse
            have hheadInline :
                Selection.isInlineFragment
                  (Selection.field responseName fieldName arguments
                    directives childSelectionSet) :=
              hallInline
                (Selection.field responseName fieldName arguments directives
                  childSelectionSet) (by simp)
            simp [Selection.isInlineFragment] at hheadInline
        | inlineFragment typeCondition directives childSelectionSet =>
            cases typeCondition with
            | none =>
                have hselectionGround :
                    selectionGroundTyped schema parentType
                      (Selection.inlineFragment none directives
                        childSelectionSet) := by
                  have hground := hnormal.1
                  unfold selectionSetGroundTyped at hground
                  exact hground.2
                    (Selection.inlineFragment none directives
                      childSelectionSet) (by simp)
                simp [selectionGroundTyped] at hselectionGround
            | some typeCondition =>
                by_cases hincludes :
                    schema.typeIncludesObjectBool typeCondition runtimeType
                · have hchildNormalFacts :=
                    selectionSetNormal_inlineFragment_child_of_mem hnormal
                      (by simp :
                        Selection.inlineFragment (some typeCondition)
                            directives childSelectionSet ∈
                          Selection.inlineFragment (some typeCondition)
                            directives childSelectionSet :: rest)
                  have hheadMem :
                      Selection.inlineFragment (some typeCondition)
                          directives childSelectionSet ∈
                        Selection.inlineFragment (some typeCondition)
                          directives childSelectionSet :: rest := by
                    simp
                  have htypeConditionObjectBool :
                      objectTypeNameBool schema typeCondition = true :=
                    objectTypeNameBool_eq_true_of_objectType_base schema
                      hchildNormalFacts.1
                  have hruntimeEqTypeCondition :
                      runtimeType = typeCondition :=
                    typeIncludesObjectBool_eq_of_objectTypeNameBool_true
                      schema htypeConditionObjectBool hincludes
                  subst runtimeType
                  have hchildValid :
                      Validation.selectionSetValid schema variableDefinitions
                        typeCondition childSelectionSet :=
                    selectionSetValid_inlineFragment_some_child_of_mem hvalid
                      hheadMem
                  have hchildFree :
                      selectionSetDirectiveFree childSelectionSet :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hfree hheadMem
                  have hchildNormal :
                      selectionSetNormal schema typeCondition
                        childSelectionSet :=
                    hchildNormalFacts.2
                  have hchildAllFields :
                      selectionsAllFields childSelectionSet :=
                    selectionSetNormal_allFields_of_object hchildNormal
                      htypeConditionObjectBool
                  have hchildPruned :
                      runtimePrunedSelectionSet schema typeCondition
                          childSelectionSet =
                        childSelectionSet :=
                    runtimePrunedSelectionSet_eq_self_of_allFields schema
                      typeCondition hchildAllFields
                  simp [runtimePrunedSelectionSet, hincludes,
                    hchildPruned]
                  exact
                    PathLocalCurrentRuntimeSound.append_valid_normal_left
                      hchildValid hchildFree hchildNormal htailSound
                · simpa [runtimePrunedSelectionSet, hincludes] using
                    htailSound

theorem fieldChildMembersByHeadAtRuntime_sound_of_valid_normal_object
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentRuntimeType childRuntimeType targetField : Name}
    {targetArguments : List Argument}
    {currentSelectionSet memberSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentRuntimeType
        currentSelectionSet
      -> selectionSetDirectiveFree currentSelectionSet
      -> selectionSetNormal schema currentRuntimeType currentSelectionSet
      -> objectTypeNameBool schema currentRuntimeType = true
      -> objectTypeNameBool schema childRuntimeType = true
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType childRuntimeType
          = true
      -> memberSelectionSet
          ∈ fieldChildMembersByHeadAtRuntime schema currentRuntimeType
              childRuntimeType targetField targetArguments currentSelectionSet
      -> PathLocalCurrentRuntimeSound schema (childRuntimeType, memberSelectionSet) := by
  intro hvalid hfree hnormal hcurrentObject hchildObject htargetLookup
    hinclude hmember
  induction currentSelectionSet with
  | nil =>
      simp [fieldChildMembersByHeadAtRuntime] at hmember
  | cons selection rest ih =>
      have htailValid :
          Validation.selectionSetValid schema variableDefinitions
            currentRuntimeType rest :=
        Validation.selectionSetValid_tail hvalid
      have htailFree : selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have htailNormal : selectionSetNormal schema currentRuntimeType rest :=
        selectionSetNormal_tail hnormal
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          classical
          by_cases hfield : fieldName == targetField
          · by_cases harguments :
                Argument.argumentsEquivalent arguments targetArguments
            · simp [fieldChildMembersByHeadAtRuntime, hfield, harguments]
                at hmember
              rcases hmember with hhead | htail
              · subst memberSelectionSet
                have hfieldEq : fieldName = targetField := by
                  simpa using hfield
                subst fieldName
                have hheadMem :
                    Selection.field responseName targetField arguments
                        directives childSelectionSet ∈
                      Selection.field responseName targetField arguments
                        directives childSelectionSet :: rest := by
                  simp
                rcases
                    selectionSetValid_field_lookup_leaf_or_composite_child
                      hvalid hheadMem with
                  ⟨fieldDefinition, hlookup, hkind⟩
                have hdefinitionEq :
                    fieldDefinition = targetFieldDefinition := by
                  rw [htargetLookup] at hlookup
                  exact Option.some.inj hlookup.symm
                subst fieldDefinition
                rcases hkind with hleaf | hcomposite
                · have hempty : childSelectionSet = [] := hleaf.2
                  subst childSelectionSet
                  intro nestedTargetParent nestedTargetField
                    nestedRuntimeType nestedTargetArguments
                    nestedTargetFieldDefinition _hnestedLookup
                    _hnestedComposite _hnestedNonObject hnestedRuntime
                  simp [runtimePrunedSelectionSet,
                    abstractRuntimeForFieldHeadDeep?] at hnestedRuntime
                · have hchildFree :
                      selectionSetDirectiveFree childSelectionSet :=
                    selectionSetDirectiveFree_field_child_of_mem hfree
                      hheadMem
                  have hchildNormal :
                      selectionSetNormal schema
                        targetFieldDefinition.outputType.namedType
                        childSelectionSet :=
                    selectionSetNormal_field_child_of_mem_lookup hnormal
                      hheadMem htargetLookup
                  exact
                    PathLocalCurrentRuntimeSound.runtimePruned_of_valid_normal_runtime
                      hcomposite.2.2 hchildFree hchildNormal hinclude
                      hchildObject
              · exact
                  ih htailValid htailFree htailNormal htail
            · simp [fieldChildMembersByHeadAtRuntime, hfield, harguments]
                at hmember
              exact ih htailValid htailFree htailNormal hmember
          · simp [fieldChildMembersByHeadAtRuntime, hfield] at hmember
            exact ih htailValid htailFree htailNormal hmember
      | inlineFragment typeCondition directives childSelectionSet =>
          have hallFields :
              selectionsAllFields
                (Selection.inlineFragment typeCondition directives
                  childSelectionSet :: rest) :=
            selectionSetNormal_allFields_of_object hnormal hcurrentObject
          have hheadField :
              Selection.isField
                (Selection.inlineFragment typeCondition directives
                  childSelectionSet) :=
            hallFields
              (Selection.inlineFragment typeCondition directives
                childSelectionSet) (by simp)
          simp [Selection.isField] at hheadField

theorem PathLocalCurrentRuntimeSound.fieldPairPathLocalNextSelectionSet_of_valid_normal_object
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentRuntimeType childRuntimeType targetField : Name}
    {targetArguments : List Argument} {currentSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentRuntimeType
        currentSelectionSet
      -> selectionSetDirectiveFree currentSelectionSet
      -> selectionSetNormal schema currentRuntimeType currentSelectionSet
      -> objectTypeNameBool schema currentRuntimeType = true
      -> objectTypeNameBool schema childRuntimeType = true
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType childRuntimeType
          = true
      -> PathLocalCurrentRuntimeSound schema
          (
            childRuntimeType,
            fieldPairPathLocalNextSelectionSet schema currentRuntimeType
              childRuntimeType targetField targetArguments
              currentSelectionSet
          ) := by
  intro hvalid hfree hnormal hcurrentObject hchildObject htargetLookup
    hinclude
  rw [fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime]
  exact
    PathLocalCurrentRuntimeSound.flatten
      (by
        intro memberSelectionSet hmember
        exact
          fieldChildMembersByHeadAtRuntime_sound_of_valid_normal_object
            hvalid hfree hnormal hcurrentObject hchildObject
            htargetLookup hinclude hmember)

theorem runtimePrunedSelectionSet_mem_fieldChildMembersByHeadAtRuntime_of_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> runtimePrunedSelectionSet schema childRuntimeType childSelectionSet
          ∈ fieldChildMembersByHeadAtRuntime schema currentRuntimeType
              childRuntimeType targetField targetArguments selectionSet := by
  intro hmem harguments
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons selection rest ih =>
      cases selection with
      | field headResponseName headFieldName headArguments headDirectives
          headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            simp [fieldChildMembersByHeadAtRuntime, harguments]
          · by_cases hfield : headFieldName == targetField
            · by_cases hheadArguments :
                  Argument.argumentsEquivalent headArguments targetArguments
              · simp [fieldChildMembersByHeadAtRuntime, hfield,
                  hheadArguments, ih htail]
              · simp [fieldChildMembersByHeadAtRuntime, hfield,
                  hheadArguments, ih htail]
            · simp [fieldChildMembersByHeadAtRuntime, hfield, ih htail]
      | inlineFragment typeCondition headDirectives headChildSelectionSet =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · cases typeCondition with
            | none =>
                simpa [fieldChildMembersByHeadAtRuntime] using
                  (List.mem_append_right
                    (fieldChildMembersByHeadAtRuntime schema
                      currentRuntimeType childRuntimeType targetField
                      targetArguments headChildSelectionSet)
                    (ih htail))
            | some typeCondition =>
                by_cases hincludes :
                    schema.typeIncludesObjectBool typeCondition
                      currentRuntimeType
                · simpa [fieldChildMembersByHeadAtRuntime, hincludes] using
                    (List.mem_append_right
                      (fieldChildMembersByHeadAtRuntime schema
                        currentRuntimeType childRuntimeType targetField
                        targetArguments headChildSelectionSet)
                      (by
                        simpa [fieldChildMembersByHeadAtRuntime, hincludes]
                          using ih htail))
                · simpa [fieldChildMembersByHeadAtRuntime, hincludes]
                    using ih htail

theorem fieldChildMembersByHeadAtRuntime_mem_exists_field_of_allFields
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField : Name}
    {targetArguments : List Argument}
    {currentSelectionSet memberSelectionSet : List Selection}
    : selectionsAllFields currentSelectionSet
      -> memberSelectionSet
          ∈ fieldChildMembersByHeadAtRuntime schema currentRuntimeType
              childRuntimeType targetField targetArguments currentSelectionSet
      -> ∃ responseName arguments directives childSelectionSet,
          Selection.field responseName targetField arguments directives childSelectionSet
            ∈ currentSelectionSet
          ∧ Argument.argumentsEquivalent arguments targetArguments
          ∧ memberSelectionSet
            = runtimePrunedSelectionSet schema childRuntimeType childSelectionSet := by
  intro hallFields hmember
  induction currentSelectionSet with
  | nil =>
      simp [fieldChildMembersByHeadAtRuntime] at hmember
  | cons selection rest ih =>
      have hrestAllFields : selectionsAllFields rest := by
        intro restSelection hrestMem
        exact hallFields restSelection (List.mem_cons_of_mem _ hrestMem)
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          by_cases hfield : fieldName == targetField
          · by_cases harguments :
                Argument.argumentsEquivalent arguments targetArguments
            · simp [fieldChildMembersByHeadAtRuntime, hfield, harguments]
                at hmember
              rcases hmember with hhead | htail
              · subst memberSelectionSet
                have hfieldEq : fieldName = targetField := by
                  simpa using hfield
                subst fieldName
                exact
                  ⟨responseName, arguments, directives, childSelectionSet,
                    by simp, harguments, rfl⟩
              · rcases ih hrestAllFields htail with
                  ⟨tailResponseName, tailArguments, tailDirectives,
                    tailChildSelectionSet, htailMem, htailArguments,
                    htailMember⟩
                exact
                  ⟨tailResponseName, tailArguments, tailDirectives,
                    tailChildSelectionSet, List.mem_cons_of_mem _ htailMem,
                    htailArguments, htailMember⟩
            · simp [fieldChildMembersByHeadAtRuntime, hfield, harguments]
                at hmember
              rcases ih hrestAllFields hmember with
                ⟨tailResponseName, tailArguments, tailDirectives,
                  tailChildSelectionSet, htailMem, htailArguments,
                  htailMember⟩
              exact
                ⟨tailResponseName, tailArguments, tailDirectives,
                  tailChildSelectionSet, List.mem_cons_of_mem _ htailMem,
                  htailArguments, htailMember⟩
          · simp [fieldChildMembersByHeadAtRuntime, hfield] at hmember
            rcases ih hrestAllFields hmember with
              ⟨tailResponseName, tailArguments, tailDirectives,
                tailChildSelectionSet, htailMem, htailArguments,
                htailMember⟩
            exact
              ⟨tailResponseName, tailArguments, tailDirectives,
                tailChildSelectionSet, List.mem_cons_of_mem _ htailMem,
                htailArguments, htailMember⟩
      | inlineFragment typeCondition directives childSelectionSet =>
          have hheadField :
              Selection.isField
                (Selection.inlineFragment typeCondition directives
                  childSelectionSet) :=
            hallFields
              (Selection.inlineFragment typeCondition directives
                childSelectionSet) (by simp)
          simp [Selection.isField] at hheadField

theorem PathLocalSupportValidNormal.field_child_object_valid_normal_of_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet currentSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : PathLocalSupportValidNormal schema currentRuntimeType currentSelectionSet
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ currentSelectionSet
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> objectTypeNameBool schema childRuntimeType = true
      -> targetFieldDefinition.outputType.namedType = childRuntimeType
      -> ∃ variableDefinitions,
          Validation.selectionSetValid schema variableDefinitions
            childRuntimeType childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema childRuntimeType childSelectionSet := by
  intro hsupport hfieldMem htargetLookup hchildObject houtputEq
  subst childRuntimeType
  rcases hsupport with ⟨members, hcurrent, hmembers⟩
  subst currentSelectionSet
  rcases List.mem_flatten.mp hfieldMem with
    ⟨memberSelectionSet, hmember, hfieldMemMember⟩
  rcases hmembers memberSelectionSet hmember with
    ⟨variableDefinitions, hvalid, hfree, hnormal⟩
  have hchildValid :
      Validation.selectionSetValid schema variableDefinitions
        targetFieldDefinition.outputType.namedType childSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hvalid
      hfieldMemMember htargetLookup hchildObject
  have hchildFree : selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hfree hfieldMemMember
  have hchildNormal :
      selectionSetNormal schema targetFieldDefinition.outputType.namedType
        childSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hnormal hfieldMemMember
      htargetLookup
  exact ⟨variableDefinitions, hchildValid, hchildFree, hchildNormal⟩

theorem PathLocalSupportValidNormal.field_child_valid_normal_of_mem_lookup
    {schema : Schema} {currentRuntimeType targetField responseName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet currentSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : PathLocalSupportValidNormal schema currentRuntimeType currentSelectionSet
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ currentSelectionSet
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ variableDefinitions,
          Validation.selectionSetValid schema variableDefinitions
            targetFieldDefinition.outputType.namedType childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema
              targetFieldDefinition.outputType.namedType childSelectionSet := by
  intro hsupport hfieldMem htargetLookup hcomposite
  rcases hsupport with ⟨members, hcurrent, hmembers⟩
  subst currentSelectionSet
  rcases List.mem_flatten.mp hfieldMem with
    ⟨memberSelectionSet, hmember, hfieldMemMember⟩
  rcases hmembers memberSelectionSet hmember with
    ⟨variableDefinitions, hvalid, hfree, hnormal⟩
  rcases
      selectionSetValid_field_lookup_leaf_or_composite_child hvalid
        hfieldMemMember with
    ⟨fieldDefinition, hlookup, hkind⟩
  have hdefinitionEq : fieldDefinition = targetFieldDefinition := by
    rw [htargetLookup] at hlookup
    exact Option.some.inj hlookup.symm
  subst fieldDefinition
  rcases hkind with hleaf | hcompositeKind
  · rw [hcomposite] at hleaf
    simp at hleaf
  · have hchildFree : selectionSetDirectiveFree childSelectionSet :=
      selectionSetDirectiveFree_field_child_of_mem hfree hfieldMemMember
    have hchildNormal :
        selectionSetNormal schema
          targetFieldDefinition.outputType.namedType childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hfieldMemMember
        htargetLookup
    exact
      ⟨variableDefinitions, hcompositeKind.2.2, hchildFree,
        hchildNormal⟩

theorem PathLocalSupportValidNormal.fieldPairPathLocalNextSelectionSet_of_object_output
    {schema : Schema} {currentRuntimeType childRuntimeType targetField : Name}
    {targetArguments : List Argument}
    {currentSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : PathLocalSupportValidNormal schema currentRuntimeType currentSelectionSet
      -> objectTypeNameBool schema currentRuntimeType = true
      -> objectTypeNameBool schema childRuntimeType = true
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> targetFieldDefinition.outputType.namedType = childRuntimeType
      -> PathLocalSupportValidNormal schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments
            currentSelectionSet) := by
  intro hsupport hcurrentObject hchildObject htargetLookup houtputEq
  subst childRuntimeType
  rw [fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime]
  refine
    ⟨fieldChildMembersByHeadAtRuntime schema currentRuntimeType
      targetFieldDefinition.outputType.namedType targetField
      targetArguments currentSelectionSet, rfl, ?_⟩
  intro memberSelectionSet hmember
  rcases
      fieldChildMembersByHeadAtRuntime_mem_exists_field_of_allFields
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := targetFieldDefinition.outputType.namedType)
        (targetField := targetField)
        (targetArguments := targetArguments)
        (currentSelectionSet := currentSelectionSet)
        (memberSelectionSet := memberSelectionSet)
        (hsupport.allFields_of_object hcurrentObject) hmember with
    ⟨responseName, arguments, directives, childSelectionSet, hfieldMem,
      _harguments, hmemberEq⟩
  rcases
      hsupport.field_child_object_valid_normal_of_mem
        hfieldMem htargetLookup hchildObject rfl with
    ⟨variableDefinitions, hchildValid, hchildFree, hchildNormal⟩
  have hallFields : selectionsAllFields childSelectionSet :=
    selectionSetNormal_allFields_of_object hchildNormal hchildObject
  have hpruned :
      runtimePrunedSelectionSet schema
          targetFieldDefinition.outputType.namedType childSelectionSet =
        childSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      targetFieldDefinition.outputType.namedType hallFields
  subst memberSelectionSet
  simpa [hpruned] using
    (show
      ∃ variableDefinitions,
        Validation.selectionSetValid schema variableDefinitions
          targetFieldDefinition.outputType.namedType childSelectionSet
        ∧ selectionSetDirectiveFree childSelectionSet
        ∧ selectionSetNormal schema
          targetFieldDefinition.outputType.namedType childSelectionSet from
      ⟨variableDefinitions, hchildValid, hchildFree, hchildNormal⟩)

theorem PathLocalSupportValidNormal.fieldPairPathLocalNextSelectionSet_of_abstract_output
    {schema : Schema} {currentRuntimeType childRuntimeType targetField : Name}
    {targetArguments : List Argument} {currentSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : PathLocalSupportValidNormal schema currentRuntimeType currentSelectionSet
      -> objectTypeNameBool schema currentRuntimeType = true
      -> objectTypeNameBool schema childRuntimeType = true
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> schema.typeIncludesObjectBool
            targetFieldDefinition.outputType.namedType childRuntimeType
          = true
      -> PathLocalSupportValidNormal schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments
            currentSelectionSet) := by
  intro hsupport hcurrentObject hchildObject htargetLookup htargetComposite
    hinclude
  rw [fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime]
  exact
    PathLocalSupportValidNormal.flatten
      (by
        intro memberSelectionSet hmember
        rcases
            fieldChildMembersByHeadAtRuntime_mem_exists_field_of_allFields
              (schema := schema) (currentRuntimeType := currentRuntimeType)
              (childRuntimeType := childRuntimeType)
              (targetField := targetField)
              (targetArguments := targetArguments)
              (currentSelectionSet := currentSelectionSet)
              (memberSelectionSet := memberSelectionSet)
              (hsupport.allFields_of_object hcurrentObject) hmember with
          ⟨responseName, arguments, directives, childSelectionSet,
            hfieldMem, _harguments, hmemberEq⟩
        rcases
            hsupport.field_child_valid_normal_of_mem_lookup
              hfieldMem htargetLookup htargetComposite with
          ⟨variableDefinitions, hchildValid, hchildFree, hchildNormal⟩
        have hmemberSupport :
            PathLocalSupportValidNormal schema childRuntimeType
              (runtimePrunedSelectionSet schema childRuntimeType
                childSelectionSet) :=
          PathLocalSupportValidNormal.runtimePruned_of_valid_normal_runtime
            hchildValid hchildFree hchildNormal hinclude hchildObject
        simpa [hmemberEq] using hmemberSupport)

theorem PathLocalSelectionSetHeadReady.fieldPairPathLocalNextSelectionSet_field_child_of_valid_normal_object_output
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet currentSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentRuntimeType
        currentSelectionSet
      -> selectionSetDirectiveFree currentSelectionSet
      -> selectionSetNormal schema currentRuntimeType currentSelectionSet
      -> objectTypeNameBool schema currentRuntimeType = true
      -> objectTypeNameBool schema childRuntimeType = true
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ currentSelectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> targetFieldDefinition.outputType.namedType = childRuntimeType
      -> PathLocalSelectionSetHeadReady schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments currentSelectionSet)
          childSelectionSet := by
  intro hvalid hfree hnormal hcurrentObject hchildObject hmem harguments
    htargetLookup houtputEq
  subst childRuntimeType
  have hinclude :
      schema.typeIncludesObjectBool targetFieldDefinition.outputType.namedType
        targetFieldDefinition.outputType.namedType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hchildObject
  have hchildValid :
      Validation.selectionSetValid schema variableDefinitions
        targetFieldDefinition.outputType.namedType childSelectionSet :=
    selectionSetValid_object_field_child_of_mem_lookup hvalid hmem
      htargetLookup hchildObject
  have hchildFree : selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hfree hmem
  have hchildNormal :
      selectionSetNormal schema targetFieldDefinition.outputType.namedType
        childSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hnormal hmem
      htargetLookup
  have hallFields : selectionsAllFields childSelectionSet :=
    selectionSetNormal_allFields_of_object hchildNormal hchildObject
  have hpruned :
      runtimePrunedSelectionSet schema
          targetFieldDefinition.outputType.namedType childSelectionSet =
        childSelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema
      targetFieldDefinition.outputType.namedType hallFields
  have hmemberPruned :
      runtimePrunedSelectionSet schema
          targetFieldDefinition.outputType.namedType childSelectionSet ∈
        fieldChildMembersByHeadAtRuntime schema currentRuntimeType
          targetFieldDefinition.outputType.namedType targetField
          targetArguments currentSelectionSet :=
    runtimePrunedSelectionSet_mem_fieldChildMembersByHeadAtRuntime_of_field_mem
      (schema := schema) (currentRuntimeType := currentRuntimeType)
      (childRuntimeType := targetFieldDefinition.outputType.namedType)
      (targetField := targetField) (responseName := responseName)
      (targetArguments := targetArguments) (arguments := arguments)
      (directives := directives) (childSelectionSet := childSelectionSet)
      (selectionSet := currentSelectionSet) hmem harguments
  have hmember :
      childSelectionSet ∈
        fieldChildMembersByHeadAtRuntime schema currentRuntimeType
          targetFieldDefinition.outputType.namedType targetField
          targetArguments currentSelectionSet := by
    simpa [hpruned] using hmemberPruned
  have hsoundNext :
      PathLocalCurrentRuntimeSound schema
        (targetFieldDefinition.outputType.namedType,
          fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            targetFieldDefinition.outputType.namedType targetField
            targetArguments currentSelectionSet) :=
    PathLocalCurrentRuntimeSound.fieldPairPathLocalNextSelectionSet_of_valid_normal_object
      hvalid hfree hnormal hcurrentObject hchildObject htargetLookup
      hinclude
  rw [fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime]
  exact
    PathLocalSelectionSetHeadReady.member_flatten_of_sound
      (by
        simpa [fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime]
          using hsoundNext)
      hmember
      (PathLocalSelectionSetHeadReady.of_valid_normal_self
        hchildValid hchildNormal)

theorem PathLocalSelectionSetHeadReady.runtimePruned_inlineFragment_body_of_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {normalParentType runtimeType : Name}
    {directives : List DirectiveApplication}
    {bodySelectionSet selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions normalParentType
        selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> schema.typeIncludesObjectBool normalParentType runtimeType = true
      -> objectTypeNameBool schema runtimeType = true
      -> Selection.inlineFragment (some runtimeType) directives bodySelectionSet
          ∈ selectionSet
      -> PathLocalSelectionSetHeadReady schema runtimeType
          (runtimePrunedSelectionSet schema runtimeType selectionSet)
          bodySelectionSet := by
  intro hvalid hfree hnormal hinclude hruntimeObject hmem
  have hbodyValid :
      Validation.selectionSetValid schema variableDefinitions runtimeType
        bodySelectionSet :=
    selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
  have hbodyNormal :
      selectionSetNormal schema runtimeType bodySelectionSet :=
    (selectionSetNormal_inlineFragment_child_of_mem hnormal hmem).2
  have hbodyAllFields : selectionsAllFields bodySelectionSet :=
    selectionSetNormal_allFields_of_object hbodyNormal hruntimeObject
  have hbodyPruned :
      runtimePrunedSelectionSet schema runtimeType bodySelectionSet =
        bodySelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema runtimeType
      hbodyAllFields
  have hincludeSelf :
      schema.typeIncludesObjectBool runtimeType runtimeType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hruntimeObject
  rcases List.mem_iff_append.mp hmem with ⟨pref, suff, hselectionSet⟩
  subst selectionSet
  have hprunedContext :
      runtimePrunedSelectionSet schema runtimeType
          (pref ++
            Selection.inlineFragment (some runtimeType) directives
              bodySelectionSet :: suff) =
        runtimePrunedSelectionSet schema runtimeType pref ++
          bodySelectionSet ++
          runtimePrunedSelectionSet schema runtimeType suff := by
    simp [runtimePrunedSelectionSet_append, runtimePrunedSelectionSet,
      hincludeSelf, hbodyPruned, List.append_assoc]
  have hsound :
      PathLocalCurrentRuntimeSound schema
        (runtimeType,
          runtimePrunedSelectionSet schema runtimeType
            (pref ++
              Selection.inlineFragment (some runtimeType) directives
                bodySelectionSet :: suff)) :=
    PathLocalCurrentRuntimeSound.runtimePruned_of_valid_normal_runtime
      hvalid hfree hnormal hinclude hruntimeObject
  have hsoundContext :
      PathLocalCurrentRuntimeSound schema
        (runtimeType,
          runtimePrunedSelectionSet schema runtimeType pref ++
            bodySelectionSet ++
            runtimePrunedSelectionSet schema runtimeType suff) := by
    simpa [hprunedContext] using hsound
  have hreadyContext :
      PathLocalSelectionSetHeadReady schema runtimeType
        (runtimePrunedSelectionSet schema runtimeType pref ++
          bodySelectionSet ++
          runtimePrunedSelectionSet schema runtimeType suff)
        bodySelectionSet :=
    PathLocalSelectionSetHeadReady.append_context_of_sound
      hsoundContext
      (PathLocalSelectionSetHeadReady.of_valid_normal_self
        hbodyValid hbodyNormal)
  simpa [hprunedContext] using hreadyContext

theorem PathLocalSelectionSetCurrentContext.runtimePruned_inlineFragment_body_of_valid_normal
    {schema : Schema} {normalParentType runtimeType : Name}
    {directives : List DirectiveApplication}
    {bodySelectionSet selectionSet : List Selection}
    : selectionSetNormal schema normalParentType selectionSet
      -> objectTypeNameBool schema runtimeType = true
      -> Selection.inlineFragment (some runtimeType) directives bodySelectionSet
          ∈ selectionSet
      -> PathLocalSelectionSetCurrentContext bodySelectionSet
          (runtimePrunedSelectionSet schema runtimeType selectionSet) := by
  intro hnormal hruntimeObject hbodyMem
  rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
      hbodyMem with
    ⟨_htypeObject, hbodyNormal⟩
  have hallFields : selectionsAllFields bodySelectionSet :=
    selectionSetNormal_allFields_of_object hbodyNormal hruntimeObject
  have hbodyPruned :
      runtimePrunedSelectionSet schema runtimeType bodySelectionSet =
        bodySelectionSet :=
    runtimePrunedSelectionSet_eq_self_of_allFields schema runtimeType
      hallFields
  rcases List.mem_iff_append.mp hbodyMem with
    ⟨pref, suff, hselectionSet⟩
  subst selectionSet
  have hincludeSelf :
      schema.typeIncludesObjectBool runtimeType runtimeType = true :=
    typeIncludesObjectBool_self_of_objectTypeNameBool schema
      hruntimeObject
  refine
    ⟨runtimePrunedSelectionSet schema runtimeType pref,
      runtimePrunedSelectionSet schema runtimeType suff, ?_⟩
  simp [runtimePrunedSelectionSet_append, runtimePrunedSelectionSet,
    hincludeSelf, hbodyPruned, List.append_assoc]

theorem PathLocalSelectionSetHeadReady.fieldPairPathLocalNextSelectionSet_abstract_body_of_valid_normal_object
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives bodyDirectives : List DirectiveApplication}
    {childSelectionSet bodySelectionSet currentSelectionSet : List Selection}
    {targetFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions currentRuntimeType
        currentSelectionSet
      -> selectionSetDirectiveFree currentSelectionSet
      -> selectionSetNormal schema currentRuntimeType currentSelectionSet
      -> objectTypeNameBool schema currentRuntimeType = true
      -> objectTypeNameBool schema childRuntimeType = true
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ currentSelectionSet
      -> Selection.inlineFragment (some childRuntimeType) bodyDirectives bodySelectionSet
          ∈ childSelectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> schema.lookupField currentRuntimeType targetField = some targetFieldDefinition
      -> (TypeRef.named targetFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema targetFieldDefinition.outputType.namedType = false
      -> abstractRuntimeForFieldHeadDeep? schema currentRuntimeType targetField
            arguments currentRuntimeType currentSelectionSet
          = some childRuntimeType
      -> schema.typeIncludesObjectBool targetFieldDefinition.outputType.namedType
            childRuntimeType
          = true
      -> PathLocalSelectionSetHeadReady schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments currentSelectionSet)
          bodySelectionSet := by
  intro hvalid hfree hnormal hcurrentObject hchildObject hfieldMem
    hbodyMem harguments htargetLookup htargetComposite htargetNonObject
    hruntime hinclude
  have hchildNonempty : childSelectionSet ≠ [] := by
    intro hempty
    subst childSelectionSet
    simp at hbodyMem
  have hchildValid :
      Validation.selectionSetValid schema variableDefinitions
        targetFieldDefinition.outputType.namedType childSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hvalid hfieldMem
      hchildNonempty htargetLookup
  have hchildFree : selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hfree hfieldMem
  have hchildNormal :
      selectionSetNormal schema targetFieldDefinition.outputType.namedType
        childSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hnormal hfieldMem
      htargetLookup
  have hmemberRoot :
      runtimePrunedSelectionSet schema childRuntimeType childSelectionSet ∈
        fieldChildMembersByHeadAtRuntime schema currentRuntimeType
          childRuntimeType targetField targetArguments currentSelectionSet :=
    runtimePrunedSelectionSet_mem_fieldChildMembersByHeadAtRuntime_of_field_mem
      (schema := schema) (currentRuntimeType := currentRuntimeType)
      (childRuntimeType := childRuntimeType)
      (targetField := targetField) (responseName := responseName)
      (targetArguments := targetArguments) (arguments := arguments)
      (directives := directives) (childSelectionSet := childSelectionSet)
      (selectionSet := currentSelectionSet) hfieldMem harguments
  have hsoundNext :
      PathLocalCurrentRuntimeSound schema
        (childRuntimeType,
          fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments
            currentSelectionSet) :=
    PathLocalCurrentRuntimeSound.fieldPairPathLocalNextSelectionSet_of_valid_normal_object
      hvalid hfree hnormal hcurrentObject hchildObject htargetLookup
      hinclude
  have hlocalReady :
      PathLocalSelectionSetHeadReady schema childRuntimeType
        (runtimePrunedSelectionSet schema childRuntimeType
          childSelectionSet)
        bodySelectionSet :=
    PathLocalSelectionSetHeadReady.runtimePruned_inlineFragment_body_of_valid_normal
      hchildValid hchildFree hchildNormal hinclude hchildObject hbodyMem
  rw [fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime]
  exact
    PathLocalSelectionSetHeadReady.selection_in_member_flatten_of_sound
      (by
        simpa [fieldPairPathLocalNextSelectionSet_eq_flatten_fieldChildMembersByHeadAtRuntime]
          using hsoundNext)
      hmemberRoot hlocalReady

theorem executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_sound_fuel_ge
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  arguments parentType currentSelectionSet
                = some runtimeType))
      -> PathLocalCurrentRuntimeSound schema (parentType, currentSelectionSet)
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
  intro hlookup hruntime hsound hfuel
  have hinclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        runtimeType = true := by
    rcases hruntime with hobject | habstract
    · rcases hobject with ⟨hobject, hruntimeEq⟩
      subst runtimeType
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
    · exact
        hsound parentType fieldName runtimeType arguments fieldDefinition
          hlookup habstract.1 habstract.2.1 habstract.2.2
  exact
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_response_of_fuel_ge
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField parentType fieldName
      sourceRuntimeType responseName leftArguments rightArguments arguments
      leftRuntime rightRuntime tag childSelectionSet fieldDefinition
      runtimeType hlookup hruntime hinclude hfuel

theorem executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_ok_of_child_response_of_sound
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument)
    (leftRuntime rightRuntime : Name) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (responseFields : List (Name × Execution.ResponseValue))
    (childErrors : Nat)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldHeadDeep? schema parentType fieldName
                  arguments parentType currentSelectionSet
                = some runtimeType))
      -> PathLocalCurrentRuntimeSound schema (parentType, currentSelectionSet)
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
  intro hlookup hruntime hsound hfuel hchildResponse
  have hinclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        runtimeType = true := by
    rcases hruntime with hobject | habstract
    · rcases hobject with ⟨hobject, hruntimeEq⟩
      subst runtimeType
      exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
    · exact
        hsound parentType fieldName runtimeType arguments fieldDefinition
          hlookup habstract.1 habstract.2.1 habstract.2.2
  exact
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_objectProbe_ok_of_child_response
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField parentType fieldName
      sourceRuntimeType responseName leftArguments rightArguments arguments
      leftRuntime rightRuntime tag childSelectionSet fieldDefinition
      runtimeType responseFields childErrors hlookup hruntime hinclude
      hfuel hchildResponse

theorem executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children_of_sound
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (selectionSet : List Selection)
    : PathLocalCurrentRuntimeSound schema (parentType, currentSelectionSet)
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
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
                                ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                                    fieldName arguments parentType currentSelectionSet
                                  = some childRuntimeType))
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
  intro hsound hchildren
  refine
    executeField_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_field_ok_of_field_children
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField parentType sourceRuntimeType
      leftArguments rightArguments leftRuntime rightRuntime tag
      selectionSet ?_
  intro responseName fieldName arguments directives childSelectionSet hmem
  rcases hchildren responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hfuel, hleafOrChild⟩
  refine ⟨fieldDefinition, hlookup, hfuel, ?_⟩
  rcases hleafOrChild with hleaf | hchild
  · exact Or.inl hleaf
  · rcases hchild with
      ⟨childRuntimeType, responseFields, childErrors, hruntime,
        hchildResponse⟩
    have hinclude :
        schema.typeIncludesObjectBool
          fieldDefinition.outputType.namedType childRuntimeType = true := by
      rcases hruntime with hobjectRuntime | habstractRuntime
      · rcases hobjectRuntime with ⟨hobject, hruntimeEq⟩
        subst childRuntimeType
        exact typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject
      · exact
          hsound parentType fieldName childRuntimeType arguments
            fieldDefinition hlookup habstractRuntime.1
            habstractRuntime.2.1 habstractRuntime.2.2
    exact
      Or.inr
        ⟨childRuntimeType, responseFields, childErrors, hruntime,
          hinclude, hchildResponse⟩

theorem executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_of_field_children_of_sound
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType sourceRuntimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) (selectionSet : List Selection)
    : selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> PathLocalCurrentRuntimeSound schema (parentType, currentSelectionSet)
      -> (∀ responseName fieldName arguments directives childSelectionSet,
            Selection.field responseName fieldName arguments directives childSelectionSet
              ∈ selectionSet
            -> ∃ fieldDefinition,
                schema.lookupField parentType fieldName = some fieldDefinition
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
                                ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                                    fieldName arguments parentType currentSelectionSet
                                  = some childRuntimeType))
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
  intro hfree hnormal hobject hsound hchildren
  refine
    executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_of_field_children
      schema rootSelectionSet leftInitialSelectionSet
      rightInitialSelectionSet currentSelectionSet variableValues fuel
      targetParent leftField rightField parentType sourceRuntimeType
      leftArguments rightArguments leftRuntime rightRuntime tag
      selectionSet hfree hnormal hobject ?_
  intro responseName fieldName arguments directives childSelectionSet hmem
  rcases hchildren responseName fieldName arguments directives
      childSelectionSet hmem with
    ⟨fieldDefinition, hlookup, hfuel, hleafOrChild⟩
  refine ⟨fieldDefinition, hlookup, hfuel, ?_⟩
  rcases hleafOrChild with hleaf | hchild
  · exact Or.inl hleaf
  · rcases hchild with
      ⟨childRuntimeType, responseFields, childErrors, hruntime,
        hchildResponse⟩
    have hinclude :
        schema.typeIncludesObjectBool
          fieldDefinition.outputType.namedType childRuntimeType = true := by
      rcases hruntime with hobjectRuntime | habstractRuntime
      · rcases hobjectRuntime with ⟨hobjectOutput, hruntimeEq⟩
        subst childRuntimeType
        exact
          typeIncludesObjectBool_self_of_objectTypeNameBool schema
            hobjectOutput
      · exact
          hsound parentType fieldName childRuntimeType arguments
            fieldDefinition hlookup habstractRuntime.1
            habstractRuntime.2.1 habstractRuntime.2.2
    exact
      Or.inr
        ⟨childRuntimeType, responseFields, childErrors, hruntime,
          hinclude, hchildResponse⟩

theorem executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_abstract_of_inlineFragment_body_children_of_sound
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> PathLocalCurrentRuntimeSound schema (runtimeType, currentSelectionSet)
      -> (∀ typeCondition bodySelectionSet,
            Selection.inlineFragment (some typeCondition) [] bodySelectionSet
              ∈ selectionSet
            -> ∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
                  bodyChildSelectionSet,
                Selection.field bodyResponseName bodyFieldName bodyArguments
                    bodyDirectives bodyChildSelectionSet
                  ∈ bodySelectionSet
                -> ∃ bodyFieldDefinition,
                    schema.lookupField typeCondition bodyFieldName
                      = some bodyFieldDefinition
                    ∧ leafProbeFuel bodyFieldDefinition.outputType ≤ fuel
                    ∧ ((TypeRef.named
                            bodyFieldDefinition.outputType.namedType).isCompositeBool
                            schema
                          = false
                        ∨ ∃ childRuntimeType responseFields childErrors,
                            (((objectTypeNameBool schema
                                      bodyFieldDefinition.outputType.namedType
                                    = true
                                  ∧ childRuntimeType
                                    = bodyFieldDefinition.outputType.namedType)
                                ∨ ((TypeRef.named
                                        bodyFieldDefinition.outputType.namedType).isCompositeBool
                                        schema
                                      = true
                                    ∧ objectTypeNameBool schema
                                        bodyFieldDefinition.outputType.namedType
                                      = false
                                    ∧ abstractRuntimeForFieldHeadDeep? schema
                                        typeCondition bodyFieldName bodyArguments
                                        typeCondition currentSelectionSet
                                      = some childRuntimeType))
                              ∧ Execution.executeSelectionSetAsResponse schema
                                  (fieldPairOrDeepSuccessResolvers schema
                                    rootSelectionSet
                                    (fieldPairPathLocalProbeResolvers schema
                                      leftInitialSelectionSet rightInitialSelectionSet
                                      targetParent leftField rightField leftArguments
                                      rightArguments leftRuntime rightRuntime)
                                    targetParent leftField rightField leftArguments
                                    rightArguments)
                                  variableValues
                                  (fuel - leafProbeFuel bodyFieldDefinition.outputType)
                                  childRuntimeType
                                  (projectionTargetResolverValue
                                    (.object childRuntimeType
                                      (FieldPairPathLocalProbeRef.target tag
                                        (fieldPairPathLocalNextSelectionSet schema
                                          typeCondition childRuntimeType
                                          bodyFieldName bodyArguments
                                          currentSelectionSet))))
                                  bodyChildSelectionSet
                                = ({
                                      data :=
                                        Execution.ResponseValue.object responseFields,
                                      errors := childErrors
                                    }
                                    : Execution.Response))))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
            selectionSet
          = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
              : Execution.Response) := by
  intro hnonObject hruntimeObject hfree hnormal hsound hbodyChildren
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let source :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
  by_cases hruntimeMem :
      runtimeType ∈ selectionSet.filterMap inlineFragmentTypeCondition?
  · rcases List.mem_filterMap.mp hruntimeMem with
      ⟨selection, hselectionMem, hselectionRuntime⟩
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        simp [inlineFragmentTypeCondition?] at hselectionRuntime
    | inlineFragment maybeTypeCondition directives bodySelectionSet =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
        | some typeCondition =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
            subst typeCondition
            have hdirectives : directives = [] :=
              selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                hfree hselectionMem
            subst directives
            rcases List.mem_iff_append.mp hselectionMem with
              ⟨pref, suffix, hselectionSet⟩
            subst selectionSet
            have hinlineMem :
                Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet ∈
                  pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix := by
              exact List.mem_append_right _ (by simp)
            have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
              selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
                hinlineMem
            have hbodyNormal :
                selectionSetNormal schema runtimeType bodySelectionSet :=
              (selectionSetNormal_inlineFragment_child_of_mem hnormal
                hinlineMem).2
            rcases
                executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_of_field_children_of_sound
                  schema rootSelectionSet leftInitialSelectionSet
                  rightInitialSelectionSet currentSelectionSet variableValues
                  fuel targetParent leftField rightField runtimeType
                  runtimeType leftArguments rightArguments leftRuntime
                  rightRuntime tag bodySelectionSet hbodyFree hbodyNormal
                  hruntimeObject hsound
                  (by
                    intro bodyResponseName bodyFieldName bodyArguments
                      bodyDirectives bodyChildSelectionSet hfieldMem
                    exact
                      hbodyChildren runtimeType bodySelectionSet hinlineMem
                        bodyResponseName bodyFieldName bodyArguments
                        bodyDirectives bodyChildSelectionSet hfieldMem) with
              ⟨bodyFields, bodyErrors, hbodyResponse⟩
            have hmiddle :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] :=
              by
                simpa [source, projectionTargetResolverValue,
                  projectionResolverValue] using
                  executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                    schema resolvers variableValues (fuel + 1)
                    (ProjectionResolverRef.target
                      (FieldPairPathLocalProbeRef.target tag
                        currentSelectionSet))
                    hnonObject hruntimeObject hfree hnormal
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  source runtimeType = true := by
              dsimp [source]
              simpa [projectionTargetResolverValue, projectionResolverValue]
                using
                  (doesFragmentTypeApplyBool_object_self schema
                    (ref :=
                      ProjectionResolverRef.target
                        (FieldPairPathLocalProbeRef.target tag
                          currentSelectionSet))
                    hruntimeObject)
            have hflatten :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet]
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source bodySelectionSet := by
              simpa using
                executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                  schema resolvers variableValues (fuel + 1) runtimeType
                  runtimeType source bodySelectionSet [] happly
            refine ⟨bodyFields, bodyErrors, ?_⟩
            calc
              Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                  =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] := by
                    simp [Execution.executeSelectionSetAsResponse, hmiddle]
              _ =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source bodySelectionSet := by
                    simp [Execution.executeSelectionSetAsResponse, hflatten]
              _ =
                ({ data := Execution.ResponseValue.object bodyFields,
                   errors := bodyErrors } : Execution.Response) := by
                    simpa [resolvers, source] using hbodyResponse
  · have hcollect :
        Execution.collectFields schema variableValues runtimeType source
          selectionSet = [] :=
      by
        simpa [source, projectionTargetResolverValue,
          projectionResolverValue] using
          collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
            schema variableValues (normalParentType := normalParentType)
            (executionParentType := runtimeType) (runtimeType := runtimeType)
            (ProjectionResolverRef.target
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
            hnonObject hfree hnormal hruntimeMem
    have hcollectObject :
        Execution.collectFields schema variableValues runtimeType
          (Execution.ResolverValue.object runtimeType
            (ProjectionResolverRef.target
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
          selectionSet = [] := by
      simpa [source, projectionTargetResolverValue,
        projectionResolverValue] using hcollect
    refine ⟨[], 0, ?_⟩
    simp [projectionTargetResolverValue, projectionResolverValue,
      Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hcollectObject, Execution.executeCollectedFields]

theorem executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_abstract_of_runtime_inlineFragment_body_children_of_sound
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> PathLocalCurrentRuntimeSound schema (runtimeType, currentSelectionSet)
      -> (∀ bodySelectionSet,
            Selection.inlineFragment (some runtimeType) [] bodySelectionSet ∈ selectionSet
            -> ∀ bodyResponseName bodyFieldName bodyArguments bodyDirectives
                  bodyChildSelectionSet,
                Selection.field bodyResponseName bodyFieldName bodyArguments
                    bodyDirectives bodyChildSelectionSet
                  ∈ bodySelectionSet
                -> ∃ bodyFieldDefinition,
                    schema.lookupField runtimeType bodyFieldName
                      = some bodyFieldDefinition
                    ∧ leafProbeFuel bodyFieldDefinition.outputType ≤ fuel
                    ∧ ((TypeRef.named
                            bodyFieldDefinition.outputType.namedType).isCompositeBool
                            schema
                          = false
                        ∨ ∃ childRuntimeType responseFields childErrors,
                            (((objectTypeNameBool schema
                                      bodyFieldDefinition.outputType.namedType
                                    = true
                                  ∧ childRuntimeType
                                    = bodyFieldDefinition.outputType.namedType)
                                ∨ ((TypeRef.named
                                        bodyFieldDefinition.outputType.namedType).isCompositeBool
                                        schema
                                      = true
                                    ∧ objectTypeNameBool schema
                                        bodyFieldDefinition.outputType.namedType
                                      = false
                                    ∧ abstractRuntimeForFieldHeadDeep? schema
                                        runtimeType bodyFieldName bodyArguments
                                        runtimeType currentSelectionSet
                                      = some childRuntimeType))
                              ∧ Execution.executeSelectionSetAsResponse schema
                                  (fieldPairOrDeepSuccessResolvers schema
                                    rootSelectionSet
                                    (fieldPairPathLocalProbeResolvers schema
                                      leftInitialSelectionSet rightInitialSelectionSet
                                      targetParent leftField rightField leftArguments
                                      rightArguments leftRuntime rightRuntime)
                                    targetParent leftField rightField leftArguments
                                    rightArguments)
                                  variableValues
                                  (fuel - leafProbeFuel bodyFieldDefinition.outputType)
                                  childRuntimeType
                                  (projectionTargetResolverValue
                                    (.object childRuntimeType
                                      (FieldPairPathLocalProbeRef.target tag
                                        (fieldPairPathLocalNextSelectionSet schema
                                          runtimeType childRuntimeType
                                          bodyFieldName bodyArguments
                                          currentSelectionSet))))
                                  bodyChildSelectionSet
                                = ({
                                      data :=
                                        Execution.ResponseValue.object responseFields,
                                      errors := childErrors
                                    }
                                    : Execution.Response))))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
            selectionSet
          = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
              : Execution.Response) := by
  intro hnonObject hruntimeObject hfree hnormal hsound hbodyChildren
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let source :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
  by_cases hruntimeMem :
      runtimeType ∈ selectionSet.filterMap inlineFragmentTypeCondition?
  · rcases List.mem_filterMap.mp hruntimeMem with
      ⟨selection, hselectionMem, hselectionRuntime⟩
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        simp [inlineFragmentTypeCondition?] at hselectionRuntime
    | inlineFragment maybeTypeCondition directives bodySelectionSet =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
        | some typeCondition =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
            subst typeCondition
            have hdirectives : directives = [] :=
              selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                hfree hselectionMem
            subst directives
            rcases List.mem_iff_append.mp hselectionMem with
              ⟨pref, suffix, hselectionSet⟩
            subst selectionSet
            have hinlineMem :
                Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet ∈
                  pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix := by
              exact List.mem_append_right _ (by simp)
            have hbodyFree : selectionSetDirectiveFree bodySelectionSet :=
              selectionSetDirectiveFree_inlineFragment_child_of_mem hfree
                hinlineMem
            have hbodyNormal :
                selectionSetNormal schema runtimeType bodySelectionSet :=
              (selectionSetNormal_inlineFragment_child_of_mem hnormal
                hinlineMem).2
            rcases
                executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_object_of_field_children_of_sound
                  schema rootSelectionSet leftInitialSelectionSet
                  rightInitialSelectionSet currentSelectionSet variableValues
                  fuel targetParent leftField rightField runtimeType
                  runtimeType leftArguments rightArguments leftRuntime
                  rightRuntime tag bodySelectionSet hbodyFree hbodyNormal
                  hruntimeObject hsound
                  (by
                    intro bodyResponseName bodyFieldName bodyArguments
                      bodyDirectives bodyChildSelectionSet hfieldMem
                    exact
                      hbodyChildren bodySelectionSet hinlineMem
                        bodyResponseName bodyFieldName bodyArguments
                        bodyDirectives bodyChildSelectionSet hfieldMem) with
              ⟨bodyFields, bodyErrors, hbodyResponse⟩
            have hmiddle :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] :=
              by
                simpa [source, projectionTargetResolverValue,
                  projectionResolverValue] using
                  executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                    schema resolvers variableValues (fuel + 1)
                    (ProjectionResolverRef.target
                      (FieldPairPathLocalProbeRef.target tag
                        currentSelectionSet))
                    hnonObject hruntimeObject hfree hnormal
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  source runtimeType = true := by
              dsimp [source]
              simpa [projectionTargetResolverValue, projectionResolverValue]
                using
                  (doesFragmentTypeApplyBool_object_self schema
                    (ref :=
                      ProjectionResolverRef.target
                        (FieldPairPathLocalProbeRef.target tag
                          currentSelectionSet))
                    hruntimeObject)
            have hflatten :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet]
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source bodySelectionSet := by
              simpa using
                executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                  schema resolvers variableValues (fuel + 1) runtimeType
                  runtimeType source bodySelectionSet [] happly
            refine ⟨bodyFields, bodyErrors, ?_⟩
            calc
              Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                  =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] := by
                    simp [Execution.executeSelectionSetAsResponse, hmiddle]
              _ =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source bodySelectionSet := by
                    simp [Execution.executeSelectionSetAsResponse, hflatten]
              _ =
                ({ data := Execution.ResponseValue.object bodyFields,
                   errors := bodyErrors } : Execution.Response) := by
                    simpa [resolvers, source] using hbodyResponse
  · have hcollect :
        Execution.collectFields schema variableValues runtimeType source
          selectionSet = [] :=
      by
        simpa [source, projectionTargetResolverValue,
          projectionResolverValue] using
          collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
            schema variableValues (normalParentType := normalParentType)
            (executionParentType := runtimeType) (runtimeType := runtimeType)
            (ProjectionResolverRef.target
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
            hnonObject hfree hnormal hruntimeMem
    have hcollectObject :
        Execution.collectFields schema variableValues runtimeType
          (Execution.ResolverValue.object runtimeType
            (ProjectionResolverRef.target
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
          selectionSet = [] := by
      simpa [source, projectionTargetResolverValue,
        projectionResolverValue] using hcollect
    refine ⟨[], 0, ?_⟩
    simp [projectionTargetResolverValue, projectionResolverValue,
      Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hcollectObject, Execution.executeCollectedFields]

theorem executeSelectionSetAsResponse_fieldPairOrDeepSuccess_pathLocalProbe_tagged_abstract_of_runtime_inlineFragment_body_response
    (schema : Schema)
    (rootSelectionSet leftInitialSelectionSet rightInitialSelectionSet currentSelectionSet
      : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField normalParentType runtimeType : Name)
    (leftArguments rightArguments : List Argument) (leftRuntime rightRuntime : Name)
    (tag : FieldPairProbeTag) {selectionSet : List Selection}
    : objectTypeNameBool schema normalParentType = false
      -> objectTypeNameBool schema runtimeType = true
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema normalParentType selectionSet
      -> (∀ bodySelectionSet,
            Selection.inlineFragment (some runtimeType) [] bodySelectionSet ∈ selectionSet
            -> ∃ responseFields errors,
                Execution.executeSelectionSetAsResponse schema
                  (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                      rightInitialSelectionSet targetParent leftField rightField
                      leftArguments rightArguments leftRuntime rightRuntime)
                    targetParent leftField rightField leftArguments rightArguments)
                  variableValues (fuel + 1) runtimeType
                  (projectionTargetResolverValue
                    (.object runtimeType
                      (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
                  bodySelectionSet
                = ({
                      data := Execution.ResponseValue.object responseFields,
                      errors := errors
                    }
                    : Execution.Response))
      -> ∃ responseFields errors,
          Execution.executeSelectionSetAsResponse schema
            (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
                rightInitialSelectionSet targetParent leftField rightField
                leftArguments rightArguments leftRuntime rightRuntime)
              targetParent leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) runtimeType
            (projectionTargetResolverValue
              (.object runtimeType
                (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
            selectionSet
          = ({ data := Execution.ResponseValue.object responseFields, errors := errors }
              : Execution.Response) := by
  intro hnonObject hruntimeObject hfree hnormal hbodyResponse
  let resolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (fieldPairPathLocalProbeResolvers schema leftInitialSelectionSet
        rightInitialSelectionSet targetParent leftField rightField
        leftArguments rightArguments leftRuntime rightRuntime)
      targetParent leftField rightField leftArguments rightArguments
  let source :=
    projectionTargetResolverValue
      (.object runtimeType
        (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
  by_cases hruntimeMem :
      runtimeType ∈ selectionSet.filterMap inlineFragmentTypeCondition?
  · rcases List.mem_filterMap.mp hruntimeMem with
      ⟨selection, hselectionMem, hselectionRuntime⟩
    cases selection with
    | field responseName fieldName arguments directives childSelectionSet =>
        simp [inlineFragmentTypeCondition?] at hselectionRuntime
    | inlineFragment maybeTypeCondition directives bodySelectionSet =>
        cases maybeTypeCondition with
        | none =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
        | some typeCondition =>
            simp [inlineFragmentTypeCondition?] at hselectionRuntime
            subst typeCondition
            have hdirectives : directives = [] :=
              selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                hfree hselectionMem
            subst directives
            rcases List.mem_iff_append.mp hselectionMem with
              ⟨pref, suffix, hselectionSet⟩
            subst selectionSet
            have hinlineMem :
                Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet ∈
                  pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix := by
              exact List.mem_append_right _ (by simp)
            rcases hbodyResponse bodySelectionSet hinlineMem with
              ⟨bodyFields, bodyErrors, hbodyExec⟩
            have hmiddle :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] :=
              by
                simpa [source, projectionTargetResolverValue,
                  projectionResolverValue] using
                  executeSelectionSet_middle_inlineFragment_only_eq_singleton_at_runtime_parent
                    schema resolvers variableValues (fuel + 1)
                    (ProjectionResolverRef.target
                      (FieldPairPathLocalProbeRef.target tag
                        currentSelectionSet))
                    hnonObject hruntimeObject hfree hnormal
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  source runtimeType = true := by
              dsimp [source]
              simpa [projectionTargetResolverValue, projectionResolverValue]
                using
                  (doesFragmentTypeApplyBool_object_self schema
                    (ref :=
                      ProjectionResolverRef.target
                        (FieldPairPathLocalProbeRef.target tag
                          currentSelectionSet))
                    hruntimeObject)
            have hflatten :
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet]
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  (fuel + 1) runtimeType source bodySelectionSet := by
              simpa using
                executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
                  schema resolvers variableValues (fuel + 1) runtimeType
                  runtimeType source bodySelectionSet [] happly
            refine ⟨bodyFields, bodyErrors, ?_⟩
            calc
              Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  (pref ++ Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet :: suffix)
                  =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source
                  [Selection.inlineFragment (some runtimeType) []
                    bodySelectionSet] := by
                    simp [Execution.executeSelectionSetAsResponse, hmiddle]
              _ =
                Execution.executeSelectionSetAsResponse schema resolvers variableValues
                  (fuel + 1) runtimeType source bodySelectionSet := by
                    simp [Execution.executeSelectionSetAsResponse, hflatten]
              _ =
                ({ data := Execution.ResponseValue.object bodyFields,
                   errors := bodyErrors } : Execution.Response) := by
                    simpa [resolvers, source] using hbodyExec
  · have hcollect :
        Execution.collectFields schema variableValues runtimeType source
          selectionSet = [] :=
      by
        simpa [source, projectionTargetResolverValue,
          projectionResolverValue] using
          collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
            schema variableValues (normalParentType := normalParentType)
            (executionParentType := runtimeType) (runtimeType := runtimeType)
            (ProjectionResolverRef.target
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet))
            hnonObject hfree hnormal hruntimeMem
    have hcollectObject :
        Execution.collectFields schema variableValues runtimeType
          (Execution.ResolverValue.object runtimeType
            (ProjectionResolverRef.target
              (FieldPairPathLocalProbeRef.target tag currentSelectionSet)))
          selectionSet = [] := by
      simpa [source, projectionTargetResolverValue,
        projectionResolverValue] using hcollect
    refine ⟨[], 0, ?_⟩
    simp [projectionTargetResolverValue, projectionResolverValue,
      Execution.executeSelectionSetAsResponse, Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, Execution.executeRootSelectionSet,
      hcollectObject, Execution.executeCollectedFields]

theorem normalSelectionSetResponsePath_of_firstFieldChildByHead?_field_mem
    {schema : Schema} {childParentType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {responsePath : List Name}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetResponsePath schema childParentType childSelectionSet
          responsePath
      -> ∃ mergedSelectionSet,
          firstFieldChildByHead? targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ NormalSelectionSetResponsePath schema childParentType
              mergedSelectionSet responsePath := by
  intro hmem harguments hpath
  rcases
      firstFieldChildByHead?_field_mem_append_context
        hmem harguments with
    ⟨mergedSelectionSet, pref, suff, hmerged, hcontext⟩
  refine ⟨mergedSelectionSet, hmerged, ?_⟩
  simpa [hcontext] using
    (NormalSelectionSetResponsePath.append_context
      (pref := pref) (suff := suff) hpath)

theorem normalSelectionSetResponsePath_of_firstFieldChildByHeadAtRuntime?_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {responsePath : List Name}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetResponsePath schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
          responsePath
      -> ∃ mergedSelectionSet,
          firstFieldChildByHeadAtRuntime? schema currentRuntimeType
              childRuntimeType targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ NormalSelectionSetResponsePath schema childRuntimeType
              mergedSelectionSet responsePath := by
  intro hmem harguments hpath
  rcases
      firstFieldChildByHeadAtRuntime?_field_mem_append_context
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) hmem harguments with
    ⟨mergedSelectionSet, pref, suff, hmerged, hcontext⟩
  refine ⟨mergedSelectionSet, hmerged, ?_⟩
  simpa [hcontext] using
    (NormalSelectionSetResponsePath.append_context
      (pref := pref) (suff := suff) hpath)

theorem normalSelectionSetResponsePath_of_fieldPairPathLocalNextSelectionSet_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {responsePath : List Name}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetResponsePath schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
          responsePath
      -> NormalSelectionSetResponsePath schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments selectionSet)
          responsePath := by
  intro hmem harguments hpath
  rcases
      normalSelectionSetResponsePath_of_firstFieldChildByHeadAtRuntime?_field_mem
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) hmem harguments hpath with
    ⟨mergedSelectionSet, hmerged, hmergedPath⟩
  have hnext :
      fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType targetField targetArguments selectionSet =
        mergedSelectionSet := by
    simp [fieldPairPathLocalNextSelectionSet, hmerged]
  simpa [hnext] using hmergedPath

theorem normalSelectionSetResponsePath_runtime_of_fieldPairPathLocalNextSelectionSet_field_mem
    {schema : Schema} {currentRuntimeType childParentType targetField responseName : Name}
    {targetArguments arguments : List Argument} {directives : List DirectiveApplication}
    {variableDefinitions : List VariableDefinition}
    {childSelectionSet currentSelectionSet : List Selection} {responsePath : List Name}
    : Validation.selectionSetValid schema variableDefinitions childParentType
        childSelectionSet
      -> selectionSetNormal schema childParentType childSelectionSet
      -> NormalSelectionSetResponsePath schema childParentType childSelectionSet
          responsePath
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ currentSelectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> ∃ childRuntimeType,
          selectionSetRuntimeActive schema childParentType childRuntimeType
            childSelectionSet
          ∧ schema.typeIncludesObjectBool childParentType childRuntimeType = true
          ∧ NormalSelectionSetResponsePath schema childRuntimeType
              (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
                childRuntimeType targetField targetArguments currentSelectionSet)
              responsePath := by
  intro hchildValid hchildNormal hpath hmem harguments
  rcases
      NormalSelectionSetResponsePath.runtimePruned_of_normal hchildValid
        hchildNormal hpath with
    ⟨childRuntimeType, hactive, hinclude, hprunedPath⟩
  exact
    ⟨childRuntimeType, hactive, hinclude,
      normalSelectionSetResponsePath_of_fieldPairPathLocalNextSelectionSet_field_mem
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType) (targetField := targetField)
        hmem harguments hprunedPath⟩

theorem normalSelectionSetObservableResponsePath_of_firstFieldChildByHeadAtRuntime?_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {responsePath : List Name}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetObservableResponsePath schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
          responsePath
      -> ∃ mergedSelectionSet,
          firstFieldChildByHeadAtRuntime? schema currentRuntimeType
              childRuntimeType targetField targetArguments selectionSet
            = some mergedSelectionSet
          ∧ NormalSelectionSetObservableResponsePath schema childRuntimeType
              mergedSelectionSet responsePath := by
  intro hmem harguments hpath
  rcases
      firstFieldChildByHeadAtRuntime?_field_mem_append_context
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) hmem harguments with
    ⟨mergedSelectionSet, pref, suff, hmerged, hcontext⟩
  refine ⟨mergedSelectionSet, hmerged, ?_⟩
  simpa [hcontext] using
    (NormalSelectionSetObservableResponsePath.append_context
      (pref := pref) (suff := suff) hpath)

theorem normalSelectionSetObservableResponsePath_of_fieldPairPathLocalNextSelectionSet_field_mem
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {responsePath : List Name}
    : Selection.field responseName targetField arguments directives childSelectionSet
        ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> NormalSelectionSetObservableResponsePath schema childRuntimeType
          (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
          responsePath
      -> NormalSelectionSetObservableResponsePath schema childRuntimeType
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments selectionSet)
          responsePath := by
  intro hmem harguments hpath
  rcases
      normalSelectionSetObservableResponsePath_of_firstFieldChildByHeadAtRuntime?_field_mem
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField) hmem harguments hpath with
    ⟨mergedSelectionSet, hmerged, hmergedPath⟩
  have hnext :
      fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType targetField targetArguments selectionSet =
        mergedSelectionSet := by
    simp [fieldPairPathLocalNextSelectionSet, hmerged]
  simpa [hnext] using hmergedPath

theorem normalSelectionSetObservableResponsePath_runtime_of_fieldPairPathLocalNextSelectionSet_field_mem
    {schema : Schema} {currentRuntimeType childParentType targetField responseName : Name}
    {targetArguments arguments : List Argument} {directives : List DirectiveApplication}
    {variableDefinitions : List VariableDefinition}
    {childSelectionSet currentSelectionSet : List Selection} {responsePath : List Name}
    : Validation.selectionSetValid schema variableDefinitions childParentType
        childSelectionSet
      -> selectionSetNormal schema childParentType childSelectionSet
      -> NormalSelectionSetObservableResponsePath schema childParentType
          childSelectionSet responsePath
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ currentSelectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> ∃ childRuntimeType,
          selectionSetRuntimeActive schema childParentType childRuntimeType
            childSelectionSet
          ∧ schema.typeIncludesObjectBool childParentType childRuntimeType = true
          ∧ NormalSelectionSetObservableResponsePath schema childRuntimeType
              (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
                childRuntimeType targetField targetArguments currentSelectionSet)
              responsePath := by
  intro hchildValid hchildNormal hpath hmem harguments
  rcases
      NormalSelectionSetObservableResponsePath.runtimePruned_of_normal
        hchildValid hchildNormal hpath with
    ⟨childRuntimeType, hactive, hinclude, hprunedPath⟩
  exact
    ⟨childRuntimeType, hactive, hinclude,
      normalSelectionSetObservableResponsePath_of_fieldPairPathLocalNextSelectionSet_field_mem
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType) (targetField := targetField)
        hmem harguments hprunedPath⟩

theorem PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
    {schema : Schema}
    {currentRuntimeType childRuntimeType targetField responseName : Name}
    {targetArguments arguments : List Argument} {directives : List DirectiveApplication}
    {selectionSet childSelectionSet currentSelectionSet : List Selection}
    : PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ selectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> runtimePrunedSelectionSet schema childRuntimeType childSelectionSet
          = childSelectionSet
      -> PathLocalSelectionSetCurrentContext childSelectionSet
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments
            currentSelectionSet) := by
  intro hcontext hfieldMem harguments hpruned
  rcases hcontext with ⟨currentPref, currentSuff, hcurrent⟩
  subst currentSelectionSet
  have hfieldMemCurrent :
      Selection.field responseName targetField arguments directives
        childSelectionSet ∈ currentPref ++ selectionSet ++ currentSuff := by
    exact
      List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inr hfieldMem)))
  rcases
      firstFieldChildByHeadAtRuntime?_field_mem_append_context
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField)
        (targetArguments := targetArguments)
        hfieldMemCurrent harguments with
    ⟨mergedSelectionSet, pref, suff, hmerged, hmergedContext⟩
  have hnext :
      fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType targetField targetArguments
          (currentPref ++ selectionSet ++ currentSuff) =
        mergedSelectionSet := by
    have hmergedAssoc :
        firstFieldChildByHeadAtRuntime? schema currentRuntimeType
            childRuntimeType targetField targetArguments
            (currentPref ++ (selectionSet ++ currentSuff)) =
          some mergedSelectionSet := by
      simpa [List.append_assoc] using hmerged
    simp [fieldPairPathLocalNextSelectionSet, hmergedAssoc]
  exact
    ⟨pref, suff, by
      rw [hnext, hmergedContext, hpruned]⟩

theorem PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
    {schema : Schema}
    {currentRuntimeType childRuntimeType childParentType targetField responseName : Name}
    {targetArguments arguments : List Argument}
    {directives bodyDirectives : List DirectiveApplication}
    {selectionSet childSelectionSet bodySelectionSet currentSelectionSet : List Selection}
    : PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Selection.field responseName targetField arguments directives childSelectionSet
          ∈ selectionSet
      -> Selection.inlineFragment (some childRuntimeType) bodyDirectives bodySelectionSet
          ∈ childSelectionSet
      -> Argument.argumentsEquivalent arguments targetArguments
      -> selectionSetNormal schema childParentType childSelectionSet
      -> objectTypeNameBool schema childRuntimeType = true
      -> PathLocalSelectionSetCurrentContext bodySelectionSet
          (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
            childRuntimeType targetField targetArguments
            currentSelectionSet) := by
  intro hcontext hfieldMem hbodyMem harguments hchildNormal hchildObject
  rcases hcontext with ⟨currentPref, currentSuff, hcurrent⟩
  subst currentSelectionSet
  have hfieldMemCurrent :
      Selection.field responseName targetField arguments directives
        childSelectionSet ∈ currentPref ++ selectionSet ++ currentSuff := by
    exact
      List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inr hfieldMem)))
  rcases
      firstFieldChildByHeadAtRuntime?_field_mem_append_context
        (schema := schema) (currentRuntimeType := currentRuntimeType)
        (childRuntimeType := childRuntimeType)
        (targetField := targetField)
        (targetArguments := targetArguments)
        hfieldMemCurrent harguments with
    ⟨mergedSelectionSet, pref, suff, hmerged, hmergedContext⟩
  have hnext :
      fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType targetField targetArguments
          (currentPref ++ selectionSet ++ currentSuff) =
        mergedSelectionSet := by
    have hmergedAssoc :
        firstFieldChildByHeadAtRuntime? schema currentRuntimeType
            childRuntimeType targetField targetArguments
            (currentPref ++ (selectionSet ++ currentSuff)) =
          some mergedSelectionSet := by
      simpa [List.append_assoc] using hmerged
    simp [fieldPairPathLocalNextSelectionSet, hmergedAssoc]
  have hprunedChildContext :
      PathLocalSelectionSetCurrentContext
        (runtimePrunedSelectionSet schema childRuntimeType childSelectionSet)
        (fieldPairPathLocalNextSelectionSet schema currentRuntimeType
          childRuntimeType targetField targetArguments
          (currentPref ++ selectionSet ++ currentSuff)) := by
    exact ⟨pref, suff, by rw [hnext, hmergedContext]⟩
  have hbodyContext :
      PathLocalSelectionSetCurrentContext bodySelectionSet
        (runtimePrunedSelectionSet schema childRuntimeType
          childSelectionSet) :=
    PathLocalSelectionSetCurrentContext.runtimePruned_inlineFragment_body_of_valid_normal
      hchildNormal hchildObject hbodyMem
  exact hbodyContext.trans hprunedChildContext

theorem pathLocalCompositeFieldChildReady_of_valid_normal_support_context
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet currentSelectionSet childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ childRuntime,
          (((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                ∧ childRuntime = fieldDefinition.outputType.namedType)
              ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
                      schema
                    = true
                  ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                  ∧ abstractRuntimeForFieldHeadDeep? schema parentType
                      fieldName arguments parentType currentSelectionSet
                    = some childRuntime))
            ∧ schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType childRuntime
              = true
            ∧ PathLocalSupportValidNormal schema childRuntime
                (fieldPairPathLocalNextSelectionSet schema parentType
                  childRuntime fieldName arguments currentSelectionSet)
            ∧ (objectTypeNameBool schema fieldDefinition.outputType.namedType = true
                -> PathLocalSelectionSetCurrentContext childSelectionSet
                    (fieldPairPathLocalNextSelectionSet schema parentType
                      childRuntime fieldName arguments currentSelectionSet))
            ∧ (objectTypeNameBool schema fieldDefinition.outputType.namedType = false
                -> ∀ {bodyDirectives bodySelectionSet},
                    Selection.inlineFragment (some childRuntime) bodyDirectives
                        bodySelectionSet
                      ∈ childSelectionSet
                    -> PathLocalSelectionSetCurrentContext bodySelectionSet
                        (fieldPairPathLocalNextSelectionSet schema parentType
                          childRuntime fieldName arguments currentSelectionSet))) := by
  intro hschema hvalid hnormal hobject hsupport hcontext hmem hlookup
    hcomposite
  rcases
      pathLocalCompositeFieldRuntime_of_valid_normal_support_context
        hvalid hnormal hsupport hcontext hmem hlookup hcomposite with
    ⟨childRuntime, hruntime, hinclude⟩
  have hchildObject : objectTypeNameBool schema childRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
  have hchildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        childSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
  have hchildSupport :
      PathLocalSupportValidNormal schema childRuntime
        (fieldPairPathLocalNextSelectionSet schema parentType
          childRuntime fieldName arguments currentSelectionSet) := by
    rcases hruntime with hobjectRuntime | habstractRuntime
    · rcases hobjectRuntime with ⟨hreturnObject, hchildRuntimeEq⟩
      subst childRuntime
      exact
        hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hobject hreturnObject hlookup rfl
    · rcases habstractRuntime with
        ⟨hreturnComposite, _hreturnNonObject, _hruntime⟩
      exact
        hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
          hobject hchildObject hlookup hreturnComposite hinclude
  have hobjectContext :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true ->
        PathLocalSelectionSetCurrentContext childSelectionSet
          (fieldPairPathLocalNextSelectionSet schema parentType
            childRuntime fieldName arguments currentSelectionSet) := by
    intro hreturnObject
    have hchildRuntimeEq :
        childRuntime = fieldDefinition.outputType.namedType := by
      rcases hruntime with hobjectRuntime | habstractRuntime
      · exact hobjectRuntime.2
      · rcases habstractRuntime with
          ⟨_hreturnComposite, hreturnNonObject, _hruntime⟩
        rw [hreturnObject] at hreturnNonObject
        simp at hreturnNonObject
    subst childRuntime
    have hallFields : selectionsAllFields childSelectionSet :=
      selectionSetNormal_allFields_of_object hchildNormal hreturnObject
    have hpruned :
        runtimePrunedSelectionSet schema
            fieldDefinition.outputType.namedType childSelectionSet =
          childSelectionSet :=
      runtimePrunedSelectionSet_eq_self_of_allFields schema
        fieldDefinition.outputType.namedType hallFields
    exact
      PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
        (schema := schema) (currentRuntimeType := parentType)
        (childRuntimeType := fieldDefinition.outputType.namedType)
        (targetField := fieldName) (responseName := responseName)
        (targetArguments := arguments) (arguments := arguments)
        (directives := directives) (selectionSet := selectionSet)
        (childSelectionSet := childSelectionSet)
        (currentSelectionSet := currentSelectionSet) hcontext hmem
        (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
  have habstractContext :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = false ->
        ∀ {bodyDirectives bodySelectionSet},
          Selection.inlineFragment (some childRuntime) bodyDirectives
            bodySelectionSet ∈ childSelectionSet ->
          PathLocalSelectionSetCurrentContext bodySelectionSet
            (fieldPairPathLocalNextSelectionSet schema parentType
              childRuntime fieldName arguments currentSelectionSet) := by
    intro _hreturnNonObject bodyDirectives bodySelectionSet hbodyMem
    exact
      PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
        (schema := schema) (currentRuntimeType := parentType)
        (childRuntimeType := childRuntime)
        (childParentType := fieldDefinition.outputType.namedType)
        (targetField := fieldName) (responseName := responseName)
        (targetArguments := arguments) (arguments := arguments)
        (directives := directives) (bodyDirectives := bodyDirectives)
        (selectionSet := selectionSet) (childSelectionSet := childSelectionSet)
        (bodySelectionSet := bodySelectionSet)
        (currentSelectionSet := currentSelectionSet) hcontext hmem hbodyMem
        (argumentsEquivalent_refl_forSyntaxDiff arguments) hchildNormal
        hchildObject
  exact
    ⟨childRuntime, hruntime, hinclude, hchildSupport, hobjectContext,
      habstractContext⟩

theorem pathLocalCompositeFieldResponsePathReady_of_valid_normal_support_context
    {schema : Schema}
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {variableDefinitions : List VariableDefinition}
    {selectionSet currentSelectionSet childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition} {responsePath : List Name}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> objectTypeNameBool schema parentType = true
      -> PathLocalSupportValidNormal schema parentType currentSelectionSet
      -> PathLocalSelectionSetCurrentContext selectionSet currentSelectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetResponsePath schema
          fieldDefinition.outputType.namedType childSelectionSet responsePath
      -> ∃ childRuntime,
          selectionSetRuntimeActive schema fieldDefinition.outputType.namedType
            childRuntime childSelectionSet
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
              childRuntime
            = true
          ∧ PathLocalSupportValidNormal schema childRuntime
              (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
                fieldName arguments currentSelectionSet)
          ∧ NormalSelectionSetResponsePath schema childRuntime
              (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
                fieldName arguments currentSelectionSet) responsePath
          ∧ (objectTypeNameBool schema fieldDefinition.outputType.namedType = true
              -> PathLocalSelectionSetCurrentContext childSelectionSet
                  (fieldPairPathLocalNextSelectionSet schema parentType
                    childRuntime fieldName arguments currentSelectionSet))
          ∧ (objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              -> ∀ {bodyDirectives bodySelectionSet},
                  Selection.inlineFragment (some childRuntime) bodyDirectives
                      bodySelectionSet
                    ∈ childSelectionSet
                  -> PathLocalSelectionSetCurrentContext bodySelectionSet
                      (fieldPairPathLocalNextSelectionSet schema parentType
                        childRuntime fieldName arguments currentSelectionSet)) := by
  intro hschema hvalid hnormal hparentObject hsupport hcontext hmem hlookup
    hcomposite hpath
  have hchildNormal :
      selectionSetNormal schema fieldDefinition.outputType.namedType
        childSelectionSet :=
    selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
  have hchildValid :
      Validation.selectionSetValid schema variableDefinitions
        fieldDefinition.outputType.namedType childSelectionSet :=
    selectionSetValid_field_child_of_mem_lookup hvalid hmem
      (normalSelectionSetResponsePath_selectionSet_nonempty hpath)
      hlookup
  rcases
      NormalSelectionSetResponsePath.runtimePruned_of_normal hchildValid
        hchildNormal hpath with
    ⟨childRuntime, hactive, hinclude, hprunedPath⟩
  have hmemCurrent :
      Selection.field responseName fieldName arguments directives
        childSelectionSet ∈ currentSelectionSet := by
    rcases hcontext with ⟨currentPref, currentSuff, hcurrent⟩
    subst currentSelectionSet
    exact
      List.mem_append.mpr
        (Or.inl (List.mem_append.mpr (Or.inr hmem)))
  have hchildObject : objectTypeNameBool schema childRuntime = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hinclude
  have hchildSupport :
      PathLocalSupportValidNormal schema childRuntime
        (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
          fieldName arguments currentSelectionSet) := by
    by_cases hreturnObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType = true
    · have hchildRuntimeEq :
          childRuntime = fieldDefinition.outputType.namedType :=
        typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
          hreturnObject hinclude
      subst childRuntime
      exact
        hsupport.fieldPairPathLocalNextSelectionSet_of_object_output
          hparentObject hreturnObject hlookup rfl
    · have hreturnNonObject :
        objectTypeNameBool schema fieldDefinition.outputType.namedType =
          false := by
        cases h :
            objectTypeNameBool schema fieldDefinition.outputType.namedType
        · rfl
        · exact False.elim (hreturnObject h)
      exact
        hsupport.fieldPairPathLocalNextSelectionSet_of_abstract_output
          hparentObject hchildObject hlookup hcomposite hinclude
  have hnextPath :
      NormalSelectionSetResponsePath schema childRuntime
        (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
          fieldName arguments currentSelectionSet) responsePath :=
    normalSelectionSetResponsePath_of_fieldPairPathLocalNextSelectionSet_field_mem
      (schema := schema) (currentRuntimeType := parentType)
      (childRuntimeType := childRuntime) (targetField := fieldName)
      (targetArguments := arguments) hmemCurrent
      (argumentsEquivalent_refl_forSyntaxDiff arguments) hprunedPath
  have hobjectContext :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = true ->
        PathLocalSelectionSetCurrentContext childSelectionSet
          (fieldPairPathLocalNextSelectionSet schema parentType childRuntime
            fieldName arguments currentSelectionSet) := by
    intro hreturnObject
    have hchildRuntimeEq :
        childRuntime = fieldDefinition.outputType.namedType :=
      typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
        hreturnObject hinclude
    subst childRuntime
    have hallFields : selectionsAllFields childSelectionSet :=
      selectionSetNormal_allFields_of_object hchildNormal hreturnObject
    have hpruned :
        runtimePrunedSelectionSet schema
            fieldDefinition.outputType.namedType childSelectionSet =
          childSelectionSet :=
      runtimePrunedSelectionSet_eq_self_of_allFields schema
        fieldDefinition.outputType.namedType hallFields
    exact
      PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_field_child
        (schema := schema) (currentRuntimeType := parentType)
        (childRuntimeType := fieldDefinition.outputType.namedType)
        (targetField := fieldName) (responseName := responseName)
        (targetArguments := arguments) (arguments := arguments)
        (directives := directives) (selectionSet := selectionSet)
        (childSelectionSet := childSelectionSet)
        (currentSelectionSet := currentSelectionSet) hcontext hmem
        (argumentsEquivalent_refl_forSyntaxDiff arguments) hpruned
  have habstractContext :
      objectTypeNameBool schema fieldDefinition.outputType.namedType = false ->
        ∀ {bodyDirectives bodySelectionSet},
          Selection.inlineFragment (some childRuntime) bodyDirectives
            bodySelectionSet ∈ childSelectionSet ->
          PathLocalSelectionSetCurrentContext bodySelectionSet
            (fieldPairPathLocalNextSelectionSet schema parentType
              childRuntime fieldName arguments currentSelectionSet) := by
    intro _hreturnNonObject bodyDirectives bodySelectionSet hbodyMem
    exact
      PathLocalSelectionSetCurrentContext.fieldPairPathLocalNextSelectionSet_inlineFragment_body
        (schema := schema) (currentRuntimeType := parentType)
        (childRuntimeType := childRuntime)
        (childParentType := fieldDefinition.outputType.namedType)
        (targetField := fieldName) (responseName := responseName)
        (targetArguments := arguments) (arguments := arguments)
        (directives := directives) (bodyDirectives := bodyDirectives)
        (selectionSet := selectionSet) (childSelectionSet := childSelectionSet)
        (bodySelectionSet := bodySelectionSet)
        (currentSelectionSet := currentSelectionSet) hcontext hmem hbodyMem
        (argumentsEquivalent_refl_forSyntaxDiff arguments) hchildNormal
        hchildObject
  exact
    ⟨childRuntime, hactive, hinclude, hchildSupport, hnextPath,
      hobjectContext, habstractContext⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
