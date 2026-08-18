import GraphQL.Theories.ResponsePath
import Proofs.GraphQL.Theories.QueryInclusion.RegionSearch

/-!
Bridge between the response-path footprint and the query-inclusion reference checker.

Both directions are collection-level statements: path inclusion at one Boolean
environment is equivalent to `selectionSetIncludesBoolWithFuel` acceptance for valid,
semantically ready selection sets. The semantic content of query inclusion enters only
through the existing reference-checker theorems.
-/

namespace GraphQL
namespace ResponsePath

open Execution
open Execution.FieldGroups
open QueryInclusion
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager

-- A type reference whose possible objects are inhabited refers to a composite type.
theorem isCompositeBool_eq_true_of_typeIncludesObject
    {schema : Schema} {typeRef : TypeRef} {objectName : Name}
    (hincludes : schema.typeIncludesObject typeRef.namedType objectName)
    : typeRef.isCompositeBool schema = true := by
  unfold Schema.typeIncludesObject Schema.getPossibleTypes at hincludes
  unfold TypeRef.isCompositeBool
  cases hlookup : schema.lookupType typeRef.namedType with
  | none =>
      rw [hlookup] at hincludes
      cases hincludes
  | some typeDefinition =>
      rw [hlookup] at hincludes
      cases typeDefinition <;> first | rfl | cases hincludes

-----------------------------------------------------------------------------------------
-- Path inclusion implies reference-checker acceptance
-----------------------------------------------------------------------------------------

-- If, at one Boolean environment, every response path selected by the right selection
-- set from `parentType` is selected by the left selection set, then the reference fuel
-- checker accepts, provided the right response depth fits in the fuel. The path
-- hypothesis is scoped to the concrete collection object because nested collection
-- always happens at the concrete object recorded by the next path step.
theorem selectionSetIncludesBoolWithFuel_of_pathInclusion
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (hparentObject : schema.objectType parentType)
    (hleftReady
      : NormalForm.selectionSetSemanticsReady schema parentType leftSelectionSet)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema parentType leftSelectionSet)
    (hrightReady
      : NormalForm.selectionSetSemanticsReady schema parentType rightSelectionSet)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema parentType rightSelectionSet)
    (hdepth : selectionSetResponseDepth rightSelectionSet ≤ fuel)
    (hpaths
      : ∀ step rest,
          step.parentObject = parentType
          -> collectedFieldsSelectPath schema variableValues
              (collectFields schema variableValues parentType
                (.object parentType PUnit.unit) rightSelectionSet)
              (step :: rest)
          -> collectedFieldsSelectPath schema variableValues
              (collectFields schema variableValues parentType
                (.object parentType PUnit.unit) leftSelectionSet)
              (step :: rest))
    : selectionSetIncludesBoolWithFuel schema fuel parentType variableValues
        leftSelectionSet rightSelectionSet
      = true := by
  induction fuel generalizing parentType leftSelectionSet rightSelectionSet with
  | zero =>
      rw [selectionSetIncludesBoolWithFuel,
        getPossibleTypes_eq_singleton_of_object schema hparentObject]
      simp only [List.all_cons, List.all_nil, Bool.and_true,
        selectionSetIncludesAtRuntimeBoolWithFuel]
      apply List.isEmpty_iff.mpr
      let rightGroups := collectRuntimeFieldGroups schema variableValues parentType
        parentType rightSelectionSet
      change rightGroups = []
      cases hgroups : rightGroups with
      | nil => rfl
      | cons group rest =>
          rcases group with ⟨responseName, fields⟩
          have hgroupsReady := executableGroupsSemanticsReady_collectFields schema
            variableValues parentType PUnit.unit rightSelectionSet hparentObject
            hrightReady hrightMerge
          have hgroupReady := hgroupsReady responseName fields (by
            simpa [rightGroups, collectRuntimeFieldGroups] using
              show (responseName, fields) ∈ rightGroups by simp [hgroups])
          cases hfields : fields with
          | nil => exact False.elim (hgroupReady.1 hfields)
          | cons field fields =>
              have hbound := collectFields_responseDepth_bound schema variableValues
                parentType (ResolverValue.object parentType PUnit.unit) rightSelectionSet
              have hgroupMem : (responseName, field :: fields) ∈
                  collectFields schema variableValues parentType
                    (ResolverValue.object parentType PUnit.unit) rightSelectionSet := by
                simpa [rightGroups, collectRuntimeFieldGroups] using
                  show (responseName, field :: fields) ∈ rightGroups by
                    simp [hgroups, hfields]
              have hfieldFlat : field ∈
                  (collectFields schema variableValues parentType
                    (ResolverValue.object parentType PUnit.unit)
                    rightSelectionSet).flatMap Prod.snd := by
                exact List.mem_flatMap.mpr
                  ⟨(responseName, field :: fields), hgroupMem, by simp⟩
              have := hbound field hfieldFlat
              omega
  | succ childFuel ih =>
      rw [selectionSetIncludesBoolWithFuel,
        getPossibleTypes_eq_singleton_of_object schema hparentObject]
      simp only [List.all_cons, List.all_nil, Bool.and_true,
        selectionSetIncludesAtRuntimeBoolWithFuel]
      let source : ResolverValue PUnit := .object parentType PUnit.unit
      have hleftGroupsReady := executableGroupsSemanticsReady_collectFields schema
        variableValues parentType PUnit.unit leftSelectionSet hparentObject hleftReady
        hleftMerge
      have hrightGroupsReady := executableGroupsSemanticsReady_collectFields schema
        variableValues parentType PUnit.unit rightSelectionSet hparentObject hrightReady
        hrightMerge
      have hleftParents := collectFields_parent schema variableValues parentType source
        leftSelectionSet
      have hrightParents := collectFields_parent schema variableValues parentType source
        rightSelectionSet
      have hleftKeysNodup :=
        (executableGroupNamesNodup_iff_map_fst_nodup _).mp
          (NormalForm.collectFields_namesNodup schema variableValues parentType source
            leftSelectionSet)
      have hrightWellFormed :=
        NormalForm.GroundTypeNormalization.collectFields_wellFormed schema variableValues
          parentType source rightSelectionSet
      apply List.all_eq_true.mpr
      intro rightGroup hrightGroup
      rcases rightGroup with ⟨rightName, rightFields⟩
      have hrightGroup' : (rightName, rightFields) ∈
          collectFields schema variableValues parentType source rightSelectionSet := by
        simpa [source, collectRuntimeFieldGroups] using hrightGroup
      have hrightGroupReady := hrightGroupsReady rightName rightFields hrightGroup'
      obtain ⟨rightHead, rightRest, rfl⟩ :=
        List.exists_cons_of_ne_nil hrightGroupReady.1
      have hrightHeadMem : rightHead ∈ rightHead :: rightRest := by simp
      rcases hrightGroupReady.2.1 rightHead hrightHeadMem with
        ⟨definition, hlookup, _hchildReady⟩
      have hrightHeadParent : rightHead.parentType = parentType :=
        hrightParents rightName (rightHead :: rightRest) hrightGroup' rightHead
          hrightHeadMem
      have hrightHeadName : rightHead.responseName = rightName :=
        (hrightWellFormed (rightName, rightHead :: rightRest) hrightGroup').2 rightHead
          hrightHeadMem
      -- The head step realized by the right group under this Boolean environment.
      let headStep : PathStep :=
        { parentObject := parentType
          responseName := rightName
          field :=
            { fieldName := rightHead.fieldName
              arguments := rightHead.arguments
              outputType := definition.outputType } }
      have hheadMatch : executableFieldMatchesPathStep schema rightHead headStep := by
        refine ⟨hrightHeadName, rfl, ?_, definition, ?_, rfl⟩
        · exact NormalForm.GroundTypeNormalization.argumentsEquivalent_refl
            rightHead.arguments
        · show schema.lookupField parentType rightHead.fieldName = some definition
          rw [← hrightHeadParent]
          exact hlookup
      have hrightSelects : collectedFieldsSelectPath schema variableValues
          (collectFields schema variableValues parentType source rightSelectionSet)
          [headStep] := by
        simp only [collectedFieldsSelectPath]
        exact ⟨rightHead :: rightRest, hrightGroup', rightHead, hrightHeadMem, hheadMatch⟩
      have hleftSelects := hpaths headStep [] rfl hrightSelects
      simp only [collectedFieldsSelectPath] at hleftSelects
      obtain ⟨leftFields, hleftGroupMem, leftWitness, hleftWitnessMem, hleftMatch⟩ :=
        hleftSelects
      obtain ⟨hleftWitnessName, hleftWitnessFieldName, hleftWitnessArgs, _witnessDefinition,
        _hwitnessLookup, _hwitnessOutput⟩ := hleftMatch
      have hleftGroupReady := hleftGroupsReady rightName leftFields hleftGroupMem
      obtain ⟨leftHead, leftRest, rfl⟩ := List.exists_cons_of_ne_nil hleftGroupReady.1
      have hleftHeadMem : leftHead ∈ leftHead :: leftRest := by simp
      apply List.any_eq_true.mpr
      refine ⟨(rightName, leftHead :: leftRest), ?_, ?_⟩
      · simpa [source, collectRuntimeFieldGroups] using hleftGroupMem
      rcases hleftGroupReady.2.2.1 leftHead leftWitness hleftHeadMem hleftWitnessMem with
        ⟨_hleftHeadWitnessParent, hleftHeadWitnessFieldName, hleftHeadWitnessArgs⟩
      have hleftHeadParent : leftHead.parentType = parentType :=
        hleftParents rightName (leftHead :: leftRest) hleftGroupMem leftHead hleftHeadMem
      have hparent : leftHead.parentType = rightHead.parentType :=
        hleftHeadParent.trans hrightHeadParent.symm
      have hfieldName : leftHead.fieldName = rightHead.fieldName :=
        hleftHeadWitnessFieldName.trans hleftWitnessFieldName
      have harguments : Argument.argumentsEquivalent leftHead.arguments
          rightHead.arguments :=
        argumentsEquivalent_trans hleftHeadWitnessArgs hleftWitnessArgs
      simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
      refine ⟨⟨⟨beq_iff_eq.mpr hparent, beq_iff_eq.mpr hfieldName⟩,
        (argumentsSyntacticallyEquivalentBool_iff _ _).mpr harguments⟩, ?_⟩
      rw [hlookup]
      cases hcomposite : definition.outputType.isCompositeBool schema with
      | false => simp [hcomposite]
      | true =>
          simp only [hcomposite, if_true, List.all_eq_true]
          intro childRuntimeType hchildRuntime
          have hchildObject : schema.objectType childRuntimeType :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
              definition.outputType.namedType childRuntimeType hchildRuntime
          have hincludes : schema.typeIncludesObjectBool
              definition.outputType.namedType childRuntimeType = true :=
            List.contains_iff_mem.mpr hchildRuntime
          have hleftWitnessLookup : schema.lookupField leftWitness.parentType
              leftWitness.fieldName = some definition := by
            have hleftWitnessParent : leftWitness.parentType = parentType :=
              hleftParents rightName (leftHead :: leftRest) hleftGroupMem leftWitness
                hleftWitnessMem
            rw [hleftWitnessParent, hleftWitnessFieldName]
            show schema.lookupField parentType rightHead.fieldName = some definition
            rw [← hrightHeadParent]
            exact hlookup
          have hleftCompletion : completionFieldsSemanticsReady schema
              definition.outputType (leftHead :: leftRest) :=
            ⟨hleftGroupReady, leftWitness, definition, hleftWitnessMem,
              hleftWitnessLookup, rfl⟩
          have hrightCompletion : completionFieldsSemanticsReady schema
              definition.outputType (rightHead :: rightRest) :=
            ⟨hrightGroupReady, rightHead, definition, hrightHeadMem, hlookup, rfl⟩
          have hrightFieldsDepth : ExecutableFieldsResponseDepthBound
              (rightHead :: rightRest) (childFuel + 1) := by
            intro field hfield
            have hbound := collectFields_responseDepth_bound schema variableValues
              parentType source rightSelectionSet
            have hfieldFlat : field ∈
                (collectFields schema variableValues parentType source
                  rightSelectionSet).flatMap Prod.snd :=
              List.mem_flatMap.mpr ⟨(rightName, rightHead :: rightRest), hrightGroup',
                hfield⟩
            exact Nat.le_trans (hbound field hfieldFlat) hdepth
          have hchildDepth : selectionSetResponseDepth
              (executableFieldsMergedSelectionSet (rightHead :: rightRest))
                ≤ childFuel :=
            selectionSetResponseDepth_flatMap_le (rightHead :: rightRest) childFuel
              hrightFieldsDepth
          -- Lift child paths into parent paths through this response-name group.
          have hchildPaths : ∀ step rest,
              step.parentObject = childRuntimeType
              -> collectedFieldsSelectPath schema variableValues
                  (collectFields schema variableValues childRuntimeType
                    (.object childRuntimeType PUnit.unit)
                    (executableFieldsMergedSelectionSet (rightHead :: rightRest)))
                  (step :: rest)
              -> collectedFieldsSelectPath schema variableValues
                  (collectFields schema variableValues childRuntimeType
                    (.object childRuntimeType PUnit.unit)
                    (executableFieldsMergedSelectionSet (leftHead :: leftRest)))
                  (step :: rest) := by
            intro step rest hscope hchildRight
            have hrightCons : collectedFieldsSelectPath schema variableValues
                (collectFields schema variableValues parentType source rightSelectionSet)
                (headStep :: step :: rest) := by
              simp only [collectedFieldsSelectPath]
              refine ⟨rightHead :: rightRest, hrightGroup',
                ⟨rightHead, hrightHeadMem, hheadMatch⟩, ?_, ?_⟩
              · show schema.typeIncludesObject definition.outputType.namedType
                  step.parentObject
                rw [hscope]
                exact hchildRuntime
              · rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
                  hscope, ← executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                exact hchildRight
            have hleftCons := hpaths headStep (step :: rest) rfl hrightCons
            simp only [collectedFieldsSelectPath] at hleftCons
            obtain ⟨leftFields2, hleftGroupMem2, _hwitness2, _htype2, hchildLeft⟩ :=
              hleftCons
            have hgroupEq : (rightName, leftFields2) = (rightName, leftHead :: leftRest) :=
              pair_eq_of_map_fst_nodup hleftKeysNodup hleftGroupMem2 hleftGroupMem rfl
            injection hgroupEq with _ hfieldsEq
            subst hfieldsEq
            rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
              hscope, ← executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              at hchildLeft
            exact hchildLeft
          have hleftChildReady :=
            completionFieldsSemanticsReady_merged_semantics hleftCompletion hincludes
          have hrightChildReady :=
            completionFieldsSemanticsReady_merged_semantics hrightCompletion hincludes
          have hleftChildMerge :=
            completionFieldsSemanticsReady_merged_canMerge hleftCompletion
              childRuntimeType
          have hrightChildMerge :=
            completionFieldsSemanticsReady_merged_canMerge hrightCompletion
              childRuntimeType
          have hresult := ih childRuntimeType
            (executableFieldsMergedSelectionSet (leftHead :: leftRest))
            (executableFieldsMergedSelectionSet (rightHead :: rightRest)) hchildObject
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hleftChildReady)
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hleftChildMerge)
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hrightChildReady)
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hrightChildMerge)
            hchildDepth hchildPaths
          exact hresult

-----------------------------------------------------------------------------------------
-- Reference-checker acceptance implies path inclusion
-----------------------------------------------------------------------------------------

-- Converse direction: acceptance of the reference fuel checker forces every right
-- selected path to be left selected. The step scope premise records that the path's
-- head step executes at the concrete collection object.
theorem selectsPath_of_selectionSetIncludesBoolWithFuel
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (variableValues : VariableValues)
    : ∀ (rest : List PathStep) (step : PathStep) (fuel : Nat) (parentType : Name)
        (leftSelectionSet rightSelectionSet : List Selection),
        schema.objectType parentType
        -> NormalForm.selectionSetSemanticsReady schema parentType leftSelectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType leftSelectionSet
        -> NormalForm.selectionSetSemanticsReady schema parentType rightSelectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType rightSelectionSet
        -> selectionSetIncludesBoolWithFuel schema fuel parentType variableValues
              leftSelectionSet rightSelectionSet
            = true
        -> step.parentObject = parentType
        -> collectedFieldsSelectPath schema variableValues
            (collectFields schema variableValues parentType
              (.object parentType PUnit.unit) rightSelectionSet)
            (step :: rest)
        -> collectedFieldsSelectPath schema variableValues
            (collectFields schema variableValues parentType
              (.object parentType PUnit.unit) leftSelectionSet)
            (step :: rest) := by
  intro rest
  induction rest with
  | nil =>
      intro step fuel parentType leftSelectionSet rightSelectionSet hparentObject
        hleftReady hleftMerge hrightReady hrightMerge hcheck hscope hrightSel
      simp only [collectedFieldsSelectPath] at hrightSel ⊢
      obtain ⟨rightFields, hrightMem, rightWitness, hrightWitnessMem, hrightMatch⟩ :=
        hrightSel
      obtain ⟨rightHead, rightRest, rfl⟩ :=
        List.exists_cons_of_ne_nil (List.ne_nil_of_mem hrightWitnessMem)
      rw [selectionSetIncludesBoolWithFuel,
        getPossibleTypes_eq_singleton_of_object schema hparentObject] at hcheck
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hcheck
      cases fuel with
      | zero =>
          rw [selectionSetIncludesAtRuntimeBoolWithFuel] at hcheck
          rw [List.isEmpty_iff] at hcheck
          have hrightMem' : (step.responseName, rightHead :: rightRest)
              ∈ collectRuntimeFieldGroups schema variableValues parentType parentType
                  rightSelectionSet := hrightMem
          rw [hcheck] at hrightMem'
          cases hrightMem'
      | succ childFuel =>
          rw [selectionSetIncludesAtRuntimeBoolWithFuel] at hcheck
          have hgroupCheck := List.all_eq_true.mp hcheck
            (step.responseName, rightHead :: rightRest) hrightMem
          rcases List.any_eq_true.mp hgroupCheck with
            ⟨⟨leftName, leftFields⟩, hleftMem, hentry⟩
          obtain ⟨leftHead, leftRest, rfl⟩ : ∃ head tail, leftFields = head :: tail := by
            cases leftFields with
            | nil => simp at hentry
            | cons head tail => exact ⟨head, tail, rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hentry
          obtain ⟨hleftName, ⟨⟨_hparentEq, hfieldNameEq⟩, hargumentsBool⟩, _hlookupPart⟩ :=
            hentry
          subst hleftName
          obtain ⟨hrightWitnessName, hrightWitnessFieldName, hrightWitnessArgs,
            witnessDefinition, hwitnessLookup, hwitnessOutput⟩ := hrightMatch
          have hrightGroupsReady := executableGroupsSemanticsReady_collectFields schema
            variableValues parentType PUnit.unit rightSelectionSet hparentObject
            hrightReady hrightMerge
          have hrightGroupReady := hrightGroupsReady step.responseName
            (rightHead :: rightRest) hrightMem
          rcases hrightGroupReady.2.2.1 rightHead rightWitness (by simp)
              hrightWitnessMem with
            ⟨_hheadWitnessParent, hheadWitnessFieldName, hheadWitnessArgs⟩
          have hleftWellFormed :=
            NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
              variableValues parentType (ResolverValue.object parentType PUnit.unit)
              leftSelectionSet
          have hleftHeadName : leftHead.responseName = step.responseName :=
            (hleftWellFormed (step.responseName, leftHead :: leftRest) hleftMem).2
              leftHead (by simp)
          refine ⟨leftHead :: leftRest, hleftMem, leftHead, by simp, ?_⟩
          refine ⟨hleftHeadName, ?_, ?_, witnessDefinition, hwitnessLookup,
            hwitnessOutput⟩
          · exact hfieldNameEq.trans
              (hheadWitnessFieldName.trans hrightWitnessFieldName)
          · exact argumentsEquivalent_trans
              ((argumentsSyntacticallyEquivalentBool_iff _ _).mp hargumentsBool)
              (argumentsEquivalent_trans hheadWitnessArgs hrightWitnessArgs)
  | cons next restTail ih =>
      intro step fuel parentType leftSelectionSet rightSelectionSet hparentObject
        hleftReady hleftMerge hrightReady hrightMerge hcheck hscope hrightSel
      simp only [collectedFieldsSelectPath] at hrightSel ⊢
      obtain ⟨rightFields, hrightMem, ⟨rightWitness, hrightWitnessMem, hrightMatch⟩,
        htypeIncludes, hchildRight⟩ := hrightSel
      obtain ⟨rightHead, rightRest, rfl⟩ :=
        List.exists_cons_of_ne_nil (List.ne_nil_of_mem hrightWitnessMem)
      rw [selectionSetIncludesBoolWithFuel,
        getPossibleTypes_eq_singleton_of_object schema hparentObject] at hcheck
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hcheck
      cases fuel with
      | zero =>
          rw [selectionSetIncludesAtRuntimeBoolWithFuel] at hcheck
          rw [List.isEmpty_iff] at hcheck
          have hrightMem' : (step.responseName, rightHead :: rightRest)
              ∈ collectRuntimeFieldGroups schema variableValues parentType parentType
                  rightSelectionSet := hrightMem
          rw [hcheck] at hrightMem'
          cases hrightMem'
      | succ childFuel =>
          rw [selectionSetIncludesAtRuntimeBoolWithFuel] at hcheck
          have hgroupCheck := List.all_eq_true.mp hcheck
            (step.responseName, rightHead :: rightRest) hrightMem
          rcases List.any_eq_true.mp hgroupCheck with
            ⟨⟨leftName, leftFields⟩, hleftMem, hentry⟩
          obtain ⟨leftHead, leftRest, rfl⟩ : ∃ head tail, leftFields = head :: tail := by
            cases leftFields with
            | nil => simp at hentry
            | cons head tail => exact ⟨head, tail, rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hentry
          obtain ⟨hleftName, ⟨⟨_hparentEq, hfieldNameEq⟩, hargumentsBool⟩, hlookupPart⟩ :=
            hentry
          subst hleftName
          obtain ⟨hrightWitnessName, hrightWitnessFieldName, hrightWitnessArgs,
            witnessDefinition, hwitnessLookup, hwitnessOutput⟩ := hrightMatch
          have hleftGroupsReady := executableGroupsSemanticsReady_collectFields schema
            variableValues parentType PUnit.unit leftSelectionSet hparentObject
            hleftReady hleftMerge
          have hrightGroupsReady := executableGroupsSemanticsReady_collectFields schema
            variableValues parentType PUnit.unit rightSelectionSet hparentObject
            hrightReady hrightMerge
          have hleftGroupReady := hleftGroupsReady step.responseName
            (leftHead :: leftRest) hleftMem
          have hrightGroupReady := hrightGroupsReady step.responseName
            (rightHead :: rightRest) hrightMem
          rcases hrightGroupReady.2.2.1 rightHead rightWitness (by simp)
              hrightWitnessMem with
            ⟨_hheadWitnessParent, hheadWitnessFieldName, hheadWitnessArgs⟩
          have hrightParents := collectFields_parent schema variableValues parentType
            (ResolverValue.object parentType PUnit.unit) rightSelectionSet
          have hleftParents := collectFields_parent schema variableValues parentType
            (ResolverValue.object parentType PUnit.unit) leftSelectionSet
          have hrightHeadParent : rightHead.parentType = parentType :=
            hrightParents step.responseName (rightHead :: rightRest) hrightMem rightHead
              (by simp)
          have hleftHeadParent : leftHead.parentType = parentType :=
            hleftParents step.responseName (leftHead :: leftRest) hleftMem leftHead
              (by simp)
          -- The checker's lookup is the path step's lookup.
          rcases hrightGroupReady.2.1 rightHead (by simp) with
            ⟨definition, hlookup, _hchildReady⟩
          have hlookupAtStep : schema.lookupField step.parentObject
              step.field.fieldName = some definition := by
            rw [hscope, ← hrightHeadParent, ← hrightWitnessFieldName,
              ← hheadWitnessFieldName]
            exact hlookup
          have hdefinitionEq : witnessDefinition = definition := by
            have h := hlookupAtStep
            rw [hwitnessLookup] at h
            exact Option.some.inj h
          rw [hdefinitionEq] at hwitnessLookup hwitnessOutput
          have houtputEq : definition.outputType = step.field.outputType :=
            hwitnessOutput
          -- The child scope is a possible object of the step's output type.
          have hnextPossible : next.parentObject
              ∈ schema.getPossibleTypes definition.outputType.namedType := by
            rw [houtputEq]
            exact htypeIncludes
          have hcomposite : definition.outputType.isCompositeBool schema = true := by
            apply isCompositeBool_eq_true_of_typeIncludesObject (objectName :=
              next.parentObject)
            rw [houtputEq]
            exact htypeIncludes
          simp only [hlookup, hcomposite, ↓reduceIte] at hlookupPart
          have hchildCheck := List.all_eq_true.mp hlookupPart next.parentObject
            hnextPossible
          have hchildObject : schema.objectType next.parentObject :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
              definition.outputType.namedType next.parentObject hnextPossible
          have hincludesBool : schema.typeIncludesObjectBool
              definition.outputType.namedType next.parentObject = true :=
            List.contains_iff_mem.mpr hnextPossible
          have hleftHeadLookup : schema.lookupField leftHead.parentType
              leftHead.fieldName = some definition := by
            rw [hleftHeadParent, hfieldNameEq, ← hrightHeadParent]
            exact hlookup
          have hleftCompletion : completionFieldsSemanticsReady schema
              definition.outputType (leftHead :: leftRest) :=
            ⟨hleftGroupReady, leftHead, definition, by simp, hleftHeadLookup, rfl⟩
          have hrightCompletion : completionFieldsSemanticsReady schema
              definition.outputType (rightHead :: rightRest) :=
            ⟨hrightGroupReady, rightHead, definition, by simp, hlookup, rfl⟩
          have hchildRight' : collectedFieldsSelectPath schema variableValues
              (collectFields schema variableValues next.parentObject
                (.object next.parentObject PUnit.unit)
                (executableFieldsMergedSelectionSet (rightHead :: rightRest)))
              (next :: restTail) := by
            rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
              ← executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              at hchildRight
            exact hchildRight
          have hleftChildReady :=
            completionFieldsSemanticsReady_merged_semantics hleftCompletion hincludesBool
          have hrightChildReady :=
            completionFieldsSemanticsReady_merged_semantics hrightCompletion
              hincludesBool
          have hleftChildMerge :=
            completionFieldsSemanticsReady_merged_canMerge hleftCompletion
              next.parentObject
          have hrightChildMerge :=
            completionFieldsSemanticsReady_merged_canMerge hrightCompletion
              next.parentObject
          have hchildLeft := ih next childFuel next.parentObject
            (executableFieldsMergedSelectionSet (leftHead :: leftRest))
            (executableFieldsMergedSelectionSet (rightHead :: rightRest)) hchildObject
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hleftChildReady)
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hleftChildMerge)
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hrightChildReady)
            (by simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
              using hrightChildMerge)
            hchildCheck rfl hchildRight'
          have hleftWellFormed :=
            NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
              variableValues parentType (ResolverValue.object parentType PUnit.unit)
              leftSelectionSet
          have hleftHeadName : leftHead.responseName = step.responseName :=
            (hleftWellFormed (step.responseName, leftHead :: leftRest) hleftMem).2
              leftHead (by simp)
          refine ⟨leftHead :: leftRest, hleftMem, ⟨leftHead, by simp, ?_⟩,
            htypeIncludes, ?_⟩
          · refine ⟨hleftHeadName, ?_, ?_, definition, hwitnessLookup, hwitnessOutput⟩
            · exact hfieldNameEq.trans
                (hheadWitnessFieldName.trans hrightWitnessFieldName)
            · exact argumentsEquivalent_trans
                ((argumentsSyntacticallyEquivalentBool_iff _ _).mp hargumentsBool)
                (argumentsEquivalent_trans hheadWitnessArgs hrightWitnessArgs)
          · rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
              ← executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
            exact hchildLeft

end ResponsePath
end GraphQL
