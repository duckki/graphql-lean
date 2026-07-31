import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Variables
import Proofs.GraphQL.Theories.ResponseShape.Compute.Exclusion
import Proofs.GraphQL.Theories.ResponseShape.Compute.GroundInvariant
import Proofs.GraphQL.Theories.ResponseShape.Compute.RootBranches
import Proofs.GraphQL.Theories.ResponseShape.Compute.Stems
import Proofs.GraphQL.Validation.SelectionValidity

/-!
The decoder invariant for roots emitted by complete normalization.
-/

namespace GraphQL

namespace ResponseShape

private theorem decodeRootBranches_generatedCases_invariant
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List NormalForm.BoolVar) (hsupport : support.Nodup)
    (hsupportNonempty : support ≠ [])
    (parentType : Name) (hparentObject : schema.objectType parentType)
    (selectionSet : List Selection) :
    ∀ (boolCases : List NormalForm.BoolCase) (seen : List Clause),
      boolCases.Nodup ->
      (∀ boolCase, boolCase ∈ boolCases ->
        boolCase ∈ NormalForm.allBoolCases support) ->
      (∀ clause, clause ∈ seen ->
        ∃ seenCase,
          seenCase ∈ NormalForm.allBoolCases support
          ∧ seenCase ∉ boolCases
          ∧ clause = Clause.canonical { literals := seenCase }) ->
      ∃ shape,
        decodeRootBranches schema support parentType seen
            (List.flatten
              (boolCases.map
                (normalizedRootBranch schema parentType selectionSet))) =
          .ok shape
        ∧ DecoderShapeInvariant schema support parentType shape
        ∧ ∀ clause, clause ∈ seen -> ShapeExcludesClause clause shape
  | [], seen, _hcasesNodup, _hcasesGenerated, _hseen => by
      exact ⟨.object [], rfl, DecoderShapeInvariant.empty _ _ _,
        fun clause _ => ShapeExcludesClause.empty clause⟩
  | boolCase :: restCases, seen, hcasesNodup, hcasesGenerated, hseen => by
      have hcaseGenerated :
          boolCase ∈ NormalForm.allBoolCases support :=
        hcasesGenerated boolCase (by simp)
      have hrestGenerated :
          ∀ candidate, candidate ∈ restCases ->
            candidate ∈ NormalForm.allBoolCases support := by
        intro candidate hcandidate
        exact hcasesGenerated candidate
          (List.mem_cons_of_mem boolCase hcandidate)
      have hcaseNonempty : boolCase ≠ [] := by
        intro hnil
        have hnames :=
          NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
            hcaseGenerated
        simp [hnil] at hnames
        exact hsupportNonempty hnames
      have hcaseLength : boolCase.length = support.length :=
        boolCase_length_of_mem_allBoolCases hcaseGenerated
      have hparts := List.nodup_cons.mp hcasesNodup
      cases hbody :
          NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase boolCase selectionSet) with
      | nil =>
          simpa [normalizedRootBranch, hbody] using
            decodeRootBranches_generatedCases_invariant schema hschema support
              hsupport hsupportNonempty parentType hparentObject selectionSet
              restCases seen hparts.2 hrestGenerated
              (fun clause hclause => by
                rcases hseen clause hclause with
                  ⟨seenCase, hseenGenerated, hseenAbsent, hclauseEq⟩
                exact ⟨seenCase, hseenGenerated,
                  fun hseenRest =>
                    hseenAbsent
                      (List.mem_cons_of_mem boolCase hseenRest),
                  hclauseEq⟩)
      | cons bodyHead bodyTail =>
          let body := bodyHead :: bodyTail
          have hbodyNonempty : body ≠ [] := by simp [body]
          rcases
              NormalForm.CompleteNormalization.wrapWithBoolCase_singleton_of_ne
                boolCase body hcaseNonempty with
            ⟨wrappedSelection, hwrap⟩
          let clause : Clause := Clause.canonical { literals := boolCase }
          have hstem :
              decodeCompleteStem support.length wrappedSelection =
                .ok (boolCase, body) := by
            rw [← hcaseLength]
            exact decodeCompleteStem_wrapWithBoolCase hcaseNonempty
              hbodyNonempty hwrap
          have hclause :
              clauseFromCompleteStem support boolCase = .ok clause := by
            exact clauseFromCompleteStem_allBoolCases support hsupport
              hcaseGenerated
          have hclauseValid : clause.Valid support := by
            exact canonicalClause_valid_of_mem_allBoolCases support hsupport
              hcaseGenerated
          have hclauseComplete : clause.CompleteMinterm support := by
            exact canonicalClause_completeMinterm_of_mem_allBoolCases support
              hsupport hcaseGenerated
          have hclauseNotSeen : clause ∉ seen := by
            intro hclauseSeen
            rcases hseen clause hclauseSeen with
              ⟨seenCase, hseenGenerated, hseenAbsent, hseenClause⟩
            have hcaseEq : boolCase = seenCase :=
              canonicalClause_injective_of_mem_allBoolCases support hsupport
                hcaseGenerated hseenGenerated (by
                  change Clause.canonical { literals := boolCase } =
                    Clause.canonical { literals := seenCase }
                  exact hseenClause)
            exact hseenAbsent (by simp [hcaseEq])
          have hduplicate :
              seen.any (clausesEqualBool clause) = false :=
            clausesEqualBool_any_eq_false_of_not_mem clause seen hclauseNotSeen
          have hfilteredFree :
              NormalForm.selectionSetDirectiveFree
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet) :=
            NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
              schema boolCase selectionSet
          have himage : GroundSelectionSetImage schema parentType body := by
            simpa [body, hbody] using
              normalizeSelectionSet_groundSelectionSetImage schema hschema
                parentType
                (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
                hparentObject hfilteredFree
          rcases foldGroundSelectionSet_success_of_image_with_invariant
              schema support clause hclauseValid hclauseComplete himage with
            ⟨branchShape, hbranchShape, hbranchInvariant, hbranchClauses,
              _hbranchNames, _hbranchObjects⟩
          have hrestSeen :
              ∀ seenClause, seenClause ∈ clause :: seen ->
                ∃ seenCase,
                  seenCase ∈ NormalForm.allBoolCases support
                  ∧ seenCase ∉ restCases
                  ∧ seenClause =
                    Clause.canonical { literals := seenCase } := by
            intro seenClause hseenClause
            rcases List.mem_cons.mp hseenClause with hhead | htail
            · subst seenClause
              exact ⟨boolCase, hcaseGenerated, hparts.1, rfl⟩
            · rcases hseen seenClause htail with
                ⟨seenCase, hseenGenerated, hseenAbsent, hseenClauseEq⟩
              exact ⟨seenCase, hseenGenerated,
                fun hseenRest =>
                  hseenAbsent
                    (List.mem_cons_of_mem boolCase hseenRest),
                hseenClauseEq⟩
          rcases decodeRootBranches_generatedCases_invariant schema hschema support
              hsupport hsupportNonempty parentType hparentObject selectionSet
              restCases (clause :: seen) hparts.2 hrestGenerated hrestSeen with
            ⟨restShape, hrestShape, hrestInvariant, hrestExcludes⟩
          have hcompatible : MergeCompatible branchShape restShape :=
            mergeCompatible_of_clausesEqual_excludes clause branchShape restShape
              hbranchClauses (hrestExcludes clause (by simp))
          refine ⟨mergeResponseShapes branchShape restShape, ?_,
            mergeResponseShapes_decoderShapeInvariant schema support parentType
              branchShape restShape hbranchInvariant hrestInvariant hcompatible,
            ?_⟩
          · simp only [List.map_cons, List.flatten_cons]
            have hbranch :
                normalizedRootBranch schema parentType selectionSet boolCase =
                  NormalForm.wrapWithBoolCase boolCase body := by
              simp [normalizedRootBranch, hbody, body]
            rw [hbranch]
            change
              decodeRootBranches schema support parentType seen
                  (NormalForm.wrapWithBoolCase boolCase body ++
                    List.flatten
                      (List.map
                        (normalizedRootBranch schema parentType selectionSet)
                        restCases)) =
                .ok (mergeResponseShapes branchShape restShape)
            rw [hwrap]
            simp only [List.singleton_append]
            rw [decodeRootBranches, hstem]
            simp only [Bind.bind, Except.bind]
            rw [hclause]
            simp only
            rw [hduplicate]
            simp only [Bool.false_eq_true, if_false]
            rw [hbranchShape]
            rw [hrestShape]
          · intro seenClause hseenClause
            have hbranchExcludes :
                ShapeExcludesClause seenClause branchShape := by
              apply ShapeClausesEqual.excludes clause seenClause branchShape
                hbranchClauses
              intro heq
              exact hclauseNotSeen (heq ▸ hseenClause)
            exact ShapeExcludesClause.merge seenClause branchShape restShape
              hbranchExcludes
              (hrestExcludes seenClause
                (List.mem_cons_of_mem clause hseenClause))

/-- Complete root normalization decodes to a root satisfying the decoder invariant. -/
theorem decodeCompleteRoot_completeNormalizeRootSelectionSet_invariant
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List NormalForm.BoolVar) (hsupport : support.Nodup)
    (parentType : Name) (hparentObject : schema.objectType parentType)
    (selectionSet : List Selection) :
    ∃ shape,
      decodeCompleteRoot schema support parentType
          (NormalForm.completeNormalizeRootSelectionSet
            schema support parentType selectionSet) = .ok shape
      ∧ DecoderShapeInvariant schema support parentType shape := by
  have hduplicate : firstDuplicate? support = none :=
    firstDuplicate?_eq_none_of_nodup support hsupport
  cases support with
  | nil =>
      let clause : Clause := { literals := [] }
      have hvalid : clause.Valid [] := by rfl
      have hcomplete : clause.CompleteMinterm [] := by rfl
      have hfree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.filterSelectionSetBoolCase [] selectionSet) :=
        NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
          schema [] selectionSet
      have himage : GroundSelectionSetImage schema parentType
          (NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase [] selectionSet)) :=
        normalizeSelectionSet_groundSelectionSetImage schema hschema parentType
          (NormalForm.filterSelectionSetBoolCase [] selectionSet)
          hparentObject hfree
      rcases foldGroundSelectionSet_success_of_image_with_invariant
          schema [] clause hvalid hcomplete himage with
        ⟨shape, hshape, hinvariant, _hclauses, _hnames, _hobjects⟩
      refine ⟨shape, ?_, hinvariant⟩
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase [] selectionSet) with
      | nil =>
          simpa [decodeCompleteRoot, firstDuplicate?,
            NormalForm.completeNormalizeRootSelectionSet,
            NormalForm.allBoolCases, NormalForm.wrapWithBoolCase,
            clause, hnormalized] using hshape
      | cons head tail =>
          simpa [decodeCompleteRoot, firstDuplicate?,
            NormalForm.completeNormalizeRootSelectionSet,
            NormalForm.allBoolCases, NormalForm.wrapWithBoolCase,
            clause, hnormalized] using hshape
  | cons varName variables =>
      have hsupportNonempty : (varName :: variables) ≠ [] := by simp
      have hcasesNodup :
          (NormalForm.allBoolCases (varName :: variables)).Nodup :=
        NormalForm.CompleteNormalization.allBoolCases_nodup hsupport
      rcases decodeRootBranches_generatedCases_invariant schema hschema
          (varName :: variables) hsupport hsupportNonempty parentType
          hparentObject selectionSet
          (NormalForm.allBoolCases (varName :: variables)) [] hcasesNodup
          (fun boolCase hcase => hcase) (by simp) with
        ⟨shape, hshape, hinvariant, _hexcludes⟩
      refine ⟨shape, ?_, hinvariant⟩
      unfold NormalForm.completeNormalizeRootSelectionSet
      change decodeCompleteRoot schema (varName :: variables) parentType
          (List.flatten
            ((NormalForm.allBoolCases (varName :: variables)).map
              (normalizedRootBranch schema parentType selectionSet))) =
        .ok shape
      simpa [decodeCompleteRoot, hduplicate] using hshape

/-- A successful computation from a well-formed valid operation is well-formed. -/
theorem computeOperationShape_wellFormed
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape) :
    shape.WellFormed schema := by
  let support := NormalForm.operationBoolVars operation
  have hsupport : support.Nodup :=
    NormalForm.CompleteNormalization.dedupBoolVars_nodup _
  have hrootEq : operation.rootType schema = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject : schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  rcases decodeCompleteRoot_completeNormalizeRootSelectionSet_invariant
      schema hschema support hsupport (operation.rootType schema) hrootObject
      operation.selectionSet with
    ⟨root, hrootDecode, hrootInvariant⟩
  rcases computeOperationShape_fields schema operation shape hcompute with
    ⟨_hoperationType, hshapeRootType, hshapeSupport, hshapeRootDecode⟩
  have hroot : root = shape.root :=
    Except.ok.inj (hrootDecode.symm.trans (by
      simpa [NormalForm.completeNormalizeOperation] using hshapeRootDecode))
  apply computeOperationShape_wellFormed_of_invariant schema operation shape
    hcompute
  rw [hshapeSupport, hshapeRootType, ← hroot]
  exact hrootInvariant

end ResponseShape

end GraphQL
