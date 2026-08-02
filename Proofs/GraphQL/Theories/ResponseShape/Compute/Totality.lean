import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Variables
import Proofs.GraphQL.Theories.ResponseShape.Compute.Ground
import Proofs.GraphQL.Theories.ResponseShape.Compute.RootBranches
import Proofs.GraphQL.Theories.ResponseShape.Compute.RootInvariant
import Proofs.GraphQL.Theories.ResponseShape.Compute.Soundness
import Proofs.GraphQL.Theories.ResponseShape.Compute.Stems
import Proofs.GraphQL.Validation.SelectionValidity

/-!
Totality of response-shape computation on the image of complete normalization.

The acceptance proof follows the normalizer construction directly. It does not
identify the broader decoder grammar, or public response-shape well-formedness,
with the normalizer image.
-/

namespace GraphQL

namespace ResponseShape

private theorem decodeRootBranches_generatedCases_success
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
  | [], seen, _hcasesNodup, _hcasesGenerated, _hseen => by
      exact ⟨.object [], rfl⟩
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
            decodeRootBranches_generatedCases_success schema hschema support
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
          rcases foldGroundSelectionSet_normalizeSelectionSet_success
              schema clause parentType
              (NormalForm.filterSelectionSetBoolCase boolCase selectionSet)
              hschema hparentObject hfilteredFree with
            ⟨branchShape, hbranchShape⟩
          have hbranchShape' :
              foldGroundSelectionSet schema clause parentType body =
                .ok branchShape := by
            simpa [body, hbody] using hbranchShape
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
          rcases decodeRootBranches_generatedCases_success schema hschema support
              hsupport hsupportNonempty parentType hparentObject selectionSet
              restCases (clause :: seen) hparts.2 hrestGenerated hrestSeen with
            ⟨restShape, hrestShape⟩
          refine ⟨mergeResponseShapes branchShape restShape, ?_⟩
          simp only [List.map_cons, List.flatten_cons]
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
          rw [hbranchShape']
          rw [hrestShape]

/-- The complete root normalizer always produces input accepted by the root decoder. -/
theorem decodeCompleteRoot_completeNormalizeRootSelectionSet_success
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (support : List NormalForm.BoolVar) (hsupport : support.Nodup)
    (parentType : Name) (hparentObject : schema.objectType parentType)
    (selectionSet : List Selection) :
    ∃ shape,
      decodeCompleteRoot schema support parentType
          (NormalForm.completeNormalizeRootSelectionSet
            schema support parentType selectionSet) =
        .ok shape := by
  have hduplicate : firstDuplicate? support = none :=
    firstDuplicate?_eq_none_of_nodup support hsupport
  cases support with
  | nil =>
      have hfree :
          NormalForm.selectionSetDirectiveFree
            (NormalForm.filterSelectionSetBoolCase [] selectionSet) :=
        NormalForm.CompleteNormalization.filterSelectionSetBoolCase_directiveFree
          schema [] selectionSet
      rcases foldGroundSelectionSet_normalizeSelectionSet_success
          schema { literals := [] } parentType
          (NormalForm.filterSelectionSetBoolCase [] selectionSet)
          hschema hparentObject hfree with
        ⟨shape, hshape⟩
      refine ⟨shape, ?_⟩
      cases hnormalized :
          NormalForm.normalizeSelectionSet schema parentType
            (NormalForm.filterSelectionSetBoolCase [] selectionSet) with
      | nil =>
          simpa [decodeCompleteRoot, firstDuplicate?,
            NormalForm.completeNormalizeRootSelectionSet,
            NormalForm.allBoolCases, NormalForm.wrapWithBoolCase,
            hnormalized] using hshape
      | cons head tail =>
          simpa [decodeCompleteRoot, firstDuplicate?,
            NormalForm.completeNormalizeRootSelectionSet,
            NormalForm.allBoolCases, NormalForm.wrapWithBoolCase,
            hnormalized] using hshape
  | cons varName variables =>
      have hsupportNonempty : (varName :: variables) ≠ [] := by simp
      have hcasesNodup :
          (NormalForm.allBoolCases (varName :: variables)).Nodup :=
        NormalForm.CompleteNormalization.allBoolCases_nodup hsupport
      rcases decodeRootBranches_generatedCases_success schema hschema
          (varName :: variables)
          hsupport hsupportNonempty parentType hparentObject selectionSet
          (NormalForm.allBoolCases (varName :: variables)) [] hcasesNodup
          (fun boolCase hcase => hcase)
          (by simp) with
        ⟨shape, hshape⟩
      refine ⟨shape, ?_⟩
      unfold NormalForm.completeNormalizeRootSelectionSet
      change decodeCompleteRoot schema (varName :: variables) parentType
          (List.flatten
            ((NormalForm.allBoolCases (varName :: variables)).map
              (normalizedRootBranch schema parentType selectionSet))) =
        .ok shape
      simpa [decodeCompleteRoot, hduplicate] using hshape

/-- Complete-normal operation output is always accepted by the staged decoder. -/
theorem decodeCompleteOperationShape_completeNormalizeOperation_success
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation) :
    ∃ shape,
      decodeCompleteOperationShape schema
          (NormalForm.operationBoolVars operation)
          (NormalForm.completeNormalizeOperation schema operation) =
        .ok shape := by
  let support := NormalForm.operationBoolVars operation
  have hsupport : support.Nodup := by
    exact NormalForm.CompleteNormalization.dedupBoolVars_nodup _
  have hrootEq : operation.rootType schema = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject : schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  rcases decodeCompleteRoot_completeNormalizeRootSelectionSet_success
      schema hschema support hsupport (operation.rootType schema) hrootObject
      operation.selectionSet with
    ⟨root, hroot⟩
  refine ⟨{
      operationType := operation.operationType
      rootType := operation.rootType schema
      boolSupport := support
      root := root
    }, ?_⟩
  unfold decodeCompleteOperationShape
  unfold NormalForm.completeNormalizeOperation
  change
    (do
      let decodedRoot ←
        decodeCompleteRoot schema support (operation.rootType schema)
          (NormalForm.completeNormalizeRootSelectionSet schema support
            (operation.rootType schema) operation.selectionSet)
      .ok ({
        operationType := operation.operationType
        rootType := operation.rootType schema
        boolSupport := support
        root := decodedRoot
      } : OperationShape)) =
    .ok ({
      operationType := operation.operationType
      rootType := operation.rootType schema
      boolSupport := support
      root := root
    } : OperationShape)
  rw [hroot]
  rfl

/-- Response-shape computation succeeds for every well-formed valid query operation. -/
theorem computeOperationShape_success
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation) :
    ∃ shape, computeOperationShape schema operation = .ok shape := by
  simpa [computeOperationShape] using
    decodeCompleteOperationShape_completeNormalizeOperation_success
      schema operation hschema hvalid

/-- Successful response-shape computation preserves the source Boolean support. -/
theorem computeOperationShape_support
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape) :
    shape.boolSupport = NormalForm.operationBoolVars operation := by
  apply (decodeCompleteOperationShape_fields schema
    (NormalForm.operationBoolVars operation)
    (NormalForm.completeNormalizeOperation schema operation) shape ?_).2.2.1
  simpa [computeOperationShape] using hcompute

/-- Successful response-shape computation emits only complete-minterm guards. -/
theorem computeOperationShape_fullMinterm
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (hcompute : computeOperationShape schema operation = .ok shape) :
    shape.FullMinterm := by
  apply decodeCompleteOperationShape_fullMinterm schema
    (NormalForm.operationBoolVars operation)
    (NormalForm.completeNormalizeOperation schema operation) shape
  simpa [computeOperationShape] using hcompute

/-- Response-shape computation is total on valid operations over well-formed
schemas, and its result is well-formed, uses complete minterms, and preserves
the operation's Boolean-variable support. -/
theorem computeOperationShape_total
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation) :
    ∃ shape,
      computeOperationShape schema operation = .ok shape
      ∧ shape.WellFormed schema
      ∧ shape.FullMinterm
      ∧ shape.boolSupport = NormalForm.operationBoolVars operation := by
  rcases computeOperationShape_success schema operation hschema hvalid with
    ⟨shape, hcompute⟩
  exact ⟨shape, hcompute,
    computeOperationShape_wellFormed schema operation shape hschema hvalid
      hcompute,
    computeOperationShape_fullMinterm schema operation shape hcompute,
    computeOperationShape_support schema operation shape hcompute⟩

end ResponseShape

end GraphQL
