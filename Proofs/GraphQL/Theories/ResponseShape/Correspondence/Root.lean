import Proofs.GraphQL.Theories.ResponseShape.Compute.RootInvariant
import Proofs.GraphQL.Theories.ResponseShape.Compute.Soundness
import Proofs.GraphQL.Theories.ResponseShape.Compute.Stems
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Ground
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Normalization

/-!
Root-branch correspondence between complete-normal decoding and the selected
field footprint of the source operation.
-/

namespace GraphQL

namespace ResponseShape

open NormalForm
open NormalForm.CompleteNormalization

private theorem ShapeClausesEqual.holdsIn_of_denotesPath
    {schema : Schema} {clause : Clause} {assignment : NormalForm.BoolCase}
    {parentType : Name} {shape : ResponseShape} {path : List PathStep}
    (hclauses : ShapeClausesEqual clause shape)
    (hdenotes : shape.DenotesPath schema assignment parentType path) :
    clause.HoldsIn assignment := by
  cases hdenotes with
  | @field _ _ position possible definition _runtimeObject
      _runtimePossible positionMem possibleMem _runtimeMem definitionMem
      clauseHolds =>
      have heq := hclauses position positionMem possible possibleMem
        definition definitionMem
      simpa [heq] using clauseHolds
  | @child _ _ position possible definition _runtimeObject _childShape
      _childPath _runtimePossible positionMem possibleMem _runtimeMem
      definitionMem clauseHolds _subshapeEq _childDenotes =>
      have heq := hclauses position positionMem possible possibleMem
        definition definitionMem
      simpa [heq] using clauseHolds

private theorem ShapeClausesEqual.not_denotesEquivalentPath
    {schema : Schema} {clause : Clause}
    {assignment : NormalForm.BoolCase} {parentType : Name}
    {shape : ResponseShape} {path : List PathStep}
    (hclauses : ShapeClausesEqual clause shape)
    (hinactive : ¬ clause.HoldsIn assignment) :
    ¬ shape.DenotesEquivalentPath schema assignment parentType path := by
  rintro ⟨denotedPath, hdenotes, _hequivalent⟩
  exact hinactive (hclauses.holdsIn_of_denotesPath hdenotes)

private theorem selectionSetSelectsPath_empty
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (path : List PathStep) :
    ¬ selectionSetSelectsPath schema variableValues parentType [] path := by
  cases path with
  | nil => simp
  | cons step rest =>
      rw [selectionSetSelectsPath_cons_iff]
      rintro ⟨_hincludes, hpath⟩
      simp [NormalForm.GroundTypeNormalization.collectFields_nil] at hpath
      cases rest with
      | nil =>
          rw [collectedFieldsSelectPath_singleton] at hpath
          simp at hpath
      | cons next tail =>
          rw [collectedFieldsSelectPath_cons_cons] at hpath
          simp at hpath

private theorem selectionSetSelectsPath_normalize_filter_iff
    (schema : Schema) (operation : Operation)
    (boolCase : NormalForm.BoolCase)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation))
    (path : List PathStep) :
    selectionSetSelectsPath schema variableValues (operation.rootType schema)
        (normalizeSelectionSet schema (operation.rootType schema)
          (filterSelectionSetBoolCase boolCase operation.selectionSet)) path
      ↔
    selectionSetSelectsPath schema variableValues (operation.rootType schema)
        operation.selectionSet path := by
  cases path with
  | nil => simp
  | cons step rest =>
      rw [selectionSetSelectsPath_cons_iff,
        selectionSetSelectsPath_cons_iff]
      constructor
      · rintro ⟨hincludes, hpath⟩
        have hrootObject : schema.objectType (operation.rootType schema) := by
          have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
          rw [hrootEq]
          exact hschema.2.1
        have hrootBool : objectTypeNameBool schema
            (operation.rootType schema) = true :=
          GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
            schema hrootObject
        have hstep : step.parentObject = operation.rootType schema :=
          GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
            schema hrootBool (List.contains_iff_mem.mpr hincludes)
        have hbridge :=
          collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation boolCase variableValues step rest hschema hvalid
              hagrees hincludes
        rw [hstep] at hincludes hpath hbridge ⊢
        exact ⟨hincludes, hbridge.mp hpath⟩
      · rintro ⟨hincludes, hpath⟩
        have hrootObject : schema.objectType (operation.rootType schema) := by
          have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
          rw [hrootEq]
          exact hschema.2.1
        have hrootBool : objectTypeNameBool schema
            (operation.rootType schema) = true :=
          GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
            schema hrootObject
        have hstep : step.parentObject = operation.rootType schema :=
          GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
            schema hrootBool (List.contains_iff_mem.mpr hincludes)
        have hbridge :=
          collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation boolCase variableValues step rest hschema hvalid
              hagrees hincludes
        rw [hstep] at hincludes hpath hbridge ⊢
        exact ⟨hincludes, hbridge.mpr hpath⟩

private theorem decodeRootBranches_generatedCases_correspondence
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (operation : Operation)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (support : List NormalForm.BoolVar) (hsupport : support.Nodup)
    (hsupportEq : support = operationBoolVars operation)
    (hsupportNonempty : support ≠ [])
    (parentType : Name) (hparentEq : parentType = operation.rootType schema)
    (hparentObject : schema.objectType parentType)
    (assignment runtimeCase : NormalForm.BoolCase)
    (hassignment : completeNormalBoolCase support assignment)
    (hruntimeMem : runtimeCase ∈ allBoolCases support)
    (hruntimeAgrees : variableValuesAgreeWithCase
      (boolCaseVariableValues assignment) runtimeCase support) :
    ∀ (boolCases : List NormalForm.BoolCase) (seen : List Clause)
        (shape : ResponseShape),
      boolCases.Nodup ->
      (∀ boolCase, boolCase ∈ boolCases ->
        boolCase ∈ allBoolCases support) ->
      (∀ clause, clause ∈ seen ->
        ∃ seenCase,
          seenCase ∈ allBoolCases support
          ∧ seenCase ∉ boolCases
          ∧ clause = Clause.canonical { literals := seenCase }) ->
      decodeRootBranches schema support parentType seen
          (List.flatten
            (boolCases.map
              (normalizedRootBranch schema parentType operation.selectionSet))) =
        .ok shape ->
      ∀ path,
        shape.DenotesEquivalentPath schema assignment parentType path
          ↔ if runtimeCase ∈ boolCases then
              selectionSetSelectsPath schema
                (boolCaseVariableValues assignment) parentType
                (normalizeSelectionSet schema parentType
                  (filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet)) path
            else False
  | [], seen, shape, _hcasesNodup, _hcasesGenerated, _hseen, hdecode,
      path => by
      have hshape : shape = .object [] := (Except.ok.inj hdecode).symm
      subst shape
      simp only [List.not_mem_nil, ↓reduceIte]
      unfold ResponseShape.DenotesEquivalentPath
      constructor
      · rintro ⟨denotedPath, hdenotes, _hequivalent⟩
        cases hdenotes with
        | field _ positionMem _ _ _ _ => simp at positionMem
        | child _ positionMem _ _ _ _ _ _ => simp at positionMem
      · intro hfalse
        exact False.elim hfalse
  | boolCase :: restCases, seen, shape, hcasesNodup, hcasesGenerated,
      hseen, hdecode, path => by
      have hcaseGenerated : boolCase ∈ allBoolCases support :=
        hcasesGenerated boolCase (by simp)
      have hrestGenerated :
          ∀ candidate, candidate ∈ restCases ->
            candidate ∈ allBoolCases support := by
        intro candidate hcandidate
        exact hcasesGenerated candidate
          (List.mem_cons_of_mem boolCase hcandidate)
      have hcaseNonempty : boolCase ≠ [] := by
        intro hnil
        have hnames := boolCase_map_fst_of_mem_allBoolCases hcaseGenerated
        simp [hnil] at hnames
        exact hsupportNonempty hnames
      have hcaseLength : boolCase.length = support.length :=
        boolCase_length_of_mem_allBoolCases hcaseGenerated
      have hparts := List.nodup_cons.mp hcasesNodup
      cases hbody :
          normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase boolCase operation.selectionSet) with
      | nil =>
          have hrestSeen :
              ∀ clause, clause ∈ seen ->
                ∃ seenCase,
                  seenCase ∈ allBoolCases support
                  ∧ seenCase ∉ restCases
                  ∧ clause = Clause.canonical { literals := seenCase } := by
            intro clause hclause
            rcases hseen clause hclause with
              ⟨seenCase, hseenGenerated, hseenAbsent, hclauseEq⟩
            exact ⟨seenCase, hseenGenerated,
              fun hseenRest =>
                hseenAbsent (List.mem_cons_of_mem boolCase hseenRest),
              hclauseEq⟩
          have hrestDecode :
              decodeRootBranches schema support parentType seen
                  (List.flatten
                    (restCases.map
                      (normalizedRootBranch schema parentType
                        operation.selectionSet))) = .ok shape := by
            simpa [normalizedRootBranch, hbody] using hdecode
          have ih := decodeRootBranches_generatedCases_correspondence
            schema hschema operation hvalid support hsupport hsupportEq
            hsupportNonempty parentType hparentEq hparentObject assignment
            runtimeCase hassignment hruntimeMem hruntimeAgrees restCases seen
            shape hparts.2 hrestGenerated hrestSeen hrestDecode path
          by_cases heq : runtimeCase = boolCase
          · subst runtimeCase
            have hrestFalse :
                ¬ shape.DenotesEquivalentPath schema assignment parentType
                  path := by
              simpa [hparts.1] using ih
            have htargetFalse :
                ¬ selectionSetSelectsPath schema
                  (boolCaseVariableValues assignment) parentType
                  (normalizeSelectionSet schema parentType
                    (filterSelectionSetBoolCase boolCase
                      operation.selectionSet)) path := by
              rw [hbody]
              exact selectionSetSelectsPath_empty schema
                (boolCaseVariableValues assignment) parentType path
            simp only [List.mem_cons_self, if_true]
            exact ⟨fun h => False.elim (hrestFalse h),
              fun h => False.elim (htargetFalse h)⟩
          · simpa [heq] using ih
      | cons bodyHead bodyTail =>
          let body := bodyHead :: bodyTail
          have hbodyNonempty : body ≠ [] := by simp [body]
          rcases wrapWithBoolCase_singleton_of_ne boolCase body hcaseNonempty with
            ⟨wrappedSelection, hwrap⟩
          let clause : Clause := Clause.canonical { literals := boolCase }
          have hstem :
              decodeCompleteStem support.length wrappedSelection =
                .ok (boolCase, body) := by
            rw [← hcaseLength]
            exact decodeCompleteStem_wrapWithBoolCase hcaseNonempty
              hbodyNonempty hwrap
          have hclause :
              clauseFromCompleteStem support boolCase = .ok clause :=
            clauseFromCompleteStem_allBoolCases support hsupport hcaseGenerated
          have hclauseValid : clause.Valid support :=
            canonicalClause_valid_of_mem_allBoolCases support hsupport
              hcaseGenerated
          have hclauseComplete : clause.CompleteMinterm support :=
            canonicalClause_completeMinterm_of_mem_allBoolCases support hsupport
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
          have hfilteredFree : selectionSetDirectiveFree
              (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
            filterSelectionSetBoolCase_directiveFree schema boolCase
              operation.selectionSet
          have himage : GroundSelectionSetImage schema parentType body := by
            simpa [body, hbody] using
              normalizeSelectionSet_groundSelectionSetImage schema hschema
                parentType
                (filterSelectionSetBoolCase boolCase operation.selectionSet)
                hparentObject hfilteredFree
          have hparentBool : objectTypeNameBool schema parentType = true :=
            GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
              schema hparentObject
          have hnormal : selectionSetNormal schema parentType body := by
            simpa [body, hbody] using
              GroundTypeNormalization.normalizeSelectionSet_normal schema hschema
                parentType
                (filterSelectionSetBoolCase boolCase operation.selectionSet)
                hparentBool
          have hfree : selectionSetDirectiveFree body := by
            simpa [body, hbody] using
              normalize_filterSelectionSetBoolCase_directiveFree schema
                parentType boolCase operation.selectionSet
          have hrestSeen :
              ∀ seenClause, seenClause ∈ clause :: seen ->
                ∃ seenCase,
                  seenCase ∈ allBoolCases support
                  ∧ seenCase ∉ restCases
                  ∧ seenClause = Clause.canonical { literals := seenCase } := by
            intro seenClause hseenClause
            rcases List.mem_cons.mp hseenClause with hhead | htail
            · subst seenClause
              exact ⟨boolCase, hcaseGenerated, hparts.1, rfl⟩
            · rcases hseen seenClause htail with
                ⟨seenCase, hseenGenerated, hseenAbsent, hseenClauseEq⟩
              exact ⟨seenCase, hseenGenerated,
                fun hseenRest =>
                  hseenAbsent (List.mem_cons_of_mem boolCase hseenRest),
                hseenClauseEq⟩
          have hbranchInput :
              List.flatten
                  ((boolCase :: restCases).map
                    (normalizedRootBranch schema parentType
                      operation.selectionSet)) =
                wrappedSelection ::
                  List.flatten
                    (restCases.map
                      (normalizedRootBranch schema parentType
                        operation.selectionSet)) := by
            simp only [List.map_cons, List.flatten_cons]
            have hbranch :
                normalizedRootBranch schema parentType operation.selectionSet
                    boolCase = wrapWithBoolCase boolCase body := by
              simp [normalizedRootBranch, hbody, body]
            rw [hbranch, hwrap]
            rfl
          rw [hbranchInput, decodeRootBranches, hstem] at hdecode
          simp only [Bind.bind, Except.bind] at hdecode
          rw [hclause] at hdecode
          simp only at hdecode
          rw [hduplicate] at hdecode
          simp only [Bool.false_eq_true, if_false] at hdecode
          cases hbranchFold :
              foldGroundSelectionSet schema clause parentType body with
          | error error => simp [hbranchFold] at hdecode
          | ok branchShape =>
              rw [hbranchFold] at hdecode
              cases hrestDecode :
                  decodeRootBranches schema support parentType (clause :: seen)
                    (List.flatten
                      (restCases.map
                        (normalizedRootBranch schema parentType
                          operation.selectionSet))) with
              | error error => simp [hrestDecode] at hdecode
              | ok restShape =>
                  rw [hrestDecode] at hdecode
                  have hshape : shape =
                      mergeResponseShapes branchShape restShape :=
                    (Except.ok.inj hdecode).symm
                  subst shape
                  have hrestRelation :=
                    decodeRootBranches_generatedCases_correspondence
                      schema hschema operation hvalid support hsupport
                      hsupportEq hsupportNonempty parentType hparentEq
                      hparentObject assignment runtimeCase hassignment
                      hruntimeMem hruntimeAgrees restCases (clause :: seen)
                      restShape hparts.2 hrestGenerated hrestSeen hrestDecode path
                  rcases foldGroundSelectionSet_success_of_image_with_invariant
                      schema support clause hclauseValid hclauseComplete himage with
                    ⟨decodedBranch, hdecodedBranch, _hinvariant,
                      hbranchClauses, _hresponseNames, _hobjectTypes⟩
                  have hdecodedEq : decodedBranch = branchShape :=
                    Except.ok.inj (hdecodedBranch.symm.trans hbranchFold)
                  subst decodedBranch
                  by_cases heq : runtimeCase = boolCase
                  · subst runtimeCase
                    have hassignmentAgrees : variableValuesAgreeWithCase
                        (boolCaseVariableValues assignment) assignment support :=
                      variableValuesAgreeWithCase_boolCaseVariableValues []
                        hassignment
                    have hactive : clause.HoldsIn assignment := by
                      intro literal hliteral
                      change literal ∈ Clause.sortLiterals boolCase at hliteral
                      have hpair : literal ∈ boolCase :=
                        (sortLiterals_perm boolCase).mem_iff.mp hliteral
                      have hvarSupport : literal.1 ∈ support :=
                        boolCase_pair_variable_mem_of_allBoolCases
                          hcaseGenerated hpair
                      calc
                        assignment.lookup? literal.1 =
                            Execution.inputValueBoolean?
                              (boolCaseVariableValues assignment)
                              (.variable literal.1) :=
                          (hassignmentAgrees literal.1 hvarSupport).symm
                        _ = boolCase.lookup? literal.1 :=
                          hruntimeAgrees literal.1 hvarSupport
                        _ = some literal.2 :=
                          BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
                            hsupport hcaseGenerated hpair
                    have hbranchRelation :=
                      foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
                        schema support clause hclauseValid hclauseComplete
                        assignment (boolCaseVariableValues assignment) himage
                        hnormal hfree hbranchFold hactive path
                    rw [mergeResponseShapes_denotesEquivalentPath_iff,
                      hbranchRelation, hrestRelation]
                    simp [hparts.1, hbody, body]
                  · have hassignmentAgrees : variableValuesAgreeWithCase
                        (boolCaseVariableValues assignment) assignment support :=
                      variableValuesAgreeWithCase_boolCaseVariableValues []
                        hassignment
                    have hinactive : ¬ clause.HoldsIn assignment := by
                      intro hactive
                      have hcaseAgree : variableValuesAgreeWithCase
                          (boolCaseVariableValues assignment) boolCase support := by
                        intro varName hvarSupport
                        have hvarCase : varName ∈ boolCase.map Prod.fst :=
                          (completeNormalBoolCase_of_mem_allBoolCases hsupport
                            hcaseGenerated).2.2 varName |>.2 hvarSupport
                        rcases List.mem_map.mp hvarCase with
                          ⟨⟨candidateName, value⟩, hpair, hname⟩
                        change candidateName = varName at hname
                        subst candidateName
                        have hliteral : (varName, value) ∈
                            (Clause.canonical { literals := boolCase }).literals := by
                          change (varName, value) ∈ Clause.sortLiterals boolCase
                          exact (sortLiterals_perm boolCase).mem_iff.mpr hpair
                        calc
                          Execution.inputValueBoolean?
                              (boolCaseVariableValues assignment)
                              (.variable varName) = assignment.lookup? varName :=
                            hassignmentAgrees varName hvarSupport
                          _ = some value := hactive (varName, value) hliteral
                          _ = boolCase.lookup? varName :=
                            (BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
                              hsupport hcaseGenerated hpair).symm
                      have hcaseEq := allBoolCases_variableValuesAgree_unique
                        (boolCaseVariableValues assignment) hsupport hruntimeMem
                        hcaseGenerated hruntimeAgrees hcaseAgree
                      exact heq hcaseEq
                    have hbranchFalse :
                        ¬ branchShape.DenotesEquivalentPath schema assignment
                          parentType path :=
                      hbranchClauses.not_denotesEquivalentPath hinactive
                    rw [mergeResponseShapes_denotesEquivalentPath_iff]
                    simpa [hbranchFalse, heq] using hrestRelation

/-- Complete-normal root decoding and the selected source operation have the
same semantic paths for every complete assignment. -/
theorem decodeCompleteRoot_denotesEquivalentPath_iff_operationSelectsPath
    (schema : Schema) (operation : Operation) (shape : ResponseShape)
    (assignment : NormalForm.BoolCase)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hdecode : decodeCompleteRoot schema (operationBoolVars operation)
      (operation.rootType schema)
      (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
        (operation.rootType schema) operation.selectionSet) = .ok shape)
    (hcomplete : completeNormalBoolCase
      (operationBoolVars operation) assignment)
    (path : List PathStep) :
    shape.DenotesEquivalentPath schema assignment
        (operation.rootType schema) path
      ↔ operationSelectsPath schema operation assignment path := by
  let support := operationBoolVars operation
  have hsupport : support.Nodup := hcomplete.1
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hassignmentAgrees : variableValuesAgreeWithCase
      (boolCaseVariableValues assignment) assignment support :=
    variableValuesAgreeWithCase_boolCaseVariableValues [] hcomplete
  have hvaluesComplete : boolVarsComplete support
      (boolCaseVariableValues assignment) :=
    boolVarsComplete_boolCaseVariableValues [] hcomplete
  rcases allBoolCases_complete_for_variableValues
      (boolCaseVariableValues assignment) support hvaluesComplete with
    ⟨runtimeCase, hruntimeMem, hruntimeAgrees⟩
  have hnormalizedBridge := selectionSetSelectsPath_normalize_filter_iff
    schema operation runtimeCase (boolCaseVariableValues assignment) hschema
    hvalid (by simpa [support] using hruntimeAgrees) path
  have hselectionOperation :
      selectionSetSelectsPath schema (boolCaseVariableValues assignment)
          (operation.rootType schema) operation.selectionSet path
        ↔ operationSelectsPath schema operation assignment path := by
    cases path with
    | nil => simp
    | cons step rest =>
        rw [selectionSetSelectsPath_cons_iff,
          operationSelectsPath_cons_iff]
        have hrootBool : objectTypeNameBool schema
            (operation.rootType schema) = true :=
          GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
            schema hrootObject
        constructor
        · rintro ⟨hincludes, hpath⟩
          have hstep : step.parentObject = operation.rootType schema :=
            GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
              schema hrootBool (List.contains_iff_mem.mpr hincludes)
          rw [hstep] at hincludes hpath ⊢
          exact ⟨hincludes, hpath⟩
        · rintro ⟨hincludes, hpath⟩
          have hstep : step.parentObject = operation.rootType schema :=
            GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
              schema hrootBool (List.contains_iff_mem.mpr hincludes)
          rw [hstep] at hincludes hpath ⊢
          exact ⟨hincludes, hpath⟩
  cases hsupportCases : support with
  | nil =>
      have hassignmentNil : assignment = [] := by
        have hnames : assignment.map Prod.fst = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro name hmem
          have : name ∈ support := (hcomplete.2.2 name).1 hmem
          simp [hsupportCases] at this
        cases assignment with
        | nil => rfl
        | cons head rest => simp at hnames
      subst assignment
      have hruntimeNil : runtimeCase = [] := by
        simpa [hsupportCases, allBoolCases] using hruntimeMem
      subst runtimeCase
      let clause : Clause := { literals := [] }
      have hclauseValid : clause.Valid [] := by rfl
      have hclauseComplete : clause.CompleteMinterm [] := by rfl
      have hclauseHolds : clause.HoldsIn [] := by simp [clause, Clause.HoldsIn]
      have hfilteredFree := filterSelectionSetBoolCase_directiveFree schema []
        operation.selectionSet
      have himage : GroundSelectionSetImage schema (operation.rootType schema)
          (normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase [] operation.selectionSet)) :=
        normalizeSelectionSet_groundSelectionSetImage schema hschema
          (operation.rootType schema)
          (filterSelectionSetBoolCase [] operation.selectionSet) hrootObject
          hfilteredFree
      have hrootBool : objectTypeNameBool schema
          (operation.rootType schema) = true :=
        GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
          schema hrootObject
      have hnormal : selectionSetNormal schema (operation.rootType schema)
          (normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase [] operation.selectionSet)) :=
        GroundTypeNormalization.normalizeSelectionSet_normal schema hschema
          (operation.rootType schema)
          (filterSelectionSetBoolCase [] operation.selectionSet) hrootBool
      have hfree := normalize_filterSelectionSetBoolCase_directiveFree schema
        (operation.rootType schema) [] operation.selectionSet
      have hfold : foldGroundSelectionSet schema clause
          (operation.rootType schema)
          (normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase [] operation.selectionSet)) = .ok shape := by
        cases hbody : normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase [] operation.selectionSet) with
        | nil =>
            simpa [support, hsupportCases, decodeCompleteRoot, firstDuplicate?,
              completeNormalizeRootSelectionSet, allBoolCases,
              wrapWithBoolCase, clause, hbody] using hdecode
        | cons head tail =>
            simpa [support, hsupportCases, decodeCompleteRoot, firstDuplicate?,
              completeNormalizeRootSelectionSet, allBoolCases,
              wrapWithBoolCase, clause, hbody] using hdecode
      have hground :=
        foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
          schema [] clause hclauseValid hclauseComplete [] [] himage hnormal
          hfree hfold hclauseHolds path
      exact hground.trans (hnormalizedBridge.trans hselectionOperation)
  | cons varName variables =>
      have hsupportNonempty : support ≠ [] := by
        simp [hsupportCases]
      have hcasesNodup : (allBoolCases support).Nodup :=
        allBoolCases_nodup hsupport
      have hduplicate : firstDuplicate? support = none :=
        firstDuplicate?_eq_none_of_nodup support hsupport
      have hrootDecode :
          decodeRootBranches schema support (operation.rootType schema) []
              (List.flatten
                ((allBoolCases support).map
                  (normalizedRootBranch schema (operation.rootType schema)
                    operation.selectionSet))) = .ok shape := by
        unfold completeNormalizeRootSelectionSet at hdecode
        change decodeCompleteRoot schema support (operation.rootType schema)
            (List.flatten
              ((allBoolCases support).map
                (normalizedRootBranch schema (operation.rootType schema)
                  operation.selectionSet))) = .ok shape at hdecode
        unfold decodeCompleteRoot at hdecode
        rw [hduplicate] at hdecode
        simp only [hsupportCases] at hdecode
        simpa [hsupportCases] using hdecode
      have hrootRelation := decodeRootBranches_generatedCases_correspondence
        schema hschema operation hvalid support hsupport rfl hsupportNonempty
        (operation.rootType schema) rfl hrootObject assignment runtimeCase
        hcomplete hruntimeMem hruntimeAgrees (allBoolCases support) [] shape
        hcasesNodup (fun boolCase hmem => hmem) (by simp) hrootDecode path
      simp only [hruntimeMem, ↓reduceIte] at hrootRelation
      exact hrootRelation.trans (hnormalizedBridge.trans hselectionOperation)

end ResponseShape

end GraphQL
