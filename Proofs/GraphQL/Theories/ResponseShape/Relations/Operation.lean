import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.VariableIndependence
import Proofs.GraphQL.Theories.ResponseShape.Compute.Totality
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Operation
import Proofs.GraphQL.Theories.ResponseShape.Relations.Basics

/-!
Operation-level consequences of response-shape subset.

The public relation quantifies over complete assignments for the union of both
shapes' Boolean supports. Operation correspondence, by contrast, takes
an assignment containing exactly one shape's support.  The private lemmas in
this module bridge that intentional boundary: they select the unique smaller
complete case observed by the union assignment, transport shape denotation
through agreement on supported variables, and transport source collection
through a directive-free normalized selection set.
-/

namespace GraphQL

namespace ResponseShape

open NormalForm
open NormalForm.CompleteNormalization

private theorem Clause.holdsIn_of_lookup_agreement
    {support : List BoolVar} {left right : BoolCase} {clause : Clause}
    (hcomplete : clause.CompleteMinterm support)
    (hagrees
      : ∀ varName, varName ∈ support -> left.lookup? varName = right.lookup? varName)
    (hholds : clause.HoldsIn left)
    : clause.HoldsIn right := by
  unfold Clause.CompleteMinterm Clause.completeMintermBool at hcomplete
  simp only [Bool.and_eq_true] at hcomplete
  have hvalid : clause.Valid support := hcomplete.1.2
  unfold Clause.Valid Clause.validBool at hvalid
  simp only [Bool.and_eq_true] at hvalid
  intro literal hliteral
  have hsupport : literal.1 ∈ support :=
    List.contains_iff_mem.mp
      (List.all_eq_true.mp hvalid.2 literal hliteral)
  exact (hagrees literal.1 hsupport).symm.trans (hholds literal hliteral)

private theorem shapeDefinition_fullMinterm_of_mem (support : List BoolVar)
    : ∀ {definitions : List ShapeDefinition} {definition : ShapeDefinition},
        shapeDefinitionsFullMintermBool support definitions = true
        -> definition ∈ definitions
        -> definition.fullMintermBool support = true
  | [], _definition, hfull, hmem => by
      simp [shapeDefinitionsFullMintermBool] at hfull hmem
  | head :: rest, definition, hfull, hmem => by
      simp only [shapeDefinitionsFullMintermBool, Bool.and_eq_true] at hfull
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact hfull.1
      · exact shapeDefinition_fullMinterm_of_mem support hfull.2 hrest

private theorem possibleDefinitions_fullMinterm_of_mem (support : List BoolVar)
    : ∀ {groups : List PossibleDefinitions} {possible : PossibleDefinitions},
        possibleDefinitionsFullMintermBool support groups = true
        -> possible ∈ groups
        -> possible.fullMintermBool support = true
  | [], _possible, hfull, hmem => by
      simp [possibleDefinitionsFullMintermBool] at hfull hmem
  | head :: rest, possible, hfull, hmem => by
      simp only [possibleDefinitionsFullMintermBool, Bool.and_eq_true] at hfull
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact hfull.1
      · exact possibleDefinitions_fullMinterm_of_mem support hfull.2 hrest

private theorem responsePosition_fullMinterm_of_mem (support : List BoolVar)
    : ∀ {positions : List ResponsePosition} {position : ResponsePosition},
        responsePositionsFullMintermBool support positions = true
        -> position ∈ positions
        -> position.fullMintermBool support = true
  | [], _position, hfull, hmem => by
      simp [responsePositionsFullMintermBool] at hfull hmem
  | head :: rest, position, hfull, hmem => by
      simp only [responsePositionsFullMintermBool, Bool.and_eq_true] at hfull
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact hfull.1
      · exact responsePosition_fullMinterm_of_mem support hfull.2 hrest

private theorem shapeDefinition_fullMinterm_of_position
    (support : List BoolVar) {position : ResponsePosition}
    {possible : PossibleDefinitions} {definition : ShapeDefinition}
    (hposition : position.fullMintermBool support = true)
    (hpossible : possible ∈ position.possibleDefinitions)
    (hdefinition : definition ∈ possible.definitions)
    : definition.fullMintermBool support = true := by
  cases position with
  | mk responseName groups =>
      change possibleDefinitionsFullMintermBool support groups = true
        at hposition
      change possible ∈ groups at hpossible
      have hpossibleFull := possibleDefinitions_fullMinterm_of_mem support
        hposition hpossible
      cases possible with
      | mk objectTypes definitions =>
          change shapeDefinitionsFullMintermBool support definitions = true
            at hpossibleFull
          change definition ∈ definitions at hdefinition
          exact shapeDefinition_fullMinterm_of_mem support hpossibleFull
            hdefinition

private theorem ShapeDefinition.clauseCompleteMinterm_of_fullMinterm
    (support : List BoolVar) {definition : ShapeDefinition}
    (hfull : definition.fullMintermBool support = true)
    : definition.clause.CompleteMinterm support := by
  cases definition with
  | mk clause field subshape =>
      rw [ShapeDefinition.fullMintermBool.eq_def] at hfull
      rw [Bool.and_eq_true] at hfull
      exact hfull.1

private theorem ShapeDefinition.childFullMinterm_of_fullMinterm
    (support : List BoolVar) {definition : ShapeDefinition}
    {child : ResponseShape}
    (hfull : definition.fullMintermBool support = true)
    (hchild : definition.subshape = some child)
    : child.fullMintermBool support = true := by
  cases definition with
  | mk clause field subshape =>
      rw [ShapeDefinition.fullMintermBool.eq_def] at hfull
      rw [Bool.and_eq_true] at hfull
      change subshape = some child at hchild
      rw [hchild] at hfull
      exact hfull.2

private theorem ResponseShape.denotesPath_of_lookup_agreement
    {support : List BoolVar} {left right : BoolCase}
    (hagrees
      : ∀ varName, varName ∈ support -> left.lookup? varName = right.lookup? varName)
    : ∀ {schema : Schema} {parentType : Name} {shape : ResponseShape}
          {path : List PathStep},
        shape.DenotesPath schema left parentType path
        -> shape.fullMintermBool support = true
        -> shape.DenotesPath schema right parentType path := by
  intro schema parentType shape path hdenotes
  induction hdenotes with
  | @field _parentType positions position possible definition runtimeObject
      runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds =>
      intro hfull
      simp only [ResponseShape.fullMintermBool] at hfull
      have hpositionFull := responsePosition_fullMinterm_of_mem support
        hfull positionMem
      have hdefinitionFull := shapeDefinition_fullMinterm_of_position support
        hpositionFull possibleMem definitionMem
      have hclauseComplete :=
        ShapeDefinition.clauseCompleteMinterm_of_fullMinterm support
          hdefinitionFull
      exact .field runtimePossible positionMem possibleMem runtimeMem
        definitionMem
        (Clause.holdsIn_of_lookup_agreement hclauseComplete hagrees
          clauseHolds)
  | @child _parentType positions position possible definition runtimeObject childShape
      childPath runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds subshapeEq childDenotes ih =>
      intro hfull
      simp only [ResponseShape.fullMintermBool] at hfull
      have hpositionFull := responsePosition_fullMinterm_of_mem support
        hfull positionMem
      have hdefinitionFull := shapeDefinition_fullMinterm_of_position support
        hpositionFull possibleMem definitionMem
      have hclauseComplete :=
        ShapeDefinition.clauseCompleteMinterm_of_fullMinterm support
          hdefinitionFull
      have hchildFull : childShape.fullMintermBool support = true :=
        ShapeDefinition.childFullMinterm_of_fullMinterm support
          hdefinitionFull subshapeEq
      exact .child runtimePossible positionMem possibleMem runtimeMem
        definitionMem
        (Clause.holdsIn_of_lookup_agreement hclauseComplete hagrees
          clauseHolds)
        subshapeEq (ih hchildFull)

private theorem ResponseShape.denotesPath_iff_of_lookup_agreement
    {schema : Schema} {support : List BoolVar} {left right : BoolCase}
    {parentType : Name} {shape : ResponseShape} {path : List PathStep}
    (hfull : shape.fullMintermBool support = true)
    (hagrees
      : ∀ varName, varName ∈ support -> left.lookup? varName = right.lookup? varName)
    : shape.DenotesPath schema left parentType path
      ↔ shape.DenotesPath schema right parentType path := by
  constructor
  · intro hdenotes
    exact ResponseShape.denotesPath_of_lookup_agreement hagrees hdenotes hfull
  · intro hdenotes
    exact ResponseShape.denotesPath_of_lookup_agreement
      (fun varName hmem => (hagrees varName hmem).symm) hdenotes hfull

private theorem ResponseShape.denotesEquivalentPath_iff_of_lookup_agreement
    {schema : Schema} {support : List BoolVar} {left right : BoolCase}
    {parentType : Name} {shape : ResponseShape} {path : List PathStep}
    (hfull : shape.fullMintermBool support = true)
    (hagrees
      : ∀ varName, varName ∈ support -> left.lookup? varName = right.lookup? varName)
    : shape.DenotesEquivalentPath schema left parentType path
      ↔ shape.DenotesEquivalentPath schema right parentType path := by
  unfold ResponseShape.DenotesEquivalentPath
  constructor
  · rintro ⟨denotedPath, hdenotes, hequivalent⟩
    exact ⟨denotedPath,
      (ResponseShape.denotesPath_iff_of_lookup_agreement hfull hagrees).mp
        hdenotes,
      hequivalent⟩
  · rintro ⟨denotedPath, hdenotes, hequivalent⟩
    exact ⟨denotedPath,
      (ResponseShape.denotesPath_iff_of_lookup_agreement hfull hagrees).mpr
        hdenotes,
      hequivalent⟩

private theorem collectedFieldsSelectPath_iff_of_directiveFree_values
    (schema : Schema)
    (leftValues rightValues : Execution.VariableValues)
    : ∀ (path : List PathStep) (groups : List (Name × List Execution.ExecutableField)),
        executableGroupsDirectiveFree groups
        -> (collectedFieldsSelectPath schema leftValues groups path
            ↔ collectedFieldsSelectPath schema rightValues groups path)
  | [], groups, _hfree => by
      simp
  | [step], groups, _hfree => by
      rfl
  | step :: next :: rest, groups, hfree => by
      rw [collectedFieldsSelectPath_cons_cons,
        collectedFieldsSelectPath_cons_cons]
      constructor
      · rintro ⟨fields, hfields, hmatch, hincludes, hrest⟩
        have hfieldsFree : executableFieldListDirectiveFree fields :=
          hfree (step.responseName, fields) hfields
        have hnextFree : executableGroupsDirectiveFree
            (Execution.collectSubfields schema leftValues next.parentObject
              (.object next.parentObject ()) fields) :=
          collectSubfields_executableGroupsDirectiveFree schema leftValues
            next.parentObject (.object next.parentObject ()) fields hfieldsFree
        have hnext :=
          (collectedFieldsSelectPath_iff_of_directiveFree_values schema
            leftValues rightValues (next :: rest)
            (Execution.collectSubfields schema leftValues next.parentObject
              (.object next.parentObject ()) fields) hnextFree).mp hrest
        have hcollect :
            Execution.collectSubfields schema leftValues next.parentObject
                (.object next.parentObject ()) fields =
              Execution.collectSubfields schema rightValues next.parentObject
                (.object next.parentObject ()) fields :=
          collectSubfields_eq_of_directiveFree schema leftValues rightValues
            next.parentObject (.object next.parentObject ()) fields hfieldsFree
        rw [hcollect] at hnext
        exact ⟨fields, hfields, hmatch, hincludes, hnext⟩
      · rintro ⟨fields, hfields, hmatch, hincludes, hrest⟩
        have hfieldsFree : executableFieldListDirectiveFree fields :=
          hfree (step.responseName, fields) hfields
        have hnextFree : executableGroupsDirectiveFree
            (Execution.collectSubfields schema rightValues next.parentObject
              (.object next.parentObject ()) fields) :=
          collectSubfields_executableGroupsDirectiveFree schema rightValues
            next.parentObject (.object next.parentObject ()) fields hfieldsFree
        have hnext :=
          (collectedFieldsSelectPath_iff_of_directiveFree_values schema
            leftValues rightValues (next :: rest)
            (Execution.collectSubfields schema rightValues next.parentObject
              (.object next.parentObject ()) fields) hnextFree).mpr hrest
        have hcollect :
            Execution.collectSubfields schema leftValues next.parentObject
                (.object next.parentObject ()) fields =
              Execution.collectSubfields schema rightValues next.parentObject
                (.object next.parentObject ()) fields :=
          collectSubfields_eq_of_directiveFree schema leftValues rightValues
            next.parentObject (.object next.parentObject ()) fields hfieldsFree
        rw [← hcollect] at hnext
        exact ⟨fields, hfields, hmatch, hincludes, hnext⟩

private theorem operationSelectsPath_iff_of_agreeing_case
    (schema : Schema) (operation : Operation)
    (assignment runtimeCase : BoolCase) (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcomplete : completeNormalBoolCase (operationBoolVars operation) runtimeCase)
    (hagrees
      : variableValuesAgreeWithCase
          (boolCaseVariableValues assignment) runtimeCase
          (operationBoolVars operation))
    : operationSelectsPath schema operation assignment path
      ↔ operationSelectsPath schema operation runtimeCase path := by
  cases path with
  | nil => simp
  | cons step rest =>
      rw [operationSelectsPath_cons_iff, operationSelectsPath_cons_iff]
      constructor
      · rintro ⟨hincludes, hpath⟩
        refine ⟨hincludes, ?_⟩
        let normalizedSelectionSet :=
          normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase runtimeCase operation.selectionSet)
        have hfree : selectionSetDirectiveFree normalizedSelectionSet := by
          exact normalize_filterSelectionSetBoolCase_directiveFree schema
            (operation.rootType schema) runtimeCase operation.selectionSet
        have hleftBridge :=
          collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation runtimeCase (boolCaseVariableValues assignment)
            step rest hschema hvalid hagrees hincludes
        have hrightAgrees : variableValuesAgreeWithCase
            (boolCaseVariableValues runtimeCase) runtimeCase
            (operationBoolVars operation) :=
          variableValuesAgreeWithCase_boolCaseVariableValues [] hcomplete
        have hrightBridge :=
          collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation runtimeCase (boolCaseVariableValues runtimeCase)
            step rest hschema hvalid hrightAgrees hincludes
        have hnormalizedLeft := hleftBridge.mpr hpath
        have hleftGroupsFree : executableGroupsDirectiveFree
            (Execution.collectFields schema (boolCaseVariableValues assignment)
              (operation.rootType schema) (.object step.parentObject ())
              normalizedSelectionSet) :=
          collectFields_executableGroupsDirectiveFree schema
            (boolCaseVariableValues assignment) (operation.rootType schema)
            (.object step.parentObject ()) normalizedSelectionSet hfree
        have hindependent :=
          (collectedFieldsSelectPath_iff_of_directiveFree_values schema
            (boolCaseVariableValues assignment)
            (boolCaseVariableValues runtimeCase) (step :: rest)
            (Execution.collectFields schema (boolCaseVariableValues assignment)
              (operation.rootType schema) (.object step.parentObject ())
              normalizedSelectionSet) hleftGroupsFree).mp hnormalizedLeft
        have hcollect :
            Execution.collectFields schema (boolCaseVariableValues assignment)
                (operation.rootType schema) (.object step.parentObject ())
                normalizedSelectionSet =
              Execution.collectFields schema (boolCaseVariableValues runtimeCase)
                (operation.rootType schema) (.object step.parentObject ())
                normalizedSelectionSet :=
          collectFields_eq_of_directiveFree schema
            (boolCaseVariableValues assignment)
            (boolCaseVariableValues runtimeCase) (operation.rootType schema)
            (.object step.parentObject ()) normalizedSelectionSet hfree
        rw [hcollect] at hindependent
        exact hrightBridge.mp hindependent
      · rintro ⟨hincludes, hpath⟩
        refine ⟨hincludes, ?_⟩
        let normalizedSelectionSet :=
          normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase runtimeCase operation.selectionSet)
        have hfree : selectionSetDirectiveFree normalizedSelectionSet := by
          exact normalize_filterSelectionSetBoolCase_directiveFree schema
            (operation.rootType schema) runtimeCase operation.selectionSet
        have hleftBridge :=
          collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation runtimeCase (boolCaseVariableValues assignment)
            step rest hschema hvalid hagrees hincludes
        have hrightAgrees : variableValuesAgreeWithCase
            (boolCaseVariableValues runtimeCase) runtimeCase
            (operationBoolVars operation) :=
          variableValuesAgreeWithCase_boolCaseVariableValues [] hcomplete
        have hrightBridge :=
          collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation runtimeCase (boolCaseVariableValues runtimeCase)
            step rest hschema hvalid hrightAgrees hincludes
        have hnormalizedRight := hrightBridge.mpr hpath
        have hrightGroupsFree : executableGroupsDirectiveFree
            (Execution.collectFields schema (boolCaseVariableValues runtimeCase)
              (operation.rootType schema) (.object step.parentObject ())
              normalizedSelectionSet) :=
          collectFields_executableGroupsDirectiveFree schema
            (boolCaseVariableValues runtimeCase) (operation.rootType schema)
            (.object step.parentObject ()) normalizedSelectionSet hfree
        have hindependent :=
          (collectedFieldsSelectPath_iff_of_directiveFree_values schema
            (boolCaseVariableValues assignment)
            (boolCaseVariableValues runtimeCase) (step :: rest)
            (Execution.collectFields schema (boolCaseVariableValues runtimeCase)
              (operation.rootType schema) (.object step.parentObject ())
              normalizedSelectionSet) hrightGroupsFree).mpr hnormalizedRight
        have hcollect :
            Execution.collectFields schema (boolCaseVariableValues assignment)
                (operation.rootType schema) (.object step.parentObject ())
                normalizedSelectionSet =
              Execution.collectFields schema (boolCaseVariableValues runtimeCase)
                (operation.rootType schema) (.object step.parentObject ())
                normalizedSelectionSet :=
          collectFields_eq_of_directiveFree schema
            (boolCaseVariableValues assignment)
            (boolCaseVariableValues runtimeCase) (operation.rootType schema)
            (.object step.parentObject ()) normalizedSelectionSet hfree
        rw [← hcollect] at hindependent
        exact hleftBridge.mp hindependent

private theorem
    computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath_of_complete_extension
    (schema : Schema) (operation : Operation) (shape : OperationShape)
    (coveringSupport : List BoolVar) (assignment : BoolCase) (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcompute : computeOperationShape schema operation = .ok shape)
    (hcomplete : completeNormalBoolCase coveringSupport assignment)
    (hsupport : ∀ varName, varName ∈ shape.boolSupport -> varName ∈ coveringSupport)
    : shape.root.DenotesEquivalentPath schema assignment shape.rootType path
      ↔ operationSelectsPath schema operation assignment path := by
  have hshapeSupport :
      shape.boolSupport = operationBoolVars operation :=
    computeOperationShape_support schema operation shape hcompute
  have hshapeSupportNodup : shape.boolSupport.Nodup :=
    computeOperationShape_support_nodup schema operation shape hcompute
  have hshapeFull :
      shape.root.fullMintermBool shape.boolSupport = true := by
    exact computeOperationShape_fullMinterm schema operation shape hcompute
  have hcoveringValuesComplete : boolVarsComplete coveringSupport
      (boolCaseVariableValues assignment) :=
    boolVarsComplete_boolCaseVariableValues [] hcomplete
  have hshapeValuesComplete : boolVarsComplete shape.boolSupport
      (boolCaseVariableValues assignment) := by
    intro varName hmem
    exact hcoveringValuesComplete varName (hsupport varName hmem)
  rcases allBoolCases_complete_for_variableValues
      (boolCaseVariableValues assignment) shape.boolSupport
      hshapeValuesComplete with
    ⟨runtimeCase, hruntimeMem, hruntimeAgrees⟩
  have hruntimeComplete :
      completeNormalBoolCase shape.boolSupport runtimeCase :=
    completeNormalBoolCase_of_mem_allBoolCases hshapeSupportNodup hruntimeMem
  have hruntimeOperationComplete :
      completeNormalBoolCase (operationBoolVars operation) runtimeCase := by
    simpa [← hshapeSupport] using hruntimeComplete
  have hoperationAgrees : variableValuesAgreeWithCase
      (boolCaseVariableValues assignment) runtimeCase
      (operationBoolVars operation) := by
    simpa [← hshapeSupport] using hruntimeAgrees
  have hassignmentAgrees : variableValuesAgreeWithCase
      (boolCaseVariableValues assignment) assignment coveringSupport :=
    variableValuesAgreeWithCase_boolCaseVariableValues [] hcomplete
  have hlookupAgrees : ∀ varName, varName ∈ shape.boolSupport ->
      assignment.lookup? varName = runtimeCase.lookup? varName := by
    intro varName hmem
    exact (hassignmentAgrees varName (hsupport varName hmem)).symm.trans
      (hruntimeAgrees varName hmem)
  have hdenotesBridge :
      shape.root.DenotesEquivalentPath schema assignment shape.rootType path
        ↔ shape.root.DenotesEquivalentPath schema runtimeCase
          shape.rootType path :=
    ResponseShape.denotesEquivalentPath_iff_of_lookup_agreement hshapeFull
      hlookupAgrees
  have hcorrespondence :=
    computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath
      schema operation shape runtimeCase path hschema hvalid hcompute
      hruntimeComplete
  have hoperationBridge := operationSelectsPath_iff_of_agreeing_case
    schema operation assignment runtimeCase path hschema hvalid
    hruntimeOperationComplete hoperationAgrees
  exact hdenotesBridge.trans (hcorrespondence.trans hoperationBridge.symm)

/--
Shape subset licenses unconditional static collection coverage.  A path
selected by the required operation under a complete assignment for both shape
supports is selected, as the same semantic query path, by the provided
operation.  This theorem makes no claim about execution errors, null bubbling,
or response projection.
-/
theorem shapeSubset_selectsPath
    (schema : Schema) (required provided : Operation)
    (requiredShape providedShape : OperationShape)
    (assignment : BoolCase) (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrequiredValid : Validation.operationDefinitionValid schema required)
    (hprovidedValid : Validation.operationDefinitionValid schema provided)
    (hrequiredCompute : computeOperationShape schema required = .ok requiredShape)
    (hprovidedCompute : computeOperationShape schema provided = .ok providedShape)
    (hsubset : ShapeSubset schema requiredShape providedShape)
    (hcomplete
      : completeNormalBoolCase
          (supportUnion requiredShape.boolSupport providedShape.boolSupport)
          assignment)
    (hrequiredSelects : operationSelectsPath schema required assignment path)
    : operationSelectsPath schema provided assignment path := by
  let unionSupport :=
    supportUnion requiredShape.boolSupport providedShape.boolSupport
  have hrequiredSupport : ∀ varName,
      varName ∈ requiredShape.boolSupport -> varName ∈ unionSupport := by
    intro varName hmem
    exact (mem_supportUnion_iff varName requiredShape.boolSupport
      providedShape.boolSupport).2 (Or.inl hmem)
  have hprovidedSupport : ∀ varName,
      varName ∈ providedShape.boolSupport -> varName ∈ unionSupport := by
    intro varName hmem
    exact (mem_supportUnion_iff varName requiredShape.boolSupport
      providedShape.boolSupport).2 (Or.inr hmem)
  have hrequiredEquivalent :=
    (computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath_of_complete_extension
      schema required requiredShape unionSupport assignment path hschema
      hrequiredValid hrequiredCompute (by simpa [unionSupport] using hcomplete)
      hrequiredSupport).mpr hrequiredSelects
  rcases hrequiredEquivalent with
    ⟨requiredPath, hrequiredDenotes, hrequiredPathEquivalent⟩
  have hprovidedEquivalent := hsubset.denotesEquivalentPath hcomplete
    hrequiredDenotes
  rcases hprovidedEquivalent with
    ⟨providedPath, hprovidedDenotes, hprovidedPathEquivalent⟩
  have hprovidedQueryEquivalent :
      PathsSemanticallyEquivalent providedPath path :=
    pathsSemanticallyEquivalent_trans hprovidedPathEquivalent
      hrequiredPathEquivalent
  apply
    (computeOperationShape_denotesEquivalentPath_iff_operationSelectsPath_of_complete_extension
      schema provided providedShape unionSupport assignment path hschema
      hprovidedValid hprovidedCompute (by simpa [unionSupport] using hcomplete)
      hprovidedSupport).mp
  exact ⟨providedPath, hprovidedDenotes, hprovidedQueryEquivalent⟩

/-- Existential form of `shapeSubset_selectsPath`, matching the design's
semantic-path envelope while retaining the same path as its witness. -/
theorem shapeSubset_selectsEquivalentPath
    (schema : Schema) (required provided : Operation)
    (requiredShape providedShape : OperationShape)
    (assignment : BoolCase) (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrequiredValid : Validation.operationDefinitionValid schema required)
    (hprovidedValid : Validation.operationDefinitionValid schema provided)
    (hrequiredCompute : computeOperationShape schema required = .ok requiredShape)
    (hprovidedCompute : computeOperationShape schema provided = .ok providedShape)
    (hsubset : ShapeSubset schema requiredShape providedShape)
    (hcomplete
      : completeNormalBoolCase
          (supportUnion requiredShape.boolSupport providedShape.boolSupport)
          assignment)
    (hrequiredSelects : operationSelectsPath schema required assignment path)
    : ∃ providedPath,
        operationSelectsPath schema provided assignment providedPath
        ∧ PathsSemanticallyEquivalent path providedPath := by
  exact ⟨path,
    shapeSubset_selectsPath schema required provided requiredShape providedShape
      assignment path hschema hrequiredValid hprovidedValid hrequiredCompute
      hprovidedCompute hsubset hcomplete hrequiredSelects,
    pathsSemanticallyEquivalent_refl path⟩

end ResponseShape

end GraphQL
