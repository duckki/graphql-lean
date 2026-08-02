import GraphQL.Theories.ResponseShape.Validity
import Proofs.GraphQL.Theories.ResponseShape.Compute.Stems

/-!
Grammar soundness of successful response-shape decoding.

These theorems use only checks performed by the decoder.  They do not identify
accepted syntax with the image of complete normalization; image-sensitive
results retain their separate normalizer provenance premises.
-/

namespace GraphQL

namespace ResponseShape

private theorem shapeDefinitionsFullMintermBool_append
    (support : List NormalForm.BoolVar) : ∀ left right,
    shapeDefinitionsFullMintermBool support (left ++ right) =
      (shapeDefinitionsFullMintermBool support left
        && shapeDefinitionsFullMintermBool support right)
  | [], right => by simp [shapeDefinitionsFullMintermBool]
  | definition :: rest, right => by
      simp [shapeDefinitionsFullMintermBool,
        shapeDefinitionsFullMintermBool_append support rest right,
        Bool.and_assoc]

private theorem possibleDefinitionsFullMintermBool_append
    (support : List NormalForm.BoolVar) : ∀ left right,
    possibleDefinitionsFullMintermBool support (left ++ right) =
      (possibleDefinitionsFullMintermBool support left
        && possibleDefinitionsFullMintermBool support right)
  | [], right => by simp [possibleDefinitionsFullMintermBool]
  | possible :: rest, right => by
      simp [possibleDefinitionsFullMintermBool,
        possibleDefinitionsFullMintermBool_append support rest right,
        Bool.and_assoc]

private theorem insertPossibleDefinitions_fullMintermBool
    (support : List NormalForm.BoolVar) (incoming : PossibleDefinitions) :
    ∀ groups,
      incoming.fullMintermBool support = true ->
      possibleDefinitionsFullMintermBool support groups = true ->
      possibleDefinitionsFullMintermBool support
          (insertPossibleDefinitions incoming groups) = true
  | [], hincoming, _hgroups => by
      simpa [insertPossibleDefinitions,
        possibleDefinitionsFullMintermBool] using hincoming
  | current :: rest, hincoming, hgroups => by
      have hcurrent : current.fullMintermBool support = true :=
        (Bool.and_eq_true_iff.mp hgroups).1
      have hrest :
          possibleDefinitionsFullMintermBool support rest = true :=
        (Bool.and_eq_true_iff.mp hgroups).2
      cases incoming with
      | mk incomingObjects incomingDefinitions =>
          cases current with
          | mk currentObjects currentDefinitions =>
              by_cases heq : currentObjects = incomingObjects
              · simp only [insertPossibleDefinitions, heq, beq_self_eq_true,
                  if_true, possibleDefinitionsFullMintermBool,
                  PossibleDefinitions.fullMintermBool,
                  PossibleDefinitions.objectTypes,
                  PossibleDefinitions.definitions]
                apply Bool.and_eq_true_iff.mpr
                constructor
                · rw [shapeDefinitionsFullMintermBool_append]
                  exact Bool.and_eq_true_iff.mpr ⟨hcurrent, hincoming⟩
                · exact hrest
              · have hbeq : (currentObjects == incomingObjects) = false := by
                  simpa using heq
                simp only [insertPossibleDefinitions, hbeq, Bool.false_eq_true,
                  if_false, possibleDefinitionsFullMintermBool,
                  PossibleDefinitions.fullMintermBool,
                  PossibleDefinitions.objectTypes,
                  PossibleDefinitions.definitions]
                exact Bool.and_eq_true_iff.mpr
                  ⟨hcurrent,
                    insertPossibleDefinitions_fullMintermBool support
                      (.mk incomingObjects incomingDefinitions) rest
                      hincoming hrest⟩

private theorem mergePossibleDefinitions_fullMintermBool
    (support : List NormalForm.BoolVar) (left right : List PossibleDefinitions)
    (hleft : possibleDefinitionsFullMintermBool support left = true)
    (hright : possibleDefinitionsFullMintermBool support right = true) :
    possibleDefinitionsFullMintermBool support
        (mergePossibleDefinitions left right) = true := by
  unfold mergePossibleDefinitions
  induction right generalizing left with
  | nil => simpa using hleft
  | cons incoming rest ih =>
      have hincoming : incoming.fullMintermBool support = true :=
        (Bool.and_eq_true_iff.mp hright).1
      have hrest :
          possibleDefinitionsFullMintermBool support rest = true :=
        (Bool.and_eq_true_iff.mp hright).2
      exact ih
        (insertPossibleDefinitions incoming left)
        (insertPossibleDefinitions_fullMintermBool support incoming left
          hincoming hleft)
        hrest

private theorem insertResponsePosition_fullMintermBool
    (support : List NormalForm.BoolVar) (incoming : ResponsePosition) :
    ∀ positions,
      incoming.fullMintermBool support = true ->
      responsePositionsFullMintermBool support positions = true ->
      responsePositionsFullMintermBool support
          (insertResponsePosition incoming positions) = true
  | [], hincoming, _hpositions => by
      simpa [insertResponsePosition,
        responsePositionsFullMintermBool] using hincoming
  | current :: rest, hincoming, hpositions => by
      have hcurrent : current.fullMintermBool support = true :=
        (Bool.and_eq_true_iff.mp hpositions).1
      have hrest : responsePositionsFullMintermBool support rest = true :=
        (Bool.and_eq_true_iff.mp hpositions).2
      cases incoming with
      | mk incomingName incomingGroups =>
          cases current with
          | mk currentName currentGroups =>
              by_cases heq : currentName = incomingName
              · simp only [insertResponsePosition, heq, beq_self_eq_true,
                  if_true, responsePositionsFullMintermBool,
                  ResponsePosition.fullMintermBool,
                  ResponsePosition.responseName,
                  ResponsePosition.possibleDefinitions]
                apply Bool.and_eq_true_iff.mpr
                exact
                  ⟨mergePossibleDefinitions_fullMintermBool support
                      currentGroups incomingGroups hcurrent hincoming,
                    hrest⟩
              · have hbeq : (currentName == incomingName) = false := by
                  simpa using heq
                simp only [insertResponsePosition, hbeq, Bool.false_eq_true,
                  if_false, responsePositionsFullMintermBool,
                  ResponsePosition.fullMintermBool,
                  ResponsePosition.responseName,
                  ResponsePosition.possibleDefinitions]
                exact Bool.and_eq_true_iff.mpr
                  ⟨hcurrent,
                    insertResponsePosition_fullMintermBool support
                      (.mk incomingName incomingGroups) rest hincoming hrest⟩

/-- Merging shapes preserves the complete-minterm property of both inputs. -/
theorem mergeResponseShapes_fullMintermBool
    (support : List NormalForm.BoolVar) (left right : ResponseShape)
    (hleft : left.fullMintermBool support = true)
    (hright : right.fullMintermBool support = true) :
    (mergeResponseShapes left right).fullMintermBool support = true := by
  cases left with
  | object leftPositions =>
      cases right with
      | object rightPositions =>
          unfold mergeResponseShapes
          unfold ResponseShape.fullMintermBool at hleft hright ⊢
          induction rightPositions generalizing leftPositions with
          | nil => simpa using hleft
          | cons incoming rest ih =>
              have hincoming : incoming.fullMintermBool support = true :=
                (Bool.and_eq_true_iff.mp hright).1
              have hrest :
                  responsePositionsFullMintermBool support rest = true :=
                (Bool.and_eq_true_iff.mp hright).2
              exact ih
                (insertResponsePosition incoming leftPositions)
                (insertResponsePosition_fullMintermBool support incoming
                  leftPositions hincoming hleft)
                hrest

/-- A successful ground fold preserves completeness of its branch clause. -/
theorem foldGroundSelectionSet_fullMintermBool
    (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
    (hcomplete : clause.CompleteMinterm support) :
    ∀ (parentType : Name) (selectionSet : List Selection)
      (shape : ResponseShape),
      foldGroundSelectionSet schema clause parentType selectionSet = .ok shape ->
      shape.fullMintermBool support = true := by
  intro parentType selectionSet
  induction parentType, selectionSet using
      foldGroundSelectionSet.induct schema clause with
  | case1 parentType hrecognized =>
      intro shape hfold
      simp [foldGroundSelectionSet, hrecognized] at hfold
      subst shape
      rfl
  | case2 parentType hrecognized =>
      intro shape hfold
      simp [foldGroundSelectionSet, hrecognized] at hfold
  | case3 parentType rest hobject responseName fieldName arguments directives
      childSelections hdirectives =>
      intro shape hfold
      simp [foldGroundSelectionSet, hobject, hdirectives] at hfold
  | case4 parentType rest hobject responseName fieldName arguments directives
      childSelections hdirectives hduplicate =>
      intro shape hfold
      simp [foldGroundSelectionSet, hobject, hdirectives, hduplicate] at hfold
  | case5 parentType rest hobject responseName fieldName arguments directives
      childSelections hdirectives hduplicate fieldDefinition hlookup ihRest
      ihChild =>
      intro shape hfold
      cases hcomposite : fieldDefinition.outputType.isCompositeBool schema with
      | false =>
          cases hleaf : NormalForm.leafTypeNameBool schema
              fieldDefinition.outputType.namedType with
          | false =>
              unfold foldGroundSelectionSet at hfold
              simp [hobject, hdirectives, hduplicate, hlookup, hcomposite,
                hleaf, Bind.bind, Except.bind] at hfold
          | true =>
              cases hchildrenEmpty : childSelections.isEmpty with
              | false =>
                  unfold foldGroundSelectionSet at hfold
                  simp [hobject, hdirectives, hduplicate, hlookup,
                    hcomposite, hleaf, hchildrenEmpty, Bind.bind, Except.bind]
                    at hfold
              | true =>
                  cases hrestFold :
                      foldGroundSelectionSet schema clause parentType rest with
                  | error error =>
                      unfold foldGroundSelectionSet at hfold
                      simp [hobject, hdirectives, hduplicate, hlookup,
                        hcomposite, hleaf, hchildrenEmpty, hrestFold,
                        Bind.bind, Except.bind] at hfold
                  | ok restShape =>
                      unfold foldGroundSelectionSet at hfold
                      simp [hobject, hdirectives, hduplicate, hlookup,
                        hcomposite, hleaf, hchildrenEmpty, hrestFold,
                        Bind.bind, Except.bind] at hfold
                      subst shape
                      apply mergeResponseShapes_fullMintermBool
                      · simpa [singletonDefinitionShape,
                          ResponseShape.fullMintermBool,
                          responsePositionsFullMintermBool,
                          ResponsePosition.fullMintermBool,
                          possibleDefinitionsFullMintermBool,
                          PossibleDefinitions.fullMintermBool,
                          shapeDefinitionsFullMintermBool,
                          ShapeDefinition.fullMintermBool,
                          Clause.CompleteMinterm] using hcomplete
                      · exact ihRest restShape hrestFold
      | true =>
          cases hchildFold :
              foldGroundSelectionSet schema clause
                fieldDefinition.outputType.namedType childSelections with
          | error error =>
              unfold foldGroundSelectionSet at hfold
              simp [hobject, hdirectives, hduplicate, hlookup, hcomposite,
                hchildFold, Bind.bind, Except.bind] at hfold
          | ok childShape =>
              cases hrestFold :
                  foldGroundSelectionSet schema clause parentType rest with
              | error error =>
                  unfold foldGroundSelectionSet at hfold
                  simp [hobject, hdirectives, hduplicate, hlookup, hcomposite,
                    hchildFold, hrestFold, Bind.bind, Except.bind] at hfold
              | ok restShape =>
                  unfold foldGroundSelectionSet at hfold
                  simp [hobject, hdirectives, hduplicate, hlookup, hcomposite,
                    hchildFold, hrestFold, Bind.bind, Except.bind] at hfold
                  subst shape
                  apply mergeResponseShapes_fullMintermBool
                  · have hchildFull :=
                      ihChild fieldDefinition childShape hchildFold
                    simpa [singletonDefinitionShape,
                        ResponseShape.fullMintermBool,
                        responsePositionsFullMintermBool,
                        ResponsePosition.fullMintermBool,
                        possibleDefinitionsFullMintermBool,
                        PossibleDefinitions.fullMintermBool,
                        shapeDefinitionsFullMintermBool,
                        ShapeDefinition.fullMintermBool,
                        Clause.CompleteMinterm, hchildFull] using hcomplete
                  · exact ihRest restShape hrestFold
  | case6 parentType rest hobject responseName fieldName arguments directives
      childSelections hdirectives hduplicate hlookup ihRest ihChild =>
      intro shape hfold
      unfold foldGroundSelectionSet at hfold
      simp [hobject, hdirectives, hduplicate, hlookup, Bind.bind,
        Except.bind] at hfold
  | case7 parentType rest hobject typeCondition directives childSelections =>
      intro shape hfold
      simp [foldGroundSelectionSet, hobject] at hfold
  | case8 parentType rest hobject habstract responseName fieldName arguments
      directives childSelections =>
      intro shape hfold
      simp [foldGroundSelectionSet, hobject, habstract] at hfold
  | case9 parentType rest hobject habstract typeCondition directives
      childSelections hdirectives =>
      intro shape hfold
      simp [foldGroundSelectionSet, hobject, habstract, hdirectives] at hfold
  | case10 parentType rest hobject habstract directives childSelections
      hdirectives objectType ihChild ihRest =>
      intro shape hfold
      unfold foldGroundSelectionSet at hfold
      simp only [hobject, habstract, if_true] at hfold
      rw [if_neg hdirectives] at hfold
      simp only [Bind.bind, Except.bind] at hfold
      simp only [Bool.false_eq_true, if_false] at hfold
      by_cases hduplicate :
          rest.any (selectionHasTypeCondition objectType) = true
      · rw [if_pos hduplicate] at hfold
        simp at hfold
      · rw [if_neg hduplicate] at hfold
        cases hlookup : schema.lookupObject objectType with
        | none => simp [hlookup] at hfold
        | some objectDefinition =>
            cases hincludes :
                schema.typeIncludesObjectBool parentType objectType with
            | false => simp [hlookup, hincludes] at hfold
            | true =>
                cases childSelections with
                | nil => simp [hlookup, hincludes] at hfold
                | cons child restChildren =>
                    cases hchildFold :
                        foldGroundSelectionSet schema clause objectType
                          (child :: restChildren) with
                    | error error =>
                        simp [hlookup, hincludes, hchildFold] at hfold
                    | ok childShape =>
                        cases hrestFold :
                            foldGroundSelectionSet schema clause parentType
                              rest with
                        | error error =>
                            simp [hlookup, hincludes, hchildFold, hrestFold]
                              at hfold
                        | ok restShape =>
                            simp [hlookup, hincludes, hchildFold, hrestFold]
                              at hfold
                            subst shape
                            exact mergeResponseShapes_fullMintermBool
                              support childShape restShape
                              (ihChild objectType childShape hchildFold)
                              (ihRest restShape hrestFold)
  | case11 parentType rest hobject habstract directives childSelections
      hdirectives ihChild ihRest =>
      intro shape hfold
      unfold foldGroundSelectionSet at hfold
      simp only [hobject, habstract, if_true] at hfold
      rw [if_neg hdirectives] at hfold
      simp [Bind.bind, Except.bind] at hfold
  | case12 parentType selection rest hobject habstract =>
      intro shape hfold
      unfold foldGroundSelectionSet at hfold
      rw [if_neg hobject] at hfold
      rw [if_neg habstract] at hfold
      simp at hfold

/-- Successful nonempty-support branch decoding emits only complete minterms. -/
theorem decodeRootBranches_fullMintermBool
    (schema : Schema) (support : List NormalForm.BoolVar) (rootType : Name) :
    ∀ (selections : List Selection) (seen : List Clause)
      (shape : ResponseShape),
      decodeRootBranches schema support rootType seen selections = .ok shape ->
      shape.fullMintermBool support = true
  | [], _seen, shape, hdecode => by
      simp [decodeRootBranches] at hdecode
      subst shape
      rfl
  | selection :: rest, seen, shape, hdecode => by
      cases hstem : decodeCompleteStem support.length selection with
      | error error =>
          simp [decodeRootBranches, hstem, Bind.bind, Except.bind] at hdecode
      | ok decoded =>
          rcases decoded with ⟨literals, branchBody⟩
          cases hclause : clauseFromCompleteStem support literals with
          | error error =>
              simp [decodeRootBranches, hstem, hclause, Bind.bind,
                Except.bind] at hdecode
          | ok clause =>
              have hcomplete : clause.CompleteMinterm support :=
                (clauseFromCompleteStem_ok support literals hclause).2.2
              unfold decodeRootBranches at hdecode
              simp only [hstem, Bind.bind, Except.bind, hclause] at hdecode
              split at hdecode
              · simp at hdecode
              · cases hbranch :
                    foldGroundSelectionSet schema clause rootType branchBody with
                | error error =>
                    simp [hbranch] at hdecode
                | ok branchShape =>
                    cases hrest :
                        decodeRootBranches schema support rootType
                          (clause :: seen) rest with
                    | error error =>
                        simp [hbranch, hrest] at hdecode
                    | ok restShape =>
                        simp [hbranch, hrest] at hdecode
                        subst shape
                        exact mergeResponseShapes_fullMintermBool support
                          branchShape restShape
                          (foldGroundSelectionSet_fullMintermBool schema support
                            clause hcomplete rootType branchBody branchShape
                            hbranch)
                          (decodeRootBranches_fullMintermBool schema support
                            rootType rest (clause :: seen) restShape hrest)

/-- Every successful root decode emits only complete-minterm definitions. -/
theorem decodeCompleteRoot_fullMintermBool
    (schema : Schema) (support : List NormalForm.BoolVar) (rootType : Name)
    (selectionSet : List Selection) (shape : ResponseShape)
    (hdecode :
      decodeCompleteRoot schema support rootType selectionSet = .ok shape) :
    shape.fullMintermBool support = true := by
  cases hduplicate : firstDuplicate? support with
  | some duplicate =>
      simp [decodeCompleteRoot, hduplicate] at hdecode
  | none =>
      cases support with
      | nil =>
          have hcomplete :
              ({ literals := [] } : Clause).CompleteMinterm [] := by
            decide
          apply foldGroundSelectionSet_fullMintermBool schema []
            { literals := [] } hcomplete rootType selectionSet shape
          simpa [decodeCompleteRoot, hduplicate, Bind.bind, Except.bind]
            using hdecode
      | cons varName variables =>
          apply decodeRootBranches_fullMintermBool schema
            (varName :: variables) rootType selectionSet [] shape
          simpa [decodeCompleteRoot, hduplicate, Bind.bind, Except.bind]
            using hdecode

/-- Absence of a reported duplicate establishes list uniqueness. -/
theorem nodup_of_firstDuplicate?_eq_none : ∀ names : List Name,
    firstDuplicate? names = none -> names.Nodup
  | [], _hduplicate => List.nodup_nil
  | name :: rest, hduplicate => by
      unfold firstDuplicate? at hduplicate
      by_cases hmem : name ∈ rest
      · simp [hmem] at hduplicate
      · apply List.nodup_cons.mpr
        exact ⟨hmem,
          nodup_of_firstDuplicate?_eq_none rest (by
            simpa [hmem] using hduplicate)⟩

/-- Successful root decoding establishes uniqueness of the declared support. -/
theorem decodeCompleteRoot_support_nodup
    (schema : Schema) (support : List NormalForm.BoolVar) (rootType : Name)
    (selectionSet : List Selection) (shape : ResponseShape)
    (hdecode :
      decodeCompleteRoot schema support rootType selectionSet = .ok shape) :
    support.Nodup := by
  cases hduplicate : firstDuplicate? support with
  | none => exact nodup_of_firstDuplicate?_eq_none support hduplicate
  | some duplicate =>
      simp [decodeCompleteRoot, hduplicate] at hdecode

/-- A successful operation decoder preserves every operation-level payload. -/
theorem decodeCompleteOperationShape_fields
    (schema : Schema) (support : List NormalForm.BoolVar)
    (normalized : Operation) (shape : OperationShape)
    (hdecode :
      decodeCompleteOperationShape schema support normalized = .ok shape) :
    shape.operationType = normalized.operationType
      ∧ shape.rootType = normalized.rootType schema
      ∧ shape.boolSupport = support
      ∧ decodeCompleteRoot schema support (normalized.rootType schema)
          normalized.selectionSet = .ok shape.root := by
  cases hroot :
      decodeCompleteRoot schema support (normalized.rootType schema)
        normalized.selectionSet with
  | error error =>
      simp [decodeCompleteOperationShape, Bind.bind, Except.bind, hroot]
        at hdecode
  | ok root =>
      simp [decodeCompleteOperationShape, Bind.bind, Except.bind, hroot]
        at hdecode
      subst shape
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- Successful operation decoding establishes uniqueness of stored support. -/
theorem decodeCompleteOperationShape_support_nodup
    (schema : Schema) (support : List NormalForm.BoolVar)
    (normalized : Operation) (shape : OperationShape)
    (hdecode :
      decodeCompleteOperationShape schema support normalized = .ok shape) :
    shape.boolSupport.Nodup := by
  rcases decodeCompleteOperationShape_fields schema support normalized shape
      hdecode with
    ⟨_operationType, _rootType, hsupport, hroot⟩
  rw [hsupport]
  exact decodeCompleteRoot_support_nodup schema support
    (normalized.rootType schema) normalized.selectionSet shape.root hroot

/-- Every successfully decoded operation shape uses complete-minterm guards. -/
theorem decodeCompleteOperationShape_fullMinterm
    (schema : Schema) (support : List NormalForm.BoolVar)
    (normalized : Operation) (shape : OperationShape)
    (hdecode :
      decodeCompleteOperationShape schema support normalized = .ok shape) :
    shape.FullMinterm := by
  rcases decodeCompleteOperationShape_fields schema support normalized shape
      hdecode with
    ⟨_operationType, _rootType, hsupport, hroot⟩
  unfold OperationShape.FullMinterm
  rw [hsupport]
  exact decodeCompleteRoot_fullMintermBool schema support
    (normalized.rootType schema) normalized.selectionSet shape.root hroot


end ResponseShape

end GraphQL
