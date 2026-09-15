import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.FreshPrefixes

/-!
Duplicate-field middle rewrites for group-list selection sets.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance groupListDuplicateFieldMiddleResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField) (middle : List Selection)
    (firstResponse laterResponse : ResponseValue)
    (suffix : List (Name × ResponseValue))
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hfirstResponse
      : firstResponse
        = executeField schema resolvers variableValues completionDepth parentType source
            none
            (executableField first.fieldName first.arguments first.selectionSet))
    (hlaterResponse
      : laterResponse
        = executeField schema resolvers variableValues completionDepth parentType source
            (some firstResponse)
            (executableField later.fieldName later.arguments later.selectionSet))
    (hmiddleEmpty
      : (visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source
          (collectedExecutableSelections
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle))
          (.object [])).fst
        = .object suffix)
    (hmiddleFlatBase
      : VisitSubfieldsFlatCollects schema resolvers variableValues
          (completionDepth + 1) parentType source middle
          (.object [(responseName, firstResponse)]))
    : VisitSubfieldsFlatCollects schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections responseName [first]
          ++ middle
          ++ executableFieldSelections responseName [later])
        (.object []) := by
  let firstField :=
    executableField first.fieldName
      first.arguments first.selectionSet
  let laterField :=
    executableField later.fieldName
      later.arguments later.selectionSet
  let flatMiddle :=
      collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType source
            middle)
  let firstStatus :=
      resultStatus
        (executeField schema resolvers variableValues completionDepth parentType source
          none firstField)
  let middleStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source flatMiddle (.object [])).snd
  let laterVisitResult : Result ResponseValue :=
      executeFieldVisitResult schema resolvers variableValues completionDepth parentType source (some firstResponse) laterField
  let laterStatus :=
    match firstResponse with
    | .null => visitOk
    | _ => resultStatus laterVisitResult
  have hfirstResponse' :
        firstResponse =
          Result.getD default
            (executeField schema resolvers variableValues completionDepth parentType source
              none firstField) := by
    simpa [firstField] using hfirstResponse
  have hfirstValue :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth parentType source
            none firstField) =
      firstResponse := by
    rw [hfirstResponse']
    cases
          executeField schema resolvers variableValues completionDepth parentType source
            none firstField <;> rfl
  have hlaterResponse' :
        laterResponse =
          Result.getD default
            (executeField schema resolvers variableValues completionDepth parentType source
              (some firstResponse) laterField) := by
    simpa [laterField] using hlaterResponse
  have hlaterValue :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth parentType source
            (some firstResponse) laterField) =
      laterResponse := by
    rw [hlaterResponse']
    cases
          executeField schema resolvers variableValues completionDepth parentType source
            (some firstResponse) laterField <;> rfl
  have hlaterValueSameResponse :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth parentType source
            (some firstResponse)
            (executableField later.fieldName
              later.arguments later.selectionSet)) =
         laterResponse := by
    simpa [laterField] using hlaterValue
  have hlaterVisitValue :
      resultValueOrNull laterVisitResult = laterResponse := by
    dsimp [laterVisitResult]
    exact (resultValueOrNull_fieldVisitResult_eq_executeField schema resolvers
      variableValues completionDepth parentType source (some firstResponse)
            laterField).trans
            hlaterValue
  have hfirstVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [first]) (.object []) =
      (.object [(responseName, firstResponse)], firstStatus) := by
    rw [visitSubfields_executableFieldSelections_singleton_succ schema
      resolvers variableValues completionDepth parentType source first]
    simp [firstField, firstStatus, hfirstValue]
  have hmiddleEmptyPair :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object []) =
      (.object suffix, middleStatus) := by
    exact Prod.ext (by simpa [flatMiddle] using hmiddleEmpty) rfl
  have hsuffixFresh :
      responseName ∉ suffix.map Prod.fst := by
    intro hmem
    have hkey :
        responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle).map Prod.fst :=
      visitSubfields_flattened_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source middle suffix
        responseName
        (by simpa [flatMiddle] using hmiddleEmpty)
        hmem
    exact hnotMiddle hkey
  have hmiddleBaseFlat :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object [(responseName, firstResponse)]) =
      (.object ([(responseName, firstResponse)] ++ suffix),
        middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object ([(responseName, firstResponse)] ++ [])) =
        (.object ([(responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      apply visitSubfields_prefix_fresh schema resolvers variableValues
        (completionDepth + 1) parentType source flatMiddle
        [(responseName, firstResponse)] [] suffix middleStatus
      · intro key hmem hname
        rw [show flatMiddle =
            collectedExecutableSelections
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle) by rfl] at hmem
        rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
          at hmem
        have hfieldEq : key = responseName := by
          simpa using hname
        exact hnotMiddle (by simpa [hfieldEq] using hmem)
      · simpa [flatMiddle] using hmiddleEmptyPair
    have hflatBase :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object [(responseName, firstResponse)]) =
        (.object ([(responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      simpa using hflatPrefix
    simpa [VisitSubfieldsFlatCollects, flatMiddle] using hmiddleFlatBase.trans hflatBase
  have hlaterVisitAfterMiddle :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [later])
        (.object ([(responseName, firstResponse)] ++ suffix)) =
      (.object
        (mergeResponseField responseName laterResponse
          ([(responseName, firstResponse)] ++ suffix)),
        laterStatus) := by
    have hlookup :
        responseObjectField? responseName
          (.object ([(responseName, firstResponse)] ++ suffix)) =
        some firstResponse := by
      apply responseObjectField?_object_append_of_some_left
      simp [responseObjectField?, lookupResponseField?]
    rw [show executableFieldSelections responseName [later] =
        [executableFieldSelection responseName later] by rfl]
    simp only [visitSubfields, executableFieldSelection]
    rw [visitSelection_field_allowed_succ schema resolvers variableValues
      completionDepth parentType source responseName later.fieldName
      later.arguments [] later.selectionSet
      (.object ([(responseName, firstResponse)] ++ suffix))
      (selectionDirectivesAllowBool_empty variableValues)]
    rw [hlookup]
    cases firstResponse with
    | null =>
        rcases hlaterLookup with ⟨_laterDefinition, hlaterLookup⟩
        have hlaterNull : laterResponse = .null := by
          rw [hlaterResponse]
          simp [executableField, executeField, hlaterLookup, GraphQL.Execution.Result.getD, reusablePreviousValue?_null]
        have hlaterDataNull :
            Result.getD default
              (executeField schema resolvers variableValues completionDepth
                parentType source (some .null)
                (executableField later.fieldName later.arguments later.selectionSet)) =
            .null := by
          have hdata :
              Result.getD default
                (executeField schema resolvers variableValues completionDepth
                  parentType source (some .null)
                  (executableField later.fieldName later.arguments later.selectionSet)) =
              laterResponse := by
            symm
            simpa [laterField] using hlaterResponse
          exact hdata.trans hlaterNull
        simp [hlaterNull, visitOk, laterStatus, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, mergeResponseFieldResult, executeField, executableField, hlaterLookup, reusablePreviousValue?_null, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine]
    | scalar value =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        change
          mergeResponseField responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth parentType source (some (.scalar value))
                  (executableField later.fieldName
                    later.arguments later.selectionSet)))
              ((responseName, .scalar value) :: suffix) =
            mergeResponseField responseName laterResponse
              ((responseName, .scalar value) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth parentType source (some (.scalar value))
                (executableField later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth parentType source (some (.scalar value))
                    (executableField later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField]
    | object objectFields =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        change
          mergeResponseField responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth parentType source (some (.object objectFields))
                  (executableField later.fieldName
                    later.arguments later.selectionSet)))
              ((responseName, .object objectFields) :: suffix) =
            mergeResponseField responseName laterResponse
              ((responseName, .object objectFields) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth parentType source (some (.object objectFields))
                (executableField later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth parentType source (some (.object objectFields))
                    (executableField later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField]
    | list values =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        change
          mergeResponseField responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth parentType source (some (.list values))
                  (executableField later.fieldName
                    later.arguments later.selectionSet)))
              ((responseName, .list values) :: suffix) =
            mergeResponseField responseName laterResponse
              ((responseName, .list values) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth parentType source (some (.list values))
                (executableField later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth parentType source (some (.list values))
                    (executableField later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField]
  have hmergedMiddleFlat :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle
        (mergeResponseFieldIntoObject responseName laterResponse
          (.object [(responseName, firstResponse)])) =
      (.object
        (mergeResponseField responseName laterResponse
          [(responseName, firstResponse)] ++ suffix),
        middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object
            (mergeResponseField responseName laterResponse
              [(responseName, firstResponse)] ++ [])) =
        (.object
          (mergeResponseField responseName laterResponse
            [(responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      apply visitSubfields_prefix_fresh schema resolvers variableValues
        (completionDepth + 1) parentType source flatMiddle
        (mergeResponseField responseName laterResponse
          [(responseName, firstResponse)])
        [] suffix middleStatus
      · intro key hmem hname
        rw [show flatMiddle =
            collectedExecutableSelections
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle) by rfl] at hmem
        rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
          at hmem
        have hfieldEq : key = responseName := by
          simpa [mergeResponseField, mergeResponse] using hname
        exact hnotMiddle (by simpa [hfieldEq] using hmem)
      · simpa [flatMiddle] using hmiddleEmptyPair
    simpa [mergeResponseFieldIntoObject] using hflatPrefix
  have hraw :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections responseName [first] ++ middle ++
          executableFieldSelections responseName [later]) (.object []) =
      (.object
        (mergeResponseField responseName laterResponse
          ([(responseName, firstResponse)] ++ suffix)),
        combineVisitStatus firstStatus
          (combineVisitStatus middleStatus laterStatus)) := by
    rw [show executableFieldSelections responseName [first] ++ middle ++
        executableFieldSelections responseName [later] =
      executableFieldSelections responseName [first] ++
        (middle ++ executableFieldSelections responseName [later]) by
      simp [List.append_assoc]]
    rw [visitSubfields_append_equivalence]
    rw [hfirstVisit]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source (middle ++ executableFieldSelections responseName [later])
                (.object [(responseName, firstResponse)])
            (rightResult.fst, combineVisitStatus firstStatus rightResult.snd))
            = _
    rw [visitSubfields_append_equivalence]
    rw [hmiddleBaseFlat]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source (executableFieldSelections responseName [later])
                (.object ([(responseName, firstResponse)] ++ suffix))
            (
              rightResult.fst,
              combineVisitStatus firstStatus
                (combineVisitStatus middleStatus rightResult.snd)
            ))
            = _
    rw [hlaterVisitAfterMiddle]
  have hnormalizedBlock :
      collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections responseName [first] ++ middle ++
                executableFieldSelections responseName [later])) =
      executableFieldSelections responseName [first, later] ++ flatMiddle := by
    simpa [flatMiddle]
      using
        executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
          schema variableValues parentType source responseName first later middle
          hnotMiddle
  have hlaterVisitAfterFirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [later])
        (.object [(responseName, firstResponse)]) =
      (mergeResponseFieldIntoObject responseName laterResponse
        (.object [(responseName, firstResponse)]),
        laterStatus) := by
    have hlookup :
        responseObjectField? responseName
          (.object [(responseName, firstResponse)]) =
        some firstResponse := by
      simp [responseObjectField?, lookupResponseField?]
    rw [show executableFieldSelections responseName [later] =
        [executableFieldSelection responseName later] by rfl]
    simp only [visitSubfields, executableFieldSelection]
    rw [visitSelection_field_allowed_succ schema resolvers variableValues
      completionDepth parentType source responseName later.fieldName
      later.arguments [] later.selectionSet
      (.object [(responseName, firstResponse)])
      (selectionDirectivesAllowBool_empty variableValues)]
    rw [hlookup]
    cases firstResponse with
    | null =>
        rcases hlaterLookup with ⟨_laterDefinition, hlaterLookup⟩
        have hlaterNull : laterResponse = .null := by
          rw [hlaterResponse]
          simp [executableField, executeField, hlaterLookup, GraphQL.Execution.Result.getD, reusablePreviousValue?_null]
        have hlaterDataNull :
            Result.getD default
              (executeField schema resolvers variableValues completionDepth
                parentType source (some .null)
                (executableField later.fieldName later.arguments later.selectionSet)) =
            .null := by
          have hdata :
              Result.getD default
                (executeField schema resolvers variableValues completionDepth
                  parentType source (some .null)
                  (executableField later.fieldName later.arguments later.selectionSet)) =
              laterResponse := by
            symm
            simpa [laterField] using hlaterResponse
          exact hdata.trans hlaterNull
        simp [hlaterNull, visitOk, laterStatus, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, mergeResponseFieldResult, executeField, executableField, hlaterLookup, reusablePreviousValue?_null, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine]
    | scalar value =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        change
          mergeResponseField responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth parentType source (some (.scalar value))
                  (executableField later.fieldName
                    later.arguments later.selectionSet)))
              [(responseName, .scalar value)] =
            mergeResponseField responseName laterResponse
              [(responseName, .scalar value)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth parentType source (some (.scalar value))
                (executableField later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth parentType source (some (.scalar value))
                    (executableField later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField]
    | object objectFields =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        change
          mergeResponseField responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth parentType source (some (.object objectFields))
                  (executableField later.fieldName
                    later.arguments later.selectionSet)))
              [(responseName, .object objectFields)] =
            mergeResponseField responseName laterResponse
              [(responseName, .object objectFields)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth parentType source (some (.object objectFields))
                (executableField later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth parentType source (some (.object objectFields))
                    (executableField later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField]
    | list values =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        change
          mergeResponseField responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth parentType source (some (.list values))
                  (executableField later.fieldName
                    later.arguments later.selectionSet)))
              [(responseName, .list values)] =
            mergeResponseField responseName laterResponse
              [(responseName, .list values)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth parentType source (some (.list values))
                (executableField later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth parentType source (some (.list values))
                    (executableField later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField]
  have hfirstLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [first, later])
        (.object []) =
      (mergeResponseFieldIntoObject responseName laterResponse
        (.object [(responseName, firstResponse)]),
        combineVisitStatus firstStatus laterStatus) := by
    rw [show executableFieldSelections responseName [first, later] =
        executableFieldSelections responseName [first] ++ executableFieldSelections responseName [later] by
      rfl]
    rw [visitSubfields_append_equivalence]
    rw [hfirstVisit]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source (executableFieldSelections responseName [later])
                (.object [(responseName, firstResponse)])
            (rightResult.fst, combineVisitStatus firstStatus rightResult.snd))
            = _
    rw [hlaterVisitAfterFirst]
  have hnormalized :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [first, later] ++ flatMiddle)
        (.object []) =
      (.object
        (mergeResponseField responseName laterResponse
          [(responseName, firstResponse)] ++ suffix),
        combineVisitStatus (combineVisitStatus firstStatus laterStatus)
          middleStatus) := by
    rw [visitSubfields_append_equivalence]
    rw [hfirstLater]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source flatMiddle
                (mergeResponseFieldIntoObject responseName laterResponse
                  (.object [(responseName, firstResponse)]))
            (
              rightResult.fst,
              combineVisitStatus (combineVisitStatus firstStatus laterStatus)
                rightResult.snd
            ))
            = _
    rw [hmergedMiddleFlat]
  unfold VisitSubfieldsFlatCollects
  rw [hraw]
  rw [hnormalizedBlock]
  rw [hnormalized]
  apply Prod.ext
  · rw [mergeResponseField_append_of_mem_left responseName laterResponse
      [(responseName, firstResponse)] suffix (by simp)]
  · rw [combineVisitStatus_assoc]
    rw [combineVisitStatus_comm middleStatus laterStatus]

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField) (middle : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddleEmpty
      : ∃ suffix,
          (visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source
            (collectedExecutableSelections
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle))
            (.object [])).fst
          = .object suffix)
    (hmiddleFresh
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollects schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections responseName [first]
          ++ middle
          ++ executableFieldSelections responseName [later])
        (.object []) := by
  rcases hmiddleEmpty with ⟨suffix, hmiddleEmpty⟩
  let firstResponse : ResponseValue :=
      executeField schema resolvers variableValues completionDepth parentType source
        none
        (executableField first.fieldName
          first.arguments first.selectionSet)
  let laterResponse : ResponseValue :=
      executeField schema resolvers variableValues completionDepth parentType source
        (some firstResponse)
        (executableField later.fieldName
          later.arguments later.selectionSet)
  apply
    VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
      schema resolvers variableValues completionDepth parentType source responseName first
      later middle firstResponse laterResponse suffix
      hlaterLookup hnotMiddle
  · rfl
  · rfl
  · exact hmiddleEmpty
  · apply hmiddleFresh
    intro entry hmem hname
    have hfieldName :
        entry.1 ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableEntries_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        entry.1 entry.2 hmem
    have hfieldEq : entry.1 = responseName := by
      simpa using hname
    exact hnotMiddle (by simpa [hfieldEq] using hfieldName)

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_freshPrefixes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField) (middle : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollects schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections responseName [first]
          ++ middle
          ++ executableFieldSelections responseName [later])
        (.object []) := by
  apply VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_fresh
    schema resolvers variableValues completionDepth parentType source responseName first
      later middle hlaterLookup hnotMiddle
  · obtain ⟨suffix, hsuffix⟩ :=
      visitSubfields_preserves_object schema resolvers variableValues
        (completionDepth + 1) parentType source
        (collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
              source middle))
        []
    exact ⟨suffix, hsuffix⟩
  · exact hmiddle

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField) (middle : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections responseName [first]
          ++ middle
          ++ executableFieldSelections responseName [later]) := by
  intro prefixFields hfresh
  let rawBlock :=
    executableFieldSelections responseName [first] ++ middle ++
      executableFieldSelections responseName [later]
  let flatFields :=
    collectedExecutableSelections
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
  have hrawKeyFresh :
      ∀ key,
        key ∈
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock).map Prod.fst ->
          key ∉ prefixFields.map Prod.fst :=
    collectedKeyFresh_of_collectedEntryFresh
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
      (collectFields_fieldsNonempty schema variableValues parentType source
        rawBlock)
      prefixFields
      (by simpa [rawBlock] using hfresh)
  obtain ⟨resultFields, hresultFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source rawBlock []
  let status :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object [])).snd
  have hrawEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object []) =
      (.object resultFields, status) :=
    Prod.ext hresultFields rfl
  have hrawPrefix
      : visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source rawBlock (.object prefixFields)
        = (.object (prefixFields ++ resultFields), status) := by
    simpa using
      visitSubfields_prefix_fresh schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock prefixFields []
        resultFields status hrawKeyFresh hrawEmpty
  have hflatEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatFields (.object []) =
      (.object resultFields, status) := by
    have hflat :=
      VisitSubfieldsFlatCollects_duplicate_field_middle_of_freshPrefixes schema
        resolvers variableValues completionDepth parentType source responseName first
      later
        middle hlaterLookup hnotMiddle hmiddle
    unfold VisitSubfieldsFlatCollects at hflat
    dsimp [rawBlock, flatFields] at hflat
    rw [← hflat]
    exact hrawEmpty
  have hflatPrefix
      : visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatFields
          (.object prefixFields)
        = (.object (prefixFields ++ resultFields), status) := by
    simpa using
      visitSubfields_prefix_fresh schema resolvers variableValues
        (completionDepth + 1) parentType source flatFields
        prefixFields [] resultFields status
        (by
          intro key hmem
          rw [show flatFields =
              collectedExecutableSelections
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rawBlock) by rfl] at hmem
          rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
            at hmem
          exact hrawKeyFresh key hmem)
        hflatEmpty
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object prefixFields) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source flatFields
        (.object prefixFields)
  rw [hrawPrefix, hflatPrefix]

theorem VisitSubfieldsFlatCollects_group_duplicate_field_middle_of_freshPrefixes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections responseName prefixFields
          ++ middle
          ++ executableFieldSelections responseName [later]) (.object []) := by
  let rawBlock :=
    executableFieldSelections responseName prefixFields ++ middle ++
      executableFieldSelections responseName [later]
  let flatMiddle :=
    collectedExecutableSelections
      (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
  let normalizedBlock :=
    executableFieldSelections responseName (prefixFields ++ [later]) ++ flatMiddle
  obtain ⟨middleSuffix, hmiddleSuffix⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source flatMiddle []
  let middleStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source flatMiddle (.object [])).snd
  have hmiddleEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object []) =
      (.object middleSuffix, middleStatus) :=
    Prod.ext hmiddleSuffix rfl
  obtain ⟨prefixResult, hprefixFst, hprefixKey⟩ :=
    visitSubfields_executableFieldSelections_same_response_key_mem schema
      resolvers variableValues completionDepth parentType source responseName
      prefixFields [] hprefixNonempty
  let prefixStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections responseName prefixFields)
      (.object [])).snd
  have hprefixVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName prefixFields)
        (.object []) =
      (.object prefixResult, prefixStatus) :=
    Prod.ext hprefixFst rfl
  have hprefixKeys :
      ∀ key, key ∈ prefixResult.map Prod.fst -> key = responseName := by
    intro key hkey
    have hcollectKey :
        key ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (executableFieldSelections responseName prefixFields)).map Prod.fst :=
      visitSubfields_object_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source
        (executableFieldSelections responseName prefixFields) prefixResult key hprefixFst
        hkey
    exact ((collectFields_executableFieldSelections_key_mem_global schema
              variableValues parentType source responseName prefixFields key).mp
            hcollectKey).2
  have hmiddleFreshPrefix :
      ∀ entry,
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle) ->
        entry.1 ∉ prefixResult.map Prod.fst := by
    intro entry hmem hkey
    have hfieldCollectName :
        entry.1 ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableEntries_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        entry.1 entry.2 hmem
    have hfieldName : entry.1 = responseName :=
      hprefixKeys entry.1 hkey
    exact hnotMiddle (by simpa [hfieldName] using hfieldCollectName)
  have hmiddleKeyFreshPrefix :
      ∀ key,
        key ∈
            (GraphQL.Execution.collectFields schema variableValues parentType
              source flatMiddle).map Prod.fst ->
          key ∉ prefixResult.map Prod.fst := by
    intro key hmem
    rw [show flatMiddle =
        collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle) by rfl] at hmem
    rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
      at hmem
    exact
      collectedKeyFresh_of_collectedEntryFresh
        (GraphQL.Execution.collectFields schema variableValues parentType source
          middle)
        (collectFields_fieldsNonempty schema variableValues parentType source
          middle)
        prefixResult hmiddleFreshPrefix key hmem
  have hmiddlePrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object prefixResult) =
      (.object (prefixResult ++ middleSuffix), middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle (.object prefixResult) =
        (.object (prefixResult ++ middleSuffix), middleStatus) := by
      simpa [flatMiddle]
        using visitSubfields_prefix_fresh schema resolvers variableValues
          (completionDepth + 1) parentType source flatMiddle
          prefixResult [] middleSuffix middleStatus hmiddleKeyFreshPrefix
          (by simpa [flatMiddle] using hmiddleEmpty)
    have hrawFlat := hmiddle prefixResult hmiddleFreshPrefix
    unfold VisitSubfieldsFlatCollects at hrawFlat
    rw [hrawFlat]
    exact hflatPrefix
  have hlaterMemPrefix : responseName ∈ prefixResult.map Prod.fst := by
    exact hprefixKey
  obtain ⟨laterResult, hlaterFst⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections responseName [later]) prefixResult
  let laterStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections responseName [later])
      (.object prefixResult)).snd
  have hlaterVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [later])
        (.object prefixResult) =
      (.object laterResult, laterStatus) :=
    Prod.ext hlaterFst rfl
  have hlaterVisitAfterMiddle :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [later])
        (.object (prefixResult ++ middleSuffix)) =
      (.object (laterResult ++ middleSuffix), laterStatus) :=
    visitSubfields_executableFieldSelections_singleton_append_of_mem_succ
      schema resolvers variableValues completionDepth parentType source
      responseName later
      prefixResult middleSuffix laterResult laterStatus hlaterMemPrefix
      hlaterLookup
      hlaterVisit
  have hraw :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object []) =
      (.object (laterResult ++ middleSuffix),
        combineVisitStatus prefixStatus
          (combineVisitStatus middleStatus laterStatus)) := by
    dsimp [rawBlock]
    rw [show executableFieldSelections responseName prefixFields ++ middle ++
        executableFieldSelections responseName [later] =
      executableFieldSelections responseName prefixFields ++
        (middle ++ executableFieldSelections responseName [later]) by
      simp [List.append_assoc]]
    rw [visitSubfields_append_equivalence]
    rw [hprefixVisit]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source (middle ++ executableFieldSelections responseName [later])
                (.object prefixResult)
            (rightResult.fst, combineVisitStatus prefixStatus rightResult.snd))
            = _
    rw [visitSubfields_append_equivalence]
    rw [hmiddlePrefix]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source (executableFieldSelections responseName [later])
                (.object (prefixResult ++ middleSuffix))
            (
              rightResult.fst,
              combineVisitStatus prefixStatus
                (combineVisitStatus middleStatus rightResult.snd)
            ))
            = _
    rw [hlaterVisitAfterMiddle]
  have hprefixLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName (prefixFields ++ [later]))
        (.object []) =
      (.object laterResult, combineVisitStatus prefixStatus laterStatus) := by
    rw [show executableFieldSelections responseName (prefixFields ++ [later]) =
        executableFieldSelections responseName prefixFields ++
          executableFieldSelections responseName [later] by
      simp [executableFieldSelections, List.map_append]]
    rw [visitSubfields_append_equivalence]
    rw [hprefixVisit]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source (executableFieldSelections responseName [later])
                (.object prefixResult)
            (rightResult.fst, combineVisitStatus prefixStatus rightResult.snd))
            = _
    rw [hlaterVisit]
  have hprefixLaterKeys :
      ∀ key, key ∈ laterResult.map Prod.fst -> key = responseName := by
    intro key hkey
    have hcollectKey :
        key ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source
            (executableFieldSelections responseName (prefixFields ++ [later]))).map
            Prod.fst :=
      visitSubfields_object_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source
        (executableFieldSelections responseName (prefixFields ++ [later])) laterResult key
        (by
          have hfst := congrArg Prod.fst hprefixLater
          simpa using hfst)
        hkey
    exact ((collectFields_executableFieldSelections_key_mem_global schema
              variableValues parentType source responseName
              (prefixFields ++ [later]) key).mp
            hcollectKey).2
  have hmiddleFreshLater :
      ∀ entry,
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle) ->
        entry.1 ∉ laterResult.map Prod.fst := by
    intro entry hmem hkey
    have hfieldCollectName :
        entry.1 ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableEntries_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        entry.1 entry.2 hmem
    have hfieldName : entry.1 = responseName :=
      hprefixLaterKeys entry.1 hkey
    exact hnotMiddle (by simpa [hfieldName] using hfieldCollectName)
  have hmiddleKeyFreshLater :
      ∀ key,
        key ∈
            (GraphQL.Execution.collectFields schema variableValues parentType
              source flatMiddle).map Prod.fst ->
          key ∉ laterResult.map Prod.fst := by
    intro key hmem
    rw [show flatMiddle =
        collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle) by rfl] at hmem
    rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
      at hmem
    exact
      collectedKeyFresh_of_collectedEntryFresh
        (GraphQL.Execution.collectFields schema variableValues parentType source
          middle)
        (collectFields_fieldsNonempty schema variableValues parentType source
          middle)
        laterResult hmiddleFreshLater key hmem
  have hflatMiddleLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object laterResult) =
      (.object (laterResult ++ middleSuffix), middleStatus) := by
    simpa [flatMiddle]
      using visitSubfields_prefix_fresh schema resolvers variableValues
        (completionDepth + 1) parentType source flatMiddle
        laterResult [] middleSuffix middleStatus hmiddleKeyFreshLater
        (by simpa [flatMiddle] using hmiddleEmpty)
  have hnormalized :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source normalizedBlock (.object []) =
      (.object (laterResult ++ middleSuffix),
        combineVisitStatus (combineVisitStatus prefixStatus laterStatus)
          middleStatus) := by
    dsimp [normalizedBlock]
    rw [visitSubfields_append_equivalence]
    rw [hprefixLater]
    change (let rightResult :=
              visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source flatMiddle (.object laterResult)
            (
              rightResult.fst,
              combineVisitStatus (combineVisitStatus prefixStatus laterStatus)
                rightResult.snd
            ))
            = _
    rw [hflatMiddleLater]
  have hnormalizedBlock :
      collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock, flatMiddle]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hnotMiddle
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object []) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source
      (collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType
            source rawBlock))
      (.object [])
  rw [hraw, hnormalizedBlock, hnormalized]
  apply Prod.ext
  · rfl
  · rw [combineVisitStatus_comm middleStatus laterStatus]
    rw [← combineVisitStatus_assoc]

theorem
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (middle : List Selection) (hprefixNonempty : prefixFields ≠ [])
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections responseName prefixFields
          ++ middle
          ++ executableFieldSelections responseName [later]) := by
  intro outputFields hfresh
  let rawBlock :=
    executableFieldSelections responseName prefixFields ++ middle ++
      executableFieldSelections responseName [later]
  let flatFields :=
    collectedExecutableSelections
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
  have hrawKeyFresh :
      ∀ key,
        key ∈
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock).map Prod.fst ->
          key ∉ outputFields.map Prod.fst :=
    collectedKeyFresh_of_collectedEntryFresh
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
      (collectFields_fieldsNonempty schema variableValues parentType source
        rawBlock)
      outputFields
      (by simpa [rawBlock] using hfresh)
  obtain ⟨resultFields, hresultFields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source rawBlock []
  let status :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object [])).snd
  have hrawEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object []) =
      (.object resultFields, status) :=
    Prod.ext hresultFields rfl
  have hrawPrefix
      : visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source rawBlock (.object outputFields)
        = (.object (outputFields ++ resultFields), status) := by
    simpa using
      visitSubfields_prefix_fresh schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock outputFields []
        resultFields status hrawKeyFresh hrawEmpty
  have hflatEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatFields
        (.object []) =
      (.object resultFields, status) := by
    have hflat :=
      VisitSubfieldsFlatCollects_group_duplicate_field_middle_of_freshPrefixes
        schema resolvers variableValues completionDepth parentType source
        responseName prefixFields later middle hprefixNonempty hlaterLookup
        hnotMiddle hmiddle
    unfold VisitSubfieldsFlatCollects at hflat
    dsimp [rawBlock, flatFields] at hflat
    rw [← hflat]
    exact hrawEmpty
  have hflatPrefix
      : visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatFields
          (.object outputFields)
        = (.object (outputFields ++ resultFields), status) := by
    simpa using
      visitSubfields_prefix_fresh schema resolvers variableValues
        (completionDepth + 1) parentType source flatFields
        outputFields [] resultFields status
        (by
          intro key hmem
          rw [show flatFields =
              collectedExecutableSelections
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rawBlock) by rfl] at hmem
          rw [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
            at hmem
          exact hrawKeyFresh key hmem)
        hflatEmpty
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object outputFields) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source flatFields
        (.object outputFields)
  rw [hrawPrefix, hflatPrefix]

theorem visitSubfields_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField) (middle suffix : List Selection)
    (prefixFields : List (Name × ResponseValue))
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    (hfresh
      : ∀ entry,
          entry
            ∈ collectedExecutableEntries
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source
                  (executableFieldSelections responseName [first]
                    ++ middle
                    ++ executableFieldSelections responseName [later]))
          -> entry.1 ∉ prefixFields.map Prod.fst)
    : visitSubfields schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        (.object prefixFields)
      = visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix)
          (.object prefixFields) := by
  let rawBlock :=
    executableFieldSelections responseName [first] ++ middle ++
      executableFieldSelections responseName [later]
  let normalizedBlock :=
    executableFieldSelections responseName [first, later] ++
      collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType source
            middle)
  have hblock :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock
        (.object prefixFields) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
      resolvers variableValues completionDepth parentType source responseName first
      later
      middle hlaterLookup hnotMiddle hmiddle prefixFields hfresh
  have hnormalizedBlock :
      collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source responseName first later middle
        hnotMiddle
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (rawBlock ++ suffix) (.object prefixFields) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (normalizedBlock ++ suffix) (.object prefixFields)
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source rawBlock suffix
    (.object prefixFields)]
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source normalizedBlock suffix
    (.object prefixFields)]
  unfold VisitSubfieldsFlatCollects at hblock
  rw [hnormalizedBlock] at hblock
  rw [hblock]

theorem visitSubfields_group_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle suffix : List Selection)
    (outputFields : List (Name × ResponseValue))
    (hprefixNonempty : prefixFields ≠ [])
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    (hfresh
      : ∀ entry,
          entry
            ∈ collectedExecutableEntries
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source
                  (executableFieldSelections responseName prefixFields
                    ++ middle
                    ++ executableFieldSelections responseName [later]))
          -> entry.1 ∉ outputFields.map Prod.fst)
    : visitSubfields schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections responseName prefixFields
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
        (.object outputFields)
      = visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections responseName (prefixFields ++ [later])
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix)
          (.object outputFields) := by
  let rawBlock :=
    executableFieldSelections responseName prefixFields ++ middle ++
      executableFieldSelections responseName [later]
  let normalizedBlock :=
    executableFieldSelections responseName (prefixFields ++ [later]) ++
      collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType source
            middle)
  have hblock :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock
        (.object outputFields) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
      schema resolvers variableValues completionDepth parentType source
      responseName prefixFields later middle hprefixNonempty hlaterLookup
      hnotMiddle hmiddle outputFields hfresh
  have hnormalizedBlock :
      collectedExecutableSelections
          (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hnotMiddle
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (rawBlock ++ suffix) (.object outputFields) =
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (normalizedBlock ++ suffix) (.object outputFields)
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source rawBlock suffix
    (.object outputFields)]
  rw [visitSubfields_append_equivalence schema resolvers variableValues
    (completionDepth + 1) parentType source normalizedBlock suffix
    (.object outputFields)]
  unfold VisitSubfieldsFlatCollects at hblock
  rw [hnormalizedBlock] at hblock
  rw [hblock]

theorem collectFields_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField) (middle suffix : List Selection)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    : GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
      = GraphQL.Execution.collectFields schema variableValues parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix) := by
  let rawBlock :=
    executableFieldSelections responseName [first] ++ middle ++
      executableFieldSelections responseName [later]
  let normalizedBlock :=
    executableFieldSelections responseName [first, later] ++
      collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)
  have hblock :
      GraphQL.Execution.collectFields schema variableValues parentType source
          rawBlock =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    rw [←
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source responseName first later middle
        hnotMiddle]
    exact (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
            schema variableValues parentType source
            (executableFieldSelections responseName [first]
              ++ middle
              ++ executableFieldSelections responseName [later])).symm
  change
    GraphQL.Execution.collectFields schema variableValues parentType source
        (rawBlock ++ suffix) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (normalizedBlock ++ suffix)
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source rawBlock suffix]
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source normalizedBlock suffix]
  rw [hblock]

theorem collectFields_group_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (prefixFields : List ExecutableField)
    (later : ExecutableField) (middle suffix : List Selection)
    (hprefixNonempty : prefixFields ≠ [])
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    : GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections responseName prefixFields
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix)
      = GraphQL.Execution.collectFields schema variableValues parentType source
          ((executableFieldSelections responseName (prefixFields ++ [later])
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix) := by
  let rawBlock :=
    executableFieldSelections responseName prefixFields ++ middle ++
      executableFieldSelections responseName [later]
  let normalizedBlock :=
    executableFieldSelections responseName (prefixFields ++ [later]) ++
      collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)
  have hblock :
      GraphQL.Execution.collectFields schema variableValues parentType source
          rawBlock =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    rw [←
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hnotMiddle]
    exact (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
            schema variableValues parentType source
            (executableFieldSelections responseName prefixFields
              ++ middle
              ++ executableFieldSelections responseName [later])).symm
  change
    GraphQL.Execution.collectFields schema variableValues parentType source
        (rawBlock ++ suffix) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (normalizedBlock ++ suffix)
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source rawBlock suffix]
  rw [GraphQL.NormalForm.collectFields_append schema variableValues parentType
    source normalizedBlock suffix]
  rw [hblock]

theorem
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_normalized
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    (hnormalized
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections responseName [first, later]
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix))
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections responseName [first]
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix) := by
  intro prefixFields hfresh
  let rawBlock :=
    executableFieldSelections responseName [first] ++ middle ++
      executableFieldSelections responseName [later]
  let normalized :=
    (executableFieldSelections responseName [first, later] ++
      collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)) ++ suffix
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (rawBlock ++ suffix) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalized := by
    dsimp [rawBlock, normalized]
    exact
      collectFields_duplicate_field_middle_append_eq_collected_middle schema
        variableValues parentType source responseName first later middle suffix
        hnotMiddle
  have hblockFresh :
      ∀ entry,
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) ->
        entry.1 ∉ prefixFields.map Prod.fst := by
    intro entry hentry
    apply hfresh entry
    have hentryRaw :
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix)) := by
      exact (collectedExecutableEntries_mem_mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix) entry).mpr
              (Or.inl hentry)
    have hentryWhole :
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (rawBlock ++ suffix)) := by
      rw [GraphQL.NormalForm.collectFields_append schema variableValues
        parentType source rawBlock suffix]
      exact hentryRaw
    simpa [rawBlock] using hentryWhole
  change
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source (rawBlock ++ suffix)
      (.object prefixFields)
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_duplicate_field_middle_append_eq_collected_middle schema
    resolvers variableValues completionDepth parentType source responseName first
      later
    middle suffix prefixFields hlaterLookup hnotMiddle hmiddle
    hblockFresh]
  rw [hcollect]
  exact hnormalized prefixFields
    (by
      intro entry hentry
      have hentryRaw :
          entry ∈
            collectedExecutableEntries
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (rawBlock ++ suffix)) := by
        rw [hcollect]
        exact hentry
      apply hfresh entry
      simpa [rawBlock, List.append_assoc] using hentryRaw)

theorem
    VisitSubfieldsFlatCollectsFreshPrefixes_group_duplicate_field_middle_append_of_normalized
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (middle suffix : List Selection) (hprefixNonempty : prefixFields ≠ [])
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    (hnormalized
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections responseName (prefixFields ++ [later])
              ++ collectedExecutableSelections
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source middle))
            ++ suffix))
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections responseName prefixFields
            ++ middle
            ++ executableFieldSelections responseName [later])
          ++ suffix) := by
  intro outputFields hfresh
  let rawBlock :=
    executableFieldSelections responseName prefixFields ++ middle ++
      executableFieldSelections responseName [later]
  let normalized :=
    (executableFieldSelections responseName (prefixFields ++ [later]) ++
      collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType
            source middle)) ++ suffix
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (rawBlock ++ suffix) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalized := by
    dsimp [rawBlock, normalized]
    exact
      collectFields_group_duplicate_field_middle_append_eq_collected_middle
        schema variableValues parentType source responseName prefixFields later
        middle suffix hprefixNonempty hnotMiddle
  have hblockFresh :
      ∀ entry,
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) ->
        entry.1 ∉ outputFields.map Prod.fst := by
    intro entry hentry
    apply hfresh entry
    have hentryRaw :
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix)) := by
      exact (collectedExecutableEntries_mem_mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix) entry).mpr
              (Or.inl hentry)
    have hentryWhole :
        entry ∈
          collectedExecutableEntries
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (rawBlock ++ suffix)) := by
      rw [GraphQL.NormalForm.collectFields_append schema variableValues
        parentType source rawBlock suffix]
      exact hentryRaw
    simpa [rawBlock] using hentryWhole
  change
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source (rawBlock ++ suffix)
      (.object outputFields)
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_group_duplicate_field_middle_append_eq_collected_middle
    schema resolvers variableValues completionDepth parentType source
    responseName prefixFields later middle suffix outputFields hprefixNonempty
    hlaterLookup hnotMiddle hmiddle hblockFresh]
  rw [hcollect]
  exact hnormalized outputFields
    (by
      intro entry hentry
      have hentryRaw :
          entry ∈
            collectedExecutableEntries
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (rawBlock ++ suffix)) := by
        rw [hcollect]
        exact hentry
      apply hfresh entry
      simpa [rawBlock, List.append_assoc] using hentryRaw)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_of_allOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (first later : ExecutableField) (middle : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections responseName [first]
          ++ middle
          ++ executableFieldSelections responseName [later]) :=
  VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
    resolvers variableValues completionDepth parentType source responseName first
    later
    middle hlaterLookup hnotMiddle
    (VisitSubfieldsFlatCollectsFreshPrefixes.of_allOutputs schema resolvers
      variableValues (completionDepth + 1) parentType source middle hmiddle)

theorem
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections responseName [first]
              ++ middle
              ++ executableFieldSelections responseName [later]))
          (GraphQL.Execution.collectFields schema variableValues parentType source
            suffix))
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    (hsuffix
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source suffix)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections responseName [first]
          ++ middle
          ++ executableFieldSelections responseName [later]
          ++ suffix) := by
  have hblock :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections responseName [first] ++ middle ++
          executableFieldSelections responseName [later]) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
      resolvers variableValues completionDepth parentType source responseName first
      later
      middle hlaterLookup hnotMiddle hmiddle
  simpa [List.append_assoc]
    using VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint schema
      resolvers variableValues (completionDepth + 1) parentType source
      (executableFieldSelections responseName [first]
        ++ middle
        ++ executableFieldSelections responseName [later])
      suffix hdisjoint hblock hsuffix

theorem
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_headDisjointTrees
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (first later : ExecutableField) (middle suffix : List Selection)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections responseName [first]
              ++ middle
              ++ executableFieldSelections responseName [later]))
          (GraphQL.Execution.collectFields schema variableValues parentType source
            suffix))
    (hmiddle
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source middle)
    (hsuffix
      : SelectionSetCollectFieldsHeadDisjointTree schema variableValues
          parentType source suffix)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections responseName [first]
          ++ middle
          ++ executableFieldSelections responseName [later]
          ++ suffix) :=
  VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
    schema resolvers variableValues completionDepth parentType source responseName first
    later
    middle suffix hlaterLookup hnotMiddle hdisjoint
    (VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source middle
      hmiddle)
    (VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source suffix
      hsuffix)

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
