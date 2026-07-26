import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.GroupList.FreshPrefixes

/-!
Duplicate-field middle rewrites for group-list selection sets.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

local instance groupListDuplicateFieldMiddleResponseVisitStatusCoe
    : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (firstResponse laterResponse : ResponseValue)
    (suffix : List (Name × ResponseValue))
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hfirstResponse
      : firstResponse
        = executeField schema resolvers variableValues completionDepth source
            none
            (executableField parentType first.responseName first.fieldName
              first.arguments first.selectionSet))
    (hlaterResponse
      : laterResponse
        = executeField schema resolvers variableValues completionDepth source
            (some firstResponse)
            (executableField parentType later.responseName later.fieldName
              later.arguments later.selectionSet))
    (hmiddleEmpty
      : (visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source
          (executableFieldSelections
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle)))
          (.object [])).fst
        = .object suffix)
    (hmiddleFlatBase
      : VisitSubfieldsFlatCollects schema resolvers variableValues
          (completionDepth + 1) parentType source middle
          (.object [(first.responseName, firstResponse)]))
    : VisitSubfieldsFlatCollects schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++ executableFieldSelections [later])
        (.object []) := by
  let firstField :=
    executableField parentType first.responseName first.fieldName
      first.arguments first.selectionSet
  let laterField :=
    executableField parentType later.responseName later.fieldName
      later.arguments later.selectionSet
  let flatMiddle :=
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle))
  let firstStatus :=
      resultStatus
        (executeField schema resolvers variableValues completionDepth source
          none firstField)
  let middleStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source flatMiddle (.object [])).snd
  let laterVisitResult : Result ResponseValue :=
      executeFieldVisitResult schema resolvers variableValues completionDepth
        source (some firstResponse) laterField
  let laterStatus :=
    match firstResponse with
    | .null => visitOk
    | _ => resultStatus laterVisitResult
  have hfirstResponse' :
        firstResponse =
          Result.getD default
            (executeField schema resolvers variableValues completionDepth source
              none firstField) := by
    simpa [firstField] using hfirstResponse
  have hfirstValue :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            none firstField) =
      firstResponse := by
    rw [hfirstResponse']
    cases
          executeField schema resolvers variableValues completionDepth source
            none firstField <;> rfl
  have hlaterResponse' :
        laterResponse =
          Result.getD default
            (executeField schema resolvers variableValues completionDepth source
              (some firstResponse) laterField) := by
    simpa [laterField] using hlaterResponse
  have hlaterValue :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            (some firstResponse) laterField) =
      laterResponse := by
    rw [hlaterResponse']
    cases
          executeField schema resolvers variableValues completionDepth source
            (some firstResponse) laterField <;> rfl
  have hlaterValueSameResponse :
        resultValueOrNull
          (executeField schema resolvers variableValues completionDepth source
            (some firstResponse)
            (executableField parentType first.responseName later.fieldName
              later.arguments later.selectionSet)) =
         laterResponse := by
    simpa [laterField, hsameResponse] using hlaterValue
  have hlaterVisitValue :
      resultValueOrNull laterVisitResult = laterResponse := by
    dsimp [laterVisitResult]
    exact
        (resultValueOrNull_fieldVisitResult_eq_executeField schema resolvers
          variableValues completionDepth source (some firstResponse)
          laterField).trans
        hlaterValue
  have hfirstVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first]) (.object []) =
      (.object [(first.responseName, firstResponse)], firstStatus) := by
    rw [visitSubfields_executableFieldSelections_singleton_succ schema
      resolvers variableValues completionDepth parentType source first]
    simp [firstField, firstStatus, hfirstValue]
  have hmiddleEmptyPair :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object []) =
      (.object suffix, middleStatus) := by
    exact Prod.ext (by simpa [flatMiddle] using hmiddleEmpty) rfl
  have hsuffixFresh :
      first.responseName ∉ suffix.map Prod.fst := by
    intro hmem
    have hkey :
        first.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle).map Prod.fst :=
      visitSubfields_flattened_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source middle suffix
        first.responseName
        (by simpa [flatMiddle] using hmiddleEmpty)
        hmem
    exact hnotMiddle hkey
  have hmiddleBaseFlat :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object [(first.responseName, firstResponse)]) =
      (.object ([(first.responseName, firstResponse)] ++ suffix),
        middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object ([(first.responseName, firstResponse)] ++ [])) =
        (.object ([(first.responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      apply visitSubfields_executableFieldSelections_prefix_fresh schema
        resolvers variableValues (completionDepth + 1) parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
        [(first.responseName, firstResponse)] [] suffix middleStatus
      · intro field hmem hname
        have hfieldName :
            field.responseName ∈
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle).map Prod.fst :=
          collectedExecutableFields_responseName_mem
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle)
            (collectFields_responseName schema variableValues parentType source
              middle)
            field hmem
        have hfieldEq : field.responseName = first.responseName := by
          simpa using hname
        exact hnotMiddle (by simpa [hfieldEq] using hfieldName)
      · simpa [flatMiddle] using hmiddleEmptyPair
    have hflatBase :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object [(first.responseName, firstResponse)]) =
        (.object ([(first.responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      simpa using hflatPrefix
    simpa [VisitSubfieldsFlatCollects, flatMiddle] using
      hmiddleFlatBase.trans hflatBase
  have hlaterVisitAfterMiddle :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object ([(first.responseName, firstResponse)] ++ suffix)) =
      (.object
        (mergeResponseField first.responseName laterResponse
          ([(first.responseName, firstResponse)] ++ suffix)),
        laterStatus) := by
    have hlookup :
        responseObjectField? later.responseName
          (.object ([(first.responseName, firstResponse)] ++ suffix)) =
        some firstResponse := by
      apply responseObjectField?_object_append_of_some_left
      simp [responseObjectField?, lookupResponseField?, hsameResponse]
    rw [show executableFieldSelections [later] =
        [executableFieldSelection later] by rfl]
    simp only [visitSubfields, executableFieldSelection]
    rw [visitSelection_field_allowed_succ schema resolvers variableValues
      completionDepth parentType source later.responseName later.fieldName
      later.arguments [] later.selectionSet
      (.object ([(first.responseName, firstResponse)] ++ suffix))
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
                source (some .null)
                (executableField parentType first.responseName
                  later.fieldName later.arguments later.selectionSet)) =
            .null := by
          have hdata :
              Result.getD default
                (executeField schema resolvers variableValues completionDepth
                  source (some .null)
                  (executableField parentType first.responseName
                    later.fieldName later.arguments later.selectionSet)) =
              laterResponse := by
            symm
            simpa [laterField, hsameResponse] using hlaterResponse
          exact hdata.trans hlaterNull
        simp [hlaterNull, visitOk, laterStatus, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, hsameResponse, mergeResponseFieldResult, executeField, executableField, hlaterLookup, reusablePreviousValue?_null, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine]
    | scalar value =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.scalar value))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              ((first.responseName, .scalar value) :: suffix) =
            mergeResponseField first.responseName laterResponse
              ((first.responseName, .scalar value) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.scalar value))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.scalar value))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | object objectFields =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.object objectFields))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              ((first.responseName, .object objectFields) :: suffix) =
            mergeResponseField first.responseName laterResponse
              ((first.responseName, .object objectFields) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.object objectFields))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.object objectFields))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | list values =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.list values))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              ((first.responseName, .list values) :: suffix) =
            mergeResponseField first.responseName laterResponse
              ((first.responseName, .list values) :: suffix) ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.list values))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.list values))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
  have hmergedMiddleFlat :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle
        (mergeResponseFieldIntoObject first.responseName laterResponse
          (.object [(first.responseName, firstResponse)])) =
      (.object
        (mergeResponseField first.responseName laterResponse
          [(first.responseName, firstResponse)] ++ suffix),
        middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (.object
            (mergeResponseField first.responseName laterResponse
              [(first.responseName, firstResponse)] ++ [])) =
        (.object
          (mergeResponseField first.responseName laterResponse
            [(first.responseName, firstResponse)] ++ suffix),
          middleStatus) := by
      apply visitSubfields_executableFieldSelections_prefix_fresh schema
        resolvers variableValues (completionDepth + 1) parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
        (mergeResponseField first.responseName laterResponse
          [(first.responseName, firstResponse)])
        [] suffix middleStatus
      · intro field hmem hname
        have hfieldName :
            field.responseName ∈
              (GraphQL.Execution.collectFields schema variableValues parentType
                source middle).map Prod.fst :=
          collectedExecutableFields_responseName_mem
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle)
            (collectFields_responseName schema variableValues parentType source
              middle)
            field hmem
        have hfieldEq : field.responseName = first.responseName := by
          simpa [mergeResponseField, mergeResponse] using hname
        exact hnotMiddle (by simpa [hfieldEq] using hfieldName)
      · simpa [flatMiddle] using hmiddleEmptyPair
    simpa [mergeResponseFieldIntoObject] using hflatPrefix
  have hraw :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) (.object []) =
      (.object
        (mergeResponseField first.responseName laterResponse
          ([(first.responseName, firstResponse)] ++ suffix)),
        combineVisitStatus firstStatus
          (combineVisitStatus middleStatus laterStatus)) := by
    rw [show executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later] =
      executableFieldSelections [first] ++
        (middle ++ executableFieldSelections [later]) by
      simp [List.append_assoc]]
    rw [visitSubfields_append_equivalence]
    rw [hfirstVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (middle ++ executableFieldSelections [later])
          (.object [(first.responseName, firstResponse)])
       (rightResult.fst, combineVisitStatus firstStatus rightResult.snd)) =
      _
    rw [visitSubfields_append_equivalence]
    rw [hmiddleBaseFlat]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object ([(first.responseName, firstResponse)] ++ suffix))
       (rightResult.fst,
        combineVisitStatus firstStatus
          (combineVisitStatus middleStatus rightResult.snd))) =
      _
    rw [hlaterVisitAfterMiddle]
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source
              (executableFieldSelections [first] ++ middle ++
                executableFieldSelections [later]))) =
      executableFieldSelections [first, later] ++ flatMiddle := by
    simpa [flatMiddle] using
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source first later middle
        hsameResponse hnotMiddle
  have hlaterVisitAfterFirst :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object [(first.responseName, firstResponse)]) =
      (mergeResponseFieldIntoObject first.responseName laterResponse
        (.object [(first.responseName, firstResponse)]),
        laterStatus) := by
    have hlookup :
        responseObjectField? later.responseName
          (.object [(first.responseName, firstResponse)]) =
        some firstResponse := by
      simp [responseObjectField?, lookupResponseField?, hsameResponse]
    rw [show executableFieldSelections [later] =
        [executableFieldSelection later] by rfl]
    simp only [visitSubfields, executableFieldSelection]
    rw [visitSelection_field_allowed_succ schema resolvers variableValues
      completionDepth parentType source later.responseName later.fieldName
      later.arguments [] later.selectionSet
      (.object [(first.responseName, firstResponse)])
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
                source (some .null)
                (executableField parentType first.responseName
                  later.fieldName later.arguments later.selectionSet)) =
            .null := by
          have hdata :
              Result.getD default
                (executeField schema resolvers variableValues completionDepth
                  source (some .null)
                  (executableField parentType first.responseName
                    later.fieldName later.arguments later.selectionSet)) =
              laterResponse := by
            symm
            simpa [laterField, hsameResponse] using hlaterResponse
          exact hdata.trans hlaterNull
        simp [hlaterNull, visitOk, laterStatus, mergeResponseFieldIntoObject, mergeResponseField, mergeResponse, hsameResponse, mergeResponseFieldResult, executeField, executableField, hlaterLookup, reusablePreviousValue?_null, resultStatus, combineVisitStatus, GraphQL.Execution.Result.combine]
    | scalar value =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.scalar value))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              [(first.responseName, .scalar value)] =
            mergeResponseField first.responseName laterResponse
              [(first.responseName, .scalar value)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.scalar value))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.scalar value))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | object objectFields =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.object objectFields))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              [(first.responseName, .object objectFields)] =
            mergeResponseField first.responseName laterResponse
              [(first.responseName, .object objectFields)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.object objectFields))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.object objectFields))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
    | list values =>
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          laterStatus]
        rw [hsameResponse]
        change
          mergeResponseField first.responseName
              (resultValueOrNull
                (executeFieldVisitResult schema resolvers variableValues
                  completionDepth source (some (.list values))
                  (executableField parentType first.responseName later.fieldName
                    later.arguments later.selectionSet)))
              [(first.responseName, .list values)] =
            mergeResponseField first.responseName laterResponse
              [(first.responseName, .list values)] ∧
          resultStatus
              (executeFieldVisitResult schema resolvers variableValues
                completionDepth source (some (.list values))
                (executableField parentType first.responseName later.fieldName
                  later.arguments later.selectionSet)) =
            laterStatus
        constructor
        · rw [show
              resultValueOrNull
                  (executeFieldVisitResult schema resolvers variableValues
                    completionDepth source (some (.list values))
                    (executableField parentType first.responseName
                      later.fieldName later.arguments later.selectionSet)) =
                laterResponse by
                simpa [laterVisitResult, laterField, hsameResponse] using
                  hlaterVisitValue]
        · simp [laterStatus, laterVisitResult, laterField, hsameResponse]
  have hfirstLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first, later])
        (.object []) =
      (mergeResponseFieldIntoObject first.responseName laterResponse
        (.object [(first.responseName, firstResponse)]),
        combineVisitStatus firstStatus laterStatus) := by
    rw [show executableFieldSelections [first, later] =
        executableFieldSelections [first] ++ executableFieldSelections [later] by
      rfl]
    rw [visitSubfields_append_equivalence]
    rw [hfirstVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object [(first.responseName, firstResponse)])
       (rightResult.fst, combineVisitStatus firstStatus rightResult.snd)) =
      _
    rw [hlaterVisitAfterFirst]
  have hnormalized :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [first, later] ++ flatMiddle)
        (.object []) =
      (.object
        (mergeResponseField first.responseName laterResponse
          [(first.responseName, firstResponse)] ++ suffix),
        combineVisitStatus (combineVisitStatus firstStatus laterStatus)
          middleStatus) := by
    rw [visitSubfields_append_equivalence]
    rw [hfirstLater]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle
          (mergeResponseFieldIntoObject first.responseName laterResponse
            (.object [(first.responseName, firstResponse)]))
       (rightResult.fst,
        combineVisitStatus (combineVisitStatus firstStatus laterStatus)
          rightResult.snd)) =
      _
    rw [hmergedMiddleFlat]
  unfold VisitSubfieldsFlatCollects
  rw [hraw]
  rw [hnormalizedBlock]
  rw [hnormalized]
  apply Prod.ext
  · rw [mergeResponseField_append_of_mem_left first.responseName laterResponse
      [(first.responseName, firstResponse)] suffix (by simp)]
  · rw [combineVisitStatus_assoc]
    rw [combineVisitStatus_comm middleStatus laterStatus]

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddleEmpty
      : ∃ suffix,
          (visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source
            (executableFieldSelections
              (collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source middle)))
            (.object [])).fst
          = .object suffix)
    (hmiddleFresh
      : ∀ fields,
          (∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    source middle)
            -> field.responseName ∉ fields.map Prod.fst)
          -> VisitSubfieldsFlatCollects schema resolvers variableValues
              (completionDepth + 1) parentType source middle (.object fields))
    : VisitSubfieldsFlatCollects schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++ executableFieldSelections [later])
        (.object []) := by
  rcases hmiddleEmpty with ⟨suffix, hmiddleEmpty⟩
  let firstResponse : ResponseValue :=
      executeField schema resolvers variableValues completionDepth source
        none
        (executableField parentType first.responseName first.fieldName
          first.arguments first.selectionSet)
  let laterResponse : ResponseValue :=
      executeField schema resolvers variableValues completionDepth source
        (some firstResponse)
        (executableField parentType later.responseName later.fieldName
          later.arguments later.selectionSet)
  apply
    VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_singleton
      schema resolvers variableValues completionDepth parentType source first
      later middle firstResponse laterResponse suffix hsameResponse
      hlaterLookup hnotMiddle
  · rfl
  · rfl
  · exact hmiddleEmpty
  · apply hmiddleFresh
    intro field hmem hname
    have hfieldName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        field hmem
    have hfieldEq : field.responseName = first.responseName := by
      simpa using hname
    exact hnotMiddle (by simpa [hfieldEq] using hfieldName)

theorem VisitSubfieldsFlatCollects_duplicate_field_middle_of_freshPrefixes
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollects schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections [first] ++ middle ++ executableFieldSelections [later])
        (.object []) := by
  apply VisitSubfieldsFlatCollects_duplicate_field_middle_of_flat_middle_fresh
    schema resolvers variableValues completionDepth parentType source first
    later middle hsameResponse hlaterLookup hnotMiddle
  · obtain ⟨suffix, hsuffix⟩ :=
      visitSubfields_preserves_object schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle)))
        []
    exact ⟨suffix, hsuffix⟩
  · exact hmiddle

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]) := by
  intro prefixFields hfresh
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let flatFields :=
    collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
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
  have hrawPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object prefixFields) =
      (.object (prefixFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_prefix_fresh schema resolvers variableValues
          (completionDepth + 1) parentType source rawBlock prefixFields []
          resultFields status hfresh hrawEmpty
  have hflatEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields) (.object []) =
      (.object resultFields, status) := by
    have hflat :=
      VisitSubfieldsFlatCollects_duplicate_field_middle_of_freshPrefixes schema
        resolvers variableValues completionDepth parentType source first later
        middle hsameResponse hlaterLookup hnotMiddle hmiddle
    unfold VisitSubfieldsFlatCollects at hflat
    dsimp [rawBlock, flatFields] at hflat
    rw [← hflat]
    exact hrawEmpty
  have hflatPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields)
        (.object prefixFields) =
      (.object (prefixFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues (completionDepth + 1) parentType source flatFields
          prefixFields [] resultFields status
          (by
            intro field hmem
            exact hfresh field
              (show
                field ∈
                  collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source
                      (executableFieldSelections [first] ++ middle ++
                        executableFieldSelections [later])) from
                by
                  change
                    field ∈
                      collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source rawBlock)
                  exact hmem))
          hflatEmpty
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object prefixFields) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections flatFields)
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
    (hprefixResponse : ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
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
        (executableFieldSelections prefixFields
          ++ middle
          ++ executableFieldSelections [later]) (.object []) := by
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let flatMiddle :=
    executableFieldSelections
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle))
  let normalizedBlock :=
    executableFieldSelections (prefixFields ++ [later]) ++ flatMiddle
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
      prefixFields [] hprefixNonempty hprefixResponse
  let prefixStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections prefixFields)
      (.object [])).snd
  have hprefixVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections prefixFields)
        (.object []) =
      (.object prefixResult, prefixStatus) :=
    Prod.ext hprefixFst rfl
  have hprefixKeys :
      ∀ key, key ∈ prefixResult.map Prod.fst -> key = responseName := by
    intro key hkey
    have hcollectKey :
        key ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source (executableFieldSelections prefixFields)).map Prod.fst :=
      visitSubfields_object_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source
        (executableFieldSelections prefixFields) prefixResult key hprefixFst
        hkey
    have hfieldKey :
        key ∈ prefixFields.map (fun field => field.responseName) :=
      (collectFields_executableFieldSelections_key_mem_global schema
        variableValues parentType source prefixFields key).mp hcollectKey
    rcases List.mem_map.mp hfieldKey with ⟨field, hfield, hfieldKeyEq⟩
    rw [← hfieldKeyEq]
    exact hprefixResponse field hfield
  have hmiddleFreshPrefix :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle) ->
        field.responseName ∉ prefixResult.map Prod.fst := by
    intro field hmem hkey
    have hfieldCollectName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        field hmem
    have hfieldName : field.responseName = responseName :=
      hprefixKeys field.responseName hkey
    exact hnotMiddle (by simpa [hfieldName] using hfieldCollectName)
  have hmiddlePrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source middle (.object prefixResult) =
      (.object (prefixResult ++ middleSuffix), middleStatus) := by
    have hflatPrefix :
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle (.object prefixResult) =
        (.object (prefixResult ++ middleSuffix), middleStatus) := by
      simpa [flatMiddle] using
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues (completionDepth + 1) parentType source
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle))
          prefixResult [] middleSuffix middleStatus hmiddleFreshPrefix
          (by simpa [flatMiddle] using hmiddleEmpty)
    have hrawFlat := hmiddle prefixResult hmiddleFreshPrefix
    unfold VisitSubfieldsFlatCollects at hrawFlat
    rw [hrawFlat]
    exact hflatPrefix
  have hlaterMemPrefix : later.responseName ∈ prefixResult.map Prod.fst := by
    simpa [hlaterResponse] using hprefixKey
  obtain ⟨laterResult, hlaterFst⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (completionDepth + 1) parentType source
      (executableFieldSelections [later]) prefixResult
  let laterStatus :=
    (visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections [later])
      (.object prefixResult)).snd
  have hlaterVisit :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object prefixResult) =
      (.object laterResult, laterStatus) :=
    Prod.ext hlaterFst rfl
  have hlaterVisitAfterMiddle :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections [later])
        (.object (prefixResult ++ middleSuffix)) =
      (.object (laterResult ++ middleSuffix), laterStatus) :=
    visitSubfields_executableFieldSelections_singleton_append_of_mem_succ
      schema resolvers variableValues completionDepth parentType source later
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
    rw [show executableFieldSelections prefixFields ++ middle ++
        executableFieldSelections [later] =
      executableFieldSelections prefixFields ++
        (middle ++ executableFieldSelections [later]) by
      simp [List.append_assoc]]
    rw [visitSubfields_append_equivalence]
    rw [hprefixVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (middle ++ executableFieldSelections [later])
          (.object prefixResult)
       (rightResult.fst,
        combineVisitStatus prefixStatus rightResult.snd)) =
      _
    rw [visitSubfields_append_equivalence]
    rw [hmiddlePrefix]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object (prefixResult ++ middleSuffix))
       (rightResult.fst,
        combineVisitStatus prefixStatus
          (combineVisitStatus middleStatus rightResult.snd))) =
      _
    rw [hlaterVisitAfterMiddle]
  have hprefixLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections (prefixFields ++ [later]))
        (.object []) =
      (.object laterResult, combineVisitStatus prefixStatus laterStatus) := by
    rw [show executableFieldSelections (prefixFields ++ [later]) =
        executableFieldSelections prefixFields ++
          executableFieldSelections [later] by
      simp [executableFieldSelections, List.map_append]]
    rw [visitSubfields_append_equivalence]
    rw [hprefixVisit]
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections [later])
          (.object prefixResult)
       (rightResult.fst,
        combineVisitStatus prefixStatus rightResult.snd)) =
      _
    rw [hlaterVisit]
  have hprefixLaterKeys :
      ∀ key, key ∈ laterResult.map Prod.fst -> key = responseName := by
    intro key hkey
    have hcollectKey :
        key ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source
            (executableFieldSelections (prefixFields ++ [later]))).map
            Prod.fst :=
      visitSubfields_object_empty_key_mem_collectFields schema resolvers
        variableValues (completionDepth + 1) parentType source
        (executableFieldSelections (prefixFields ++ [later])) laterResult key
        (by
          have hfst := congrArg Prod.fst hprefixLater
          simpa using hfst)
        hkey
    have hfieldKey :
        key ∈ (prefixFields ++ [later]).map
          (fun field => field.responseName) :=
      (collectFields_executableFieldSelections_key_mem_global schema
        variableValues parentType source (prefixFields ++ [later]) key).mp
        hcollectKey
    rcases List.mem_map.mp hfieldKey with ⟨field, hfield, hfieldKeyEq⟩
    rw [← hfieldKeyEq]
    rcases List.mem_append.mp hfield with hprefix | hlater
    · exact hprefixResponse field hprefix
    · rcases List.mem_singleton.mp hlater
      exact hlaterResponse
  have hmiddleFreshLater :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source middle) ->
        field.responseName ∉ laterResult.map Prod.fst := by
    intro field hmem hkey
    have hfieldCollectName :
        field.responseName ∈
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map Prod.fst :=
      collectedExecutableFields_responseName_mem
        (GraphQL.Execution.collectFields schema variableValues parentType
          source middle)
        (collectFields_responseName schema variableValues parentType source
          middle)
        field hmem
    have hfieldName : field.responseName = responseName :=
      hprefixLaterKeys field.responseName hkey
    exact hnotMiddle (by simpa [hfieldName] using hfieldCollectName)
  have hflatMiddleLater :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source flatMiddle (.object laterResult) =
      (.object (laterResult ++ middleSuffix), middleStatus) := by
    simpa [flatMiddle] using
      visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
        variableValues (completionDepth + 1) parentType source
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
        laterResult [] middleSuffix middleStatus hmiddleFreshLater
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
    change
      (let rightResult :=
        visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source flatMiddle (.object laterResult)
       (rightResult.fst,
        combineVisitStatus (combineVisitStatus prefixStatus laterStatus)
          rightResult.snd)) =
      _
    rw [hflatMiddleLater]
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock)) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock, flatMiddle]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object []) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source
      (executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rawBlock)))
      (.object [])
  rw [hraw, hnormalizedBlock, hnormalized]
  apply Prod.ext
  · rfl
  · rw [combineVisitStatus_comm middleStatus laterStatus]
    rw [← combineVisitStatus_assoc]

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (middle : List Selection) (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse : ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
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
        (executableFieldSelections prefixFields
          ++ middle
          ++ executableFieldSelections [later]) := by
  intro outputFields hfresh
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let flatFields :=
    collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues parentType source
        rawBlock)
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
  have hrawPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source rawBlock (.object outputFields) =
      (.object (outputFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_prefix_fresh schema resolvers variableValues
          (completionDepth + 1) parentType source rawBlock outputFields []
          resultFields status hfresh hrawEmpty
  have hflatEmpty :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields)
        (.object []) =
      (.object resultFields, status) := by
    have hflat :=
      VisitSubfieldsFlatCollects_group_duplicate_field_middle_of_freshPrefixes
        schema resolvers variableValues completionDepth parentType source
        responseName prefixFields later middle hprefixNonempty
        hprefixResponse hlaterResponse hlaterLookup hnotMiddle hmiddle
    unfold VisitSubfieldsFlatCollects at hflat
    dsimp [rawBlock, flatFields] at hflat
    rw [← hflat]
    exact hrawEmpty
  have hflatPrefix :
      visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections flatFields)
        (.object outputFields) =
      (.object (outputFields ++ resultFields), status) :=
    by
      simpa using
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues (completionDepth + 1) parentType source flatFields
          outputFields [] resultFields status
          (by
            intro field hmem
            exact hfresh field
              (show
                field ∈
                  collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source
                      (executableFieldSelections prefixFields ++ middle ++
                        executableFieldSelections [later])) from
                by
                  change
                    field ∈
                      collectedExecutableFields
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source rawBlock)
                  exact hmem))
          hflatEmpty
  unfold VisitSubfieldsFlatCollects
  change
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source rawBlock (.object outputFields) =
    visitSubfields schema resolvers variableValues (completionDepth + 1)
      parentType source (executableFieldSelections flatFields)
        (.object outputFields)
  rw [hrawPrefix, hflatPrefix]

theorem visitSubfields_duplicate_field_middle_append_eq_collected_middle
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle suffix : List Selection)
    (prefixFields : List (Name × ResponseValue))
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    (hfresh
      : ∀ field,
          field
            ∈ collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source
                  (executableFieldSelections [first]
                    ++ middle
                    ++ executableFieldSelections [later]))
          -> field.responseName ∉ prefixFields.map Prod.fst)
    : visitSubfields schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections [first]
            ++ middle
            ++ executableFieldSelections [later])
          ++ suffix)
        (.object prefixFields)
      = visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)
          (.object prefixFields) := by
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections [first, later] ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle))
  have hblock :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock
        (.object prefixFields) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
      resolvers variableValues completionDepth parentType source first later
      middle hsameResponse hlaterLookup hnotMiddle hmiddle prefixFields hfresh
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock)) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source first later middle
        hsameResponse hnotMiddle
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
    (hprefixResponse : ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
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
      : ∀ field,
          field
            ∈ collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source
                  (executableFieldSelections prefixFields
                    ++ middle
                    ++ executableFieldSelections [later]))
          -> field.responseName ∉ outputFields.map Prod.fst)
    : visitSubfields schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections prefixFields
            ++ middle
            ++ executableFieldSelections [later])
          ++ suffix)
        (.object outputFields)
      = visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections (prefixFields ++ [later])
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix)
          (.object outputFields) := by
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections (prefixFields ++ [later]) ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            middle))
  have hblock :
      VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source rawBlock
        (.object outputFields) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_after_same_response_prefix
      schema resolvers variableValues completionDepth parentType source
      responseName prefixFields later middle hprefixNonempty hprefixResponse
      hlaterResponse hlaterLookup hnotMiddle hmiddle outputFields hfresh
  have hnormalizedBlock :
      executableFieldSelections
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock)) =
        normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    exact
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
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
    (first later : ExecutableField) (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    : GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections [first]
            ++ middle
            ++ executableFieldSelections [later])
          ++ suffix)
      = GraphQL.Execution.collectFields schema variableValues parentType source
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix) := by
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections [first, later] ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
  have hblock :
      GraphQL.Execution.collectFields schema variableValues parentType source
          rawBlock =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    rw [←
      executableFieldSelections_collectedExecutableFields_collectFields_duplicate_around_disjoint
        schema variableValues parentType source first later middle
        hsameResponse hnotMiddle]
    exact
      (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later])).symm
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
    (hprefixResponse : ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
    (hnotMiddle
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    : GraphQL.Execution.collectFields schema variableValues parentType source
        ((executableFieldSelections prefixFields
            ++ middle
            ++ executableFieldSelections [later])
          ++ suffix)
      = GraphQL.Execution.collectFields schema variableValues parentType source
          ((executableFieldSelections (prefixFields ++ [later])
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix) := by
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let normalizedBlock :=
    executableFieldSelections (prefixFields ++ [later]) ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))
  have hblock :
      GraphQL.Execution.collectFields schema variableValues parentType source
          rawBlock =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalizedBlock := by
    dsimp [rawBlock, normalizedBlock]
    rw [←
      executableFieldSelections_collectedExecutableFields_collectFields_group_duplicate_around_disjoint
        schema variableValues parentType source responseName prefixFields later
        middle hprefixNonempty hprefixResponse hlaterResponse hnotMiddle]
    exact
      (collectFields_executableFieldSelections_collectedExecutableFields_collectFields
        schema variableValues parentType source
        (executableFieldSelections prefixFields ++ middle ++
          executableFieldSelections [later])).symm
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

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_normalized
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (first later : ExecutableField)
    (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    (hnormalized
      : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType source
          ((executableFieldSelections [first, later]
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix))
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections [first]
            ++ middle
            ++ executableFieldSelections [later])
          ++ suffix) := by
  intro prefixFields hfresh
  let rawBlock :=
    executableFieldSelections [first] ++ middle ++
      executableFieldSelections [later]
  let normalized :=
    (executableFieldSelections [first, later] ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))) ++ suffix
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (rawBlock ++ suffix) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalized := by
    dsimp [rawBlock, normalized]
    exact
      collectFields_duplicate_field_middle_append_eq_collected_middle schema
        variableValues parentType source first later middle suffix
        hsameResponse hnotMiddle
  have hblockFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) ->
        field.responseName ∉ prefixFields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    have hfieldRaw :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix)) := by
      exact
        (collectedExecutableFields_mem_mergeExecutableGroups
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rawBlock)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source suffix) field).mpr (Or.inl hfield)
    have hfieldWhole :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (rawBlock ++ suffix)) := by
      rw [GraphQL.NormalForm.collectFields_append schema variableValues
        parentType source rawBlock suffix]
      exact hfieldRaw
    simpa [rawBlock] using hfieldWhole
  change
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source (rawBlock ++ suffix)
      (.object prefixFields)
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_duplicate_field_middle_append_eq_collected_middle schema
    resolvers variableValues completionDepth parentType source first later
    middle suffix prefixFields hsameResponse hlaterLookup hnotMiddle hmiddle
    hblockFresh]
  rw [hcollect]
  exact hnormalized prefixFields
    (by
      intro field hfield
      have hfieldRaw :
          field ∈
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (rawBlock ++ suffix)) := by
        rw [hcollect]
        exact hfield
      apply hfresh field
      simpa [rawBlock, List.append_assoc] using hfieldRaw)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_group_duplicate_field_middle_append_of_normalized
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (prefixFields : List ExecutableField) (later : ExecutableField)
    (middle suffix : List Selection) (hprefixNonempty : prefixFields ≠ [])
    (hprefixResponse : ∀ field, field ∈ prefixFields -> field.responseName = responseName)
    (hlaterResponse : later.responseName = responseName)
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
          ((executableFieldSelections (prefixFields ++ [later])
              ++ executableFieldSelections
                  (collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues
                      parentType source middle)))
            ++ suffix))
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        ((executableFieldSelections prefixFields
            ++ middle
            ++ executableFieldSelections [later])
          ++ suffix) := by
  intro outputFields hfresh
  let rawBlock :=
    executableFieldSelections prefixFields ++ middle ++
      executableFieldSelections [later]
  let normalized :=
    (executableFieldSelections (prefixFields ++ [later]) ++
      executableFieldSelections
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType
            source middle))) ++ suffix
  have hcollect :
      GraphQL.Execution.collectFields schema variableValues parentType source
          (rawBlock ++ suffix) =
        GraphQL.Execution.collectFields schema variableValues parentType source
          normalized := by
    dsimp [rawBlock, normalized]
    exact
      collectFields_group_duplicate_field_middle_append_eq_collected_middle
        schema variableValues parentType source responseName prefixFields later
        middle suffix hprefixNonempty hprefixResponse hlaterResponse hnotMiddle
  have hblockFresh :
      ∀ field,
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source rawBlock) ->
        field.responseName ∉ outputFields.map Prod.fst := by
    intro field hfield
    apply hfresh field
    have hfieldRaw :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.mergeExecutableGroups
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rawBlock)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source suffix)) := by
      exact
        (collectedExecutableFields_mem_mergeExecutableGroups
          (GraphQL.Execution.collectFields schema variableValues parentType
            source rawBlock)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source suffix) field).mpr (Or.inl hfield)
    have hfieldWhole :
        field ∈
          collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (rawBlock ++ suffix)) := by
      rw [GraphQL.NormalForm.collectFields_append schema variableValues
        parentType source rawBlock suffix]
      exact hfieldRaw
    simpa [rawBlock] using hfieldWhole
  change
    VisitSubfieldsFlatCollects schema resolvers variableValues
      (completionDepth + 1) parentType source (rawBlock ++ suffix)
      (.object outputFields)
  unfold VisitSubfieldsFlatCollects
  rw [visitSubfields_group_duplicate_field_middle_append_eq_collected_middle
    schema resolvers variableValues completionDepth parentType source
    responseName prefixFields later middle suffix outputFields hprefixNonempty
    hprefixResponse hlaterResponse hlaterLookup hnotMiddle hmiddle
    hblockFresh]
  rw [hcollect]
  exact hnormalized outputFields
    (by
      intro field hfield
      have hfieldRaw :
          field ∈
            collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (rawBlock ++ suffix)) := by
        rw [hcollect]
        exact hfield
      apply hfresh field
      simpa [rawBlock, List.append_assoc] using hfieldRaw)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_of_allOutputs
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (first later : ExecutableField) (middle : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hmiddle
      : VisitSubfieldsFlatCollectsAllOutputs schema resolvers variableValues
          (completionDepth + 1) parentType source middle)
    : VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]) :=
  VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
    resolvers variableValues completionDepth parentType source first later
    middle hsameResponse hlaterLookup hnotMiddle
    (VisitSubfieldsFlatCollectsFreshPrefixes.of_allOutputs schema resolvers
      variableValues (completionDepth + 1) parentType source middle hmiddle)

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (first later : ExecutableField)
    (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later]))
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
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]
          ++ suffix) := by
  have hblock :
      VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections [first] ++ middle ++
          executableFieldSelections [later]) :=
    VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle schema
      resolvers variableValues completionDepth parentType source first later
      middle hsameResponse hlaterLookup hnotMiddle hmiddle
  simpa [List.append_assoc] using
    VisitSubfieldsFlatCollectsFreshPrefixes_append_of_namesDisjoint schema
      resolvers variableValues (completionDepth + 1) parentType source
      (executableFieldSelections [first] ++ middle ++
        executableFieldSelections [later])
      suffix hdisjoint hblock hsuffix

theorem VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_headDisjointTrees
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (first later : ExecutableField)
    (middle suffix : List Selection)
    (hsameResponse : later.responseName = first.responseName)
    (hlaterLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType later.fieldName = some fieldDefinition)
    (hnotMiddle
      : first.responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source middle).map
            Prod.fst)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections [first]
              ++ middle
              ++ executableFieldSelections [later]))
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
        (executableFieldSelections [first]
          ++ middle
          ++ executableFieldSelections [later]
          ++ suffix) :=
  VisitSubfieldsFlatCollectsFreshPrefixes_duplicate_field_middle_append_of_namesDisjoint
    schema resolvers variableValues completionDepth parentType source first later
    middle suffix hsameResponse hlaterLookup hnotMiddle hdisjoint
    (VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source middle
      hmiddle)
    (VisitSubfieldsFlatCollectsFreshPrefixes_of_headDisjointTree schema
      resolvers variableValues (completionDepth + 1) parentType source suffix
      hsuffix)

end ExecutionUngrouped
end Algorithms

end GraphQL
