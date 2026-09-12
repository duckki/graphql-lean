import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.TwoField

/-!
Group-list proof helpers for the final ungrouped execution equivalence theorem.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

local instance : Coe (ResponseValue × VisitStatus) ResponseValue where
  coe := Prod.fst

theorem combineVisitStatus_left_rotate (left middle right : VisitStatus)
    : combineVisitStatus left (combineVisitStatus middle right)
      = combineVisitStatus middle (combineVisitStatus left right) := by
  rw [← combineVisitStatus_assoc,
    combineVisitStatus_comm left middle,
    combineVisitStatus_assoc]

theorem combineVisitStatus_error_one_left_rotate (middle right : VisitStatus)
    : combineVisitStatus (.error 1 : VisitStatus) (combineVisitStatus middle right)
      = combineVisitStatus middle (combineVisitStatus (.error 1 : VisitStatus) right) :=
  combineVisitStatus_left_rotate (.error 1 : VisitStatus) middle right

theorem lookupResponseField?_append_of_not_mem
    (responseName : Name) (prefixFields suffix : List (Name × ResponseValue))
    : responseName ∉ prefixFields.map Prod.fst
      -> lookupResponseField? responseName (prefixFields ++ suffix)
          = lookupResponseField? responseName suffix := by
  induction prefixFields with
  | nil =>
      intro _hfresh
      simp
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, response⟩
      intro hfresh
      have hhead : (fieldResponseName == responseName) = false := by
        cases h : fieldResponseName == responseName
        · exact rfl
        · exfalso
          exact hfresh (by simp [beq_iff_eq.mp h])
      have hrest : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hfresh (by simp [hmem])
      simp [lookupResponseField?, hhead, ih hrest]

theorem responseObjectField?_object_append_of_not_mem
    (responseName : Name) (prefixFields suffix : List (Name × ResponseValue))
    : responseName ∉ prefixFields.map Prod.fst
      -> responseObjectField? responseName (.object (prefixFields ++ suffix))
          = responseObjectField? responseName (.object suffix) := by
  intro hfresh
  simp [responseObjectField?,
    lookupResponseField?_append_of_not_mem responseName prefixFields suffix hfresh]

theorem mergeResponseField_append_of_not_mem
    (responseName : Name) (incoming : ResponseValue)
    (prefixFields suffix : List (Name × ResponseValue))
    : responseName ∉ prefixFields.map Prod.fst
      -> mergeResponseField responseName incoming (prefixFields ++ suffix)
          = prefixFields ++ mergeResponseField responseName incoming suffix := by
  induction prefixFields with
  | nil =>
      intro _hfresh
      simp
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, existing⟩
      intro hfresh
      have hhead : (fieldResponseName == responseName) = false := by
        cases h : fieldResponseName == responseName
        · exact rfl
        · exfalso
          exact hfresh (by simp [beq_iff_eq.mp h])
      have hrest : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hfresh (by simp [hmem])
      simp [mergeResponseField, hhead, ih hrest]

theorem mergeResponseField_self_key_mem (responseName : Name) (incoming : ResponseValue)
    : ∀ fields : List (Name × ResponseValue),
        responseName ∈ (mergeResponseField responseName incoming fields).map Prod.fst
  | [] => by
      simp [mergeResponseField]
  | (fieldName, response) :: rest => by
      by_cases h : fieldName == responseName
      · simp [mergeResponseField, beq_iff_eq.mp h]
      · simp [mergeResponseField, h,
          mergeResponseField_self_key_mem responseName incoming rest]

theorem mergeResponseField_preserves_key_mem
    (target responseName : Name) (incoming : ResponseValue)
    : ∀ fields : List (Name × ResponseValue),
        target ∈ fields.map Prod.fst
        -> target ∈ (mergeResponseField responseName incoming fields).map Prod.fst
  | [], hmem => by
      simp at hmem
  | (fieldName, response) :: rest, hmem => by
      by_cases h : fieldName == responseName
      · simp [mergeResponseField, h] at hmem ⊢
        exact hmem
      · simp [mergeResponseField, h] at hmem ⊢
        rcases hmem with hhead | htail
        · exact Or.inl hhead
        · rcases htail with ⟨tailResponse, htailPair⟩
          rcases
            List.mem_map.mp
              (mergeResponseField_preserves_key_mem target responseName incoming
                rest
                (List.mem_map.mpr
                  ⟨(target, tailResponse), htailPair, rfl⟩))
          with ⟨mergedPair, hmergedPair, hmergedName⟩
          rcases mergedPair with ⟨mergedName, mergedResponse⟩
          dsimp at hmergedName
          subst mergedName
          exact Or.inr ⟨mergedResponse, hmergedPair⟩

mutual
  theorem visitSelection_preserves_object_key_mem
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (target : Name)
      : ∀ (selection : Selection) (fields : List (Name × ResponseValue)),
          target ∈ fields.map Prod.fst
          -> ∃ outputFields,
              (visitSelection schema resolvers variableValues depth parentType source
                  selection (.object fields)).fst
                = .object outputFields
              ∧ target ∈ outputFields.map Prod.fst := by
    intro selection fields hmem
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases depth with
          | zero =>
              cases hprevious : responseObjectField? responseName (.object fields) with
              | none =>
                  refine ⟨
                    mergeResponseField responseName .null fields,
                    ?_,
                    mergeResponseField_preserves_key_mem target responseName
                      .null fields hmem
                  ⟩
                  simp [visitSelection, hallowed, hprevious,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    resultValueOrNull, outOfFuel]
              | some previous =>
                  refine ⟨
                    mergeResponseField responseName previous fields,
                    ?_,
                    mergeResponseField_preserves_key_mem target responseName
                      previous fields hmem
                  ⟩
                  simp [visitSelection, hallowed, hprevious,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    resultValueOrNull]
          | succ depth' =>
              let previous? :=
                responseObjectField? responseName (.object fields)
              let field :=
                executableField fieldName arguments
                  selectionSet
              let fieldResult :=
                executeFieldVisitResult schema resolvers variableValues depth'
                  parentType source previous? field
              let incoming := resultValueOrNull fieldResult
              cases hprevious : responseObjectField? responseName (.object fields) with
              | none =>
                  refine ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                  · rw [visitSelection_field_allowed_succ schema resolvers
                      variableValues depth' parentType source responseName
                      fieldName arguments directives selectionSet
                      (.object fields) hallowed]
                    simp [mergeResponseFieldResult,
                      mergeResponseFieldIntoObject, incoming, fieldResult,
                      previous?, field, executeFieldVisitResult, hprevious]
                  · exact mergeResponseField_preserves_key_mem target
                      responseName incoming fields hmem
              | some previous =>
                  cases previous with
                  | null =>
                      have hlookupRaw :
                          lookupResponseField? responseName fields =
                            some .null := by
                        simpa [responseObjectField?] using hprevious
                      have hincoming :
                          resultValueOrNull
                            (executeField schema resolvers variableValues
                              depth' parentType source (some .null)
                              (executableField fieldName arguments selectionSet)) =
                            .null := by
                        cases hlookup :
                            schema.lookupField parentType fieldName <;>
                          simp [executeField, executableField, hlookup,
                            reusablePreviousValue?_null, resultValueOrNull]
                      have hmerge :
                          mergeResponseField responseName
                              (resultValueOrNull
                                (executeField schema resolvers variableValues
                                  depth' parentType source (some .null)
                                  (executableField fieldName arguments selectionSet)))
                              fields =
                            fields := by
                        rw [hincoming]
                        exact mergeResponseField_null_of_lookup_null
                          responseName fields hlookupRaw
                      refine ⟨fields, ?_, hmem⟩
                      rw [visitSelection_field_allowed_succ schema resolvers
                        variableValues depth' parentType source responseName
                        fieldName arguments directives selectionSet
                        (.object fields) hallowed]
                      simp [hprevious, mergeResponseFieldResult, mergeResponseFieldIntoObject, hmerge]
                  | scalar value =>
                      refine ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                      · rw [visitSelection_field_allowed_succ schema resolvers
                          variableValues depth' parentType source responseName
                          fieldName arguments directives selectionSet
                          (.object fields) hallowed]
                        simp [mergeResponseFieldResult,
                          mergeResponseFieldIntoObject, incoming, fieldResult,
                          previous?, field, executeFieldVisitResult, hprevious]
                      · exact mergeResponseField_preserves_key_mem target
                          responseName incoming fields hmem
                  | object objectFields =>
                      refine ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                      · rw [visitSelection_field_allowed_succ schema resolvers
                          variableValues depth' parentType source responseName
                          fieldName arguments directives selectionSet
                          (.object fields) hallowed]
                        simp [mergeResponseFieldResult,
                          mergeResponseFieldIntoObject, incoming, fieldResult,
                          previous?, field, executeFieldVisitResult, hprevious]
                      · exact mergeResponseField_preserves_key_mem target
                          responseName incoming fields hmem
                  | list values =>
                      refine ⟨mergeResponseField responseName incoming fields, ?_, ?_⟩
                      · rw [visitSelection_field_allowed_succ schema resolvers
                          variableValues depth' parentType source responseName
                          fieldName arguments directives selectionSet
                          (.object fields) hallowed]
                        simp [mergeResponseFieldResult,
                          mergeResponseFieldIntoObject, incoming, fieldResult,
                          previous?, field, executeFieldVisitResult, hprevious]
                      · exact mergeResponseField_preserves_key_mem target
                          responseName incoming fields hmem
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives with
            | false => rfl
            | true => exact False.elim (hallowed h)
          exact ⟨
            fields,
            by
              unfold visitSelection
              simp [hblocked],
            hmem
          ⟩
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives
        · cases typeCondition with
          | none =>
              rcases
                visitSubfields_preserves_object_key_mem schema resolvers
                  variableValues depth parentType source target selectionSet
                  fields hmem
              with ⟨outputFields, hvisit, hkey⟩
              exact ⟨
                outputFields,
                by
                  simp [visitSelection, hallowed, hvisit],
                hkey
              ⟩
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · rcases
                  visitSubfields_preserves_object_key_mem schema resolvers
                    variableValues depth parentType source target selectionSet
                    fields hmem
                with ⟨outputFields, hvisit, hkey⟩
                exact ⟨
                  outputFields,
                  by
                    simp [visitSelection, hallowed, happly, hvisit],
                  hkey
                ⟩
              · exact ⟨
                  fields,
                  by
                    simp [visitSelection, hallowed, happly],
                  hmem
                ⟩
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives with
            | false => rfl
            | true => exact False.elim (hallowed h)
          cases typeCondition with
          | none =>
              exact ⟨
                fields,
                by
                  unfold visitSelection
                  simp [hblocked],
                hmem
              ⟩
          | some typeCondition =>
              exact ⟨
                fields,
                by
                  unfold visitSelection
                  simp [hblocked],
                hmem
              ⟩

  theorem visitSubfields_preserves_object_key_mem
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (target : Name)
      : ∀ (selectionSet : List Selection) (fields : List (Name × ResponseValue)),
          target ∈ fields.map Prod.fst
          -> ∃ outputFields,
              (visitSubfields schema resolvers variableValues depth parentType source
                  selectionSet (.object fields)).fst
                = .object outputFields
              ∧ target ∈ outputFields.map Prod.fst := by
    intro selectionSet fields hmem
    cases selectionSet with
    | nil =>
        exact ⟨fields, by simp [visitSubfields], hmem⟩
    | cons selection rest =>
        rcases
          visitSelection_preserves_object_key_mem schema resolvers
            variableValues depth parentType source target selection fields hmem
        with ⟨headFields, hhead, hheadMem⟩
        rcases
          visitSubfields_preserves_object_key_mem schema resolvers
            variableValues depth parentType source target rest headFields
            hheadMem
        with ⟨tailFields, htail, htailMem⟩
        exact ⟨
          tailFields,
          by
            simp [visitSubfields]
            rw [hhead]
            simpa using htail,
          htailMem
        ⟩
end

theorem executeField_object_append_fresh_eq
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType responseName : Name) (source : ResolverValue ObjectIdentity)
    (field : ExecutableField)
    (prefixFields suffix : List (Name × ResponseValue))
    : responseName ∉ prefixFields.map Prod.fst
      -> executeField schema resolvers variableValues depth parentType source
            (responseObjectField? responseName (.object (prefixFields ++ suffix)))
            field
          = executeField schema resolvers variableValues depth parentType source
              (responseObjectField? responseName (.object suffix)) field := by
  intro hfresh
  rw [responseObjectField?_object_append_of_not_mem responseName
    prefixFields suffix hfresh]

theorem visitSelection_executableField_prefix_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name) (field : ExecutableField)
    (prefixFields suffix result : List (Name × ResponseValue))
    (status : VisitStatus)
    : responseName ∉ prefixFields.map Prod.fst
      -> visitSelection schema resolvers variableValues depth parentType source
            (executableFieldSelection responseName field) (.object suffix)
          = (.object result, status)
      -> visitSelection schema resolvers variableValues depth parentType source
            (executableFieldSelection responseName field)
            (.object (prefixFields ++ suffix))
          = (.object (prefixFields ++ result), status) := by
  intro hfresh hvisit
  cases field with
  | mk fieldName arguments selectionSet =>
      have hfreshName : responseName ∉ prefixFields.map Prod.fst := hfresh
      cases depth with
      | zero =>
          have happend :
              responseObjectField? responseName
                  (.object (prefixFields ++ suffix)) =
                responseObjectField? responseName (.object suffix) :=
            responseObjectField?_object_append_of_not_mem responseName
              prefixFields suffix hfreshName
          cases hprevious : responseObjectField? responseName (.object suffix) with
          | none =>
              simp [visitSelection, executableFieldSelection,
                selectionDirectivesAllowBool_empty, happend, hprevious,
                mergeResponseFieldResult, mergeResponseFieldIntoObject,
                resultValueOrNull] at hvisit ⊢
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simpa [resultValueOrNull, outOfFuel] using
                mergeResponseField_append_of_not_mem responseName .null
                  prefixFields suffix hfreshName
          | some previous =>
              simp [visitSelection, executableFieldSelection,
                selectionDirectivesAllowBool_empty, happend, hprevious,
                mergeResponseFieldResult, mergeResponseFieldIntoObject,
                resultValueOrNull] at hvisit ⊢
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simpa using
                mergeResponseField_append_of_not_mem responseName previous
                  prefixFields suffix hfreshName
      | succ depth' =>
          have happend :
              responseObjectField? responseName
                  (.object (prefixFields ++ suffix)) =
                responseObjectField? responseName (.object suffix) :=
            responseObjectField?_object_append_of_not_mem responseName
              prefixFields suffix hfreshName
          cases hprevious : responseObjectField? responseName (.object suffix) with
          | none =>
              simp [visitSelection, executableFieldSelection, executableField,
                selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                mergeResponseFieldIntoObject, hprevious] at hvisit
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simp [visitSelection, executableFieldSelection, executableField,
                selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                mergeResponseFieldIntoObject, happend, hprevious]
              simpa [hprevious] using
                mergeResponseField_append_of_not_mem responseName
                  (resultValueOrNull
                    (executeField schema resolvers variableValues depth' parentType source
                      (responseObjectField? responseName (.object suffix))
                      { fieldName := fieldName
                        arguments := arguments
                        selectionSet := selectionSet }))
                  prefixFields suffix hfreshName
          | some previous =>
              cases previous with
              | null =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    happend, hprevious]
                  simpa [hprevious, executableField] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          parentType source
                          (responseObjectField? responseName (.object suffix))
                          (executableField fieldName
                            arguments selectionSet)))
                      prefixFields suffix hfreshName
              | scalar value =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection, executableField,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, happend, hprevious]
                  simpa [hprevious] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          parentType source
                          (responseObjectField? responseName (.object suffix))
                          { fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet }))
                      prefixFields suffix hfreshName
              | object objectFields =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection, executableField,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, happend, hprevious]
                  simpa [hprevious] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          parentType source
                          (responseObjectField? responseName (.object suffix))
                          { fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet }))
                      prefixFields suffix hfreshName
              | list values =>
                  simp [visitSelection, executableFieldSelection,
                    executableField, selectionDirectivesAllowBool_empty,
                    mergeResponseFieldResult, mergeResponseFieldIntoObject,
                    hprevious] at hvisit
                  rcases hvisit with ⟨hresult, hstatus⟩
                  subst result
                  subst status
                  simp [visitSelection, executableFieldSelection, executableField,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, happend, hprevious]
                  simpa [hprevious] using
                    mergeResponseField_append_of_not_mem responseName
                      (resultValueOrNull
                        (executeField schema resolvers variableValues depth'
                          parentType source
                          (responseObjectField? responseName (.object suffix))
                          { fieldName := fieldName
                            arguments := arguments
                            selectionSet := selectionSet }))
                      prefixFields suffix hfreshName

theorem visitSubfields_executableFieldSelections_prefix_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name)
    : ∀ (fields : List ExecutableField)
        (prefixFields suffix result : List (Name × ResponseValue))
        (status : VisitStatus),
        responseName ∉ prefixFields.map Prod.fst
        -> visitSubfields schema resolvers variableValues depth parentType source
              (executableFieldSelections responseName fields) (.object suffix)
            = (.object result, status)
        -> visitSubfields schema resolvers variableValues depth parentType source
              (executableFieldSelections responseName fields)
              (.object (prefixFields ++ suffix))
            = (.object (prefixFields ++ result), status)
  | [], prefixFields, suffix, result, status, _hfresh, hvisit => by
      simp [executableFieldSelections, visitSubfields, visitOk] at hvisit
      rcases hvisit with ⟨hresult, hstatus⟩
      subst result
      subst status
      simp [executableFieldSelections, visitSubfields, visitOk]
  | field :: rest, prefixFields, suffix, result, status, hfresh, hvisit => by
      have hfreshHead :
          responseName ∉ prefixFields.map Prod.fst := hfresh
      have hfreshRest :
          responseName ∉ prefixFields.map Prod.fst := hfresh
      rcases
        visitSelection_preserves_object schema resolvers variableValues depth
          parentType source (executableFieldSelection responseName field) suffix
        with ⟨headFields, hheadFst⟩
      let headStatus :=
        (visitSelection schema resolvers variableValues depth parentType source
          (executableFieldSelection responseName field) (.object suffix)).snd
      have hhead :
          visitSelection schema resolvers variableValues depth parentType source
            (executableFieldSelection responseName field) (.object suffix) =
          (.object headFields, headStatus) := by
        exact Prod.ext hheadFst rfl
      let tail :=
        visitSubfields schema resolvers variableValues depth parentType source
          (executableFieldSelections responseName rest) (.object headFields)
      have hvisitTail :
          tail.fst = .object result ∧
            combineVisitStatus headStatus tail.snd = status := by
        simp [executableFieldSelections, visitSubfields] at hvisit
        rw [hhead] at hvisit
        simpa [tail, executableFieldSelections] using hvisit
      have htail :
          visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections responseName rest) (.object headFields) =
          (.object result, tail.snd) := by
        exact Prod.ext hvisitTail.1 rfl
      have hheadPrefix :
          visitSelection schema resolvers variableValues depth parentType source
            (executableFieldSelection responseName field)
            (.object (prefixFields ++ suffix)) =
          (.object (prefixFields ++ headFields), headStatus) :=
        visitSelection_executableField_prefix_fresh schema resolvers
          variableValues depth parentType source responseName field prefixFields suffix
          headFields headStatus hfreshHead hhead
      have htailPrefix :
          visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections responseName rest)
            (.object (prefixFields ++ headFields)) =
          (.object (prefixFields ++ result), tail.snd) :=
        visitSubfields_executableFieldSelections_prefix_fresh schema resolvers
          variableValues depth parentType source responseName rest prefixFields headFields
          result tail.snd hfreshRest htail
      simp [executableFieldSelections, visitSubfields]
      rw [hheadPrefix]
      change
        (visitSubfields schema resolvers variableValues depth parentType source
            (executableFieldSelections responseName rest)
            (.object (prefixFields ++ headFields))).fst =
            .object (prefixFields ++ result) ∧
          combineVisitStatus headStatus
            (visitSubfields schema resolvers variableValues depth parentType
              source (executableFieldSelections responseName rest)
              (.object (prefixFields ++ headFields))).snd =
            status
      constructor
      · rw [htailPrefix]
      · rw [htailPrefix]
        exact hvisitTail.2

theorem visitSelection_field_prefix_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (prefixFields suffix result : List (Name × ResponseValue))
    (status : VisitStatus)
    : (selectionDirectivesAllowBool variableValues directives = true
        -> responseName ∉ prefixFields.map Prod.fst)
      -> visitSelection schema resolvers variableValues depth parentType source
            (.field responseName fieldName arguments directives selectionSet)
            (.object suffix)
          = (.object result, status)
      -> visitSelection schema resolvers variableValues depth parentType source
            (.field responseName fieldName arguments directives selectionSet)
            (.object (prefixFields ++ suffix))
          = (.object (prefixFields ++ result), status) := by
  intro hfreshIfAllowed hvisit
  by_cases hallowed :
      selectionDirectivesAllowBool variableValues directives = true
  · have hfreshName := hfreshIfAllowed hallowed
    cases depth with
    | zero =>
        have happend :
            responseObjectField? responseName
                (.object (prefixFields ++ suffix)) =
              responseObjectField? responseName (.object suffix) :=
          responseObjectField?_object_append_of_not_mem responseName
            prefixFields suffix hfreshName
        cases hprevious : responseObjectField? responseName (.object suffix) with
        | none =>
            simp [visitSelection, hallowed, happend, hprevious,
              mergeResponseFieldResult, mergeResponseFieldIntoObject,
              resultValueOrNull] at hvisit ⊢
            rcases hvisit with ⟨hresult, hstatus⟩
            subst result
            subst status
            simpa [resultValueOrNull, outOfFuel] using
              mergeResponseField_append_of_not_mem responseName .null
                prefixFields suffix hfreshName
        | some previous =>
            simp [visitSelection, hallowed, happend, hprevious,
              mergeResponseFieldResult, mergeResponseFieldIntoObject,
              resultValueOrNull] at hvisit ⊢
            rcases hvisit with ⟨hresult, hstatus⟩
            subst result
            subst status
            simpa using
              mergeResponseField_append_of_not_mem responseName previous
                prefixFields suffix hfreshName
    | succ depth' =>
        have happend :
            responseObjectField? responseName
                (.object (prefixFields ++ suffix)) =
              responseObjectField? responseName (.object suffix) :=
          responseObjectField?_object_append_of_not_mem responseName
            prefixFields suffix hfreshName
        cases hprevious : responseObjectField? responseName (.object suffix) with
        | none =>
            simp [visitSelection, hallowed, mergeResponseFieldResult,
              mergeResponseFieldIntoObject, hprevious] at hvisit
            rcases hvisit with ⟨hresult, hstatus⟩
            subst result
            subst status
            simp [visitSelection, hallowed, mergeResponseFieldResult,
              mergeResponseFieldIntoObject, happend, hprevious]
            simpa [hprevious, executableField] using
              mergeResponseField_append_of_not_mem responseName
                (resultValueOrNull
                  (executeField schema resolvers variableValues depth' parentType source
                    (responseObjectField? responseName (.object suffix))
                    { fieldName := fieldName
                      arguments := arguments
                      selectionSet := selectionSet }))
                prefixFields suffix hfreshName
        | some previous =>
            cases previous with
            | null =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious, executableField] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        parentType source
                        (responseObjectField? responseName (.object suffix))
                        { fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
            | scalar value =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious, executableField] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        parentType source
                        (responseObjectField? responseName (.object suffix))
                        { fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
            | object objectFields =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious, executableField] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        parentType source
                        (responseObjectField? responseName (.object suffix))
                        { fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
            | list values =>
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, hprevious] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, mergeResponseFieldResult,
                  mergeResponseFieldIntoObject, happend, hprevious]
                simpa [hprevious, executableField] using
                  mergeResponseField_append_of_not_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues depth'
                        parentType source
                        (responseObjectField? responseName (.object suffix))
                        { fieldName := fieldName
                          arguments := arguments
                          selectionSet := selectionSet }))
                    prefixFields suffix hfreshName
  · have hskipped :
        selectionDirectivesAllowBool variableValues directives = false := by
      cases hdir :
          selectionDirectivesAllowBool variableValues directives <;>
        simp [hdir] at hallowed ⊢
    have hnotAllowed :
        ¬ selectionDirectivesAllowBool variableValues directives := by
      intro hallowed
      simp [hskipped] at hallowed
    unfold visitSelection at hvisit ⊢
    simp [hnotAllowed] at hvisit ⊢
    rcases hvisit with ⟨hresult, hstatus⟩
    subst result
    subst status
    simp

mutual
  theorem visitSelection_prefix_fresh
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selection : Selection)
          (prefixFields suffix result : List (Name × ResponseValue))
          (status : VisitStatus),
          (∀ responseName,
            responseName
              ∈ (GraphQL.Execution.collectSelection schema variableValues
                  parentType source selection).map
                  Prod.fst
            -> responseName ∉ prefixFields.map Prod.fst)
          -> visitSelection schema resolvers variableValues depth parentType source
                selection (.object suffix)
              = (.object result, status)
          -> visitSelection schema resolvers variableValues depth parentType source
                selection (.object (prefixFields ++ suffix))
              = (.object (prefixFields ++ result), status) := by
    intro selection prefixFields suffix result status hfresh hvisit
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        apply visitSelection_field_prefix_fresh schema resolvers variableValues
          depth parentType source responseName fieldName arguments directives
          selectionSet prefixFields suffix result status
        · intro hallowed
          apply hfresh responseName
          simp [GraphQL.Execution.collectSelection, hallowed]
        · exact hvisit
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallowed :
                selectionDirectivesAllowBool variableValues directives
            · have hbodyFresh :
                  ∀ responseName,
                    responseName ∈
                      (GraphQL.Execution.collectFields schema variableValues
                        parentType source selectionSet).map Prod.fst ->
                    responseName ∉ prefixFields.map Prod.fst := by
                intro responseName hmem
                apply hfresh responseName
                simpa [GraphQL.Execution.collectSelection, hallowed] using hmem
              have hbodyVisit :
                  visitSubfields schema resolvers variableValues depth parentType
                    source selectionSet (.object suffix) =
                  (.object result, status) := by
                simpa [visitSelection, hallowed] using hvisit
              have hprefix :=
                visitSubfields_prefix_fresh schema resolvers variableValues
                  depth parentType source selectionSet prefixFields suffix result
                  status hbodyFresh hbodyVisit
              simpa [visitSelection, hallowed] using hprefix
            · simp [visitSelection, hallowed] at hvisit
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simp [visitSelection, hallowed]
        | some typeCondition =>
            by_cases hallowed :
                selectionDirectivesAllowBool variableValues directives
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition
              · have hbodyFresh :
                    ∀ responseName,
                      responseName ∈
                        (GraphQL.Execution.collectFields schema variableValues
                          parentType source selectionSet).map Prod.fst ->
                      responseName ∉ prefixFields.map Prod.fst := by
                  intro responseName hmem
                  apply hfresh responseName
                  simpa [GraphQL.Execution.collectSelection, hallowed, happly]
                    using hmem
                have hbodyVisit :
                    visitSubfields schema resolvers variableValues depth
                      parentType source selectionSet (.object suffix) =
                    (.object result, status) := by
                  simpa [visitSelection, hallowed, happly] using hvisit
                have hprefix :=
                  visitSubfields_prefix_fresh schema resolvers variableValues
                    depth parentType source selectionSet prefixFields suffix
                    result status hbodyFresh hbodyVisit
                simpa [visitSelection, hallowed, happly] using hprefix
              · simp [visitSelection, hallowed, happly] at hvisit
                rcases hvisit with ⟨hresult, hstatus⟩
                subst result
                subst status
                simp [visitSelection, hallowed, happly]
            · simp [visitSelection, hallowed] at hvisit
              rcases hvisit with ⟨hresult, hstatus⟩
              subst result
              subst status
              simp [visitSelection, hallowed]

  theorem visitSubfields_prefix_fresh
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ (selectionSet : List Selection)
          (prefixFields suffix result : List (Name × ResponseValue))
          (status : VisitStatus),
          (∀ responseName,
            responseName
              ∈ (GraphQL.Execution.collectFields schema variableValues
                  parentType source selectionSet).map
                  Prod.fst
            -> responseName ∉ prefixFields.map Prod.fst)
          -> visitSubfields schema resolvers variableValues depth parentType source
                selectionSet (.object suffix)
              = (.object result, status)
          -> visitSubfields schema resolvers variableValues depth parentType source
                selectionSet (.object (prefixFields ++ suffix))
              = (.object (prefixFields ++ result), status)
    | [], prefixFields, suffix, result, status, _hfresh, hvisit => by
        simp [visitSubfields] at hvisit
        rcases hvisit with ⟨hresult, hstatus⟩
        subst result
        subst status
        simp [visitSubfields]
    | selection :: rest, prefixFields, suffix, result, status, hfresh, hvisit => by
        have hheadFresh :
            ∀ responseName,
              responseName ∈
                (GraphQL.Execution.collectSelection schema variableValues
                  parentType source selection).map Prod.fst ->
              responseName ∉ prefixFields.map Prod.fst := by
          intro responseName hmem
          apply hfresh responseName
          simpa [GraphQL.Execution.collectFields] using
            (mergeExecutableGroups_key_mem
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
              responseName).mpr (Or.inl hmem)
        have htailFresh :
            ∀ responseName,
              responseName ∈
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest).map Prod.fst ->
              responseName ∉ prefixFields.map Prod.fst := by
          intro responseName hmem
          apply hfresh responseName
          simpa [GraphQL.Execution.collectFields] using
            (mergeExecutableGroups_key_mem
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
              responseName).mpr (Or.inr hmem)
        rcases
          visitSelection_preserves_object schema resolvers variableValues depth
            parentType source selection suffix
        with ⟨headFields, hheadFst⟩
        let headStatus :=
          (visitSelection schema resolvers variableValues depth parentType source
            selection (.object suffix)).snd
        have hhead :
            visitSelection schema resolvers variableValues depth parentType source
              selection (.object suffix) =
            (.object headFields, headStatus) := by
          exact Prod.ext hheadFst rfl
        let tail :=
          visitSubfields schema resolvers variableValues depth parentType source
            rest (.object headFields)
        have hvisitTail :
            tail.fst = .object result ∧
              combineVisitStatus headStatus tail.snd = status := by
          simp [visitSubfields] at hvisit
          rw [hhead] at hvisit
          simpa [tail] using hvisit
        have htail :
            visitSubfields schema resolvers variableValues depth parentType source
              rest (.object headFields) =
            (.object result, tail.snd) := by
          exact Prod.ext hvisitTail.1 rfl
        have hheadPrefix :
            visitSelection schema resolvers variableValues depth parentType source
              selection (.object (prefixFields ++ suffix)) =
            (.object (prefixFields ++ headFields), headStatus) :=
          visitSelection_prefix_fresh schema resolvers variableValues depth
            parentType source selection prefixFields suffix headFields headStatus
            hheadFresh hhead
        have htailPrefix :
            visitSubfields schema resolvers variableValues depth parentType source
              rest (.object (prefixFields ++ headFields)) =
            (.object (prefixFields ++ result), tail.snd) :=
          visitSubfields_prefix_fresh schema resolvers variableValues depth
            parentType source rest prefixFields headFields result tail.snd
            htailFresh htail
        simp [visitSubfields]
        rw [hheadPrefix]
        change
          (visitSubfields schema resolvers variableValues depth parentType source
              rest (.object (prefixFields ++ headFields))).fst =
              .object (prefixFields ++ result) ∧
            combineVisitStatus headStatus
              (visitSubfields schema resolvers variableValues depth parentType
                source rest (.object (prefixFields ++ headFields))).snd =
              status
        constructor
        · rw [htailPrefix]
        · rw [htailPrefix]
          exact hvisitTail.2
end

theorem visitSubfields_executableFieldSelections_same_response_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        fields ≠ []
        -> ∃ resultFields,
            (visitSubfields schema resolvers variableValues (completionDepth + 1)
                parentType source (executableFieldSelections responseName fields)
                (.object outputFields)).fst
              = .object resultFields
            ∧ responseName ∈ resultFields.map Prod.fst
  | [], _outputFields, hnonempty => by
      exact False.elim (hnonempty rfl)
  | field :: rest, outputFields, _hnonempty => by
      rcases
        visitSelection_preserves_object schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelection responseName field) outputFields
      with ⟨headFields, hheadFst⟩
      have hheadMemField :
          responseName ∈ headFields.map Prod.fst := by
        cases field with
        | mk fieldName arguments selectionSet =>
              cases hprevious :
                  responseObjectField? responseName (.object outputFields) with
              | none =>
                  simp [executableFieldSelection, visitSelection,
                    selectionDirectivesAllowBool_empty, mergeResponseFieldResult,
                    mergeResponseFieldIntoObject, hprevious] at hheadFst
                  rw [← hheadFst]
                  simpa [hprevious] using
                    mergeResponseField_self_key_mem responseName
                    (resultValueOrNull
                      (executeField schema resolvers variableValues
                        completionDepth parentType source
                        (responseObjectField? responseName (.object outputFields))
                        (executableField fieldName
                          arguments selectionSet)))
                    outputFields
              | some previous =>
                  cases previous with
                  | null =>
                      have hlookupRaw :
                          lookupResponseField? responseName outputFields =
                            some .null := by
                        simpa [responseObjectField?] using hprevious
                      have hmem :
                          responseName ∈ outputFields.map Prod.fst :=
                        List.mem_map_of_mem (f := Prod.fst)
                          (lookupResponseField?_some_mem responseName .null
                            outputFields hlookupRaw)
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      exact mergeResponseField_preserves_key_mem responseName
                        responseName
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth parentType source
                            (some .null)
                            (executableField fieldName
                              arguments selectionSet)))
                        outputFields hmem
                  | scalar value =>
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      simpa [hprevious] using
                        mergeResponseField_self_key_mem responseName
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth parentType source
                            (responseObjectField? responseName
                              (.object outputFields))
                            (executableField fieldName
                              arguments selectionSet)))
                        outputFields
                  | object objectFields =>
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      simpa [hprevious] using
                        mergeResponseField_self_key_mem responseName
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth parentType source
                            (responseObjectField? responseName
                              (.object outputFields))
                            (executableField fieldName
                              arguments selectionSet)))
                        outputFields
                  | list values =>
                      simp [executableFieldSelection, visitSelection,
                        selectionDirectivesAllowBool_empty,
                        mergeResponseFieldResult, mergeResponseFieldIntoObject,
                        hprevious] at hheadFst
                      rw [← hheadFst]
                      simpa [hprevious] using
                        mergeResponseField_self_key_mem responseName
                        (resultValueOrNull
                          (executeField schema resolvers variableValues
                            completionDepth parentType source
                            (responseObjectField? responseName
                              (.object outputFields))
                            (executableField fieldName
                              arguments selectionSet)))
                        outputFields
      have hheadMem : responseName ∈ headFields.map Prod.fst :=
        hheadMemField
      rcases
        visitSubfields_preserves_object_key_mem schema resolvers variableValues
          (completionDepth + 1) parentType source responseName
          (executableFieldSelections responseName rest) headFields hheadMem
      with ⟨resultFields, htail, htailMem⟩
      refine ⟨resultFields, ?_, htailMem⟩
      let headStatus :=
        (visitSelection schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelection responseName field)
          (.object outputFields)).snd
      have hhead :
          visitSelection schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelection responseName field)
            (.object outputFields) =
          (.object headFields, headStatus) := by
        exact Prod.ext hheadFst rfl
      simp [executableFieldSelections, visitSubfields]
      rw [hhead]
      simpa [executableFieldSelections] using htail

theorem visitSubfields_executableFieldSelections_singleton_append_of_mem_succ
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (responseName : Name)
    (field : ExecutableField)
    (fields suffix resultFields : List (Name × ResponseValue)) (status : VisitStatus)
    (hmem : responseName ∈ fields.map Prod.fst)
    (hfieldLookup
      : ∃ fieldDefinition,
          schema.lookupField parentType field.fieldName = some fieldDefinition)
    (hvisit
      : visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source (executableFieldSelections responseName [field])
          (.object fields)
        = (.object resultFields, status))
    : visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source (executableFieldSelections responseName [field])
        (.object (fields ++ suffix))
      = (.object (resultFields ++ suffix), status) := by
  let executedField :=
    executableField field.fieldName
      field.arguments field.selectionSet
  rcases lookupResponseField?_some_of_mem responseName fields hmem with
    ⟨previous, hlookupRaw⟩
  have hlookup :
      responseObjectField? responseName (.object fields) =
        some previous := by
    simpa [responseObjectField?] using hlookupRaw
  have hlookupAppend :
      responseObjectField? responseName (.object (fields ++ suffix)) =
        some previous :=
    responseObjectField?_object_append_of_some_left responseName fields
      suffix previous hlookup
  let fieldResult :=
    executeFieldVisitResult schema resolvers variableValues completionDepth
      parentType source previous executedField
  cases previous with
  | null =>
      rcases hfieldLookup with ⟨fieldDefinition, hfieldLookup⟩
      rw [show executableFieldSelections responseName [field] =
          [executableFieldSelection responseName field] by rfl] at hvisit ⊢
      simp only [visitSubfields, executableFieldSelection] at hvisit ⊢
      rw [visitSelection_field_allowed_succ schema resolvers variableValues
        completionDepth parentType source responseName field.fieldName
        field.arguments [] field.selectionSet (.object fields)
        (selectionDirectivesAllowBool_empty variableValues)] at hvisit
      rw [hlookup] at hvisit
      simp [visitOk, executeField, executableField, hfieldLookup,
        reusablePreviousValue?_null] at hvisit
      rcases hvisit with ⟨hfields, hstatus⟩
      have hmerge :
          mergeResponseField responseName .null fields = fields :=
        mergeResponseField_null_of_lookup_null responseName fields
          hlookupRaw
      simp [mergeResponseFieldResult, mergeResponseFieldIntoObject]
        at hfields hstatus
      cases hfields
      subst status
      have hlookupAppendRaw :
          lookupResponseField? responseName (fields ++ suffix) =
            some .null := by
        simpa [responseObjectField?] using hlookupAppend
      have hmergeAppend :
          mergeResponseField responseName .null (fields ++ suffix) =
            fields ++ suffix :=
        mergeResponseField_null_of_lookup_null responseName
          (fields ++ suffix) hlookupAppendRaw
      rw [visitSelection_field_allowed_succ schema resolvers variableValues
        completionDepth parentType source responseName field.fieldName
        field.arguments [] field.selectionSet (.object (fields ++ suffix))
        (selectionDirectivesAllowBool_empty variableValues)]
      rw [hlookupAppend]
      simpa [visitOk, executeField, executableField, hfieldLookup,
        reusablePreviousValue?_null, mergeResponseFieldResult,
        mergeResponseFieldIntoObject, resultValueOrNull] using
        mergeResponseField_append_of_mem_left responseName .null fields
          suffix hmem
  | scalar value =>
      have hbase :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections responseName [field])
            (.object fields) =
          (.object
            (mergeResponseField responseName
              (resultValueOrNull fieldResult) fields),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections responseName [field] =
            [executableFieldSelection responseName field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source responseName field.fieldName
          field.arguments [] field.selectionSet (.object fields)
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookup]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      have happend :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections responseName [field])
            (.object (fields ++ suffix)) =
          (.object
            (mergeResponseField responseName
              (resultValueOrNull fieldResult) (fields ++ suffix)),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections responseName [field] =
            [executableFieldSelection responseName field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source responseName field.fieldName
          field.arguments [] field.selectionSet (.object (fields ++ suffix))
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookupAppend]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      rw [hbase] at hvisit
      injection hvisit with hresult hstatus
      injection hresult with hfields
      rw [happend]
      rw [mergeResponseField_append_of_mem_left responseName
        (resultValueOrNull fieldResult) fields suffix hmem]
      subst status
      subst resultFields
      rfl
  | object objectFields =>
      have hbase :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections responseName [field])
            (.object fields) =
          (.object
            (mergeResponseField responseName
              (resultValueOrNull fieldResult) fields),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections responseName [field] =
            [executableFieldSelection responseName field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source responseName field.fieldName
          field.arguments [] field.selectionSet (.object fields)
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookup]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      have happend :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections responseName [field])
            (.object (fields ++ suffix)) =
          (.object
            (mergeResponseField responseName
              (resultValueOrNull fieldResult) (fields ++ suffix)),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections responseName [field] =
            [executableFieldSelection responseName field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source responseName field.fieldName
          field.arguments [] field.selectionSet (.object (fields ++ suffix))
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookupAppend]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      rw [hbase] at hvisit
      injection hvisit with hresult hstatus
      injection hresult with hfields
      rw [happend]
      rw [mergeResponseField_append_of_mem_left responseName
        (resultValueOrNull fieldResult) fields suffix hmem]
      subst status
      subst resultFields
      rfl
  | list values =>
      have hbase :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections responseName [field])
            (.object fields) =
          (.object
            (mergeResponseField responseName
              (resultValueOrNull fieldResult) fields),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections responseName [field] =
            [executableFieldSelection responseName field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source responseName field.fieldName
          field.arguments [] field.selectionSet (.object fields)
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookup]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      have happend :
          visitSubfields schema resolvers variableValues (completionDepth + 1)
            parentType source (executableFieldSelections responseName [field])
            (.object (fields ++ suffix)) =
          (.object
            (mergeResponseField responseName
              (resultValueOrNull fieldResult) (fields ++ suffix)),
            resultStatus fieldResult) := by
        rw [show executableFieldSelections responseName [field] =
            [executableFieldSelection responseName field] by rfl]
        simp only [visitSubfields, executableFieldSelection]
        rw [visitSelection_field_allowed_succ schema resolvers variableValues
          completionDepth parentType source responseName field.fieldName
          field.arguments [] field.selectionSet (.object (fields ++ suffix))
          (selectionDirectivesAllowBool_empty variableValues)]
        rw [hlookupAppend]
        simp [mergeResponseFieldResult, mergeResponseFieldIntoObject,
          fieldResult, executedField, executableField, executeFieldVisitResult]
      rw [hbase] at hvisit
      injection hvisit with hresult hstatus
      injection hresult with hfields
      rw [happend]
      rw [mergeResponseField_append_of_mem_left responseName
        (resultValueOrNull fieldResult) fields suffix hmem]
      subst status
      subst resultFields
      rfl

theorem collectFields_executableFieldSelections_key_mem_global
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (renderResponseName : Name) (fields : List ExecutableField)
    (responseName : Name)
    : responseName
        ∈ (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections renderResponseName fields)).map
            Prod.fst
      ↔ fields ≠ [] ∧ responseName = renderResponseName := by
  induction fields with
  | nil =>
      simp [executableFieldSelections, GraphQL.Execution.collectFields]
  | cons field rest ih =>
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection renderResponseName field) =
            [(renderResponseName, [field])] := by
        exact collectSelection_executableFieldSelection schema variableValues
          parentType source renderResponseName field
      simp only [executableFieldSelections, List.map_cons,
        GraphQL.Execution.collectFields]
      rw [hhead]
      rw [mergeExecutableGroups_key_mem]
      change
        responseName ∈ [(renderResponseName, [field])].map Prod.fst
            ∨ responseName ∈
              (GraphQL.Execution.collectFields schema variableValues parentType
                source (executableFieldSelections renderResponseName rest)).map
                Prod.fst
          ↔ field :: rest ≠ [] ∧ responseName = renderResponseName
      rw [ih]
      simp

theorem collectedExecutableFields_collectFields_executableFieldSelections_lookup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (responseName : Name)
    : ∀ fields : List ExecutableField,
        (∀ field,
          field ∈ fields
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    source (executableFieldSelections responseName fields))
            -> ∃ fieldDefinition,
                schema.lookupField parentType field.fieldName = some fieldDefinition
  | [], _hlookups, field, hmem => by
      simp [executableFieldSelections, GraphQL.Execution.collectFields,
        collectedExecutableFields] at hmem
  | original :: rest, hlookups, field, hmem => by
      have hhead :
          GraphQL.Execution.collectSelection schema variableValues parentType
              source (executableFieldSelection responseName original) =
            [(responseName, [original])] := by
        exact collectSelection_executableFieldSelection schema variableValues
          parentType source responseName original
      have hmemSplit :
          field ∈
              collectedExecutableFields
                [(responseName, [original])]
            ∨ field ∈
              collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source
                    (executableFieldSelections responseName rest)) := by
          have hmerge := hmem
          simp only [executableFieldSelections] at hmerge
          exact
            (collectedExecutableFields_mem_mergeExecutableGroups
            [(responseName, [original])]
            (GraphQL.Execution.collectFields schema variableValues parentType
              source (executableFieldSelections responseName rest)) field).mp hmerge
      rcases hmemSplit with hheadMem | htailMem
      · have hfieldName : field.fieldName = original.fieldName := by
          have hfieldEq :
              field = original := by
            simpa [collectedExecutableFields, executableField] using hheadMem
          simp [hfieldEq, executableField]
        rcases hlookups original (by simp) with
          ⟨fieldDefinition, hlookup⟩
        exact ⟨fieldDefinition, by simpa [hfieldName] using hlookup⟩
      · exact
          collectedExecutableFields_collectFields_executableFieldSelections_lookup
            schema variableValues parentType source responseName rest
            (by
              intro candidate hcandidate
              exact hlookups candidate (by simp [hcandidate]))
            field htailMem

mutual
  def executionSelectionLookupValid (schema : Schema) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives _selectionSet =>
        ∃ fieldDefinition, schema.lookupField parentType fieldName = some fieldDefinition
    | .inlineFragment none _directives selectionSet =>
        executionSelectionSetLookupValid schema parentType selectionSet
    | .inlineFragment (some _typeCondition) _directives selectionSet =>
        executionSelectionSetLookupValid schema parentType selectionSet

  def executionSelectionSetLookupValid (schema : Schema)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> executionSelectionLookupValid schema parentType selection
end

mutual
  theorem collectedExecutableFields_collectSelection_lookupValid
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selection : Selection)
      : executionSelectionLookupValid schema parentType selection
        -> ∀ candidate,
            candidate
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType source selection)
            -> ∃ fieldDefinition,
                schema.lookupField parentType candidate.fieldName
                = some fieldDefinition := by
    intro hlookup candidate hcandidate
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldLookupExists :
            ∃ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition := by
          simpa [executionSelectionLookupValid] using hlookup
        rcases hfieldLookupExists with ⟨fieldDefinition, hfieldLookup⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows,
            collectedExecutableFields] at hcandidate
          subst candidate
          exact ⟨fieldDefinition, hfieldLookup⟩
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            collectedExecutableFields] at hcandidate
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hchildLookup :
                executionSelectionSetLookupValid schema parentType
                  selectionSet := by
              simpa [executionSelectionLookupValid] using hlookup
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows] at hcandidate
              exact
                collectedExecutableFields_collectFields_lookupValid schema
                  variableValues parentType source selectionSet hchildLookup
                  candidate hcandidate
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases h :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate
        | some typeCondition =>
            have hchildLookup :
                executionSelectionSetLookupValid schema parentType
                  selectionSet := by
              simpa [executionSelectionLookupValid] using hlookup
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly] at hcandidate
                exact
                  collectedExecutableFields_collectFields_lookupValid schema
                    variableValues parentType source selectionSet hchildLookup
                    candidate hcandidate
              · have hskip :
                    doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases h :
                      doesFragmentTypeApplyBool schema parentType source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hskip,
                  collectedExecutableFields] at hcandidate
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases h :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate

  theorem collectedExecutableFields_collectFields_lookupValid
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : executionSelectionSetLookupValid schema parentType selectionSet
        -> ∀ candidate,
            candidate
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    source selectionSet)
            -> ∃ fieldDefinition,
                schema.lookupField parentType candidate.fieldName
                = some fieldDefinition := by
    intro hlookup candidate hcandidate
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hcandidate
    | cons selection rest =>
        have hlookupFn :
            ∀ selected, selected ∈ selection :: rest ->
              executionSelectionLookupValid schema parentType selected := by
          simpa [executionSelectionSetLookupValid] using hlookup
        have hheadLookup :
            executionSelectionLookupValid schema parentType selection :=
          hlookupFn selection (by simp)
        have htailLookup :
            executionSelectionSetLookupValid schema parentType rest := by
          unfold executionSelectionSetLookupValid
          intro selected hselected
          exact hlookupFn selected (List.mem_cons_of_mem selection hselected)
        simp [GraphQL.Execution.collectFields] at hcandidate
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType source selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                source rest)
              candidate).mp hcandidate with hhead | htail
        · exact
            collectedExecutableFields_collectSelection_lookupValid schema
              variableValues parentType source selection hheadLookup candidate
              hhead
        · exact
            collectedExecutableFields_collectFields_lookupValid schema
              variableValues parentType source rest htailLookup candidate htail
end

theorem collectedGroupsFieldLookupValid_of_executionSelectionSetLookupValid
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : executionSelectionSetLookupValid schema parentType selectionSet
      -> CollectedGroupsFieldLookupValid schema parentType
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet) := by
  intro hlookup responseName field fields hgroup
  exact
    collectedExecutableFields_collectFields_lookupValid schema variableValues
      parentType source selectionSet hlookup field
      (collectedExecutableFields_mem_of_group_mem hgroup (by simp))

theorem visitSubfields_flattened_empty_key_mem_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (fields : List (Name × ResponseValue))
    (responseName : Name)
    : (visitSubfields schema resolvers variableValues depth parentType source
          (collectedExecutableSelections
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))
          (.object [])).fst
        = .object fields
      -> responseName ∈ fields.map Prod.fst
      -> responseName
          ∈ (GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet).map
              Prod.fst := by
  intro hvisit hmem
  have hflatKey :=
    visitSubfields_object_empty_key_mem_collectFields schema resolvers
      variableValues depth parentType source
      (collectedExecutableSelections
        (GraphQL.Execution.collectFields schema variableValues parentType
          source selectionSet))
      fields responseName hvisit hmem
  simpa [collectFields_executableFieldSelections_collectedExecutableFields_collectFields]
        using hflatKey

theorem collectedExecutableEntries_responseName_mem
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (field : ExecutableField)
    : (responseName, field) ∈ collectedExecutableEntries groups
      -> responseName ∈ groups.map Prod.fst := by
  induction groups with
  | nil =>
      intro hmem
      simp [collectedExecutableEntries] at hmem
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, fields⟩
      intro hmem
      simp only [collectedExecutableEntries, List.mem_append] at hmem
      rcases hmem with hhead | hrest
      · rcases List.mem_map.mp hhead with ⟨candidate, _hcandidate, heq⟩
        injection heq with hname _hfield
        subst groupResponseName
        simp
      · simp [ih hrest]

theorem collectedExecutableEntries_responseName_ne_of_not_mem
    (targetResponseName : Name)
    (groups : List (Name × List ExecutableField))
    : targetResponseName ∉ groups.map Prod.fst
      -> ∀ responseName field,
          (responseName, field) ∈ collectedExecutableEntries groups
          -> responseName ≠ targetResponseName := by
  intro hnot responseName field hfield heq
  have hmem : responseName ∈ groups.map Prod.fst :=
    collectedExecutableEntries_responseName_mem groups responseName field hfield
  exact hnot (by simpa [heq] using hmem)

theorem collectedExecutableEntries_fresh_singleton_prefix_of_not_mem
    (targetResponseName : Name) (response : ResponseValue)
    (groups : List (Name × List ExecutableField))
    : targetResponseName ∉ groups.map Prod.fst
      -> ∀ responseName field,
          (responseName, field) ∈ collectedExecutableEntries groups
          -> responseName ∉ [(targetResponseName, response)].map Prod.fst := by
  intro hnot responseName field hfield hprefix
  have hne :=
    collectedExecutableEntries_responseName_ne_of_not_mem targetResponseName groups
      hnot responseName field hfield
  simp at hprefix
  exact hne hprefix

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
