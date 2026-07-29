import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.SliceFold

/-!
Order-insensitivity lemmas for the ungrouped execution proof.

The useful reorder step is asymmetric: a later duplicate response key may move
left across a different response key only after the duplicate key has already
been populated by the prefix. This preserves GraphQL's first-seen response field
order while exposing the grouped order used by the spec definition.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem mergeResponseField_key_mem_of_mem
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
              (mergeResponseField_key_mem_of_mem target responseName incoming
                rest
                (List.mem_map.mpr ⟨(target, tailResponse), htailPair, rfl⟩))
            with ⟨mergedPair, hmergedPair, hmergedName⟩
          rcases mergedPair with ⟨mergedName, mergedResponse⟩
          dsimp at hmergedName
          subst mergedName
          exact Or.inr
            ⟨mergedResponse, hmergedPair⟩

theorem mergeResponseField_comm_of_mem_left_ne
    (target other : Name) (targetResponse otherResponse : ResponseValue)
    : ∀ (fields : List (Name × ResponseValue)),
        target ∈ fields.map Prod.fst
        -> target ≠ other
        -> mergeResponseField target targetResponse
              (mergeResponseField other otherResponse fields)
            = mergeResponseField other otherResponse
                (mergeResponseField target targetResponse fields)
  | [], hmem, _hne => by
      simp at hmem
  | (fieldName, response) :: rest, hmem, hne => by
      by_cases htarget : fieldName = target
      · subst fieldName
        have hother : (target == other) = false := by
          simp [beq_eq_false_iff_ne, hne]
        simp [mergeResponseField, hother]
      · have htargetBool : (fieldName == target) = false := by
          simp [beq_eq_false_iff_ne, htarget]
        by_cases hotherName : fieldName = other
        · subst fieldName
          simp [mergeResponseField, htargetBool]
        · have hotherBool : (fieldName == other) = false := by
            simp [beq_eq_false_iff_ne, hotherName]
          have hrestMem : target ∈ rest.map Prod.fst := by
            simp only [List.map_cons, List.mem_cons] at hmem
            rcases hmem with hhead | htail
            · exact False.elim (htarget hhead.symm)
            · exact htail
          simp [mergeResponseField, htargetBool, hotherBool,
            mergeResponseField_comm_of_mem_left_ne target other targetResponse
              otherResponse rest hrestMem hne]

theorem mergeResponseField_comm_across_mergeResponseFields_of_mem_not_mem
    (target : Name) (targetResponse : ResponseValue)
    : ∀ (incoming fields : List (Name × ResponseValue)),
        target ∈ fields.map Prod.fst
        -> target ∉ incoming.map Prod.fst
        -> mergeResponseField target targetResponse (mergeResponseFields fields incoming)
            = mergeResponseFields
                (mergeResponseField target targetResponse fields)
                incoming
  | [], fields, _hmem, _hnot => by
      simp [mergeResponseFields]
  | (other, otherResponse) :: rest, fields, hmem, hnot => by
      have hne : target ≠ other := by
        intro heq
        exact hnot (by simp [heq])
      have hrestNot : target ∉ rest.map Prod.fst := by
        intro hrest
        exact hnot (by simp [hrest])
      have htargetAfterOther :
          target ∈
            (mergeResponseField other otherResponse fields).map Prod.fst :=
        mergeResponseField_key_mem_of_mem target other otherResponse fields hmem
      simp only [mergeResponseFields]
      rw [mergeResponseField_comm_across_mergeResponseFields_of_mem_not_mem
        target targetResponse rest
        (mergeResponseField other otherResponse fields) htargetAfterOther
        hrestNot]
      rw [mergeResponseField_comm_of_mem_left_ne target other targetResponse
        otherResponse fields hmem hne]

theorem mergeResponseFields_append_singleton
    (fields incoming : List (Name × ResponseValue))
    (responseName : Name) (response : ResponseValue)
    : mergeResponseFields fields (incoming ++ [(responseName, response)])
      = mergeResponseField responseName response
          (mergeResponseFields fields incoming) := by
  induction incoming generalizing fields with
  | nil =>
      simp [mergeResponseFields]
  | cons incomingField rest ih =>
      rcases incomingField with ⟨incomingName, incomingResponse⟩
      simp [mergeResponseFields, ih]

theorem mergeResponseSliceFold_object_eq_mergeResponseFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    : ∀ (fields : List ExecutableField) (outputFields : List (Name × ResponseValue)),
        mergeResponseSliceFold schema resolvers variableValues completionDepth
          source fields (.object outputFields)
        = .object
            (mergeResponseFields outputFields
              (responseObjectSlices schema resolvers variableValues
                completionDepth source fields))
  | [], outputFields => by
      simp [mergeResponseSliceFold, responseObjectSlices, mergeResponseFields]
  | field :: rest, outputFields => by
      have hrest :=
        mergeResponseSliceFold_object_eq_mergeResponseFields schema resolvers
          variableValues completionDepth source rest
          (mergeResponseFields outputFields
            [(field.responseName,
              responseFieldSlice schema resolvers variableValues
                completionDepth source field)])
      simpa [mergeResponseSliceFold, responseObjectSlice,
        responseObjectSlices, mergeResponse, mergeResponseFields] using hrest

theorem mergeResponse_singleton_comm_of_existing_left_ne
    (target other : Name) (targetResponse otherResponse : ResponseValue)
    (fields : List (Name × ResponseValue))
    (htarget : target ∈ fields.map Prod.fst)
    (hne : target ≠ other)
    : mergeResponse
        (mergeResponse (.object fields) (.object [(other, otherResponse)]))
        (.object [(target, targetResponse)])
      = mergeResponse
          (mergeResponse (.object fields) (.object [(target, targetResponse)]))
          (.object [(other, otherResponse)]) := by
  simp [mergeResponse, mergeResponseFields,
    mergeResponseField_comm_of_mem_left_ne target other targetResponse
      otherResponse fields htarget hne]

theorem mergeResponseSliceFold_adjacent_existing_second_swap
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (first second : ExecutableField) (fields : List (Name × ResponseValue))
    (hsecond : second.responseName ∈ fields.map Prod.fst)
    (hne : second.responseName ≠ first.responseName)
    : mergeResponseSliceFold schema resolvers variableValues completionDepth source
        [first, second] (.object fields)
      = mergeResponseSliceFold schema resolvers variableValues completionDepth source
          [second, first] (.object fields) := by
  simpa [mergeResponseSliceFold, responseObjectSlice] using
    mergeResponse_singleton_comm_of_existing_left_ne second.responseName
      first.responseName
      (responseFieldSlice schema resolvers variableValues completionDepth source
        second)
      (responseFieldSlice schema resolvers variableValues completionDepth source
        first)
      fields hsecond hne

theorem mergeResponseSliceFold_middle_existing_last_swap
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (fields : List (Name × ResponseValue))
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    : mergeResponseSliceFold schema resolvers variableValues completionDepth source
        (middle ++ [later]) (.object fields)
      = mergeResponseSliceFold schema resolvers variableValues completionDepth source
          (later :: middle) (.object fields) := by
  rw [mergeResponseSliceFold_object_eq_mergeResponseFields schema resolvers
    variableValues completionDepth source (middle ++ [later]) fields]
  rw [mergeResponseSliceFold_object_eq_mergeResponseFields schema resolvers
    variableValues completionDepth source (later :: middle) fields]
  have hnotSlices :
      later.responseName ∉
        (responseObjectSlices schema resolvers variableValues completionDepth
          source middle).map Prod.fst := by
    intro hmem
    rw [responseObjectSlices_key_mem schema resolvers variableValues
      completionDepth source middle later.responseName] at hmem
    exact hnotMiddle hmem
  simpa [responseObjectSlices, mergeResponseFields,
    mergeResponseFields_append_singleton] using
    mergeResponseField_comm_across_mergeResponseFields_of_mem_not_mem
      later.responseName
      (responseFieldSlice schema resolvers variableValues completionDepth source
        later)
      (responseObjectSlices schema resolvers variableValues completionDepth
        source middle)
      fields hlater hnotSlices

theorem mergeResponseSliceFold_middle_existing_last_swap_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    : mergeResponseSliceFold schema resolvers variableValues completionDepth source
        ((middle ++ [later]) ++ rest) (.object fields)
      = mergeResponseSliceFold schema resolvers variableValues completionDepth source
          ((later :: middle) ++ rest) (.object fields) := by
  have hswap :
      mergeResponseSliceFold schema resolvers variableValues completionDepth source
          (middle ++ [later]) (.object fields) =
        mergeResponseSliceFold schema resolvers variableValues completionDepth source
          (later :: middle) (.object fields) :=
    mergeResponseSliceFold_middle_existing_last_swap schema resolvers
      variableValues completionDepth source middle later fields hlater
      hnotMiddle
  unfold mergeResponseSliceFold at hswap ⊢
  conv =>
    lhs
    rw [List.foldl_append]
  conv =>
    rhs
    rw [List.foldl_append]
  exact congrArg
    (fun output =>
      List.foldl
        (fun output field =>
          mergeResponse output
            (responseObjectSlice schema resolvers variableValues
              completionDepth source field))
        output rest)
    hswap

theorem visitFieldSliceFold_succ_middle_existing_last_swap_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    : visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source ((middle ++ [later]) ++ rest) (.object fields)
      = visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
          source ((later :: middle) ++ rest) (.object fields) := by
  rw [visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
    resolvers variableValues completionDepth source
    ((middle ++ [later]) ++ rest) (.object fields) hleftTrace]
  rw [visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
    resolvers variableValues completionDepth source
    ((later :: middle) ++ rest) (.object fields) hrightTrace]
  exact
    mergeResponseSliceFold_middle_existing_last_swap_cons schema resolvers
      variableValues completionDepth source middle later rest fields hlater
      hnotMiddle

theorem visitSubfields_executableFieldSelections_middle_existing_last_swap_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hparents
      : ∀ field, field ∈ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    : visitSubfields schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ((middle ++ [later]) ++ rest))
        (.object fields)
      = visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ((later :: middle) ++ rest))
          (.object fields) := by
  have hparentsRight :
      ∀ field, field ∈ ((later :: middle) ++ rest) ->
        field.parentType = parentType := by
    intro field hmem
    apply hparents field
    simp only [List.mem_append, List.mem_cons] at hmem ⊢
    rcases hmem with hprefix | hrestMem
    · rcases hprefix with hlaterEq | hmiddle
      · subst field
        simp
      · simp [hmiddle]
    · simp [hrestMem]
  have hleftVisit :
      visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((middle ++ [later]) ++ rest)
          (.object fields) =
        visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ((middle ++ [later]) ++ rest))
          (.object fields) :=
    visitFieldSliceFoldResult_eq_visitSubfields_executableFieldSelections
      schema resolvers variableValues (completionDepth + 1) parentType source
      ((middle ++ [later]) ++ rest) (.object fields) hparents
  have hrightVisit :
      visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((later :: middle) ++ rest)
          (.object fields) =
        visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ((later :: middle) ++ rest))
          (.object fields) :=
    visitFieldSliceFoldResult_eq_visitSubfields_executableFieldSelections
      schema resolvers variableValues (completionDepth + 1) parentType source
      ((later :: middle) ++ rest) (.object fields) hparentsRight
  have hfoldFst :
      (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((middle ++ [later]) ++ rest)
          (.object fields)).fst =
        (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((later :: middle) ++ rest)
          (.object fields)).fst := by
    rw [visitFieldSliceFoldResult_fst_eq_visitFieldSliceFold schema
      resolvers variableValues (completionDepth + 1) source
      ((middle ++ [later]) ++ rest) (.object fields)]
    rw [visitFieldSliceFoldResult_fst_eq_visitFieldSliceFold schema
      resolvers variableValues (completionDepth + 1) source
      ((later :: middle) ++ rest) (.object fields)]
    exact
      visitFieldSliceFold_succ_middle_existing_last_swap_of_traces schema
        resolvers variableValues completionDepth source middle later rest
        fields hlater hnotMiddle hleftTrace hrightTrace
  have hfoldSnd :
      (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((middle ++ [later]) ++ rest)
          (.object fields)).snd =
        (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((later :: middle) ++ rest)
          (.object fields)).snd :=
    visitFieldSliceFoldResult_snd_middle_existing_last_swap_cons schema
      resolvers variableValues (completionDepth + 1) source middle later rest
      fields hnotMiddle
  have hfold :
      visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((middle ++ [later]) ++ rest)
          (.object fields) =
        visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((later :: middle) ++ rest)
          (.object fields) := by
    exact Prod.ext hfoldFst hfoldSnd
  have hvisit :
      visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ((middle ++ [later]) ++ rest))
          (.object fields) =
        visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ((later :: middle) ++ rest))
          (.object fields) := by
    rw [← hleftVisit, ← hrightVisit]
    exact hfold
  exact hvisit

theorem VisitSubfieldsFlatCollects_middle_existing_last_swap_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hparents
      : ∀ field, field ∈ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections ((middle ++ [later]) ++ rest))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections ((later :: middle) ++ rest)))
    (hnormalized
      : VisitSubfieldsFlatCollects schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections ((later :: middle) ++ rest))
          (.object fields))
    : VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections ((middle ++ [later]) ++ rest))
        (.object fields) := by
  unfold VisitSubfieldsFlatCollects at hnormalized ⊢
  rw [hcollect]
  rw [visitSubfields_executableFieldSelections_middle_existing_last_swap_of_traces
    schema resolvers variableValues completionDepth parentType source middle
    later rest fields hparents hlater hnotMiddle hleftTrace hrightTrace]
  exact hnormalized

theorem visitFieldSliceFold_succ_middle_existing_last_swap_after_prefix_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (pre middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    : visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source (pre ++ ((middle ++ [later]) ++ rest)) (.object [])
      = visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
          source (pre ++ ((later :: middle) ++ rest)) (.object []) := by
  unfold visitFieldSliceFold at hprefix ⊢
  conv =>
    lhs
    rw [List.foldl_append]
  conv =>
    rhs
    rw [List.foldl_append]
  rw [hprefix]
  change
    visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source ((middle ++ [later]) ++ rest) (.object fields) =
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source ((later :: middle) ++ rest) (.object fields)
  exact
    visitFieldSliceFold_succ_middle_existing_last_swap_of_traces schema
      resolvers variableValues completionDepth source middle later rest fields
      hlater hnotMiddle hleftTrace hrightTrace

theorem
    visitSubfields_executableFieldSelections_middle_existing_last_swap_after_prefix_of_traces
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity) (pre middle : List ExecutableField)
    (later : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hparents
      : ∀ field,
          field ∈ pre ++ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    : visitSubfields schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        (.object [])
      = visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((later :: middle) ++ rest)))
          (.object []) := by
  have hparentsRight :
      ∀ field, field ∈ pre ++ ((later :: middle) ++ rest) ->
        field.parentType = parentType := by
    intro field hmem
    apply hparents field
    simp only [List.mem_append, List.mem_cons] at hmem ⊢
    rcases hmem with hpreMem | htail
    · exact Or.inl hpreMem
    · rcases htail with hprefix | hrestMem
      · rcases hprefix with hlaterEq | hmiddle
        · subst field
          simp
        · simp [hmiddle]
      · simp [hrestMem]
  have hprefixResultFst :
      (visitFieldSliceFoldResult schema resolvers variableValues
        (completionDepth + 1) source pre (.object [])).fst =
      .object fields := by
    rw [visitFieldSliceFoldResult_fst_eq_visitFieldSliceFold schema
      resolvers variableValues (completionDepth + 1) source pre (.object [])]
    exact hprefix
  have htailFst :
      (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((middle ++ [later]) ++ rest)
          (.object fields)).fst =
        (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((later :: middle) ++ rest)
          (.object fields)).fst := by
    rw [visitFieldSliceFoldResult_fst_eq_visitFieldSliceFold schema
      resolvers variableValues (completionDepth + 1) source
      ((middle ++ [later]) ++ rest) (.object fields)]
    rw [visitFieldSliceFoldResult_fst_eq_visitFieldSliceFold schema
      resolvers variableValues (completionDepth + 1) source
      ((later :: middle) ++ rest) (.object fields)]
    exact
      visitFieldSliceFold_succ_middle_existing_last_swap_of_traces schema
        resolvers variableValues completionDepth source middle later rest
        fields hlater hnotMiddle hleftTrace hrightTrace
  have htailSnd :
      (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((middle ++ [later]) ++ rest)
          (.object fields)).snd =
        (visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((later :: middle) ++ rest)
          (.object fields)).snd :=
    visitFieldSliceFoldResult_snd_middle_existing_last_swap_cons schema
      resolvers variableValues (completionDepth + 1) source middle later rest
      fields hnotMiddle
  have htail :
      visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((middle ++ [later]) ++ rest)
          (.object fields) =
        visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source ((later :: middle) ++ rest)
          (.object fields) := by
    exact Prod.ext htailFst htailSnd
  have hfold :
      visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source
          (pre ++ ((middle ++ [later]) ++ rest)) (.object []) =
        visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source
          (pre ++ ((later :: middle) ++ rest)) (.object []) := by
    rw [visitFieldSliceFoldResult_append schema resolvers variableValues
      (completionDepth + 1) source pre ((middle ++ [later]) ++ rest)
      (.object [])]
    rw [visitFieldSliceFoldResult_append schema resolvers variableValues
      (completionDepth + 1) source pre ((later :: middle) ++ rest)
      (.object [])]
    simp only
    rw [hprefixResultFst, htail]
  have hleftVisit :
      visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source
          (pre ++ ((middle ++ [later]) ++ rest)) (.object []) =
        visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections
            (pre ++ ((middle ++ [later]) ++ rest)))
          (.object []) :=
    visitFieldSliceFoldResult_eq_visitSubfields_executableFieldSelections
      schema resolvers variableValues (completionDepth + 1) parentType source
      (pre ++ ((middle ++ [later]) ++ rest)) (.object []) hparents
  have hrightVisit :
      visitFieldSliceFoldResult schema resolvers variableValues
          (completionDepth + 1) source
          (pre ++ ((later :: middle) ++ rest)) (.object []) =
        visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections
            (pre ++ ((later :: middle) ++ rest)))
          (.object []) :=
    visitFieldSliceFoldResult_eq_visitSubfields_executableFieldSelections
      schema resolvers variableValues (completionDepth + 1) parentType source
      (pre ++ ((later :: middle) ++ rest)) (.object []) hparentsRight
  have hvisit :
      visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections
            (pre ++ ((middle ++ [later]) ++ rest)))
          (.object []) =
        visitSubfields schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections
            (pre ++ ((later :: middle) ++ rest)))
          (.object []) := by
    rw [← hleftVisit, ← hrightVisit]
    exact hfold
  exact hvisit

theorem VisitSubfieldsFlatCollects_middle_existing_last_swap_after_prefix_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (pre middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hparents
      : ∀ field,
          field ∈ pre ++ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hnormalized
      : VisitSubfieldsFlatCollects schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((later :: middle) ++ rest)))
          (.object []))
    : VisitSubfieldsFlatCollects schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        (.object []) := by
  unfold VisitSubfieldsFlatCollects at hnormalized ⊢
  rw [hcollect]
  rw [visitSubfields_executableFieldSelections_middle_existing_last_swap_after_prefix_of_traces
    schema resolvers variableValues completionDepth parentType source pre
    middle later rest fields hprefix hparents hlater hnotMiddle hleftTrace
    hrightTrace]
  exact hnormalized

theorem executeRootSelectionSet_eq_spec_of_middle_existing_last_swap_after_prefix
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (pre middle : List ExecutableField) (later : ExecutableField)
    (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hparents
      : ∀ field,
          field ∈ pre ++ ((middle ++ [later]) ++ rest) -> field.parentType = parentType)
    (hlater : later.responseName ∈ fields.map Prod.fst)
    (hnotMiddle : later.responseName ∉ middle.map (fun field => field.responseName))
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((middle ++ [later]) ++ rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source ((later :: middle) ++ rest) (.object fields))
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
        = GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (pre ++ ((later :: middle) ++ rest))))
    (hnormalized
      : VisitSubfieldsFlatCollects schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((later :: middle) ++ rest)))
          (.object []))
    (hgroups
      : ExecutableGroupsFlatSpecEquivalent schema resolvers variableValues
          (completionDepth + 1) parentType source
          (GraphQL.Execution.collectFields schema variableValues parentType source
            (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))))
    : executeRootSelectionSet schema resolvers variableValues
        (completionDepth + 1) parentType source
        (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          (completionDepth + 1) parentType source
          (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest))) := by
  exact
    executeRootSelectionSet_eq_spec_of_flatCollects_and_groupFlatSpecEquivalent
      schema resolvers variableValues (completionDepth + 1) parentType source
      (executableFieldSelections (pre ++ ((middle ++ [later]) ++ rest)))
      (VisitSubfieldsFlatCollects_middle_existing_last_swap_after_prefix_of_traces
        schema resolvers variableValues completionDepth parentType source pre
        middle later rest fields hprefix hparents hlater hnotMiddle hleftTrace
        hrightTrace hcollect hnormalized)
      hgroups

theorem mergeResponseSliceFold_adjacent_existing_second_swap_cons
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (first second : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hsecond : second.responseName ∈ fields.map Prod.fst)
    (hne : second.responseName ≠ first.responseName)
    : mergeResponseSliceFold schema resolvers variableValues completionDepth source
        (first :: second :: rest) (.object fields)
      = mergeResponseSliceFold schema resolvers variableValues completionDepth source
          (second :: first :: rest) (.object fields) := by
  have hswap :
      mergeResponse
          (mergeResponse (.object fields)
            (responseObjectSlice schema resolvers variableValues
              completionDepth source first))
          (responseObjectSlice schema resolvers variableValues
            completionDepth source second) =
        mergeResponse
          (mergeResponse (.object fields)
            (responseObjectSlice schema resolvers variableValues
              completionDepth source second))
          (responseObjectSlice schema resolvers variableValues
            completionDepth source first) := by
    simpa [responseObjectSlice] using
      mergeResponse_singleton_comm_of_existing_left_ne second.responseName
        first.responseName
        (responseFieldSlice schema resolvers variableValues completionDepth
          source second)
        (responseFieldSlice schema resolvers variableValues completionDepth
          source first)
        fields hsecond hne
  simp only [mergeResponseSliceFold, List.foldl_cons]
  rw [hswap]

theorem visitFieldSliceFold_succ_adjacent_existing_second_swap_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (first second : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hsecond : second.responseName ∈ fields.map Prod.fst)
    (hne : second.responseName ≠ first.responseName)
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source (first :: second :: rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source (second :: first :: rest) (.object fields))
    : visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source (first :: second :: rest) (.object fields)
      = visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
          source (second :: first :: rest) (.object fields) := by
  rw [visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
    resolvers variableValues completionDepth source (first :: second :: rest)
    (.object fields) hleftTrace]
  rw [visitFieldSliceFold_succ_eq_mergeResponseSliceFold_of_trace schema
    resolvers variableValues completionDepth source (second :: first :: rest)
    (.object fields) hrightTrace]
  exact
    mergeResponseSliceFold_adjacent_existing_second_swap_cons schema
      resolvers variableValues completionDepth source first second rest fields
      hsecond hne

theorem visitSubfields_executableFieldSelections_adjacent_existing_second_swap_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    (first second : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hparents : ∀ field, field ∈ first :: second :: rest -> field.parentType = parentType)
    (hsecond : second.responseName ∈ fields.map Prod.fst)
    (hne : second.responseName ≠ first.responseName)
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source (first :: second :: rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source (second :: first :: rest) (.object fields))
    : (visitSubfields schema resolvers variableValues (completionDepth + 1)
        parentType source
        (executableFieldSelections (first :: second :: rest))
        (.object fields)).fst
      = (visitSubfields schema resolvers variableValues (completionDepth + 1)
          parentType source
          (executableFieldSelections (second :: first :: rest))
          (.object fields)).fst := by
  have hparentsRight :
      ∀ field, field ∈ second :: first :: rest ->
        field.parentType = parentType := by
    intro field hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hsecondMem | htail
    · exact hparents field (by simp [hsecondMem])
    · rcases htail with hfirstMem | hrestMem
      · exact hparents field (by simp [hfirstMem])
      · exact hparents field (by simp [hrestMem])
  rw [← visitFieldSliceFold_eq_visitSubfields_executableFieldSelections schema
    resolvers variableValues (completionDepth + 1) parentType source
    (first :: second :: rest) (.object fields) hparents]
  rw [← visitFieldSliceFold_eq_visitSubfields_executableFieldSelections schema
    resolvers variableValues (completionDepth + 1) parentType source
    (second :: first :: rest) (.object fields) hparentsRight]
  exact
    visitFieldSliceFold_succ_adjacent_existing_second_swap_of_traces schema
      resolvers variableValues completionDepth source first second rest fields
      hsecond hne hleftTrace hrightTrace

theorem visitFieldSliceFold_succ_adjacent_existing_second_swap_after_prefix_of_traces
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (completionDepth : Nat) (source : ResolverValue ObjectIdentity)
    (pre : List ExecutableField)
    (first second : ExecutableField) (rest : List ExecutableField)
    (fields : List (Name × ResponseValue))
    (hprefix
      : visitFieldSliceFold schema resolvers variableValues
          (completionDepth + 1) source pre (.object [])
        = .object fields)
    (hsecond : second.responseName ∈ fields.map Prod.fst)
    (hne : second.responseName ≠ first.responseName)
    (hleftTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source (first :: second :: rest) (.object fields))
    (hrightTrace
      : FieldSliceMergeTrace schema resolvers variableValues completionDepth
          source (second :: first :: rest) (.object fields))
    : visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source (pre ++ first :: second :: rest) (.object [])
      = visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
          source (pre ++ second :: first :: rest) (.object []) := by
  unfold visitFieldSliceFold at hprefix ⊢
  rw [List.foldl_append, List.foldl_append]
  rw [hprefix]
  change
    visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source (first :: second :: rest) (.object fields) =
      visitFieldSliceFold schema resolvers variableValues (completionDepth + 1)
        source (second :: first :: rest) (.object fields)
  exact
    visitFieldSliceFold_succ_adjacent_existing_second_swap_of_traces schema
      resolvers variableValues completionDepth source first second rest fields
      hsecond hne hleftTrace hrightTrace

end ExecutionUngrouped
end Algorithms

end GraphQL
