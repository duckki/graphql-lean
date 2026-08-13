import GraphQL.Algorithms.ExecutionUngrouped
import GraphQL.Algorithms.ExecutionUngroupedUncached
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Semantics
import Proofs.GraphQL.Validation.FieldMerge

/-!
Cache invariants for the source-caching ungrouped executor.

This layer establishes output projection, source alignment, merge readiness,
and absorption properties for `FieldCacheValue`.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem sameResponseShape_isCompositeBool_eq (schema : Schema)
    : ∀ left right,
        GraphQL.FieldMerge.sameResponseShape schema left right
        -> left.isCompositeBool schema = right.isCompositeBool schema
  | .nonNull left, .nonNull right, hshape => by
      exact sameResponseShape_isCompositeBool_eq schema left right hshape
  | .nonNull _, .named _, hshape => by
      simp [GraphQL.FieldMerge.sameResponseShape] at hshape
  | .nonNull _, .list _, hshape => by
      simp [GraphQL.FieldMerge.sameResponseShape] at hshape
  | .named _, .nonNull _, hshape => by
      simp [GraphQL.FieldMerge.sameResponseShape] at hshape
  | .list _, .nonNull _, hshape => by
      simp [GraphQL.FieldMerge.sameResponseShape] at hshape
  | .list left, .list right, hshape => by
      exact sameResponseShape_isCompositeBool_eq schema left right hshape
  | .list _, .named _, hshape => by
      simp [GraphQL.FieldMerge.sameResponseShape] at hshape
  | .named _, .list _, hshape => by
      simp [GraphQL.FieldMerge.sameResponseShape] at hshape
  | .named left, .named right, hshape => by
      by_cases hleft : schema.isLeafType left
      · have hnames : left = right := hshape.2.2 (Or.inl hleft)
        subst right
        rfl
      · by_cases hright : schema.isLeafType right
        · have hnames : left = right := hshape.2.2 (Or.inr hright)
          subst right
          rfl
        · unfold TypeRef.isCompositeBool TypeRef.namedType
          rcases hshape with ⟨hleftOut, hrightOut, _hleafEq⟩
          rcases hleftOut with ⟨leftDefinition, hleftLookup, hleftOutput⟩
          rcases hrightOut with ⟨rightDefinition, hrightLookup, hrightOutput⟩
          rw [hleftLookup, hrightLookup]
          have hleftNotLeaf : ¬leftDefinition.isLeafType := by
            intro hdefinitionLeaf
            exact hleft ⟨leftDefinition, hleftLookup, hdefinitionLeaf⟩
          have hrightNotLeaf : ¬rightDefinition.isLeafType := by
            intro hdefinitionLeaf
            exact hright ⟨rightDefinition, hrightLookup, hdefinitionLeaf⟩
          cases leftDefinition <;> cases rightDefinition <;>
            simp [TypeDefinition.isLeafType, TypeDefinition.isOutputType] at hleftOutput hrightOutput hleftNotLeaf hrightNotLeaf ⊢

theorem named_isCompositeBool_eq_true_of_typeIncludesObjectBool
    (schema : Schema) (typeName objectName : Name)
    : schema.typeIncludesObjectBool typeName objectName = true
      -> (TypeRef.named typeName).isCompositeBool schema = true := by
  intro hincludes
  unfold Schema.typeIncludesObjectBool Schema.getPossibleTypes at hincludes
  unfold TypeRef.isCompositeBool TypeRef.namedType
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hincludes
  | some typeDefinition =>
      cases typeDefinition <;> simp [hlookup] at hincludes ⊢

@[simp]
theorem output_null {ObjectRef : Type}
    : (FieldCacheValue.null : FieldCacheValue ObjectRef).output = .null := by
  rw [FieldCacheValue.output.eq_def]

@[simp]
theorem output_scalar {ObjectRef : Type} (value : String)
    : (FieldCacheValue.scalar (ObjectRef := ObjectRef) value).output = .scalar value := by
  rw [FieldCacheValue.output.eq_def]

@[simp]
theorem output_object {ObjectRef : Type} (source : ResolverValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : (FieldCacheValue.object source fields).output = .object (outputFields fields) := by
  rw [FieldCacheValue.output.eq_def]

@[simp]
theorem output_list {ObjectRef : Type}
    (sourceValues? : Option (List (ResolverValue ObjectRef)))
    (values : List (FieldCacheValue ObjectRef))
    : (FieldCacheValue.list sourceValues? values).output
      = .list (outputValues values) := by
  rw [FieldCacheValue.output.eq_def]

@[simp]
theorem outputValues_nil {ObjectRef : Type}
    : outputValues ([] : List (FieldCacheValue ObjectRef)) = [] := by
  rw [outputValues.eq_def]

@[simp]
theorem outputValues_cons {ObjectRef : Type} (value : FieldCacheValue ObjectRef)
    (values : List (FieldCacheValue ObjectRef))
    : outputValues (value :: values) = value.output :: outputValues values := by
  rw [outputValues.eq_def]

@[simp]
theorem outputFields_nil {ObjectRef : Type}
    : outputFields ([] : List (Name × FieldCacheValue ObjectRef)) = [] := by
  rw [outputFields.eq_def]

@[simp]
theorem outputFields_cons {ObjectRef : Type} (field : Name × FieldCacheValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : outputFields (field :: fields)
      = (field.1, field.2.output) :: outputFields fields := by
  rw [outputFields.eq_def]

theorem output_mergeResponse {ObjectRef : Type} (left right : FieldCacheValue ObjectRef)
    : (mergeResponse left right).output
      = ExecutionUngroupedUncached.mergeResponse left.output right.output := by
  let motive1 : FieldCacheValue ObjectRef -> FieldCacheValue ObjectRef -> Prop :=
    fun left right =>
      (mergeResponse left right).output =
        ExecutionUngroupedUncached.mergeResponse left.output right.output
  let motive2
      : List (FieldCacheValue ObjectRef) -> List (FieldCacheValue ObjectRef)
        -> Prop :=
    fun left right =>
      outputValues (mergeResponseLists left right) =
        ExecutionUngroupedUncached.mergeResponseLists (outputValues left)
          (outputValues right)
  let motive3
      : List (Name × FieldCacheValue ObjectRef)
        -> List (Name × FieldCacheValue ObjectRef) -> Prop :=
    fun left right =>
      outputFields (mergeResponseFields left right) =
        ExecutionUngroupedUncached.mergeResponseFields (outputFields left)
          (outputFields right)
  let motive4
      : Name -> FieldCacheValue ObjectRef
        -> List (Name × FieldCacheValue ObjectRef) -> Prop :=
    fun responseName incoming fields =>
      outputFields (mergeResponseField responseName incoming fields) =
        ExecutionUngroupedUncached.mergeResponseField responseName incoming.output
          (outputFields fields)
  exact
    mergeResponse.induct motive1 motive2 motive3 motive4
      (by
        intro right
        cases right <;>
          simp [motive1, mergeResponse,
            ExecutionUngroupedUncached.mergeResponse])
      (by
        intro left hnot
        cases left <;>
          simp [motive1, mergeResponse,
            ExecutionUngroupedUncached.mergeResponse] at hnot ⊢)
      (by
        intro _existingSource existingFields _incomingSource incomingFields ih
        simp [motive1, mergeResponse,
          ExecutionUngroupedUncached.mergeResponse]
        simpa [motive3] using ih)
      (by
        intro _existingSourceValues existingValues _incomingSourceValues
          incomingValues ih
        simp [motive1, mergeResponse,
          ExecutionUngroupedUncached.mergeResponse]
        simpa [motive2] using ih)
      (by
        intro existing incoming hExisting hIncoming hNotObject hNotList
        cases existing <;> cases incoming <;>
          simp [motive1, mergeResponse, ExecutionUngroupedUncached.mergeResponse] at hExisting hIncoming hNotObject hNotList ⊢
        · exact False.elim ((hNotObject _ _ _ _ rfl rfl rfl) rfl)
        · exact False.elim ((hNotList _ _ _ _ rfl rfl rfl) rfl))
      (by
        intro incomingValues
        cases incomingValues <;>
          simp [motive2, mergeResponseLists,
            ExecutionUngroupedUncached.mergeResponseLists])
      (by
        intro existingValues hnot
        cases existingValues <;>
          simp [motive2, mergeResponseLists,
            ExecutionUngroupedUncached.mergeResponseLists] at hnot ⊢)
      (by
        intro existing existingRest incoming incomingRest ihValue ihList
        simp [motive2, mergeResponseLists,
          ExecutionUngroupedUncached.mergeResponseLists]
        exact
          ⟨by simpa [motive1] using ihValue,
            by simpa [motive2] using ihList⟩)
      (by
        intro existingFields
        cases existingFields <;>
          simp [motive3, mergeResponseFields,
            ExecutionUngroupedUncached.mergeResponseFields])
      (by
        intro existingFields responseName incoming rest ihField ihFields
        simp [motive3, mergeResponseFields,
          ExecutionUngroupedUncached.mergeResponseFields]
        have hfields :
            outputFields
                (mergeResponseFields
                  (mergeResponseField responseName incoming existingFields)
                  rest)
              =
            ExecutionUngroupedUncached.mergeResponseFields
              (outputFields
                (mergeResponseField responseName incoming existingFields))
              (outputFields rest) := by
          simpa [motive3] using ihFields
        rw [hfields]
        exact
          congrArg
            (fun fields =>
              ExecutionUngroupedUncached.mergeResponseFields fields
                (outputFields rest))
            (by simpa [motive4] using ihField))
      (by
        intro responseName incoming
        simp [motive4, mergeResponseField,
          ExecutionUngroupedUncached.mergeResponseField])
      (by
        intro responseName incoming fieldResponseName existing _rest h ih
        simp [motive4, mergeResponseField,
          ExecutionUngroupedUncached.mergeResponseField, h]
        simpa [motive1] using ih)
      (by
        intro responseName incoming fieldResponseName existing rest h ih
        simp [motive4, mergeResponseField,
          ExecutionUngroupedUncached.mergeResponseField, h, ih])
      left right

theorem output_mergeResponseLists {ObjectRef : Type}
    : ∀ left right : List (FieldCacheValue ObjectRef),
        outputValues (mergeResponseLists left right)
        = ExecutionUngroupedUncached.mergeResponseLists (outputValues left)
            (outputValues right)
  | [], [] => by
      simp [mergeResponseLists,
        ExecutionUngroupedUncached.mergeResponseLists]
  | [], _incoming :: _incomingRest => by
      simp [mergeResponseLists,
        ExecutionUngroupedUncached.mergeResponseLists]
  | _existing :: _existingRest, [] => by
      simp [mergeResponseLists,
        ExecutionUngroupedUncached.mergeResponseLists]
  | existing :: existingRest, incoming :: incomingRest => by
      simp [mergeResponseLists, ExecutionUngroupedUncached.mergeResponseLists,
        output_mergeResponse existing incoming,
        output_mergeResponseLists existingRest incomingRest]

theorem output_mergeResponseField {ObjectRef : Type}
    (responseName : Name) (incoming : FieldCacheValue ObjectRef)
    : ∀ fields : List (Name × FieldCacheValue ObjectRef),
        outputFields (mergeResponseField responseName incoming fields)
        = ExecutionUngroupedUncached.mergeResponseField responseName incoming.output
            (outputFields fields)
  | [] => by
      simp [mergeResponseField, ExecutionUngroupedUncached.mergeResponseField]
  | (fieldResponseName, existing) :: rest => by
      by_cases h : fieldResponseName == responseName
      · simp [mergeResponseField, ExecutionUngroupedUncached.mergeResponseField, h,
          output_mergeResponse existing incoming]
      · simp [mergeResponseField, ExecutionUngroupedUncached.mergeResponseField, h,
          output_mergeResponseField responseName incoming rest]

theorem output_mergeResponseFields {ObjectRef : Type}
    (left : List (Name × FieldCacheValue ObjectRef))
    : ∀ right : List (Name × FieldCacheValue ObjectRef),
        outputFields (mergeResponseFields left right)
        = ExecutionUngroupedUncached.mergeResponseFields (outputFields left)
            (outputFields right)
  | [] => by
      simp [mergeResponseFields, ExecutionUngroupedUncached.mergeResponseFields]
  | (responseName, incoming) :: rest => by
      simp [mergeResponseFields, ExecutionUngroupedUncached.mergeResponseFields,
        output_mergeResponseField responseName incoming left,
        output_mergeResponseFields
          (mergeResponseField responseName incoming left) rest]

theorem sizeOf_mergeResponseField_le {ObjectRef : Type}
    (responseName : Name) (incoming : FieldCacheValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : sizeOf (mergeResponseField responseName incoming fields)
      ≤ sizeOf fields + sizeOf responseName + sizeOf incoming + 2 := by
  let responseMotive : FieldCacheValue ObjectRef -> FieldCacheValue ObjectRef -> Prop :=
    fun left right => sizeOf (mergeResponse left right) ≤ sizeOf left + sizeOf right
  let listMotive
      : List (FieldCacheValue ObjectRef) -> List (FieldCacheValue ObjectRef) -> Prop :=
    fun left right =>
      sizeOf (mergeResponseLists left right) ≤ sizeOf left + sizeOf right
  let fieldsMotive
      : List (Name × FieldCacheValue ObjectRef)
        -> List (Name × FieldCacheValue ObjectRef) -> Prop :=
    fun left right =>
      sizeOf (mergeResponseFields left right) ≤ sizeOf left + sizeOf right
  let fieldMotive
      : Name -> FieldCacheValue ObjectRef
        -> List (Name × FieldCacheValue ObjectRef) -> Prop :=
    fun responseName incoming fields =>
      sizeOf (mergeResponseField responseName incoming fields)
        ≤ sizeOf fields + sizeOf responseName + sizeOf incoming + 2
  exact
    mergeResponseField.induct responseMotive listMotive fieldsMotive fieldMotive
      (by
        intro right
        cases right <;> simp [responseMotive, mergeResponse] <;> omega)
      (by
        intro left hnot
        cases left <;> simp [responseMotive, mergeResponse] at hnot ⊢ <;> omega)
      (by
        intro existingSource existingFields incomingSource incomingFields ih
        simp [responseMotive, fieldsMotive, mergeResponse] at ih ⊢
        omega)
      (by
        intro existingSourceValues existingValues incomingSourceValues
          incomingValues ih
        simp [responseMotive, listMotive, mergeResponse] at ih ⊢
        omega)
      (by
        intro existing incoming hExisting hIncoming hNotObject hNotList
        cases existing <;> cases incoming <;>
          simp [responseMotive, mergeResponse] at hExisting hIncoming hNotObject hNotList ⊢
        · exact False.elim ((hNotObject _ _ _ _ rfl rfl rfl) rfl)
        · exact False.elim ((hNotList _ _ _ _ rfl rfl rfl) rfl))
      (by
        intro incomingValues
        cases incomingValues <;> simp [listMotive, mergeResponseLists] <;> omega)
      (by
        intro existingValues hnot
        cases existingValues <;>
          simp [listMotive, mergeResponseLists] at hnot ⊢ <;> omega)
      (by
        intro existing existingRest incoming incomingRest ihValue ihList
        simp [listMotive, responseMotive, mergeResponseLists] at ihValue ihList ⊢
        omega)
      (by
        intro existingFields
        cases existingFields <;> simp [fieldsMotive, mergeResponseFields] <;> omega)
      (by
        intro existingFields responseName incoming rest ihField ihFields
        simp [fieldsMotive, fieldMotive, mergeResponseFields] at ihField ihFields ⊢
        omega)
      (by
        intro responseName incoming
        simp [fieldMotive, mergeResponseField]
        omega)
      (by
        intro responseName incoming fieldResponseName existing rest h ih
        simp [fieldMotive, responseMotive, mergeResponseField, h] at ih ⊢
        omega)
      (by
        intro responseName incoming fieldResponseName existing rest h ih
        simp [fieldMotive, mergeResponseField, h] at ih ⊢
        omega)
      responseName incoming fields

def FieldCacheKeysNodup {ObjectRef : Type}
    (fields : List (Name × FieldCacheValue ObjectRef))
    : Prop :=
  (fields.map Prod.fst).Nodup

inductive FieldCacheMergeReady {ObjectRef : Type}
    : FieldCacheValue ObjectRef -> Prop where
  | null : FieldCacheMergeReady .null
  | scalar (value : String) : FieldCacheMergeReady (.scalar value)
  | object (source : ResolverValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : FieldCacheKeysNodup fields
      -> (∀ responseName response,
            (responseName, response) ∈ fields -> FieldCacheMergeReady response)
      -> FieldCacheMergeReady (.object source fields)
  | list (sourceValues? : Option (List (ResolverValue ObjectRef)))
    (values : List (FieldCacheValue ObjectRef))
    : (∀ response, response ∈ values -> FieldCacheMergeReady response)
      -> FieldCacheMergeReady (.list sourceValues? values)

mutual
  inductive FieldCacheSourceAligned {ObjectRef : Type}
      : ResolverValue ObjectRef -> FieldCacheValue ObjectRef -> Prop where
    | null (source : ResolverValue ObjectRef) : FieldCacheSourceAligned source .null
    | scalar (value : String) : FieldCacheSourceAligned (.scalar value) (.scalar value)
    | object (source : ResolverValue ObjectRef)
      (fields : List (Name × FieldCacheValue ObjectRef))
      : FieldCacheSourceAligned source (.object source fields)
    | cachedList (sourceValues : List (ResolverValue ObjectRef))
      (values : List (FieldCacheValue ObjectRef))
      : FieldCacheSourcesAligned sourceValues values
        -> FieldCacheSourceAligned (.list sourceValues) (.list (some sourceValues) values)
    | finalList (sourceValues : List (ResolverValue ObjectRef))
      (values : List (FieldCacheValue ObjectRef))
      : FieldCacheSourcesAligned sourceValues values
        -> FieldCacheSourceAligned (.list sourceValues) (.list none values)

  inductive FieldCacheSourcesAligned {ObjectRef : Type}
      : List (ResolverValue ObjectRef) -> List (FieldCacheValue ObjectRef) -> Prop where
    | nil : FieldCacheSourcesAligned [] []
    | cons {source : ResolverValue ObjectRef}
      {value : FieldCacheValue ObjectRef}
      {sourceRest : List (ResolverValue ObjectRef)}
      {valueRest : List (FieldCacheValue ObjectRef)}
      : FieldCacheSourceAligned source value
        -> FieldCacheSourcesAligned sourceRest valueRest
        -> FieldCacheSourcesAligned (source :: sourceRest) (value :: valueRest)

  inductive FieldCacheSourcesPrefixAligned {ObjectRef : Type}
      : List (ResolverValue ObjectRef) -> List (FieldCacheValue ObjectRef) -> Prop where
    | nil (sources : List (ResolverValue ObjectRef))
      : FieldCacheSourcesPrefixAligned sources []
    | cons {source : ResolverValue ObjectRef}
      {value : FieldCacheValue ObjectRef}
      {sourceRest : List (ResolverValue ObjectRef)}
      {valueRest : List (FieldCacheValue ObjectRef)}
      : FieldCacheSourceAligned source value
        -> FieldCacheSourcesPrefixAligned sourceRest valueRest
        -> FieldCacheSourcesPrefixAligned (source :: sourceRest) (value :: valueRest)
end

theorem FieldCacheSourcesAligned.toPrefixAligned {ObjectRef : Type}
    : ∀ {sources : List (ResolverValue ObjectRef)}
        {values : List (FieldCacheValue ObjectRef)},
        FieldCacheSourcesAligned sources values
        -> FieldCacheSourcesPrefixAligned sources values
  | [], [], FieldCacheSourcesAligned.nil =>
      FieldCacheSourcesPrefixAligned.nil []
  | _source :: _sourceRest,
    _value :: _valueRest,
    FieldCacheSourcesAligned.cons haligned hrest =>
      FieldCacheSourcesPrefixAligned.cons haligned
        (FieldCacheSourcesAligned.toPrefixAligned hrest)

def FieldCacheAbsorbs {ObjectRef : Type} (base output : FieldCacheValue ObjectRef)
    : Prop :=
  mergeResponse base output = output

theorem mergeResponseFields_cons_left_of_not_mem {ObjectRef : Type}
    (responseName : Name) (response : FieldCacheValue ObjectRef)
    (existing incoming : List (Name × FieldCacheValue ObjectRef))
    : responseName ∉ incoming.map Prod.fst
      -> mergeResponseFields ((responseName, response) :: existing) incoming
          = (responseName, response) :: mergeResponseFields existing incoming := by
  intro hnot
  induction incoming generalizing existing with
  | nil =>
      simp [mergeResponseFields]
  | cons field rest ih =>
      rcases field with ⟨incomingName, incomingResponse⟩
      have hne : responseName ≠ incomingName := by
        intro heq
        exact hnot (by simp [heq])
      have hbeq : (responseName == incomingName) = false := by
        simp [beq_eq_false_iff_ne, hne]
      have hrestNot : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact hnot (by simp [hmem])
      simp [mergeResponseFields, mergeResponseField, hbeq,
        ih (mergeResponseField incomingName incomingResponse existing) hrestNot]

mutual
  theorem mergeResponse_self_of_cacheReady {ObjectRef : Type}
      : ∀ response : FieldCacheValue ObjectRef,
          FieldCacheMergeReady response -> mergeResponse response response = response
    | .null, _hready => by
        simp [mergeResponse]
    | .scalar value, _hready => by
        simp [mergeResponse]
    | .object source fields, hready => by
        cases hready with
        | object _ _ hnodup hfields =>
            simp [mergeResponse]
            exact mergeResponseFields_self_of_cacheReady fields hnodup hfields
    | .list sourceValues? values, hready => by
        cases hready with
        | list _ _ hvalues =>
            simp [mergeResponse]
            exact mergeResponseLists_self_of_cacheReady values hvalues

  theorem mergeResponseFields_self_of_cacheReady {ObjectRef : Type}
      : ∀ fields : List (Name × FieldCacheValue ObjectRef),
          FieldCacheKeysNodup fields
          -> (∀ responseName response,
                (responseName, response) ∈ fields -> FieldCacheMergeReady response)
          -> mergeResponseFields fields fields = fields
    | [], _hnodup, _hfields => by
        simp [mergeResponseFields]
    | (responseName, response) :: rest, hnodup, hfields => by
        have hresponseReady : FieldCacheMergeReady response :=
          hfields responseName response (by simp)
        have hresponseSelf : mergeResponse response response = response :=
          mergeResponse_self_of_cacheReady response hresponseReady
        have hrestNodup : FieldCacheKeysNodup rest := by
          unfold FieldCacheKeysNodup at hnodup ⊢
          exact (List.nodup_cons.mp hnodup).2
        have hresponseNameNotRest : responseName ∉ rest.map Prod.fst := by
          unfold FieldCacheKeysNodup at hnodup
          exact (List.nodup_cons.mp hnodup).1
        have hrestFields :
            ∀ restName restResponse,
              (restName, restResponse) ∈ rest ->
                FieldCacheMergeReady restResponse := by
          intro restName restResponse hmem
          exact hfields restName restResponse (by simp [hmem])
        have hrestSelf : mergeResponseFields rest rest = rest :=
          mergeResponseFields_self_of_cacheReady rest hrestNodup hrestFields
        simp [mergeResponseFields, mergeResponseField, hresponseSelf,
          mergeResponseFields_cons_left_of_not_mem responseName response rest rest
            hresponseNameNotRest, hrestSelf]

  theorem mergeResponseLists_self_of_cacheReady {ObjectRef : Type}
      : ∀ values : List (FieldCacheValue ObjectRef),
          (∀ response, response ∈ values -> FieldCacheMergeReady response)
          -> mergeResponseLists values values = values
    | [], _hvalues => by
        simp [mergeResponseLists]
    | response :: rest, hvalues => by
        have hresponseReady : FieldCacheMergeReady response :=
          hvalues response (by simp)
        have hresponseSelf : mergeResponse response response = response :=
          mergeResponse_self_of_cacheReady response hresponseReady
        have hrestValues :
            ∀ restResponse, restResponse ∈ rest ->
              FieldCacheMergeReady restResponse := by
          intro restResponse hmem
          exact hvalues restResponse (by simp [hmem])
        have hrestSelf : mergeResponseLists rest rest = rest :=
          mergeResponseLists_self_of_cacheReady rest hrestValues
        simp [mergeResponseLists, hresponseSelf, hrestSelf]
end

theorem FieldCacheAbsorbs.refl_of_ready {ObjectRef : Type}
    (response : FieldCacheValue ObjectRef)
    : FieldCacheMergeReady response -> FieldCacheAbsorbs response response := by
  exact mergeResponse_self_of_cacheReady response

theorem FieldCacheMergeReady.object_keysNodup {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : FieldCacheMergeReady (.object source fields) -> FieldCacheKeysNodup fields := by
  intro hready
  cases hready with
  | object _ _ hnodup _ => exact hnodup

theorem FieldCacheMergeReady.object_field {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    (responseName : Name) (response : FieldCacheValue ObjectRef)
    : FieldCacheMergeReady (.object source fields)
      -> (responseName, response) ∈ fields
      -> FieldCacheMergeReady response := by
  intro hready hmem
  cases hready with
  | object _ _ _ hfields => exact hfields responseName response hmem

theorem FieldCacheMergeReady.list_value {ObjectRef : Type}
    (sourceValues? : Option (List (ResolverValue ObjectRef)))
    (values : List (FieldCacheValue ObjectRef))
    (response : FieldCacheValue ObjectRef)
    : FieldCacheMergeReady (.list sourceValues? values)
      -> response ∈ values
      -> FieldCacheMergeReady response := by
  intro hready hmem
  cases hready with
  | list _ _ hvalues => exact hvalues response hmem

theorem mergeResponseField_key_mem {ObjectRef : Type}
    (responseName key : Name) (incoming : FieldCacheValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : key ∈ (mergeResponseField responseName incoming fields).map Prod.fst
      -> key = responseName ∨ key ∈ fields.map Prod.fst := by
  induction fields with
  | nil =>
      simp [mergeResponseField]
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, existing⟩
      by_cases h : fieldResponseName == responseName
      · intro hmem
        simp [mergeResponseField, h] at hmem
        rcases hmem with hhead | hrest
        · exact Or.inr (by simp [hhead])
        · exact Or.inr (by simp [hrest])
      · intro hmem
        simp [mergeResponseField, h] at hmem
        rcases hmem with hhead | htail
        · exact Or.inr (by simp [hhead])
        · rcases ih (by simpa [List.mem_map] using htail) with hkey | hrest
          · exact Or.inl hkey
          · exact Or.inr (by simp [hrest])

theorem mergeResponseField_keysNodup {ObjectRef : Type}
    (responseName : Name) (incoming : FieldCacheValue ObjectRef)
    : ∀ fields : List (Name × FieldCacheValue ObjectRef),
        FieldCacheKeysNodup fields
        -> FieldCacheKeysNodup (mergeResponseField responseName incoming fields)
  | [], _hnodup => by
      simp [FieldCacheKeysNodup, mergeResponseField]
  | (fieldResponseName, existing) :: rest, hnodup => by
      by_cases h : fieldResponseName == responseName
      · simpa [FieldCacheKeysNodup, mergeResponseField, h] using hnodup
      · unfold FieldCacheKeysNodup at hnodup ⊢
        simp only [mergeResponseField, h]
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          rcases
              mergeResponseField_key_mem responseName fieldResponseName incoming rest
                hmem with
            heq | hrest
          · have hne : fieldResponseName ≠ responseName := by
              intro heq'
              simp [heq'] at h
            exact hne heq
          · exact (List.nodup_cons.mp hnodup).1 hrest
        · exact mergeResponseField_keysNodup responseName incoming rest (by
            unfold FieldCacheKeysNodup
            exact (List.nodup_cons.mp hnodup).2)

theorem mergeResponseField_values_ready {ObjectRef : Type}
    (responseName : Name) (incoming : FieldCacheValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : FieldCacheMergeReady incoming
      -> (∀ fieldResponseName response,
            (fieldResponseName, response) ∈ fields -> FieldCacheMergeReady response)
      -> (∀ existing,
            (responseName, existing) ∈ fields
            -> FieldCacheMergeReady (mergeResponse existing incoming))
      -> ∀ fieldResponseName response,
          (fieldResponseName, response) ∈ mergeResponseField responseName incoming fields
          -> FieldCacheMergeReady response := by
  intro hincoming hfields hmerge
  induction fields with
  | nil =>
      intro fieldResponseName response hmem
      simp [mergeResponseField] at hmem
      rcases hmem with ⟨_hname, hresponse⟩
      rw [hresponse]
      exact hincoming
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, existing⟩
      by_cases h : fieldResponseName == responseName
      · intro candidateName response hmem
        simp [mergeResponseField, h] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hname, hresponse⟩
          rw [hresponse]
          exact hmerge existing (by simp [beq_iff_eq.mp h])
        · exact hfields candidateName response (by simp [htail])
      · intro candidateName response hmem
        simp [mergeResponseField, h] at hmem
        rcases hmem with hhead | htail
        · exact hfields candidateName response (by simp [hhead])
        · apply ih
          · intro restName restResponse hrest
            exact hfields restName restResponse (by simp [hrest])
          · intro restExisting hrest
            exact hmerge restExisting (by simp [hrest])
          · exact htail

mutual
  theorem mergeResponse_cacheReady {ObjectRef : Type}
      : ∀ existing incoming : FieldCacheValue ObjectRef,
          FieldCacheMergeReady existing
          -> FieldCacheMergeReady incoming
          -> FieldCacheMergeReady (mergeResponse existing incoming)
    | .object existingSource existingFields,
      .object incomingSource incomingFields,
      hexisting,
      hincoming => by
        simp [mergeResponse]
        exact
          mergeResponseFields_cacheReady existingSource incomingSource
            existingFields incomingFields hexisting hincoming
    | .list existingSourceValues? existingValues,
      .list incomingSourceValues? incomingValues,
      hexisting,
      hincoming => by
        simp [mergeResponse]
        exact
          mergeResponseLists_cacheReady existingSourceValues? incomingSourceValues?
            existingValues incomingValues hexisting hincoming
    | .null, _, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .scalar _value, .null, _hexisting, _hincoming => by
        simpa [mergeResponse] using FieldCacheMergeReady.null
    | .scalar value, .scalar _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .scalar value, .object _source _fields, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .scalar value, .list _sourceValues _values, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .object _source _fields, .null, _hexisting, _hincoming => by
        simpa [mergeResponse] using FieldCacheMergeReady.null
    | .object source fields, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .object source fields, .list sourceValues? values, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .list _sourceValues _values, .null, _hexisting, _hincoming => by
        simpa [mergeResponse] using FieldCacheMergeReady.null
    | .list sourceValues? values, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .list sourceValues? values, .object source fields, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting

  theorem mergeResponseFields_cacheReady {ObjectRef : Type}
      : ∀ existingSource incomingSource : ResolverValue ObjectRef,
        ∀ existing incoming : List (Name × FieldCacheValue ObjectRef),
          FieldCacheMergeReady (.object existingSource existing)
          -> FieldCacheMergeReady (.object incomingSource incoming)
          -> FieldCacheMergeReady
              (.object existingSource (mergeResponseFields existing incoming))
    | existingSource, _incomingSource, existing, [], hexisting, _hincoming => by
        simpa [mergeResponseFields] using hexisting
    | existingSource,
      incomingSource,
      existing,
      (responseName, incomingResponse) :: rest,
      hexisting,
      hincoming => by
        have hincomingResponse : FieldCacheMergeReady incomingResponse :=
          FieldCacheMergeReady.object_field incomingSource
            ((responseName, incomingResponse) :: rest) responseName incomingResponse
            hincoming (by simp)
        have hrestIncoming : FieldCacheMergeReady (.object incomingSource rest) := by
          apply FieldCacheMergeReady.object
          · exact
              (FieldCacheMergeReady.object_keysNodup incomingSource
                ((responseName, incomingResponse) :: rest) hincoming).tail
          · intro restName restResponse hmem
            exact
              FieldCacheMergeReady.object_field incomingSource
                ((responseName, incomingResponse) :: rest) restName restResponse
                hincoming (by simp [hmem])
        have hupdatedReady :
            FieldCacheMergeReady
              (.object existingSource
                (mergeResponseField responseName incomingResponse existing)) := by
          apply FieldCacheMergeReady.object
          · exact
              mergeResponseField_keysNodup responseName incomingResponse existing
                (FieldCacheMergeReady.object_keysNodup existingSource existing
                  hexisting)
          · apply mergeResponseField_values_ready responseName incomingResponse existing
            · exact hincomingResponse
            · intro fieldName response hmem
              exact
                FieldCacheMergeReady.object_field existingSource existing fieldName
                  response hexisting hmem
            · intro existingResponse hmem
              exact
                mergeResponse_cacheReady existingResponse incomingResponse
                  (FieldCacheMergeReady.object_field existingSource existing
                    responseName existingResponse hexisting hmem)
                  hincomingResponse
        simp [mergeResponseFields]
        exact
          mergeResponseFields_cacheReady existingSource incomingSource
            (mergeResponseField responseName incomingResponse existing) rest
            hupdatedReady hrestIncoming

  theorem mergeResponseLists_cacheReady {ObjectRef : Type}
      : ∀ existingSourceValues? incomingSourceValues?,
        ∀ existing incoming : List (FieldCacheValue ObjectRef),
          FieldCacheMergeReady (.list existingSourceValues? existing)
          -> FieldCacheMergeReady (.list incomingSourceValues? incoming)
          -> FieldCacheMergeReady
              (.list existingSourceValues? (mergeResponseLists existing incoming))
    | existingSourceValues?, _incomingSourceValues?, [], _incoming, hexisting,
      _hincoming => by
        simpa [mergeResponseLists] using hexisting
    | existingSourceValues?, _incomingSourceValues?, existing, [], hexisting,
      _hincoming => by
        cases existing <;> simpa [mergeResponseLists] using hexisting
    | existingSourceValues?,
      incomingSourceValues?,
      existing :: existingRest,
      incoming :: incomingRest,
      hexisting,
      hincoming => by
        apply FieldCacheMergeReady.list
        intro response hmem
        simp [mergeResponseLists] at hmem
        rcases hmem with hhead | htail
        · rw [hhead]
          exact
            mergeResponse_cacheReady existing incoming
              (FieldCacheMergeReady.list_value existingSourceValues?
                (existing :: existingRest) existing hexisting (by simp))
              (FieldCacheMergeReady.list_value incomingSourceValues?
                (incoming :: incomingRest) incoming hincoming (by simp))
        · exact
            FieldCacheMergeReady.list_value existingSourceValues?
              (mergeResponseLists existingRest incomingRest) response
              (mergeResponseLists_cacheReady existingSourceValues?
                incomingSourceValues? existingRest incomingRest
                (FieldCacheMergeReady.list existingSourceValues? existingRest
                  (by
                    intro restResponse hrest
                    exact
                      FieldCacheMergeReady.list_value existingSourceValues?
                        (existing :: existingRest) restResponse hexisting
                        (by simp [hrest])))
                (FieldCacheMergeReady.list incomingSourceValues? incomingRest
                  (by
                    intro restResponse hrest
                    exact
                      FieldCacheMergeReady.list_value incomingSourceValues?
                        (incoming :: incomingRest) restResponse hincoming
                        (by simp [hrest]))))
              htail
end

theorem mergeResponseField_object_cacheReady {ObjectRef : Type}
    (source : ResolverValue ObjectRef)
    (responseName : Name) (incoming : FieldCacheValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : FieldCacheMergeReady (.object source fields)
      -> FieldCacheMergeReady incoming
      -> FieldCacheMergeReady
          (.object source (mergeResponseField responseName incoming fields)) := by
  intro hfields hincoming
  apply FieldCacheMergeReady.object
  · exact
      mergeResponseField_keysNodup responseName incoming fields
        (FieldCacheMergeReady.object_keysNodup source fields hfields)
  · apply mergeResponseField_values_ready responseName incoming fields
    · exact hincoming
    · intro fieldName response hmem
      exact
        FieldCacheMergeReady.object_field source fields fieldName response hfields
          hmem
    · intro existing hmem
      exact
        mergeResponse_cacheReady existing incoming
          (FieldCacheMergeReady.object_field source fields responseName existing
            hfields hmem)
          hincoming

theorem mergeResponseFields_nil_left_of_keysNodup {ObjectRef : Type}
    : ∀ fields : List (Name × FieldCacheValue ObjectRef),
        FieldCacheKeysNodup fields -> mergeResponseFields [] fields = fields
  | [], _hnodup => by
      simp [mergeResponseFields]
  | (responseName, response) :: rest, hnodup => by
      have hrestNodup : FieldCacheKeysNodup rest := by
        unfold FieldCacheKeysNodup at hnodup ⊢
        exact (List.nodup_cons.mp hnodup).2
      have hresponseNameNotRest : responseName ∉ rest.map Prod.fst := by
        unfold FieldCacheKeysNodup at hnodup
        exact (List.nodup_cons.mp hnodup).1
      simp [mergeResponseFields, mergeResponseField]
      rw [mergeResponseFields_cons_left_of_not_mem responseName response [] rest
        hresponseNameNotRest]
      simp [mergeResponseFields_nil_left_of_keysNodup rest hrestNodup]

mutual
  inductive FieldCacheAbsorptionShape {ObjectRef : Type}
      : FieldCacheValue ObjectRef -> FieldCacheValue ObjectRef -> Prop where
    | null : FieldCacheAbsorptionShape .null .null
    | toNull (base : FieldCacheValue ObjectRef) : FieldCacheAbsorptionShape base .null
    | scalar (value : String) : FieldCacheAbsorptionShape (.scalar value) (.scalar value)
    | object {source : ResolverValue ObjectRef}
      {base output : List (Name × FieldCacheValue ObjectRef)}
      : FieldCacheFieldsAbsorptionShape source base output
        -> FieldCacheAbsorptionShape (.object source base) (.object source output)
    | list {sourceValues? : Option (List (ResolverValue ObjectRef))}
      {base output : List (FieldCacheValue ObjectRef)}
      : FieldCacheListAbsorptionShape sourceValues? base output
        -> FieldCacheAbsorptionShape
            (.list sourceValues? base) (.list sourceValues? output)

  inductive FieldCacheFieldsAbsorptionShape {ObjectRef : Type}
      : ResolverValue ObjectRef
        -> List (Name × FieldCacheValue ObjectRef)
        -> List (Name × FieldCacheValue ObjectRef) -> Prop where
    | nil (output : List (Name × FieldCacheValue ObjectRef))
      : FieldCacheMergeReady (.object source output)
        -> FieldCacheFieldsAbsorptionShape source [] output
    | cons (responseName : Name)
      {baseResponse outputResponse : FieldCacheValue ObjectRef}
      {baseRest outputRest : List (Name × FieldCacheValue ObjectRef)}
      : FieldCacheMergeReady
          (.object source ((responseName, outputResponse) :: outputRest))
        -> FieldCacheAbsorptionShape baseResponse outputResponse
        -> FieldCacheFieldsAbsorptionShape source baseRest outputRest
        -> FieldCacheFieldsAbsorptionShape source
            ((responseName, baseResponse) :: baseRest)
            ((responseName, outputResponse) :: outputRest)

  inductive FieldCacheListAbsorptionShape {ObjectRef : Type}
      : Option (List (ResolverValue ObjectRef)) -> List (FieldCacheValue ObjectRef)
        -> List (FieldCacheValue ObjectRef) -> Prop where
    | nil : FieldCacheListAbsorptionShape sourceValues? [] []
    | cons {baseResponse outputResponse : FieldCacheValue ObjectRef}
      {baseRest outputRest : List (FieldCacheValue ObjectRef)}
      : FieldCacheMergeReady (.list sourceValues? (outputResponse :: outputRest))
        -> FieldCacheAbsorptionShape baseResponse outputResponse
        -> FieldCacheListAbsorptionShape sourceValues? baseRest outputRest
        -> FieldCacheListAbsorptionShape sourceValues?
            (baseResponse :: baseRest) (outputResponse :: outputRest)
end

mutual
  theorem FieldCacheAbsorptionShape.output_ready {ObjectRef : Type}
      : ∀ {base output : FieldCacheValue ObjectRef},
          FieldCacheAbsorptionShape base output -> FieldCacheMergeReady output
    | .null, .null, FieldCacheAbsorptionShape.null =>
        FieldCacheMergeReady.null
    | _base, .null, FieldCacheAbsorptionShape.toNull _ =>
        FieldCacheMergeReady.null
    | .scalar value, .scalar _, FieldCacheAbsorptionShape.scalar _ =>
        FieldCacheMergeReady.scalar value
    | .object _source _base,
      .object _ _output,
      FieldCacheAbsorptionShape.object hfields =>
        FieldCacheFieldsAbsorptionShape.output_ready hfields
    | .list _sourceValues _base,
      .list _ _output,
      FieldCacheAbsorptionShape.list hvalues =>
        FieldCacheListAbsorptionShape.output_ready hvalues

  theorem FieldCacheFieldsAbsorptionShape.output_ready {ObjectRef : Type}
      {source : ResolverValue ObjectRef}
      : ∀ {base output : List (Name × FieldCacheValue ObjectRef)},
          FieldCacheFieldsAbsorptionShape source base output
          -> FieldCacheMergeReady (.object source output)
    | _base, _output, hshape => by
        cases hshape with
        | nil _ hready => exact hready
        | cons _ hready _ _ => exact hready

  theorem FieldCacheListAbsorptionShape.output_ready {ObjectRef : Type}
      {sourceValues? : Option (List (ResolverValue ObjectRef))}
      : ∀ {base output : List (FieldCacheValue ObjectRef)},
          FieldCacheListAbsorptionShape sourceValues? base output
          -> FieldCacheMergeReady (.list sourceValues? output)
    | [], [], FieldCacheListAbsorptionShape.nil =>
        FieldCacheMergeReady.list sourceValues? [] (by simp)
    | _baseResponse :: _baseRest,
      _outputResponse :: _outputRest,
      FieldCacheListAbsorptionShape.cons hready _ _ =>
        hready
end

mutual
  theorem FieldCacheAbsorptionShape.trans {ObjectRef : Type}
      {base middle output : FieldCacheValue ObjectRef}
      (hbaseMiddle : FieldCacheAbsorptionShape base middle)
      (hmiddleOutput : FieldCacheAbsorptionShape middle output)
      : FieldCacheAbsorptionShape base output := by
    cases hmiddleOutput with
    | null =>
        exact FieldCacheAbsorptionShape.toNull base
    | toNull _middle =>
        exact FieldCacheAbsorptionShape.toNull base
    | scalar _value =>
        exact hbaseMiddle
    | object hmiddleOutput =>
        cases hbaseMiddle with
        | object hbaseMiddle =>
            exact
              FieldCacheAbsorptionShape.object
                (FieldCacheFieldsAbsorptionShape.trans hbaseMiddle hmiddleOutput)
    | list hmiddleOutput =>
        cases hbaseMiddle with
        | list hbaseMiddle =>
            exact
              FieldCacheAbsorptionShape.list
                (FieldCacheListAbsorptionShape.trans hbaseMiddle hmiddleOutput)

  theorem FieldCacheFieldsAbsorptionShape.trans {ObjectRef : Type}
      {source : ResolverValue ObjectRef}
      : ∀ {base middle output : List (Name × FieldCacheValue ObjectRef)},
          FieldCacheFieldsAbsorptionShape source base middle
          -> FieldCacheFieldsAbsorptionShape source middle output
          -> FieldCacheFieldsAbsorptionShape source base output
    | _base, _middle, _output, hbaseMiddle, hmiddleOutput => by
        cases hbaseMiddle with
        | nil _ _ =>
            exact
              FieldCacheFieldsAbsorptionShape.nil _ hmiddleOutput.output_ready
        | cons responseName _ hbaseMiddleResponse hbaseMiddleRest =>
            cases hmiddleOutput with
            | cons _ houtputReady hmiddleOutputResponse hmiddleOutputRest =>
                exact
                  FieldCacheFieldsAbsorptionShape.cons responseName houtputReady
                    (FieldCacheAbsorptionShape.trans hbaseMiddleResponse
                      hmiddleOutputResponse)
                    (FieldCacheFieldsAbsorptionShape.trans hbaseMiddleRest
                      hmiddleOutputRest)

  theorem FieldCacheListAbsorptionShape.trans {ObjectRef : Type}
      {sourceValues? : Option (List (ResolverValue ObjectRef))}
      : ∀ {base middle output : List (FieldCacheValue ObjectRef)},
          FieldCacheListAbsorptionShape sourceValues? base middle
          -> FieldCacheListAbsorptionShape sourceValues? middle output
          -> FieldCacheListAbsorptionShape sourceValues? base output
    | [],
      [],
      [],
      FieldCacheListAbsorptionShape.nil,
      FieldCacheListAbsorptionShape.nil =>
        FieldCacheListAbsorptionShape.nil
    | _baseResponse :: _baseRest,
      _middleResponse :: _middleRest,
      _outputResponse :: _outputRest,
      FieldCacheListAbsorptionShape.cons _ hbaseMiddleResponse hbaseMiddleRest,
      FieldCacheListAbsorptionShape.cons houtputReady hmiddleOutputResponse
        hmiddleOutputRest =>
        FieldCacheListAbsorptionShape.cons houtputReady
          (FieldCacheAbsorptionShape.trans hbaseMiddleResponse hmiddleOutputResponse)
          (FieldCacheListAbsorptionShape.trans hbaseMiddleRest hmiddleOutputRest)
end

mutual
  theorem FieldCacheAbsorptionShape.to_absorbs {ObjectRef : Type}
      : ∀ {base output : FieldCacheValue ObjectRef},
          FieldCacheAbsorptionShape base output -> FieldCacheAbsorbs base output
    | .null, .null, FieldCacheAbsorptionShape.null => by
        simp [FieldCacheAbsorbs, mergeResponse]
    | base, .null, FieldCacheAbsorptionShape.toNull _ => by
        cases base <;> simp [FieldCacheAbsorbs, mergeResponse]
    | .scalar _value, .scalar _, FieldCacheAbsorptionShape.scalar _ => by
        simp [FieldCacheAbsorbs, mergeResponse]
    | .object _source _base,
      .object _ _output,
      FieldCacheAbsorptionShape.object hfields => by
        simp [FieldCacheAbsorbs, mergeResponse]
        exact FieldCacheFieldsAbsorptionShape.to_merge _ hfields
    | .list _sourceValues _base,
      .list _ _output,
      FieldCacheAbsorptionShape.list hvalues => by
        simp [FieldCacheAbsorbs, mergeResponse]
        exact FieldCacheListAbsorptionShape.to_merge _ hvalues

  theorem FieldCacheFieldsAbsorptionShape.to_merge {ObjectRef : Type}
      : ∀ (source : ResolverValue ObjectRef)
          {base output : List (Name × FieldCacheValue ObjectRef)},
          FieldCacheFieldsAbsorptionShape source base output
          -> mergeResponseFields base output = output
    | source, _base, output, hshape => by
        cases hshape with
        | nil _ houtputReady =>
            exact
              mergeResponseFields_nil_left_of_keysNodup output
                (FieldCacheMergeReady.object_keysNodup source output houtputReady)
        | cons responseName houtputReady hresponse hrest =>
            rename_i baseResponse outputResponse baseRest outputRest
            have hresponseAbsorbs :
                mergeResponse baseResponse outputResponse = outputResponse := by
              simpa [FieldCacheAbsorbs] using
                FieldCacheAbsorptionShape.to_absorbs hresponse
            have hrestMerge : mergeResponseFields baseRest outputRest = outputRest :=
              FieldCacheFieldsAbsorptionShape.to_merge source hrest
            have hresponseNameNotRest : responseName ∉ outputRest.map Prod.fst := by
              have hnodup :=
                FieldCacheMergeReady.object_keysNodup source
                  ((responseName, outputResponse) :: outputRest) houtputReady
              unfold FieldCacheKeysNodup at hnodup
              exact (List.nodup_cons.mp hnodup).1
            simp [mergeResponseFields, mergeResponseField, hresponseAbsorbs]
            rw [mergeResponseFields_cons_left_of_not_mem responseName outputResponse
              baseRest outputRest hresponseNameNotRest]
            simp [hrestMerge]

  theorem FieldCacheListAbsorptionShape.to_merge {ObjectRef : Type}
      : ∀ (sourceValues? : Option (List (ResolverValue ObjectRef)))
          {base output : List (FieldCacheValue ObjectRef)},
          FieldCacheListAbsorptionShape sourceValues? base output
          -> mergeResponseLists base output = output
    | _sourceValues, [], [], FieldCacheListAbsorptionShape.nil => by
        simp [mergeResponseLists]
    | sourceValues?,
      baseResponse :: baseRest,
      outputResponse :: outputRest,
      FieldCacheListAbsorptionShape.cons _houtputReady hresponse hrest => by
        have hresponseAbsorbs :
            mergeResponse baseResponse outputResponse = outputResponse := by
          simpa [FieldCacheAbsorbs] using
            FieldCacheAbsorptionShape.to_absorbs hresponse
        have hrestMerge : mergeResponseLists baseRest outputRest = outputRest :=
          FieldCacheListAbsorptionShape.to_merge sourceValues? hrest
        simp [mergeResponseLists, hresponseAbsorbs, hrestMerge]
end

theorem FieldCacheAbsorbs.trans_of_shape {ObjectRef : Type}
    {base middle output : FieldCacheValue ObjectRef}
    : FieldCacheAbsorptionShape base middle
      -> FieldCacheAbsorptionShape middle output
      -> FieldCacheAbsorbs base output := by
  intro hbaseMiddle hmiddleOutput
  exact
    FieldCacheAbsorptionShape.to_absorbs
      (FieldCacheAbsorptionShape.trans hbaseMiddle hmiddleOutput)

mutual
  theorem FieldCacheAbsorptionShape.refl_of_ready {ObjectRef : Type}
      : ∀ response : FieldCacheValue ObjectRef,
          FieldCacheMergeReady response -> FieldCacheAbsorptionShape response response
    | .null, _hready =>
        FieldCacheAbsorptionShape.null
    | .scalar value, _hready =>
        FieldCacheAbsorptionShape.scalar value
    | .object source fields, hready =>
        FieldCacheAbsorptionShape.object
          (FieldCacheFieldsAbsorptionShape.refl_of_ready source fields hready)
    | .list sourceValues? values, hready =>
        FieldCacheAbsorptionShape.list
          (FieldCacheListAbsorptionShape.refl_of_ready sourceValues? values hready)

  theorem FieldCacheFieldsAbsorptionShape.refl_of_ready {ObjectRef : Type}
      (source : ResolverValue ObjectRef)
      : ∀ fields : List (Name × FieldCacheValue ObjectRef),
          FieldCacheMergeReady (.object source fields)
          -> FieldCacheFieldsAbsorptionShape source fields fields
    | [], hready =>
        FieldCacheFieldsAbsorptionShape.nil [] hready
    | (responseName, response) :: rest, hready => by
        have hresponseReady : FieldCacheMergeReady response :=
          FieldCacheMergeReady.object_field source
            ((responseName, response) :: rest) responseName response hready (by simp)
        have hrestReady : FieldCacheMergeReady (.object source rest) := by
          apply FieldCacheMergeReady.object
          · exact
              (FieldCacheMergeReady.object_keysNodup source
                ((responseName, response) :: rest) hready).tail
          · intro restName restResponse hmem
            exact
              FieldCacheMergeReady.object_field source
                ((responseName, response) :: rest) restName restResponse hready
                (by simp [hmem])
        exact
          FieldCacheFieldsAbsorptionShape.cons responseName hready
            (FieldCacheAbsorptionShape.refl_of_ready response hresponseReady)
            (FieldCacheFieldsAbsorptionShape.refl_of_ready source rest hrestReady)

  theorem FieldCacheListAbsorptionShape.refl_of_ready {ObjectRef : Type}
      (sourceValues? : Option (List (ResolverValue ObjectRef)))
      : ∀ values : List (FieldCacheValue ObjectRef),
          FieldCacheMergeReady (.list sourceValues? values)
          -> FieldCacheListAbsorptionShape sourceValues? values values
    | [], _hready =>
        FieldCacheListAbsorptionShape.nil
    | response :: rest, hready => by
        have hresponseReady : FieldCacheMergeReady response :=
          FieldCacheMergeReady.list_value sourceValues? (response :: rest) response
            hready (by simp)
        have hrestReady : FieldCacheMergeReady (.list sourceValues? rest) :=
          FieldCacheMergeReady.list sourceValues? rest (by
            intro restResponse hmem
            exact
              FieldCacheMergeReady.list_value sourceValues? (response :: rest)
                restResponse hready (by simp [hmem]))
        exact
          FieldCacheListAbsorptionShape.cons hready
            (FieldCacheAbsorptionShape.refl_of_ready response hresponseReady)
            (FieldCacheListAbsorptionShape.refl_of_ready sourceValues? rest hrestReady)
end

mutual
  theorem FieldCacheAbsorptionShape.merge_of_ready {ObjectRef : Type}
      : ∀ existing incoming : FieldCacheValue ObjectRef,
          FieldCacheMergeReady existing
          -> FieldCacheMergeReady incoming
          -> FieldCacheAbsorptionShape existing (mergeResponse existing incoming)
    | .object existingSource existingFields,
      .object incomingSource incomingFields,
      hexisting,
      hincoming => by
        simp [mergeResponse]
        exact
          FieldCacheAbsorptionShape.object
            (FieldCacheFieldsAbsorptionShape.mergeFields_of_ready existingSource
              incomingSource existingFields incomingFields hexisting hincoming)
    | .list existingSourceValues? existingValues,
      .list incomingSourceValues? incomingValues,
      hexisting,
      hincoming => by
        simp [mergeResponse]
        exact
          FieldCacheAbsorptionShape.list
            (FieldCacheListAbsorptionShape.mergeLists_of_ready existingSourceValues?
              incomingSourceValues? existingValues incomingValues hexisting hincoming)
    | .null, _, _hexisting, _hincoming => by
        simp [mergeResponse]
        exact FieldCacheAbsorptionShape.null
    | .scalar _value, .null, _hexisting, _hincoming => by
        simp [mergeResponse]
        exact FieldCacheAbsorptionShape.toNull _
    | .scalar value, .scalar _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using
          FieldCacheAbsorptionShape.refl_of_ready (.scalar value) hexisting
    | .scalar value, .object _source _fields, hexisting, _hincoming => by
        simpa [mergeResponse] using
          FieldCacheAbsorptionShape.refl_of_ready (.scalar value) hexisting
    | .scalar value, .list _sourceValues _values, hexisting, _hincoming => by
        simpa [mergeResponse] using
          FieldCacheAbsorptionShape.refl_of_ready (.scalar value) hexisting
    | .object _source _fields, .null, _hexisting, _hincoming => by
        simp [mergeResponse]
        exact FieldCacheAbsorptionShape.toNull _
    | .object source fields, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using
          FieldCacheAbsorptionShape.refl_of_ready (.object source fields) hexisting
    | .object source fields,
      .list sourceValues? values,
      hexisting,
      _hincoming => by
        simpa [mergeResponse] using
          FieldCacheAbsorptionShape.refl_of_ready (.object source fields) hexisting
    | .list _sourceValues _values, .null, _hexisting, _hincoming => by
        simp [mergeResponse]
        exact FieldCacheAbsorptionShape.toNull _
    | .list sourceValues? values, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using
          FieldCacheAbsorptionShape.refl_of_ready
            (.list sourceValues? values) hexisting
    | .list sourceValues? values, .object source fields, hexisting, _hincoming => by
        simpa [mergeResponse] using
          FieldCacheAbsorptionShape.refl_of_ready
            (.list sourceValues? values) hexisting
  termination_by existing incoming =>
    (sizeOf existing + sizeOf incoming, 0)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem FieldCacheFieldsAbsorptionShape.mergeField_of_ready {ObjectRef : Type}
      (source : ResolverValue ObjectRef)
      (responseName : Name) (incoming : FieldCacheValue ObjectRef)
      : ∀ fields : List (Name × FieldCacheValue ObjectRef),
          FieldCacheMergeReady (.object source fields)
          -> FieldCacheMergeReady incoming
          -> FieldCacheFieldsAbsorptionShape source fields
              (mergeResponseField responseName incoming fields)
    | [], hfields, hincoming => by
        apply FieldCacheFieldsAbsorptionShape.nil
        simpa [mergeResponseField] using
          mergeResponseField_object_cacheReady source responseName incoming []
            hfields hincoming
    | (fieldResponseName, existing) :: rest, hfields, hincoming => by
        have hexistingReady : FieldCacheMergeReady existing :=
          FieldCacheMergeReady.object_field source
            ((fieldResponseName, existing) :: rest) fieldResponseName existing
            hfields (by simp)
        have hrestReady : FieldCacheMergeReady (.object source rest) := by
          apply FieldCacheMergeReady.object
          · exact
              (FieldCacheMergeReady.object_keysNodup source
                ((fieldResponseName, existing) :: rest) hfields).tail
          · intro restName restResponse hmem
            exact
              FieldCacheMergeReady.object_field source
                ((fieldResponseName, existing) :: rest) restName restResponse
                hfields (by simp [hmem])
        by_cases h : fieldResponseName == responseName
        · have hmergedReady :
              FieldCacheMergeReady
                (.object source
                  ((fieldResponseName, mergeResponse existing incoming) :: rest)) := by
            simpa [mergeResponseField, h] using
              mergeResponseField_object_cacheReady source responseName incoming
                ((fieldResponseName, existing) :: rest) hfields hincoming
          simpa [mergeResponseField, h] using
            FieldCacheFieldsAbsorptionShape.cons fieldResponseName hmergedReady
              (FieldCacheAbsorptionShape.merge_of_ready existing incoming
                hexistingReady hincoming)
              (FieldCacheFieldsAbsorptionShape.refl_of_ready source rest hrestReady)
        · have hupdatedReady :
              FieldCacheMergeReady
                (.object source
                  ((fieldResponseName, existing) ::
                    mergeResponseField responseName incoming rest)) := by
            simpa [mergeResponseField, h] using
              mergeResponseField_object_cacheReady source responseName incoming
                ((fieldResponseName, existing) :: rest) hfields hincoming
          simpa [mergeResponseField, h] using
            FieldCacheFieldsAbsorptionShape.cons fieldResponseName hupdatedReady
              (FieldCacheAbsorptionShape.refl_of_ready existing hexistingReady)
              (FieldCacheFieldsAbsorptionShape.mergeField_of_ready source
                responseName incoming rest hrestReady hincoming)
  termination_by fields => (sizeOf incoming + sizeOf fields, 1)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem FieldCacheFieldsAbsorptionShape.mergeFields_of_ready {ObjectRef : Type}
      (existingSource incomingSource : ResolverValue ObjectRef)
      : ∀ existing incoming : List (Name × FieldCacheValue ObjectRef),
          FieldCacheMergeReady (.object existingSource existing)
          -> FieldCacheMergeReady (.object incomingSource incoming)
          -> FieldCacheFieldsAbsorptionShape existingSource existing
              (mergeResponseFields existing incoming)
    | existing, [], hexisting, _hincoming => by
        simpa [mergeResponseFields] using
          FieldCacheFieldsAbsorptionShape.refl_of_ready existingSource existing
            hexisting
    | existing,
      (responseName, incomingResponse) :: rest,
      hexisting,
      hincoming => by
        have hincomingResponse : FieldCacheMergeReady incomingResponse :=
          FieldCacheMergeReady.object_field incomingSource
            ((responseName, incomingResponse) :: rest) responseName incomingResponse
            hincoming (by simp)
        have hrestIncoming : FieldCacheMergeReady (.object incomingSource rest) := by
          apply FieldCacheMergeReady.object
          · exact
              (FieldCacheMergeReady.object_keysNodup incomingSource
                ((responseName, incomingResponse) :: rest) hincoming).tail
          · intro restName restResponse hmem
            exact
              FieldCacheMergeReady.object_field incomingSource
                ((responseName, incomingResponse) :: rest) restName restResponse
                hincoming (by simp [hmem])
        have hstep :=
          FieldCacheFieldsAbsorptionShape.mergeField_of_ready existingSource
            responseName incomingResponse existing hexisting hincomingResponse
        have hupdatedReady := hstep.output_ready
        have hrest :=
          FieldCacheFieldsAbsorptionShape.mergeFields_of_ready existingSource
            incomingSource (mergeResponseField responseName incomingResponse existing)
            rest hupdatedReady hrestIncoming
        simp [mergeResponseFields]
        exact FieldCacheFieldsAbsorptionShape.trans hstep hrest
  termination_by existing incoming =>
    (sizeOf existing + sizeOf incoming, incoming.length + 2)
  decreasing_by
    all_goals
      simp_wf
      try
        have hsize :=
          sizeOf_mergeResponseField_le responseName incomingResponse existing
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem FieldCacheListAbsorptionShape.mergeLists_of_ready {ObjectRef : Type}
      (existingSourceValues? incomingSourceValues?
        : Option (List (ResolverValue ObjectRef)))
      : ∀ existing incoming : List (FieldCacheValue ObjectRef),
          FieldCacheMergeReady (.list existingSourceValues? existing)
          -> FieldCacheMergeReady (.list incomingSourceValues? incoming)
          -> FieldCacheListAbsorptionShape existingSourceValues? existing
              (mergeResponseLists existing incoming)
    | [], _incoming, _hexisting, _hincoming => by
        simpa only [mergeResponseLists] using
          (FieldCacheListAbsorptionShape.nil
            : FieldCacheListAbsorptionShape existingSourceValues? [] [])
    | existing, [], hexisting, _hincoming => by
        cases existing with
        | nil =>
            simpa only [mergeResponseLists] using
              (FieldCacheListAbsorptionShape.nil
                : FieldCacheListAbsorptionShape existingSourceValues? [] [])
        | cons response rest =>
            simpa [mergeResponseLists] using
              FieldCacheListAbsorptionShape.refl_of_ready existingSourceValues?
                (response :: rest) hexisting
    | existing :: existingRest,
      incoming :: incomingRest,
      hexisting,
      hincoming => by
        have hexistingHead : FieldCacheMergeReady existing :=
          FieldCacheMergeReady.list_value existingSourceValues?
            (existing :: existingRest) existing hexisting (by simp)
        have hincomingHead : FieldCacheMergeReady incoming :=
          FieldCacheMergeReady.list_value incomingSourceValues?
            (incoming :: incomingRest) incoming hincoming (by simp)
        have hexistingRest :
            FieldCacheMergeReady (.list existingSourceValues? existingRest) :=
          FieldCacheMergeReady.list existingSourceValues? existingRest (by
            intro response hmem
            exact
              FieldCacheMergeReady.list_value existingSourceValues?
                (existing :: existingRest) response hexisting (by simp [hmem]))
        have hincomingRest :
            FieldCacheMergeReady (.list incomingSourceValues? incomingRest) :=
          FieldCacheMergeReady.list incomingSourceValues? incomingRest (by
            intro response hmem
            exact
              FieldCacheMergeReady.list_value incomingSourceValues?
                (incoming :: incomingRest) response hincoming (by simp [hmem]))
        have hmergedReady :=
          mergeResponseLists_cacheReady existingSourceValues? incomingSourceValues?
            (existing :: existingRest) (incoming :: incomingRest) hexisting
            hincoming
        have hmergedReady' :
            FieldCacheMergeReady
              (.list existingSourceValues?
                (mergeResponse existing incoming ::
                  mergeResponseLists existingRest incomingRest)) := by
          simpa only [mergeResponseLists] using hmergedReady
        simpa [mergeResponseLists] using
          FieldCacheListAbsorptionShape.cons hmergedReady'
            (FieldCacheAbsorptionShape.merge_of_ready existing incoming
              hexistingHead hincomingHead)
            (FieldCacheListAbsorptionShape.mergeLists_of_ready
              existingSourceValues? incomingSourceValues? existingRest incomingRest
              hexistingRest hincomingRest)
  termination_by existing incoming =>
    (sizeOf existing + sizeOf incoming, incoming.length + 2)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

theorem FieldCacheAbsorbs.merge_of_ready {ObjectRef : Type}
    (existing incoming : FieldCacheValue ObjectRef)
    : FieldCacheMergeReady existing
      -> FieldCacheMergeReady incoming
      -> FieldCacheAbsorbs existing (mergeResponse existing incoming) := by
  intro hexisting hincoming
  exact
    FieldCacheAbsorptionShape.to_absorbs
      (FieldCacheAbsorptionShape.merge_of_ready existing incoming hexisting hincoming)

mutual
  theorem FieldCacheSourceAligned.of_absorptionShape {ObjectRef : Type}
      {source : ResolverValue ObjectRef}
      {base output : FieldCacheValue ObjectRef}
      : FieldCacheSourceAligned source base
        -> FieldCacheAbsorptionShape base output
        -> FieldCacheSourceAligned source output := by
    intro haligned hshape
    cases hshape with
    | null => exact haligned
    | toNull _base => exact FieldCacheSourceAligned.null source
    | scalar value =>
        cases haligned
        exact FieldCacheSourceAligned.scalar value
    | object hfields =>
        cases haligned with
        | object _source _baseFields =>
            exact FieldCacheSourceAligned.object source _
    | list hvalues =>
        cases haligned with
        | cachedList sourceValues baseValues halignedValues =>
            exact
              FieldCacheSourceAligned.cachedList sourceValues _
                (FieldCacheSourcesAligned.of_listAbsorptionShape
                  halignedValues hvalues)
        | finalList sourceValues baseValues halignedValues =>
            exact
              FieldCacheSourceAligned.finalList sourceValues _
                (FieldCacheSourcesAligned.of_listAbsorptionShape halignedValues
                  hvalues)

  theorem FieldCacheSourcesAligned.of_listAbsorptionShape {ObjectRef : Type}
      : ∀ {sourceValues? : Option (List (ResolverValue ObjectRef))}
          {sourceValues : List (ResolverValue ObjectRef)}
          {base output : List (FieldCacheValue ObjectRef)},
          FieldCacheSourcesAligned sourceValues base
          -> FieldCacheListAbsorptionShape sourceValues? base output
          -> FieldCacheSourcesAligned sourceValues output
    | _sourceValues?,
      [],
      [],
      [],
      FieldCacheSourcesAligned.nil,
      FieldCacheListAbsorptionShape.nil =>
        FieldCacheSourcesAligned.nil
    | sourceValues?,
      _source :: _sourceRest,
      _base :: _baseRest,
      _output :: _outputRest,
      FieldCacheSourcesAligned.cons haligned halignedRest,
      FieldCacheListAbsorptionShape.cons _hready hshape hshapeRest =>
        FieldCacheSourcesAligned.cons
          (FieldCacheSourceAligned.of_absorptionShape haligned hshape)
          (FieldCacheSourcesAligned.of_listAbsorptionShape
            (sourceValues? := sourceValues?) halignedRest
            hshapeRest)
end

end ExecutionUngrouped
end Algorithms

end GraphQL
