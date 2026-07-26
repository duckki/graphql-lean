import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.InlineFragmentSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality

/-!
Abstract return grounding semantics for ground-type normalization.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectRef : Type}

theorem collectFields_possibleTypeFragments_not_mem_eq_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes -> objectTypeNameBool schema objectType = true)
      -> runtimeType ∉ possibleTypes
      -> Execution.collectFields schema variableValues runtimeType
            (.object runtimeType ref)
            (possibleTypes.map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (normalizeSelectionSet schema objectType selectionSet)))
          = [] := by
  intro hobjects hnotin
  induction possibleTypes with
  | nil =>
      simp [Execution.collectFields]
  | cons objectType rest ih =>
      have hobject : objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hne : objectType ≠ runtimeType := by
        intro heq
        subst objectType
        exact hnotin (by simp)
      have hrestNotin : runtimeType ∉ rest := by
        intro hmem
        exact hnotin (by simp [hmem])
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      rw [List.map_cons]
      rw [collectFields_inlineFragment_some_directiveFree_skip_eq]
      · exact ih hrestObjects hrestNotin
      · exact doesFragmentTypeApplyBool_object_other_false schema
          (ref := ref)
          hobject hne

theorem executeSelectionSet_append_possibleTypeFragments_not_mem
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name)
    (selectionSet suffix : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes -> objectTypeNameBool schema objectType = true)
      -> runtimeType ∉ possibleTypes
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            runtimeType (.object runtimeType ref)
            (suffix
              ++ possibleTypes.map
                  (fun objectType =>
                    Selection.inlineFragment (some objectType) []
                      (normalizeSelectionSet schema objectType selectionSet)))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              runtimeType (.object runtimeType ref) suffix := by
  intro hobjects hnotin
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    ]
  rw [collectFields_append]
  rw [collectFields_possibleTypeFragments_not_mem_eq_nil schema
    variableValues runtimeType (ref := ref) possibleTypes selectionSet hobjects
    hnotin]
  simp [Execution.mergeExecutableGroups_nil_right]

theorem collectFields_possibleTypeNormalizations_not_mem_eq_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes -> objectTypeNameBool schema objectType = true)
      -> runtimeType ∉ possibleTypes
      -> Execution.collectFields schema variableValues runtimeType
            (.object runtimeType ref)
            (possibleTypeNormalizations schema possibleTypes selectionSet)
          = [] := by
  intro hobjects hnotin
  induction possibleTypes with
  | nil =>
      simp [possibleTypeNormalizations, Execution.collectFields]
  | cons objectType rest ih =>
      have hobject : objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hne : objectType ≠ runtimeType := by
        intro heq
        subst objectType
        exact hnotin (by simp)
      have hrestNotin : runtimeType ∉ rest := by
        intro hmem
        exact hnotin (by simp [hmem])
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          simpa [possibleTypeNormalizations, hnormalized] using
            ih hrestObjects hrestNotin
      | cons selection restNormalized =>
          rw [show possibleTypeNormalizations schema (objectType :: rest)
              selectionSet =
              Selection.inlineFragment (some objectType) []
                (selection :: restNormalized)
                :: possibleTypeNormalizations schema rest selectionSet by
            simp [possibleTypeNormalizations, hnormalized]]
          rw [collectFields_inlineFragment_some_directiveFree_skip_eq]
          · exact ih hrestObjects hrestNotin
          · exact doesFragmentTypeApplyBool_object_other_false schema
              (ref := ref)
              hobject hne

theorem executeSelectionSet_append_possibleTypeNormalizations_not_mem
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name)
    (selectionSet suffix : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes -> objectTypeNameBool schema objectType = true)
      -> runtimeType ∉ possibleTypes
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            runtimeType (.object runtimeType ref)
            (suffix ++ possibleTypeNormalizations schema possibleTypes selectionSet)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              runtimeType (.object runtimeType ref) suffix := by
  intro hobjects hnotin
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    ]
  rw [collectFields_append]
  rw [collectFields_possibleTypeNormalizations_not_mem_eq_nil schema
    variableValues runtimeType (ref := ref) possibleTypes selectionSet hobjects
    hnotin]
  simp [Execution.mergeExecutableGroups_nil_right]

def completeValueSelectionSetField (parentType : Name) (selectionSet : List Selection)
    : Execution.ExecutableField :=
  {
    parentType := parentType,
    responseName := "",
    fieldName := "",
    arguments := [],
    selectionSet := selectionSet
  }

theorem executeSelectionSet_possibleTypeFragments_runtime_branch
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes -> objectTypeNameBool schema objectType = true)
      -> possibleTypes.Nodup
      -> runtimeType ∈ possibleTypes
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            runtimeType (.object runtimeType ref)
            (normalizeSelectionSet schema runtimeType selectionSet)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              runtimeType (.object runtimeType ref) selectionSet
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            runtimeType (.object runtimeType ref)
            (possibleTypes.map
              (fun objectType =>
                Selection.inlineFragment (some objectType) []
                  (normalizeSelectionSet schema objectType selectionSet)))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              runtimeType (.object runtimeType ref) selectionSet := by
  intro hobjects hnodup hmem hrecursive
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := by
        exact hnodup.tail
      rw [List.map_cons]
      cases hhead : objectType == runtimeType
      · have hne : objectType ≠ runtimeType := by
          intro heq
          subst objectType
          simp at hhead
        have hskip :
            Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType ref) objectType = false :=
          doesFragmentTypeApplyBool_object_other_false schema
            (ref := ref)
            hobject hne
        rw [executeSelectionSet_inlineFragment_some_directiveFree_skip
          schema resolvers variableValues depth runtimeType objectType
          (.object runtimeType ref)
          (normalizeSelectionSet schema objectType selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType selectionSet)))
          (by simpa [] using hskip)]
        have hrestMem : runtimeType ∈ rest := by
          cases List.mem_cons.mp hmem with
          | inl hmemHead =>
              exact False.elim (hne hmemHead.symm)
          | inr hmemRest => exact hmemRest
        exact ih hrestObjects hrestNodup hrestMem
      · have heq : objectType = runtimeType :=
          beq_iff_eq.mp hhead
        subst objectType
        have hrestNotin : runtimeType ∉ rest := by
          exact (List.nodup_cons.mp hnodup).1
        have happly :
            Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType ref) runtimeType = true :=
          doesFragmentTypeApplyBool_object_self schema (ref := ref) hobject
        rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
          schema resolvers variableValues depth runtimeType runtimeType
          (.object runtimeType ref)
          (normalizeSelectionSet schema runtimeType selectionSet)
          (rest.map
            (fun objectType =>
              Selection.inlineFragment (some objectType) []
                (normalizeSelectionSet schema objectType selectionSet)))
          (by simpa [] using happly)]
        rw [executeSelectionSet_append_possibleTypeFragments_not_mem schema
          resolvers variableValues depth runtimeType (ref := ref) rest
          selectionSet
          (normalizeSelectionSet schema runtimeType selectionSet)
          hrestObjects hrestNotin]
        exact hrecursive

theorem executeSelectionSet_possibleTypeNormalizations_runtime_branch
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    : (∀ objectType,
        objectType ∈ possibleTypes -> objectTypeNameBool schema objectType = true)
      -> possibleTypes.Nodup
      -> runtimeType ∈ possibleTypes
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            runtimeType (.object runtimeType ref)
            (normalizeSelectionSet schema runtimeType selectionSet)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              runtimeType (.object runtimeType ref) selectionSet
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            runtimeType (.object runtimeType ref)
            (possibleTypeNormalizations schema possibleTypes selectionSet)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              runtimeType (.object runtimeType ref) selectionSet := by
  intro hobjects hnodup hmem hrecursive
  induction possibleTypes with
  | nil =>
      cases hmem
  | cons objectType rest ih =>
      have hobject : objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects :
          ∀ candidate, candidate ∈ rest ->
            objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := by
        exact hnodup.tail
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have hnilEq :
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (.object runtimeType ref) []
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (.object runtimeType ref)
                  selectionSet := by
              simpa [hnormalized] using hrecursive
            have hrestEq :
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (.object runtimeType ref)
                  (possibleTypeNormalizations schema rest selectionSet)
                =
                Execution.executeSelectionSet schema resolvers variableValues
                  depth runtimeType (.object runtimeType ref) [] := by
              simpa using
                executeSelectionSet_append_possibleTypeNormalizations_not_mem
                  schema resolvers variableValues depth runtimeType (ref := ref)
                  rest selectionSet [] hrestObjects hrestNotin
            simpa [possibleTypeNormalizations, hnormalized] using
              hrestEq.trans hnilEq
          · have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hmemHead => exact False.elim (heq hmemHead.symm)
              | inr hmemRest => exact hmemRest
            simpa [possibleTypeNormalizations, hnormalized] using
              ih hrestObjects hrestNodup hrestMem
      | cons selection restNormalized =>
          rw [show possibleTypeNormalizations schema (objectType :: rest)
              selectionSet =
              Selection.inlineFragment (some objectType) []
                (selection :: restNormalized)
                :: possibleTypeNormalizations schema rest selectionSet by
            simp [possibleTypeNormalizations, hnormalized]]
          cases hhead : objectType == runtimeType
          · have hne : objectType ≠ runtimeType := by
              intro heq
              subst objectType
              simp at hhead
            have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType ref) objectType = false :=
              doesFragmentTypeApplyBool_object_other_false schema
                (ref := ref)
                hobject hne
            rw [executeSelectionSet_inlineFragment_some_directiveFree_skip
              schema resolvers variableValues depth runtimeType objectType
              (.object runtimeType ref)
              (selection :: restNormalized)
              (possibleTypeNormalizations schema rest selectionSet)
              (by simpa [] using hskip)]
            have hrestMem : runtimeType ∈ rest := by
              cases List.mem_cons.mp hmem with
              | inl hmemHead =>
                  exact False.elim (hne hmemHead.symm)
              | inr hmemRest => exact hmemRest
            exact ih hrestObjects hrestNodup hrestMem
          · have heq : objectType = runtimeType :=
              beq_iff_eq.mp hhead
            subst objectType
            have hrestNotin : runtimeType ∉ rest := by
              exact (List.nodup_cons.mp hnodup).1
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType ref) runtimeType = true :=
              doesFragmentTypeApplyBool_object_self schema (ref := ref) hobject
            rw [executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
              schema resolvers variableValues depth runtimeType runtimeType
              (.object runtimeType ref)
              (selection :: restNormalized)
              (possibleTypeNormalizations schema rest selectionSet)
              (by simpa [] using happly)]
            rw [executeSelectionSet_append_possibleTypeNormalizations_not_mem
              schema resolvers variableValues depth runtimeType (ref := ref) rest
              selectionSet (selection :: restNormalized) hrestObjects
              hrestNotin]
            simpa [hnormalized] using hrecursive

theorem completeValue_possibleTypeFragments_eq_of_child_object_lt
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ depth childType selectionSet value,
        (∀ childDepth runtimeType ref,
          childDepth < depth
          -> runtimeType ∈ schema.getPossibleTypes childType
          -> Execution.executeSelectionSet schema resolvers variableValues
                childDepth runtimeType (.object runtimeType ref)
                (normalizeSelectionSet schema runtimeType selectionSet)
              = Execution.executeSelectionSet schema resolvers variableValues
                  childDepth runtimeType (.object runtimeType ref)
                  selectionSet)
        -> Execution.completeValue schema resolvers variableValues depth childType
              [completeValueSelectionSetField childType
                ((schema.getPossibleTypes childType).map
                  (fun objectType =>
                    Selection.inlineFragment (some objectType) []
                      (normalizeSelectionSet schema objectType selectionSet)))]
              value
            = Execution.completeValue schema resolvers variableValues depth
                childType [completeValueSelectionSetField childType selectionSet] value
  | 0, _childType, _selectionSet, _value, _hrecursive => by
      simp [Execution.completeValue]
  | depth + 1, childType, selectionSet, value, hrecursive => by
      cases value with
      | null =>
          simp [Execution.completeValue]
        | scalar value =>
            simp [Execution.completeValue]
        | object runtimeType ref =>
          by_cases hinclude :
              schema.typeIncludesObjectBool childType runtimeType = true
          · have hmem :
                runtimeType ∈ schema.getPossibleTypes childType := by
              exact List.contains_iff_mem.mp hinclude
            have hobjects :
                ∀ objectType, objectType ∈ schema.getPossibleTypes childType ->
                  objectTypeNameBool schema objectType = true := by
              intro objectType hobjectType
              exact objectTypeNameBool_eq_true_of_objectType schema
                (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                  hschema childType objectType hobjectType)
            have hbranch :=
              executeSelectionSet_possibleTypeFragments_runtime_branch
                schema resolvers variableValues depth runtimeType
                (ref := ref)
                (schema.getPossibleTypes childType) selectionSet hobjects
                (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup
                  hschema childType)
                hmem
                (hrecursive depth runtimeType ref
                  (Nat.lt_succ_self depth) hmem)
            simp [Execution.completeValue, hinclude]
            exact congrArg
              (Execution.catchBubbleAsNull Execution.ResponseValue.object)
              (by
                simpa [Execution.executeSelectionSet,
                  Execution.executeRootSelectionSet, Execution.collectSubfields,
                  completeValueSelectionSetField] using hbranch)
          · have hfalse :
                schema.typeIncludesObjectBool childType runtimeType = false := by
              cases hmatch :
                  schema.typeIncludesObjectBool childType runtimeType
              · rfl
              · contradiction
            simp [Execution.completeValue, hfalse]
      | list values =>
          simp [Execution.completeValue]

end GroundTypeNormalization

end NormalForm

end GraphQL
