import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection
import Proofs.GraphQL.Execution.FieldCollection

/-!
Runtime fragment-application facts for ground-type normalization semantics.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectRef : Type}

theorem executeSelectionSet_inlineFragment_some_directiveFree_skip
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source rest := by
  intro hskip
  have hcollect :=
    collectFields_inlineFragment_some_directiveFree_skip_eq schema
      variableValues parentType typeCondition source selectionSet rest
      hskip
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hcollect]

theorem executeSelectionSet_inlineFragment_none_directiveFree_flatten
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.executeSelectionSet schema resolvers variableValues depth
        parentType source
        (Selection.inlineFragment none [] selectionSet :: rest)
      = Execution.executeSelectionSet schema resolvers variableValues depth
          parentType source (selectionSet ++ rest) := by
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    collectFields_inlineFragment_none_directiveFree_flatten]

theorem executeSelectionSet_inlineFragment_some_directiveFree_apply_flatten
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType typeCondition : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source (selectionSet ++ rest) := by
  intro happly
  simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    collectFields_inlineFragment_some_directiveFree_apply_flatten, happly]

theorem lookupType_name_eq (schema : Schema) {typeName : Name}
    {typeDefinition : TypeDefinition}
    : schema.lookupType typeName = some typeDefinition
      -> typeDefinition.name = typeName := by
  intro hlookup
  have hmatch := List.find?_some hlookup
  simpa [Schema.lookupType] using hmatch

theorem typeIncludesObjectBool_eq_of_objectTypeNameBool_true
    (schema : Schema) {typeName runtimeType : Name}
    : objectTypeNameBool schema typeName = true
      -> schema.typeIncludesObjectBool typeName runtimeType = true
      -> runtimeType = typeName := by
  intro hobject hinclude
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = typeName :=
            lookupType_name_eq schema hlookup
          simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
            hlookup, hname] at hinclude
          exact hinclude
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_true_of_typesOverlapBool_true_of_object_source
    (schema : Schema) {parentType typeCondition : Name}
    {source : Execution.ResolverValue ObjectRef}
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> schema.typesOverlapBool parentType typeCondition = true
      -> Execution.doesFragmentTypeApplyBool schema parentType source typeCondition
          = true := by
  intro hobject hsource hoverlap
  rcases hsource with ⟨runtimeType, ref, hsourceEq, hparent⟩
  subst source
  have hruntime :
      runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hparent
  subst runtimeType
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType parentType with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = parentType :=
            lookupType_name_eq schema hlookup
          unfold Schema.typesOverlapBool at hoverlap
          simp [Schema.getPossibleTypes, hlookup, hname] at hoverlap
          simpa [Execution.doesFragmentTypeApplyBool,
            Execution.runtimeObjectType?] using hoverlap
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_false_of_typesOverlapBool_false
    (schema : Schema) {parentType typeCondition runtimeType : Name} (ref : ObjectRef)
    : schema.typeIncludesObjectBool parentType runtimeType = true
      -> schema.typesOverlapBool parentType typeCondition = false
      -> Execution.doesFragmentTypeApplyBool schema parentType
            (.object runtimeType ref) typeCondition
          = false := by
  intro hparent hoverlap
  unfold Execution.doesFragmentTypeApplyBool
  cases hcondition :
      schema.typeIncludesObjectBool typeCondition runtimeType
  · simp [Execution.runtimeObjectType?, hcondition]
  · have hparentMem :
        runtimeType ∈ schema.getPossibleTypes parentType := by
      exact List.contains_iff_mem.mp hparent
    have hoverlapTrue :
        schema.typesOverlapBool parentType typeCondition = true := by
      unfold Schema.typesOverlapBool
      exact List.any_eq_true.mpr
        ⟨runtimeType, hparentMem, hcondition⟩
    rw [hoverlap] at hoverlapTrue
    contradiction

theorem rootSourceAppliesBool_true_object (schema : Schema) (operation : Operation)
    (source : Execution.ResolverValue ObjectRef)
    : Execution.rootSourceAppliesBool schema operation source = true
      -> ∃ runtimeType ref,
          source = .object runtimeType ref
          ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType
            = true := by
    intro hroot
    cases source with
    | null =>
        simp [Execution.rootSourceAppliesBool,
          Execution.runtimeObjectType?] at hroot
    | scalar value =>
        simp [Execution.rootSourceAppliesBool,
          Execution.runtimeObjectType?] at hroot
    | object runtimeType ref =>
        simp [Execution.rootSourceAppliesBool,
          Execution.runtimeObjectType?] at hroot
        exact ⟨runtimeType, ref, rfl, hroot⟩
    | list values =>
        simp [Execution.rootSourceAppliesBool,
          Execution.runtimeObjectType?] at hroot

theorem doesFragmentTypeApplyBool_false_of_typesOverlapBool_false_of_source
    (schema : Schema) {parentType typeCondition : Name}
    {source : Execution.ResolverValue ObjectRef}
    : (∃ runtimeType ref,
        source = .object runtimeType ref
        ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> schema.typesOverlapBool parentType typeCondition = false
      -> Execution.doesFragmentTypeApplyBool schema parentType source typeCondition
          = false := by
  intro hsource hoverlap
  rcases hsource with ⟨runtimeType, ref, hsourceEq, hparent⟩
  subst source
  exact doesFragmentTypeApplyBool_false_of_typesOverlapBool_false schema
    (ref := ref) hparent hoverlap

theorem objectTypeNameBool_eq_true_of_objectType (schema : Schema) {typeName : Name}
    : schema.objectType typeName -> objectTypeNameBool schema typeName = true := by
  intro hobject
  rcases hobject with ⟨objectType, hlookup⟩
  simp [objectTypeNameBool, hlookup]

theorem typeIncludesObjectBool_self_of_objectTypeNameBool
    (schema : Schema) {typeName : Name}
    : objectTypeNameBool schema typeName = true
      -> schema.typeIncludesObjectBool typeName typeName = true := by
  intro hobject
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = typeName :=
            lookupType_name_eq schema hlookup
          simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
            hlookup, hname]
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_object_self
    (schema : Schema) {runtimeType : Name} (ref : ObjectRef)
    : objectTypeNameBool schema runtimeType = true
      -> Execution.doesFragmentTypeApplyBool schema runtimeType
            (.object runtimeType ref)
            runtimeType
          = true := by
  intro hobject
  simp [Execution.doesFragmentTypeApplyBool, Execution.runtimeObjectType?,
    typeIncludesObjectBool_self_of_objectTypeNameBool schema hobject]

theorem doesFragmentTypeApplyBool_object_other_false
    (schema : Schema) {runtimeType objectType : Name} (ref : ObjectRef)
    : objectTypeNameBool schema objectType = true
      -> objectType ≠ runtimeType
      -> Execution.doesFragmentTypeApplyBool schema runtimeType
            (.object runtimeType ref)
            objectType
          = false := by
  intro hobject hne
  unfold Execution.doesFragmentTypeApplyBool
  cases hinclude :
      schema.typeIncludesObjectBool objectType runtimeType
  · simp [Execution.runtimeObjectType?, hinclude]
  · have heq :
        runtimeType = objectType :=
      typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
        hinclude
    exact False.elim (hne heq.symm)

end GroundTypeNormalization

end NormalForm

end GraphQL
