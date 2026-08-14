import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Probes

/-!
Tagged probe resolvers for head-discrimination proofs.

The root source uses `none`. Once a root field is resolved, its selected tag is
stored in the object reference and propagated through composite children. Leaf
values expose the tag as a scalar, so field-head differences can be observed
inside arbitrary composite return values without making unrelated sibling fields
fail.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive FieldPairProbeTag where
  | left
  | right
  | filler
deriving DecidableEq, Repr

def FieldPairProbeTag.scalar : FieldPairProbeTag -> String
  | .left => "left"
  | .right => "right"
  | .filler => "filler"

def fieldProbeTarget
    (targetParent targetField : Name) (targetArguments : List Argument)
    (parentType fieldName : Name) (arguments : List Argument)
    : Prop :=
  parentType = targetParent
  ∧ fieldName = targetField
  ∧ Argument.argumentsEquivalent arguments targetArguments

theorem fieldProbeTarget_iff_of_argumentsEquivalent
    (targetParent targetField : Name) (targetArguments : List Argument)
    (parentType fieldName : Name)
    (firstArguments laterArguments : List Argument)
    : Argument.argumentsEquivalent firstArguments laterArguments
      -> (fieldProbeTarget targetParent targetField targetArguments parentType
            fieldName firstArguments
          ↔ fieldProbeTarget targetParent targetField targetArguments parentType
              fieldName laterArguments) := by
  intro harguments
  have hiff :
      Argument.argumentsEquivalent firstArguments targetArguments
        ↔ Argument.argumentsEquivalent laterArguments targetArguments := by
    constructor
    · intro hfirst
      exact argumentsEquivalent_trans
        (FieldMerge.argumentsEquivalent_symm harguments) hfirst
    · intro hlater
      exact argumentsEquivalent_trans harguments hlater
  constructor
  · intro htarget
    exact ⟨htarget.1, htarget.2.1, hiff.mp htarget.2.2⟩
  · intro htarget
    exact ⟨htarget.1, htarget.2.1, hiff.mpr htarget.2.2⟩

noncomputable def fieldPairProbeTag
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (parentType fieldName : Name) (arguments : List Argument)
    : FieldPairProbeTag := by
  classical
  exact
    if fieldProbeTarget targetParent leftField leftArguments parentType
        fieldName arguments then
      .left
    else if fieldProbeTarget targetParent rightField rightArguments parentType
        fieldName arguments then
      .right
    else
      .filler

theorem fieldPairProbeTag_eq_of_argumentsEquivalent
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    (parentType fieldName : Name)
    (firstArguments laterArguments : List Argument)
    : Argument.argumentsEquivalent firstArguments laterArguments
      -> fieldPairProbeTag targetParent leftField rightField leftArguments
            rightArguments parentType fieldName firstArguments
          = fieldPairProbeTag targetParent leftField rightField leftArguments
              rightArguments parentType fieldName laterArguments := by
  intro harguments
  classical
  have hleftIff :=
    fieldProbeTarget_iff_of_argumentsEquivalent targetParent leftField
      leftArguments parentType fieldName firstArguments laterArguments
      harguments
  have hrightIff :=
    fieldProbeTarget_iff_of_argumentsEquivalent targetParent rightField
      rightArguments parentType fieldName firstArguments laterArguments
      harguments
  by_cases hfirstLeft :
      fieldProbeTarget targetParent leftField leftArguments parentType
        fieldName firstArguments
  · have hlaterLeft :
        fieldProbeTarget targetParent leftField leftArguments parentType
          fieldName laterArguments :=
      hleftIff.mp hfirstLeft
    simp [fieldPairProbeTag, hfirstLeft, hlaterLeft]
  · have hlaterLeft :
        ¬ fieldProbeTarget targetParent leftField leftArguments parentType
          fieldName laterArguments := by
      intro hlater
      exact hfirstLeft (hleftIff.mpr hlater)
    by_cases hfirstRight :
        fieldProbeTarget targetParent rightField rightArguments parentType
          fieldName firstArguments
    · have hlaterRight :
          fieldProbeTarget targetParent rightField rightArguments parentType
            fieldName laterArguments :=
        hrightIff.mp hfirstRight
      simp [fieldPairProbeTag, hfirstLeft, hlaterLeft, hfirstRight,
        hlaterRight]
    · have hlaterRight :
          ¬ fieldProbeTarget targetParent rightField rightArguments parentType
            fieldName laterArguments := by
        intro hlater
        exact hfirstRight (hrightIff.mpr hlater)
      simp [fieldPairProbeTag, hfirstLeft, hlaterLeft, hfirstRight,
        hlaterRight]

def fieldPairProbeResolverValue
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name) (tag : FieldPairProbeTag)
    : TypeRef -> Execution.ResolverValue (Option FieldPairProbeTag)
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName (some tag)
        else
          match abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet with
          | some runtimeType => .object runtimeType (some tag)
          | none => .object typeName (some tag)
      else
        .scalar tag.scalar
  | .list inner =>
      .list
        [fieldPairProbeResolverValue schema rootSelectionSet parentType
          fieldName tag inner]
  | .nonNull inner =>
      fieldPairProbeResolverValue schema rootSelectionSet parentType fieldName tag inner

theorem fieldPairProbeResolverValue_leaf_eq_leafProbeResolverValue
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name) (tag : FieldPairProbeTag)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = false
        -> fieldPairProbeResolverValue schema rootSelectionSet parentType
              fieldName tag outputType
            = leafProbeResolverValue outputType tag.scalar
  | .named typeName, hleaf => by
      have hleafNamed :
          (TypeRef.named typeName).isCompositeBool schema = false := by
        simpa [TypeRef.namedType] using hleaf
      simp [fieldPairProbeResolverValue, leafProbeResolverValue, hleafNamed]
  | .list inner, hleaf => by
      have hinner :
          fieldPairProbeResolverValue schema rootSelectionSet parentType
              fieldName tag inner
            =
            leafProbeResolverValue inner tag.scalar :=
        fieldPairProbeResolverValue_leaf_eq_leafProbeResolverValue schema
          rootSelectionSet parentType fieldName tag inner
          (by simpa [TypeRef.namedType] using hleaf)
      simp [fieldPairProbeResolverValue, leafProbeResolverValue, hinner]
  | .nonNull inner, hleaf => by
      exact
        fieldPairProbeResolverValue_leaf_eq_leafProbeResolverValue schema
          rootSelectionSet parentType fieldName tag inner
          (by simpa [TypeRef.namedType] using hleaf)

theorem fieldPairProbeResolverValue_object_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name) (tag : FieldPairProbeTag)
    : ∀ outputType,
        objectTypeNameBool schema outputType.namedType = true
        -> fieldPairProbeResolverValue schema rootSelectionSet parentType
              fieldName tag outputType
            = objectProbeResolverValueWithRuntime outputType.namedType
                (some tag) outputType
  | .named typeName, hobject => by
      have hobjectNamed :
          objectTypeNameBool schema typeName = true := by
        simpa [TypeRef.namedType] using hobject
      have hcomposite :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        unfold objectTypeNameBool at hobjectNamed
        unfold TypeRef.isCompositeBool TypeRef.namedType
        cases hlookup : schema.lookupType typeName with
        | none =>
            simp [hlookup] at hobjectNamed
        | some typeDefinition =>
            cases typeDefinition <;> simp [hlookup] at hobjectNamed ⊢
      simp [fieldPairProbeResolverValue, objectProbeResolverValueWithRuntime,
        TypeRef.namedType, hcomposite, hobjectNamed]
  | .list inner, hobject => by
      have hinner :=
        fieldPairProbeResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName tag inner
          (by simpa [TypeRef.namedType] using hobject)
      simpa [fieldPairProbeResolverValue, objectProbeResolverValueWithRuntime,
        TypeRef.namedType] using hinner
  | .nonNull inner, hobject => by
      exact
        fieldPairProbeResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName tag inner
          (by simpa [TypeRef.namedType] using hobject)

theorem fieldPairProbeResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (tag : FieldPairProbeTag)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = true
        -> objectTypeNameBool schema outputType.namedType = false
        -> abstractRuntimeForFieldDeep? schema parentType fieldName parentType
              rootSelectionSet
            = some runtimeType
        -> fieldPairProbeResolverValue schema rootSelectionSet parentType
              fieldName tag outputType
            = objectProbeResolverValueWithRuntime runtimeType (some tag) outputType
  | .named typeName, hcomposite, hnonObject, hruntime => by
      have hcompositeNamed :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        simpa [TypeRef.namedType] using hcomposite
      have hnonObjectNamed :
          objectTypeNameBool schema typeName = false := by
        simpa [TypeRef.namedType] using hnonObject
      simp [fieldPairProbeResolverValue, objectProbeResolverValueWithRuntime,
        hcompositeNamed, hnonObjectNamed, hruntime]
  | .list inner, hcomposite, hnonObject, hruntime => by
      have hinner :=
        fieldPairProbeResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName runtimeType tag inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject) hruntime
      simpa [fieldPairProbeResolverValue, objectProbeResolverValueWithRuntime,
        TypeRef.namedType] using hinner
  | .nonNull inner, hcomposite, hnonObject, hruntime => by
      exact
        fieldPairProbeResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName runtimeType tag inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject) hruntime

theorem fieldPairProbeResolverValue_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (tag : FieldPairProbeTag)
    (outputType : TypeRef)
    : ((objectTypeNameBool schema outputType.namedType = true
          ∧ runtimeType = outputType.namedType)
        ∨ ((TypeRef.named outputType.namedType).isCompositeBool schema = true
            ∧ objectTypeNameBool schema outputType.namedType = false
            ∧ abstractRuntimeForFieldDeep? schema parentType fieldName parentType
                rootSelectionSet
              = some runtimeType))
      -> fieldPairProbeResolverValue schema rootSelectionSet parentType
            fieldName tag outputType
          = objectProbeResolverValueWithRuntime runtimeType (some tag) outputType := by
  intro hcase
  rcases hcase with hobject | habstract
  · rcases hobject with ⟨hobject, hruntime⟩
    subst runtimeType
    exact
      fieldPairProbeResolverValue_object_eq_objectProbeResolverValueWithRuntime
        schema rootSelectionSet parentType fieldName tag outputType hobject
  · exact
      fieldPairProbeResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
        schema rootSelectionSet parentType fieldName runtimeType tag
        outputType habstract.1 habstract.2.1 habstract.2.2

noncomputable def fieldPairProbeHeadResolverValue
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag)
    : TypeRef -> Execution.ResolverValue (Option FieldPairProbeTag)
  | .named typeName =>
      if (TypeRef.named typeName).isCompositeBool schema then
        if objectTypeNameBool schema typeName then
          .object typeName (some tag)
        else
          match abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet with
          | some runtimeType => .object runtimeType (some tag)
          | none => .object typeName (some tag)
      else
        .scalar tag.scalar
  | .list inner =>
      .list
        [fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
          fieldName arguments tag inner]
  | .nonNull inner =>
      fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
        fieldName arguments tag inner

theorem fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name) {firstArguments laterArguments : List Argument}
    (tag : FieldPairProbeTag)
    : Argument.argumentsEquivalent firstArguments laterArguments
      -> ∀ outputType,
          fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
            fieldName firstArguments tag outputType
          = fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
              fieldName laterArguments tag outputType
  | hequivalent, .named typeName => by
      by_cases hcomposite :
          (TypeRef.named typeName).isCompositeBool schema
      · by_cases hobject : objectTypeNameBool schema typeName
        · simp [fieldPairProbeHeadResolverValue, hcomposite, hobject]
        · simp [fieldPairProbeHeadResolverValue, hcomposite, hobject]
      · simp [fieldPairProbeHeadResolverValue, hcomposite]
  | hequivalent, .list inner => by
      have hinner :=
        fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent schema
          rootSelectionSet parentType fieldName tag hequivalent inner
      simp [fieldPairProbeHeadResolverValue, hinner]
  | hequivalent, .nonNull inner => by
      exact
        fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent schema
          rootSelectionSet parentType fieldName tag hequivalent inner

theorem fieldPairProbeHeadResolverValue_leaf_eq_leafProbeResolverValue
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = false
        -> fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
              fieldName arguments tag outputType
            = leafProbeResolverValue outputType tag.scalar
  | .named typeName, hleaf => by
      have hleafNamed :
          (TypeRef.named typeName).isCompositeBool schema = false := by
        simpa [TypeRef.namedType] using hleaf
      simp [fieldPairProbeHeadResolverValue, leafProbeResolverValue,
        hleafNamed]
  | .list inner, hleaf => by
      have hinner :=
        fieldPairProbeHeadResolverValue_leaf_eq_leafProbeResolverValue schema
          rootSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hleaf)
      simp [fieldPairProbeHeadResolverValue, leafProbeResolverValue, hinner]
  | .nonNull inner, hleaf => by
      exact
        fieldPairProbeHeadResolverValue_leaf_eq_leafProbeResolverValue schema
          rootSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hleaf)

theorem fieldPairProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag)
    : ∀ outputType,
        objectTypeNameBool schema outputType.namedType = true
        -> fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
              fieldName arguments tag outputType
            = objectProbeResolverValueWithRuntime outputType.namedType
                (some tag) outputType
  | .named typeName, hobject => by
      have hobjectNamed :
          objectTypeNameBool schema typeName = true := by
        simpa [TypeRef.namedType] using hobject
      have hcomposite :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        unfold objectTypeNameBool at hobjectNamed
        unfold TypeRef.isCompositeBool TypeRef.namedType
        cases hlookup : schema.lookupType typeName with
        | none =>
            simp [hlookup] at hobjectNamed
        | some typeDefinition =>
            cases typeDefinition <;> simp [hlookup] at hobjectNamed ⊢
      simp [fieldPairProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType, hcomposite,
        hobjectNamed]
  | .list inner, hobject => by
      have hinner :=
        fieldPairProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hobject)
      simpa [fieldPairProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType] using hinner
  | .nonNull inner, hobject => by
      exact
        fieldPairProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName arguments tag inner
          (by simpa [TypeRef.namedType] using hobject)

theorem fieldPairProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag)
    : ∀ outputType,
        (TypeRef.named outputType.namedType).isCompositeBool schema = true
        -> objectTypeNameBool schema outputType.namedType = false
        -> abstractRuntimeForFieldDeep? schema parentType fieldName parentType
              rootSelectionSet
            = some runtimeType
        -> fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
              fieldName arguments tag outputType
            = objectProbeResolverValueWithRuntime runtimeType (some tag) outputType
  | .named typeName, hcomposite, hnonObject, hruntime => by
      have hcompositeNamed :
          (TypeRef.named typeName).isCompositeBool schema = true := by
        simpa [TypeRef.namedType] using hcomposite
      have hnonObjectNamed :
          objectTypeNameBool schema typeName = false := by
        simpa [TypeRef.namedType] using hnonObject
      simp [fieldPairProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, hcompositeNamed,
        hnonObjectNamed, hruntime]
  | .list inner, hcomposite, hnonObject, hruntime => by
      have hinner :=
        fieldPairProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName runtimeType arguments
          tag inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject) hruntime
      simpa [fieldPairProbeHeadResolverValue,
        objectProbeResolverValueWithRuntime, TypeRef.namedType] using hinner
  | .nonNull inner, hcomposite, hnonObject, hruntime => by
      exact
        fieldPairProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
          schema rootSelectionSet parentType fieldName runtimeType arguments
          tag inner
          (by simpa [TypeRef.namedType] using hcomposite)
          (by simpa [TypeRef.namedType] using hnonObject) hruntime

theorem fieldPairProbeHeadResolverValue_eq_objectProbeResolverValueWithRuntime
    (schema : Schema) (rootSelectionSet : List Selection)
    (parentType fieldName runtimeType : Name) (arguments : List Argument)
    (tag : FieldPairProbeTag) (outputType : TypeRef)
    : ((objectTypeNameBool schema outputType.namedType = true
          ∧ runtimeType = outputType.namedType)
        ∨ ((TypeRef.named outputType.namedType).isCompositeBool schema = true
            ∧ objectTypeNameBool schema outputType.namedType = false
            ∧ abstractRuntimeForFieldDeep? schema parentType fieldName parentType
                rootSelectionSet
              = some runtimeType))
      -> fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
            fieldName arguments tag outputType
          = objectProbeResolverValueWithRuntime runtimeType (some tag) outputType := by
  intro hcase
  rcases hcase with hobject | habstract
  · rcases hobject with ⟨hobject, hruntime⟩
    subst runtimeType
    exact
      fieldPairProbeHeadResolverValue_object_eq_objectProbeResolverValueWithRuntime
        schema rootSelectionSet parentType fieldName arguments tag outputType
        hobject
  · exact
      fieldPairProbeHeadResolverValue_abstract_eq_objectProbeResolverValueWithRuntime
        schema rootSelectionSet parentType fieldName runtimeType arguments tag
        outputType habstract.1 habstract.2.1 habstract.2.2

noncomputable def fieldPairProbeResolvers
    (schema : Schema) (rootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments : List Argument)
    : Execution.Resolvers (Option FieldPairProbeTag) where
  resolve parentType fieldName arguments source := by
    classical
    exact
      match schema.lookupField parentType fieldName with
      | none => none
      | some fieldDefinition =>
          match source with
          | .object _ (some tag) =>
              some
                (fieldPairProbeHeadResolverValue schema rootSelectionSet
                  parentType fieldName arguments tag fieldDefinition.outputType)
          | .object _ none =>
              if fieldProbeTarget targetParent leftField leftArguments
                  parentType fieldName arguments then
                some
                  (fieldPairProbeHeadResolverValue schema rootSelectionSet
                    parentType fieldName arguments FieldPairProbeTag.left
                    fieldDefinition.outputType)
              else if fieldProbeTarget targetParent rightField rightArguments
                  parentType fieldName arguments then
                some
                  (fieldPairProbeHeadResolverValue schema rootSelectionSet
                    parentType fieldName arguments FieldPairProbeTag.right
                    fieldDefinition.outputType)
              else
                some
                  (fieldPairProbeResolverValue schema rootSelectionSet
                    parentType fieldName FieldPairProbeTag.filler
                    fieldDefinition.outputType)
          | _ =>
              some
                (fieldPairProbeResolverValue schema rootSelectionSet
                  parentType fieldName FieldPairProbeTag.filler
                  fieldDefinition.outputType)
  resolve_argumentsEquivalent := by
    classical
    intro parentType fieldName firstArguments laterArguments source
      harguments
    cases hlookup : schema.lookupField parentType fieldName with
    | none =>
        cases source <;> simp
    | some fieldDefinition =>
        cases source with
        | null =>
            simp
        | scalar value =>
            simp
        | list values =>
            simp
        | object runtimeType sourceTag =>
            cases sourceTag with
            | some tag =>
                have hvalue :=
                  fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent
                    schema rootSelectionSet parentType fieldName tag
                    harguments fieldDefinition.outputType
                simp [hvalue]
            | none =>
                have hleftIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    leftField leftArguments parentType fieldName firstArguments
                    laterArguments harguments
                have hrightIff :=
                  fieldProbeTarget_iff_of_argumentsEquivalent targetParent
                    rightField rightArguments parentType fieldName
                    firstArguments laterArguments harguments
                by_cases hfirstLeft :
                    fieldProbeTarget targetParent leftField leftArguments
                      parentType fieldName firstArguments
                · have hlaterLeft :
                      fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments :=
                    hleftIff.mp hfirstLeft
                  have hvalue :=
                    fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent
                      schema rootSelectionSet parentType fieldName
                      FieldPairProbeTag.left harguments
                      fieldDefinition.outputType
                  simp [hfirstLeft, hlaterLeft, hvalue]
                · have hlaterLeft :
                      ¬ fieldProbeTarget targetParent leftField leftArguments
                        parentType fieldName laterArguments := by
                    intro hlater
                    exact hfirstLeft (hleftIff.mpr hlater)
                  by_cases hfirstRight :
                      fieldProbeTarget targetParent rightField rightArguments
                        parentType fieldName firstArguments
                  · have hlaterRight :
                        fieldProbeTarget targetParent rightField rightArguments
                          parentType fieldName laterArguments :=
                      hrightIff.mp hfirstRight
                    have hvalue :=
                      fieldPairProbeHeadResolverValue_eq_of_argumentsEquivalent
                        schema rootSelectionSet parentType fieldName
                        FieldPairProbeTag.right harguments
                        fieldDefinition.outputType
                    simp [hfirstLeft, hlaterLeft, hfirstRight,
                      hlaterRight, hvalue]
                  · have hlaterRight :
                        ¬ fieldProbeTarget targetParent rightField
                          rightArguments parentType fieldName
                          laterArguments := by
                      intro hlater
                      exact hfirstRight (hrightIff.mpr hlater)
                    simp [hfirstLeft, hlaterLeft, hfirstRight,
                      hlaterRight]

theorem fieldPairProbeResolvers_left_root
    (schema : Schema) (rootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (fieldDefinition : FieldDefinition)
    : Argument.argumentsEquivalent arguments leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments).resolve
            targetParent leftField arguments (.object targetParent none)
          = some
              (fieldPairProbeHeadResolverValue schema rootSelectionSet targetParent
                leftField arguments .left fieldDefinition.outputType) := by
  intro harguments hlookup
  classical
  have htarget :
      fieldProbeTarget targetParent leftField leftArguments targetParent
        leftField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairProbeResolvers, hlookup, htarget]

theorem fieldPairProbeResolvers_right_root_of_not_left
    (schema : Schema) (rootSelectionSet : List Selection)
    (targetParent leftField rightField : Name)
    (leftArguments rightArguments arguments : List Argument)
    (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField arguments
      -> Argument.argumentsEquivalent arguments rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments).resolve
            targetParent rightField arguments (.object targetParent none)
          = some
              (fieldPairProbeHeadResolverValue schema rootSelectionSet targetParent
                rightField arguments .right fieldDefinition.outputType) := by
  intro hnotLeft harguments hlookup
  classical
  have hright :
      fieldProbeTarget targetParent rightField rightArguments targetParent
        rightField arguments := by
    exact ⟨rfl, rfl, harguments⟩
  simp [fieldPairProbeResolvers, hlookup, hnotLeft,
    hright]

theorem fieldPairProbeResolvers_tagged_object
    (schema : Schema) (rootSelectionSet : List Selection)
    (targetParent leftField rightField parentType fieldName runtimeType : Name)
    (leftArguments rightArguments arguments : List Argument)
    (tag : FieldPairProbeTag) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> (fieldPairProbeResolvers schema rootSelectionSet targetParent
            leftField rightField leftArguments rightArguments).resolve
            parentType fieldName arguments (.object runtimeType (some tag))
          = some
              (fieldPairProbeHeadResolverValue schema rootSelectionSet parentType
                fieldName arguments tag fieldDefinition.outputType) := by
  intro hlookup
  simp [fieldPairProbeResolvers, hlookup]

theorem executeField_fieldPairProbe_tagged_object_leaf (schema : Schema)
    (rootSelectionSet : List Selection) (variableValues : Execution.VariableValues)
    (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) (.object sourceRuntimeType (some tag))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  leafProbeResponseValue fieldDefinition.outputType tag.scalar
                )],
                0
              ) := by
  intro hlookup hfuel hleaf
  have hresolve :
      Execution.resolveFieldValue schema
        (fieldPairProbeResolvers schema rootSelectionSet targetParent
          leftField rightField leftArguments rightArguments)
        variableValues fieldDefinition parentType fieldName arguments
        (.object sourceRuntimeType (some tag))
      =
      some
        (leafProbeResolverValue
          (ObjectRef := Option FieldPairProbeTag)
          fieldDefinition.outputType tag.scalar) := by
    simp only [Execution.resolveFieldValue]
    rw [fieldPairProbeResolvers_tagged_object schema rootSelectionSet
      targetParent leftField rightField parentType fieldName
      sourceRuntimeType leftArguments rightArguments
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments) tag
      fieldDefinition hlookup]
    rw [fieldPairProbeHeadResolverValue_leaf_eq_leafProbeResolverValue schema
      rootSelectionSet parentType fieldName
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments) tag
      fieldDefinition.outputType hleaf]
  exact
    executeField_leafProbe_singleton_of_resolve_fuel_ge schema
      (fieldPairProbeResolvers schema rootSelectionSet targetParent
        leftField rightField leftArguments rightArguments)
      variableValues fuel (.object sourceRuntimeType (some tag)) responseName
      parentType fieldName arguments childSelectionSet fieldDefinition
      tag.scalar hlookup hresolve hfuel hleaf

theorem executeField_fieldPairProbe_tagged_object_objectProbe_response_of_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) (.object sourceRuntimeType (some tag))
            responseName
            [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType (.object runtimeType (some tag))
                  childSelectionSet)) := by
  intro hlookup hruntime hinclude hfuel
  have hresolve :
      Execution.resolveFieldValue schema
        (fieldPairProbeResolvers schema rootSelectionSet targetParent
          leftField rightField leftArguments rightArguments)
        variableValues fieldDefinition parentType fieldName arguments
        (.object sourceRuntimeType (some tag))
      =
      some
        (objectProbeResolverValueWithRuntime runtimeType (some tag)
          fieldDefinition.outputType) := by
    simp only [Execution.resolveFieldValue]
    rw [fieldPairProbeResolvers_tagged_object schema rootSelectionSet
      targetParent leftField rightField parentType fieldName
      sourceRuntimeType leftArguments rightArguments
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments) tag
      fieldDefinition hlookup]
    rw [fieldPairProbeHeadResolverValue_eq_objectProbeResolverValueWithRuntime
      schema rootSelectionSet parentType fieldName runtimeType
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments) tag
      fieldDefinition.outputType hruntime]
  exact
    executeField_objectProbeWithRuntime_response_of_fuel_ge schema
      (fieldPairProbeResolvers schema rootSelectionSet targetParent
        leftField rightField leftArguments rightArguments)
      variableValues fuel (.object sourceRuntimeType (some tag))
      responseName parentType fieldName arguments childSelectionSet
      fieldDefinition runtimeType (some tag) hlookup hresolve hinclude hfuel

theorem executeField_fieldPairProbe_tagged_object_objectProbe_ok_of_child_response
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField parentType fieldName sourceRuntimeType responseName
      : Name)
    (leftArguments rightArguments arguments : List Argument) (tag : FieldPairProbeTag)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name) (responseFields : List (Name × Execution.ResponseValue))
    (childErrors : Nat)
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema parentType fieldName
                  parentType rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType (.object runtimeType (some tag))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) (.object sourceRuntimeType (some tag))
              responseName
              [{
                parentType := parentType
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hlookup hruntime hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairProbe_tagged_object_objectProbe_response_of_fuel_ge
      schema rootSelectionSet variableValues fuel targetParent leftField
      rightField parentType fieldName sourceRuntimeType responseName
      leftArguments rightArguments arguments tag childSelectionSet
      fieldDefinition runtimeType hlookup hruntime hinclude hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

theorem executeField_fieldPairProbe_left_root_leaf
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : Argument.argumentsEquivalent
        (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  leafProbeResponseValue fieldDefinition.outputType
                    FieldPairProbeTag.left.scalar
                )],
                0
              ) := by
  intro harguments hlookup hfuel hleaf
  have hresolve :
      Execution.resolveFieldValue schema
        (fieldPairProbeResolvers schema rootSelectionSet targetParent
          leftField rightField leftArguments rightArguments)
        variableValues fieldDefinition targetParent leftField arguments
        (.object targetParent none)
      =
      some
        (leafProbeResolverValue
          (ObjectRef := Option FieldPairProbeTag)
          fieldDefinition.outputType FieldPairProbeTag.left.scalar) := by
    simp only [Execution.resolveFieldValue]
    rw [fieldPairProbeResolvers_left_root schema rootSelectionSet
      targetParent leftField rightField leftArguments rightArguments
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      fieldDefinition harguments hlookup]
    rw [fieldPairProbeHeadResolverValue_leaf_eq_leafProbeResolverValue schema
      rootSelectionSet targetParent leftField
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      FieldPairProbeTag.left
      fieldDefinition.outputType hleaf]
  exact
    executeField_leafProbe_singleton_of_resolve_fuel_ge schema
      (fieldPairProbeResolvers schema rootSelectionSet targetParent
        leftField rightField leftArguments rightArguments)
      variableValues fuel (.object targetParent none) responseName
      targetParent leftField arguments childSelectionSet fieldDefinition
      FieldPairProbeTag.left.scalar hlookup hresolve hfuel hleaf

theorem executeField_fieldPairProbe_right_root_leaf_of_not_left
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = .ok
              (
                [(
                  responseName,
                  leafProbeResponseValue fieldDefinition.outputType
                    FieldPairProbeTag.right.scalar
                )],
                0
              ) := by
  intro hnotLeft harguments hlookup hfuel hleaf
  have hresolve :
      Execution.resolveFieldValue schema
        (fieldPairProbeResolvers schema rootSelectionSet targetParent
          leftField rightField leftArguments rightArguments)
        variableValues fieldDefinition targetParent rightField arguments
        (.object targetParent none)
      =
      some
        (leafProbeResolverValue
          (ObjectRef := Option FieldPairProbeTag)
          fieldDefinition.outputType FieldPairProbeTag.right.scalar) := by
    simp only [Execution.resolveFieldValue]
    rw [fieldPairProbeResolvers_right_root_of_not_left schema
      rootSelectionSet targetParent leftField rightField leftArguments
      rightArguments
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      fieldDefinition hnotLeft harguments hlookup]
    rw [fieldPairProbeHeadResolverValue_leaf_eq_leafProbeResolverValue schema
      rootSelectionSet targetParent rightField
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      FieldPairProbeTag.right
      fieldDefinition.outputType hleaf]
  exact
    executeField_leafProbe_singleton_of_resolve_fuel_ge schema
      (fieldPairProbeResolvers schema rootSelectionSet targetParent
        leftField rightField leftArguments rightArguments)
      variableValues fuel (.object targetParent none) responseName
      targetParent rightField arguments childSelectionSet fieldDefinition
      FieldPairProbeTag.right.scalar hlookup hresolve hfuel hleaf

theorem executeField_fieldPairProbe_left_root_objectProbe_response
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : Argument.argumentsEquivalent
        (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema targetParent leftField
                  targetParent rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairProbeResolvers schema rootSelectionSet targetParent
                      leftField rightField leftArguments rightArguments)
                    variableValues fuel
                    (.object runtimeType (some FieldPairProbeTag.left))
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType (some FieldPairProbeTag.left))
                      childSelectionSet)))) := by
  intro harguments hlookup hruntime hinclude
  have hresolve :
      Execution.resolveFieldValue schema
        (fieldPairProbeResolvers schema rootSelectionSet targetParent
          leftField rightField leftArguments rightArguments)
        variableValues fieldDefinition targetParent leftField arguments
        (.object targetParent none)
      =
      some
        (objectProbeResolverValueWithRuntime runtimeType
          (some FieldPairProbeTag.left) fieldDefinition.outputType) := by
    simp only [Execution.resolveFieldValue]
    rw [fieldPairProbeResolvers_left_root schema rootSelectionSet
      targetParent leftField rightField leftArguments rightArguments
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      fieldDefinition harguments hlookup]
    rw [fieldPairProbeHeadResolverValue_eq_objectProbeResolverValueWithRuntime
      schema rootSelectionSet targetParent leftField runtimeType
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      FieldPairProbeTag.left fieldDefinition.outputType hruntime]
  exact
    executeField_objectProbeWithRuntime_response schema
      (fieldPairProbeResolvers schema rootSelectionSet targetParent
        leftField rightField leftArguments rightArguments)
      variableValues fuel (.object targetParent none) responseName
      targetParent leftField arguments childSelectionSet fieldDefinition
      runtimeType (some FieldPairProbeTag.left) hlookup hresolve hinclude

theorem executeField_fieldPairProbe_left_root_objectProbe_response_of_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : Argument.argumentsEquivalent
        (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema targetParent leftField
                  targetParent rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := leftField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType (.object runtimeType (some FieldPairProbeTag.left))
                  childSelectionSet)) := by
  intro harguments hlookup hruntime hinclude hfuel
  have hexecute :=
    executeField_fieldPairProbe_left_root_objectProbe_response schema
      rootSelectionSet variableValues
      (fuel - leafProbeFuel fieldDefinition.outputType) targetParent
      leftField rightField responseName leftArguments rightArguments
      arguments childSelectionSet fieldDefinition runtimeType harguments
      hlookup hruntime hinclude
  have hfuelEq :
      fuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      fuel + 1 := by
    omega
  simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
    Execution.executeRootSelectionSet, hfuelEq] using hexecute

theorem executeField_fieldPairProbe_left_root_objectProbe_ok_of_child_response
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    (responseFields : List (Name × Execution.ResponseValue))
    (childErrors : Nat)
    : Argument.argumentsEquivalent
        (Execution.coerceArgumentValues schema variableValues
          fieldDefinition.arguments arguments)
        leftArguments
      -> schema.lookupField targetParent leftField = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema targetParent leftField
                  targetParent rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType (.object runtimeType (some FieldPairProbeTag.left))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) (.object targetParent none)
              responseName
              [{
                parentType := targetParent
                responseName := responseName
                fieldName := leftField
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro harguments hlookup hruntime hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairProbe_left_root_objectProbe_response_of_fuel_ge
      schema rootSelectionSet variableValues fuel targetParent leftField
      rightField responseName leftArguments rightArguments arguments
      childSelectionSet fieldDefinition runtimeType harguments hlookup
      hruntime hinclude hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

theorem executeField_fieldPairProbe_right_root_objectProbe_response_of_not_left
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema targetParent rightField
                  targetParent rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + leafProbeFuel fieldDefinition.outputType + 1)
            (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.selectionSetResultToResponse
                  (Execution.executeCollectedFields schema
                    (fieldPairProbeResolvers schema rootSelectionSet targetParent
                      leftField rightField leftArguments rightArguments)
                    variableValues fuel
                    (.object runtimeType (some FieldPairProbeTag.right))
                    (Execution.collectFields schema variableValues runtimeType
                      (.object runtimeType (some FieldPairProbeTag.right))
                      childSelectionSet)))) := by
  intro hnotLeft harguments hlookup hruntime hinclude
  have hresolve :
      Execution.resolveFieldValue schema
        (fieldPairProbeResolvers schema rootSelectionSet targetParent
          leftField rightField leftArguments rightArguments)
        variableValues fieldDefinition targetParent rightField arguments
        (.object targetParent none)
      =
      some
        (objectProbeResolverValueWithRuntime runtimeType
          (some FieldPairProbeTag.right) fieldDefinition.outputType) := by
    simp only [Execution.resolveFieldValue]
    rw [fieldPairProbeResolvers_right_root_of_not_left schema rootSelectionSet
      targetParent leftField rightField leftArguments rightArguments
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      fieldDefinition hnotLeft harguments hlookup]
    rw [fieldPairProbeHeadResolverValue_eq_objectProbeResolverValueWithRuntime
      schema rootSelectionSet targetParent rightField runtimeType
      (Execution.coerceArgumentValues schema variableValues
        fieldDefinition.arguments arguments)
      FieldPairProbeTag.right fieldDefinition.outputType hruntime]
  exact
    executeField_objectProbeWithRuntime_response schema
      (fieldPairProbeResolvers schema rootSelectionSet targetParent
        leftField rightField leftArguments rightArguments)
      variableValues fuel (.object targetParent none) responseName
      targetParent rightField arguments childSelectionSet fieldDefinition
      runtimeType (some FieldPairProbeTag.right) hlookup hresolve hinclude

theorem executeField_fieldPairProbe_right_root_objectProbe_response_of_not_left_of_fuel_ge
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema targetParent rightField
                  targetParent rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeField schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues (fuel + 1) (.object targetParent none) responseName
            [{
              parentType := targetParent
              responseName := responseName
              fieldName := rightField
              arguments := arguments
              selectionSet := childSelectionSet
            }]
          = Execution.singleFieldResult responseName
              (wrapTypeRefSelectionSetResult fieldDefinition.outputType
                (Execution.executeSelectionSetAsResponse schema
                  (fieldPairProbeResolvers schema rootSelectionSet targetParent
                    leftField rightField leftArguments rightArguments)
                  variableValues
                  (fuel - leafProbeFuel fieldDefinition.outputType)
                  runtimeType (.object runtimeType (some FieldPairProbeTag.right))
                  childSelectionSet)) := by
  intro hnotLeft harguments hlookup hruntime hinclude hfuel
  have hexecute :=
    executeField_fieldPairProbe_right_root_objectProbe_response_of_not_left
      schema rootSelectionSet variableValues
      (fuel - leafProbeFuel fieldDefinition.outputType) targetParent
      leftField rightField responseName leftArguments rightArguments
      arguments childSelectionSet fieldDefinition runtimeType hnotLeft
      harguments hlookup hruntime hinclude
  have hfuelEq :
      fuel - leafProbeFuel fieldDefinition.outputType
          + leafProbeFuel fieldDefinition.outputType + 1
        =
      fuel + 1 := by
    omega
  simpa [Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
    Execution.executeRootSelectionSet, hfuelEq] using hexecute

theorem executeField_fieldPairProbe_right_root_objectProbe_ok_of_child_response
    (schema : Schema) (rootSelectionSet : List Selection)
    (variableValues : Execution.VariableValues)
    (fuel : Nat) (targetParent leftField rightField responseName : Name)
    (leftArguments rightArguments arguments : List Argument)
    (childSelectionSet : List Selection) (fieldDefinition : FieldDefinition)
    (runtimeType : Name)
    (responseFields : List (Name × Execution.ResponseValue))
    (childErrors : Nat)
    : ¬ fieldProbeTarget targetParent leftField leftArguments targetParent
          rightField
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
      -> Argument.argumentsEquivalent
          (Execution.coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments)
          rightArguments
      -> schema.lookupField targetParent rightField = some fieldDefinition
      -> ((objectTypeNameBool schema fieldDefinition.outputType.namedType = true
            ∧ runtimeType = fieldDefinition.outputType.namedType)
          ∨ ((TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
              ∧ objectTypeNameBool schema fieldDefinition.outputType.namedType = false
              ∧ abstractRuntimeForFieldDeep? schema targetParent rightField
                  targetParent rootSelectionSet
                = some runtimeType))
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> leafProbeFuel fieldDefinition.outputType ≤ fuel
      -> Execution.executeSelectionSetAsResponse schema
            (fieldPairProbeResolvers schema rootSelectionSet targetParent
              leftField rightField leftArguments rightArguments)
            variableValues
            (fuel - leafProbeFuel fieldDefinition.outputType)
            runtimeType (.object runtimeType (some FieldPairProbeTag.right))
            childSelectionSet
          = ({
                data := Execution.ResponseValue.object responseFields,
                errors := childErrors
              }
              : Execution.Response)
      -> ∃ responseValue fieldErrors,
          Execution.executeField schema
              (fieldPairProbeResolvers schema rootSelectionSet targetParent
                leftField rightField leftArguments rightArguments)
              variableValues (fuel + 1) (.object targetParent none)
              responseName
              [{
                parentType := targetParent
                responseName := responseName
                fieldName := rightField
                arguments := arguments
                selectionSet := childSelectionSet
              }]
            = .ok ([(responseName, responseValue)], fieldErrors)
          ∧ responseValue ≠ Execution.ResponseValue.null := by
  intro hnotLeft harguments hlookup hruntime hinclude hfuel hchildResponse
  have hfield :=
    executeField_fieldPairProbe_right_root_objectProbe_response_of_not_left_of_fuel_ge
      schema rootSelectionSet variableValues fuel targetParent leftField
      rightField responseName leftArguments rightArguments arguments
      childSelectionSet fieldDefinition runtimeType hnotLeft harguments
      hlookup hruntime hinclude hfuel
  rcases
      wrapTypeRefSelectionSetResult_ok_nonNull_of_object_response
        fieldDefinition.outputType responseFields childErrors with
    ⟨responseValue, fieldErrors, hwrapped, hnonNull⟩
  refine ⟨responseValue, fieldErrors, ?_, hnonNull⟩
  rw [hfield, hchildResponse, hwrapped]
  simp [Execution.singleFieldResult]

end GroundTypeNormalization

end NormalForm

end GraphQL
