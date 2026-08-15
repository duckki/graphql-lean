import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ObservablePath
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Validity

/-!
Focused syntactic traces for normal-form uniqueness.

`NormalSelectionSetDiff` identifies a syntactic difference between two normal
selection sets.  The semantic separation proof only needs one observable
response path through that difference, not a proof that every sibling and every
support selection set is observable.  This module records that focused path and
proves it is available from any valid normal diff.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

inductive NormalSelectionSetResponsePath (schema : Schema)
    : Name -> List Selection -> List Name -> Prop where
  | objectHere
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> NormalSelectionSetResponsePath schema parentType selectionSet [responseName]
  | objectChild
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> NormalSelectionSetResponsePath schema
          fieldDefinition.outputType.namedType childSelectionSet childPath
      -> NormalSelectionSetResponsePath schema parentType selectionSet
          (responseName :: childPath)
  | abstractInlineFragment
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> NormalSelectionSetResponsePath schema typeCondition childSelectionSet childPath
      -> NormalSelectionSetResponsePath schema parentType selectionSet childPath

inductive NormalSelectionSetObservableResponsePath (schema : Schema)
    : Name -> List Selection -> List Name -> Prop where
  | objectLeaf
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObservableResponsePath schema parentType
          selectionSet [responseName]
  | objectChild
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetObservableResponsePath schema
          fieldDefinition.outputType.namedType childSelectionSet childPath
      -> NormalSelectionSetObservableResponsePath schema parentType
          selectionSet (responseName :: childPath)
  | abstractInlineFragment
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> NormalSelectionSetObservableResponsePath schema typeCondition
          childSelectionSet childPath
      -> NormalSelectionSetObservableResponsePath schema parentType selectionSet childPath

theorem NormalSelectionSetObservableResponsePath.to_responsePath
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObservableResponsePath schema parentType selectionSet responsePath
      -> NormalSelectionSetResponsePath schema parentType selectionSet responsePath := by
  intro hpath
  induction hpath with
  | objectLeaf hobject hmem _hlookup _hleaf =>
      exact NormalSelectionSetResponsePath.objectHere hobject hmem
  | objectChild hobject hmem hlookup _hcomposite _hchild ih =>
      exact NormalSelectionSetResponsePath.objectChild hobject hmem hlookup ih
  | abstractInlineFragment hnonObject hmem _hchild ih =>
      exact
        NormalSelectionSetResponsePath.abstractInlineFragment hnonObject hmem
          ih

theorem normalSelectionSetObservableResponsePath_of_observableLeaf
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : NormalSelectionSetObservableLeaf schema parentType selectionSet
      -> ∃ responsePath,
          NormalSelectionSetObservableResponsePath schema parentType
            selectionSet responsePath := by
  intro hpath
  induction hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      exact ⟨
        [_],
        NormalSelectionSetObservableResponsePath.objectLeaf hobject hmem hlookup hleaf
      ⟩
  | objectChild hobject hmem hlookup hcomposite _hchild ih =>
      rcases ih with ⟨childPath, hchildPath⟩
      exact ⟨
        _ :: childPath,
        NormalSelectionSetObservableResponsePath.objectChild hobject hmem
          hlookup
          (by
            rcases hcomposite with ⟨typeDefinition, htypeLookup,
              htypeComposite⟩
            unfold TypeRef.isCompositeBool TypeRef.namedType
            rw [htypeLookup]
            cases typeDefinition <;>
              simp [TypeDefinition.isCompositeType] at htypeComposite ⊢)
          hchildPath
      ⟩
  | abstractInlineFragment hnonObject hmem _hchild ih =>
      rcases ih with ⟨childPath, hchildPath⟩
      exact ⟨
        childPath,
        NormalSelectionSetObservableResponsePath.abstractInlineFragment
          hnonObject hmem hchildPath
      ⟩

structure NormalSelectionSetObservableFieldStep where
  responseName : Name
  fieldName : Name
  arguments : List Argument
  childRuntime : Option Name

inductive NormalSelectionSetObservableFieldSpine (schema : Schema)
    : Name -> List Selection -> List NormalSelectionSetObservableFieldStep -> Prop where
  | objectLeaf
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> NormalSelectionSetObservableFieldSpine schema parentType
          selectionSet
          [{
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            childRuntime := none
          }]
  | objectChildObject
    {parentType responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = true
      -> NormalSelectionSetObservableFieldSpine schema
          fieldDefinition.outputType.namedType childSelectionSet childSpine
      -> NormalSelectionSetObservableFieldSpine schema parentType
          selectionSet
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              childRuntime := some fieldDefinition.outputType.namedType
            }
            :: childSpine)
  | objectChildAbstract
    {parentType responseName fieldName runtimeType : Name}
    {arguments : List Argument}
    {directives childDirectives : List DirectiveApplication}
    {childSelectionSet childBodySelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> objectTypeNameBool schema fieldDefinition.outputType.namedType = false
      -> Selection.inlineFragment (some runtimeType) childDirectives childBodySelectionSet
          ∈ childSelectionSet
      -> NormalSelectionSetObservableFieldSpine schema
          fieldDefinition.outputType.namedType childSelectionSet childSpine
      -> NormalSelectionSetObservableFieldSpine schema parentType
          selectionSet
          ({
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              childRuntime := some runtimeType
            }
            :: childSpine)
  | abstractInlineFragment
    {parentType typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {childSpine : List NormalSelectionSetObservableFieldStep}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ selectionSet
      -> NormalSelectionSetObservableFieldSpine schema typeCondition
          childSelectionSet childSpine
      -> NormalSelectionSetObservableFieldSpine schema parentType selectionSet childSpine

theorem normalSelectionSetObservableFieldSpine_ne_nil
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : NormalSelectionSetObservableFieldSpine schema parentType selectionSet fieldSpine
      -> fieldSpine ≠ [] := by
  intro hspine
  induction hspine with
  | objectLeaf =>
      simp
  | objectChildObject =>
      simp
  | objectChildAbstract =>
      simp
  | abstractInlineFragment _hnonObject _hmem _hchildSpine ih =>
      exact ih

theorem normalSelectionSetObservableFieldSpine_selectionSet_ne_nil
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {fieldSpine : List NormalSelectionSetObservableFieldStep}
    : NormalSelectionSetObservableFieldSpine schema parentType selectionSet fieldSpine
      -> selectionSet ≠ [] := by
  intro hspine
  cases hspine with
  | objectLeaf _hobject hmem _hlookup _hleaf =>
      intro hempty
      subst selectionSet
      simp at hmem
  | objectChildObject _hobject hmem _hlookup _hreturnObject _hchildSpine =>
      intro hempty
      subst selectionSet
      simp at hmem
  | objectChildAbstract _hobject hmem _hlookup _hcomposite
      _hreturnNonObject _hfragmentMem _hchildSpine =>
      intro hempty
      subst selectionSet
      simp at hmem
  | abstractInlineFragment _hnonObject hmem _hchildSpine =>
      intro hempty
      subst selectionSet
      simp at hmem

theorem normalSelectionSetObservableFieldSpine_of_observableResponsePath
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObservableResponsePath schema parentType selectionSet responsePath
      -> ∃ fieldSpine,
          NormalSelectionSetObservableFieldSpine schema parentType
            selectionSet fieldSpine := by
  intro hpath
  induction hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      exact ⟨
        _,
        NormalSelectionSetObservableFieldSpine.objectLeaf hobject hmem hlookup hleaf
      ⟩
  | objectChild hobject hmem hlookup hcomposite hchildPath ih =>
      rename_i parentType responseName fieldName arguments directives
        childSelectionSet selectionSet fieldDefinition childPath
      by_cases hreturnObject :
          objectTypeNameBool schema fieldDefinition.outputType.namedType =
            true
      · rcases ih with ⟨childSpine, hchildSpine⟩
        exact ⟨
          _,
          NormalSelectionSetObservableFieldSpine.objectChildObject
            hobject hmem hlookup hreturnObject hchildSpine
        ⟩
      · have hreturnNonObject :
            objectTypeNameBool schema fieldDefinition.outputType.namedType =
              false := by
          cases h :
              objectTypeNameBool schema
                fieldDefinition.outputType.namedType
          · rfl
          · exact False.elim (hreturnObject h)
        cases hchildPath with
        | objectLeaf hchildObject _hchildMem _hchildLookup _hchildLeaf =>
            rw [hreturnNonObject] at hchildObject
            simp at hchildObject
        | objectChild hchildObject _hchildMem _hchildLookup _hchildComposite
            _hgrandChildPath =>
            rw [hreturnNonObject] at hchildObject
            simp at hchildObject
        | abstractInlineFragment _hchildNonObject hfragmentMem
            hgrandChildPath =>
            rcases ih with ⟨childSpine, hchildSpine⟩
            exact ⟨
              _,
              NormalSelectionSetObservableFieldSpine.objectChildAbstract
                hobject hmem hlookup hcomposite hreturnNonObject
                hfragmentMem hchildSpine
            ⟩
  | abstractInlineFragment hnonObject hmem _hchildPath ih =>
      rcases ih with ⟨childSpine, hchildSpine⟩
      exact ⟨
        childSpine,
        NormalSelectionSetObservableFieldSpine.abstractInlineFragment
          hnonObject hmem hchildSpine
      ⟩

inductive NormalSelectionSetDiffTrace (schema : Schema)
    : Name -> List Selection -> List Selection -> List Name -> Prop where
  | objectLeftResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> NormalSelectionSetDiffTrace schema parentType left right [responseName]
  | objectRightResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> NormalSelectionSetDiffTrace schema parentType left right [responseName]
  | objectFieldName
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> leftFieldName ≠ rightFieldName
      -> NormalSelectionSetDiffTrace schema parentType left right [responseName]
  | objectArguments
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> NormalSelectionSetDiffTrace schema parentType left right [responseName]
  | objectChild
    {parentType returnType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> schema.fieldReturnType? parentType fieldName = some returnType
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Argument.argumentsEquivalent leftArguments rightArguments
      -> NormalSelectionSetDiffTrace schema returnType leftChildSelectionSet
          rightChildSelectionSet childPath
      -> NormalSelectionSetDiffTrace schema parentType left right
          (responseName :: childPath)
  | abstractLeftTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet ∈ left
      -> typeCondition ∉ right.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetResponsePath schema typeCondition childSelectionSet childPath
      -> NormalSelectionSetDiffTrace schema parentType left right childPath
  | abstractRightTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ right
      -> typeCondition ∉ left.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetResponsePath schema typeCondition childSelectionSet childPath
      -> NormalSelectionSetDiffTrace schema parentType left right childPath
  | abstractChild
    {parentType typeCondition : Name} {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.inlineFragment (some typeCondition) rightDirectives
            rightChildSelectionSet
          ∈ right
      -> NormalSelectionSetDiffTrace schema typeCondition
          leftChildSelectionSet rightChildSelectionSet childPath
      -> NormalSelectionSetDiffTrace schema parentType left right childPath

inductive NormalSelectionSetDiffObservableTrace (schema : Schema)
    : Name -> List Selection -> List Selection -> List Name -> Prop where
  | objectLeftResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ left
      -> responseName ∉ right.filterMap Selection.responseName?
      -> NormalSelectionSetDiffObservableTrace schema parentType left right [responseName]
  | objectRightResponseName
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {arguments : List Argument}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ right
      -> responseName ∉ left.filterMap Selection.responseName?
      -> NormalSelectionSetDiffObservableTrace schema parentType left right [responseName]
  | objectFieldNameLeaf
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> leftFieldName ≠ rightFieldName
      -> NormalSelectionSetDiffObservableTrace schema parentType left right [responseName]
  | objectFieldNameCompositeLeft
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetObservableResponsePath schema
          leftFieldDefinition.outputType.namedType leftChildSelectionSet
          childPath
      -> leftFieldName ≠ rightFieldName
      -> NormalSelectionSetDiffObservableTrace schema parentType left right
          (responseName :: childPath)
  | objectFieldNameCompositeRight
    {parentType : Name} {left right : List Selection}
    {responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments
            rightDirectives rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetObservableResponsePath schema
          rightFieldDefinition.outputType.namedType rightChildSelectionSet
          childPath
      -> leftFieldName ≠ rightFieldName
      -> NormalSelectionSetDiffObservableTrace schema parentType left right
          (responseName :: childPath)
  | objectArgumentsLeaf
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = false
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> NormalSelectionSetDiffObservableTrace schema parentType left right [responseName]
  | objectArgumentsCompositeLeft
    {parentType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> NormalSelectionSetObservableResponsePath schema
          fieldDefinition.outputType.namedType leftChildSelectionSet
          childPath
      -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
      -> NormalSelectionSetDiffObservableTrace schema parentType left right
          (responseName :: childPath)
  | objectChild
    {parentType returnType : Name} {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = true
      -> schema.fieldReturnType? parentType fieldName = some returnType
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> Argument.argumentsEquivalent leftArguments rightArguments
      -> NormalSelectionSetDiffObservableTrace schema returnType
          leftChildSelectionSet rightChildSelectionSet childPath
      -> NormalSelectionSetDiffObservableTrace schema parentType left right
          (responseName :: childPath)
  | abstractLeftTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet ∈ left
      -> typeCondition ∉ right.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetObservableResponsePath schema typeCondition
          childSelectionSet childPath
      -> NormalSelectionSetDiffObservableTrace schema parentType left right childPath
  | abstractRightTypeCondition
    {parentType : Name} {left right : List Selection}
    {typeCondition : Name}
    {directives : List DirectiveApplication}
    {childSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) directives childSelectionSet
          ∈ right
      -> typeCondition ∉ left.filterMap inlineFragmentTypeCondition?
      -> NormalSelectionSetObservableResponsePath schema typeCondition
          childSelectionSet childPath
      -> NormalSelectionSetDiffObservableTrace schema parentType left right childPath
  | abstractChild
    {parentType typeCondition : Name} {left right : List Selection}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet : List Selection}
    {childPath : List Name}
    : objectTypeNameBool schema parentType = false
      -> Selection.inlineFragment (some typeCondition) leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.inlineFragment (some typeCondition) rightDirectives
            rightChildSelectionSet
          ∈ right
      -> NormalSelectionSetDiffObservableTrace schema typeCondition
          leftChildSelectionSet rightChildSelectionSet childPath
      -> NormalSelectionSetDiffObservableTrace schema parentType left right childPath

theorem normalSelectionSetResponsePath_of_observableLeaf
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    : NormalSelectionSetObservableLeaf schema parentType selectionSet
      -> ∃ responsePath,
          NormalSelectionSetResponsePath schema parentType selectionSet responsePath := by
  intro hpath
  rcases normalSelectionSetObservableResponsePath_of_observableLeaf hpath with
    ⟨responsePath, hobservablePath⟩
  exact ⟨responsePath, hobservablePath.to_responsePath⟩

theorem normalSelectionSetResponsePath_of_valid_normal_nonempty
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> selectionSet ≠ []
      -> ∃ responsePath,
          NormalSelectionSetResponsePath schema parentType selectionSet responsePath := by
  intro hvalid hnormal hnonempty
  exact
    normalSelectionSetResponsePath_of_observableLeaf
      (normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
        parentType variableDefinitions selectionSet hvalid hnormal hnonempty)

theorem normalSelectionSetResponsePath_of_valid_normal_composite_field_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ responsePath,
          NormalSelectionSetResponsePath schema
            fieldDefinition.outputType.namedType childSelectionSet
            responsePath := by
  intro hvalid hnormal hmem hlookup hcomposite
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid
      hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · rw [hcomposite] at hleaf
    simp at hleaf
  · have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    exact
      normalSelectionSetResponsePath_of_valid_normal_nonempty
        hcompositeKind.2.2 hchildNormal hcompositeKind.2.1

theorem normalSelectionSetObservableResponsePath_of_valid_normal_composite_field_mem
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> Selection.field responseName fieldName arguments directives childSelectionSet
          ∈ selectionSet
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> ∃ responsePath,
          NormalSelectionSetObservableResponsePath schema
            fieldDefinition.outputType.namedType childSelectionSet
            responsePath := by
  intro hvalid hnormal hmem hlookup hcomposite
  rcases selectionSetValid_field_lookup_leaf_or_composite_child hvalid
      hmem with
    ⟨candidateDefinition, hcandidateLookup, hkind⟩
  have hcandidateEq : candidateDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateDefinition
  rcases hkind with hleaf | hcompositeKind
  · rw [hcomposite] at hleaf
    simp at hleaf
  · have hchildNormal :
        selectionSetNormal schema fieldDefinition.outputType.namedType
          childSelectionSet :=
      selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
    exact
      normalSelectionSetObservableResponsePath_of_observableLeaf
        (normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
          fieldDefinition.outputType.namedType variableDefinitions
          childSelectionSet hcompositeKind.2.2 hchildNormal
          hcompositeKind.2.1)

theorem normalSelectionSetResponsePath_of_valid_normal_fieldName_composite_mem
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName leftFieldName rightFieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {leftFieldDefinition rightFieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> Selection.field responseName leftFieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName rightFieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
      -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
      -> ((TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
            = true
          ∨ (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
              schema
            = true)
      -> (∃ responsePath,
            NormalSelectionSetResponsePath schema
              leftFieldDefinition.outputType.namedType leftChildSelectionSet
              responsePath)
          ∨ (∃ responsePath,
              NormalSelectionSetResponsePath schema
                rightFieldDefinition.outputType.namedType rightChildSelectionSet
                responsePath) := by
  intro hleftValid hrightValid hleftNormal hrightNormal hleftMem hrightMem
    hleftLookup hrightLookup hcomposite
  rcases hcomposite with hleftComposite | hrightComposite
  · exact
      Or.inl
        (normalSelectionSetResponsePath_of_valid_normal_composite_field_mem
          hleftValid hleftNormal hleftMem hleftLookup hleftComposite)
  · exact
      Or.inr
        (normalSelectionSetResponsePath_of_valid_normal_composite_field_mem
          hrightValid hrightNormal hrightMem hrightLookup hrightComposite)

theorem normalSelectionSetResponsePath_pair_of_valid_normal_arguments_composite_mem
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
          = true
      -> (∃ responsePath,
            NormalSelectionSetResponsePath schema
              fieldDefinition.outputType.namedType leftChildSelectionSet
              responsePath)
          ∧ (∃ responsePath,
              NormalSelectionSetResponsePath schema
                fieldDefinition.outputType.namedType rightChildSelectionSet
                responsePath) := by
  intro hleftValid hrightValid hleftNormal hrightNormal hleftMem hrightMem
    hlookup hcomposite
  exact ⟨
    normalSelectionSetResponsePath_of_valid_normal_composite_field_mem
      hleftValid hleftNormal hleftMem hlookup hcomposite,
    normalSelectionSetResponsePath_of_valid_normal_composite_field_mem
      hrightValid hrightNormal hrightMem hlookup hcomposite
  ⟩

theorem NormalSelectionSetResponsePath.append_context
    {schema : Schema} {parentType : Name}
    {selectionSet pref suff : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetResponsePath schema parentType selectionSet responsePath
      -> NormalSelectionSetResponsePath schema parentType
          (pref ++ selectionSet ++ suff) responsePath := by
  intro hpath
  cases hpath with
  | objectHere hobject hmem =>
      exact
        NormalSelectionSetResponsePath.objectHere hobject
          (by
            simpa [List.append_assoc] using
              (List.mem_append_right pref
                (List.mem_append_left suff hmem)))
  | objectChild hobject hmem hlookup hchildPath =>
      exact
        NormalSelectionSetResponsePath.objectChild hobject
          (by
            simpa [List.append_assoc] using
              (List.mem_append_right pref
                (List.mem_append_left suff hmem)))
          hlookup hchildPath
  | abstractInlineFragment hnonObject hmem hchildPath =>
      exact
        NormalSelectionSetResponsePath.abstractInlineFragment hnonObject
          (by
            simpa [List.append_assoc] using
              (List.mem_append_right pref
                (List.mem_append_left suff hmem)))
          hchildPath

theorem NormalSelectionSetObservableResponsePath.append_context
    {schema : Schema} {parentType : Name}
    {selectionSet pref suff : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetObservableResponsePath schema parentType selectionSet responsePath
      -> NormalSelectionSetObservableResponsePath schema parentType
          (pref ++ selectionSet ++ suff) responsePath := by
  intro hpath
  cases hpath with
  | objectLeaf hobject hmem hlookup hleaf =>
      exact
        NormalSelectionSetObservableResponsePath.objectLeaf hobject
          (by
            simpa [List.append_assoc] using
              (List.mem_append_right pref
                (List.mem_append_left suff hmem)))
          hlookup hleaf
  | objectChild hobject hmem hlookup hcomposite hchildPath =>
      exact
        NormalSelectionSetObservableResponsePath.objectChild hobject
          (by
            simpa [List.append_assoc] using
              (List.mem_append_right pref
                (List.mem_append_left suff hmem)))
          hlookup hcomposite hchildPath
  | abstractInlineFragment hnonObject hmem hchildPath =>
      exact
        NormalSelectionSetObservableResponsePath.abstractInlineFragment
          hnonObject
          (by
            simpa [List.append_assoc] using
              (List.mem_append_right pref
                (List.mem_append_left suff hmem)))
          hchildPath

theorem normalSelectionSetResponsePath_ne_nil
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetResponsePath schema parentType selectionSet responsePath
      -> responsePath ≠ [] := by
  intro hpath
  induction hpath with
  | objectHere _hobject _hmem =>
      simp
  | objectChild _hobject _hmem _hlookup _hchildPath _ih =>
      simp
  | abstractInlineFragment _hnonObject _hmem _hchildPath ih =>
      exact ih

theorem normalSelectionSetResponsePath_selectionSet_nonempty
    {schema : Schema} {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetResponsePath schema parentType selectionSet responsePath
      -> selectionSet ≠ [] := by
  intro hpath hempty
  cases hpath with
  | objectHere _hobject hmem =>
      subst selectionSet
      simp at hmem
  | objectChild _hobject hmem _hlookup _hchildPath =>
      subst selectionSet
      simp at hmem
  | abstractInlineFragment _hnonObject hmem _hchildPath =>
      subst selectionSet
      simp at hmem

theorem normalSelectionSetObservableLeaf_of_responsePath_valid_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    {responsePath : List Name}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> NormalSelectionSetResponsePath schema parentType selectionSet responsePath
      -> NormalSelectionSetObservableLeaf schema parentType selectionSet := by
  intro hvalid hnormal hpath
  induction hpath with
  | objectHere hobject hmem =>
      rename_i _pathParentType _responseName _fieldName _arguments _directives
        childSelectionSet _pathSelectionSet
      rcases
          selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem
        with
        ⟨fieldDefinition, hlookup, hkind⟩
      rcases hkind with hleaf | hcomposite
      · exact
          NormalSelectionSetObservableLeaf.objectLeaf hobject hmem
            hlookup hleaf.1
      · have hchildNormal :
            selectionSetNormal schema fieldDefinition.outputType.namedType
              childSelectionSet :=
          selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
        have hchildLeaf :
            NormalSelectionSetObservableLeaf schema
              fieldDefinition.outputType.namedType childSelectionSet :=
          normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
            fieldDefinition.outputType.namedType variableDefinitions
            childSelectionSet hcomposite.2.2 hchildNormal hcomposite.2.1
        exact
          NormalSelectionSetObservableLeaf.objectChild hobject hmem hlookup
            hcomposite.1 hchildLeaf
  | objectChild hobject hmem hlookup hchildPath ih =>
      rename_i _pathParentType _responseName _fieldName _arguments _directives
        childSelectionSet _pathSelectionSet fieldDefinition _childPath
      have hchildNonempty : childSelectionSet ≠ [] :=
        normalSelectionSetResponsePath_selectionSet_nonempty hchildPath
      rcases
          selectionSetValid_field_lookup_leaf_or_composite_child hvalid hmem
        with
        ⟨candidateDefinition, hcandidateLookup, hkind⟩
      have hcandidateEq : candidateDefinition = fieldDefinition := by
        rw [hlookup] at hcandidateLookup
        exact Option.some.inj hcandidateLookup.symm
      subst candidateDefinition
      have hchildNormal :
          selectionSetNormal schema fieldDefinition.outputType.namedType
            childSelectionSet :=
        selectionSetNormal_field_child_of_mem_lookup hnormal hmem hlookup
      rcases hkind with hleaf | hcomposite
      · exact False.elim (hchildNonempty hleaf.2)
      · have hchildLeaf :
            NormalSelectionSetObservableLeaf schema
              fieldDefinition.outputType.namedType childSelectionSet :=
          ih hcomposite.2.2 hchildNormal
        exact
          NormalSelectionSetObservableLeaf.objectChild hobject hmem hlookup
            hcomposite.1 hchildLeaf
  | abstractInlineFragment hnonObject hmem hchildPath ih =>
      rename_i _pathParentType typeCondition _directives childSelectionSet
        _pathSelectionSet _childPath
      have hchildValid :
          Validation.selectionSetValid schema variableDefinitions
            typeCondition childSelectionSet :=
        selectionSetValid_inlineFragment_some_child_of_mem hvalid hmem
      have hchildNormal :
          selectionSetNormal schema typeCondition childSelectionSet :=
        (selectionSetNormal_inlineFragment_child_of_mem hnormal hmem).2
      have hchildLeaf :
          NormalSelectionSetObservableLeaf schema typeCondition
            childSelectionSet :=
        ih hchildValid hchildNormal
      exact
        NormalSelectionSetObservableLeaf.abstractInlineFragment hnonObject
          hmem hchildLeaf

theorem normalSelectionSetDiffTrace_ne_nil
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetDiffTrace schema parentType left right responsePath
      -> responsePath ≠ [] := by
  intro htrace
  induction htrace with
  | objectLeftResponseName _hobject _hmem _hno =>
      simp
  | objectRightResponseName _hobject _hmem _hno =>
      simp
  | objectFieldName _hobject _hleftMem _hrightMem _hfield =>
      simp
  | objectArguments _hobject _hleftMem _hrightMem _harguments =>
      simp
  | objectChild _hobject _hreturnType _hleftMem _hrightMem _harguments
      _hchildTrace _ih =>
      simp
  | abstractLeftTypeCondition _hnonObject _hmem _hno hpath =>
      exact normalSelectionSetResponsePath_ne_nil hpath
  | abstractRightTypeCondition _hnonObject _hmem _hno hpath =>
      exact normalSelectionSetResponsePath_ne_nil hpath
  | abstractChild _hnonObject _hleftMem _hrightMem _hchildTrace ih =>
      exact ih

theorem normalSelectionSetDiff_of_diffTrace
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetDiffTrace schema parentType left right responsePath
      -> NormalSelectionSetDiff schema parentType left right := by
  intro htrace
  induction htrace with
  | objectLeftResponseName hobject hmem hno =>
      exact NormalSelectionSetDiff.objectLeftResponseName hobject hmem hno
  | objectRightResponseName hobject hmem hno =>
      exact NormalSelectionSetDiff.objectRightResponseName hobject hmem hno
  | objectFieldName hobject hleftMem hrightMem hfield =>
      exact NormalSelectionSetDiff.objectFieldName hobject hleftMem
        hrightMem hfield
  | objectArguments hobject hleftMem hrightMem harguments =>
      exact NormalSelectionSetDiff.objectArguments hobject hleftMem
        hrightMem harguments
  | objectChild hobject hreturnType hleftMem hrightMem harguments
      _hchildTrace ih =>
      exact NormalSelectionSetDiff.objectChild hobject hreturnType hleftMem
        hrightMem harguments ih
  | abstractLeftTypeCondition hnonObject hmem hno _hpath =>
      exact NormalSelectionSetDiff.abstractLeftTypeCondition hnonObject
        hmem hno
  | abstractRightTypeCondition hnonObject hmem hno _hpath =>
      exact NormalSelectionSetDiff.abstractRightTypeCondition hnonObject
        hmem hno
  | abstractChild hnonObject hleftMem hrightMem _hchildTrace ih =>
      exact NormalSelectionSetDiff.abstractChild hnonObject hleftMem
        hrightMem ih

theorem normalSelectionSetResponsePath_left_or_right_of_diffTrace
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetDiffTrace schema parentType left right responsePath
      -> NormalSelectionSetResponsePath schema parentType left responsePath
          ∨ NormalSelectionSetResponsePath schema parentType right responsePath := by
  intro htrace
  induction htrace with
  | objectLeftResponseName hobject hleftMem _hrightNoResponseName =>
      exact Or.inl (NormalSelectionSetResponsePath.objectHere hobject hleftMem)
  | objectRightResponseName hobject hrightMem _hleftNoResponseName =>
      exact Or.inr (NormalSelectionSetResponsePath.objectHere hobject hrightMem)
  | objectFieldName hobject hleftMem _hrightMem _hfieldDiff =>
      exact Or.inl (NormalSelectionSetResponsePath.objectHere hobject hleftMem)
  | objectArguments hobject hleftMem _hrightMem _hargumentsDiff =>
      exact Or.inl (NormalSelectionSetResponsePath.objectHere hobject hleftMem)
  | objectChild hobject hreturnType hleftMem hrightMem _harguments
      _hchildTrace ih =>
      rename_i traceParentType returnType traceLeft traceRight responseName
        fieldName leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet childPath
      cases hlookup : schema.lookupField traceParentType fieldName with
      | none =>
          simp [Schema.fieldReturnType?, hlookup] at hreturnType
      | some fieldDefinition =>
          have hreturnEq :
              fieldDefinition.outputType.namedType = returnType :=
            fieldDefinition_namedType_eq_of_fieldReturnType? hlookup
              hreturnType
          subst returnType
          rcases ih with hleftPath | hrightPath
          · exact
              Or.inl
                (NormalSelectionSetResponsePath.objectChild hobject hleftMem
                  hlookup hleftPath)
          · exact
              Or.inr
                (NormalSelectionSetResponsePath.objectChild hobject hrightMem
                  hlookup hrightPath)
  | abstractLeftTypeCondition hnonObject hleftMem _hrightNoTypeCondition
      hpath =>
      exact
        Or.inl
          (NormalSelectionSetResponsePath.abstractInlineFragment hnonObject
            hleftMem hpath)
  | abstractRightTypeCondition hnonObject hrightMem _hleftNoTypeCondition
      hpath =>
      exact
        Or.inr
          (NormalSelectionSetResponsePath.abstractInlineFragment hnonObject
            hrightMem hpath)
  | abstractChild hnonObject hleftMem hrightMem _hchildTrace ih =>
      rcases ih with hleftPath | hrightPath
      · exact
          Or.inl
            (NormalSelectionSetResponsePath.abstractInlineFragment hnonObject
              hleftMem hleftPath)
      · exact
          Or.inr
            (NormalSelectionSetResponsePath.abstractInlineFragment hnonObject
              hrightMem hrightPath)

theorem normalSelectionSetObservableLeaf_left_or_right_of_diffTrace_valid_normal
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> NormalSelectionSetDiffTrace schema parentType left right responsePath
      -> NormalSelectionSetObservableLeaf schema parentType left
          ∨ NormalSelectionSetObservableLeaf schema parentType right := by
  intro hleftValid hrightValid hleftNormal hrightNormal htrace
  rcases normalSelectionSetResponsePath_left_or_right_of_diffTrace htrace with
    hleftPath | hrightPath
  · exact
      Or.inl
        (normalSelectionSetObservableLeaf_of_responsePath_valid_normal
          hleftValid hleftNormal hleftPath)
  · exact
      Or.inr
        (normalSelectionSetObservableLeaf_of_responsePath_valid_normal
          hrightValid hrightNormal hrightPath)

theorem normalSelectionSetDiffTrace_left_or_right_nonempty
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetDiffTrace schema parentType left right responsePath
      -> left ≠ [] ∨ right ≠ [] := by
  intro htrace
  rcases normalSelectionSetResponsePath_left_or_right_of_diffTrace htrace with
    hleftPath | hrightPath
  · exact Or.inl (normalSelectionSetResponsePath_selectionSet_nonempty hleftPath)
  · exact Or.inr (normalSelectionSetResponsePath_selectionSet_nonempty hrightPath)

theorem normalSelectionSetDiffTrace_of_valid_normal_diff
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> NormalSelectionSetDiff schema parentType left right
      -> ∃ responsePath,
          NormalSelectionSetDiffTrace schema parentType left right responsePath := by
  intro hleftValid hrightValid hleftNormal hrightNormal hdiff
  revert leftVariableDefinitions rightVariableDefinitions
  induction hdiff with
  | objectLeftResponseName hobject hleftMem hrightNoResponseName =>
      intro _leftVariableDefinitions _rightVariableDefinitions _hleftValid
        _hrightValid
      exact ⟨
        [_],
        NormalSelectionSetDiffTrace.objectLeftResponseName hobject hleftMem
          hrightNoResponseName
      ⟩
  | objectRightResponseName hobject hrightMem hleftNoResponseName =>
      intro _leftVariableDefinitions _rightVariableDefinitions _hleftValid
        _hrightValid
      exact ⟨
        [_],
        NormalSelectionSetDiffTrace.objectRightResponseName hobject
          hrightMem hleftNoResponseName
      ⟩
  | objectFieldName hobject hleftMem hrightMem hfieldDiff =>
      intro _leftVariableDefinitions _rightVariableDefinitions _hleftValid
        _hrightValid
      exact ⟨
        [_],
        NormalSelectionSetDiffTrace.objectFieldName hobject hleftMem hrightMem hfieldDiff
      ⟩
  | objectArguments hobject hleftMem hrightMem hargumentsDiff =>
      intro _leftVariableDefinitions _rightVariableDefinitions _hleftValid
        _hrightValid
      exact ⟨
        [_],
        NormalSelectionSetDiffTrace.objectArguments hobject hleftMem
          hrightMem hargumentsDiff
      ⟩
  | objectChild hobject hreturnType hleftMem hrightMem harguments hchildDiff ih =>
      rename_i diffParentType returnType diffLeft diffRight responseName
        fieldName leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions hleftValid
        hrightValid
      rcases
          selectionSetValid_field_children_of_diff hleftValid hrightValid
            hleftMem hrightMem hreturnType hchildDiff with
        ⟨_fieldDefinition, _hlookup, _hnamedType, hleftChildValid,
          hrightChildValid⟩
      rcases
          selectionSetNormal_field_child_of_mem_with_returnType hleftNormal
            hleftMem with
        ⟨leftReturnType, hleftReturnType, hleftChildNormal⟩
      have hleftReturnTypeEq : leftReturnType = returnType := by
        rw [hreturnType] at hleftReturnType
        exact Option.some.inj hleftReturnType.symm
      subst leftReturnType
      rcases
          selectionSetNormal_field_child_of_mem_with_returnType hrightNormal
            hrightMem with
        ⟨rightReturnType, hrightReturnType, hrightChildNormal⟩
      have hrightReturnTypeEq : rightReturnType = returnType := by
        rw [hreturnType] at hrightReturnType
        exact Option.some.inj hrightReturnType.symm
      subst rightReturnType
      rcases
          ih hleftChildNormal hrightChildNormal hleftChildValid
            hrightChildValid with
        ⟨childPath, hchildTrace⟩
      exact ⟨
        _ :: childPath,
        NormalSelectionSetDiffTrace.objectChild hobject hreturnType
          hleftMem hrightMem harguments hchildTrace
      ⟩
  | abstractLeftTypeCondition hnonObject hleftMem hrightNoTypeCondition =>
      intro leftVariableDefinitions _rightVariableDefinitions hleftValid
        _hrightValid
      have hchildValid :
          Validation.selectionSetValid schema leftVariableDefinitions
            _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hleftValid
          hleftMem
      rcases
          selectionSetNormal_inlineFragment_child_of_mem hleftNormal
            hleftMem with
        ⟨_htypeObject, hchildNormal⟩
      rcases
          normalSelectionSetResponsePath_of_valid_normal_nonempty hchildValid
            hchildNormal
            (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
              hleftValid hleftMem) with
        ⟨childPath, hchildPath⟩
      exact ⟨
        childPath,
        NormalSelectionSetDiffTrace.abstractLeftTypeCondition hnonObject
          hleftMem hrightNoTypeCondition hchildPath
      ⟩
  | abstractRightTypeCondition hnonObject hrightMem hleftNoTypeCondition =>
      intro _leftVariableDefinitions rightVariableDefinitions _hleftValid
        hrightValid
      have hchildValid :
          Validation.selectionSetValid schema rightVariableDefinitions
            _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hrightValid
          hrightMem
      rcases
          selectionSetNormal_inlineFragment_child_of_mem hrightNormal
            hrightMem with
        ⟨_htypeObject, hchildNormal⟩
      rcases
          normalSelectionSetResponsePath_of_valid_normal_nonempty hchildValid
            hchildNormal
            (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
              hrightValid hrightMem) with
        ⟨childPath, hchildPath⟩
      exact ⟨
        childPath,
        NormalSelectionSetDiffTrace.abstractRightTypeCondition hnonObject
          hrightMem hleftNoTypeCondition hchildPath
      ⟩
  | abstractChild hnonObject hleftMem hrightMem hchildDiff ih =>
      intro leftVariableDefinitions rightVariableDefinitions hleftValid
        hrightValid
      have hleftChildValid :
          Validation.selectionSetValid schema leftVariableDefinitions _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hleftValid
          hleftMem
      have hrightChildValid :
          Validation.selectionSetValid schema rightVariableDefinitions _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hrightValid
          hrightMem
      have hleftChildNormal :
          selectionSetNormal schema _ _ :=
        (selectionSetNormal_inlineFragment_child_of_mem hleftNormal
          hleftMem).2
      have hrightChildNormal :
          selectionSetNormal schema _ _ :=
        (selectionSetNormal_inlineFragment_child_of_mem hrightNormal
          hrightMem).2
      rcases
          ih hleftChildNormal hrightChildNormal hleftChildValid
            hrightChildValid with
        ⟨childPath, hchildTrace⟩
      exact ⟨
        childPath,
        NormalSelectionSetDiffTrace.abstractChild hnonObject hleftMem
          hrightMem hchildTrace
      ⟩

theorem normalSelectionSetDiffObservableTrace_of_valid_normal_diff
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> NormalSelectionSetDiff schema parentType left right
      -> ∃ responsePath,
          NormalSelectionSetDiffObservableTrace schema parentType left right
            responsePath := by
  intro hleftValid hrightValid hleftNormal hrightNormal hdiff
  revert leftVariableDefinitions rightVariableDefinitions
  induction hdiff with
  | objectLeftResponseName hobject hleftMem hrightNoResponseName =>
      intro _leftVariableDefinitions _rightVariableDefinitions _hleftValid
        _hrightValid
      exact ⟨
        [_],
        NormalSelectionSetDiffObservableTrace.objectLeftResponseName
          hobject hleftMem hrightNoResponseName
      ⟩
  | objectRightResponseName hobject hrightMem hleftNoResponseName =>
      intro _leftVariableDefinitions _rightVariableDefinitions _hleftValid
        _hrightValid
      exact ⟨
        [_],
        NormalSelectionSetDiffObservableTrace.objectRightResponseName
          hobject hrightMem hleftNoResponseName
      ⟩
  | objectFieldName hobject hleftMem hrightMem hfieldDiff =>
      intro leftVariableDefinitions rightVariableDefinitions hleftValid
        hrightValid
      rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
        ⟨leftFieldDefinition, hleftLookup, _hleftArguments,
          _hleftFieldValid⟩
      rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
        ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
          _hrightFieldValid⟩
      by_cases hleftLeaf :
          (TypeRef.named
            leftFieldDefinition.outputType.namedType).isCompositeBool
            schema = false
      · by_cases hrightLeaf :
            (TypeRef.named
              rightFieldDefinition.outputType.namedType).isCompositeBool
              schema = false
        · exact ⟨
            [_],
            NormalSelectionSetDiffObservableTrace.objectFieldNameLeaf
              hobject hleftMem hrightMem hleftLookup hrightLookup
              hleftLeaf hrightLeaf hfieldDiff
          ⟩
        · have hrightComposite :
              (TypeRef.named
                rightFieldDefinition.outputType.namedType).isCompositeBool
                schema = true := by
            cases h :
                (TypeRef.named
                  rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema <;>
              simp [h] at hrightLeaf ⊢
          rcases
              normalSelectionSetObservableResponsePath_of_valid_normal_composite_field_mem
                hrightValid hrightNormal hrightMem hrightLookup
                hrightComposite with
            ⟨childPath, hchildPath⟩
          exact ⟨
            _ :: childPath,
            NormalSelectionSetDiffObservableTrace.objectFieldNameCompositeRight
              hobject hleftMem hrightMem hleftLookup hrightLookup
              hrightComposite hchildPath hfieldDiff
          ⟩
      · have hleftComposite :
            (TypeRef.named
              leftFieldDefinition.outputType.namedType).isCompositeBool
              schema = true := by
          cases h :
              (TypeRef.named
                leftFieldDefinition.outputType.namedType).isCompositeBool
                schema <;>
            simp [h] at hleftLeaf ⊢
        rcases
            normalSelectionSetObservableResponsePath_of_valid_normal_composite_field_mem
              hleftValid hleftNormal hleftMem hleftLookup
              hleftComposite with
          ⟨childPath, hchildPath⟩
        exact ⟨
          _ :: childPath,
          NormalSelectionSetDiffObservableTrace.objectFieldNameCompositeLeft
            hobject hleftMem hrightMem hleftLookup hrightLookup
            hleftComposite hchildPath hfieldDiff
        ⟩
  | objectArguments hobject hleftMem hrightMem hargumentsDiff =>
      intro leftVariableDefinitions _rightVariableDefinitions hleftValid
        _hrightValid
      rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
        ⟨fieldDefinition, hlookup, _harguments, _hfieldValid⟩
      by_cases hleaf :
          (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
            schema = false
      · exact ⟨
          [_],
          NormalSelectionSetDiffObservableTrace.objectArgumentsLeaf
            hobject hleftMem hrightMem hlookup hleaf hargumentsDiff
        ⟩
      · have hcomposite :
            (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool
              schema = true := by
          cases h :
              (TypeRef.named
                fieldDefinition.outputType.namedType).isCompositeBool
                schema <;>
            simp [h] at hleaf ⊢
        rcases
            normalSelectionSetObservableResponsePath_of_valid_normal_composite_field_mem
              hleftValid hleftNormal hleftMem hlookup hcomposite with
          ⟨childPath, hchildPath⟩
        exact ⟨
          _ :: childPath,
          NormalSelectionSetDiffObservableTrace.objectArgumentsCompositeLeft
            hobject hleftMem hrightMem hlookup hcomposite hchildPath
            hargumentsDiff
        ⟩
  | objectChild hobject hreturnType hleftMem hrightMem harguments hchildDiff ih =>
      rename_i diffParentType returnType diffLeft diffRight responseName
        fieldName leftArguments rightArguments leftDirectives rightDirectives
        leftChildSelectionSet rightChildSelectionSet
      intro leftVariableDefinitions rightVariableDefinitions hleftValid
        hrightValid
      rcases
          selectionSetValid_field_children_of_diff hleftValid hrightValid
            hleftMem hrightMem hreturnType hchildDiff with
        ⟨_fieldDefinition, _hlookup, _hnamedType, hleftChildValid,
          hrightChildValid⟩
      rcases
          selectionSetNormal_field_child_of_mem_with_returnType hleftNormal
            hleftMem with
        ⟨leftReturnType, hleftReturnType, hleftChildNormal⟩
      have hleftReturnTypeEq : leftReturnType = returnType := by
        rw [hreturnType] at hleftReturnType
        exact Option.some.inj hleftReturnType.symm
      subst leftReturnType
      rcases
          selectionSetNormal_field_child_of_mem_with_returnType hrightNormal
            hrightMem with
        ⟨rightReturnType, hrightReturnType, hrightChildNormal⟩
      have hrightReturnTypeEq : rightReturnType = returnType := by
        rw [hreturnType] at hrightReturnType
        exact Option.some.inj hrightReturnType.symm
      subst rightReturnType
      rcases
          ih hleftChildNormal hrightChildNormal hleftChildValid
            hrightChildValid with
        ⟨childPath, hchildTrace⟩
      exact ⟨
        responseName :: childPath,
        NormalSelectionSetDiffObservableTrace.objectChild hobject
          hreturnType hleftMem hrightMem harguments hchildTrace
      ⟩
  | abstractLeftTypeCondition hnonObject hleftMem hrightNoTypeCondition =>
      intro leftVariableDefinitions _rightVariableDefinitions hleftValid
        _hrightValid
      have hchildValid :
          Validation.selectionSetValid schema leftVariableDefinitions
            _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hleftValid
          hleftMem
      rcases
          selectionSetNormal_inlineFragment_child_of_mem hleftNormal
            hleftMem with
        ⟨_htypeObject, hchildNormal⟩
      rcases
          normalSelectionSetObservableResponsePath_of_observableLeaf
            (normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
              _ leftVariableDefinitions _ hchildValid hchildNormal
              (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
                hleftValid hleftMem)) with
        ⟨childPath, hchildPath⟩
      exact ⟨
        childPath,
        NormalSelectionSetDiffObservableTrace.abstractLeftTypeCondition
          hnonObject hleftMem hrightNoTypeCondition hchildPath
      ⟩
  | abstractRightTypeCondition hnonObject hrightMem hleftNoTypeCondition =>
      intro _leftVariableDefinitions rightVariableDefinitions _hleftValid
        hrightValid
      have hchildValid :
          Validation.selectionSetValid schema rightVariableDefinitions
            _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hrightValid
          hrightMem
      rcases
          selectionSetNormal_inlineFragment_child_of_mem hrightNormal
            hrightMem with
        ⟨_htypeObject, hchildNormal⟩
      rcases
          normalSelectionSetObservableResponsePath_of_observableLeaf
            (normalSelectionSetObservableLeaf_of_valid_normal_nonempty schema
              _ rightVariableDefinitions _ hchildValid hchildNormal
              (selectionSetValid_inlineFragment_some_child_nonempty_of_mem
                hrightValid hrightMem)) with
        ⟨childPath, hchildPath⟩
      exact ⟨
        childPath,
        NormalSelectionSetDiffObservableTrace.abstractRightTypeCondition
          hnonObject hrightMem hleftNoTypeCondition hchildPath
      ⟩
  | abstractChild hnonObject hleftMem hrightMem hchildDiff ih =>
      intro leftVariableDefinitions rightVariableDefinitions hleftValid
        hrightValid
      have hleftChildValid :
          Validation.selectionSetValid schema leftVariableDefinitions _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hleftValid
          hleftMem
      have hrightChildValid :
          Validation.selectionSetValid schema rightVariableDefinitions _ _ :=
        selectionSetValid_inlineFragment_some_child_of_mem hrightValid
          hrightMem
      have hleftChildNormal :
          selectionSetNormal schema _ _ :=
        (selectionSetNormal_inlineFragment_child_of_mem hleftNormal
          hleftMem).2
      have hrightChildNormal :
          selectionSetNormal schema _ _ :=
        (selectionSetNormal_inlineFragment_child_of_mem hrightNormal
          hrightMem).2
      rcases
          ih hleftChildNormal hrightChildNormal hleftChildValid
            hrightChildValid with
        ⟨childPath, hchildTrace⟩
      exact ⟨
        childPath,
        NormalSelectionSetDiffObservableTrace.abstractChild hnonObject
          hleftMem hrightMem hchildTrace
      ⟩

theorem normalSelectionSetDiffTrace_exists_of_observableTrace
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetDiffObservableTrace schema parentType left right responsePath
      -> ∃ collapsedResponsePath,
          NormalSelectionSetDiffTrace schema parentType left right
            collapsedResponsePath := by
  intro htrace
  induction htrace with
  | objectLeftResponseName hobject hleftMem hrightNoResponseName =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectLeftResponseName hobject
          hleftMem hrightNoResponseName
      ⟩
  | objectRightResponseName hobject hrightMem hleftNoResponseName =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectRightResponseName hobject
          hrightMem hleftNoResponseName
      ⟩
  | objectFieldNameLeaf hobject hleftMem hrightMem _hleftLookup
      _hrightLookup _hleftLeaf _hrightLeaf hfieldDiff =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectFieldName hobject hleftMem hrightMem hfieldDiff
      ⟩
  | objectFieldNameCompositeLeft hobject hleftMem hrightMem _hleftLookup
      _hrightLookup _hleftComposite _hchildPath hfieldDiff =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectFieldName hobject hleftMem hrightMem hfieldDiff
      ⟩
  | objectFieldNameCompositeRight hobject hleftMem hrightMem _hleftLookup
      _hrightLookup _hrightComposite _hchildPath hfieldDiff =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectFieldName hobject hleftMem hrightMem hfieldDiff
      ⟩
  | objectArgumentsLeaf hobject hleftMem hrightMem _hlookup _hleaf
      hargumentsDiff =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectArguments hobject hleftMem
          hrightMem hargumentsDiff
      ⟩
  | objectArgumentsCompositeLeft hobject hleftMem hrightMem _hlookup
      _hcomposite _hchildPath hargumentsDiff =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectArguments hobject hleftMem
          hrightMem hargumentsDiff
      ⟩
  | objectChild hobject hreturnType hleftMem hrightMem harguments
      _hchildTrace ih =>
      rcases ih with ⟨childPath, hchildTrace⟩
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.objectChild hobject hreturnType
          hleftMem hrightMem harguments hchildTrace
      ⟩
  | abstractLeftTypeCondition hnonObject hleftMem hrightNoTypeCondition
      hchildPath =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.abstractLeftTypeCondition hnonObject
          hleftMem hrightNoTypeCondition hchildPath.to_responsePath
      ⟩
  | abstractRightTypeCondition hnonObject hrightMem hleftNoTypeCondition
      hchildPath =>
      exact ⟨
        _,
        NormalSelectionSetDiffTrace.abstractRightTypeCondition hnonObject
          hrightMem hleftNoTypeCondition hchildPath.to_responsePath
      ⟩
  | abstractChild hnonObject hleftMem hrightMem _hchildTrace ih =>
      rcases ih with ⟨childPath, hchildTrace⟩
      exact ⟨
        childPath,
        NormalSelectionSetDiffTrace.abstractChild hnonObject hleftMem
          hrightMem hchildTrace
      ⟩

theorem normalSelectionSetDiff_of_observableTrace
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetDiffObservableTrace schema parentType left right responsePath
      -> NormalSelectionSetDiff schema parentType left right := by
  intro htrace
  rcases normalSelectionSetDiffTrace_exists_of_observableTrace htrace with
    ⟨_collapsedResponsePath, hcollapsedTrace⟩
  exact normalSelectionSetDiff_of_diffTrace hcollapsedTrace

end GroundTypeNormalization

end NormalForm

end GraphQL
