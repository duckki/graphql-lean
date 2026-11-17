import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Operation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Validity

/-!
Ground-type normalization preserves the September 2025 non-emptiness rule.

`normalizeOperation_subselectionsNonempty` shows that normalizing a source operation that
meets `operationSubselectionsNonempty` produces an operation that meets it too.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

/-
Proof-internal invariant for ground normalization: along the object scopes that
normalization visits, every composite field keeps a non-empty child selection set whose
inline fragments are non-empty. Inline fragments are followed only in the current
object scope, so Boolean filtering preserves it.
-/
mutual
  def selectionSubselectionsNonemptyOnObjectPaths (schema : Schema) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∀ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          -> (schema.isCompositeType fieldDefinition.outputType.namedType
                -> selectionSet ≠ [])
              ∧ selectionSetInlineFragmentsNonempty selectionSet
              ∧ ∀ objectType,
                  objectType
                    ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
                  -> selectionSetSubselectionsNonemptyOnObjectPaths schema objectType
                      selectionSet
    | .inlineFragment none _directives selectionSet =>
        selectionSetSubselectionsNonemptyOnObjectPaths schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typesOverlapBool parentType typeCondition = true
        -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType selectionSet

  def selectionSetSubselectionsNonemptyOnObjectPaths (schema : Schema) (parentType : Name)
      : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionSubselectionsNonemptyOnObjectPaths schema parentType selection
        ∧ selectionSetSubselectionsNonemptyOnObjectPaths schema parentType rest
end

theorem selectionSetSubselectionsNonemptyOnObjectPaths_nil
    (schema : Schema)
    (parentType : Name)
    : selectionSetSubselectionsNonemptyOnObjectPaths schema parentType [] := by
  simp [selectionSetSubselectionsNonemptyOnObjectPaths]

theorem selectionSetSubselectionsNonemptyOnObjectPaths_cons
    {schema : Schema}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : selectionSubselectionsNonemptyOnObjectPaths schema parentType selection
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType selectionSet
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema
          parentType (selection :: selectionSet) := by
  intro hselection hselectionSet
  simp [selectionSetSubselectionsNonemptyOnObjectPaths, hselection,
    hselectionSet]

theorem selectionSetSubselectionsNonemptyOnObjectPaths_head
    {schema : Schema}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : selectionSetSubselectionsNonemptyOnObjectPaths schema
        parentType (selection :: selectionSet)
      -> selectionSubselectionsNonemptyOnObjectPaths schema parentType selection := by
  intro hvalid
  simpa [selectionSetSubselectionsNonemptyOnObjectPaths] using hvalid.1

theorem selectionSetSubselectionsNonemptyOnObjectPaths_tail
    {schema : Schema}
    {parentType : Name} {selection : Selection}
    {selectionSet : List Selection}
    : selectionSetSubselectionsNonemptyOnObjectPaths schema
        parentType (selection :: selectionSet)
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema
          parentType selectionSet := by
  intro hvalid
  simpa [selectionSetSubselectionsNonemptyOnObjectPaths] using hvalid.2

theorem selectionSetSubselectionsNonemptyOnObjectPaths_append
    {schema : Schema}
    {parentType : Name} {left right : List Selection}
    : selectionSetSubselectionsNonemptyOnObjectPaths schema parentType left
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType right
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema
          parentType (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons selection rest ih =>
      have hhead :=
        selectionSetSubselectionsNonemptyOnObjectPaths_head hleft
      have htail :=
        selectionSetSubselectionsNonemptyOnObjectPaths_tail hleft
      simp [selectionSetSubselectionsNonemptyOnObjectPaths]
      exact ⟨hhead, ih htail⟩

theorem
    selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
    (schema : Schema) (responseName : Name)
    : ∀ parentType selectionSet,
        selectionSetSubselectionsNonemptyOnObjectPaths schema parentType selectionSet
        -> selectionSetSubselectionsNonemptyOnObjectPaths schema
            parentType
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | _parentType, [], _hvalid => by
      simp [withoutFieldSelectionsWithResponseName,
        selectionSetSubselectionsNonemptyOnObjectPaths]
  | parentType, selection :: rest, hvalid => by
      have hhead :=
        selectionSetSubselectionsNonemptyOnObjectPaths_head hvalid
      have htail :=
        selectionSetSubselectionsNonemptyOnObjectPaths_tail hvalid
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            exact
              selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
                schema responseName parentType rest htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse,
              selectionSetSubselectionsNonemptyOnObjectPaths]
            exact ⟨hhead,
              selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
                schema responseName parentType rest htail⟩
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldSelectionsWithResponseName,
            selectionSetSubselectionsNonemptyOnObjectPaths]
          constructor
          · cases typeCondition with
            | none =>
                have hbody :
                    selectionSetSubselectionsNonemptyOnObjectPaths schema
                      parentType selectionSet := by
                  simpa [selectionSubselectionsNonemptyOnObjectPaths] using hhead
                exact
                  selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
                    schema responseName parentType selectionSet hbody
            | some typeCondition =>
                intro hoverlap
                have hbody :
                    selectionSetSubselectionsNonemptyOnObjectPaths schema
                      parentType selectionSet := by
                  simpa [selectionSubselectionsNonemptyOnObjectPaths] using
                    hhead hoverlap
                exact
                  selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
                    schema responseName parentType selectionSet hbody
          · exact
              selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
                schema responseName parentType rest htail

theorem selectionSetSubselectionsNonemptyOnObjectPaths_mergeSelectionSets_of_subselections
    {schema : Schema} {parentType : Name}
    : ∀ selections,
        (∀ selection,
          selection ∈ selections
          -> selectionSetSubselectionsNonemptyOnObjectPaths schema
              parentType selection.subselections)
        -> selectionSetSubselectionsNonemptyOnObjectPaths schema
            parentType (mergeSelectionSets selections)
  | [], _hvalid => by
      simp [mergeSelectionSets,
        selectionSetSubselectionsNonemptyOnObjectPaths]
  | selection :: rest, hvalid => by
      simp [mergeSelectionSets]
      apply selectionSetSubselectionsNonemptyOnObjectPaths_append
      · exact hvalid selection (by simp)
      · exact
          selectionSetSubselectionsNonemptyOnObjectPaths_mergeSelectionSets_of_subselections
            rest (by
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate]))

theorem
    selectionSetSubselectionsNonemptyOnObjectPaths_mergeSelectionSets_of_field_subselections
    {schema : Schema} {parentType responseName : Name} (selections : List Selection)
    : (∀ selection,
        selection ∈ selections
        -> ∃ fieldName arguments directives subselections,
            selection
            = Selection.field responseName fieldName arguments directives subselections)
      -> (∀ fieldName arguments directives subselections,
            Selection.field responseName fieldName arguments directives subselections
              ∈ selections
            -> selectionSetSubselectionsNonemptyOnObjectPaths schema
                parentType subselections)
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema
          parentType (mergeSelectionSets selections) := by
  intro hshape hfields
  apply selectionSetSubselectionsNonemptyOnObjectPaths_mergeSelectionSets_of_subselections
  intro selection hselection
  rcases hshape selection hselection with
    ⟨fieldName, arguments, directives, subselections, hselectionShape⟩
  subst selection
  simpa [Selection.subselections]
    using hfields fieldName arguments directives subselections hselection

theorem selectionSubselectionsNonemptyOnObjectPaths_field_child
    {schema : Schema}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {subselections : List Selection} {fieldDefinition : FieldDefinition}
    {childType : Name}
    : selectionSubselectionsNonemptyOnObjectPaths schema parentType
        (Selection.field responseName fieldName arguments directives subselections)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> childType ∈ schema.getPossibleTypes fieldDefinition.outputType.namedType
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema
          childType subselections := by
  intro hvalid hlookup hchildType
  simp only [selectionSubselectionsNonemptyOnObjectPaths] at hvalid
  exact (hvalid fieldDefinition hlookup).2.2 childType hchildType

theorem fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
    (schema : Schema) (parentType responseName : Name)
    : schema.objectType parentType
      -> ∀ selectionSet,
          selectionSetSubselectionsNonemptyOnObjectPaths schema parentType selectionSet
          -> ∀ fieldName arguments directives subselections,
              Selection.field responseName fieldName arguments directives subselections
                ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                    selectionSet
              -> selectionSubselectionsNonemptyOnObjectPaths schema parentType
                  (Selection.field responseName fieldName arguments directives
                    subselections)
  | hobject, [], himplementation, fieldName, arguments, directives,
      subselections, hfield => by
      simp [fieldSelectionsWithResponseNameInScope] at hfield
  | hobject, selection :: rest, himplementation, fieldName, arguments,
      directives, subselections, hfield => by
      have hheadImplementation :
          selectionSubselectionsNonemptyOnObjectPaths schema parentType selection :=
        selectionSetSubselectionsNonemptyOnObjectPaths_head himplementation
      have htailImplementation :
          selectionSetSubselectionsNonemptyOnObjectPaths schema
            parentType rest :=
        selectionSetSubselectionsNonemptyOnObjectPaths_tail himplementation
      cases selection with
      | field fieldResponseName matchedFieldName matchedArguments
          matchedDirectives matchedSubselections =>
          by_cases hname : (fieldResponseName == responseName) = true
          · have hresponse : fieldResponseName = responseName :=
              beq_iff_eq.mp hname
            subst fieldResponseName
            simp [fieldSelectionsWithResponseNameInScope] at hfield
            rcases hfield with hhead | htail
            · rcases hhead with
                ⟨hfieldName, harguments, hdirectives, hsubselections⟩
              subst fieldName
              subst arguments
              subst directives
              subst subselections
              exact hheadImplementation
            · exact
                fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
                  schema parentType responseName hobject
                  rest htailImplementation fieldName arguments directives
                  subselections htail
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
            exact
              fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
                schema parentType responseName hobject
                rest htailImplementation fieldName arguments directives
                subselections hfield
      | inlineFragment typeCondition fragmentDirectives selectionSet =>
          cases typeCondition with
          | none =>
              have hbodyImplementation :
                  selectionSetSubselectionsNonemptyOnObjectPaths schema
                    parentType selectionSet := by
                simpa [selectionSubselectionsNonemptyOnObjectPaths] using
                  hheadImplementation
              simp [fieldSelectionsWithResponseNameInScope] at hfield
              rcases hfield with hbody | htail
              · exact
                  fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
                    schema parentType responseName
                    hobject selectionSet hbodyImplementation fieldName
                    arguments directives subselections hbody
              · exact
                  fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
                    schema parentType responseName
                    hobject rest htailImplementation fieldName arguments
                    directives subselections htail
          | some typeCondition =>
              by_cases hoverlap :
                  schema.typesOverlapBool parentType typeCondition = true
              · have hbodyImplementation :
                    selectionSetSubselectionsNonemptyOnObjectPaths schema
                      parentType selectionSet := by
                  simpa [selectionSubselectionsNonemptyOnObjectPaths] using
                    hheadImplementation hoverlap
                simp [fieldSelectionsWithResponseNameInScope, hoverlap] at hfield
                rcases hfield with hbody | htail
                · exact
                    fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
                      schema parentType responseName
                      hobject selectionSet hbodyImplementation fieldName
                      arguments directives subselections hbody
                · exact
                    fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
                      schema parentType responseName
                      hobject rest htailImplementation fieldName arguments
                      directives subselections htail
              · have hfalse :
                    schema.typesOverlapBool parentType typeCondition =
                      false := by
                  cases hmatch :
                      schema.typesOverlapBool parentType typeCondition
                  · rfl
                  · contradiction
                simp [fieldSelectionsWithResponseNameInScope, hfalse] at hfield
                exact
                  fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
                    schema parentType responseName
                    hobject rest htailImplementation fieldName arguments
                    directives subselections hfield

theorem
    selectionSetSubselectionsNonemptyOnObjectPaths_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    {schema : Schema} {parentType responseName childType : Name}
    (selectionSet : List Selection)
    : (∀ fieldName arguments directives subselections,
        Selection.field responseName fieldName arguments directives subselections
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet
        -> selectionSetSubselectionsNonemptyOnObjectPaths schema childType subselections)
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema
          childType
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              selectionSet)) := by
  intro hfields
  apply selectionSetSubselectionsNonemptyOnObjectPaths_mergeSelectionSets_of_field_subselections
  · intro selection hselection
    exact fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      selectionSet selection hselection
  · intro fieldName arguments directives subselections hselection
    exact hfields fieldName arguments directives subselections hselection

theorem
    fieldSelectionsWithResponseNameInScope_matching_subselections_subselectionsNonemptyOnObjectPaths_of_child_object
    (schema : Schema) (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> ∀ matchedFieldName matchedArguments matchedDirectives matchedSubselections,
          Selection.field responseName matchedFieldName matchedArguments
              matchedDirectives matchedSubselections
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest
          -> selectionSetSubselectionsNonemptyOnObjectPaths schema runtimeType
              matchedSubselections := by
  intro hobject hlookupValid hnonempty hmerge hlookup hinclude
    matchedFieldName matchedArguments matchedDirectives matchedSubselections
    hmatched
  have hmatchedNonempty :=
    fieldSelectionsWithResponseNameInScope_field_subselectionsNonemptyOnObjectPaths
      schema parentType responseName hobject rest
      (selectionSetSubselectionsNonemptyOnObjectPaths_tail hnonempty)
      matchedFieldName matchedArguments matchedDirectives matchedSubselections hmatched
  have hsame :
      matchedFieldName = fieldName :=
    runtimeMergeSource_matching_same_field
      schema parentType responseName fieldName arguments subselections rest
      hobject hlookupValid hmerge matchedFieldName matchedArguments
      matchedDirectives matchedSubselections hmatched
  subst matchedFieldName
  exact selectionSubselectionsNonemptyOnObjectPaths_field_child hmatchedNonempty hlookup
    (List.contains_iff_mem.mp hinclude)

theorem selectionSetSubselectionsNonemptyOnObjectPaths_fieldHead_merged_of_child_object
    (schema : Schema)
    (parentType responseName fieldName runtimeType : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : schema.objectType parentType
      -> selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> selectionSetSubselectionsNonemptyOnObjectPaths schema runtimeType
          (subselections
            ++ mergeSelectionSets
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest)) := by
  intro hobject hlookupValid hnonempty hmerge hlookup hinclude
  apply selectionSetSubselectionsNonemptyOnObjectPaths_append
  · exact selectionSubselectionsNonemptyOnObjectPaths_field_child
      (selectionSetSubselectionsNonemptyOnObjectPaths_head hnonempty) hlookup
      (List.contains_iff_mem.mp hinclude)
  · apply
      selectionSetSubselectionsNonemptyOnObjectPaths_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
    intro matchedFieldName matchedArguments matchedDirectives
      matchedSubselections hmatched
    exact
      fieldSelectionsWithResponseNameInScope_matching_subselections_subselectionsNonemptyOnObjectPaths_of_child_object
        schema parentType responseName fieldName runtimeType arguments subselections rest
        fieldDefinition hobject hlookupValid hnonempty hmerge hlookup hinclude
        matchedFieldName matchedArguments matchedDirectives matchedSubselections
        hmatched

mutual
  theorem selectionInlineFragmentsNonempty_of_selectionValid_subselectionsNonempty
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      : ∀ parentType selection,
          Validation.selectionValid schema variableDefinitions parentType selection
          -> selectionSubselectionsNonempty schema parentType selection
          -> selectionInlineFragmentsNonempty selection
    | parentType,
      .field _responseName fieldName _arguments _directives selectionSet,
      hvalid, hnonempty => by
        unfold selectionInlineFragmentsNonempty
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, hchild⟩
        have hchildNonempty :
            selectionSetSubselectionsNonempty schema
              fieldDefinition.outputType.namedType selectionSet := by
          simp only [selectionSubselectionsNonempty, hlookup] at hnonempty
          exact hnonempty.2
        simp [Validation.fieldSelectionSetValid] at hchild
        rcases hchild.2 with hleaf | hcomposite
        · rw [hleaf.2]
          unfold selectionSetInlineFragmentsNonempty
          intro selection hselection
          cases hselection
        · exact
            selectionSetInlineFragmentsNonempty_of_selectionSetValid_subselectionsNonempty
              schema variableDefinitions
              fieldDefinition.outputType.namedType selectionSet
              hcomposite.2 hchildNonempty
    | parentType,
      .inlineFragment none _directives selectionSet, hvalid, hnonempty => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        simp only [selectionSubselectionsNonempty, Option.getD_none] at hnonempty
        exact ⟨hnonempty.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid_subselectionsNonempty
            schema variableDefinitions parentType selectionSet hvalid'.2 hnonempty.2⟩
    | _parentType,
      .inlineFragment (some typeCondition) _directives selectionSet,
      hvalid, hnonempty => by
        unfold selectionInlineFragmentsNonempty
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        simp only [selectionSubselectionsNonempty, Option.getD_some] at hnonempty
        exact ⟨hnonempty.1,
          selectionSetInlineFragmentsNonempty_of_selectionSetValid_subselectionsNonempty
            schema variableDefinitions typeCondition selectionSet
            hvalid'.2.2.2 hnonempty.2⟩

  theorem selectionSetInlineFragmentsNonempty_of_selectionSetValid_subselectionsNonempty
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      : ∀ parentType selectionSet,
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetSubselectionsNonempty schema parentType selectionSet
          -> selectionSetInlineFragmentsNonempty selectionSet
    | parentType, selectionSet, hvalid, hnonempty => by
        unfold selectionSetInlineFragmentsNonempty
        unfold Validation.selectionSetValid at hvalid
        intro selection hselection
        exact selectionInlineFragmentsNonempty_of_selectionValid_subselectionsNonempty
          schema variableDefinitions parentType selection (hvalid selection hselection)
          (selectionSetSubselectionsNonempty_of_mem hnonempty hselection)
end

theorem normalizeSelectionSet_subselectionsNonempty_of_typeConditionFeasible
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ parentType selectionSet,
      ∀ typeConditions,
        schema.objectType parentType
        -> objectSatisfiesTypeConditionStack schema parentType typeConditions
        -> selectionSetSemanticsReady schema parentType selectionSet
        -> runtimeMergeSource schema parentType selectionSet
        -> selectionSetDirectiveFree selectionSet
        -> selectionSetTypeConditionFeasible schema parentType typeConditions selectionSet
        -> selectionSetSubselectionsNonemptyOnObjectPaths schema parentType selectionSet
        -> selectionSetSubselectionsNonempty schema parentType
            (normalizeSelectionSet schema parentType selectionSet) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema with
  | case1 parentType =>
      intro _typeConditions _hobject _hstack _hready
        _hmerge _hfree _hfeasible _hnonempty
      simpa [normalizeSelectionSet]
        using (selectionSetSubselectionsNonempty_nil (schema := schema)
                (parentType := parentType))
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup hrest =>
      intro typeConditions hobject hstack hready hmerge hfree
        hfeasible hnonempty
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          runtimeMergeSource schema parentType rest :=
        runtimeMergeSource_tail hmerge
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredMerge :
          runtimeMergeSource schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        runtimeMergeSource_without schema responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions

            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest
          (selectionSetTypeConditionFeasible_tail hfeasible)
      have hfilteredNonempty :=
        selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
          schema responseName parentType rest
          (selectionSetSubselectionsNonemptyOnObjectPaths_tail hnonempty)
      simpa [normalizeSelectionSet, hlookup]
        using hrest typeConditions hobject hstack hfilteredReady
          hfilteredMerge hfilteredFree hfilteredFeasible
          hfilteredNonempty
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType hrest hmerged hpossible =>
      intro typeConditions hobject hstack hready hmerge hfree
        hfeasible hnonempty
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hrestFree :
          selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hsubselectionsFree : selectionSetDirectiveFree subselections :=
        hselectionFree.2
      have htailReady :
          selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          runtimeMergeSource schema parentType rest :=
        runtimeMergeSource_tail hmerge
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailReady
      have hfilteredMerge :
          runtimeMergeSource schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        runtimeMergeSource_without schema responseName parentType rest htailMerge
      have hfilteredFree :
          selectionSetDirectiveFree
            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        withoutFieldSelectionsWithResponseName_directiveFree schema responseName rest
          hrestFree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfilteredFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions

            (withoutFieldSelectionsWithResponseName schema responseName rest) :=
        selectionSetTypeConditionFeasible_withoutFieldSelectionsWithResponseName
          schema responseName parentType typeConditions rest htailFeasible
      have hnormalizedRest :
          selectionSetSubselectionsNonempty schema parentType
            (normalizeSelectionSet schema parentType
              (withoutFieldSelectionsWithResponseName schema responseName rest)) :=
        hrest typeConditions hobject hstack hfilteredReady
        hfilteredMerge hfilteredFree hfilteredFeasible
          (selectionSetSubselectionsNonemptyOnObjectPaths_withoutFieldSelectionsWithResponseName
            schema responseName parentType rest
            (selectionSetSubselectionsNonemptyOnObjectPaths_tail hnonempty))
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments []
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments []
            subselections :: rest)
          hready
      have hmatchingFree :
          selectionSetDirectiveFree matching := by
        subst matching
        exact fieldSelectionsWithResponseNameInScope_directiveFree schema parentType
          responseName rest hrestFree
      have hmergedFree :
          selectionSetDirectiveFree mergedSubselections := by
        subst mergedSubselections
        exact selectionSetDirectiveFree_append hsubselectionsFree
          (selectionSetDirectiveFree_mergeSelectionSets hmatchingFree)
      have hheadFeasible :
          selectionTypeConditionFeasible schema parentType typeConditions

            (Selection.field responseName fieldName arguments []
              subselections) := by
        simpa [selectionSetTypeConditionFeasible] using hfeasible.1
      have hmergedFeasible :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetTypeConditionFeasible schema objectType [objectType]
                 mergedSubselections := by
        intro objectType hobjectType
        have hheadChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
               subselections :=
          selectionTypeConditionFeasible_field_child_branch_forObject
            schema hheadFeasible hstack hlookup
            (by simpa [returnType] using hobjectType)
        have hmatchingChildFeasible :
            selectionSetTypeConditionFeasible schema objectType [objectType]
               (mergeSelectionSets matching) := by
          subst matching
          apply
            selectionSetTypeConditionFeasible_mergeSelectionSets_fieldSelectionsWithResponseNameInScope
          intro matchedFieldName matchedArguments matchedDirectives
            matchedSubselections hmatched
          have hsame :
              matchedFieldName = fieldName :=
            runtimeMergeSource_matching_same_field
              schema parentType responseName fieldName arguments subselections
              rest hobject hlookupValid hmerge matchedFieldName
              matchedArguments matchedDirectives matchedSubselections hmatched
          subst matchedFieldName
          exact
            fieldSelectionsWithResponseNameInScope_field_child_branch_forObject
              schema parentType responseName hobject hstack rest
              htailFeasible fieldName matchedArguments matchedDirectives
              matchedSubselections fieldDefinition objectType hmatched hlookup
              (by simpa [returnType] using hobjectType)
        subst mergedSubselections
        exact selectionSetTypeConditionFeasible_append hheadChildFeasible
          hmatchingChildFeasible
      have hheadOnPaths :=
        selectionSetSubselectionsNonemptyOnObjectPaths_head hnonempty
      simp only [selectionSubselectionsNonemptyOnObjectPaths] at hheadOnPaths
      have hheadParts := hheadOnPaths fieldDefinition hlookup
      have hmergedNonempty :
          ∀ objectType,
            objectType ∈ schema.getPossibleTypes returnType ->
              selectionSetSubselectionsNonemptyOnObjectPaths schema objectType
                mergedSubselections := by
        intro objectType hobjectType
        subst mergedSubselections
        exact
          selectionSetSubselectionsNonemptyOnObjectPaths_fieldHead_merged_of_child_object
            schema parentType responseName fieldName objectType arguments
            subselections rest fieldDefinition hobject hlookupValid hnonempty hmerge
            hlookup (List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType))
      have hnormalizedSubselectionsSub :
          selectionSetSubselectionsNonempty schema returnType normalizedSubselections := by
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType]
              using object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup
              (by simpa [returnType] using hinclude)
          have hchildMerge :
              runtimeMergeSource schema returnType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_merged schema hschema hmerge hlookup
              (by simpa [returnType] using hinclude)
          have hreturnPossible :
              returnType ∈ schema.getPossibleTypes returnType := by
            simpa [returnType]
              using (List.contains_iff_mem.mp
                      (object_typeIncludesObjectBool_self schema hreturnObjectType))
          simpa [hreturnObject]
            using hmerged [returnType] hreturnObjectType
              (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hreturnObjectType)
              hchildReady
              hchildMerge hmergedFree
              (hmergedFeasible returnType hreturnPossible)
              (hmergedNonempty returnType hreturnPossible)
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp only [hreturnObjectFalse, Bool.false_eq_true, ↓reduceIte]
          refine selectionSetSubselectionsNonempty_iff.mpr ?_
          intro selection hselectionMem
          unfold possibleTypeNormalizations at hselectionMem
          rw [List.mem_filterMap] at hselectionMem
          rcases hselectionMem with ⟨objectType, hobjectType, hselection⟩
          have hobjectBranch :
              schema.objectType objectType :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
              hschema returnType objectType hobjectType
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType objectType = true :=
            List.contains_iff_mem.mpr (by simpa [returnType] using hobjectType)
          have hchildReady :
              selectionSetSemanticsReady schema objectType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup
              (by simpa [returnType] using hinclude)
          have hchildMerge :
              runtimeMergeSource schema objectType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_merged schema hschema hmerge hlookup
              (by simpa [returnType] using hinclude)
          have hbranchSub :=
            hpossible objectType [objectType] hobjectBranch
              (objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
                schema hobjectBranch)
              hchildReady
              hchildMerge hmergedFree
              (hmergedFeasible objectType hobjectType)
              (hmergedNonempty objectType hobjectType)
          cases hnormalized
                : normalizeSelectionSet schema objectType mergedSubselections with
          | nil =>
              simp [hnormalized] at hselection
          | cons head tail =>
              simp [hnormalized] at hselection
              subst selection
              simp only [selectionSubselectionsNonempty, Option.getD_some]
              exact ⟨by simp, by simpa [hnormalized] using hbranchSub⟩
      have hnormalizedSubselectionsNonempty :
          schema.isCompositeType fieldDefinition.outputType.namedType ->
            normalizedSubselections ≠ [] := by
        intro hcomposite
        have hsubselectionsNonempty :
            subselections ≠ [] :=
          hheadParts.1 hcomposite
        have hsubselectionsInlineNonempty :
            selectionSetInlineFragmentsNonempty subselections :=
          hheadParts.2.1
        rcases
            selectionTypeConditionFeasible_field_child_contains_forPossibleType
              schema hheadFeasible hstack hlookup
              hsubselectionsNonempty hsubselectionsInlineNonempty with
          ⟨childObjectType, hchildObjectType, hheadChildContains⟩
        have hmergedContains :
            selectionSetContainsTypeConditionFeasibleField schema
              [childObjectType]
              mergedSubselections := by
          subst mergedSubselections
          exact
            selectionSetContainsTypeConditionFeasibleField_append_left_forValidity
              schema [childObjectType] hheadChildContains
        subst normalizedSubselections
        by_cases hreturnObject : objectTypeNameBool schema returnType = true
        · have hreturnObjectType :
              schema.objectType returnType :=
            objectType_of_objectTypeNameBool_eq_true schema hreturnObject
          have hchildObjectEq :
              childObjectType = returnType :=
            object_typeIncludesObjectBool_eq_self schema hreturnObjectType
              (List.contains_iff_mem.mpr
                (by simpa [returnType] using hchildObjectType))
          subst childObjectType
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType returnType = true := by
            simpa [returnType]
              using object_typeIncludesObjectBool_self schema hreturnObjectType
          have hchildReady :
              selectionSetSemanticsReady schema returnType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup
              (by simpa [returnType] using hinclude)
          simpa [hreturnObject]
            using normalizeSelectionSet_ne_nil_of_contains schema
              returnType mergedSubselections hreturnObjectType hchildReady
              hmergedContains
        · have hreturnObjectFalse :
              objectTypeNameBool schema returnType = false := by
            cases hmatch : objectTypeNameBool schema returnType
            · rfl
            · contradiction
          simp [hreturnObjectFalse]
          have hbranchObject :
              schema.objectType childObjectType :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
              hschema returnType childObjectType
              (by simpa [returnType] using hchildObjectType)
          have hinclude :
              schema.typeIncludesObjectBool
                fieldDefinition.outputType.namedType childObjectType = true :=
            List.contains_iff_mem.mpr
              hchildObjectType
          have hchildReady :
              selectionSetSemanticsReady schema childObjectType
                mergedSubselections :=
            runtimeMergeSource_fieldHead_semanticsReady schema hmerge hready hlookup
              hinclude
          exact
            possibleTypeNormalizations_ne_nil_of_branch_forValidity schema
              (by simpa [returnType] using hchildObjectType)
              (normalizeSelectionSet_ne_nil_of_contains schema
                childObjectType mergedSubselections hbranchObject hchildReady
                hmergedContains)
      have hheadResult :
          selectionSubselectionsNonempty schema parentType
            (normalizedField schema returnType responseName fieldName arguments []
              normalizedSubselections) := by
        simp only [normalizedField, selectionSubselectionsNonempty, hlookup]
        exact ⟨hnormalizedSubselectionsNonempty,
          by simpa [returnType] using hnormalizedSubselectionsSub⟩
      rw [normalizeSelectionSet.eq_2, hlookup]
      change selectionSetSubselectionsNonempty schema parentType
        (normalizedFieldWithRest schema returnType responseName fieldName
          arguments [] normalizedSubselections
          (normalizeSelectionSet schema parentType
            (withoutFieldSelectionsWithResponseName schema responseName rest)))
      refine selectionSetSubselectionsNonempty_iff.mpr ?_
      intro selection hselection
      simp only [normalizedFieldWithRest, List.mem_cons] at hselection
      rcases hselection with hhead | htail
      · subst selection
        exact hheadResult
      · exact selectionSetSubselectionsNonempty_of_mem hnormalizedRest htail
  | case4 parentType rest directives subselections happend =>
      intro typeConditions hobject hstack hready hmerge hfree
        hfeasible hnonempty
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hhead :
            selectionSemanticsReady schema parentType
              (Selection.inlineFragment none [] subselections) := by
          unfold selectionSetSemanticsReady at hready
          exact hready _ (by simp)
        simpa [selectionSemanticsReady] using hhead
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hbodyTailMerge :
          runtimeMergeSource schema parentType
            (subselections ++ rest) :=
        runtimeMergeSource_inlineFragment_flatten schema parentType none
          subselections rest (by simp) hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             subselections := by
        simpa [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible]
          using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions

            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasible htailFeasible
      have hbodyTailNonempty :
          selectionSetSubselectionsNonemptyOnObjectPaths schema parentType
            (subselections ++ rest) := by
        have hhead :=
          selectionSetSubselectionsNonemptyOnObjectPaths_head hnonempty
        apply selectionSetSubselectionsNonemptyOnObjectPaths_append
        · simpa [selectionSubselectionsNonemptyOnObjectPaths] using hhead
        · exact selectionSetSubselectionsNonemptyOnObjectPaths_tail hnonempty
      simpa [normalizeSelectionSet]
        using happend typeConditions hobject hstack hbodyTailReady
          hbodyTailMerge hbodyTailFree
          hbodyTailFeasible hbodyTailNonempty
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro typeConditions hobject hstack hready hmerge hfree
        hfeasible hnonempty
      have hselectionFree :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := hselectionFree.1
      subst directives
      have hrestFree :=
        selectionSetDirectiveFree_tail hfree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) []
              subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hbodyReady :
          selectionSetSemanticsReady schema parentType subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.2 hoverlap
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have hbodyTailReady :
          selectionSetSemanticsReady schema parentType
            (subselections ++ rest) :=
        selectionSetSemanticsReady_append hbodyReady htailReady
      have hlookupBodyType :
          selectionSetLookupValid schema typeCondition subselections := by
        have hpair :
            selectionSetLookupValid schema typeCondition subselections
              ∧ (schema.typesOverlapBool parentType typeCondition = true ->
                selectionSetSemanticsReady schema parentType subselections) := by
          simpa [selectionSemanticsReady] using hheadReady
        exact hpair.1
      have hlookupBodyParent :
          selectionSetLookupValid schema parentType subselections :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hbodyReady
      have hlookupRest :
          selectionSetLookupValid schema parentType rest :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hbodyTailMerge :
          runtimeMergeSource schema parentType
            (subselections ++ rest) :=
        runtimeMergeSource_inlineFragment_flatten schema parentType (some typeCondition)
          subselections rest (by intro _ h; cases h; exact hoverlap) hmerge
      have hbodyTailFree :
          selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree.2 hrestFree
      have hbodyFeasible :
          selectionSetTypeConditionFeasible schema parentType
            (typeCondition :: typeConditions)  subselections := by
        simpa [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible]
          using hfeasible.1
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hbodyFeasibleInOuterStack :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             subselections :=
        selectionSetTypeConditionFeasible_of_stack_subset schema
          (fun candidate hcandidate =>
            List.mem_cons_of_mem typeCondition hcandidate)
          subselections hbodyFeasible
      have hbodyTailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
            (subselections ++ rest) :=
        selectionSetTypeConditionFeasible_append hbodyFeasibleInOuterStack
          htailFeasible
      have hbodyTailNonempty :
          selectionSetSubselectionsNonemptyOnObjectPaths schema parentType
            (subselections ++ rest) := by
        have hhead :=
          selectionSetSubselectionsNonemptyOnObjectPaths_head hnonempty
        apply selectionSetSubselectionsNonemptyOnObjectPaths_append
        · simpa [selectionSubselectionsNonemptyOnObjectPaths] using hhead hoverlap
        · exact selectionSetSubselectionsNonemptyOnObjectPaths_tail hnonempty
      simpa [normalizeSelectionSet, hoverlap]
        using happend typeConditions hobject hstack
          hbodyTailReady hbodyTailMerge
          hbodyTailFree hbodyTailFeasible hbodyTailNonempty
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro typeConditions hobject hstack hready hmerge hfree
        hfeasible hnonempty
      have htailReady :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          runtimeMergeSource schema parentType rest :=
        runtimeMergeSource_tail hmerge
      have htailFree :=
        selectionSetDirectiveFree_tail hfree
      have htailFeasible :
          selectionSetTypeConditionFeasible schema parentType typeConditions
             rest :=
        selectionSetTypeConditionFeasible_tail hfeasible
      have hfalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · contradiction
      simpa [normalizeSelectionSet, hfalse]
        using hrest typeConditions hobject hstack htailReady
          htailMerge htailFree htailFeasible
          (selectionSetSubselectionsNonemptyOnObjectPaths_tail hnonempty)

private theorem outputTypeSubtype_namedType_isSubType {schema : Schema}
    {implementation expected : TypeRef}
    (hsubtype : schema.outputTypeSubtype implementation expected)
    : schema.isSubType implementation.namedType expected.namedType := by
  induction implementation generalizing expected with
  | named name =>
      cases expected <;> simp_all [Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype,
        TypeRef.namedType]
  | list inner ih =>
      cases expected <;> simp_all [Schema.outputTypeSubtype, TypeRef.namedType]
  | nonNull inner ih =>
      cases expected with
      | named name => exact ih hsubtype
      | list inner => exact ih hsubtype
      | nonNull expectedInner => exact ih (expected := expectedInner) hsubtype

private theorem isCompositeType_of_isSubType {schema : Schema}
    {implementation expected : Name}
    (hsubtype : schema.isSubType implementation expected)
    (hcomposite : schema.isCompositeType implementation)
    : schema.isCompositeType expected := by
  rcases hsubtype with rfl | hsubtype
  · exact hcomposite
  split at hsubtype
  · rename_i _ unionType _ hunion
    exact ⟨.union unionType, hunion, trivial⟩
  · rename_i _ interfaceType _ hinterface
    exact ⟨.interface interfaceType, hinterface, trivial⟩
  · rename_i _ interfaceType _ hinterface
    exact ⟨.interface interfaceType, hinterface, trivial⟩
  · contradiction

/-
Bridge from the source premise to the proof-internal invariant. A selection is checked
for non-emptiness in its declared scope and placed by normalization in a possible object
scope; schema covariance carries composite return types and possible object types from
the object's field implementation back to the declared field.
-/
mutual
  theorem selectionSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      : ∀ declaredType objectType selection,
          schema.objectType objectType
          -> objectType ∈ schema.getPossibleTypes declaredType
          -> Validation.selectionValid schema variableDefinitions declaredType selection
          -> selectionSubselectionsNonempty schema declaredType selection
          -> Validation.selectionValidInPossibleTypes schema variableDefinitions
              objectType selection
          -> selectionSubselectionsNonemptyOnObjectPaths schema objectType selection
    | declaredType, objectType,
      .field responseName fieldName arguments directives selectionSet,
      _hobject, hpossible, hvalid, hnonempty, himplementation => by
        simp only [selectionSubselectionsNonemptyOnObjectPaths]
        intro fieldDefinition hlookup
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨declaredDefinition, hdeclaredLookup, _harguments, hchild⟩
        have hnonemptyParts := hnonempty
        simp only [selectionSubselectionsNonempty, hdeclaredLookup] at hnonemptyParts
        have houtputSubtype :
            schema.outputTypeSubtype fieldDefinition.outputType
              declaredDefinition.outputType :=
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
            hschema hpossible hdeclaredLookup hlookup
        have hsubtype := outputTypeSubtype_namedType_isSubType houtputSubtype
        have hchildImplementation := himplementation
        simp only [Validation.selectionValidInPossibleTypes] at hchildImplementation
        have hchildImplementation := hchildImplementation.2
        rw [hlookup] at hchildImplementation
        have hchildParts := hchild
        simp [Validation.fieldSelectionSetValid] at hchildParts
        rcases hchildParts.2 with hleaf | hcomposite
        · rw [hleaf.2]
          refine ⟨?_, ?_, ?_⟩
          · intro hcompositeImplementation
            exact (isLeafType_not_isCompositeType hleaf.1
              (isCompositeType_of_isSubType hsubtype hcompositeImplementation)).elim
          · unfold selectionSetInlineFragmentsNonempty
            intro selection hselection
            cases hselection
          · intro childObjectType _hchildObjectType
            exact selectionSetSubselectionsNonemptyOnObjectPaths_nil schema childObjectType
        · refine ⟨fun _ => hnonemptyParts.1 hcomposite.1, ?_, ?_⟩
          · exact
              selectionSetInlineFragmentsNonempty_of_selectionSetValid_subselectionsNonempty
                schema variableDefinitions declaredDefinition.outputType.namedType
                selectionSet hcomposite.2 hnonemptyParts.2
          · intro childObjectType hchildObjectType
            have hdeclaredPossible :
                childObjectType
                  ∈ schema.getPossibleTypes declaredDefinition.outputType.namedType :=
              List.contains_iff_mem.mp
                (typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
                  houtputSubtype (List.contains_iff_mem.mpr hchildObjectType))
            exact
              selectionSetSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty
                schema variableDefinitions hschema
                declaredDefinition.outputType.namedType childObjectType selectionSet
                (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
                  fieldDefinition.outputType.namedType childObjectType hchildObjectType)
                hdeclaredPossible hcomposite.2 hnonemptyParts.2
                (hchildImplementation childObjectType hchildObjectType)
    | declaredType, objectType, .inlineFragment none directives selectionSet,
      hobject, hpossible, hvalid, hnonempty, himplementation => by
        simp only [selectionSubselectionsNonemptyOnObjectPaths]
        have hselfPossible : objectType ∈ schema.getPossibleTypes objectType :=
          List.contains_iff_mem.mp (object_typeIncludesObjectBool_self schema hobject)
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        simp only [selectionSubselectionsNonempty, Option.getD_none] at hnonempty
        simp only [Validation.selectionValidInPossibleTypes] at himplementation
        exact
          selectionSetSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty schema
            variableDefinitions hschema declaredType objectType selectionSet hobject
            hpossible hvalid'.2 hnonempty.2 (himplementation objectType hselfPossible)
    | _declaredType, objectType,
      .inlineFragment (some typeCondition) directives selectionSet,
      hobject, _hpossible, hvalid, hnonempty, himplementation => by
        simp only [selectionSubselectionsNonemptyOnObjectPaths]
        intro hoverlap
        have hconditionPossible : objectType ∈ schema.getPossibleTypes typeCondition :=
          List.contains_iff_mem.mp
            (typeIncludesObjectBool_of_object_typesOverlapBool schema hobject hoverlap)
        have hvalid' := hvalid
        simp [Validation.selectionValid] at hvalid'
        simp only [selectionSubselectionsNonempty, Option.getD_some] at hnonempty
        simp only [Validation.selectionValidInPossibleTypes] at himplementation
        exact
          selectionSetSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty schema
            variableDefinitions hschema typeCondition objectType selectionSet hobject
            hconditionPossible hvalid'.2.2.2 hnonempty.2
            (himplementation hoverlap objectType hconditionPossible)

  theorem selectionSetSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      : ∀ declaredType objectType selectionSet,
          schema.objectType objectType
          -> objectType ∈ schema.getPossibleTypes declaredType
          -> Validation.selectionSetValid schema variableDefinitions declaredType
              selectionSet
          -> selectionSetSubselectionsNonempty schema declaredType selectionSet
          -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
              objectType selectionSet
          -> selectionSetSubselectionsNonemptyOnObjectPaths schema objectType selectionSet
    | _declaredType, _objectType, [], _hobject, _hpossible, _hvalid, _hnonempty,
      _himplementation => by
        simp [selectionSetSubselectionsNonemptyOnObjectPaths]
    | declaredType, objectType, selection :: rest, hobject, hpossible, hvalid,
      hnonempty, himplementation => by
        simp only [Validation.selectionSetValidInPossibleTypes] at himplementation
        unfold Validation.selectionSetValid at hvalid
        have hvalidRest :
            Validation.selectionSetValid schema variableDefinitions declaredType rest := by
          unfold Validation.selectionSetValid
          intro other hother
          exact hvalid other (List.mem_cons_of_mem _ hother)
        have hnonemptyRest : selectionSetSubselectionsNonempty schema declaredType rest :=
          selectionSetSubselectionsNonempty_iff.mpr fun other hother =>
            selectionSetSubselectionsNonempty_of_mem hnonempty
              (List.mem_cons_of_mem _ hother)
        simp only [selectionSetSubselectionsNonemptyOnObjectPaths]
        exact ⟨
          selectionSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty schema
            variableDefinitions hschema declaredType objectType selection hobject
            hpossible (hvalid selection List.mem_cons_self)
            (selectionSetSubselectionsNonempty_of_mem hnonempty List.mem_cons_self)
            himplementation.1,
          selectionSetSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty schema
            variableDefinitions hschema declaredType objectType rest hobject hpossible
            hvalidRest hnonemptyRest himplementation.2⟩
end

theorem normalizeOperation_subselectionsNonempty (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationDirectiveFree operation
      -> operationFieldsValidInPossibleTypes schema operation
      -> operationTypeConditionFeasible schema operation
      -> operationSubselectionsNonempty schema operation
      -> operationSubselectionsNonempty schema (normalizeOperation schema operation) := by
  intro hschema hvalid hfree himplementation hfeasible hnonempty
  have hrootEq :
      (operation.rootType schema) = schema.queryType :=
    Validation.operationDefinitionValid_rootType_eq hvalid
  have hrootObject :
      schema.objectType (operation.rootType schema) := by
    simpa [hrootEq] using hschema.2.1
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet (Validation.operationDefinitionValid_selectionSetValid hvalid)
  have hmerge :
      runtimeMergeSource schema (operation.rootType schema)
        operation.selectionSet :=
    runtimeMergeSource_of_valid schema operation.variableDefinitions hrootObject
      (object_typeIncludesObjectBool_self schema hrootObject)
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
      (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
  have hrootStack :
      objectSatisfiesTypeConditionStack schema (operation.rootType schema)
        [(operation.rootType schema)] :=
    objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hrootObject
  have hsourceOnPaths :=
    selectionSetSubselectionsNonemptyOnObjectPaths_of_subselectionsNonempty schema
      operation.variableDefinitions hschema (operation.rootType schema)
      (operation.rootType schema) operation.selectionSet hrootObject
      (List.contains_iff_mem.mp (object_typeIncludesObjectBool_self schema hrootObject))
      (Validation.operationDefinitionValid_selectionSetValid hvalid) hnonempty
      himplementation
  have hnormalized :=
    normalizeSelectionSet_subselectionsNonempty_of_typeConditionFeasible schema
      hschema (operation.rootType schema)
      operation.selectionSet [(operation.rootType schema)] hrootObject hrootStack
      hready hmerge hfree hfeasible hsourceOnPaths
  simpa [operationSubselectionsNonempty, normalizeOperation, Operation.rootType]
    using hnormalized

end GroundTypeNormalization

end NormalForm

end GraphQL
