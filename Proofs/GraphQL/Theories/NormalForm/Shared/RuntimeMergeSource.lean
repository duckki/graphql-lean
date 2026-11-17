import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMerge
import Proofs.GraphQL.Theories.NormalForm.Shared.DeclaredLookup
import Proofs.GraphQL.Theories.NormalForm.Shared.OutputShapes

/-!
Declared-scope evidence for merge compatibility along runtime object paths.
-/

namespace GraphQL.NormalForm

def scopedFieldMatches (source : FieldMerge.ScopedField)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet : List Selection)
    : Prop :=
  source.responseName = responseName
  ∧ source.fieldName = fieldName
  ∧ source.arguments = arguments
  ∧ source.selectionSet = selectionSet

-- Static source fields keep their declared return scopes. Coverage refers only to
-- fields applicable to the current runtime object, without asserting that raw
-- children remain statically mergeable after a covariant lookup changes scope.
def runtimeMergeSources (schema : Schema) (runtimeType : Name)
    (selectionSet : List Selection) (sources : List FieldMerge.ScopedField)
    : Prop :=
  (∀ source,
    source ∈ sources
    -> ∃ definition,
        schema.lookupField source.parentType source.fieldName = some definition
        ∧ definition.outputType = source.outputType
        ∧ selectionSetDeclaredLookupReady schema source.outputType.namedType
            source.selectionSet)
  ∧ (∀ left,
      left ∈ sources
      -> ∀ right,
          right ∈ sources
          -> left.responseName = right.responseName
          -> FieldMerge.fieldsForNameCanMerge schema left right)
  ∧ (∀ responseName fieldName arguments directives children,
      Selection.field responseName fieldName arguments directives children
        ∈ fieldSelectionsWithResponseNameInScope schema runtimeType responseName
            selectionSet
      -> ∃ source,
          source ∈ sources
          ∧ schema.typeIncludesObjectBool source.parentType runtimeType = true
          ∧ scopedFieldMatches source responseName fieldName arguments children)

def runtimeMergeSource (schema : Schema) (runtimeType : Name)
    (selectionSet : List Selection)
    : Prop :=
  ∃ sources, runtimeMergeSources schema runtimeType selectionSet sources

def runtimeMergeParentSources (schema : Schema) (runtimeType responseName : Name)
    (sources : List FieldMerge.ScopedField)
    : List FieldMerge.ScopedField :=
  sources.filter
    (fun source =>
      (source.responseName == responseName)
      && schema.typeIncludesObjectBool source.parentType runtimeType)

theorem runtimeMergeSources_of_declaredLookupReady (schema : Schema)
    {parentType runtimeType : Name} {selectionSet : List Selection}
    (hobject : schema.objectType runtimeType)
    (hpossible : schema.typeIncludesObjectBool parentType runtimeType = true)
    (hvalid : selectionSetDeclaredLookupReady schema parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    : runtimeMergeSources schema runtimeType selectionSet
        (FieldMerge.collectFields schema parentType selectionSet) := by
  refine ⟨?_, ?_, ?_⟩
  · intro source hsource
    exact collectFields_declaredLookupReady schema
      parentType selectionSet source hvalid hsource
  · intro left hleft right hright hresponse
    exact FieldMerge.fieldsInSetCanMerge_pair hmerge hleft hright hresponse
  · intro responseName fieldName arguments directives children hfield
    exact runtimeFields_declaredSource schema runtimeType hobject parentType selectionSet
      responseName fieldName arguments directives children hpossible hvalid hfield

theorem runtimeMergeSource_of_declaredLookupReady (schema : Schema)
    {parentType runtimeType : Name} {selectionSet : List Selection}
    (hobject : schema.objectType runtimeType)
    (hpossible : schema.typeIncludesObjectBool parentType runtimeType = true)
    (hvalid : selectionSetDeclaredLookupReady schema parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    : runtimeMergeSource schema runtimeType selectionSet := by
  exact ⟨_, runtimeMergeSources_of_declaredLookupReady schema hobject hpossible hvalid hmerge⟩

theorem runtimeMergeSource_of_valid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    {parentType runtimeType : Name} {selectionSet : List Selection}
    (hobject : schema.objectType runtimeType)
    (hpossible : schema.typeIncludesObjectBool parentType runtimeType = true)
    (hvalid
      : Validation.selectionSetValid schema variableDefinitions parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    : runtimeMergeSource schema runtimeType selectionSet := by
  exact runtimeMergeSource_of_declaredLookupReady schema hobject hpossible
    (selectionSetDeclaredLookupReady_of_valid schema variableDefinitions parentType selectionSet hvalid)
    hmerge

theorem runtimeSource_mergeIdentityCondition (schema : Schema)
    {runtimeType : Name} {left right : FieldMerge.ScopedField}
    (hleft : schema.typeIncludesObjectBool left.parentType runtimeType = true)
    (hright : schema.typeIncludesObjectBool right.parentType runtimeType = true)
    : left.parentType = right.parentType
      ∨ ¬ schema.objectType left.parentType
      ∨ ¬ schema.objectType right.parentType := by
  by_cases hleftObject : schema.objectType left.parentType
  · by_cases hrightObject : schema.objectType right.parentType
    · exact Or.inl
        ((object_typeIncludesObjectBool_eq_self schema hleftObject hleft).symm.trans
          (object_typeIncludesObjectBool_eq_self schema hrightObject hright))
    · exact Or.inr (Or.inr hrightObject)
  · exact Or.inr (Or.inl hleftObject)

theorem runtimeMergeSource_identity {schema : Schema} {runtimeType responseName : Name}
    {selectionSet : List Selection} {leftName rightName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildren rightChildren : List Selection}
    (hsource : runtimeMergeSource schema runtimeType selectionSet)
    (hleft
      : Selection.field responseName leftName leftArguments leftDirectives leftChildren
        ∈ fieldSelectionsWithResponseNameInScope schema runtimeType responseName
            selectionSet)
    (hright
      : Selection.field responseName rightName rightArguments rightDirectives
          rightChildren
        ∈ fieldSelectionsWithResponseNameInScope schema runtimeType responseName
            selectionSet)
    : leftName = rightName
      ∧ Argument.argumentsEquivalent leftArguments rightArguments := by
  rcases hsource with ⟨sources, hvalid, hmerge, hcover⟩
  rcases hcover _ _ _ _ _ hleft with ⟨left, hleft, hleftApplies, hlmatch⟩
  rcases hcover _ _ _ _ _ hright with ⟨right, hright, hrightApplies, hrmatch⟩
  have hpair := hmerge left hleft right hright (hlmatch.1.trans hrmatch.1.symm)
  have hidentity := FieldMerge.fieldsForNameCanMerge_identity hpair
    (runtimeSource_mergeIdentityCondition schema hleftApplies hrightApplies)
  simpa [hlmatch.2.1, hrmatch.2.1, hlmatch.2.2.1, hrmatch.2.2.1] using hidentity

theorem runtimeMergeSources_of_fields_subset {schema : Schema} {runtimeType : Name}
    {source target : List Selection} {sources : List FieldMerge.ScopedField}
    (hsource : runtimeMergeSources schema runtimeType source sources)
    (hsubset
      : ∀ responseName,
          fieldSelectionsWithResponseNameInScope schema runtimeType responseName target
          ⊆ fieldSelectionsWithResponseNameInScope schema runtimeType responseName source)
    : runtimeMergeSources schema runtimeType target sources := by
  rcases hsource with ⟨hvalid, hmerge, hcover⟩
  exact ⟨hvalid, hmerge,
    fun responseName fieldName arguments directives children hfield =>
      hcover responseName fieldName arguments directives children (hsubset responseName hfield)⟩

theorem runtimeMergeSource_of_fields_subset {schema : Schema} {runtimeType : Name}
    {source target : List Selection}
    (hsource : runtimeMergeSource schema runtimeType source)
    (hsubset
      : ∀ responseName,
          fieldSelectionsWithResponseNameInScope schema runtimeType responseName target
          ⊆ fieldSelectionsWithResponseNameInScope schema runtimeType responseName source)
    : runtimeMergeSource schema runtimeType target := by
  rcases hsource with ⟨sources, hsource⟩
  exact ⟨sources, runtimeMergeSources_of_fields_subset hsource hsubset⟩

private theorem runtimeFields_append (schema : Schema) (parentType responseName : Name)
    (left right : List Selection)
    : fieldSelectionsWithResponseNameInScope schema parentType responseName
        (left ++ right)
      = fieldSelectionsWithResponseNameInScope schema parentType responseName left
        ++ fieldSelectionsWithResponseNameInScope schema parentType responseName
            right := by
  induction left with
  | nil => simp [fieldSelectionsWithResponseNameInScope]
  | cons selection rest ih =>
      cases selection with
      | field name fieldName arguments directives children =>
          simp only [List.cons_append, fieldSelectionsWithResponseNameInScope, ih]
          split <;> simp
      | inlineFragment condition directives children =>
          cases condition with
          | none => simp [fieldSelectionsWithResponseNameInScope, ih, List.append_assoc]
          | some condition =>
              simp only [List.cons_append, fieldSelectionsWithResponseNameInScope, ih]
              split <;> simp [List.append_assoc]

private theorem runtimeFields_without_mem (schema : Schema)
    (parentType responseName removed : Name)
    : ∀ selectionSet field,
        field
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              (withoutFieldSelectionsWithResponseName schema removed selectionSet)
        -> field
            ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet
  | [], field, hfield => by
      simp [withoutFieldSelectionsWithResponseName, fieldSelectionsWithResponseNameInScope] at hfield
  | selection :: rest, field, hfield => by
      cases selection with
      | field name fieldName arguments directives children =>
          by_cases hremoved : (name == removed) = true
          · simp only [withoutFieldSelectionsWithResponseName, hremoved, ↓reduceIte] at hfield
            have htail := runtimeFields_without_mem schema parentType responseName removed
              rest field hfield
            simp only [fieldSelectionsWithResponseNameInScope]
            split
            · exact List.mem_cons_of_mem _ htail
            · exact htail
          · have hremoved' : (name == removed) = false := by
              cases h : name == removed <;> simp_all
            simp only [withoutFieldSelectionsWithResponseName, hremoved', Bool.false_eq_true,
              ↓reduceIte, fieldSelectionsWithResponseNameInScope] at hfield ⊢
            split at hfield
            · rename_i hname
              simp only [hname, ↓reduceIte]
              rcases List.mem_cons.mp hfield with rfl | htail
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _
                  (runtimeFields_without_mem schema parentType responseName removed rest field htail)
            · rename_i hname
              simp only [hname]
              exact runtimeFields_without_mem schema parentType responseName removed rest field hfield
      | inlineFragment condition directives children =>
          cases condition with
          | none =>
              simp only [withoutFieldSelectionsWithResponseName,
                fieldSelectionsWithResponseNameInScope, List.mem_append] at hfield ⊢
              exact hfield.imp
                (runtimeFields_without_mem schema parentType responseName removed children field)
                (runtimeFields_without_mem schema parentType responseName removed rest field)
          | some condition =>
              simp only [withoutFieldSelectionsWithResponseName,
                fieldSelectionsWithResponseNameInScope] at hfield ⊢
              split at hfield
              · rename_i hoverlap
                simp only [hoverlap, ↓reduceIte]
                exact (List.mem_append.mp hfield).elim
                  (fun h => List.mem_append_left _
                    (runtimeFields_without_mem schema parentType responseName removed children field h))
                  (fun h => List.mem_append_right _
                    (runtimeFields_without_mem schema parentType responseName removed rest field h))
              · rename_i hoverlap
                simp only [hoverlap]
                exact runtimeFields_without_mem schema parentType responseName removed rest field hfield

theorem runtimeMergeSources_tail {schema : Schema} {parentType : Name}
    {selection : Selection} {rest : List Selection}
    {sources : List FieldMerge.ScopedField}
    (hsource : runtimeMergeSources schema parentType (selection :: rest) sources)
    : runtimeMergeSources schema parentType rest sources := by
  apply runtimeMergeSources_of_fields_subset hsource
  intro responseName field hfield
  cases selection with
  | field name fieldName arguments directives children =>
      simp only [fieldSelectionsWithResponseNameInScope]
      split
      · exact List.mem_cons_of_mem _ hfield
      · exact hfield
  | inlineFragment condition directives children =>
      cases condition with
      | none =>
          simpa [fieldSelectionsWithResponseNameInScope] using List.mem_append_right
            (fieldSelectionsWithResponseNameInScope schema parentType responseName children) hfield
      | some condition =>
          simp only [fieldSelectionsWithResponseNameInScope]
          split
          · exact List.mem_append_right _ hfield
          · exact hfield

theorem runtimeMergeSource_tail {schema : Schema} {parentType : Name}
    {selection : Selection} {rest : List Selection}
    (hsource : runtimeMergeSource schema parentType (selection :: rest))
    : runtimeMergeSource schema parentType rest := by
  rcases hsource with ⟨sources, hsource⟩
  exact ⟨sources, runtimeMergeSources_tail hsource⟩

theorem runtimeMergeSources_without (schema : Schema) (responseName parentType : Name)
    (selectionSet : List Selection) {sources : List FieldMerge.ScopedField}
    (hsource : runtimeMergeSources schema parentType selectionSet sources)
    : runtimeMergeSources schema parentType
        (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        sources := by
  apply runtimeMergeSources_of_fields_subset hsource
  exact fun name => runtimeFields_without_mem schema parentType name responseName selectionSet

theorem runtimeMergeSource_without (schema : Schema) (responseName parentType : Name)
    (selectionSet : List Selection)
    (hsource : runtimeMergeSource schema parentType selectionSet)
    : runtimeMergeSource schema parentType
        (withoutFieldSelectionsWithResponseName schema responseName selectionSet) := by
  apply runtimeMergeSource_of_fields_subset hsource
  exact fun name => runtimeFields_without_mem schema parentType name responseName selectionSet

theorem runtimeMergeSources_inlineFragment_flatten (schema : Schema)
    (parentType : Name) (condition : Option Name) (children rest : List Selection)
    {directives : List DirectiveApplication}
    {sources : List FieldMerge.ScopedField}
    (happlies
      : ∀ typeCondition,
          condition = some typeCondition
          -> schema.typesOverlapBool parentType typeCondition = true)
    (hsource
      : runtimeMergeSources schema parentType
          (Selection.inlineFragment condition directives children :: rest) sources)
    : runtimeMergeSources schema parentType (children ++ rest) sources := by
  apply runtimeMergeSources_of_fields_subset hsource
  intro responseName field hfield
  rw [runtimeFields_append] at hfield
  cases condition with
  | none => simpa [fieldSelectionsWithResponseNameInScope] using hfield
  | some condition =>
      simpa [fieldSelectionsWithResponseNameInScope, happlies condition rfl] using hfield

theorem runtimeMergeSource_inlineFragment_flatten (schema : Schema)
    (parentType : Name) (condition : Option Name) (children rest : List Selection)
    {directives : List DirectiveApplication}
    (happlies
      : ∀ typeCondition,
          condition = some typeCondition
          -> schema.typesOverlapBool parentType typeCondition = true)
    (hsource
      : runtimeMergeSource schema parentType
          (Selection.inlineFragment condition directives children :: rest))
    : runtimeMergeSource schema parentType (children ++ rest) := by
  rcases hsource with ⟨sources, hsource⟩
  exact ⟨sources, runtimeMergeSources_inlineFragment_flatten schema parentType condition
    children rest happlies hsource⟩

private theorem runtimeFields_mergeSelectionSets_mem (schema : Schema)
    (parentType responseName : Name) (group : List Selection) (field : Selection)
    (hfield
      : field
        ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
            (mergeSelectionSets group))
    : ∃ selection,
        selection ∈ group
        ∧ field
          ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName
              selection.subselections := by
  induction group with
  | nil => simp [mergeSelectionSets, fieldSelectionsWithResponseNameInScope] at hfield
  | cons selection rest ih =>
      rw [mergeSelectionSets, runtimeFields_append] at hfield
      rcases List.mem_append.mp hfield with hhead | htail
      · exact ⟨selection, by simp, hhead⟩
      · rcases ih htail with ⟨selection, hselection, hfield⟩
        exact ⟨selection, by simp [hselection], hfield⟩

theorem runtimeMergeSources_fieldHead_merged (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {parentType responseName fieldName runtimeType : Name}
    {arguments : List Argument} {children rest : List Selection}
    {definition : FieldDefinition} {sources : List FieldMerge.ScopedField}
    (hsource
      : runtimeMergeSources schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest) sources)
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hinclude
      : schema.typeIncludesObjectBool definition.outputType.namedType runtimeType = true)
    : runtimeMergeSources schema runtimeType
        (children
          ++ mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest))
        ((runtimeMergeParentSources schema parentType responseName sources).flatMap
          (fun source =>
            FieldMerge.collectFields schema source.outputType.namedType
              source.selectionSet)) := by
  rcases hsource with ⟨hvalid, hmerge, hcover⟩
  have hhead : Selection.field responseName fieldName arguments [] children ∈
      fieldSelectionsWithResponseNameInScope schema parentType responseName
        (Selection.field responseName fieldName arguments [] children :: rest) := by
    simp [fieldSelectionsWithResponseNameInScope]
  rcases hcover _ _ _ _ _ hhead with
    ⟨headSource, hheadSource, hheadApplies, hheadMatch⟩
  let parents := runtimeMergeParentSources schema parentType responseName sources
  have hparentsMem (source : FieldMerge.ScopedField) : source ∈ parents ↔
      source ∈ sources ∧ source.responseName = responseName
        ∧ schema.typeIncludesObjectBool source.parentType parentType = true := by
    simp [parents, runtimeMergeParentSources, Bool.and_eq_true]
  have hreturn (source : FieldMerge.ScopedField) (hsource : source ∈ parents)
      : schema.typeIncludesObjectBool source.outputType.namedType runtimeType = true := by
    rcases (hparentsMem source).mp hsource with ⟨hsource, hresponse, happlies⟩
    have hpair := hmerge source hsource headSource hheadSource
      (hresponse.trans hheadMatch.1.symm)
    have hname := (FieldMerge.fieldsForNameCanMerge_identity hpair
      (runtimeSource_mergeIdentityCondition schema happlies hheadApplies)).1
    have hname' : source.fieldName = fieldName := hname.trans hheadMatch.2.1
    rcases hvalid source hsource with ⟨expected, hexpected, houtput, _⟩
    have hsubtype :=
      SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
        hschema (List.contains_iff_mem.mp happlies) hexpected
        (by simpa [hname'] using hlookup)
    simpa [houtput]
      using typeIncludesObjectBool_of_outputTypeSubtype_namedType schema hsubtype hinclude
  let childSources := parents.flatMap (fun source =>
    FieldMerge.collectFields schema source.outputType.namedType source.selectionSet)
  have hchildValid (source : FieldMerge.ScopedField) (hsource : source ∈ parents)
      : selectionSetDeclaredLookupReady schema source.outputType.namedType
          source.selectionSet := by
    rcases hvalid source ((hparentsMem source).mp hsource).1 with
      ⟨expected, hexpected, houtput, hchildren⟩
    exact hchildren
  refine ⟨?_, ?_, ?_⟩
  · intro child hchild
    rcases List.mem_flatMap.mp hchild with ⟨source, hsource, hchild⟩
    exact collectFields_declaredLookupReady schema
      source.outputType.namedType source.selectionSet child (hchildValid source hsource) hchild
  · intro left hleft right hright hresponse
    rcases List.mem_flatMap.mp hleft with ⟨leftParent, hleftParent, hleft⟩
    rcases List.mem_flatMap.mp hright with ⟨rightParent, hrightParent, hright⟩
    rcases (hparentsMem leftParent).mp hleftParent with ⟨hlmem, hlresponse, hlapplies⟩
    rcases (hparentsMem rightParent).mp hrightParent with ⟨hrmem, hrresponse, hrapplies⟩
    have hpair := hmerge leftParent hlmem rightParent hrmem (hlresponse.trans hrresponse.symm)
    exact FieldMerge.fieldsForNameCanMerge_collected_subfields hpair
      (runtimeSource_mergeIdentityCondition schema hlapplies hrapplies)
      left (List.mem_append_left _ hleft) right (List.mem_append_right _ hright) hresponse
  · intro childResponse childName childArguments childDirectives childChildren hchild
    let group := Selection.field responseName fieldName arguments [] children ::
      fieldSelectionsWithResponseNameInScope schema parentType responseName rest
    have hgroup : mergeSelectionSets group = children ++ mergeSelectionSets
        (fieldSelectionsWithResponseNameInScope schema parentType responseName rest) := rfl
    rw [← hgroup] at hchild
    rcases runtimeFields_mergeSelectionSets_mem schema runtimeType childResponse group
      (.field childResponse childName childArguments childDirectives childChildren) hchild with
      ⟨selection, hselection, hchild⟩
    have hselected : selection ∈ fieldSelectionsWithResponseNameInScope schema parentType
        responseName (Selection.field responseName fieldName arguments [] children :: rest) := by
      simpa [group, fieldSelectionsWithResponseNameInScope] using hselection
    rcases fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      _ selection hselected with ⟨name, args, dirs, body, rfl⟩
    rcases hcover _ _ _ _ _ hselected with
      ⟨source, hsource, happlies, hmatch⟩
    have hparent : source ∈ parents :=
      (hparentsMem source).mpr ⟨hsource, hmatch.1, happlies⟩
    have hchildObject : schema.objectType runtimeType :=
      SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
        definition.outputType.namedType runtimeType (List.contains_iff_mem.mp hinclude)
    have hchild' : Selection.field childResponse childName childArguments childDirectives
        childChildren ∈ fieldSelectionsWithResponseNameInScope schema runtimeType childResponse
          source.selectionSet := by
      simpa [Selection.subselections, hmatch.2.2.2] using hchild
    rcases runtimeFields_declaredSource schema runtimeType hchildObject
        source.outputType.namedType source.selectionSet childResponse childName childArguments
        childDirectives childChildren (hreturn source hparent) (hchildValid source hparent) hchild' with
      ⟨childSource, hchildSource, hchildApplies, hresponse, hname, harguments, hchildren⟩
    exact ⟨childSource, List.mem_flatMap.mpr ⟨source, hparent, hchildSource⟩,
      hchildApplies, hresponse, hname, harguments, hchildren⟩

theorem runtimeMergeSource_fieldHead_merged (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {parentType responseName fieldName runtimeType : Name}
    {arguments : List Argument} {children rest : List Selection}
    {definition : FieldDefinition}
    (hsource
      : runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest))
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hinclude
      : schema.typeIncludesObjectBool definition.outputType.namedType runtimeType = true)
    : runtimeMergeSource schema runtimeType
        (children
          ++ mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest)) := by
  rcases hsource with ⟨sources, hsource⟩
  exact ⟨_, runtimeMergeSources_fieldHead_merged schema hschema hsource hlookup hinclude⟩

theorem runtimeMergeSources_fieldHead_parents (schema : Schema)
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {children rest : List Selection}
    {definition : FieldDefinition} {sources : List FieldMerge.ScopedField}
    (hsource
      : runtimeMergeSources schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest) sources)
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hshapes : fieldSameOutputShape schema fieldName)
    : runtimeMergeParentSources schema parentType responseName sources ≠ []
      ∧ ∀ source,
          source ∈ runtimeMergeParentSources schema parentType responseName sources
          -> FieldMerge.sameTypeShape schema source.outputType definition.outputType
              ∧ source.responseName = responseName
              ∧ source.fieldName = fieldName
              ∧ Argument.argumentsEquivalent source.arguments arguments
              ∧ (source.parentType = parentType
                  ∨ ¬ schema.objectType source.parentType) := by
  rcases hsource with ⟨hvalid, hmerge, hcover⟩
  have hhead : Selection.field responseName fieldName arguments [] children ∈
      fieldSelectionsWithResponseNameInScope schema parentType responseName
        (Selection.field responseName fieldName arguments [] children :: rest) := by
    simp [fieldSelectionsWithResponseNameInScope]
  rcases hcover _ _ _ _ _ hhead with ⟨headSource, hheadSource, hheadApplies, hheadMatch⟩
  have hparentsMem (source : FieldMerge.ScopedField) :
      source ∈ runtimeMergeParentSources schema parentType responseName sources ↔
        source ∈ sources ∧ source.responseName = responseName
          ∧ schema.typeIncludesObjectBool source.parentType parentType = true := by
    simp [runtimeMergeParentSources, Bool.and_eq_true]
  constructor
  · have hmem := (hparentsMem headSource).mpr ⟨hheadSource, hheadMatch.1, hheadApplies⟩
    intro hempty
    simp [hempty] at hmem
  · intro source hsource
    rcases (hparentsMem source).mp hsource with ⟨hsource, hresponse, happlies⟩
    have hpair := hmerge source hsource headSource hheadSource
      (hresponse.trans hheadMatch.1.symm)
    have hidentity := FieldMerge.fieldsForNameCanMerge_identity hpair
      (runtimeSource_mergeIdentityCondition schema happlies hheadApplies)
    have hname : source.fieldName = fieldName := hidentity.1.trans hheadMatch.2.1
    have harguments : Argument.argumentsEquivalent source.arguments arguments := by
      simpa [hheadMatch.2.2.1] using hidentity.2
    rcases hvalid source hsource with ⟨expected, hexpected, houtput, _⟩
    have hshape := hshapes _ _ _ _ (List.contains_iff_mem.mp happlies)
      (by simpa [hname] using hexpected) hlookup
    refine ⟨?_, hresponse, hname, harguments, ?_⟩
    · simpa [houtput] using FieldMerge.sameTypeShape_symm schema _ _ hshape
    · by_cases hobject : schema.objectType source.parentType
      · exact Or.inl (object_typeIncludesObjectBool_eq_self schema hobject happlies).symm
      · exact Or.inr hobject

theorem runtimeMergeSource_matching_same_field
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (children rest : List Selection)
    (_hobject : schema.objectType parentType)
    (_hlookup
      : selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest))
    (hsource
      : runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest))
    (matchedName : Name) (matchedArguments : List Argument)
    (matchedDirectives : List DirectiveApplication) (matchedChildren : List Selection)
    (hmatched
      : Selection.field responseName matchedName matchedArguments matchedDirectives
          matchedChildren
        ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest)
    : matchedName = fieldName := by
  have hhead : Selection.field responseName fieldName arguments [] children ∈
      fieldSelectionsWithResponseNameInScope schema parentType responseName
        (Selection.field responseName fieldName arguments [] children :: rest) := by
    simp [fieldSelectionsWithResponseNameInScope]
  exact (runtimeMergeSource_identity hsource
          (by simpa [fieldSelectionsWithResponseNameInScope] using Or.inr hmatched)
          hhead).1

theorem runtimeMergeSource_matching_field_shape
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (children rest : List Selection)
    (hobject : schema.objectType parentType)
    (hlookup
      : selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest))
    (hsource
      : runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest))
    (selection : Selection)
    (hselection
      : selection
        ∈ fieldSelectionsWithResponseNameInScope schema parentType responseName rest)
    : ∃ args dirs body,
        selection = Selection.field responseName fieldName args dirs body := by
  rcases fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName rest
    selection hselection with ⟨name, args, dirs, body, rfl⟩
  have hname := runtimeMergeSource_matching_same_field schema parentType responseName
    fieldName arguments children rest hobject hlookup hsource name args dirs body hselection
  exact ⟨args, dirs, body, by rw [hname]⟩

end GraphQL.NormalForm
