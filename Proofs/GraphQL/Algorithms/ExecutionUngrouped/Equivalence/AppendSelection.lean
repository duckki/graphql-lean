import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.DepthZero
import Proofs.GraphQL.Execution.ResolverValue

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

inductive ValueContainsObject {ObjectIdentity : Type}
    : ResolverValue ObjectIdentity -> Name -> ObjectIdentity -> Prop where
  | here {runtimeType : Name} {identity : ObjectIdentity}
    : ValueContainsObject (.object runtimeType identity) runtimeType identity
  | list {values : List (ResolverValue ObjectIdentity)}
    {value : ResolverValue ObjectIdentity} {runtimeType : Name}
    {identity : ObjectIdentity}
    : value ∈ values -> ValueContainsObject value runtimeType identity
      -> ValueContainsObject (.list values) runtimeType identity

theorem completeResolvedValue_none_eq_completeValue
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    : ∀ (fieldType : TypeRef) (selectionSet : List Selection)
        (value : ResolverValue ObjectIdentity),
        completeResolvedValue schema resolvers variableValues depth fieldType
          selectionSet value none
        = completeValue schema resolvers variableValues depth fieldType
            selectionSet value none := by
  intro fieldType
  induction fieldType with
  | named typeName =>
      intro selectionSet value
      simp [completeResolvedValue, reusablePreviousValue?_none]
  | list inner ih =>
      intro selectionSet value
      simp [completeResolvedValue, reusablePreviousValue?_none]
  | nonNull inner ih =>
      intro selectionSet value
      cases depth with
      | zero =>
          simp [completeResolvedValue, reusablePreviousValue?_none]
          rw [ih selectionSet value]
          cases value <;>
            simp [completeValue, outOfFuel, nonNullCompletion]
      | succ depth' =>
          simp [completeResolvedValue, completeValue,
            reusablePreviousValue?_none, ih selectionSet value]

theorem resultCombine_append_assoc {α : Type} (left middle right : Result (List α))
    : Result.combine List.append (Result.combine List.append left middle) right
      = Result.combine List.append left (Result.combine List.append middle right) := by
  cases left with
  | error leftErrors =>
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨middleFields, middleErrors⟩
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
  | ok leftResult =>
      rcases leftResult with ⟨leftFields, leftErrors⟩
      cases middle with
      | error middleErrors =>
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
      | ok middleResult =>
          rcases middleResult with ⟨middleFields, middleErrors⟩
          cases right with
          | error rightErrors =>
              simp [GraphQL.Execution.Result.combine,
                Nat.add_assoc]
          | ok rightResult =>
              rcases rightResult with ⟨rightFields, rightErrors⟩
              simp [GraphQL.Execution.Result.combine,
                List.append_assoc, Nat.add_assoc]

theorem specExecuteCollectedFields_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    : ∀ left right : List (Name × List ExecutableField),
        GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          depth source (left ++ right)
        = Result.combine List.append
            (GraphQL.Execution.executeCollectedFields schema resolvers
              variableValues depth source left)
            (GraphQL.Execution.executeCollectedFields schema resolvers
              variableValues depth source right)
  | [], right => by
      cases hright :
          GraphQL.Execution.executeCollectedFields schema resolvers
            variableValues depth source right with
      | error rightErrors =>
          simp [GraphQL.Execution.executeCollectedFields, Result.combine,
            GraphQL.Execution.Result.combine, hright]
      | ok rightResult =>
          rcases rightResult with ⟨rightFields, rightErrors⟩
          simp [GraphQL.Execution.executeCollectedFields, Result.combine,
            GraphQL.Execution.Result.combine, hright]
  | (responseName, fields) :: rest, right => by
      simp [GraphQL.Execution.executeCollectedFields,
        specExecuteCollectedFields_append schema resolvers variableValues depth
          source rest right]
      rw [resultCombine_append_assoc]

theorem specExecuteRootSelectionSet_append_of_namesDisjoint
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left right : List Selection)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType source right))
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ right)
      = Result.combine List.append
          (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source left)
          (GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source right) := by
  simp [GraphQL.Execution.executeRootSelectionSet]
  rw [GraphQL.NormalForm.collectFields_append]
  rw [GraphQL.NormalForm.mergeExecutableGroups_eq_append_of_namesDisjoint]
  · exact specExecuteCollectedFields_append schema resolvers variableValues
      depth source
      (GraphQL.Execution.collectFields schema variableValues parentType source
        left)
      (GraphQL.Execution.collectFields schema variableValues parentType source
        right)
  · exact hdisjoint
  · exact GraphQL.NormalForm.collectFields_namesNodup schema variableValues
      parentType source right

theorem resultValueOrNull_eq_result_getD (completed : Result ResponseValue)
    : resultValueOrNull completed = GraphQL.Execution.Result.getD .null completed := by
  cases completed with
  | error errors =>
      rfl
  | ok result =>
      rcases result with ⟨value, errors⟩
      rfl

theorem executeField_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    : ∀ {responseName groupName fields},
        responseName
          ∈ (GraphQL.Execution.executeFieldData schema resolvers variableValues
              depth source groupName fields).map
              Prod.fst
        -> responseName = groupName
  | _responseName, _groupName, [], hmem => by
      simp [GraphQL.Execution.executeFieldData, GraphQL.Execution.executeField,
        GraphQL.Execution.Result.getD] at hmem
  | _responseName, _groupName, field :: fields, hmem => by
      cases depth with
      | zero =>
          simp [GraphQL.Execution.executeFieldData,
            GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
            outOfFuel] at hmem
      | succ depth' =>
          cases hlookup :
              schema.lookupField field.parentType field.fieldName with
          | none =>
              simp [GraphQL.Execution.executeFieldData,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
                hlookup] at hmem
          | some fieldDefinition =>
              cases hresolve :
                  resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
              | none =>
                  cases hcompleted :
                      GraphQL.Execution.handleFieldError
                        fieldDefinition.outputType with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] at hmem
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] using hmem
              | some resolved =>
                  cases hcompleted :
                      GraphQL.Execution.completeValue schema resolvers
                        variableValues depth' fieldDefinition.outputType
                        (field :: fields) resolved with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] at hmem
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted] using hmem

theorem executeCollectedFields_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    : ∀ {responseName groups},
        responseName
          ∈ (GraphQL.Execution.executeCollectedFieldsData schema resolvers
              variableValues depth source groups).map
              Prod.fst
        -> responseName ∈ groups.map Prod.fst
  | _responseName, [], hmem => by
      simp [GraphQL.Execution.executeCollectedFieldsData,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.Result.getD]
        at hmem
  | responseName, (groupName, fields) :: rest, hmem => by
      cases hhead :
          GraphQL.Execution.executeField schema resolvers variableValues depth
            source groupName fields with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
      | ok headResult =>
          rcases headResult with ⟨headFields, headErrors⟩
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] at hmem
              rcases hmem with hheadMem | htailMem
              · have hkey :
                    responseName = groupName :=
                  executeField_key_mem schema resolvers variableValues depth
                    source (responseName := responseName)
                    (groupName := groupName) (fields := fields) <| by
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.Result.getD, hhead] using hheadMem
                subst responseName
                simp
              · right
                apply executeCollectedFields_key_mem schema resolvers
                  variableValues depth source
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.Result.getD, htail] using htailMem

theorem executeField_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    (groupName : Name) (fields : List ExecutableField)
    : PairKeysNodup
        (GraphQL.Execution.executeFieldData schema resolvers variableValues
          depth source groupName fields) := by
  unfold PairKeysNodup
  cases fields with
  | nil =>
      simp [GraphQL.Execution.executeFieldData, GraphQL.Execution.executeField,
        GraphQL.Execution.Result.getD]
  | cons field rest =>
      cases depth with
      | zero =>
          simp [GraphQL.Execution.executeFieldData,
            GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
            outOfFuel]
      | succ depth' =>
          cases hlookup : schema.lookupField field.parentType field.fieldName with
          | none =>
              simp [GraphQL.Execution.executeFieldData,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
                hlookup]
          | some fieldDefinition =>
              cases hresolve
                    : resolvers.resolve field.parentType field.fieldName
                        field.arguments source with
              | none =>
                  cases hcompleted
                        : GraphQL.Execution.handleFieldError
                            fieldDefinition.outputType with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]
              | some resolved =>
                  cases hcompleted
                        : GraphQL.Execution.completeValue schema resolvers
                            variableValues depth' fieldDefinition.outputType
                            (field :: rest) resolved with
                  | error errors =>
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]
                  | ok result =>
                      rcases result with ⟨response, errors⟩
                      simp [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.executeField,
                        GraphQL.Execution.singleFieldResult,
                        GraphQL.Execution.Result.getD, hlookup, hresolve,
                        hcompleted]

theorem specExecuteRootSelectionSet_key_mem
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name)
    : responseName
        ∈ (GraphQL.Execution.executeRootSelectionSetData schema resolvers
            variableValues depth parentType source selectionSet).map
            Prod.fst
      -> responseName
          ∈ (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet).map
              Prod.fst := by
  intro hmem
  simpa [GraphQL.Execution.executeRootSelectionSetData] using
    executeCollectedFields_key_mem schema resolvers variableValues depth source
      hmem

theorem executeRootSelectionSet_key_mem_of_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (responseName : Name)
    (hroot
      : executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source selectionSet)
    : responseName
        ∈ (GraphQL.Execution.Result.getD []
            (executeRootSelectionSet schema resolvers variableValues depth
              parentType source selectionSet)).map
            Prod.fst
      -> responseName
          ∈ (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet).map
              Prod.fst := by
    intro hmem
    apply specExecuteRootSelectionSet_key_mem schema resolvers variableValues
      depth parentType source selectionSet responseName
    simpa [hroot, GraphQL.Execution.executeRootSelectionSetData] using hmem

theorem responseName_fresh_of_disjoint_single_field
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hleftEq
      : executeRootSelectionSet schema resolvers variableValues depth parentType
          source left
        = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source left)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source
            [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : responseName
      ∉ (GraphQL.Execution.Result.getD []
          (executeRootSelectionSet schema resolvers variableValues depth
            parentType source left)).map
          Prod.fst := by
  intro hmem
  have hleftMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst :=
    executeRootSelectionSet_key_mem_of_eq_spec schema resolvers variableValues
      depth parentType source left responseName hleftEq hmem
  have hrightMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]).map
          Prod.fst := by
    simp [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      hallowed]
  exact hdisjoint responseName hleftMem hrightMem

theorem visitSubfields_object_empty_key_mem_collectFields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection) (fields : List (Name × ResponseValue))
    (responseName : Name)
    : (visitSubfields schema resolvers variableValues depth parentType source
          selectionSet (.object [])).fst
        = .object fields
      -> responseName ∈ fields.map Prod.fst
      -> responseName
          ∈ (GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet).map
              Prod.fst := by
  intro hvisit hmem
  by_cases hcollect :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet).map Prod.fst
  · exact hcollect
  have hpreserve :=
    visitSubfields_responseObjectField?_of_not_mem_collectFields schema
      resolvers variableValues depth parentType source responseName selectionSet
      (.object []) hcollect
  rw [hvisit] at hpreserve
  rcases lookupResponseField?_some_of_mem responseName fields hmem with
    ⟨response, hlookup⟩
  simp [responseObjectField?, lookupResponseField?, hlookup] at hpreserve

theorem responseName_fresh_of_disjoint_single_field_visitSubfields
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source
            [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : ∀ fields status,
        visitSubfields schema resolvers variableValues depth parentType source
            left (.object [])
          = (.object fields, status)
        -> responseName ∉ fields.map Prod.fst := by
  intro fields status hvisit hmem
  have hleftMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source left).map Prod.fst :=
    visitSubfields_object_empty_key_mem_collectFields schema resolvers
      variableValues depth parentType source left fields responseName
      (by simp [hvisit]) hmem
  have hrightMem :
      responseName ∈
        (GraphQL.Execution.collectFields schema variableValues parentType
          source
          [.field responseName fieldName arguments directives selectionSet]).map
          Prod.fst := by
    simp [GraphQL.Execution.collectFields,
      GraphQL.Execution.collectSelection, GraphQL.Execution.mergeExecutableGroups,
      hallowed]
  exact hdisjoint responseName hleftMem hrightMem

theorem executableGroupNamesDisjoint_single_field_of_responseName_fresh
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh
      : responseName
        ∉ (GraphQL.Execution.collectFields schema variableValues parentType
            source left).map
            Prod.fst)
    : GraphQL.NormalForm.executableGroupNamesDisjoint
        (GraphQL.Execution.collectFields schema variableValues parentType source left)
        (GraphQL.Execution.collectFields schema variableValues parentType source
          [.field responseName fieldName arguments directives selectionSet]) := by
  intro candidate hleft hright
  simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
    GraphQL.Execution.mergeExecutableGroups, hallowed] at hright
  exact hfresh (by simpa [hright] using hleft)

theorem executeCollectedFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        PairKeysNodup groups
        -> PairKeysNodup
            (GraphQL.Execution.executeCollectedFieldsData schema resolvers
              variableValues depth source groups)
  | [], _hnodup => by
      simp [GraphQL.Execution.executeCollectedFieldsData,
        GraphQL.Execution.executeCollectedFields, GraphQL.Execution.Result.getD,
        PairKeysNodup]
  | (groupName, fields) :: rest, hnodup => by
      have hrestNodup : PairKeysNodup rest :=
        PairKeysNodup.tail hnodup
      cases hhead :
          GraphQL.Execution.executeField schema resolvers variableValues depth
            source groupName fields with
      | error headErrors =>
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, PairKeysNodup, hhead, htail]
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, PairKeysNodup, hhead, htail]
      | ok headResult =>
          rcases headResult with ⟨headFields, headErrors⟩
          cases htail :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth source rest with
          | error tailErrors =>
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, PairKeysNodup, hhead, htail]
          | ok tailResult =>
              rcases tailResult with ⟨tailFields, tailErrors⟩
              have hheadNodup : PairKeysNodup headFields := by
                simpa [GraphQL.Execution.executeFieldData,
                  GraphQL.Execution.Result.getD, hhead] using
                  executeField_pairKeysNodup schema resolvers variableValues
                    depth source groupName fields
              have htailNodup : PairKeysNodup tailFields := by
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.Result.getD, htail] using
                  executeCollectedFields_pairKeysNodup schema resolvers
                    variableValues depth source rest hrestNodup
              have hdisjoint :
                  ∀ responseName,
                    responseName ∈ headFields.map Prod.fst ->
                      responseName ∉ tailFields.map Prod.fst := by
                intro responseName hheadMem htailMem
                have hheadKey :
                    responseName = groupName :=
                  executeField_key_mem schema resolvers variableValues depth
                    source (responseName := responseName)
                    (groupName := groupName) (fields := fields) <| by
                      simpa [GraphQL.Execution.executeFieldData,
                        GraphQL.Execution.Result.getD, hhead] using hheadMem
                have htailKey :
                    responseName ∈ rest.map Prod.fst :=
                  executeCollectedFields_key_mem schema resolvers
                    variableValues depth source <| by
                      simpa [GraphQL.Execution.executeCollectedFieldsData,
                        GraphQL.Execution.Result.getD, htail] using htailMem
                rw [hheadKey] at htailKey
                exact PairKeysNodup.head_not_mem_tail hnodup htailKey
              simpa [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hhead, htail] using
                PairKeysNodup.append hheadNodup htailNodup hdisjoint

theorem collectFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : PairKeysNodup
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet) :=
  PairKeysNodup_of_executableGroupNamesNodup
    (GraphQL.Execution.collectFields schema variableValues parentType source selectionSet)
    (NormalForm.collectFields_namesNodup schema variableValues parentType
      source selectionSet)

theorem collectSubfields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectIdentity)
    (fields : List ExecutableField)
    : PairKeysNodup
        (GraphQL.Execution.collectSubfields schema variableValues objectType
          objectValue fields) := by
  simpa [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
    using
      collectFields_pairKeysNodup schema variableValues objectType objectValue
        (GraphQL.Execution.mergedFieldSelectionSet fields)

mutual
  theorem specExecuteCollectedFields_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (source : ResolverValue ObjectIdentity)
      : ∀ groups,
          PairKeysNodup groups
          -> ResponseMergeReady
              (.object
                (GraphQL.Execution.executeCollectedFieldsData schema resolvers
                  variableValues depth source groups))
    | [], _hnodup => by
        simpa [GraphQL.Execution.executeCollectedFieldsData,
          GraphQL.Execution.executeCollectedFields,
          GraphQL.Execution.Result.getD] using
          ResponseMergeReady_empty_object
    | (groupName, fields) :: rest, hnodup => by
        have hrestNodup : PairKeysNodup rest :=
          PairKeysNodup.tail hnodup
        cases hhead :
            GraphQL.Execution.executeField schema resolvers variableValues depth
              source groupName fields with
        | error headErrors =>
            cases htail :
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues depth source rest with
            | error tailErrors =>
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, hhead, htail] using
                  ResponseMergeReady_empty_object
            | ok tailResult =>
                rcases tailResult with ⟨tailFields, tailErrors⟩
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, hhead, htail] using
                  ResponseMergeReady_empty_object
        | ok headResult =>
            rcases headResult with ⟨headFields, headErrors⟩
            cases htail :
                GraphQL.Execution.executeCollectedFields schema resolvers
                  variableValues depth source rest with
            | error tailErrors =>
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, hhead, htail] using
                  ResponseMergeReady_empty_object
            | ok tailResult =>
                rcases tailResult with ⟨tailFields, tailErrors⟩
                have hheadReady : ResponseMergeReady (.object headFields) := by
                  simpa [GraphQL.Execution.executeFieldData,
                    GraphQL.Execution.Result.getD, hhead] using
                    specExecuteField_response_ready schema resolvers
                      variableValues depth source groupName fields
                have htailReady : ResponseMergeReady (.object tailFields) := by
                  simpa [GraphQL.Execution.executeCollectedFieldsData,
                    GraphQL.Execution.Result.getD, htail] using
                    specExecuteCollectedFields_response_ready schema resolvers
                      variableValues depth source rest hrestNodup
                have hdisjoint :
                    ∀ responseName,
                      responseName ∈ headFields.map Prod.fst ->
                        responseName ∉ tailFields.map Prod.fst := by
                  intro responseName hheadMem htailMem
                  have hheadKey :
                      responseName = groupName :=
                    executeField_key_mem schema resolvers variableValues depth
                      source (responseName := responseName)
                      (groupName := groupName) (fields := fields) <| by
                        simpa [GraphQL.Execution.executeFieldData,
                          GraphQL.Execution.Result.getD, hhead] using hheadMem
                  have htailKey :
                      responseName ∈ rest.map Prod.fst :=
                    executeCollectedFields_key_mem schema resolvers
                      variableValues depth source <| by
                        simpa [GraphQL.Execution.executeCollectedFieldsData,
                          GraphQL.Execution.Result.getD, htail] using htailMem
                  rw [hheadKey] at htailKey
                  exact PairKeysNodup.head_not_mem_tail hnodup htailKey
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, hhead, htail] using
                  ResponseMergeReady_object_append headFields tailFields
                    hheadReady htailReady
                    (by
                      intro responseName htailMem hheadMem
                      exact hdisjoint responseName hheadMem htailMem)

  theorem specExecuteField_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues) (depth : Nat)
      (source : ResolverValue ObjectIdentity)
      : ∀ responseName fields,
          ResponseMergeReady
            (.object
              (GraphQL.Execution.executeFieldData schema resolvers variableValues
                depth source responseName fields))
    | _responseName, [] => by
        simpa [GraphQL.Execution.executeFieldData,
          GraphQL.Execution.executeField, GraphQL.Execution.Result.getD] using
          ResponseMergeReady_empty_object
    | responseName, field :: rest => by
        cases depth with
        | zero =>
            simpa [GraphQL.Execution.executeFieldData,
              GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
              GraphQL.Execution.outOfFuel] using
              ResponseMergeReady_empty_object
        | succ depth' =>
            cases hlookup :
                schema.lookupField field.parentType field.fieldName with
            | none =>
                simpa [GraphQL.Execution.executeFieldData,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.getD,
                  hlookup] using
                  ResponseMergeReady_empty_object
            | some fieldDefinition =>
                cases hresolve :
                    resolvers.resolve field.parentType field.fieldName
                      field.arguments source with
                | none =>
                    cases hcompleted :
                        GraphQL.Execution.handleFieldError
                          fieldDefinition.outputType with
                    | error errors =>
                        simpa [GraphQL.Execution.executeFieldData,
                          GraphQL.Execution.executeField,
                          GraphQL.Execution.singleFieldResult,
                          GraphQL.Execution.Result.getD, hlookup, hresolve,
                          hcompleted] using
                          ResponseMergeReady_empty_object
                    | ok result =>
                        rcases result with ⟨response, errors⟩
                        have hresponseReady : ResponseMergeReady response := by
                          simpa [resultValueOrNull, hcompleted] using
                            resultValueOrNull_handleFieldError_ready
                              fieldDefinition.outputType
                        simpa [GraphQL.Execution.executeFieldData,
                          GraphQL.Execution.executeField,
                          GraphQL.Execution.singleFieldResult,
                          GraphQL.Execution.Result.getD, hlookup, hresolve,
                          hcompleted] using
                          ResponseMergeReady.object [(responseName, response)]
                            (by simp [PairKeysNodup])
                            (by
                              intro candidate candidateResponse hmem
                              simp at hmem
                              rcases hmem with ⟨rfl, rfl⟩
                              exact hresponseReady)
                | some resolved =>
                    cases hcompleted :
                        GraphQL.Execution.completeValue schema resolvers
                          variableValues depth' fieldDefinition.outputType
                          (field :: rest) resolved with
                    | error errors =>
                        simpa [GraphQL.Execution.executeFieldData,
                          GraphQL.Execution.executeField,
                          GraphQL.Execution.singleFieldResult,
                          GraphQL.Execution.Result.getD, hlookup, hresolve,
                          hcompleted] using
                          ResponseMergeReady_empty_object
                    | ok result =>
                        rcases result with ⟨response, errors⟩
                        have hresponseReady : ResponseMergeReady response := by
                          simpa [GraphQL.Execution.completeValueData,
                            GraphQL.Execution.Result.getD, hcompleted] using
                            specCompleteValue_response_ready schema resolvers
                              variableValues depth'
                              fieldDefinition.outputType (field :: rest)
                              resolved
                        simpa [GraphQL.Execution.executeFieldData,
                          GraphQL.Execution.executeField,
                          GraphQL.Execution.singleFieldResult,
                          GraphQL.Execution.Result.getD, hlookup, hresolve,
                          hcompleted] using
                          ResponseMergeReady.object [(responseName, response)]
                            (by simp [PairKeysNodup])
                            (by
                              intro candidate candidateResponse hmem
                              simp at hmem
                              rcases hmem with ⟨rfl, rfl⟩
                              exact hresponseReady)

  theorem specCompleteValue_response_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      : ∀ (depth : Nat) (fieldType : TypeRef) (fields : List ExecutableField)
          (value : ResolverValue ObjectIdentity),
          ResponseMergeReady
            (GraphQL.Execution.completeValueData schema resolvers variableValues
              depth fieldType fields value)
    | 0, _fieldType, _fields, value => by
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue, GraphQL.Execution.outOfFuel,
          GraphQL.Execution.Result.getD] using
          ResponseMergeReady.null
    | depth + 1, .nonNull inner, fields, value => by
        have hinner :
            ResponseMergeReady
              (resultValueOrNull
                (GraphQL.Execution.completeValue schema resolvers
                  variableValues (depth + 1) inner fields value)) := by
          simpa [GraphQL.Execution.completeValueData,
            resultValueOrNull_eq_result_getD] using
            specCompleteValue_response_ready schema resolvers
              variableValues (depth + 1) inner fields value
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue,
          ← resultValueOrNull_eq_result_getD
            (GraphQL.Execution.nonNullCompletion
              (GraphQL.Execution.completeValue schema resolvers variableValues
                (depth + 1) inner fields value))] using
          resultValueOrNull_nonNullCompletion_ready
            (GraphQL.Execution.completeValue schema resolvers variableValues
              (depth + 1) inner fields value)
            hinner
    | depth + 1, .named typeName, fields, .null => by
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
          ResponseMergeReady.null
    | depth + 1, .named typeName, fields, .scalar value => by
        by_cases hcomposite :
            (TypeRef.named typeName).isCompositeBool schema = true
        · simp [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD,
            hcomposite]
          exact ResponseMergeReady.null
        · simp [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD,
            hcomposite]
          exact ResponseMergeReady.scalar value
    | depth + 1, .named typeName, fields,
        .object runtimeType identity => by
        by_cases hinclude :
            schema.typeIncludesObjectBool typeName runtimeType
        · have hgroupsNodup :
              PairKeysNodup
                (GraphQL.Execution.collectSubfields schema variableValues
                  runtimeType (.object runtimeType identity) fields) :=
            collectSubfields_pairKeysNodup schema variableValues runtimeType
              (.object runtimeType identity) fields
          cases hcompleted :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues depth (.object runtimeType identity)
                (GraphQL.Execution.collectSubfields schema variableValues
                  runtimeType (.object runtimeType identity) fields) with
          | error errors =>
              have hcompleted' :
                  GraphQL.Execution.executeCollectedFields schema resolvers
                    variableValues depth (.object runtimeType identity)
                    (GraphQL.Execution.collectFields schema variableValues
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet fields)) =
                  .error errors := by
                simpa
                  [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using hcompleted
              simpa [GraphQL.Execution.completeValueData,
                GraphQL.Execution.completeValue, hinclude,
                GraphQL.Execution.catchBubbleAsNull,
                GraphQL.Execution.Result.getD, hcompleted',
                GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                using
                ResponseMergeReady.null
          | ok result =>
              rcases result with ⟨completedFields, errors⟩
              have hcompleted' :
                  GraphQL.Execution.executeCollectedFields schema resolvers
                    variableValues depth (.object runtimeType identity)
                    (GraphQL.Execution.collectFields schema variableValues
                      runtimeType (.object runtimeType identity)
                      (GraphQL.Execution.mergedFieldSelectionSet fields)) =
                  .ok (completedFields, errors) := by
                simpa
                  [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using hcompleted
              have hready :
                  ResponseMergeReady (.object completedFields) := by
                simpa [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.Result.getD, hcompleted',
                  GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                  using
                  specExecuteCollectedFields_response_ready schema resolvers
                    variableValues depth (.object runtimeType identity)
                    (GraphQL.Execution.collectSubfields schema variableValues
                      runtimeType (.object runtimeType identity) fields)
                    hgroupsNodup
              simpa [GraphQL.Execution.completeValueData,
                GraphQL.Execution.completeValue, hinclude,
                GraphQL.Execution.catchBubbleAsNull,
                GraphQL.Execution.Result.getD, hcompleted',
                GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                using hready
        · simpa [GraphQL.Execution.completeValueData,
            GraphQL.Execution.completeValue, hinclude,
            GraphQL.Execution.Result.getD] using
            ResponseMergeReady.null
    | depth + 1, .named typeName, fields, .list values => by
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
          ResponseMergeReady.null
    | depth + 1, .list inner, fields, .null => by
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
          ResponseMergeReady.null
    | depth + 1, .list inner, fields, .scalar value => by
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
          ResponseMergeReady.null
    | depth + 1, .list inner, fields, .object runtimeType identity => by
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue, GraphQL.Execution.Result.getD] using
          ResponseMergeReady.null
    | depth + 1, .list inner, fields, .list values => by
        simpa [GraphQL.Execution.completeValueData,
          GraphQL.Execution.completeValue,
          ← resultValueOrNull_eq_result_getD
            (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
              (GraphQL.Execution.completeValueList schema resolvers
                variableValues depth inner fields values))] using
          resultValueOrNull_catchBubbleAsNull_ready
            ResponseValue.list
            (GraphQL.Execution.completeValueList schema resolvers
              variableValues depth inner fields values)
            (by
              intro completedValues errors hok
              exact ResponseMergeReady.list completedValues
                (specCompleteValueList_values_ready schema resolvers
                  variableValues depth inner fields values completedValues
                  errors hok))

  theorem specCompleteValueList_values_ready
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      : ∀ (depth : Nat) (fieldType : TypeRef)
          (fields : List ExecutableField)
          (values : List (ResolverValue ObjectIdentity))
          (completedValues : List ResponseValue) (errors : Nat),
          GraphQL.Execution.completeValueList schema resolvers variableValues
              depth fieldType fields values
            = .ok (completedValues, errors)
          -> ∀ response, response ∈ completedValues -> ResponseMergeReady response
    | _depth, _fieldType, _fields, [], completedValues, errors, hok => by
        intro response hmem
        simp [GraphQL.Execution.completeValueList] at hok
        rcases hok with ⟨hcompletedValues, _herrors⟩
        subst completedValues
        simp at hmem
    | depth, fieldType, fields, value :: values, completedValues, errors,
        hok => by
        cases hhead :
            GraphQL.Execution.completeValue schema resolvers variableValues
              depth fieldType fields value with
        | error headErrors =>
            cases htail :
                GraphQL.Execution.completeValueList schema resolvers
                  variableValues depth fieldType fields values with
            | error tailErrors =>
                simp [GraphQL.Execution.completeValueList,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine, hhead, htail] at hok
            | ok tailResult =>
                rcases tailResult with ⟨tailValues, tailErrors⟩
                simp [GraphQL.Execution.completeValueList,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine, hhead, htail] at hok
        | ok headResult =>
            rcases headResult with ⟨headValue, headErrors⟩
            cases htail :
                GraphQL.Execution.completeValueList schema resolvers
                  variableValues depth fieldType fields values with
            | error tailErrors =>
                simp [GraphQL.Execution.completeValueList,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine, hhead, htail] at hok
            | ok tailResult =>
                rcases tailResult with ⟨tailValues, tailErrors⟩
                simp [GraphQL.Execution.completeValueList,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine, hhead, htail] at hok
                rcases hok with ⟨rfl, rfl⟩
                intro response hmem
                rcases List.mem_cons.mp hmem with hheadMem | htailMem
                · subst response
                  simpa [GraphQL.Execution.completeValueData,
                    GraphQL.Execution.Result.getD, hhead] using
                    specCompleteValue_response_ready schema resolvers
                      variableValues depth fieldType fields value
                · exact
                    specCompleteValueList_values_ready schema resolvers
                      variableValues depth fieldType fields values tailValues
                      tailErrors htail response htailMem
end

theorem specExecuteCollectedFields_collectFields_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : ResponseMergeReady
        (.object
          (GraphQL.Execution.executeCollectedFieldsData schema resolvers
            variableValues depth source
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet))) :=
  specExecuteCollectedFields_response_ready schema resolvers variableValues
    depth source
    (GraphQL.Execution.collectFields schema variableValues parentType source selectionSet)
    (collectFields_pairKeysNodup schema variableValues parentType source selectionSet)

theorem specExecuteRootSelectionSet_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : ResponseMergeReady
        (.object
          (GraphQL.Execution.executeRootSelectionSetData schema resolvers
            variableValues depth parentType source selectionSet)) := by
  simpa [GraphQL.Execution.executeRootSelectionSetData,
    GraphQL.Execution.executeRootSelectionSet,
    GraphQL.Execution.executeCollectedFieldsData] using
    specExecuteCollectedFields_collectFields_response_ready schema resolvers
      variableValues depth parentType source selectionSet

theorem executeCollectedFields_collectFields_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : PairKeysNodup
        (GraphQL.Execution.executeCollectedFieldsData schema resolvers variableValues
          depth source
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)) :=
  executeCollectedFields_pairKeysNodup schema resolvers variableValues depth
    source
    (GraphQL.Execution.collectFields schema variableValues parentType source selectionSet)
    (collectFields_pairKeysNodup schema variableValues parentType source selectionSet)

theorem executeRootSelectionSet_pairKeysNodup
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : PairKeysNodup
        (GraphQL.Execution.Result.getD []
          (executeRootSelectionSet schema resolvers variableValues depth parentType
            source selectionSet)) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  have hnodup : PairKeysNodup fields := by
    simpa [hfields] using
      visitSubfields_pairKeysNodup schema resolvers variableValues depth
        parentType source selectionSet [] (by simp [PairKeysNodup])
  unfold executeRootSelectionSet
  cases hstatus
        : (visitSubfields schema resolvers variableValues depth parentType source
            selectionSet (.object [])).snd with
  | error errors =>
      simp [GraphQL.Execution.Result.getD, hstatus, PairKeysNodup]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [GraphQL.Execution.Result.getD, hstatus, hfields]
      exact hnodup

theorem executeRootSelectionSet_response_ready
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : ResponseMergeReady
        (.object
          (GraphQL.Execution.Result.getD []
            (executeRootSelectionSet schema resolvers variableValues depth
              parentType source selectionSet))) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source selectionSet []
  have hready : ResponseMergeReady (.object fields) := by
    simpa [hfields] using
      visitSubfields_response_ready schema resolvers variableValues depth
        parentType source selectionSet [] ResponseMergeReady_empty_object
  unfold executeRootSelectionSet
  cases hstatus
        : (visitSubfields schema resolvers variableValues depth parentType source
            selectionSet (.object [])).snd with
  | error errors =>
      simp [GraphQL.Execution.Result.getD, hstatus]
      exact ResponseMergeReady_empty_object
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [GraphQL.Execution.Result.getD, hstatus, hfields]
      exact hready

theorem ExecutionWindowEquivalent.ext
    (window : ExecutionWindow ObjectIdentity)
    (hresult : window.ungroupedResult = window.specResult)
    : ExecutionWindowEquivalent window := by
  simpa [ExecutionWindowEquivalent, ResponseResultEquivalent] using hresult

theorem ExecutionStateEquivalent.ext
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hresponse : state.ungroupedProjectionResult = state.specProjectionResult)
    : ExecutionStateEquivalent state := by
  simpa [ExecutionStateEquivalent, ResponseResultEquivalent] using hresponse

theorem stateEquivalent_of_executeRootSelectionSet_eq_spec
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hroot
      : executeRootSelectionSet schema resolvers variableValues depth parentType
          source selectionSet
        = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
            depth parentType source selectionSet)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } := by
  apply ExecutionStateEquivalent.ext
  rw [ExecutionEquivalenceState.ungroupedProjectionResult,
    visitSubfieldsResult_empty_eq_executeRootSelectionSet_object, hroot]
  unfold ExecutionEquivalenceState.specProjectionResult
  unfold GraphQL.Execution.executeRootSelectionSet
  cases hspec
        : GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            depth source
            (GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet) with
  | error errors =>
      simp
  | ok result =>
      rcases result with ⟨fields, errors⟩
      have hnodup : PairKeysNodup fields := by
        have hcollected :=
          executeCollectedFields_collectFields_pairKeysNodup schema resolvers
            variableValues depth parentType source selectionSet
        simpa [GraphQL.Execution.executeCollectedFieldsData,
          GraphQL.Execution.Result.getD, hspec] using hcollected
      have hmerge :
          mergeResponse (.object []) (.object fields) = .object fields :=
        mergeResponse_empty_object_left_of_pairKeysNodup fields hnodup
      simp [hmerge]

theorem stateEquivalent_of_exact_empty_group
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    (hcollect
      : GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet
        = [])
    (hdirect
      : VisitSubfieldsFlatCollects schema resolvers variableValues depth
          parentType source selectionSet (.object []))
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := selectionSet
            }
          initial := .object []
        } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source selectionSet
    (executeRootSelectionSet_eq_spec_of_exact_empty_group schema resolvers
      variableValues depth parentType source selectionSet hcollect hdirect)

theorem executeRootSelectionSet_eq_spec_of_state_equivalent
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate : ExecutionStateEquivalent { window := window, initial := .object [] })
    (hmerge
      : mergeResponse (.object [])
          (.object
            (GraphQL.Execution.executeCollectedFieldsData window.schema
              window.resolvers window.variableValues window.depth window.source
              (GraphQL.Execution.collectFields window.schema window.variableValues
                window.parentType window.source window.selectionSet)))
        = .object
            (GraphQL.Execution.executeCollectedFieldsData window.schema
              window.resolvers window.variableValues window.depth window.source
              (GraphQL.Execution.collectFields window.schema window.variableValues
                window.parentType window.source window.selectionSet)))
    : window.ungroupedResult = window.specResult := by
  have hprojection :
      ExecutionWindow.visitSubfieldsResult window.schema window.resolvers
        window.variableValues window.depth window.parentType window.source
        window.selectionSet (.object []) =
      match
        GraphQL.Execution.executeCollectedFields window.schema
          window.resolvers window.variableValues window.depth window.source
          (GraphQL.Execution.collectFields window.schema
            window.variableValues window.parentType window.source
            window.selectionSet)
      with
      | .error errors => .error errors
      | .ok (fields, errors) =>
          .ok (mergeResponse (.object []) (.object fields), errors) := by
    change
      ExecutionWindow.visitSubfieldsResult window.schema window.resolvers
          window.variableValues window.depth window.parentType window.source
          window.selectionSet (.object []) =
        match
          GraphQL.Execution.executeCollectedFields window.schema
            window.resolvers window.variableValues window.depth window.source
            (GraphQL.Execution.collectFields window.schema
              window.variableValues window.parentType window.source
              window.selectionSet)
        with
        | .error errors => .error errors
        | .ok (fields, errors) =>
            .ok (mergeResponse (.object []) (.object fields), errors) at hstate
    exact hstate
  rw [visitSubfieldsResult_empty_eq_executeRootSelectionSet_object] at hprojection
  unfold ExecutionWindow.ungroupedResult ExecutionWindow.specResult
  unfold GraphQL.Execution.executeRootSelectionSet
  cases hspec
        : GraphQL.Execution.executeCollectedFields window.schema window.resolvers
            window.variableValues window.depth window.source
            (GraphQL.Execution.collectFields window.schema window.variableValues
              window.parentType window.source window.selectionSet) with
  | error errors =>
      cases hungrouped
            : executeRootSelectionSet window.schema window.resolvers
                window.variableValues window.depth window.parentType
                window.source window.selectionSet with
      | error ungroupedErrors =>
          simpa [hungrouped, hspec] using hprojection
      | ok ungroupedResult =>
          rcases ungroupedResult with ⟨ungroupedFields, ungroupedErrors⟩
          simp [hungrouped, hspec] at hprojection
  | ok result =>
      rcases result with ⟨fields, errors⟩
      have hmergeFields : mergeResponse (.object []) (.object fields) =
          .object fields := by
        have hget :
            GraphQL.Execution.executeCollectedFieldsData window.schema
              window.resolvers window.variableValues window.depth window.source
              (GraphQL.Execution.collectFields window.schema
                window.variableValues window.parentType window.source
                window.selectionSet) = fields := by
          simp [GraphQL.Execution.executeCollectedFieldsData,
            GraphQL.Execution.Result.getD, hspec]
        simpa [hget] using hmerge
      cases hungrouped
            : executeRootSelectionSet window.schema window.resolvers
                window.variableValues window.depth window.parentType
                window.source window.selectionSet with
      | error ungroupedErrors =>
          simp [hungrouped, hspec, hmergeFields] at hprojection
      | ok ungroupedResult =>
          rcases ungroupedResult with ⟨ungroupedFields, ungroupedErrors⟩
          have hwrapped :
              (Except.ok (ResponseValue.object ungroupedFields,
                  ungroupedErrors) : Result ResponseValue) =
                (Except.ok (ResponseValue.object fields, errors) :
                  Result ResponseValue) := by
            simpa [hungrouped, hspec, hmergeFields] using hprojection
          cases hwrapped
          rfl

theorem executeRootSelectionSet_eq_spec_of_state_equivalent_nodup
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate : ExecutionStateEquivalent { window := window, initial := .object [] })
    (hnodup
      : PairKeysNodup
          (GraphQL.Execution.executeCollectedFieldsData window.schema
            window.resolvers window.variableValues window.depth window.source
            (GraphQL.Execution.collectFields window.schema window.variableValues
              window.parentType window.source window.selectionSet)))
    : window.ungroupedResult = window.specResult :=
  executeRootSelectionSet_eq_spec_of_state_equivalent window hstate
    (mergeResponse_empty_object_left_of_pairKeysNodup
      (GraphQL.Execution.executeCollectedFieldsData window.schema
        window.resolvers window.variableValues window.depth window.source
        (GraphQL.Execution.collectFields window.schema window.variableValues
          window.parentType window.source window.selectionSet))
      hnodup)

theorem executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
    {ObjectIdentity : Type}
    (window : ExecutionWindow ObjectIdentity)
    (hstate : ExecutionStateEquivalent { window := window, initial := .object [] })
    : window.ungroupedResult = window.specResult :=
  executeRootSelectionSet_eq_spec_of_state_equivalent_nodup window hstate
    (executeCollectedFields_collectFields_pairKeysNodup window.schema
      window.resolvers window.variableValues window.depth window.parentType
      window.source window.selectionSet)

theorem executeRootSelectionSet_append_single_field_allowed_eq_combine
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hfresh
      : ∀ fields status,
          visitSubfields schema resolvers variableValues (depth + 1)
              parentType source left (.object [])
            = (.object fields, status)
          -> responseName ∉ fields.map Prod.fst)
    : executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        (left ++ [.field responseName fieldName arguments directives selectionSet])
      = Result.combine List.append
          (executeRootSelectionSet schema resolvers variableValues (depth + 1)
            parentType source left)
          (executeRootSelectionSet schema resolvers variableValues (depth + 1)
            parentType source
            [.field responseName fieldName arguments directives selectionSet]) := by
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues
      (depth + 1) parentType source left []
  let leftStatus :=
    (visitSubfields schema resolvers variableValues (depth + 1) parentType
      source left (.object [])).snd
  have hleftVisit :
      visitSubfields schema resolvers variableValues (depth + 1) parentType
        source left (.object []) = (.object fields, leftStatus) := by
    exact Prod.ext hfields rfl
  have hfreshFields : responseName ∉ fields.map Prod.fst :=
    hfresh fields leftStatus hleftVisit
  have hrightVisit :
      visitSubfields schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet]
        (.object fields) =
      let fieldResult :=
        executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)
      (.object (fields ++ [(responseName, resultValueOrNull fieldResult)]),
        resultStatus fieldResult) :=
    visitSubfields_single_field_allowed_succ_fresh_eq_append schema resolvers
      variableValues depth parentType source responseName fieldName arguments
      directives selectionSet fields hallowed hfreshFields
  have hsingle :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet] =
      GraphQL.Execution.singleFieldResult responseName
        (executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)) :=
    executeRootSelectionSet_single_field_allowed_succ_eq_executeField_empty
      schema resolvers variableValues depth parentType source responseName
      fieldName arguments directives selectionSet hallowed
  have happendVisit :
      visitSubfields schema resolvers variableValues (depth + 1) parentType
        source
        (left ++
          [.field responseName fieldName arguments directives selectionSet])
        (.object []) =
      let fieldResult :=
        executeField schema resolvers variableValues depth source none
          (executableField parentType responseName fieldName arguments
            selectionSet)
      (.object (fields ++ [(responseName, resultValueOrNull fieldResult)]),
        combineVisitStatus leftStatus (resultStatus fieldResult)) := by
    rw [visitSubfields_append_equivalence]
    simp [hleftVisit, hrightVisit]
  have hleftRoot :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source left =
      match leftStatus with
      | .error errors => .error errors
      | .ok (_unit, errors) => .ok (fields, errors) := by
    unfold executeRootSelectionSet
    rw [hleftVisit]
    rfl
  have happendRoot :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) =
      match
        combineVisitStatus leftStatus
          (resultStatus
            (executeField schema resolvers variableValues depth source
              none
              (executableField parentType responseName fieldName arguments
                selectionSet)))
      with
      | .error errors => .error errors
      | .ok (_unit, errors) =>
          .ok
            (fields ++
              [(responseName,
                resultValueOrNull
                  (executeField schema resolvers variableValues depth source
                    none
                    (executableField parentType responseName fieldName
                      arguments selectionSet)))],
              errors) := by
    unfold executeRootSelectionSet
    rw [happendVisit]
    rfl
  rw [happendRoot, hleftRoot, hsingle]
  cases leftStatus with
  | error leftErrors =>
      cases hfield :
          executeField schema resolvers variableValues depth source none
            (executableField parentType responseName fieldName arguments
              selectionSet) <;>
        simp [combineVisitStatus, Result.combine,
          GraphQL.Execution.Result.combine, GraphQL.Execution.singleFieldResult,
          resultStatus, visitOk]
  | ok leftStatusResult =>
      rcases leftStatusResult with ⟨unitValue, leftErrors⟩
      cases unitValue
      cases hfield
            : executeField schema resolvers variableValues depth source none
                (executableField parentType responseName fieldName arguments
                  selectionSet) with
      | error fieldErrors =>
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, GraphQL.Execution.singleFieldResult,
            resultStatus]
      | ok fieldResult =>
          rcases fieldResult with ⟨response, fieldErrors⟩
          simp [combineVisitStatus, Result.combine,
            GraphQL.Execution.Result.combine, GraphQL.Execution.singleFieldResult,
            resultValueOrNull, resultStatus, visitOk]

theorem stateEquivalent_of_append_single_field_of_disjoint
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth + 1
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hright
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth + 1
                parentType := parentType
                source := source
                selectionSet :=
                  [.field responseName fieldName arguments directives selectionSet]
              }
            initial := .object []
          })
    (hdisjoint
      : GraphQL.NormalForm.executableGroupNamesDisjoint
          (GraphQL.Execution.collectFields schema variableValues parentType source left)
          (GraphQL.Execution.collectFields schema variableValues parentType
            source
            [.field responseName fieldName arguments directives selectionSet]))
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth + 1
              parentType := parentType
              source := source
              selectionSet :=
                left ++ [.field responseName fieldName arguments directives selectionSet]
            }
          initial := .object []
        } := by
  have hleftEq :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source left =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source left :=
    executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth + 1
        parentType := parentType
        source := source
        selectionSet := left }
      hleft
  have hrightEq :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        [.field responseName fieldName arguments directives selectionSet] =
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source
        [.field responseName fieldName arguments directives selectionSet] :=
    executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth + 1
        parentType := parentType
        source := source
        selectionSet :=
          [.field responseName fieldName arguments directives selectionSet] }
      hright
  have hungroupedAppend :
      executeRootSelectionSet schema resolvers variableValues (depth + 1)
        parentType source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) =
      Result.combine List.append
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source left)
        (executeRootSelectionSet schema resolvers variableValues (depth + 1)
          parentType source
          [.field responseName fieldName arguments directives selectionSet]) :=
    executeRootSelectionSet_append_single_field_allowed_eq_combine schema
      resolvers variableValues depth parentType source left responseName
      fieldName arguments directives selectionSet hallowed
      (responseName_fresh_of_disjoint_single_field_visitSubfields schema
        resolvers variableValues (depth + 1) parentType source left responseName
        fieldName arguments directives selectionSet hdisjoint hallowed)
  have hspecAppend :
      GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        (depth + 1) parentType source
        (left ++
          [.field responseName fieldName arguments directives selectionSet]) =
      Result.combine List.append
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues (depth + 1) parentType source left)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues (depth + 1) parentType source
          [.field responseName fieldName arguments directives selectionSet]) :=
    specExecuteRootSelectionSet_append_of_namesDisjoint schema resolvers
      variableValues (depth + 1) parentType source left
      [.field responseName fieldName arguments directives selectionSet]
      hdisjoint
  exact
    stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
      variableValues (depth + 1) parentType source
      (left ++
        [.field responseName fieldName arguments directives selectionSet])
      (by
        calc
          executeRootSelectionSet schema resolvers variableValues (depth + 1)
              parentType source
              (left ++
                [.field responseName fieldName arguments directives
                  selectionSet])
              =
            Result.combine List.append
              (executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source left)
              (executeRootSelectionSet schema resolvers variableValues
                (depth + 1) parentType source
                [.field responseName fieldName arguments directives
                  selectionSet]) := by
              exact hungroupedAppend
          _ =
            Result.combine List.append
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues (depth + 1) parentType source left)
              (GraphQL.Execution.executeRootSelectionSet schema resolvers
                variableValues (depth + 1) parentType source
                [.field responseName fieldName arguments directives
                  selectionSet]) := by
              rw [hleftEq, hrightEq]
          _ =
            GraphQL.Execution.executeRootSelectionSet schema resolvers
              variableValues (depth + 1) parentType source
              (left ++
                [.field responseName fieldName arguments directives
                  selectionSet]) := by
              exact hspecAppend.symm)

theorem executeRootSelectionSet_append_single_field_blocked_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (left ++ [.field responseName fieldName arguments directives selectionSet])
      = executeRootSelectionSet schema resolvers variableValues depth parentType
          source left := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus
        : (visitSubfields schema resolvers variableValues depth parentType source
            left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields,
        visitSelection_field_directives_blocked schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet (.object fields) hblocked]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields,
        visitSelection_field_directives_blocked schema resolvers
          variableValues depth parentType source responseName fieldName
          arguments directives selectionSet (.object fields) hblocked]

theorem specExecuteRootSelectionSet_append_single_field_blocked_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++ [.field responseName fieldName arguments directives selectionSet])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source left := by
  have hcollect :
      GraphQL.Execution.collectSelection schema variableValues parentType source
        (.field responseName fieldName arguments directives selectionSet) = [] := by
    simp [GraphQL.Execution.collectSelection, hblocked]
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [.field responseName fieldName arguments directives selectionSet]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        left := by
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, hcollect,
      GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (left ++ [.field responseName fieldName arguments directives selectionSet])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source
          (left
            ++ [.field responseName fieldName arguments directives selectionSet]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
          source
          (left ++ [.field responseName fieldName arguments directives selectionSet])
        = executeRootSelectionSet schema resolvers variableValues depth parentType
            source left := by
      exact executeRootSelectionSet_append_single_field_blocked_eq_left
        schema resolvers variableValues depth parentType source left
        responseName fieldName arguments directives selectionSet hblocked
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source left := by
      exact
        executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          hleft
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source
          (left
            ++ [.field responseName fieldName arguments directives selectionSet]) := by
      exact
        (specExecuteRootSelectionSet_append_single_field_blocked_eq_left
          schema resolvers variableValues depth parentType source left
          responseName fieldName arguments directives selectionSet
          hblocked).symm

theorem stateEquivalent_of_append_single_field_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet :=
                left ++ [.field responseName fieldName arguments directives selectionSet]
            }
          initial := .object []
        } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.field responseName fieldName arguments directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_field_blocked hleft hblocked)

theorem executeRootSelectionSet_append_single_selection_noop_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection) (selection : Selection)
    (hvisit
      : ∀ fields,
          visitSelection schema resolvers variableValues depth parentType source
            selection (.object fields)
          = (.object fields, visitOk))
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [selection])
      = executeRootSelectionSet schema resolvers variableValues depth parentType
          source left := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus
        : (visitSubfields schema resolvers variableValues depth parentType source
            left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields, hvisit fields]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields, hvisit fields]

theorem specExecuteRootSelectionSet_append_single_selection_noop_eq_left
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left : List Selection) (selection : Selection)
    (hcollect
      : GraphQL.Execution.collectSelection schema variableValues parentType
          source selection
        = [])
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source (left ++ [selection])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source left := by
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [selection]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        left := by
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, hcollect,
      GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_selection_noop
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hvisit
      : ∀ fields,
          visitSelection schema resolvers variableValues depth parentType source
            selection (.object fields)
          = (.object fields, visitOk))
    (hcollect
      : GraphQL.Execution.collectSelection schema variableValues parentType
          source selection
        = [])
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [selection])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source (left ++ [selection]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
          source (left ++ [selection])
        = executeRootSelectionSet schema resolvers variableValues depth parentType
            source left := by
      exact executeRootSelectionSet_append_single_selection_noop_eq_left
        schema resolvers variableValues depth parentType source left
        selection hvisit
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source left := by
      exact
        executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left }
          hleft
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source (left ++ [selection]) := by
      exact
        (specExecuteRootSelectionSet_append_single_selection_noop_eq_left
          schema resolvers variableValues depth parentType source left
          selection hcollect).symm

theorem stateEquivalent_of_append_single_selection_noop
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection} {selection : Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hvisit
      : ∀ fields,
          visitSelection schema resolvers variableValues depth parentType source
            selection (.object fields)
          = (.object fields, visitOk))
    (hcollect
      : GraphQL.Execution.collectSelection schema variableValues parentType
          source selection
        = [])
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := left ++ [selection]
            }
          initial := .object []
        } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source (left ++ [selection])
    (executeRootSelectionSet_eq_spec_of_append_single_selection_noop hleft
      hvisit hcollect)

theorem stateEquivalent_of_append_single_inline_none_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet :=
                left ++ [.inlineFragment none directives selectionSet]
            }
          initial := .object []
        } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_none_directives_blocked schema resolvers
        variableValues depth parentType source directives selectionSet
        (.object fields) hblocked)
    (by
      simp [GraphQL.Execution.collectSelection, hblocked])

theorem stateEquivalent_of_append_single_inline_some_blocked
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hblocked : selectionDirectivesAllowBool variableValues directives = false)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet :=
                left ++ [.inlineFragment (some typeCondition) directives selectionSet]
            }
          initial := .object []
        } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_some_directives_blocked schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet (.object fields) hblocked)
    (by
      simp [GraphQL.Execution.collectSelection, hblocked])

theorem stateEquivalent_of_append_single_inline_some_not_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    {selectionSet : List Selection}
    (hleft
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left
              }
            initial := .object []
          })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (hnotApply : doesFragmentTypeApplyBool schema parentType source typeCondition = false)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet :=
                left ++ [.inlineFragment (some typeCondition) directives selectionSet]
            }
          initial := .object []
        } :=
  stateEquivalent_of_append_single_selection_noop hleft
    (by
      intro fields
      exact visitSelection_inline_some_type_not_apply schema resolvers
        variableValues depth parentType source typeCondition directives
        selectionSet (.object fields) hallowed hnotApply)
    (by
      simp [GraphQL.Execution.collectSelection, hallowed, hnotApply])

theorem executeRootSelectionSet_append_single_inline_none_allowed_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [.inlineFragment none directives selectionSet])
      = executeRootSelectionSet schema resolvers variableValues depth parentType
          source (left ++ selectionSet) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus
        : (visitSubfields schema resolvers variableValues depth parentType source
            left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed]

theorem specExecuteRootSelectionSet_append_single_inline_none_allowed_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++ [.inlineFragment none directives selectionSet])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source (left ++ selectionSet) := by
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [.inlineFragment none directives selectionSet]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ selectionSet) := by
    rw [GraphQL.NormalForm.collectFields_append]
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      hallowed, GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {directives : List DirectiveApplication}
    (hbody
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet
              }
            initial := .object []
          })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source (left ++ [.inlineFragment none directives selectionSet])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source
          (left ++ [.inlineFragment none directives selectionSet]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
          source (left ++ [.inlineFragment none directives selectionSet])
        = executeRootSelectionSet schema resolvers variableValues depth parentType
            source (left ++ selectionSet) := by
      exact executeRootSelectionSet_append_single_inline_none_allowed_eq_body_append
        schema resolvers variableValues depth parentType source left
        selectionSet directives hallowed
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source (left ++ selectionSet) := by
      exact
        executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          hbody
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source
          (left ++ [.inlineFragment none directives selectionSet]) := by
      exact
        (specExecuteRootSelectionSet_append_single_inline_none_allowed_eq_body_append
          schema resolvers variableValues depth parentType source left
          selectionSet directives hallowed).symm

theorem stateEquivalent_of_append_single_inline_none_allowed
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {directives : List DirectiveApplication}
    (hbody
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet
              }
            initial := .object []
          })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet :=
                left ++ [.inlineFragment none directives selectionSet]
            }
          initial := .object []
        } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.inlineFragment none directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_inline_none_allowed hbody hallowed)

theorem executeRootSelectionSet_append_single_inline_some_apply_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
      = executeRootSelectionSet schema resolvers variableValues depth parentType
          source (left ++ selectionSet) := by
  unfold executeRootSelectionSet
  rw [visitSubfields_append_equivalence]
  rw [visitSubfields_append_equivalence]
  obtain ⟨fields, hfields⟩ :=
    visitSubfields_preserves_object schema resolvers variableValues depth
      parentType source left []
  cases hstatus
        : (visitSubfields schema resolvers variableValues depth parentType source
            left (.object [])).snd with
  | error errors =>
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed,
        happly]
  | ok status =>
      rcases status with ⟨_unit, errors⟩
      simp [hfields, hstatus, visitSubfields, visitSelection, hallowed,
        happly]

theorem specExecuteRootSelectionSet_append_single_inline_some_apply_eq_body_append
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (left selectionSet : List Selection)
    (typeCondition : Name) (directives : List DirectiveApplication)
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    : GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
        depth parentType source
        (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source (left ++ selectionSet) := by
  have hcollectAppend :
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) =
      GraphQL.Execution.collectFields schema variableValues parentType source
        (left ++ selectionSet) := by
    rw [GraphQL.NormalForm.collectFields_append]
    rw [GraphQL.NormalForm.collectFields_append]
    simp [GraphQL.Execution.collectFields, GraphQL.Execution.collectSelection,
      hallowed, happly, GraphQL.Execution.mergeExecutableGroups]
  simp [GraphQL.Execution.executeRootSelectionSet, hcollectAppend]

theorem executeRootSelectionSet_eq_spec_of_append_single_inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    (hbody
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet
              }
            initial := .object []
          })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    : executeRootSelectionSet schema resolvers variableValues depth parentType
        source
        (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source
          (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) := by
  calc
    executeRootSelectionSet schema resolvers variableValues depth parentType
          source (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
        = executeRootSelectionSet schema resolvers variableValues depth parentType
            source (left ++ selectionSet) := by
      exact executeRootSelectionSet_append_single_inline_some_apply_eq_body_append
        schema resolvers variableValues depth parentType source left
        selectionSet typeCondition directives hallowed happly
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source (left ++ selectionSet) := by
      exact
        executeRootSelectionSet_eq_spec_of_state_equivalent_auto_nodup
          { schema := schema
            resolvers := resolvers
            variableValues := variableValues
            depth := depth
            parentType := parentType
            source := source
            selectionSet := left ++ selectionSet }
          hbody
    _ = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues
          depth parentType source
          (left ++ [.inlineFragment (some typeCondition) directives selectionSet]) := by
      exact
        (specExecuteRootSelectionSet_append_single_inline_some_apply_eq_body_append
          schema resolvers variableValues depth parentType source left
          selectionSet typeCondition directives hallowed happly).symm

theorem stateEquivalent_of_append_single_inline_some_apply
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {depth : Nat}
    {parentType : Name} {source : ResolverValue ObjectIdentity}
    {left selectionSet : List Selection}
    {typeCondition : Name} {directives : List DirectiveApplication}
    (hbody
      : ExecutionStateEquivalent
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := left ++ selectionSet
              }
            initial := .object []
          })
    (hallowed : selectionDirectivesAllowBool variableValues directives = true)
    (happly : doesFragmentTypeApplyBool schema parentType source typeCondition = true)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet :=
                left ++ [.inlineFragment (some typeCondition) directives selectionSet]
            }
          initial := .object []
        } :=
  stateEquivalent_of_executeRootSelectionSet_eq_spec schema resolvers
    variableValues depth parentType source
    (left ++ [.inlineFragment (some typeCondition) directives selectionSet])
    (executeRootSelectionSet_eq_spec_of_append_single_inline_some_apply
      hbody hallowed happly)

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
