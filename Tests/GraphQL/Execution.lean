import GraphQL.Execution

namespace GraphQL
namespace Tests
namespace Execution

#check GraphQL.Execution.selectionSetResultToResponse

def genericUnitObject : GraphQL.Execution.ResolverValue :=
  .object "Query" ()

theorem genericUnitObjectSmoke
    : genericUnitObject = GraphQL.Execution.ResolverValue.object "Query" () := by
  rfl

def objectConstructorUsesConcreteRef : PUnit -> GraphQL.Execution.ResolverValue PUnit :=
  GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query"

mutual
  def responseEqBool
      : GraphQL.Execution.ResponseValue -> GraphQL.Execution.ResponseValue -> Bool
    | .null, .null => true
    | .scalar left, .scalar right => left == right
    | .object left, .object right => responseFieldsEqBool left right
    | .list left, .list right => responseListEqBool left right
    | _, _ => false

  def responseListEqBool
      : List GraphQL.Execution.ResponseValue -> List GraphQL.Execution.ResponseValue
        -> Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        responseEqBool left right && responseListEqBool lefts rights
    | _, _ => false

  def responseFieldsEqBool
      : List (Name × GraphQL.Execution.ResponseValue)
        -> List (Name × GraphQL.Execution.ResponseValue) -> Bool
    | [], [] => true
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        (leftName == rightName)
        && responseEqBool leftValue rightValue
        && responseFieldsEqBool lefts rights
    | _, _ => false
end

def testStringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .named "String", arguments := [] }

def testNonNullStringFieldDefinition (name : Name) : FieldDefinition :=
  { name := name, outputType := .nonNull (.named "String"), arguments := [] }

def testObjectFieldDefinition
    (name typeName : Name) (arguments : List InputValueDefinition := [])
    : FieldDefinition :=
  { name := name, outputType := .named typeName, arguments := arguments }

def testNonNullObjectFieldDefinition
    (name typeName : Name) (arguments : List InputValueDefinition := [])
    : FieldDefinition :=
  { name := name, outputType := .nonNull (.named typeName), arguments := arguments }

def testEpisodeArgumentDefinition : InputValueDefinition :=
  { name := "episode", inputType := .named "Episode" }

def sampleSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .enum { name := "Episode", values := ["NEWHOPE"] },
        .object
          {
            name := "Query"
            fields :=
              [
                testObjectFieldDefinition "hero" "Character"
                  [testEpisodeArgumentDefinition],
                testStringFieldDefinition "name",
                { name := "age", outputType := .named "Int" }
              ]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [
                testStringFieldDefinition "name",
                testObjectFieldDefinition "friends" "Character"
              ]
            interfaces := []
          }
      ]
  }

def sampleHeroQuery : Operation :=
  {
    name := some "HeroName"
    selectionSet :=
      [.field "mainHero" "hero" [] [] [.field "name" "name" [] [] []]]
  }

def sampleResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      some <|
        match parentType, fieldName with
        | "Query", "hero" => .object "Character" ()
        | "Character", "name" => .scalar "Leia"
        | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem executeHeroQuerySmoke
    : responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema sampleResolvers []
          sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("mainHero", .object [("name", .scalar "Leia")])])
      = true := by
  native_decide

def sampleErrorResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => none
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem executeHeroQueryErrorCountSmoke
    : let response :=
        GraphQL.Execution.executeQuery sampleSchema sampleErrorResolvers []
          sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1
      ∧ responseEqBool response.data (.object [("mainHero", .object [("name", .null)])])
        = true := by
  native_decide

def nestedNonNullSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [testObjectFieldDefinition "hero" "Character"]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [testNonNullStringFieldDefinition "name"]
            interfaces := []
          }
      ]
  }

def rootNonNullSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [testNonNullObjectFieldDefinition "hero" "Character"]
            interfaces := []
          },
        .object
          {
            name := "Character"
            fields :=
              [testNonNullStringFieldDefinition "name"]
            interfaces := []
          }
      ]
  }

def nonNullNameErrorResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => none
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

def nonNullNameNullResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "hero" => some (.object "Character" ())
      | "Character", "name" => some .null
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem executeNestedNonNullBubblesToNullableParentSmoke
    : let response :=
        GraphQL.Execution.executeQuery nestedNonNullSchema
          nonNullNameErrorResolvers [] sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1
      ∧ responseEqBool response.data (.object [("mainHero", .null)]) = true := by
  native_decide

theorem executeNestedNonNullBubblesToRootSmoke
    : let response :=
        GraphQL.Execution.executeQuery rootNonNullSchema
          nonNullNameErrorResolvers [] sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1 ∧ responseEqBool response.data .null = true := by
  native_decide

theorem executeExplicitNullForNonNullFieldCountsErrorSmoke
    : let response :=
        GraphQL.Execution.executeQuery nestedNonNullSchema
          nonNullNameNullResolvers [] sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())
      response.errors = 1
      ∧ responseEqBool response.data (.object [("mainHero", .null)]) = true := by
  native_decide

def profileStatusSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                testObjectFieldDefinition "profile" "Profile",
                {
                  name := "profiles"
                  outputType := .list (.named "Profile")
                  arguments := []
                }
              ]
            interfaces := []
          },
        .object
          {
            name := "Profile"
            fields :=
              [
                testNonNullStringFieldDefinition "id",
                testNonNullStringFieldDefinition "status"
              ]
            interfaces := []
          }
      ]
  }

def profileIdQuery : Operation :=
  {
    name := some "ProfileId"
    selectionSet :=
      [.field "profile" "profile" [] [] [.field "id" "id" [] [] []]]
  }

def profileIdAndStatusQuery : Operation :=
  {
    name := some "ProfileIdAndStatus"
    selectionSet :=
      [
        .field "profile" "profile" [] []
          [
            .field "id" "id" [] [] [],
            .field "status" "status" [] [] []
          ]
      ]
  }

def profileListIdQuery : Operation :=
  {
    name := some "ProfileListId"
    selectionSet :=
      [.field "profiles" "profiles" [] [] [.field "id" "id" [] [] []]]
  }

def profileListIdAndStatusQuery : Operation :=
  {
    name := some "ProfileListIdAndStatus"
    selectionSet :=
      [
        .field "profiles" "profiles" [] []
          [
            .field "id" "id" [] [] [],
            .field "status" "status" [] [] []
          ]
      ]
  }

def profileStatusResolvers : GraphQL.Execution.Resolvers String :=
  { resolve := fun parentType fieldName _arguments source =>
      match parentType, fieldName, source with
      | "Query", "profile", .object _ "root" =>
          some (.object "Profile" "pending")
      | "Query", "profiles", .object _ "root" =>
          some (.list [.object "Profile" "pending", .object "Profile" "ready"])
      | "Profile", "id", .object _ "pending" => some (.scalar "profile-pending")
      | "Profile", "id", .object _ "ready" => some (.scalar "profile-ready")
      | "Profile", "status", .object _ "pending" => none
      | "Profile", "status", .object _ "ready" => some (.scalar "READY")
      | _, _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

def profileStatusRoot : GraphQL.Execution.ResolverValue String :=
  .object "Query" "root"

-- Spec 6.4.4: an error completing a non-null child bubbles through its nullable
-- object field, even though selecting only the unaffected child succeeds.
theorem executeExtraNonNullProfileFieldBubblesNullableParent
    : let baseline :=
        GraphQL.Execution.executeQuery profileStatusSchema profileStatusResolvers []
          profileIdQuery profileStatusRoot
      let withStatus :=
        GraphQL.Execution.executeQuery profileStatusSchema profileStatusResolvers []
          profileIdAndStatusQuery profileStatusRoot
      baseline.errors = 0
      ∧ responseEqBool baseline.data
          (.object
            [("profile", .object [("id", .scalar "profile-pending")])])
        = true
      ∧ withStatus.errors = 1
      ∧ responseEqBool withStatus.data (.object [("profile", .null)]) = true := by
  native_decide

-- Spec 6.4.4: nullable list items catch non-null bubbling independently, so an
-- error in one object does not null a successfully completed sibling item.
theorem executeExtraNonNullProfileFieldNullsOnlyFailingListItem
    : let baseline :=
        GraphQL.Execution.executeQuery profileStatusSchema profileStatusResolvers []
          profileListIdQuery profileStatusRoot
      let withStatus :=
        GraphQL.Execution.executeQuery profileStatusSchema profileStatusResolvers []
          profileListIdAndStatusQuery profileStatusRoot
      baseline.errors = 0
      ∧ responseEqBool baseline.data
          (.object
            [
              (
                "profiles",
                .list
                  [
                    .object [("id", .scalar "profile-pending")],
                    .object [("id", .scalar "profile-ready")]
                  ]
              )
            ])
        = true
      ∧ withStatus.errors = 1
      ∧ responseEqBool withStatus.data
          (.object
            [
              (
                "profiles",
                .list
                  [
                    .null,
                    .object
                      [
                        ("id", .scalar "profile-ready"),
                        ("status", .scalar "READY")
                      ]
                  ]
              )
            ])
        = true := by
  native_decide

theorem collectSubfieldsMatchesGroupedSelections
    (field : GraphQL.Execution.ExecutableField)
    (fields : List GraphQL.Execution.ExecutableField)
    : GraphQL.Execution.collectSubfields sampleSchema [] "Query"
        (GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query" ())
        (field :: fields)
      = GraphQL.Execution.mergeExecutableGroups
          (GraphQL.Execution.collectFields sampleSchema [] "Query"
            (GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query" ())
            field.selectionSet)
          (GraphQL.Execution.collectSubfields sampleSchema [] "Query"
            (GraphQL.Execution.ResolverValue.object (ObjectRef := PUnit) "Query" ())
            fields) := by
  rfl

theorem executeRootSelectionSetSmoke
    : (match GraphQL.Execution.executeRootSelectionSet sampleSchema sampleResolvers []
              (GraphQL.Execution.executeQueryFuelBound sampleHeroQuery)
              "Query"
              (GraphQL.Execution.ResolverValue.object "Query" ())
              sampleHeroQuery.selectionSet with
        | .ok (fields, _errors) =>
            responseEqBool (.object fields)
              (.object [("mainHero", .object [("name", .scalar "Leia")])])
        | .error _errors => false)
      = true := by
  native_decide

def variableDefaultQuery : Operation :=
  {
    name := some "VariableDefault"
    variableDefinitions :=
      [{
        name := "includeName"
        typeRef := .named "Boolean"
        defaultValue := some (.boolean true)
      }]
    selectionSet :=
      [.field "name" "name" [] [.include (.variable "includeName")] []]
  }

def nullVariableDefaultQuery : Operation :=
  {
    variableDefaultQuery with
      variableDefinitions :=
        [{
          name := "includeName"
          typeRef := .named "Boolean"
          defaultValue := some .null
        }]
  }

def skipVariableDefaultQuery : Operation :=
  {
    variableDefaultQuery with
      name := some "SkipVariableDefault"
      selectionSet :=
        [.field "name" "name" [] [.skip (.variable "includeName")] []]
  }

def rootNameResolvers : GraphQL.Execution.Resolvers :=
  { resolve := fun parentType fieldName _arguments _source =>
      match parentType, fieldName with
      | "Query", "name" => some (.scalar "Query")
      | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl }

theorem coerceVariableValuesUsesMissingDefault
    : GraphQL.Execution.lookupVariableValue?
        (GraphQL.Execution.coerceVariableValues variableDefaultQuery []) "includeName"
      = some (.boolean true) := by
  rfl

theorem coerceVariableValuesKeepsExplicitValue
    : GraphQL.Execution.lookupVariableValue?
        (GraphQL.Execution.coerceVariableValues variableDefaultQuery
          [("includeName", .boolean false)])
        "includeName"
      = some (.boolean false) := by
  rfl

theorem coerceVariableValuesKeepsExplicitNull
    : GraphQL.Execution.lookupVariableValue?
        (GraphQL.Execution.coerceVariableValues variableDefaultQuery
          [("includeName", .null)])
        "includeName"
      = some .null := by
  rfl

theorem coerceVariableValuesIncludesNullDefault
    : GraphQL.Execution.lookupVariableValue?
        (GraphQL.Execution.coerceVariableValues nullVariableDefaultQuery [])
        "includeName"
      = some .null := by
  rfl

theorem executeQueryUsesVariableDefault
    : responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema rootNameResolvers []
          variableDefaultQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("name", .scalar "Query")])
      = true := by
  native_decide

theorem executeQueryUsesSkipVariableDefault
    : responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema rootNameResolvers []
          skipVariableDefaultQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [])
      = true := by
  native_decide

theorem executeQueryExplicitVariableOverridesDefault
    : responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema rootNameResolvers
          [("includeName", .boolean false)]
          variableDefaultQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [])
      = true := by
  native_decide

theorem executeQueryExplicitNullDoesNotUseDefault
    : responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema rootNameResolvers
          [("includeName", .null)]
          variableDefaultQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [])
      = true := by
  native_decide

end Execution
end Tests
end GraphQL
