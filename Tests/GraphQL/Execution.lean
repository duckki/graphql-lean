import GraphQL.Algorithms.Common
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
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        some
        <| match parentType, fieldName with
            | "Query", "hero" => .object "Character" ()
            | "Character", "name" => .scalar "Leia"
            | _, _ => .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

theorem executeHeroQuerySmoke
    : responseEqBool
        (GraphQL.Execution.executeQuery sampleSchema sampleResolvers []
          sampleHeroQuery
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("mainHero", .object [("name", .scalar "Leia")])])
      = true := by
  native_decide

def sampleErrorResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "hero" => some (.object "Character" ())
        | "Character", "name" => none
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

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
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "hero" => some (.object "Character" ())
        | "Character", "name" => none
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def nonNullNameNullResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "hero" => some (.object "Character" ())
        | "Character", "name" => some .null
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

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
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "name" => some (.scalar "Query")
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

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

def nestedInputDefinition : InputValueDefinition :=
  {
    name := "leaf"
    inputType := .named "Int"
    defaultValue := some (.int 3)
  }

def nestedInputListDefinition : InputValueDefinition :=
  {
    name := "items"
    inputType := .list (.named "NestedInput")
    defaultValue := some (.list [.object []])
  }

def defaultedInputDefinition : InputValueDefinition :=
  {
    name := "nested"
    inputType := .named "NestedInput"
    defaultValue := some (.object [])
  }

def nullableFlagDefinition : InputValueDefinition :=
  {
    name := "flag"
    inputType := .named "Boolean"
    defaultValue := some (.boolean true)
  }

def resolverPayloadDefinition : InputValueDefinition :=
  {
    name := "payload"
    inputType := .named "ResolverInput"
    defaultValue := some (.object [])
  }

def coercedResolverSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .inputObject
          {
            name := "NestedInput"
            inputFields := [nestedInputDefinition]
          },
        .inputObject
          {
            name := "ResolverInput"
            inputFields :=
              [
                defaultedInputDefinition,
                nestedInputListDefinition,
                nullableFlagDefinition
              ]
          },
        .object
          {
            name := "Query"
            fields :=
              [{
                name := "echo"
                outputType := .named "String"
                arguments := [resolverPayloadDefinition]
              }]
          }
      ]
  }

def defaultedResolverPayload : InputValue :=
  .object
    [
      ("nested", .object [("leaf", .int 3)]),
      ("items", .list [.object [("leaf", .int 3)]]),
      ("flag", .boolean true)
    ]

def operationDefaultResolverPayload : InputValue :=
  .object
    [
      ("nested", .object [("leaf", .int 3)]),
      ("items", .list [.object [("leaf", .int 3)]]),
      ("flag", .boolean false)
    ]

def coercedResolverOperation : Operation :=
  {
    name := some "CoercedResolverArguments"
    variableDefinitions :=
      [{
        name := "payload"
        typeRef := .named "ResolverInput"
        defaultValue := some (.object [("flag", .boolean false), ("nested", .object [])])
      }]
    selectionSet :=
      [.field "echo" "echo" [{ name := "payload", value := .variable "payload" }] [] []]
  }

theorem coerceVariableValuesPreservesOperationDefaultSyntax
    : GraphQL.Execution.lookupVariableValue?
        (GraphQL.Execution.coerceVariableValues coercedResolverOperation [])
        "payload"
      = some (.object [("flag", .boolean false), ("nested", .object [])]) := by
  rfl

def omittedResolverArgumentOperation : Operation :=
  {
    name := some "OmittedResolverArgument"
    selectionSet := [.field "echo" "echo" [] [] []]
  }

theorem coerceArgumentValuesUsesArgumentDefaultForOmittedArgument
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema []
          [resolverPayloadDefinition] [])
        [{ name := "payload", value := defaultedResolverPayload }]
      = true := by
  native_decide

theorem coerceArgumentValuesUsesArgumentDefaultForUndefinedVariable
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema []
          [resolverPayloadDefinition]
          [{ name := "payload", value := .variable "undefined" }])
        [{ name := "payload", value := defaultedResolverPayload }]
      = true := by
  native_decide

theorem coerceArgumentValuesPreservesExplicitNull
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema []
          [resolverPayloadDefinition] [{ name := "payload", value := .null }])
        [{ name := "payload", value := .null }]
      = true := by
  native_decide

theorem coerceArgumentValuesUsesOperationDefaultBeforeArgumentDefault
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema
          (GraphQL.Execution.coerceVariableValues coercedResolverOperation [])
          [resolverPayloadDefinition]
          [{ name := "payload", value := .variable "payload" }])
        [{ name := "payload", value := operationDefaultResolverPayload }]
      = true := by
  native_decide

theorem coerceArgumentValuesUsesSuppliedNullBeforeOperationAndArgumentDefaults
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema
          (GraphQL.Execution.coerceVariableValues coercedResolverOperation
            [("payload", .null)])
          [resolverPayloadDefinition]
          [{ name := "payload", value := .variable "payload" }])
        [{ name := "payload", value := .null }]
      = true := by
  native_decide

theorem coerceArgumentValuesHandlesMissingUndefinedNullAndSuppliedObjectFields
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema []
          [resolverPayloadDefinition]
          [{
            name := "payload"
            value :=
              .object
                [
                  ("nested", .object [("leaf", .int 9)]),
                  ("items", .variable "undefined"),
                  ("flag", .null)
                ]
          }])
        [{
          name := "payload"
          value :=
            .object
              [
                ("nested", .object [("leaf", .int 9)]),
                ("items", .list [.object [("leaf", .int 3)]]),
                ("flag", .null)
              ]
        }]
      = true := by
  native_decide

theorem coerceArgumentValuesUsesSchemaOrderWithoutCanonicalizingObjectFields
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema []
          [resolverPayloadDefinition]
          [{
            name := "payload"
            value :=
              .object
                [
                  ("flag", .boolean true),
                  ("items", .list [.object [("leaf", .int 3)]]),
                  ("nested", .object [("leaf", .int 3)])
                ]
          }])
        [{ name := "payload", value := defaultedResolverPayload }]
      = true := by
  native_decide

theorem mergeCompatibleArgumentOrdersCoerceToTheSameResolverArguments
    : GraphQL.Algorithms.argumentListEqBool
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema []
          [
            { name := "first", inputType := .named "Int" },
            { name := "second", inputType := .named "Int" }
          ]
          [{ name := "first", value := .int 1 }, { name := "second", value := .int 2 }])
        (GraphQL.Execution.coerceArgumentValues coercedResolverSchema []
          [
            { name := "first", inputType := .named "Int" },
            { name := "second", inputType := .named "Int" }
          ]
          [{ name := "second", value := .int 2 }, { name := "first", value := .int 1 }])
      = true := by
  native_decide

def resolverArgumentPresenceResolvers : GraphQL.Execution.Resolvers :=
  {
    resolve :=
      fun parentType fieldName arguments _source =>
        match parentType, fieldName, arguments with
        | "Query", "echo", [] => some (.scalar "missing")
        | "Query", "echo", _ :: _ => some (.scalar "present")
        | _, _, _ => some .null
    resolve_argumentsEquivalent := by
      intro parentType fieldName firstArguments laterArguments source hequivalent
      cases firstArguments with
      | nil =>
          cases laterArguments with
          | nil => rfl
          | cons argument arguments =>
              have hmember := hequivalent.2 argument (by simp)
              simp at hmember
      | cons argument arguments =>
          cases laterArguments with
          | nil =>
              have hmember := hequivalent.1 argument (by simp)
              simp at hmember
          | cons laterArgument laterArguments =>
              by_cases hparent : parentType = "Query"
              · subst parentType
                by_cases hfield : fieldName = "echo"
                · subst fieldName
                  rfl
                · simp [hfield]
              · simp [hparent]
  }

theorem specExecutorPassesCoercedArgumentsToGivenResolver
    : responseEqBool
        (GraphQL.Execution.executeQuery coercedResolverSchema
          resolverArgumentPresenceResolvers [] omittedResolverArgumentOperation
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("echo", .scalar "present")])
      = true := by
  native_decide

end Execution
end Tests
end GraphQL
