import GraphQL.Algorithms.ExecutionBreadth
import Tests.GraphQL.Execution

namespace GraphQL
namespace Tests
namespace ExecutionBreadth

open GraphQL.Tests.Execution

def testListObjectFieldDefinition (name typeName : Name) : FieldDefinition :=
  { name := name, outputType := .list (.named typeName), arguments := [] }

def widgetListSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [testListObjectFieldDefinition "widgets" "Widget"]
            interfaces := []
          },
        .object
          {
            name := "Widget"
            fields :=
              [
                testStringFieldDefinition "id",
                testObjectFieldDefinition "friend" "Widget"
              ]
            interfaces := []
          }
      ]
  }

def widgetListQuery : Operation :=
  {
    name := some "WidgetList"
    selectionSet :=
      [.field "widgets" "widgets" [] []
        [
          .field "id" "id" [] [] [],
          .field "friend" "friend" [] [] [.field "id" "id" [] [] []]
        ]]
  }

def duplicateWidgetListQuery : Operation :=
  {
    name := some "DuplicateWidgetList"
    selectionSet :=
      [
        .field "widgets" "widgets" [] [] [.field "id" "id" [] [] []],
        .field "widgets" "widgets" [] []
          [.field "friend" "friend" [] [] [.field "id" "id" [] [] []]]
      ]
  }

def widgetResolvers : GraphQL.Execution.Resolvers String :=
  {
    resolve :=
      fun parentType fieldName _arguments source =>
        match parentType, fieldName, source with
        | "Query", "widgets", _ =>
            some (.list [.object "Widget" "a", .object "Widget" "b"])
        | "Widget", "id", .object _ ref =>
            some (.scalar ref)
        | "Widget", "friend", .object _ "a" =>
            some (.object "Widget" "b")
        | "Widget", "friend", .object _ "b" =>
            some (.object "Widget" "a")
        | _, _, _ =>
            some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def widgetRoot : GraphQL.Execution.ResolverValue String :=
  .object "Query" "root"

def expectedWidgetListResponse : GraphQL.Execution.ResponseValue :=
  .object
    [(
      "widgets",
      .list
        [
          .object [("id", .scalar "a"), ("friend", .object [("id", .scalar "b")])],
          .object [("id", .scalar "b"), ("friend", .object [("id", .scalar "a")])]
        ]
    )]

def siblingWidgetSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                testObjectFieldDefinition "left" "Widget",
                testObjectFieldDefinition "right" "Widget"
              ]
            interfaces := []
          },
        .object
          {
            name := "Widget"
            fields := [testStringFieldDefinition "id"]
            interfaces := []
          }
      ]
  }

def siblingWidgetQuery : Operation :=
  {
    name := some "SiblingWidgets"
    selectionSet :=
      [
        .field "left" "left" [] [] [.field "id" "id" [] [] []],
        .field "right" "right" [] [] [.field "id" "id" [] [] []]
      ]
  }

def siblingWidgetResolvers : GraphQL.Execution.Resolvers String :=
  {
    resolve :=
      fun parentType fieldName _arguments _source =>
        match parentType, fieldName with
        | "Query", "left" => some (.object "Widget" "left")
        | "Query", "right" => some (.object "Widget" "right")
        | "Widget", "id" =>
            match _source with
            | .object _ ref => some (.scalar ref)
            | _ => some .null
        | _, _ => some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def expectedSiblingWidgetResponse : GraphQL.Execution.ResponseValue :=
  .object
    [
      ("left", .object [("id", .scalar "left")]),
      ("right", .object [("id", .scalar "right")])
    ]

def listCousinSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testListObjectFieldDefinition "parents" "Parent"]
            interfaces := []
          },
        .object
          {
            name := "Parent"
            fields := [testObjectFieldDefinition "child" "Widget"]
            interfaces := []
          },
        .object
          {
            name := "Widget"
            fields := [testStringFieldDefinition "id"]
            interfaces := []
          }
      ]
  }

def listCousinQuery : Operation :=
  {
    name := some "ListCousins"
    selectionSet :=
      [.field "parents" "parents" [] []
        [.field "child" "child" [] [] [.field "id" "id" [] [] []]]]
  }

def listCousinResolvers : GraphQL.Execution.Resolvers String :=
  {
    resolve :=
      fun parentType fieldName _arguments source =>
        match parentType, fieldName, source with
        | "Query", "parents", _ =>
            some (.list [.object "Parent" "p1", .object "Parent" "p2"])
        | "Parent", "child", .object _ "p1" =>
            some (.object "Widget" "w1")
        | "Parent", "child", .object _ "p2" =>
            some (.object "Widget" "w2")
        | "Widget", "id", .object _ ref =>
            some (.scalar ref)
        | _, _, _ =>
            some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def distinctRuntimeSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testListObjectFieldDefinition "nodes" "Node"]
            interfaces := []
          },
        .interface
          {
            name := "Node"
            fields := [testStringFieldDefinition "id"]
            interfaces := []
          },
        .object
          {
            name := "Alpha"
            fields :=
              [testStringFieldDefinition "id", testStringFieldDefinition "alpha"]
            interfaces := ["Node"]
          },
        .object
          {
            name := "Beta"
            fields :=
              [testStringFieldDefinition "id", testStringFieldDefinition "beta"]
            interfaces := ["Node"]
          }
      ]
  }

def distinctRuntimeQuery : Operation :=
  {
    name := some "DistinctRuntimeNodes"
    selectionSet :=
      [.field "nodes" "nodes" [] []
        [
          .inlineFragment (some "Alpha") [] [.field "alpha" "alpha" [] [] []],
          .inlineFragment (some "Beta") [] [.field "beta" "beta" [] [] []]
        ]]
  }

def distinctRuntimeResolvers : GraphQL.Execution.Resolvers String :=
  {
    resolve :=
      fun parentType fieldName _arguments source =>
        match parentType, fieldName, source with
        | "Query", "nodes", _ =>
            some (.list [.object "Alpha" "a", .object "Beta" "b"])
        | "Alpha", "alpha", .object _ ref =>
            some (.scalar s!"alpha-{ref}")
        | "Beta", "beta", .object _ ref =>
            some (.scalar s!"beta-{ref}")
        | _, _, _ =>
            some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def expectedDistinctRuntimeResponse : GraphQL.Execution.ResponseValue :=
  .object
    [(
      "nodes",
      .list [.object [("alpha", .scalar "alpha-a")], .object [("beta", .scalar "beta-b")]]
    )]

def aliasedBatchSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "widget" "Widget"]
            interfaces := []
          },
        .object
          {
            name := "Widget"
            fields :=
              [
                testObjectFieldDefinition "friend" "Widget",
                testStringFieldDefinition "id",
                testStringFieldDefinition "label"
              ]
            interfaces := []
          }
      ]
  }

def aliasedBatchQuery : Operation :=
  {
    name := some "AliasedBatch"
    selectionSet :=
      [.field "widget" "widget" [] []
        [
          .field "first" "friend" [] [] [.field "id" "id" [] [] []],
          .field "second" "friend" [] [] [.field "label" "label" [] [] []]
        ]]
  }

def aliasedBatchResolvers : GraphQL.Execution.Resolvers String :=
  {
    resolve :=
      fun parentType fieldName _arguments source =>
        match parentType, fieldName, source with
        | "Query", "widget", _ =>
            some (.object "Widget" "root-widget")
        | "Widget", "friend", .object _ ref =>
            some (.object "Widget" s!"friend-{ref}")
        | "Widget", "id", .object _ ref =>
            some (.scalar s!"id-{ref}")
        | "Widget", "label", .object _ ref =>
            some (.scalar s!"label-{ref}")
        | _, _, _ =>
            some .null
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

def expectedAliasedBatchResponse : GraphQL.Execution.ResponseValue :=
  .object
    [(
      "widget",
      .object
        [
          ("first", .object [("id", .scalar "id-friend-root-widget")]),
          ("second", .object [("label", .scalar "label-friend-root-widget")])
        ]
    )]

def rootExecutionTrace
    (schema : Schema)
    (resolvers : GraphQL.Algorithms.ExecutionBreadth.ResolverMap ObjectRef)
    (variableValues : GraphQL.Execution.VariableValues) (fuel : Nat)
    (operation : Operation) (source : GraphQL.Execution.ResolverValue ObjectRef)
    : GraphQL.Algorithms.ExecutionBreadth.ExecutionTrace :=
  let (queue, rootFrame) :=
    GraphQL.Algorithms.ExecutionBreadth.scheduleScope schema variableValues
      (operation.rootType schema) [source] operation.selectionSet []
  rootFrame
  :: GraphQL.Algorithms.ExecutionBreadth.drainLoop schema resolvers variableValues
      fuel queue

def fieldKeyMatches
    (key : GraphQL.Algorithms.ExecutionBreadth.ScheduleKey)
    (parentType fieldName : Name)
    : Bool :=
  (key.parentType == parentType)
  && (key.fieldName == fieldName)
  && GraphQL.Algorithms.argumentListEqBool key.arguments []

def fieldBindingMatches
    (binding : GraphQL.Algorithms.ExecutionBreadth.FieldBinding)
    (parentType responseName fieldName : Name)
    : Bool :=
  (binding.responseName == responseName)
  && fieldKeyMatches binding.key parentType fieldName

theorem breadthListQueryMatchesSpecSmoke
    : let spec :=
        GraphQL.Execution.executeQuery widgetListSchema widgetResolvers []
          widgetListQuery widgetRoot
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQuery widgetListSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            widgetResolvers)
          [] widgetListQuery widgetRoot
      spec.errors = breadth.errors
      ∧ responseEqBool spec.data breadth.data = true
      ∧ responseEqBool breadth.data expectedWidgetListResponse = true := by
  native_decide

theorem breadthLowFuelDivergesFromSpecSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQueryWithFuel sampleSchema sampleResolvers []
          sampleHeroQuery 1 source
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQueryWithFuel sampleSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            sampleResolvers)
          [] sampleHeroQuery 1 source
      spec.errors = breadth.errors ∧ responseEqBool spec.data breadth.data = false := by
  native_decide

def siblingTraceCoalescesCousinSegmentsBool : Bool :=
  let trace :=
    rootExecutionTrace siblingWidgetSchema
      (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
        siblingWidgetResolvers)
      ([] : GraphQL.Execution.VariableValues) 10 siblingWidgetQuery
      (GraphQL.Execution.ResolverValue.object "Query" "root")
  match trace with
  | [
    .scope [1] [rootLeftBinding, rootRightBinding],
    .field leftKey _ [("left", 1)] [.child],
    .scope [1] [leftIdBinding],
    .field rightKey _ [("right", 1)] [.child],
    .scope [1] [rightIdBinding],
    .field idKey _ [("id", 1), ("id", 1)] _
  ] =>
      fieldBindingMatches rootLeftBinding "Query" "left" "left"
      && fieldBindingMatches rootRightBinding "Query" "right" "right"
      && fieldKeyMatches leftKey "Query" "left"
      && fieldKeyMatches rightKey "Query" "right"
      && fieldBindingMatches leftIdBinding "Widget" "id" "id"
      && fieldBindingMatches rightIdBinding "Widget" "id" "id"
      && fieldKeyMatches idKey "Widget" "id"
  | _ => false

theorem siblingTraceCoalescesCousinSegmentsSmoke
    : siblingTraceCoalescesCousinSegmentsBool = true := by
  native_decide

theorem breadthSiblingCousinOrderMatchesSpecSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" "root"
      let spec :=
        GraphQL.Execution.executeQuery siblingWidgetSchema siblingWidgetResolvers []
          siblingWidgetQuery source
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQuery siblingWidgetSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            siblingWidgetResolvers)
          [] siblingWidgetQuery source
      spec.errors = breadth.errors
      ∧ responseEqBool spec.data breadth.data = true
      ∧ responseEqBool breadth.data expectedSiblingWidgetResponse = true := by
  native_decide

def listTraceCoalescesCousinSegmentsBool : Bool :=
  let trace :=
    rootExecutionTrace listCousinSchema
      (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
        listCousinResolvers)
      ([] : GraphQL.Execution.VariableValues) 10 listCousinQuery
      (GraphQL.Execution.ResolverValue.object "Query" "root")
  match trace with
  | [
    .scope [1] [parentsRootBinding],
    .field parentsKey _ [("parents", 1)] [.list [.child, .child]],
    .scope [1] [childScopeBinding],
    .scope [1] [childScopeBinding'],
    .field childKey _ [("child", 1), ("child", 1)] [.child, .child],
    .scope [1] [idScopeBinding],
    .scope [1] [idScopeBinding'],
    .field idKey _ [("id", 1), ("id", 1)] _
  ] =>
      fieldBindingMatches parentsRootBinding "Query" "parents" "parents"
      && fieldKeyMatches parentsKey "Query" "parents"
      && fieldBindingMatches childScopeBinding "Parent" "child" "child"
      && fieldBindingMatches childScopeBinding' "Parent" "child" "child"
      && fieldKeyMatches childKey "Parent" "child"
      && fieldBindingMatches idScopeBinding "Widget" "id" "id"
      && fieldBindingMatches idScopeBinding' "Widget" "id" "id"
      && fieldKeyMatches idKey "Widget" "id"
  | _ => false

theorem listTraceCoalescesCousinSegmentsSmoke
    : listTraceCoalescesCousinSegmentsBool = true := by
  native_decide

def aliasedTraceCoalescesResponseNamesBool : Bool :=
  let trace :=
    rootExecutionTrace aliasedBatchSchema
      (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
        aliasedBatchResolvers)
      ([] : GraphQL.Execution.VariableValues) 10 aliasedBatchQuery
      (GraphQL.Execution.ResolverValue.object "Query" "root")
  match trace with
  | [
    .scope [1] [widgetBinding],
    .field widgetKey _ [("widget", 1)] [.child],
    .scope [1] [firstBinding, secondBinding],
    .field friendKey _ [("first", 1), ("second", 1)] [.child, .child],
    .scope [1] [idBinding],
    .scope [1] [labelBinding],
    .field idKey _ [("id", 1)] _,
    .field labelKey _ [("label", 1)] _
  ] =>
      fieldBindingMatches widgetBinding "Query" "widget" "widget"
      && fieldKeyMatches widgetKey "Query" "widget"
      && fieldBindingMatches firstBinding "Widget" "first" "friend"
      && fieldBindingMatches secondBinding "Widget" "second" "friend"
      && fieldKeyMatches friendKey "Widget" "friend"
      && fieldBindingMatches idBinding "Widget" "id" "id"
      && fieldBindingMatches labelBinding "Widget" "label" "label"
      && fieldKeyMatches idKey "Widget" "id"
      && fieldKeyMatches labelKey "Widget" "label"
  | _ => false

theorem aliasedTraceCoalescesResponseNamesSmoke
    : aliasedTraceCoalescesResponseNamesBool = true := by
  native_decide

theorem breadthAliasedBatchMatchesSpecSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" "root"
      let spec :=
        GraphQL.Execution.executeQuery aliasedBatchSchema aliasedBatchResolvers []
          aliasedBatchQuery source
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQuery aliasedBatchSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            aliasedBatchResolvers)
          [] aliasedBatchQuery source
      spec.errors = breadth.errors
      ∧ responseEqBool spec.data breadth.data = true
      ∧ responseEqBool breadth.data expectedAliasedBatchResponse = true := by
  native_decide

theorem breadthDistinctRuntimeChildrenMatchSpecSmoke
    : let spec :=
        GraphQL.Execution.executeQuery distinctRuntimeSchema distinctRuntimeResolvers []
          distinctRuntimeQuery widgetRoot
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQuery distinctRuntimeSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            distinctRuntimeResolvers)
          [] distinctRuntimeQuery widgetRoot
      spec.errors = breadth.errors
      ∧ responseEqBool spec.data breadth.data = true
      ∧ responseEqBool breadth.data expectedDistinctRuntimeResponse = true := by
  native_decide

theorem breadthDuplicateFieldMergesSubfieldsSmoke
    : let spec :=
        GraphQL.Execution.executeQuery widgetListSchema widgetResolvers []
          duplicateWidgetListQuery widgetRoot
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQuery widgetListSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            widgetResolvers)
          [] duplicateWidgetListQuery widgetRoot
      spec.errors = breadth.errors
      ∧ responseEqBool spec.data breadth.data = true
      ∧ responseEqBool breadth.data expectedWidgetListResponse = true := by
  native_decide

theorem breadthNestedNonNullBubbleMatchesSpecSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQuery nestedNonNullSchema
          nonNullNameErrorResolvers [] sampleHeroQuery source
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQuery nestedNonNullSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            nonNullNameErrorResolvers)
          [] sampleHeroQuery source
      spec.errors = breadth.errors
      ∧ responseEqBool spec.data breadth.data = true
      ∧ responseEqBool breadth.data (.object [("mainHero", .null)]) = true := by
  native_decide

theorem breadthRootNonNullBubbleMatchesSpecSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let spec :=
        GraphQL.Execution.executeQuery rootNonNullSchema
          nonNullNameErrorResolvers [] sampleHeroQuery source
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQuery rootNonNullSchema
          (GraphQL.Algorithms.ExecutionBreadth.ResolverMap.fromSpecResolvers
            nonNullNameErrorResolvers)
          [] sampleHeroQuery source
      spec.errors = breadth.errors
      ∧ responseEqBool spec.data breadth.data = true
      ∧ responseEqBool breadth.data .null = true := by
  native_decide

def resultCountMismatchResolverMap : GraphQL.Algorithms.ExecutionBreadth.ResolverMap :=
  {
    resolve := fun _parentType _fieldName _arguments _sources => []
    resolve_argumentsEquivalent := by
      intros
      rfl
  }

theorem breadthResultCountMismatchIsFieldErrorSmoke
    : let source := GraphQL.Execution.ResolverValue.object "Query" ()
      let breadth :=
        GraphQL.Algorithms.ExecutionBreadth.executeQueryWithFuel sampleSchema
          resultCountMismatchResolverMap [] sampleHeroQuery 5 source
      breadth.errors = 1
      ∧ responseEqBool breadth.data (.object [("mainHero", .null)]) = true := by
  native_decide

theorem breadthExecutorPassesCoercedArgumentsToGivenResolver
    : responseEqBool
        (GraphQL.Algorithms.ExecutionBreadth.executeQueryWithSpecResolvers
          coercedResolverSchema resolverArgumentPresenceResolvers []
          omittedResolverArgumentOperation
          (GraphQL.Execution.ResolverValue.object "Query" ())).data
        (.object [("echo", .scalar "present")])
      = true := by
  native_decide

end ExecutionBreadth
end Tests
end GraphQL
