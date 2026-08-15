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
    (parentType responseName fieldName : Name)
    : Bool :=
  (key.parentType == parentType)
  && (key.responseName == responseName)
  && (key.fieldName == fieldName)
  && GraphQL.Algorithms.argumentListEqBool key.arguments []

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
    .scope [1] [rootLeftKey, rootRightKey],
    .field leftKey _ [1] [.child],
    .scope [1] [leftIdKey],
    .field rightKey _ [1] [.child],
    .scope [1] [rightIdKey],
    .field idKey _ [1, 1] _
  ] =>
      fieldKeyMatches rootLeftKey "Query" "left" "left"
      && fieldKeyMatches rootRightKey "Query" "right" "right"
      && fieldKeyMatches leftKey "Query" "left" "left"
      && fieldKeyMatches rightKey "Query" "right" "right"
      && fieldKeyMatches leftIdKey "Widget" "id" "id"
      && fieldKeyMatches rightIdKey "Widget" "id" "id"
      && fieldKeyMatches idKey "Widget" "id" "id"
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
    .scope [1] [parentsRootKey],
    .field parentsKey _ [1] [.list [.child, .child]],
    .scope [1] [childScopeKey],
    .scope [1] [childScopeKey'],
    .field childKey _ [1, 1] [.child, .child],
    .scope [1] [idScopeKey],
    .scope [1] [idScopeKey'],
    .field idKey _ [1, 1] _
  ] =>
      fieldKeyMatches parentsRootKey "Query" "parents" "parents"
      && fieldKeyMatches parentsKey "Query" "parents" "parents"
      && fieldKeyMatches childScopeKey "Parent" "child" "child"
      && fieldKeyMatches childScopeKey' "Parent" "child" "child"
      && fieldKeyMatches childKey "Parent" "child" "child"
      && fieldKeyMatches idScopeKey "Widget" "id" "id"
      && fieldKeyMatches idScopeKey' "Widget" "id" "id"
      && fieldKeyMatches idKey "Widget" "id" "id"
  | _ => false

theorem listTraceCoalescesCousinSegmentsSmoke
    : listTraceCoalescesCousinSegmentsBool = true := by
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

end ExecutionBreadth
end Tests
end GraphQL
