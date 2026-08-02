import GraphQL.Theories.ResponseShape
import Proofs.GraphQL.Theories.ResponseShape.Validity
import Tests.GraphQL.Theories.NormalForm.Common

namespace GraphQL
namespace Tests
namespace ResponseShape

open GraphQL.ResponseShape

theorem clauseValiditySmoke :
    ({ literals := [] } : Clause).Valid []
    ∧ ({ literals := [("x", true)] } : Clause).Valid ["x", "y"]
    ∧ ({ literals := [("x", false), ("y", true)] } : Clause).CompleteMinterm
        ["x", "y"]
    ∧ ¬({ literals := [("x", true), ("x", false)] } : Clause).Valid
        ["x", "y"]
    ∧ ¬({ literals := [("y", true), ("x", false)] } : Clause).Valid
        ["x", "y"] := by
  native_decide

theorem groundSetValiditySmoke :
    GroundSet.Valid NormalForm.groundTypingSchema "Character" ["Human"]
    ∧ ¬GroundSet.Valid NormalForm.groundTypingSchema "Character" []
    ∧ ¬GroundSet.Valid
        NormalForm.groundTypingSchema "Character" ["Character"]
    ∧ ¬GroundSet.Valid NormalForm.groundTypingSchema "Character" ["Query"] := by
  native_decide

def reorderedObjectArgumentsLeft : List Argument :=
  [
    {
      name := "filter"
      value :=
        .object
          [
            ("first", .int 1),
            ("second", .string "sample")
          ]
    }
  ]

def reorderedObjectArgumentsRight : List Argument :=
  [
    {
      name := "filter"
      value :=
        .object
          [
            ("second", .string "sample"),
            ("first", .int 1)
          ]
    }
  ]

theorem semanticArgumentEquivalenceIgnoresObjectFieldOrder :
    argumentsEquivalentBool
        reorderedObjectArgumentsLeft reorderedObjectArgumentsRight := by
  native_decide

def semanticArgumentFirst : Argument :=
  { name := "first", value := .int 1 }

def semanticArgumentSecond : Argument :=
  { name := "second", value := .string "sample" }

def semanticArgumentFirstWithDifferentValue : Argument :=
  { name := "first", value := .int 2 }

theorem semanticArgumentEquivalenceIgnoresArgumentOrder
    : argumentsEquivalentBool
        [semanticArgumentFirst, semanticArgumentSecond]
        [semanticArgumentSecond, semanticArgumentFirst]
      ∧ Argument.argumentsEquivalent
          [semanticArgumentFirst, semanticArgumentSecond]
          [semanticArgumentSecond, semanticArgumentFirst] := by
  rw [← argumentsEquivalentBool_iff]
  decide

theorem semanticArgumentEquivalenceIgnoresMultiplicity
    : argumentsEquivalentBool
        [semanticArgumentFirst, semanticArgumentFirst]
        [semanticArgumentFirst]
      ∧ Argument.argumentsEquivalent
          [semanticArgumentFirst, semanticArgumentFirst]
          [semanticArgumentFirst] := by
  rw [← argumentsEquivalentBool_iff]
  decide

theorem semanticArgumentEquivalenceRejectsDifferentValues
    : argumentsEquivalentBool
          [semanticArgumentFirst]
          [semanticArgumentFirstWithDifferentValue]
        = false
      ∧ ¬Argument.argumentsEquivalent
          [semanticArgumentFirst]
          [semanticArgumentFirstWithDifferentValue] := by
  rw [← argumentsEquivalentBool_iff]
  decide

def validitySchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields :=
              [
                { name := "left", outputType := .named "String" },
                { name := "right", outputType := .named "String" }
              ]
          },
        .object
          {
            name := "Other"
            fields := []
          }
      ]
  }

def ambiguousShape : OperationShape :=
  {
    operationType := .query
    rootType := "Query"
    boolSupport := []
    root :=
      .object
        [
          .mk "value"
            [
              .mk ["Query"]
                [
                  .mk { literals := [] }
                    {
                      fieldName := "left"
                      arguments := []
                      outputType := .named "String"
                    }
                    none
                ],
              .mk ["Query"]
                [
                  .mk { literals := [] }
                    {
                      fieldName := "right"
                      arguments := []
                      outputType := .named "String"
                    }
                    none
                ]
            ]
        ]
  }

theorem incompatibleActiveDefinitionsAreNotWellFormed :
    ¬ambiguousShape.WellFormed validitySchema := by
  native_decide

def wrongRootShape : OperationShape :=
  {
    operationType := .query
    rootType := "Other"
    boolSupport := []
    root := .object []
  }

theorem operationShapeRootMatchesOperationType :
    ¬wrongRootShape.WellFormed validitySchema := by
  native_decide

def partialClauseShape : OperationShape :=
  {
    operationType := .query
    rootType := "Query"
    boolSupport := ["x", "y"]
    root :=
      .object
        [
          .mk "value"
            [
              .mk ["Query"]
                [
                  .mk { literals := [("x", true)] }
                    {
                      fieldName := "left"
                      arguments := []
                      outputType := .named "String"
                    }
                    none
                ]
            ]
        ]
  }

theorem partialClausesAreValidButNotFullMinterms :
    partialClauseShape.WellFormed validitySchema
    ∧ ¬partialClauseShape.FullMinterm := by
  native_decide

end ResponseShape
end Tests
end GraphQL
