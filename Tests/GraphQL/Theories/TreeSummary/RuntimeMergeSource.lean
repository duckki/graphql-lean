import Proofs.GraphQL.Theories.TreeSummary.ExecutionValidity
import Proofs.GraphQL.Theories.TreeSummary.MaxResponseSize
import Tests.GraphQL.Validation.FieldMerge

namespace GraphQL.Tests.TreeSummary.RuntimeMergeSource

open GraphQL.Execution
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
open GraphQL.TreeSummary
open GraphQL.Tests.Validation.FieldMerge

private def queryObject : ObjectType :=
  { name := "Query", fields := [{ name := "user", outputType := .named "User" }] }

private def userFields : List ExecutableField :=
  [
    { fieldName := "user", arguments := [], selectionSet := directName },
    { fieldName := "user", arguments := [], selectionSet := fragmentName }
  ]

theorem declaredReturnScope_groupsValid
    (hschema : SchemaWellFormedness.schemaWellFormed returnScopeSchema)
    : ExecutableGroupsValid returnScopeSchema "Query"
        (collectFields returnScopeSchema [] "Query" (.object "Query" ())
          returnScopeQuery.selectionSet) := by
  have hobject : returnScopeSchema.objectType "Query" := ⟨queryObject, rfl⟩
  have hvalid := Validation.operationDefinitionValid_selectionSetValid returnScopeQuery_valid
  apply collectFields_executableGroupsValid returnScopeSchema [] "Query" ()
    returnScopeQuery.selectionSet hschema hobject
  · exact NormalForm.selectionSetSemanticsReady_of_selectionSetValid_object
      returnScopeSchema [] "Query" hschema hobject returnScopeQuery.selectionSet hvalid
  · exact NormalForm.runtimeMergeSource_of_valid returnScopeSchema [] hobject (by decide)
      hvalid returnScopeQuery_canMerge
  · exact Execution.selectionSetArgumentsNodup_of_selectionSetValid hvalid

theorem declaredReturnScope_childGroupsValid
    (hschema : SchemaWellFormedness.schemaWellFormed returnScopeSchema)
    : NormalForm.runtimeMergeSource returnScopeSchema "User"
        (mergedFieldSelectionSet userFields)
      ∧ ExecutableGroupsValid returnScopeSchema "User"
          (collectFields returnScopeSchema [] "User" (.object "User" ())
            (mergedFieldSelectionSet userFields)) := by
  have hgroup : ("user", userFields) ∈ collectFields returnScopeSchema [] "Query"
      (.object "Query" ()) returnScopeQuery.selectionSet := by
    change ("user", userFields) ∈ [("user", userFields)]
    exact List.mem_singleton_self _
  have hvalid := declaredReturnScope_groupsValid hschema "user" userFields hgroup
  have hfirst : { fieldName := "user", arguments := [], selectionSet := directName }
      ∈ userFields := by simp [userFields]
  rcases hvalid.childrenValid _ { name := "user", outputType := .named "User" } "User"
      hfirst rfl (by decide) with ⟨hobject, hready, hsource⟩
  exact ⟨hsource, collectFields_executableGroupsValid returnScopeSchema [] "User" ()
    (mergedFieldSelectionSet userFields) hschema hobject hready hsource
    (selectionSetArgumentsNodup_mergedFieldSelectionSet userFields
      hvalid.childArgumentsNodup)⟩

theorem declaredReturnScope_estimates
    : MaxResponseSize.ExactCases.estimateOperation returnScopeSchema 1 returnScopeQuery
        = 2
      ∧ MaxResponseSize.Syntactic.estimateOperation returnScopeSchema 1 returnScopeQuery
        = 2 := by
  native_decide

end GraphQL.Tests.TreeSummary.RuntimeMergeSource
