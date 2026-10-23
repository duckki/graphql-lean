import Proofs.GraphQL.IncrementalDelivery.Correctness.ExecutedScopes
import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupScopeOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupProducerOrigins
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryOutcomeExistence
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedMixedOwners
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Notice scopes can be broader than their introducing task's data attachment. -/

namespace GraphQL.IncrementalDelivery.Tests.ScopeMetadata
open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics

private def nestedSchema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          { name := "Query", fields := [{ name := "x", outputType := .named "X" }] },
        .object
          {
            name := "X",
            fields :=
              [
                { name := "w", outputType := .named "X" },
                { name := "a", outputType := .named "String" },
                { name := "b", outputType := .named "String" }
              ]
          }
      ]
  }

private def nestedResolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ field _ _ =>
        if field = "x" ∨ field = "w" then some (.object "X" 1) else some (.scalar field),
    resolve_argumentsEquivalent := by intros; rfl
  }

private def selections : List Selection :=
  [
    field "x" [field "a"],
    defer
      [
        field "x" [field "w" [field "a"]],
        defer [field "x" [field "w" [field "b"]]] (some "D")
      ]
      (some "P")
  ]

private def completed :=
  ((executeRootSelectionSetCore nestedSchema nestedResolvers [] 30 "Query"
      (.object "Query" 0) selections).run
    0).1

private def parent : DeliveryNode := { ref := 0, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 1, path := [], label := some (.string "D") }
private def parentAddress : Address := [0, 0, 1, 0]
private def childAddress : Address := parentAddress ++ [0, 0, 1, 0]

private def parentResult : Result (List (Name × ResponseValue)) :=
  .ok ([("w", .object [("a", .scalar "a")])], 0)

private def childResult : Result (List (Name × ResponseValue)) :=
  .ok ([("b", .scalar "b")], 0)

private def childWork : Work :=
  .executionGroup [⟨child, [parent]⟩] [.field "x", .field "w"] { result := childResult }
    (.combine .empty .empty)

private def parentChildren : Work :=
  .combine
    (.combine (.combine .empty .empty) (.declareGroups [] (.combine childWork .empty)))
    .empty

private theorem parent_task
    : TaskAt completed.work (.executionGroup parentAddress) [0]
        none (.object [.field "x"] parentResult) := by
  refine ⟨[⟨parent, []⟩], [.field "x"], { result := parentResult }, parentChildren, [], ?_, rfl, rfl⟩
  cbv

private theorem child_task
    : TaskAt completed.work (.executionGroup childAddress) [1]
        (some (.executionGroup parentAddress))
        (.object [.field "x", .field "w"] childResult) := by
  refine ⟨[⟨child, [parent]⟩], [.field "x", .field "w"], { result := childResult },
    .combine .empty .empty, [0], ?_, rfl, rfl⟩
  cbv

private theorem child_node
    : NodeAt completed.work child .group [0] (some (.executionGroup parentAddress)) := by
  refine ⟨
    childAddress,
    [⟨child, [parent]⟩],
    [.field "x", .field "w"],
    { result := childResult },
    .combine .empty .empty,
    [0],
    ⟨child, [parent]⟩,
    ?_,
    by simp,
    rfl,
    rfl
  ⟩
  cbv

/-- This generated broad-scope child is introduced beneath a narrower task attachment.
Witness: the actual parent and child descriptors, not an arbitrary raw work tree.
-/
theorem introducing_attachment_is_narrower
    : NodeAt completed.work child .group [0] (some (.executionGroup parentAddress))
      ∧ TaskAt completed.work (.executionGroup parentAddress) [0] none
          (.object [.field "x"] parentResult)
      ∧ ¬([.field "x"] : ResponsePath).IsPrefix child.path :=
  ⟨child_node, parent_task, by decide⟩

/-- Actual execution certifies scopes despite the narrower introducing attachment.
Witness: the general mutual execution proof; P's notice scope covers D's notice scope.
-/
theorem execution_scopes : Correctness.ScopeMetadata.Under [] completed :=
  Correctness.ScopeMetadata.executeRootSelectionSetCore_scopes nestedSchema
    nestedResolvers [] 30 "Query" (.object "Query" 0) selections 0

/-- The same generated work satisfies the correct owner-scope origin certificate.
Witness: the unconditional root-execution theorem, not a fixture-specific origin premise.
-/
theorem execution_scope_origins : GroupScopeOrigins completed.work :=
  executeRoot_groupScopeOrigins nestedSchema nestedResolvers [] 30 "Query"
    (.object "Query" 0) selections

/-- The stronger introducing-payload certificate does not hold for all generated work.
Witness: the only D descriptor has the narrower P producer; no alternate D origin can
repair the mismatch. This refutes a proof helper, not the public queue contract.
-/
theorem payload_origins_too_strong : ¬GroupProducerOrigins completed.work := by
  intro origins
  obtain ⟨origin, dependencies, birth, known, same, supported⟩ := origins _ _ _ child_node
  obtain ⟨paths, coherent⟩ := MixedOwnerPaths.executeRoot_owners nestedSchema nestedResolvers
    [] 30 "Query" (.object "Query" 0) selections 0
  have scope : origin.path = child.path := workAt_same_path coherent known child_node same
  obtain ⟨address, groups, path, result, children, enclosing, group, located, member,
    nodeEq, _⟩ := known
  have task := TaskAt.executionGroup located
  have contributes : origin.ref ∈ groups.map (fun group => group.node.ref) :=
    nodeEq ▸ List.mem_map.mpr ⟨group, member, rfl⟩
  have inventory := task.observationToken
  have tokens : observationTokens [] completed.work =
      [.inl (.executionGroup parentAddress), .inr 0,
        .inl (.executionGroup childAddress), .inr 1] := by cbv
  rw [tokens] at inventory
  have either : address = parentAddress ∨ address = childAddress := by
    simpa using inventory
  rcases either with rfl | rfl
  · have owners := (task.unique parent_task).1
    rw [same, owners] at contributes
    simp [child] at contributes
  · have producer := (task.unique child_task).2.1
    rcases supported with root | ⟨source, owners, ancestor, payload, ref, sourceEq,
      sourceTask, _, _, below⟩
    · cases root.symm.trans producer
    · have sourceSame : source = .executionGroup parentAddress :=
        Option.some.inj (sourceEq.symm.trans producer)
      subst source
      have payloadSame := (sourceTask.unique parent_task).2.2
      rw [payloadSame, scope] at below
      exact (by decide : ¬([.field "x"] : ResponsePath).IsPrefix child.path) below

/-- Stream-item defer scopes also satisfy the same general execution certificate.
Witness: zero-initial-count streaming resets inherited defer context for each item.
-/
theorem streamed_scopes
    : Correctness.ScopeMetadata.Under []
        ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
            [field "users" [defer [field "name"]]
              [.stream (.boolean true) none (.int 0)]]).run
          0).1 :=
  Correctness.ScopeMetadata.executeRootSelectionSetCore_scopes schema resolvers [] 30
    "Query" (.object "Query" 0) _ 0

/-- Broader inherited notice scopes do not prevent complete finite execution.
Witness: unconditional generated-work progress uses owner scopes rather than the refuted
producer-payload certificate; the nonempty work tree is computed from this actual query.
-/
theorem execution_completeRun : ∃ history, AdmissibleRun completed.work history := by
  apply executeRoot_completeRun_exists nestedSchema nestedResolvers [] 30 "Query"
    (.object "Query" 0) selections
  cbv

#print axioms execution_completeRun
#print axioms Explains.failed_group_scope_reported
#print axioms Explains.cancelled_reported_of_scope_origins
#print axioms snapshot_cancelled_owner_scope_reported_below
#print axioms execution_scopes
#print axioms execution_scope_origins
#print axioms executeRoot_groupScopeOrigins
#print axioms payload_origins_too_strong
#print axioms streamed_scopes
#print axioms Correctness.ScopeMetadata.executeRootSelectionSetCore_scopes

end GraphQL.IncrementalDelivery.Tests.ScopeMetadata
