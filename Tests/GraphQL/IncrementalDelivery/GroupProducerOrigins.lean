import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupProducerOrigins
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedMixedOwners
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedRefRoles
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Generated deferred groups below cancelled stream producers retain structural origins. -/

namespace GraphQL.IncrementalDelivery.Tests.GroupProducerOrigins
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

private def selections : List Selection :=
  [
    defer [field "required"] (some "R"),
    defer
      [
        field "required",
        field "users" [defer [field "name"] (some "C")]
          [.stream (.boolean true) none (.int 0)]
      ]
      (some "P")
  ]

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1

private def root (ref : NodeRef) (label : String) : DeliveryNode :=
  { ref, path := [], label := some (.string label) }

private def stream : DeliveryNode := { ref := 2, path := [.field "users"] }

private def child (ref index : Nat) : DeliveryNode :=
  { ref, path := [.field "users", .index index], label := some (.string "C") }

private def childWork (ref index : Nat) (name : String) : Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨child ref index, []⟩] (child ref index).path
        ({ result := .ok ([("name", .scalar name)], 0) }) (.combine .empty .empty))
      .empty)

private def streamed : Work :=
  .stream stream
    [
      ({ result := .ok (.object [], 0) }, childWork 3 0 "name1"),
      ({ result := .ok (.object [], 0) }, childWork 4 1 "name2")
    ]

private def generatedWork : Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨root 0 "R", []⟩, ⟨root 1 "P", []⟩] []
        ({ result := .error 1, cause := some 1 }) .empty)
      (.combine
        (.executionGroup [⟨root 1 "P", []⟩] []
          ({ result := .ok ([("users", .list [])], 0) })
          (.combine (.combine .empty streamed) .empty)) .empty))

/-- Shared root failure, an unpublished stream, and its deferred item tasks are generated.
Witness: reduction of the query's defer collection and zero-initial-count stream completion.
-/
theorem execution_generated : completed.work = generatedWork := by cbv

private def streamAddress : Address := [1, 1, 0, 0, 0, 1]

private theorem root_r : NodeAt generatedWork (root 0 "R") .group [] none :=
  ⟨[1, 0], _, _, _, _, [], ⟨root 0 "R", []⟩, rfl, by simp, rfl, rfl⟩

private theorem root_p : NodeAt generatedWork (root 1 "P") .group [] none :=
  ⟨[1, 0], _, _, _, _, [], ⟨root 1 "P", []⟩, rfl, by simp, rfl, rfl⟩

private theorem first_child
    : NodeAt generatedWork (child 3 0) .group [] (some (.item streamAddress 0)) :=
  ⟨
    streamAddress ++ [0, 1, 0],
    [⟨child 3 0, []⟩],
    (child 3 0).path,
    { result := .ok ([("name", .scalar "name1")], 0) },
    .combine .empty .empty,
    [],
    ⟨child 3 0, []⟩,
    by cbv,
    by simp,
    rfl,
    rfl
  ⟩

private theorem second_child
    : NodeAt generatedWork (child 4 1) .group [] (some (.item streamAddress 1)) :=
  ⟨
    streamAddress ++ [1, 1, 0],
    [⟨child 4 1, []⟩],
    (child 4 1).path,
    { result := .ok ([("name", .scalar "name2")], 0) },
    .combine .empty .empty,
    [],
    ⟨child 4 1, []⟩,
    by cbv,
    by simp,
    rfl,
    rfl
  ⟩

private theorem first_item
    : TaskAt generatedWork (.item streamAddress 0) [2]
        (some (.executionGroup [1, 1, 0])) (.item stream (.ok (.object [], 0))) :=
  .item (result := { result := .ok (.object [], 0) })
    (show Located generatedWork streamAddress streamed
            (some (.executionGroup [1, 1, 0])) [1] from rfl)
    rfl

private theorem second_item
    : TaskAt generatedWork (.item streamAddress 1) [2]
        (some (.executionGroup [1, 1, 0])) (.item stream (.ok (.object [], 0))) :=
  .item (result := { result := .ok (.object [], 0) })
    (show Located generatedWork streamAddress streamed
            (some (.executionGroup [1, 1, 0])) [1] from rfl)
    rfl

/-- Each streamed-item defer group has an earlier producer with a covering list attachment.
Witness: concrete root descriptors for R/P and actual item tasks for C's two occurrences.
The child defer ancestry is empty, so producer inheritance cannot be replaced by reporting
a failed defer ancestor. No output history or report is assumed by this certificate.
-/
theorem generated_origins : Correctness.GroupProducerOrigins generatedWork := by
  intro node dependencies producer known
  have refs : MixedRefs.WorkAt (fun _ => []) 0 5 generatedWork := by
    simp [MixedRefs.WorkAt, Ancestry.FragmentAt, generatedWork, streamed, childWork,
      root, child, stream]
  have roles : RefRoles.WorkRoles (fun ref => ref == 2) generatedWork := by
    simp [RefRoles.WorkRoles, generatedWork, streamed, childWork, root, child, stream]
  have bound := (coherent_node_bounds refs known).2
  have role := node_ref_role roles known
  change (node.ref == 2) = false at role
  have notStream : node.ref ≠ 2 := by
    intro same
    simp [same] at role
  have cases : node.ref = 0 ∨ node.ref = 1 ∨ node.ref = 3 ∨ node.ref = 4 := by
    have finite : node.ref ≤ 4 := Nat.le_of_lt_succ bound
    have enumerate : ∀ n : Nat, n ≤ 4 → n ≠ 2 → n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 4 := by
      intro n bound different
      omega
    exact enumerate node.ref finite notStream
  rcases cases with same | same | same | same
  · exact ⟨root 0 "R", [], none, root_r, same.symm, Or.inl rfl⟩
  · exact ⟨root 1 "P", [], none, root_p, same.symm, Or.inl rfl⟩
  · refine ⟨child 3 0, [], some (.item streamAddress 0), first_child, same.symm,
      Or.inr ⟨.item streamAddress 0, [2], _, _, 2, rfl, first_item, by simp, by decide, ?_⟩⟩
    exact ⟨[.index 0], rfl⟩
  · refine ⟨child 4 1, [], some (.item streamAddress 1), second_child, same.symm,
      Or.inr ⟨.item streamAddress 1, [2], _, _, 2, rfl, second_item, by simp, by decide, ?_⟩⟩
    exact ⟨[.index 1], rfl⟩

/-- Execution supplies all ref, role, path, locality, and positive-error certificates.
Witness: existing root-completion metadata plus reduction of this generated work tree.
-/
private theorem certificates
    : ∃ ancestry refBound roles paths pathBound,
        Ancestry.Valid ancestry refBound
        ∧ MixedRefs.WorkAt ancestry 0 refBound generatedWork
        ∧ RefRoles.WorkRoles roles generatedWork
        ∧ GeneralScheduling.DeferContinuous ancestry generatedWork
        ∧ GeneralScheduling.StreamOwnersOrdered generatedWork
        ∧ MixedOwnerPaths.WorkAt paths pathBound generatedWork
        ∧ ExecutionPaths.WorkUnder [] generatedWork
        ∧ ExecutionErrors.WorkPositive generatedWork := by
  obtain ⟨_, ancestry, valid, coherent, continuous⟩ :=
    GeneralScheduling.executeRoot_continuity schema resolvers [] 30 "Query"
      (.object "Query" 0) selections 0
  obtain ⟨roles, roleCoherent⟩ := RefRoles.executeRoot_roles schema resolvers [] 30 "Query"
    (.object "Query" 0) selections 0
  obtain ⟨paths, pathCoherent⟩ := MixedOwnerPaths.executeRoot_owners schema resolvers [] 30
    "Query" (.object "Query" 0) selections 0
  have ordered := GeneralScheduling.executeRoot_streamOwnersOrdered schema resolvers [] 30
    "Query" (.object "Query" 0) selections 0
  change MixedRefs.WorkAt ancestry 0 _ completed.work at coherent
  change GeneralScheduling.DeferContinuous ancestry completed.work at continuous
  change RefRoles.WorkRoles roles completed.work at roleCoherent
  change MixedOwnerPaths.WorkAt paths _ completed.work at pathCoherent
  change GeneralScheduling.StreamOwnersOrdered completed.work at ordered
  rw [execution_generated] at coherent continuous roleCoherent pathCoherent ordered
  have under : ExecutionPaths.WorkUnder [] generatedWork := by
    simp [ExecutionPaths.WorkUnder, ExecutionPaths.ItemsUnder, generatedWork, streamed,
      childWork, root, child, stream]
  have positive : ExecutionErrors.WorkPositive generatedWork := by
    simp [ExecutionErrors.WorkPositive, ExecutionErrors.ItemsPositive,
      BasicErrors.PositiveFailure, TaskOutcome.deliveryResult, generatedWork, streamed, childWork]
  exact ⟨ancestry, _, roles, paths, _, valid, coherent, roleCoherent, continuous, ordered,
    pathCoherent, under, positive⟩

/-- This generated mixed query admits a complete run with actual failure-path reporting.
Witness: structural origins, execution-derived ancestry/role/path certificates, and the
reporting-aware finite construction. No all-groups-announced or root-group-only premise
is used: C's descriptors are produced by streamed item tasks and cannot be initial notices.
-/
theorem generated_completeRun : ∃ history, AdmissibleRun generatedWork history := by
  obtain ⟨ancestry, refBound, roles, paths, pathBound, valid, coherent, roleCoherent,
    continuous, ordered, pathCoherent, under, positive⟩ := certificates
  exact mixed_completeRun_exists_of_group_origins valid coherent roleCoherent continuous
    ordered pathCoherent under positive
    (by simp [generatedWork, streamed, childWork, GeneralScheduling.streamAllocationRefs])
    generated_origins (by decide)

/-- Every cancelled task in a closed accounted reporting frontier has an actual report.
Witness: the full structural-origin induction for arbitrary explained output histories,
not a supplied terminal run. Stream-item defer groups have empty defer ancestry; their
unpublished producer case must therefore use structural ref/path inheritance.
-/
theorem cancelled_task_reported
    {groups streams events matching failures occurrence owners producer payload}
    (explained : Explains generatedWork groups streams events matching failures)
    (covered
      : GroupNoticesCovered generatedWork ((groups ++ streams).map DeliveryNode.ref)
          matching events failures)
    (satisfied
      : ∀ ref,
          ¬NodeFailed generatedWork matching events failures ref
          → DependencySatisfied generatedWork ((groups ++ streams).map DeliveryNode.ref)
              matching events failures ref)
    (closed
      : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
          ref ∈ completedRefs events)
    (accounted
      : ∀ occurrence owners producer payload,
          TaskAt generatedWork occurrence owners producer payload
          → TaskAccounted generatedWork matching events failures occurrence)
    (cancelled : TaskCancelled generatedWork matching events failures occurrence)
    (known : TaskAt generatedWork occurrence owners producer payload)
    : FailureReportedFor events payload.path := by
  obtain ⟨ancestry, refBound, roles, paths, pathBound, valid, coherent, roleCoherent,
    continuous, ordered, pathCoherent, under, positive⟩ := certificates
  exact Explains.cancelled_reported_of_group_origins valid coherent roleCoherent continuous
    ordered pathCoherent under positive
    generated_origins explained covered satisfied closed
    accounted cancelled known

#print axioms generated_origins
#print axioms generated_completeRun
#print axioms cancelled_task_reported
#print axioms Explains.failed_owner_reported_of_group_origins
#print axioms mixed_completeRun_exists_of_group_origins

end GraphQL.IncrementalDelivery.Tests.GroupProducerOrigins
