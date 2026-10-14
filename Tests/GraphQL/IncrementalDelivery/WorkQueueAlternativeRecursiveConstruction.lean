import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveExecutionSemantics
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PairedOriginConstruction
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveOriginCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PairedOriginCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveCutAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveRecordingCorrespondence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginOmissions
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Generated multi-level object/list/defer/stream execution. Caught nested failures
skip allocations, retained stream-item Work spans later gaps, and the first fatal item
stops the finite stream tail. The generic theorem constructs every child and one map. -/

namespace AlternativeRecursiveConstructionChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.Semantics
open KeyRenaming ScheduledErrors ScheduledWork

private def schema : GraphQL.Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query",
            fields :=
              [
                { name := "user", outputType := .named "User" },
                { name := "users", outputType := .list (.nonNull (.named "User")) },
                { name := "values", outputType := .list (.named "String") }
              ]
          },
        .object
          {
            name := "User",
            fields :=
              [
                { name := "user", outputType := .named "User" },
                { name := "required", outputType := .nonNull (.named "String") },
                { name := "values", outputType := .list (.named "String") }
              ]
          }
      ]
  }

private def resolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ name _ source =>
        match name, source with
        | "user", _ => some (.object "User" 10)
        | "users", _ =>
            some (.list [.object "User" 1, .object "User" 2, .object "User" 3])
        | "required", .object _ 1 => some (.scalar "ok")
        | "required", _ => none
        | "values", _ => some (.list [.scalar "x"])
        | _, _ => none
    resolve_argumentsEquivalent := by intros; rfl
  }

private def failedChildren : List Selection :=
  [
    Tests.field "required" [] [] (some "first"),
    Tests.field "required" [] [] (some "second"),
    Tests.field "values" [] [.stream] (some "skipped")
  ]

private def itemChildren : List Selection :=
  [
    Tests.field "user" failedChildren,
    Tests.field "values" [] [.stream] (some "before"),
    Tests.field "required",
    Tests.field "values" [] [.stream] (some "after"),
    Tests.defer [Tests.defer [Tests.field "values" [] [.stream] (some "deferred")]]
  ]

private def selections : List Selection :=
  [
    Tests.field "user" failedChildren,
    Tests.field "users" itemChildren [.stream],
    Tests.field "values" [] [.stream] (some "later")
  ]

private def cut :=
  (ScheduledExecution.executeRootSelectionSetCore schema resolvers [] 12 "Query"
    (.object "Query" 0) selections).run
    0

private def eager :=
  (Execution.executeRootSelectionSetCore schema resolvers [] 12 "Query"
    (.object "Query" 0) selections).run
    0

private theorem constructed : ∃ next, RunRefines id next 0 0 cut eager :=
  recursiveExecutionConstruction_holds _ schema resolvers [] 12 "Query"
    (.object "Query" 0) selections id 0 0
    ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩

example : cut.2 = 10 ∧ eager.2 = 14 := by cbv

example
    : cut.1.result = .ok ([("user", .null), ("users", .list []), ("later", .list [])], 1)
      ∧ eager.1.result
        = .ok ([("user", .null), ("users", .list []), ("later", .list [])], 2) := by cbv

private theorem stream_key {keys : Nat → Nat} {before after : DeliveryNode}
    {items eagerItems}
    (known : WorkRefines keys (.stream before items) (.stream after eagerItems))
    : keys before.ref = after.ref := by cases known; rfl

-- Every retained hidden item key and the later root stream use the root's one witness.
example
    : ∃ next,
        next 0 = 1
        ∧ next 3 = 5
        ∧ next 4 = 6
        ∧ next 5 = 7
        ∧ next 9 = 13
        ∧ next 10 = 14
        ∧ CompletionRefines next cut.1 eager.1 := by
  obtain ⟨next, related⟩ := constructed
  have outer := related.completion.2.locate [0, 1, 0, 1]
  have before := related.completion.2.locate [0, 1, 0, 1, 0, 0, 1, 0, 1]
  have after := related.completion.2.locate [0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1]
  have deferred := related.completion.2.locate [0, 1, 0, 1, 0, 1, 0, 0, 0, 1]
  have later := related.completion.2.locate [0, 1, 1, 0, 1]
  cbv at outer before after deferred later
  refine ⟨next, stream_key outer.1, stream_key before.1, stream_key after.1,
    stream_key deferred.1, stream_key later.1, ?_, related.completion⟩
  simpa only [show cut.2 = 10 by cbv, show eager.2 = 14 by cbv]
    using related.supplies.boundary

private def streamItems (work : Work) : List (Result ResponseValue × Work) :=
  match WorkQueueSemantics.locateWork work [0, 1, 0, 1] with
  | some ⟨.stream _ items, _, _⟩ => items
  | _ => []

-- Both policies retain exactly the first two item positions. The second item's fatal
-- report includes the preceding caught nested error; the third item is never retained.
example
    : (streamItems cut.1.work).length = 2 ∧ (streamItems eager.1.work).length = 2 := by
  cbv

example
    : (streamItems cut.1.work)[1]? = some (.error 2, .empty)
      ∧ (streamItems eager.1.work)[1]? = some (.error 3, .empty) := by cbv

-----------------------------------------------------------------------------------------
-- Ordinary lists also construct maps after inherited gaps and caught object failures
-----------------------------------------------------------------------------------------

private def keys : Nat → Nat := retargetTail id 18 21

private theorem initial : SupplyMap keys 20 23 := by
  have prefixBound : PrefixBelow id 18 21 := by intro key earlier; dsimp; omega
  refine ⟨
    retargetTail_injective (fun _ _ same => same) prefixBound,
    ?_,
    ?_,
    (retargetTail_fresh id 18 21).advance (by omega)
  ⟩
  · intro key earlier
    unfold keys retargetTail
    split
    · change key < 23
      omega
    · omega
  · cbv

private def fields : List FieldDetails :=
  [{ fieldName := "users", arguments := [], selectionSet := itemChildren }]

private def values : ResolverValue Nat :=
  .list [.object "User" 1, .object "User" 2, .object "User" 3]

private def listCut :=
  (ScheduledExecution.completeValue schema resolvers [] 12 (.list (.named "User")) fields
    values [.field "users"] [] [] false).run
    20

private def listEager :=
  (Execution.completeValue schema resolvers [] 12 (.list (.named "User"))
    (fields.map (field keys)) values [.field "users"] [] [] false).run
    23

private theorem list_constructed
    : ∃ next, RunRefines keys next 20 23 listCut listEager := by
  apply valueRunConstruction_holds schema resolvers [] 12 (.list (.named "User")) fields
    values [.field "users"] [] [] false keys 20 23 initial
  · intro details member
    simp only [fields, List.mem_singleton] at member
    subst details
    simp [UsageBefore]
  · simp
  · simp

example : listCut.2 = 31 ∧ listEager.2 = 39 := by cbv

example
    : ∃ next,
        next 16 = 16
        ∧ next 17 = 17
        ∧ next 31 = 39
        ∧ CompletionRefines next listCut.1 listEager.1 := by
  obtain ⟨next, related⟩ := list_constructed
  refine ⟨
    next,
    (related.compatible 16 (by omega)).trans (by cbv),
    (related.compatible 17 (by omega)).trans (by cbv),
    ?_,
    related.completion
  ⟩
  simpa only [show listCut.2 = 31 by cbv, show listEager.2 = 39 by cbv]
    using related.supplies.boundary

private def initialFields : List FieldDetails :=
  [{
    fieldName := "users",
    arguments := [],
    selectionSet := itemChildren,
    directives := [.stream (.boolean true) none (.int 1)]
  }]

private def initialCut :=
  (ScheduledExecution.completeValue schema resolvers [] 12
    (.list (.nonNull (.named "User"))) initialFields values [.field "users"] [] []
    true).run
    20

private def initialEager :=
  (Execution.completeValue schema resolvers [] 12 (.list (.nonNull (.named "User")))
    (initialFields.map (field keys)) values [.field "users"] [] [] true).run
    23

private theorem initial_constructed
    : ∃ next, RunRefines keys next 20 23 initialCut initialEager := by
  apply valueRunConstruction_holds schema resolvers [] 12 (.list (.nonNull (.named "User")))
    initialFields values [.field "users"] [] [] true keys 20 23 initial
  · intro details member
    simp only [initialFields, List.mem_singleton] at member
    subst details
    simp [UsageBefore]
  · simp
  · simp

example : initialCut.2 = 29 ∧ initialEager.2 = 35 := by cbv

-- Initial item Work must be rekeyed by the final map after the tail's nested cut.
example
    : ∃ next,
        next 16 = 16
        ∧ next 17 = 17
        ∧ next 29 = 35
        ∧ CompletionRefines next initialCut.1 initialEager.1 := by
  obtain ⟨next, related⟩ := initial_constructed
  refine ⟨
    next,
    (related.compatible 16 (by omega)).trans (by cbv),
    (related.compatible 17 (by omega)).trans (by cbv),
    ?_,
    related.completion
  ⟩
  simpa only [show initialCut.2 = 29 by cbv, show initialEager.2 = 35 by cbv]
    using related.supplies.boundary

example : RecursiveExecutionConstruction := recursiveExecutionConstruction_holds

example : RecursiveExecutionSemantics := recursiveExecutionSemantics_holds

example (fuel : Nat) : ValueRunConstruction schema resolvers [] fuel :=
  valueRunConstruction_holds schema resolvers [] fuel

-----------------------------------------------------------------------------------------
-- Actual retained fatal item, its mapped owner and the same shared publication cut
-----------------------------------------------------------------------------------------

private def fatalItem : WorkQueueSemantics.Occurrence := .item [0, 1, 0, 1] 1
private def firstItem : WorkQueueSemantics.Occurrence := .item [0, 1, 0, 1] 0

private theorem fatal_task
    : WorkQueueSemantics.TaskAt cut.1.work fatalItem [0] none
        (.item { ref := 0, path := [.field "users"] } (.error 2)) := by
  refine ⟨{ ref := 0, path := [.field "users"] }, streamItems cut.1.work,
    [], .error 2, .empty, ?_, ?_, rfl, rfl⟩
  · cbv
  · cbv

private theorem first_task
    : ∃ value, WorkQueueSemantics.TaskAt cut.1.work firstItem [0] none value := by
  let item := (streamItems cut.1.work)[0]'(by cbv)
  refine ⟨.item { ref := 0, path := [.field "users"] } item.1,
    { ref := 0, path := [.field "users"] }, streamItems cut.1.work,
    [], item.1, item.2, ?_, ?_, rfl, rfl⟩
  · cbv
  · dsimp only [item]
    cbv

private theorem constructed_semantics
    : ∃ next,
        RunRefines id next 0 0 cut eager
        ∧ WorkSemanticsRefines next cut.1.work eager.1.work :=
  recursiveExecutionSemantics_holds _ schema resolvers [] 12 "Query" (.object "Query" 0)
    selections id 0 0 ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩

example
    : ∃ next,
        WorkSemanticsRefines next cut.1.work eager.1.work
        ∧ WorkQueueSemantics.TaskAt eager.1.work fatalItem [1] none
            (.item { ref := 1, path := [.field "users"] } (.error 3))
        ∧ WorkQueueSemantics.Causality.NodeFailed eager.1.work [fatalItem]
            (fun _ => False) 1
        ∧ WorkQueueSemantics.Causality.TaskCancelled eager.1.work [fatalItem]
            (fun _ => False) firstItem := by
  obtain ⟨next, related, semantics⟩ := constructed_semantics
  have outer := related.completion.2.locate [0, 1, 0, 1]
  cbv at outer
  have owner : next 0 = 1 := stream_key outer.1
  have failure : WorkQueueSemantics.Causality.NodeFailed cut.1.work [fatalItem] (fun _ => False) 0 :=
    .task ⟨none, _, fatal_task⟩ (by simp) (by simp)
  obtain ⟨value, first⟩ := first_task
  have cancelled : WorkQueueSemantics.Causality.TaskCancelled cut.1.work [fatalItem] (fun _ => False) firstItem :=
    .owners ⟨none, value, first⟩ (by simp) (by simp)
      (by intro key member; obtain rfl := List.mem_singleton.mp member; exact failure)
  refine ⟨next, semantics, ?_, ?_, (semantics.cancellations ..).mpr cancelled⟩
  · obtain ⟨after, actual, _⟩ := semantics.tasks _ _ _ _ fatal_task
    have exactLookup : ∀ payload,
        WorkQueueSemantics.TaskAt eager.1.work fatalItem [1] none payload
        → payload = .item { ref := 1, path := [.field "users"] } (.error 3) := by
      intro payload known
      rcases known with ⟨node, items, enclosing, result, children, located, item, _, rfl⟩
      cbv at located
      cases located
      cbv at item
      cases item
      rfl
    simp only [List.map_cons, List.map_nil, owner] at actual
    rw [exactLookup after actual] at actual
    exact actual
  · exact (semantics.nodeFailures _ _ 1).mpr ⟨0, owner, failure⟩

-- Publishing a producer protects it at the shared cut in both actual Work trees.
example
    : ¬ WorkQueueSemantics.Causality.TaskCancelled eager.1.work [fatalItem]
          (fun occurrence => occurrence = firstItem) firstItem := by
  intro known
  cases known with
  | owners _ unpublished _ _ => exact unpublished rfl
  | producerFailed _ unpublished _ => exact unpublished rfl
  | producerCancelled _ unpublished _ => exact unpublished rfl

-----------------------------------------------------------------------------------------
-- Primitive origin reports erase to this same actual recursive cut execution
-----------------------------------------------------------------------------------------

open OriginAccounting

private def annotated :=
  (RecordedExecution.executeRootSelectionSetCore schema resolvers [] 12 "Query"
    (.object "Query" 0) selections).run
    0

private def eagerAnnotated :=
  (EagerRecordedExecution.executeRootSelectionSetCore schema resolvers [] 12 "Query"
    (.object "Query" 0) selections).run
    0

private theorem eagerAnnotated_erases : eraseCompletionRun eagerAnnotated = eager :=
  EagerErasure.recursiveEagerOriginErasure_holds _ schema resolvers [] 12 "Query"
    (.object "Query" 0) selections [] 0

example : eagerAnnotated.2 = 14 :=
  (congrArg Prod.snd eagerAnnotated_erases).trans (by cbv)

example : eagerAnnotated.1.report.origins.length = 2 := by cbv
example : eagerAnnotated.1.origins.length = 7 := by cbv

example : eagerAnnotated.1.origins.Nodup :=
  (EagerScopes.recursiveEagerOriginUniqueness_holds _ schema resolvers [] 12 "Query"
    (.object "Query" 0) selections [] 0).unique

private theorem origin_coverage : CompletionOriginsRefine annotated.1 eagerAnnotated.1 :=
  recursiveOriginCoverage_holds _ schema resolvers [] 12 "Query" (.object "Query" 0)
    selections [] id 0 0
    ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩

-- Constructed by the general theorem, not by evaluating the desired relation.
example : annotated.1.report.origins.Sublist eagerAnnotated.1.report.origins :=
  origin_coverage.1.2

example : annotated.1.origins.Sublist eagerAnnotated.1.origins := origin_coverage.origins

-- Missing identities account exactly for both the initial and whole retained
-- inventory gaps. Future task errors are not added to the initial report's count.
example
    : ScheduledErrors.countedErrors annotated.1.report.outcome
        + (omittedOrigins annotated.1.report.origins
            eagerAnnotated.1.report.origins).length
      = ScheduledErrors.countedErrors eagerAnnotated.1.report.outcome :=
  origin_coverage.1.omitted_count
    (EagerScopes.recursiveEagerOriginUniqueness_holds _ schema resolvers []
      12 "Query" (.object "Query" 0) selections [] 0).left.unique

example
    : annotated.1.origins.length
        + (omittedOrigins annotated.1.origins eagerAnnotated.1.origins).length
      = eagerAnnotated.1.origins.length :=
  omittedOrigins_partition origin_coverage.origins
    (EagerScopes.recursiveEagerOriginUniqueness_holds _ schema
      resolvers [] 12 "Query" (.object "Query" 0) selections [] 0).unique

example
    : (omittedOrigins annotated.1.report.origins eagerAnnotated.1.report.origins).length
        = 1
      ∧ (omittedOrigins annotated.1.origins eagerAnnotated.1.origins).length = 3 := by cbv

private def annotatedList :=
  (RecordedExecution.completeValue schema resolvers [] 12 (.list (.named "User")) fields
    values [.field "users"] [] [] false [4]).run
    20

private def eagerAnnotatedList :=
  (EagerRecordedExecution.completeValue schema resolvers [] 12 (.list (.named "User"))
    (fields.map (field keys)) values [.field "users"] [] [] false [4]).run
    23

private theorem list_origin_coverage
    : CompletionOriginsRefine annotatedList.1 eagerAnnotatedList.1 := by
  apply valueOriginsConstruction_holds schema resolvers [] 12 (.list (.named "User")) fields values
    [.field "users"] [] [] false [4] keys 20 23 initial
  · intro details member
    simp only [fields, List.mem_singleton] at member
    subst details
    simp [UsageBefore]
  · simp
  · simp

example : annotatedList.1.origins.Sublist eagerAnnotatedList.1.origins :=
  list_origin_coverage.origins

example : annotatedList.2 = 31 ∧ eagerAnnotatedList.2 = 39 := by cbv

private def failedDeferSelections : List Selection :=
  [Tests.field "user"
    [
      Tests.defer failedChildren,
      Tests.defer [Tests.field "values" [] [.stream] (some "survivor")]
    ]]

private def failedDeferCut :=
  (RecordedExecution.executeRootSelectionSetCore schema resolvers [] 12 "Query"
    (.object "Query" 0) failedDeferSelections).run
    0

private def failedDeferEager :=
  (EagerRecordedExecution.executeRootSelectionSetCore schema resolvers [] 12 "Query"
    (.object "Query" 0) failedDeferSelections).run
    0

private theorem failedDefer_coverage
    : CompletionOriginsRefine failedDeferCut.1 failedDeferEager.1 :=
  recursiveOriginCoverage_holds _ schema resolvers [] 12 "Query" (.object "Query" 0)
    failedDeferSelections [] id 0 0
    ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩

-- The first deferred task fails, but the later group's stream is still allocated.
-- The initial report has no errors; all originating faults belong to the failed task.
example
    : failedDeferCut.1.report.origins = []
      ∧ failedDeferEager.1.report.origins = []
      ∧ failedDeferCut.1.origins.length = 1
      ∧ failedDeferEager.1.origins.length = 2
      ∧ failedDeferCut.2 = 3
      ∧ failedDeferEager.2 = 4 := by cbv

example : failedDeferCut.1.origins.Sublist failedDeferEager.1.origins :=
  failedDefer_coverage.origins

-- Count equality alone cannot identify an originating primitive.
example
    : ¬ (Report.fault [0] (.error 1 : Result ResponseValue)).origins.Sublist
          (Report.fault [1] (.error 1 : Result ResponseValue)).origins := by decide

private theorem annotated_erases : eraseCompletionRun annotated = cut :=
  recursiveOriginErasure_holds _ schema resolvers [] 12 "Query"
    (.object "Query" 0) selections [] 0

example : annotated.1.erase = cut.1 ∧ annotated.2 = 10 := by
  have output := congrArg Prod.fst annotated_erases
  have supply := congrArg Prod.snd annotated_erases
  exact ⟨output, supply.trans (by cbv)⟩

-- The caught initial error has one origin; retained future item/task errors are
-- distinct inventories, not extra errors in the initial response.
example : annotated.1.report.origins.length = 1 := by cbv
example : annotated.1.origins.length = 4 := by cbv

example : annotated.1.origins.Nodup :=
  (recursiveOriginUniqueness_holds _ schema resolvers [] 12 "Query"
    (.object "Query" 0) selections [] 0).unique

private theorem origins_constructed
    : ∃ next,
        Scoped [] annotated.1.origins
        ∧ eraseCompletionRun annotated = cut
        ∧ RunRefines id next 0 0 (eraseCompletionRun annotated) eager
        ∧ WorkSemanticsRefines next annotated.1.erase.work eager.1.work :=
  recursiveOriginConstruction_holds _ schema resolvers [] 12 "Query"
    (.object "Query" 0) selections [] id 0 0
    ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩

private theorem paired_covered
    : ∃ next,
        CompletionOriginsRefine annotated.1 eagerAnnotated.1
        ∧ RunRefines id next 0 0 cut eager
        ∧ WorkSemanticsRefines next cut.1.work eager.1.work := by
  obtain ⟨next, _, _, _, _, related, semantics, covered, _, _⟩ := pairedOriginCoverage_holds _ schema
    resolvers [] 12 "Query" (.object "Query" 0) selections [] id 0 0
    ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩
  change RunRefines id next 0 0 (eraseCompletionRun annotated) (eraseCompletionRun eagerAnnotated) at related
  change WorkSemanticsRefines next annotated.1.erase.work eagerAnnotated.1.erase.work at semantics
  rw [annotated_erases, eagerAnnotated_erases] at related
  have cutWork := congrArg (fun output => output.1.work) annotated_erases
  have eagerWork := congrArg (fun output => output.1.work) eagerAnnotated_erases
  dsimp only [eraseCompletionRun] at cutWork eagerWork
  rw [cutWork, eagerWork] at semantics
  exact ⟨next, covered, related, semantics⟩

private theorem cuts_constructed
    : ∃ initialSites futureSites,
        CompletionCutTrace annotated.1 eagerAnnotated.1
        ∧ CutAccounted annotated.1.report.origins eagerAnnotated.1.report.origins
            initialSites
        ∧ CutAccounted annotated.1.work.origins eagerAnnotated.1.work.origins futureSites
        ∧ CutAccounted annotated.1.origins eagerAnnotated.1.origins
            (initialSites ++ futureSites) := by
  obtain ⟨_, initialSites, futureSites, _, _, trace, initial, future, whole, _, _⟩ :=
    recursiveCutAccounting_holds _ schema resolvers [] 12 "Query" (.object "Query" 0)
      selections [] id 0 0
      ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩
  exact ⟨initialSites, futureSites, trace, initial, future, whole⟩

private theorem recordings_constructed
    : ReportRecording annotated.1.report eagerAnnotated.1.report
      ∧ WorkRecordings annotated.1.work eagerAnnotated.1.work := by
  obtain ⟨_, _, _, _, _, _, _, _, _, initial, future, _, _⟩ :=
    recursiveRecordingCorrespondence_holds _ schema resolvers [] 12 "Query" (.object "Query" 0)
      selections [] id 0 0
      ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩
  exact ⟨initial, future⟩

example
    : ∃ (actions : List OriginAction) (omitted : List Origin),
        (actions.filterMap OriginAction.recorded?).length
          = ScheduledErrors.countedErrors annotated.1.report.outcome
        ∧ ScheduledErrors.countedErrors annotated.1.report.outcome + omitted.length
          = ScheduledErrors.countedErrors eagerAnnotated.1.report.outcome := by
  obtain ⟨actions, omitted, _, _, _, count, gap⟩ := recordings_constructed.1.observation
  exact ⟨actions, omitted, count, gap⟩

example
    : ReportRecording failedDeferCut.1.report failedDeferEager.1.report
      ∧ WorkRecordings failedDeferCut.1.work failedDeferEager.1.work := by
  obtain ⟨_, _, _, _, _, _, _, _, _, initial, future, _, _⟩ :=
    recursiveRecordingCorrespondence_holds _ schema resolvers [] 12 "Query" (.object "Query" 0)
      failedDeferSelections [] id 0 0
      ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩
  exact ⟨initial, future⟩

example : CompletionCutTrace failedDeferCut.1 failedDeferEager.1 :=
  recursiveCutConstruction_holds _ schema resolvers [] 12 "Query" (.object "Query" 0)
    failedDeferSelections [] id 0 0
    ⟨fun _ _ same => same, fun _ earlier => earlier, rfl, fun _ => rfl⟩

example : CompletionCutTrace annotatedList.1 eagerAnnotatedList.1 := by
  apply valueCutConstruction_holds schema resolvers [] 12 (.list (.named "User")) fields values
    [.field "users"] [] [] false [4] keys 20 23 initial
  · intro details member
    simp only [fields, List.mem_singleton] at member
    subst details
    simp [UsageBefore]
  · simp
  · simp

-- One actual annotated run supplies both the unique origin inventory and the key
-- map before task observations or failure/publication snapshots are selected.
example
    : ∃ next,
        annotated.1.origins.Nodup
        ∧ RunRefines id next 0 0 (eraseCompletionRun annotated) eager
        ∧ WorkSemanticsRefines next annotated.1.erase.work eager.1.work := by
  obtain ⟨next, origins, _, related, semantics⟩ := origins_constructed
  exact ⟨next, origins.unique, related, semantics⟩

-- Future outcomes cannot duplicate an error already present in the initial report.
example : ∀ origin ∈ annotated.1.report.origins, origin ∉ annotated.1.work.origins := by
  obtain ⟨_, origins, _, _, _⟩ := origins_constructed
  have distinct := (List.nodup_append.mp origins.unique).2.2
  intro origin initial future
  exact distinct origin initial origin future rfl

-- Repeated bubbles do not relabel, duplicate or drop a preceding nullable error.
private def prior : Report ResponseValue := .fault [7, 0] (.ok (.null, 1))
private def fatal : Report ResponseValue := .fault [7, 1] (.error 1)
private def joined := Report.combine (fun left _ => left) prior fatal
private def rebubbled := (joined.catchNull id).nonNull [7]

example : rebubbled.outcome = .error 2 := rfl
example : rebubbled.origins = [([7, 0], 0), ([7, 1], 0)] := rfl
example : (Report.pure ResponseValue.null |>.nonNull [9]).origins = [([9], 0)] := rfl

#print axioms valueRunConstruction_holds
#print axioms recursiveExecutionConstruction_holds
#print axioms constructed
#print axioms list_constructed
#print axioms initial_constructed
#print axioms recursiveExecutionSemantics_holds
#print axioms constructed_semantics
#print axioms recursiveOriginErasure_holds
#print axioms annotated_erases
#print axioms recursiveOriginUniqueness_holds
#print axioms recursiveOriginConstruction_holds
#print axioms origins_constructed
#print axioms EagerErasure.recursiveEagerOriginErasure_holds
#print axioms EagerScopes.recursiveEagerOriginUniqueness_holds
#print axioms pairedOriginConstruction_holds
#print axioms eagerAnnotated_erases
#print axioms recursiveOriginCoverage_holds
#print axioms recursiveOriginSubsequence_holds
#print axioms origin_coverage
#print axioms list_origin_coverage
#print axioms failedDefer_coverage
#print axioms pairedOriginCoverage_holds
#print axioms paired_covered
#print axioms cuts_constructed
#print axioms recursiveCutAccounting_holds
#print axioms recordings_constructed
#print axioms recursiveRecordingCorrespondence_holds

end AlternativeRecursiveConstructionChecks
