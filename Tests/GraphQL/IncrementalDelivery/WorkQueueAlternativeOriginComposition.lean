import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralReachedCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralStreamCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralStreamAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralValueAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginOmissions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginUniqueness

/-! Constructed primitive coverage, exact omissions and prior-error boundaries.
These pure finite runs do not represent native starts or error-recording events. -/

namespace AlternativeOriginCompositionChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open OriginAccounting ScheduledWork

private def schema : GraphQL.Schema := { queryType := "Query", types := [] }

private def resolvers : Resolvers Nat :=
  { resolve := fun _ _ _ _ => none, resolve_argumentsEquivalent := by intros; rfl }

private def values : ResolverValue Nat :=
  .list [.list [.scalar "good", .null, .null], .list [.null, .null]]

private theorem literal : LiteralValue values := by
  apply LiteralValue.list
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply LiteralValue.list
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .scalar _
    · exact .null
    · exact .null
  · apply LiteralValue.list
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .null

private def itemType : GraphQL.TypeRef := .list (.nonNull (.named "String"))

private def cut (required : Bool) :=
  (RecordedExecution.completeValue schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) [] values [] [] [] false
    []).run
    7

private def eager (required : Bool) :=
  (EagerRecordedExecution.completeValue schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) [] values [] [] [] false
    []).run
    7

private theorem constructed (required : Bool)
    : CompletionOriginsRefine (cut required).1 (eager required).1
      ∧ (cut required).2 = 7
      ∧ (eager required).2 = 7 :=
  literalNoStreamOriginsConstruction_holds _ schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) [] values [] [] [] []
    literal 7

private def reachedCuts (required : Bool) :=
  LiteralCuts.value schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) [] values [] [] [] [] 7

private theorem omissions_constructed (required : Bool)
    : OmissionAtCuts (cut required).1 (eager required).1 (reachedCuts required) :=
  literalReachedCutOmission_holds _ schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) [] values [] [] [] [] 7
    literal

example (required : Bool) (origin : Origin)
    (missing
      : origin
        ∈ omittedOrigins (cut required).1.report.origins
            (eager required).1.report.origins)
    : ∃ site ∈ reachedCuts required, site.tailRoute.IsPrefix origin.1 :=
  (omissions_constructed required).1 origin missing

example (required : Bool) (site : SiblingCut) (reached : site ∈ reachedCuts required)
    : 0 < site.errors :=
  (omissions_constructed required).2 site reached

-- The required outer-list run reaches the inner cut and then the outer cut, not
-- the second inner list. One cut may cover several unexecuted eager errors.
example
    : (reachedCuts true).map SiblingCut.tailRoute
      = [[0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 1]] := by cbv

example : (reachedCuts true).map SiblingCut.errors = [1, 1] := by cbv

private theorem eagerUnique (required : Bool) : (eager required).1.report.origins.Nodup :=
  (EagerScopes.completeValue_origins schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) [] values [] [] [] false []
    7).left.unique

-- Exact counts follow from the constructed coverage and actual eager uniqueness,
-- rather than supplying the desired count gap as a premise.
example (required : Bool)
    : ScheduledErrors.countedErrors (cut required).1.report.outcome
        + (omittedOrigins (cut required).1.report.origins
            (eager required).1.report.origins).length
      = ScheduledErrors.countedErrors (eager required).1.report.outcome :=
  (constructed required).1.1.omitted_count (eagerUnique required)

-- Nullable inner lists catch the two independent cuts. Both actual data values agree.
example
    : (cut false).1.report.outcome = .ok (.list [.null, .null], 2)
      ∧ (eager false).1.report.outcome = .ok (.list [.null, .null], 4) := by cbv

-- A required inner list bubbles the first caught cut; the later outer item is skipped.
example
    : (cut true).1.report.outcome = .ok (.null, 1)
      ∧ (eager true).1.report.outcome = .ok (.null, 4) := by cbv

example (required : Bool) : (cut required).1.origins.Sublist (eager required).1.origins :=
  (constructed required).1.origins

example
    : (omittedOrigins (cut false).1.report.origins (eager false).1.report.origins).length
        = 2
      ∧ (omittedOrigins (cut true).1.report.origins (eager true).1.report.origins).length
        = 3 := by
  cbv

-----------------------------------------------------------------------------------------
-- Retained stream reports and the original shared fatal tail boundary
-----------------------------------------------------------------------------------------

private def streamFields (initialCount : Nat) : List FieldDetails :=
  [{
    fieldName := "values",
    arguments := [],
    selectionSet := [],
    directives := [.stream (.boolean true) none (.int (Int.ofNat initialCount))]
  }]

private def streamCut (required : Bool) (initialCount : Nat) :=
  (RecordedExecution.completeValue schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) (streamFields initialCount)
    values [] [] [] true []).run
    7

private def streamEager (required : Bool) (initialCount : Nat) :=
  (EagerRecordedExecution.completeValue schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) (streamFields initialCount)
    values [] [] [] true []).run
    7

private theorem stream_constructed (required : Bool) (initialCount : Nat)
    : CompletionOriginsRefine (streamCut required initialCount).1
        (streamEager required initialCount).1
      ∧ (streamCut required initialCount).2 = (streamEager required initialCount).2 :=
  literalOriginsConstruction_holds _ schema resolvers [] 8
    (.list (if required then .nonNull itemType else itemType)) (streamFields initialCount)
    values [] [] [] true [] literal 7

private def items (work : RecordedWork) : List (Report ResponseValue × RecordedWork) :=
  match work with
  | .combine _ (.stream _ items) => items
  | _ => []

example
    : (items (streamCut false 0).1.work).length = 2
      ∧ (items (streamEager false 0).1.work).length = 2
      ∧ (streamCut false 0).1.origins.length = 2
      ∧ (streamEager false 0).1.origins.length = 4 := by cbv

-- Both retain the first fatal item; neither executes the second item in the public tail.
example
    : (items (streamCut true 0).1.work).length = 1
      ∧ (items (streamEager true 0).1.work).length = 1
      ∧ (streamCut true 0).1.origins.length = 1
      ∧ (streamEager true 0).1.origins.length = 2 := by cbv

example (required : Bool) (initialCount : Nat)
    : (streamCut required initialCount).1.origins.Sublist
        (streamEager required initialCount).1.origins :=
  (stream_constructed required initialCount).1.origins

-- Equal length keeps an empty stream boundary; an excess initialCount has no boundary.
example : (streamCut false 2).2 = 8 ∧ (streamCut false 3).2 = 7 := by cbv

-- Initial fatal bubbling discards future stream Work before allocating its boundary.
example : (streamCut true 1).2 = 7 ∧ (streamCut true 1).1.work = .empty := by cbv

-----------------------------------------------------------------------------------------
-- One actual cut inventory for the retained stream tail
-----------------------------------------------------------------------------------------

private def streamSources : List (ResolverValue Nat) :=
  [.list [.scalar "good", .null, .null], .list [.null, .null]]

private theorem streamSources_literal
    : ∀ source ∈ streamSources, LiteralValue source := by
  cases literal with
  | list known => exact known

private def tailFields :=
  (streamFields 0).map (fun field => { field with deferUsage := none })

private def cutTail (required : Bool) :=
  ((RecordedExecution.completeStreamItems schema resolvers [] 7
      (if required then .nonNull itemType else itemType) tailFields streamSources [] 0
      [0, 1]).run
    8).1

private def eagerTail (required : Bool) :=
  ((EagerRecordedExecution.completeStreamItems schema resolvers [] 7
      (if required then .nonNull itemType else itemType) tailFields streamSources [] 0
      [0, 1]).run
    8).1

private def tailCuts (required : Bool) :=
  LiteralCuts.streamItems schema resolvers [] 7
    (if required then .nonNull itemType else itemType) tailFields streamSources [] 0
    [0, 1] 8

private theorem tail_constructed (required : Bool)
    : ItemCutAccounting (cutTail required) (eagerTail required) (tailCuts required) :=
  literalStreamTailAccounting_holds _ schema resolvers [] 7
    (if required then .nonNull itemType else itemType) tailFields streamSources [] 0
    [0, 1] 8 streamSources_literal

private theorem tail_is_actual (required : Bool)
    : items (streamCut required 0).1.work = cutTail required
      ∧ items (streamEager required 0).1.work = eagerTail required := by
  cases required <;> cbv

-- All indices use the one inventory constructed from the actual retained tail.
example (required : Bool) (index : Nat)
    : ItemCutAccounting.AtIndex (items (streamCut required 0).1.work)
        (items (streamEager required 0).1.work) (tailCuts required) index := by
  rw [(tail_is_actual required).1, (tail_is_actual required).2]
  exact (tail_constructed required).atIndex index

example (required : Bool) (origin : Origin)
    (missing
      : origin
        ∈ omittedOrigins (itemOrigins (cutTail required))
            (itemOrigins (eagerTail required)))
    : WithinCuts (tailCuts required).flatten origin :=
  (tail_constructed required).omitted_origins origin missing

example (required : Bool) (site : SiblingCut)
    (reached : site ∈ (tailCuts required).flatten)
    : 0 < site.errors :=
  (tail_constructed required).cuts_positive site reached

-- The shared stream stop has no extra site: only the first item's internal cut
-- explains omissions, and index 1 is absent on both sides.
example
    : ((tailCuts true).flatten).map SiblingCut.tailRoute
      = [[0, 1, 0, 0, 0, 0, 1, 1]] := by cbv

example : (tailCuts true).length = 1 ∧ (tailCuts false).length = 2 := by cbv

example : (cutTail true)[1]? = none ∧ (eagerTail true)[1]? = none := by cbv

example
    : (omittedOrigins (itemOrigins (cutTail true)) (itemOrigins (eagerTail true))).length
      = 1 := by cbv

example
    : (omittedOrigins (itemOrigins (cutTail false))
        (itemOrigins (eagerTail false))).length
      = 2 := by cbv

-----------------------------------------------------------------------------------------
-- Initial and retained tail scopes from the same actual outer-stream run
-----------------------------------------------------------------------------------------

private def streamInventory (required : Bool) (initialCount : Nat) :=
  LiteralCuts.listWithStream schema resolvers [] 7
    (if required then .nonNull itemType else itemType) (streamFields initialCount)
    streamSources [] [] [] true [0] 7

private theorem stream_accounted (required : Bool) (initialCount : Nat)
    : StreamCutAccounting (streamCut required initialCount).1
        (streamEager required initialCount).1 (streamInventory required initialCount)
      ∧ CompletionOriginsRefine (streamCut required initialCount).1
          (streamEager required initialCount).1
      ∧ (streamCut required initialCount).2 = (streamEager required initialCount).2 := by
  simpa only [streamCut, streamEager, values, streamSources, streamInventory,
    List.nil_append, RecordedExecution.completeValue,
    EagerRecordedExecution.completeValue]
    using literalStreamAccounting_holds _ schema resolvers [] 7
      (if required then .nonNull itemType else itemType) (streamFields initialCount)
      streamSources [] [] [] true [0] 7 streamSources_literal

example (required : Bool) (initialCount : Nat) (origin : Origin)
    (missing
      : origin
        ∈ omittedOrigins (streamCut required initialCount).1.origins
            (streamEager required initialCount).1.origins)
    : WithinCuts (streamInventory required initialCount).sites origin :=
  (stream_accounted required initialCount).1.omitted_origins origin missing

example (required : Bool) (initialCount : Nat) (site : SiblingCut)
    (reached : site ∈ (streamInventory required initialCount).sites)
    : 0 < site.errors :=
  (stream_accounted required initialCount).1.cuts_positive site reached

-- Initial errors and future item errors stay in separate scope inventories.
example
    : (streamInventory false 0).initial = []
      ∧ (streamInventory false 0).items.length = 2 := by cbv

example
    : (streamInventory false 1).initial.length = 1
      ∧ (streamInventory false 1).items.length = 1 := by cbv

-- Initial fatal bubbling suppresses the boundary; there are no tail sites.
example
    : (streamInventory true 1).initial.length = 2
      ∧ (streamInventory true 1).items = [] := by cbv

private def hasBoundary (work : RecordedWork) : Bool :=
  match work with
  | .combine _ (.stream _ _) => true
  | _ => false

-- Empty retained boundaries and excess-count suppression have the same empty
-- item inventory, but different actual Work. The witness retains this distinction.
example
    : (streamInventory false 2).items = []
      ∧ (streamInventory false 3).items = []
      ∧ hasBoundary (streamCut false 2).1.work = true
      ∧ hasBoundary (streamCut false 3).1.work = false := by cbv

private def invalidFields : List FieldDetails :=
  [{
    fieldName := "values",
    arguments := [],
    selectionSet := [],
    directives := [.stream (.boolean true) none (.int (-1))]
  }]

private def invalidCut :=
  (RecordedExecution.completeListValueWithStream schema resolvers [] 7 itemType
    invalidFields streamSources [] [] [] true [0]).run
    7

private def invalidEager :=
  (EagerRecordedExecution.completeListValueWithStream schema resolvers [] 7 itemType
    invalidFields streamSources [] [] [] true [0]).run
    7

private def invalidInventory :=
  LiteralCuts.listWithStream schema resolvers [] 7 itemType invalidFields streamSources
    [] [] [] true [0] 7

private theorem invalid_stream_accounted
    : StreamCutAccounting invalidCut.1 invalidEager.1 invalidInventory :=
  (literalStreamAccounting_holds _ schema resolvers [] 7 itemType invalidFields
    streamSources [] [] [] true [0] 7 streamSources_literal).1

-- Invalid stream usage is the same primitive error on both sides, not a cut.
example : invalidInventory.sites = [] := by cbv

example : invalidCut.1.report.outcome = .ok (.null, 1) := by cbv

-----------------------------------------------------------------------------------------
-- Full value construction through outer non-null wrappers
-----------------------------------------------------------------------------------------

private def wrappedType (required : Bool) : GraphQL.TypeRef :=
  .nonNull (.list (if required then .nonNull itemType else itemType))

private def wrappedCut (required : Bool) (initialCount : Nat) :=
  (RecordedExecution.completeValue schema resolvers [] 8 (wrappedType required)
    (streamFields initialCount) values [] [] [] true []).run
    7

private def wrappedEager (required : Bool) (initialCount : Nat) :=
  (EagerRecordedExecution.completeValue schema resolvers [] 8 (wrappedType required)
    (streamFields initialCount) values [] [] [] true []).run
    7

private def wrappedInventory (required : Bool) (initialCount : Nat) :=
  LiteralCuts.streamValue schema resolvers [] 8 (wrappedType required)
    (streamFields initialCount) values [] [] [] true [] 7

private theorem wrapped_accounted (required : Bool) (initialCount : Nat)
    : StreamCutAccounting (wrappedCut required initialCount).1
        (wrappedEager required initialCount).1 (wrappedInventory required initialCount)
      ∧ CompletionOriginsRefine (wrappedCut required initialCount).1
          (wrappedEager required initialCount).1
      ∧ (wrappedCut required initialCount).2 = (wrappedEager required initialCount).2 :=
  literalValueCutAccounting_holds _ schema resolvers [] 8 (wrappedType required)
    (streamFields initialCount) values [] [] [] true [] 7 literal

example (required : Bool) (initialCount : Nat) (origin : Origin)
    (missing
      : origin
        ∈ omittedOrigins (wrappedCut required initialCount).1.origins
            (wrappedEager required initialCount).1.origins)
    : WithinCuts (wrappedInventory required initialCount).sites origin :=
  (wrapped_accounted required initialCount).1.omitted_origins origin missing

-- This is an exact partition of retained pure inventories, not the initial wire count.
example (required : Bool) (initialCount : Nat)
    : (wrappedCut required initialCount).1.origins.length
        + (omittedOrigins (wrappedCut required initialCount).1.origins
            (wrappedEager required initialCount).1.origins).length
      = (wrappedEager required initialCount).1.origins.length :=
  omittedOrigins_partition (wrapped_accounted required initialCount).2.1.origins
    (EagerScopes.completeValue_origins schema resolvers [] 8 (wrappedType required)
      (streamFields initialCount) values [] [] [] true [] 7).unique

-- Healthy outer non-null completion retains the stream, including future errors.
example
    : hasBoundary (wrappedCut false 0).1.work = true
      ∧ (wrappedInventory false 0).items.length = 2 := by cbv

-- Positive initial errors bubble without minting a wrapper origin or future sites.
example
    : (wrappedCut true 1).1.report.outcome = .error 1
      ∧ (wrappedEager true 1).1.report.outcome = .error 2
      ∧ (wrappedCut true 1).1.work = .empty
      ∧ (wrappedEager true 1).1.work = .empty
      ∧ (wrappedInventory true 1).items = [] := by cbv

-- Only the innermost unexplained null mints an origin; the outer wrapper reuses it.
example
    : ((RecordedExecution.completeValue schema resolvers [] 8
          (.nonNull (.nonNull (.named "String"))) [] .null [] [] [] true []).run
        7).1.report.origins
      = [([0], 0)] := by cbv

example
    : (LiteralCuts.streamValue schema resolvers [] 8
        (.nonNull (.nonNull (.named "String"))) [] (.null : ResolverValue Nat)
        [] [] [] true [] 7).sites
      = [] := by cbv

-- Fuel exhaustion is the same primitive error, before any stream can be inspected.
example
    : (LiteralCuts.streamValue schema resolvers [] 0 (wrappedType false)
        (streamFields 0) values [] [] [] true [] 7).sites
      = [] := by cbv

-- Non-null bubbling introduces a wrapper origin only when the child has no errors.
example : (Report.nonNull [9] (Report.pure ResponseValue.null)).origins = [([9], 0)] := by
  rfl

private def prior : Report ResponseValue := .fault [0, 0] (.ok (.null, 1))
private def fatal : Report ResponseValue := .fault [0, 1] (.error 1)
private def head : Report ResponseValue := .combine (fun _ _ => .null) prior fatal
private def tail : Report ResponseValue := .fault [1] (.error 1)

example : (head.nonNull [9]).origins = head.origins := by rfl
example : (head.nonNull [9]).outcome = .error 2 := by rfl

private theorem headScoped : Scoped [0] head.origins := by
  simpa only [head, Report.combine]
    using Scoped.join (Scoped.primitive [0, 0] 1) (Scoped.primitive [0, 1] 1)

-- The fatal cut preserves the preceding nullable error. Only the unexecuted tail is new omission.
example
    : omittedOrigins (head.map id).origins
        (Report.combine (fun _ _ => ResponseValue.null) head tail).origins
      = tail.origins := by
  have classified := fatal_cut_omitted (fun _ _ => ResponseValue.null) id tail []
    (eagerHead := head) headScoped (Scoped.primitive [1] 1)
  simpa only [omittedOrigins_self, List.nil_append] using classified

-- A subsequence relation alone still permits dropping the preceding error. Such a
-- missing head origin is NOT in the tail cone, so this is not a lawful sibling cut.
example : ReportRefines fatal head := by
  cbv
  decide

example : omittedOrigins fatal.origins head.origins = [([0, 0], 0)] := by rfl
example : ¬ [1].IsPrefix (omittedOrigins fatal.origins head.origins).head!.1 := by decide

#print axioms ReportRefines.nonNull
#print axioms CompletionOriginsRefine.fatal_cut
#print axioms ReportRefines.omitted_count
#print axioms fatal_cut_omitted_within
#print axioms literalNoStreamOriginsConstruction_holds
#print axioms literalOriginsConstruction_holds
#print axioms literalReachedCutOmission_holds
#print axioms literalReachedCutAccounting_holds
#print axioms constructed
#print axioms omissions_constructed
#print axioms stream_constructed
#print axioms literalStreamTailAccounting_holds
#print axioms ItemCutAccounting.omitted_origins
#print axioms ItemCutAccounting.cuts_positive
#print axioms tail_constructed
#print axioms tail_is_actual
#print axioms literalStreamAccounting_holds
#print axioms StreamCutAccounting.omitted_origins
#print axioms StreamCutAccounting.cuts_positive
#print axioms stream_accounted
#print axioms invalid_stream_accounted
#print axioms literalValueCutAccounting_holds
#print axioms StreamCutAccounting.nonNull
#print axioms wrapped_accounted

end AlternativeOriginCompositionChecks
