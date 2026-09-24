import GraphQL.IncrementalDelivery.WorkScheduler

/-! Correctness of incremental delivery relative to basic execution.
Read in order: directive erasure, finite observations, wire positions and ID lifecycle,
response reconstruction, then scheduler-quantified query statements. Wire definitions
do not depend on work admission or assume successful merging. Proof witnesses live
under Proofs/GraphQL/IncrementalDelivery/Correctness/.
-/

namespace GraphQL.IncrementalDelivery

-----------------------------------------------------------------------------------------
-- Incremental directive-freeness
-----------------------------------------------------------------------------------------

/-- Recognize defer/stream regardless of their activation conditions. -/
def DirectiveApplication.isIncremental : DirectiveApplication → Bool
  | .defer .. | .stream .. => true
  | .skip .. | .include .. => false

mutual
  /-- Inspect a selection's directives and all nested selections. -/
  def Selection.hasIncrementalDirectives : Selection → Bool
    | .field _ _ _ directives children | .inlineFragment _ directives children =>
        directives.any DirectiveApplication.isIncremental
        || SelectionSet.hasIncrementalDirectives children

  /-- A selection set is incremental when any selection contains defer/stream. -/
  def SelectionSet.hasIncrementalDirectives : List Selection → Bool
    | [] => false
    | selection :: rest =>
        selection.hasIncrementalDirectives || SelectionSet.hasIncrementalDirectives rest
end

/-- This is syntactic absence, including nested and inactive selections. @skip and
@include are allowed; even a disabled @defer or @stream violates this predicate.
-/
def Operation.incrementalDirectiveFree (operation : Operation) : Prop :=
  SelectionSet.hasIncrementalDirectives operation.selectionSet = false

instance (operation : Operation) : Decidable operation.incrementalDirectiveFree :=
  inferInstanceAs
    (Decidable (SelectionSet.hasIncrementalDirectives operation.selectionSet = false))

-----------------------------------------------------------------------------------------
-- Removing incremental directives
-----------------------------------------------------------------------------------------

/-- Preserve the basic directives, including their original condition expressions. -/
def DirectiveApplication.eraseIncremental?
    : DirectiveApplication → Option GraphQL.DirectiveApplication
  | .skip condition => some (.skip condition)
  | .include condition => some (.include condition)
  | .defer .. | .stream .. => none

mutual
  /-- Erase defer/stream while preserving the selection and its basic directives. -/
  def Selection.eraseIncrementalDirectives : Selection → GraphQL.Selection
    | .field responseName fieldName arguments directives children =>
        .field responseName fieldName arguments
          (directives.filterMap DirectiveApplication.eraseIncremental?)
          (SelectionSet.eraseIncrementalDirectives children)
    | .inlineFragment condition directives children =>
        .inlineFragment condition
          (directives.filterMap DirectiveApplication.eraseIncremental?)
          (SelectionSet.eraseIncrementalDirectives children)

  /-- Erase incremental directives recursively, preserving selection order. -/
  def SelectionSet.eraseIncrementalDirectives : List Selection → List GraphQL.Selection
    | [] => []
    | selection :: rest =>
        selection.eraseIncrementalDirectives
        :: SelectionSet.eraseIncrementalDirectives rest
end

/-- Explicit translation to the basic syntax. Preserve aliases, field/selection order,
arguments, type conditions, and variable definitions/defaults, even if erasure makes a
variable unused. Execution does not perform the unused-variable validation check.
-/
def Operation.eraseIncrementalDirectives (operation : Operation) : GraphQL.Operation :=
  {
    name := operation.name
    operationType := operation.operationType
    variableDefinitions := operation.variableDefinitions
    selectionSet := SelectionSet.eraseIncrementalDirectives operation.selectionSet
  }

namespace Execution

-----------------------------------------------------------------------------------------
-- Finite response observations
-----------------------------------------------------------------------------------------

/-- A finite observation of query execution. Unlike `ExecutionResult`, which retains a
resumable response-event stream, this type materializes only the updates observed so far.
-/
inductive ExecutionObservation where
  | single (response : Response)
  | incremental (initial : InitialIncrementalStreamResult)
    (subsequent : List IncrementalStreamUpdateResult)
deriving Repr

/-- An observation supplies one input to this stage. For a batched stream, that input is
itself a nonempty available group. Admission belongs to the upstream source.
-/
def ResponseEventStream.Accepts (stream : ResponseEventStream) (input : stream.Input)
    : Prop :=
  stream.source.Allows [input]

/-- Deterministic state update after an admissible observation. This does not choose what
becomes available next; several inputs may satisfy Accepts at the same state.
-/
def ResponseEventStream.next (stream : ResponseEventStream) (input : stream.Input)
    (_allowed : stream.Accepts input)
    : IncrementalStreamUpdateResult × ResponseEventStream :=
  let result := (stream.mapEvent input).run stream.ids
  (result.1, { stream with source := stream.source.advance [input], ids := result.2 })

/-- Single-threaded observation: accept an available batch, update the partial source
history and mapper IDs, then repeat. Stopping observation does not assert termination.
-/
inductive ResponseEventStream.Observes
    : ResponseEventStream → List IncrementalStreamUpdateResult → ResponseEventStream
      → Prop where
  | nil (stream) : Observes stream [] stream
  | cons (stream batches) (allowed : stream.Accepts batches)
    {updates final}
    (rest : Observes (stream.next batches allowed).2 updates final)
    : Observes stream ((stream.next batches allowed).1 :: updates) final

/-- complete=false includes stalled/interrupted observations; complete=true additionally
requires source termination, independently of response lifecycle or merge predicates.
-/
def ExecutionResult.Observes (execution : ExecutionResult) (result : ExecutionObservation)
    (complete : Bool := false)
    : Prop :=
  match execution, result with
  | .single response, .single observed => response = observed
  | .incremental initial stream, .incremental observed updates =>
      initial = observed
      ∧ ∃ final,
          stream.Observes updates final ∧ (complete = true → final.source.IsFinished)
  | _, _ => False

-----------------------------------------------------------------------------------------
-- Response positions
-----------------------------------------------------------------------------------------

namespace ResponsePositions

mutual
  /-- Absolute paths use response aliases and zero-based indices. Container roots are
  optional; without them only scalar/null leaves are included.
  -/
  def value (containers : Bool) (path : ResponsePath) : ResponseValue → List ResponsePath
    | .null | .scalar _ => [path]
    | .object data => (if containers then [path] else []) ++ fields containers path data
    | .list data => (if containers then [path] else []) ++ items containers path 0 data

  /-- Field contributions omit the enclosing object, which is already present. -/
  def fields (containers : Bool) (path : ResponsePath)
      : List (Name × ResponseValue) → List ResponsePath
    | [] => []
    | (name, data) :: rest =>
        value containers (path ++ [.field name]) data ++ fields containers path rest

  /-- List contributions begin at the supplied append index and omit the parent list. -/
  def items (containers : Bool) (path : ResponsePath) (index : Nat)
      : List ResponseValue → List ResponsePath
    | [] => []
    | data :: rest =>
        value containers (path ++ [.index index]) data
        ++ items containers path (index + 1) rest
end

-----------------------------------------------------------------------------------------
-- Stream position cursors
-----------------------------------------------------------------------------------------

/-- The next append index of every list introduced by the observed payloads. New entries
precede old ones, so later payloads replace a previous cursor at the same path. This
tracks wire positions without assuming successful merging. Cursors are historical
observations, not validation of current attachment shapes.
-/
abbrev Cursors := List (ResponsePath × Nat)

/-- Read the newest cursor for a list path. -/
def cursorAt (cursors : Cursors) (path : ResponsePath) : Option Nat :=
  (cursors.find? (fun entry => entry.1 == path)).map Prod.snd

mutual
  /-- Each list introduces its current length and the cursors nested inside it. -/
  def listCursors (path : ResponsePath) : ResponseValue → Cursors
    | .null | .scalar _ => []
    | .object data => fieldCursors path data
    | .list data => (path, data.length) :: itemCursors path 0 data

  /-- Collect cursors introduced by object fields at their absolute paths. -/
  def fieldCursors (path : ResponsePath) : List (Name × ResponseValue) → Cursors
    | [] => []
    | (name, data) :: rest =>
        listCursors (path ++ [.field name]) data ++ fieldCursors path rest

  /-- Collect nested cursors from list items beginning at the supplied append index. -/
  def itemCursors (path : ResponsePath) (index : Nat) : List ResponseValue → Cursors
    | [] => []
    | data :: rest =>
        listCursors (path ++ [.index index]) data ++ itemCursors path (index + 1) rest
end

end ResponsePositions

-----------------------------------------------------------------------------------------
-- Wire delivery slices
-----------------------------------------------------------------------------------------

/-- The one notified owner ID of a payload, not all defer IDs sharing its selection. -/
def IncrementalResult.id : IncrementalResult → String
  | .object id _ _ _ | .list id _ _ => id

/-- Count the errors carried by this payload. -/
def IncrementalResult.errors : IncrementalResult → Nat
  | .object _ _ errors _ | .list _ _ errors => errors

namespace DeliveryTrace

open ResponsePositions

/-- Decode one payload using an already available owner notice. Stream indices start at
the current observed list length, not zero or initialCount, and advance per received item.
Missing owners or stream cursors return none; lifecycle and attachment are not checked.
-/
def decodePatch (containers : Bool) (notices : List IncrementalPendingNotice)
    (cursors : Cursors) (patch : IncrementalResult)
    : Option (List ResponsePath × Cursors) := do
  let notice ← notices.find? (fun notice => notice.id == patch.id)
  match patch with
  | .object _ data _ subPath =>
      return (
        fields containers (notice.path ++ subPath) data,
        fieldCursors (notice.path ++ subPath) data ++ cursors
      )
  | .list _ data _ =>
      let index ← cursorAt cursors notice.path
      return (
        items containers notice.path index data,
        (notice.path, index + data.length) :: itemCursors notice.path index data
        ++ cursors
      )

/-- Decode supplied patches in order, retaining one slice per payload and threading
cursors.
-/
def decodePatches (containers : Bool) (notices : List IncrementalPendingNotice)
    (cursors : Cursors)
    : List IncrementalResult → Option (List (List ResponsePath) × Cursors)
  | [] => some ([], cursors)
  | patch :: rest => do
      let (head, middle) ← decodePatch containers notices cursors patch
      let (tail, final) ← decodePatches containers notices middle rest
      return (head :: tail, final)

/-- Decode supplied updates using only earlier or same-update notices. Future updates
cannot resolve an earlier payload's missing owner or cursor.
-/
def decodeUpdates (containers : Bool) (notices : List IncrementalPendingNotice)
    (cursors : Cursors)
    : List IncrementalStreamUpdateResult → Option (List (List ResponsePath) × Cursors)
  | [] => some ([], cursors)
  | update :: rest => do
      let available := notices ++ update.pending
      let (head, middle) ← decodePatches containers available cursors update.incremental
      let (tail, final) ← decodeUpdates containers available middle rest
      return (head ++ tail, final)

end DeliveryTrace

/-- Decode initial data and observed payloads into delivery slices. This deterministic
replay neither selects future events nor validates lifecycle or successful merging.
-/
def ExecutionObservation.decodeSlices (containers : Bool)
    : ExecutionObservation → Option (List (List ResponsePath))
  | .single response => some [ResponsePositions.value containers [] response.data]
  | .incremental initial subsequent => do
      let (tail, _) ←
        DeliveryTrace.decodeUpdates containers initial.pending
          (ResponsePositions.listCursors [] initial.data) subsequent
      return ResponsePositions.value containers [] initial.data :: tail

/-- Delivery slices are exactly the successful output of the causal wire decoder.
No work history, future notice, lifecycle predicate, or merge premise is inspected.
-/
def ExecutionObservation.DeliversSlices (result : ExecutionObservation)
    (containers : Bool) (slices : List (List ResponsePath))
    : Prop :=
  result.decodeSlices containers = some slices

-----------------------------------------------------------------------------------------
-- Wire IDs, causal references, and liveness
-----------------------------------------------------------------------------------------

namespace DeliveryTrace

/-- All announcements in response order, retaining duplicate occurrences. -/
def pendingIDs (updates : List IncrementalStreamUpdateResult) : List String :=
  updates.flatMap (fun update => update.pending.map IncrementalPendingNotice.id)

/-- All completion notices in response order, including distinct IDs sharing data. -/
def completedIDs (updates : List IncrementalStreamUpdateResult) : List String :=
  updates.flatMap (fun update => update.completed.map IncrementalCompletionNotice.id)

/-- Causal ID resolution only: an announcement must be in an earlier or the same update.
This does not assert that the ID is still open or its path can be merged.
-/
def patchesAnnounced (prior : List String) : List IncrementalStreamUpdateResult → Prop
  | [] => True
  | update :: rest =>
      let available := prior ++ update.pending.map IncrementalPendingNotice.id
      (∀ patch ∈ update.incremental, patch.id ∈ available)
      ∧ patchesAnnounced available rest

/-- A completion before an announcement cannot discharge that announcement. -/
def announcementsEventuallyComplete : List IncrementalStreamUpdateResult → Prop
  | [] => True
  | update :: rest =>
      (∀ id ∈ update.pending.map IncrementalPendingNotice.id,
        id ∈ completedIDs (update :: rest))
      ∧ announcementsEventuallyComplete rest

/-- One ID-safety checker, shared by prefix safety and complete lifecycle validity.
Same-update announcements precede patches, which precede completions.
-/
def idUsageValid (seen active : List String) : List IncrementalStreamUpdateResult → Bool
  | [] => true
  | update :: rest =>
      let fresh := update.pending.map IncrementalPendingNotice.id
      let completed := update.completed.map IncrementalCompletionNotice.id
      let available := active ++ fresh
      fresh.all (fun id => !seen.contains id)
      && decide fresh.Nodup
      && decide completed.Nodup
      && completed.all available.contains
      && update.incremental.all (fun patch => available.contains patch.id)
      && idUsageValid (seen ++ fresh)
          (available.filter (fun id => !completed.contains id)) rest

/-- hasNext concerns later responses, independently of which IDs remain open. -/
def hasNextValid : List IncrementalStreamUpdateResult → Bool
  | [] => true
  | update :: rest => update.hasNext == !rest.isEmpty && hasNextValid rest

end DeliveryTrace

namespace ExecutionObservation

/-- Uniqueness is across the entire announcement history, including completed IDs. -/
def idsUnique : ExecutionObservation → Prop
  | .single _ => True
  | .incremental initial subsequent =>
      (initial.pending.map IncrementalPendingNotice.id
        ++ DeliveryTrace.pendingIDs subsequent).Nodup

/-- Every payload references an earlier or same-update announcement. -/
def patchesAnnounced : ExecutionObservation → Prop
  | .single _ => True
  | .incremental initial subsequent =>
      DeliveryTrace.patchesAnnounced
        (initial.pending.map IncrementalPendingNotice.id) subsequent

/-- Announcements are fresh, and payloads/completions refer only to open IDs. -/
def idUsageValid : ExecutionObservation → Prop
  | .single _ => True
  | .incremental initial subsequent =>
      let ids := initial.pending.map IncrementalPendingNotice.id
      ids.Nodup ∧ DeliveryTrace.idUsageValid ids ids subsequent = true

/-- Count completion notices, not payloads: shared data may notify several distinct IDs.
-/
def idsCompleteExactlyOnce : ExecutionObservation → Prop
  | .single _ => True
  | .incremental initial subsequent =>
      ∀ id ∈
        initial.pending.map IncrementalPendingNotice.id
        ++ DeliveryTrace.pendingIDs subsequent,
        (DeliveryTrace.completedIDs subsequent).count id = 1

/-- Eventual completion is weaker than full lifecycle validity: it does not assert unique
IDs/completions, open-ID patch legality, or correct hasNext bookkeeping.
-/
def idsEventuallyComplete : ExecutionObservation → Prop
  | .single _ => True
  | .incremental initial subsequent =>
      (∀ id ∈ initial.pending.map IncrementalPendingNotice.id,
        id ∈ DeliveryTrace.completedIDs subsequent)
      ∧ DeliveryTrace.announcementsEventuallyComplete subsequent

-----------------------------------------------------------------------------------------
-- Delivery completion and execution errors
-----------------------------------------------------------------------------------------

/-- Complete delivery combines ID safety, closure of every announcement, and the
response-continuation flags. A termination-only final response is permitted.
-/
def deliveryComplete : ExecutionObservation → Bool
  | .single _ => true
  | .incremental initial subsequent =>
      let ids := initial.pending.map IncrementalPendingNotice.id
      !ids.isEmpty
      && decide ids.Nodup
      && DeliveryTrace.idUsageValid ids ids subsequent
      && (ids ++ DeliveryTrace.pendingIDs subsequent).all
          (DeliveryTrace.completedIDs subsequent).contains
      && initial.hasNext == !subsequent.isEmpty
      && DeliveryTrace.hasNextValid subsequent

/-- Count errors from every envelope, patch, and completion notice. Failed shared groups
can report errors under multiple IDs; no error-identity deduplication exists in this
count-only model.
-/
def totalErrors : ExecutionObservation → Nat
  | .single response => response.errors
  | .incremental initial subsequent =>
      initial.errors
      + (subsequent.map
          (fun update =>
            (update.incremental.map IncrementalResult.errors).sum
            + (update.completed.map IncrementalCompletionNotice.errors).sum)).sum

/-- Successful complete delivery: the lifecycle closes and no execution error is counted.
Closing IDs alone permits discarded fields/items or cancelled work. Zero errors also
excludes reported fuel exhaustion. Merge success, response equivalence, and parent-before-
child attachment are conclusions of the correctness proofs, not premises here.
-/
def executionComplete (result : ExecutionObservation) : Prop :=
  result.deliveryComplete = true ∧ result.totalErrors = 0

end ExecutionObservation

instance (result : ExecutionObservation) : Decidable result.executionComplete :=
  inferInstanceAs (Decidable (result.deliveryComplete = true ∧ result.totalErrors = 0))

-----------------------------------------------------------------------------------------
-- Response reconstruction
-----------------------------------------------------------------------------------------

namespace ResponseMerging

/-- Traverse response aliases and list indices. A patch cannot create a missing parent or
descend through null; such a trace cannot be reconstructed by this merger.
-/
def modifyAtPath (path : ResponsePath) (modify : ResponseValue → Option ResponseValue)
    (value : ResponseValue)
    : Option ResponseValue :=
  match path, value with
  | [], value => modify value
  | .field name :: rest, .object fields => do
      let field ← fields.find? (fun field => field.fst == name)
      let updated ← modifyAtPath rest modify field.snd
      return .object
        (fields.map
          (fun field =>
            if field.fst == name then (name, updated) else field))
  | .index index :: rest, .list items => do
      let item ← items[index]?
      let updated ← modifyAtPath rest modify item
      return .list (items.set index updated)
  | _, _ => none

/-- Object payloads supply fields at their resolved path; other fields remain present.
Nested deferred payloads target their own paths rather than replacing ancestors.
-/
def putFields (fields incoming : List (Name × ResponseValue))
    : List (Name × ResponseValue) :=
  incoming.foldl
    (fun current field =>
      if current.any (fun existing => existing.fst == field.fst) then
        current.map
          (fun existing => if existing.fst == field.fst then field else existing)
      else
        current ++ [field])
    fields

/-- Resolve the owner ID, then insert object fields or append stream items at its path. -/
def applyPatch (notices : List IncrementalPendingNotice) (value : ResponseValue)
    (patch : IncrementalResult)
    : Option ResponseValue := do
  let notice ← notices.find? (fun notice => notice.id == patch.id)
  match patch with
  | .object _ fields _ subPath =>
      modifyAtPath (notice.path ++ subPath)
        (fun value =>
          match value with
          | .object existing => some (.object (putFields existing fields))
          | _ => none) value
  | .list _ items _ =>
      modifyAtPath notice.path
        (fun value =>
          match value with
          | .list existing => some (.list (existing ++ items))
          | _ => none) value

/-- Notices resolve paths; ID safety is checked separately. Reconstruction changes only
data. All envelope/patch/completion errors are counted once by totalErrors.
-/
def applyUpdate (state : ResponseValue × List IncrementalPendingNotice)
    (update : IncrementalStreamUpdateResult)
    : Option (ResponseValue × List IncrementalPendingNotice) := do
  let notices := state.2 ++ update.pending
  let data ← update.incremental.foldlM (applyPatch notices) state.1
  return (data, notices)

end ResponseMerging

/-- Reconstruct data in delivery order using IDs as path references, not fragment
membership. Reject unfinished/malformed lifecycles and patches at invalid paths. Failed
deliveries may still merge to partial data with errors; merging does not undo already
delivered data or simulate basic execution's different null bubbling.
-/
def mergeExecutionObservation (result : ExecutionObservation) : Option Response :=
  if !result.deliveryComplete then
    none
  else
    match result with
    | .single response => some response
    | .incremental initial subsequent => do
        let (data, _) ←
          subsequent.foldlM ResponseMerging.applyUpdate (initial.data, initial.pending)
        return { data, errors := result.totalErrors }

end Execution

namespace Correctness

open GraphQL.IncrementalDelivery.Execution (
  Resolvers ResolverValue VariableValues ExecutionObservation)

-----------------------------------------------------------------------------------------
-- Query observations under the scheduler contract
-----------------------------------------------------------------------------------------

/-- The invariant is local to the work this query actually submits. Invalid roots and
ordinary responses do not use a work queue; unrelated raw Work is irrelevant.
-/
def queryObservation (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef) (result : ExecutionObservation)
    (complete : Bool := false)
    : Prop :=
  ∃ scheduler : Execution.WorkScheduler,
    (Execution.rootSourceAppliesBool schema operation source = true
      → let prepared := Execution.coerceVariableValues operation variables
        let completed :=
          ((Execution.executeRootSelectionSetCore schema resolvers prepared fuel
              (operation.rootType schema) source operation.selectionSet).run
            0).1
        scheduler.Conforms completed.work)
    ∧ (Execution.executeQueryWithFuel scheduler schema resolvers variables operation fuel
        source).Observes
        result complete

/-- Complete observations use the same definition, additionally requiring termination.
Prefix observations permit an interrupted or stalled computation.
-/
def queryOutcome (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef) (result : ExecutionObservation)
    : Prop :=
  queryObservation schema resolvers variables operation fuel source result true

-----------------------------------------------------------------------------------------
-- Correctness statements: defer/stream-free operation
-----------------------------------------------------------------------------------------

/-- Ordinary execution is independent of the supplied factory, even before conformance.
Witness: incrementalDirectiveFreeExecutionEquivalentToBasic_holds in Correctness/Query,
via work-free execution.
-/
def incrementalDirectiveFreeExecutionEquivalentToBasic (schema : Schema)
    (operation : Operation)
    : Prop :=
  operation.incrementalDirectiveFree
  → ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
      variables fuel (source : ResolverValue ObjectRef)
      (scheduler : Execution.WorkScheduler),
      Execution.executeQueryWithFuel scheduler schema resolvers variables operation fuel
        source
      = .single
          (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
            operation.eraseIncrementalDirectives fuel source)

-----------------------------------------------------------------------------------------
-- Correctness statements: all observed prefixes
-----------------------------------------------------------------------------------------

/-- Every observed prefix has unique IDs. Witness: deliveryIDsUnique_holds in
Correctness/QueryIdentity, via key uniqueness and injective stable allocation.
-/
def deliveryIDsUnique (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryObservation schema resolvers variables operation fuel source result
    → result.idsUnique

/-- Patches refer to announced IDs. Witness: deliveryPatchesAnnounced_holds in
Correctness/QueryIDUsage, derived from the stronger open-ID safety statement.
-/
def deliveryPatchesAnnounced (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryObservation schema resolvers variables operation fuel source result
    → result.patchesAnnounced

/-- Prefixes obey open-ID safety. Witness: deliveryIDUsageValid_holds in
Correctness/QueryIDUsage, via work references, stable allocation, and batching.
-/
def deliveryIDUsageValid (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryObservation schema resolvers variables operation fuel source result
    → result.idUsageValid

/-- All delivered paths are globally unique: each slice is internally unique and
distinct slices do not overlap.
Witness: deliverySlicesDisjoint_holds in Correctness/QueryDisjointness, from source
ownership, causal stream cursors, stable IDs, and batching preservation.
-/
def deliverySlicesDisjoint (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef) variables fuel
    (source : ResolverValue ObjectRef) result (containers : Bool),
    queryObservation schema resolvers variables operation fuel source result
    → ∃ slices, result.DeliversSlices containers slices ∧ slices.flatten.Nodup

-----------------------------------------------------------------------------------------
-- Correctness statements: complete finite runs
-----------------------------------------------------------------------------------------

/-- Every modeled query has some complete finite outcome, including failures and exhausted
fuel. This does not require every admitted prefix or every conforming source to complete.
Witness: queryOutcomeExists_holds in Correctness/QueryOutcomeExistence, via generated-work
progress and actual response realization. No scheduler or successful-run premise is used.
-/
def queryOutcomeExists (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef),
    ∃ result, queryOutcome schema resolvers variables operation fuel source result

/-- Liveness is conditional on a complete finite work run. It does not assert that an
arbitrary asynchronous resolver or unfair scheduler eventually produces such a run.
Witness: deliveryIDsEventuallyComplete_holds in Correctness/QueryIdentity.
-/
def deliveryIDsEventuallyComplete (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryOutcome schema resolvers variables operation fuel source result
    → result.idsEventuallyComplete

/-- Each announced ID completes exactly once in terminal observations. Witness:
deliveryIDsCompleteExactlyOnce_holds in Correctness/QueryIdentity, by uniqueness/liveness.
-/
def deliveryIDsCompleteExactlyOnce (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryOutcome schema resolvers variables operation fuel source result
    → result.idsCompleteExactlyOnce

/-- Complete runs satisfy the whole lifecycle checker. Witness:
deliveryLifecycleValid_holds in Correctness/QueryLifecycle, via safety and final-marker
control independent of the number of open IDs.
-/
def deliveryLifecycleValid (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryOutcome schema resolvers variables operation fuel source result
    → result.deliveryComplete = true

-----------------------------------------------------------------------------------------
-- Correctness statements: successful complete execution
-----------------------------------------------------------------------------------------

/-- Successful complete outcomes merge to the ordinary directive-erased response.
Only zero errors is assumed beyond queryOutcome; delivery lifecycle validity is proved.
Witness: mergedExecutionEquivalentToBasic_holds in Correctness/QueryReconstruction,
via causal attachments, actual wire merging, and typed source equivalence. Correctness
quantifies over the independent scheduler contract; it is not an admission condition.
-/
def mergedExecutionEquivalentToBasic (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryOutcome schema resolvers variables operation fuel source result
    → result.totalErrors = 0
    → ∃ response,
        Execution.mergeExecutionObservation result = some response
        ∧ GraphQL.Execution.Response.semanticEquivalent response
            (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
              operation.eraseIncrementalDirectives fuel source)

/-- Successful complete outcomes deliver exactly the ordinary execution's positions.
Only zero errors is assumed beyond queryOutcome; delivery lifecycle validity is proved.
Witness: deliveredResponsePositionsEquivalentToBasic_holds in Correctness/QueryCoverage,
via typed source reconstruction and schedule-independent full wire coverage.
-/
def deliveredResponsePositionsEquivalentToBasic (schema : Schema) (operation : Operation)
    : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryOutcome schema resolvers variables operation fuel source result
    → result.totalErrors = 0
    → ∀ containers,
        ∃ slices,
          result.DeliversSlices containers slices
          ∧ slices.flatten.Perm
              (Execution.ResponsePositions.value containers []
                (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
                  operation.eraseIncrementalDirectives fuel source).data)

/-- Every ordinary scalar/null leaf occurs exactly once in successful complete delivery.
Only zero errors is assumed beyond queryOutcome; delivery lifecycle validity is proved.
Witness: basicLeavesDeliveredExactlyOnce_holds in Correctness/QueryCoverage, by position
coverage and ordinary response-path uniqueness.
-/
def basicLeavesDeliveredExactlyOnce (schema : Schema) (operation : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variables fuel (source : ResolverValue ObjectRef) result,
    queryOutcome schema resolvers variables operation fuel source result
    → result.totalErrors = 0
    → ∃ slices,
        result.DeliversSlices false slices
        ∧ ∀ path ∈
            Execution.ResponsePositions.value false []
              (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
                operation.eraseIncrementalDirectives fuel source).data,
            slices.flatten.count path = 1

end Correctness
end GraphQL.IncrementalDelivery
