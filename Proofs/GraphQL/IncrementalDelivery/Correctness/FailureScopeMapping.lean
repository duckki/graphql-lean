import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureScopes
import Proofs.GraphQL.IncrementalDelivery.Correctness.NoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureReportOrigins

/-! Positive-error work completions retain their identities and client-visible scopes. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

-----------------------------------------------------------------------------------------
-- Successful wire decoding retains every error-bearing completion
-----------------------------------------------------------------------------------------

/-- A successful Option traversal contains the image of each supplied element.
Witness: list induction inverts the successful head and tail computations.
-/
private theorem option_mapM_member {α β : Type} {values : List α} {f : α → Option β}
    {outputs : List β} (mapped : values.mapM f = some outputs)
    {value : α} (member : value ∈ values)
    : ∃ output, f value = some output ∧ output ∈ outputs := by
  induction values generalizing outputs with
  | nil => simp at member
  | cons head tail ih =>
      cases current : f head with
      | none => simp [List.mapM_cons, current] at mapped
      | some output =>
          cases rest : tail.mapM f with
          | none => simp [List.mapM_cons, current, rest] at mapped
          | some subsequent =>
              have equal : output :: subsequent = outputs := by
                simpa [List.mapM_cons, current, rest] using mapped
              subst outputs
              rcases List.mem_cons.mp member with rfl | included
              · exact ⟨output, current, by simp⟩
              · obtain ⟨next, found, present⟩ := ih rest included
                exact ⟨next, found, List.mem_cons_of_mem _ present⟩

/-- A decoded failure list includes the path of every positive-error completion.
Witness: successful traversal supplies its available notice; consistent notice metadata
identifies its path. Future notices are used only for metadata, never for ID lookup.
-/
theorem collectFailureScopes_contains {notices : List IncrementalPendingNotice}
    {updates : List IncrementalStreamUpdateResult} {scopes : List ResponsePath}
    (decoded : DeliveryTrace.collectFailureScopes notices updates = some scopes)
    {update : IncrementalStreamUpdateResult} (member : update ∈ updates)
    {completion : IncrementalCompletionNotice} (completed : completion ∈ update.completed)
    (positive : 0 < completion.errors) {scope : ResponsePath}
    (metadata
      : ∀ notice ∈ notices ++ updates.flatMap IncrementalStreamUpdateResult.pending,
          notice.id = completion.id → notice.path = scope)
    : scope ∈ scopes := by
  induction updates generalizing notices scopes with
  | nil => simp at member
  | cons head tail ih =>
      let available := notices ++ head.pending
      let decode := fun entry : IncrementalCompletionNotice => do
        let notice ← available.find? (fun notice : IncrementalPendingNotice =>
          notice.id == entry.id)
        return notice.path
      change ((head.completed.filter (fun entry => entry.errors > 0)).mapM decode |>.bind
        fun found => (DeliveryTrace.collectFailureScopes available tail).bind
          fun subsequent => some (found ++ subsequent)) = some scopes at decoded
      cases current
            : (head.completed.filter (fun entry => entry.errors > 0)).mapM decode with
      | none => simp only [current, Option.bind_none, reduceCtorEq] at decoded
      | some found =>
          cases rest : DeliveryTrace.collectFailureScopes available tail with
          | none =>
              simp only [current, rest, Option.bind_some, Option.bind_none, reduceCtorEq]
                at decoded
          | some subsequent =>
              have equal : found ++ subsequent = scopes := by
                simpa only [current, rest, Option.bind_some, Option.some.injEq]
                  using decoded
              subst scopes
              rcases List.mem_cons.mp member with rfl | later
              · obtain ⟨path, lookup, included⟩ := option_mapM_member current
                  (List.mem_filter.mpr ⟨completed, by simpa using positive⟩)
                cases noticeFound
                      : available.find? (fun notice => notice.id == completion.id) with
                | none => simp [decode, noticeFound] at lookup
                | some notice =>
                    have same : notice.path = path := by simpa [decode, noticeFound] using lookup
                    have visible : notice ∈ available := List.mem_of_find?_eq_some noticeFound
                    have noticeScope := metadata notice (by
                      simp only [List.flatMap_cons, ← List.append_assoc]
                      exact List.mem_append_left _ visible)
                      (by simpa using List.find?_some noticeFound)
                    rw [← same, noticeScope] at included
                    exact List.mem_append_left _ included
              · apply List.mem_append_right
                apply ih rest later
                intro notice included sameID
                apply metadata notice _ sameID
                simpa only [available, List.flatMap_cons, List.append_assoc] using included

-----------------------------------------------------------------------------------------
-- The response mapper retains exact failure identities and counts
-----------------------------------------------------------------------------------------

/-- Mapping a failure event adds its exact positive or zero error count under a stable ID.
Witness: getCompletedEntry allocates the node ID and copies the supplied error count.
-/
theorem eventLoop_failureCompletion {event : WorkQueueEvent} {node : DeliveryNode}
    {errors : Nat}
    (failure : event = .groupFailure node errors ∨ event = .streamFailure node errors)
    {initial update : IncrementalStreamUpdateResult} {ids next : IDState}
    (mapped : (eventLoop event initial).run ids = (.yield update, next))
    : ∃ completion ∈ update.completed,
        Known next node.ref completion.id ∧ completion.errors = errors := by
  rcases failure with rfl | rfl
  all_goals
    cases allocated
        : (getCompletedEntry (m := StateM IDState) node errors ensureID).run ids with
    | mk completion final =>
        have known := (getCompletedEntry_of_eq allocated).2
        have count : completion.errors = errors := by
          have copied : ((getCompletedEntry (m := StateM IDState) node errors ensureID).run
              ids).1.errors = errors := rfl
          simpa only [allocated] using copied
        simp only [StateT.run] at allocated
        simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure,
          allocated] at mapped
        cases mapped
        exact ⟨completion, by simp, known, count⟩

/-- Mapper-loop traversal retains each failure completion and its ID in the final state.
Witness: event induction, append-only completion accumulation, and stable allocation.
-/
theorem loop_failureCompletion {events : List WorkQueueEvent} {node : DeliveryNode}
    {errors : Nat}
    (failure : .groupFailure node errors ∈ events ∨ .streamFailure node errors ∈ events)
    (initial : IncrementalStreamUpdateResult) (ids : IDState)
    : ∃ completion ∈ ((forIn events initial eventLoop).run ids).1.completed,
        Known ((forIn events initial eventLoop).run ids).2 node.ref completion.id
        ∧ completion.errors = errors := by
  induction events generalizing initial ids with
  | nil => simp at failure
  | cons event rest ih =>
      obtain ⟨middle, next, mapped, _⟩ := eventLoop_spec event initial ids
      obtain ⟨update, final, replayed, spec⟩ := loop_spec rest middle next
      have equation : (forIn (event :: rest) initial eventLoop).run ids = (update, final) := by
        simp only [StateT.run] at mapped replayed
        simp only [List.forIn_cons, StateT.run, StateT.bind, bind, mapped, replayed]
      rw [equation]
      have located : (event = .groupFailure node errors ∨ event = .streamFailure node errors)
          ∨ (.groupFailure node errors ∈ rest ∨ .streamFailure node errors ∈ rest) := by
        simpa only [List.mem_cons, eq_comm, or_assoc, or_left_comm, or_comm] using failure
      rcases located with current | subsequent
      · obtain ⟨completion, member, known, count⟩ :=
          eventLoop_failureCompletion current mapped
        obtain ⟨added, completed, _⟩ := spec.completed
        exact ⟨completion, completed ▸ List.mem_append_left added member,
          spec.preserves _ _ known, count⟩
      · have tail := ih subsequent middle next
        simpa only [replayed] using tail

/-- One work batch retains each failure's node identity and exact error count.
Witness: the public batch mapper is the proved append-only mapper loop.
-/
theorem mapWorkEventBatch_failureCompletion {events : List WorkQueueEvent}
    {node : DeliveryNode} {errors : Nat}
    (failure : .groupFailure node errors ∈ events ∨ .streamFailure node errors ∈ events)
    (ids : IDState)
    : ∃ completion ∈ ((mapWorkEventBatch events).run ids).1.completed,
        Known ((mapWorkEventBatch events).run ids).2 node.ref completion.id
        ∧ completion.errors = errors := by
  rw [mapWorkEventBatch_loop]
  exact loop_failureCompletion failure { hasNext := true } ids

/-- Finite batch replay retains every failure completion under its final stable identity.
Witness: batch induction transports earlier identities through all later allocations.
-/
theorem mappedTrace_failureCompletion {batches : List (List WorkQueueEvent)}
    {node : DeliveryNode} {errors : Nat}
    (failure
      : .groupFailure node errors ∈ batches.flatten
        ∨ .streamFailure node errors ∈ batches.flatten)
    (ids : IDState)
    : ∃ completion ∈
        (mappedTrace batches ids).flatMap IncrementalStreamUpdateResult.completed,
        Known (finalIDs batches ids) node.ref completion.id
        ∧ completion.errors = errors := by
  induction batches generalizing ids with
  | nil => simp at failure
  | cons batch rest ih =>
      cases mapped : (mapWorkEventBatch batch).run ids with
      | mk update next =>
          have located : (.groupFailure node errors ∈ batch
                ∨ .streamFailure node errors ∈ batch)
              ∨ (.groupFailure node errors ∈ rest.flatten
                ∨ .streamFailure node errors ∈ rest.flatten) := by
            simpa only [List.flatten_cons, List.mem_append, or_assoc, or_left_comm,
              or_comm]
              using failure
          simp only [mappedTrace, finalIDs, mapped, List.flatMap_cons]
          rcases located with current | subsequent
          · obtain ⟨completion, member, known, count⟩ :=
              mapWorkEventBatch_failureCompletion current ids
            simp only [mapped] at member known
            exact ⟨completion, List.mem_append_left _ member,
              (mappedTrace_spec rest next).1 _ _ known, count⟩
          · obtain ⟨completion, member, known, count⟩ := ih subsequent next
            exact ⟨completion, List.mem_append_right _ member, known, count⟩

-----------------------------------------------------------------------------------------
-- Response batching and wire-scope reconstruction
-----------------------------------------------------------------------------------------

/-- Combining responses concatenates their full completion notices, not just counts.
Witness: aggregation-fold induction preserves the exact IDs and error fields.
-/
theorem combineFrom_completed (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : (combineFrom updates initial).completed
      = initial.completed ++ updates.flatMap IncrementalStreamUpdateResult.completed := by
  induction updates generalizing initial with
  | nil => simp [combineFrom]
  | cons update rest ih =>
      simpa [combineFrom, List.append_assoc] using ih
        { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
          incremental := initial.incremental ++ update.incremental,
          completed := initial.completed ++ update.completed }

/-- Arbitrary response coalescing preserves every exact completion descriptor.
Witness: each group concatenates completions; group induction preserves the full list.
-/
theorem batched_completed (groups : List (List IncrementalStreamUpdateResult))
    : (groups.map combineIncrementalResults).flatMap
        IncrementalStreamUpdateResult.completed
      = groups.flatten.flatMap IncrementalStreamUpdateResult.completed := by
  have one (updates : List IncrementalStreamUpdateResult)
      : (combineIncrementalResults updates).completed
        = updates.flatMap IncrementalStreamUpdateResult.completed := by
    simpa only [combineFrom, combineIncrementalResults, List.nil_append]
      using combineFrom_completed updates { hasNext := false }
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.flatten_cons, List.flatMap_append,
        one, ih]

/-- Consistent notices sharing a completion ID have that completion node's exact path.
Witness: injectivity of stable allocation identifies the node reference, then metadata
identifies its path. This does not assume a particular lookup or notice order.
-/
theorem NoticePaths.same_id {paths ids notices} (metadata : NoticePaths paths ids notices)
    (allocated : Allocated ids) {node : DeliveryNode} {id : String}
    (known : Known ids node.ref id) (path : paths node.ref = node.path)
    {notice : IncrementalPendingNotice} (member : notice ∈ notices)
    (same : notice.id = id)
    : notice.path = node.path := by
  obtain ⟨ref, noticeKnown, noticePath⟩ := metadata notice member
  rw [same] at noticeKnown
  have equal := Known.injective allocated noticeKnown known
  rw [equal] at noticePath
  exact noticePath.symm.trans path

/-- Every reported work-level attachment scope appears in the replay's decoded wire
failure scopes. Witness: exact failure completions survive mapping and response batching;
stable IDs and generated notice paths identify the client-visible scope.
-/
theorem replayResponse_reportedScope
    {paths bound response work groups streams batches scopes path}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (admitted : WorkQueueSemantics.ValidHistory work ⟨groups, streams, batches.flatten⟩)
    (decoded
      : (replayResponse response groups streams batches).collectFailureScopes
        = some scopes)
    (reported : WorkQueueSemantics.FailureReportedFor batches.flatten.flatten path)
    : ∃ scope ∈ scopes, scope.IsPrefix path := by
  obtain ⟨node, errors, positive, below, failure⟩ := reported
  obtain ⟨initialPaths, eventPaths⟩ := history_node_paths coherent admitted
  have descriptor : paths node.ref = node.path := by
    rcases failure with member | member
    all_goals
      apply eventPaths node
      apply List.mem_flatMap.mpr
      exact ⟨_, member, by simp [eventNodes]⟩
  cases allocated
        : (getPendingEntry (m := StateM IDState) groups streams ensureID).run {} with
  | mk pending ids =>
      have valid := (getPendingEntry_metadata_of_eq allocated).paths initialPaths
      have well := getPendingEntry_allocated groups streams {} Allocated.empty
      simp only [allocated] at well
      have finalWell := finalIDs_allocated batches.flatten ids well
      have metadata := (valid.mono (mappedTrace_spec batches.flatten ids).1).append
        (mappedTrace_noticePaths batches.flatten ids eventPaths)
      obtain ⟨completion, present, known, count⟩ := mappedTrace_failureCompletion failure ids
      have replayed := replayResponse_groups response groups streams batches
      rw [allocated] at replayed
      obtain ⟨updates, flat, replay⟩ := replayed
      rw [replay] at decoded
      change DeliveryTrace.collectFailureScopes pending (updates.map combineIncrementalResults)
        = some scopes at decoded
      have completed : completion ∈ (updates.map combineIncrementalResults).flatMap
          IncrementalStreamUpdateResult.completed := by
        rwa [batched_completed, flat]
      obtain ⟨update, included, member⟩ := List.mem_flatMap.mp completed
      refine ⟨node.path, ?_, below⟩
      apply collectFailureScopes_contains decoded included member (count ▸ positive)
      intro notice visible sameID
      apply metadata.same_id finalWell known descriptor _ sameID
      simpa only [batched_pending, flat] using visible

/-- Every unpublished terminal task is covered by an actual decoded wire failure scope.
Witness: Terminal supplies its attachment report, work batching retains that completion,
and the real response mapper exposes the same scope through its allocated wire ID.
No response-position coverage or ordinary-execution equivalence is assumed here.
-/
theorem replayResponse_unpublishedScope
    {paths bound response work groups streams batches scopes events matching failures}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (explained : WorkQueueSemantics.Explains work groups streams events matching failures)
    (terminal
      : WorkQueueSemantics.Terminal work
          ((groups ++ streams).map DeliveryNode.ref) matching events failures)
    (batching
      : WorkQueueSemantics.WorkBatching
          (events ++ [.workQueueTermination]) batches.flatten)
    (decoded
      : (replayResponse response groups streams batches).collectFailureScopes
        = some scopes)
    {occurrence owners producer payload}
    (known : WorkQueueSemantics.TaskAt work occurrence owners producer payload)
    (unpublished : ¬WorkQueueSemantics.Published matching events occurrence)
    : ∃ scope ∈ scopes, scope.IsPrefix payload.path := by
  apply replayResponse_reportedScope coherent (Or.inr
    ⟨events, matching, failures, explained, terminal, batching⟩) decoded
  exact batching.failure_reported ((terminal.failure_reported known unpublished).append _)

end GraphQL.IncrementalDelivery.Correctness
