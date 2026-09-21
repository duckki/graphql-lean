import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceReconstructionAlgebra
import Proofs.GraphQL.IncrementalDelivery.Semantics.SingleStreamCompletion
import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedListShape

/-! Successful list prefixes and streamed tails retain exact typed slices and seeds. -/

namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open TypedResponse

/-- Concatenating lists appends entries at the shifted index, by list induction. -/
theorem items_append (path : ResponsePath) (index : Nat) (left right : List ResponseValue)
    : items path index (left ++ right)
      = items path index left ++ items path (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [items]
  | cons head tail ih =>
      simp only [List.cons_append, items, ih, List.length_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm 1]

/-- Successful ordinary list completion preserves item count, by result-list induction. -/
theorem basicList_length (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (selected : List GraphQL.Execution.ExecutableField)
    (values : List (ResolverValue ObjectRef)) (data : List ResponseValue) (errors : Nat)
    (h
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          selected values
        = .ok (data, errors))
    : data.length = values.length := by
  induction values generalizing data errors with
  | nil =>
      simp [GraphQL.Execution.completeValueList] at h; simp [← h.1]
  | cons head tail ih =>
      cases hh : GraphQL.Execution.completeValue schema resolvers variables fuel itemType selected head <;>
        cases ht : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType selected tail <;>
        simp only [GraphQL.Execution.completeValueList, hh, ht, GraphQL.Execution.Result.combine,
          Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      obtain ⟨rfl, _⟩ := h
      simpa using ih _ _ ht

/-- A retained stream starts at initialCount, including an exactly exhausted list.
Witness: successful list completion preserves the length of the taken prefix.
-/
theorem basicPrefix_length (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (selected : List GraphQL.Execution.ExecutableField)
    (values : List (ResolverValue ObjectRef)) (count : Nat)
    (ht : count ≤ values.length) (data : List ResponseValue)
    (h
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          selected (values.take count)
        = .ok (data, 0))
    : data.length = count := by
  have hl := basicList_length schema resolvers variables fuel itemType selected _ data 0 h
  simpa only [List.length_take, Nat.min_eq_left ht] using hl

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open TypedResponse
open MixedPaths (WorkCursorSeed ItemCursorSeed resultCursors CursorHistory)
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)

/-- Adding the enclosing list cursor preserves nested cursors, since their paths lie
strictly below it. -/
theorem list_cursors_extend (path : ResponsePath) (data : List ResponseValue)
    : MixedPaths.CursorExtends (itemCursors path 0 data)
        (listCursors path (.list data)) := by
  change MixedPaths.CursorExtends (itemCursors path 0 data)
    ([(path, data.length)] ++ itemCursors path 0 data)
  apply MixedPaths.CursorExtends.prepend
  intro entry he index hc
  obtain rfl := List.mem_singleton.mp he
  obtain ⟨entry, he, hp⟩ := List.mem_map.mp ((itemCursors_history path 0 data).lookup hc)
  exact underItems_ne (TypedResponse.items_under path 0 data entry he) hp

/-- Object-field concatenation concatenates list cursors, by field-list induction. -/
theorem fieldCursors_append (path : ResponsePath)
    (left right : List (Name × ResponseValue))
    : fieldCursors path (left ++ right)
      = fieldCursors path left ++ fieldCursors path right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, fieldCursors, ih, List.append_assoc]

/-- A successful item and suffix combine typed slices and seeds at consecutive offsets. -/
theorem seededItems_cons (path : ResponsePath) (index : Nat)
    {completed : Completion ResponseValue} {tail : List (Result ResponseValue × Work)}
    {basicHead : Result ResponseValue} {basicTail : Result (List ResponseValue)}
    (hh
      : SeededReconstructs (value (path ++ [.index index]))
          (listCursors (path ++ [.index index])) basicHead completed)
    (ht : SeededItemsReconstructs path (index + 1) basicTail tail)
    : SeededItemsReconstructs path index
        (GraphQL.Execution.Result.combine List.cons basicHead basicTail)
        ((completed.result, completed.work) :: tail) := by
  intro hs
  obtain ⟨head, sh, hb, hw, hp, hseed⟩ := hh.reconstruct ⟨hs.1, hs.2.1⟩
  obtain ⟨rest, st, hbt, hwt, hpt, hseet⟩ := ht hs.2.2
  refine ⟨
    head :: rest,
    _,
    by simp [hb, hbt, GraphQL.Execution.Result.combine],
    .cons hw hwt,
    ?_,
    ?_
  ⟩
  · simpa only [List.flatten_cons, List.flatten_append, items, List.append_assoc] using hp.append hpt
  · intro hn
    have hn' : (((result (value (path ++ [.index index])) completed.result ++ sh.flatten) ++
        st.flatten).map Prod.fst).Nodup := by
      simpa only [List.flatten_cons, List.flatten_append, List.append_assoc] using hn
    have hp := List.nodup_append.mp (by simpa only [List.map_append] using hn')
    simpa only [entryPaths, List.map_cons, List.map_append, result_value_paths]
      using ItemCursorSeed.cons (hseed (by simpa only [List.map_append] using hp.1))
        (hseet hp.2.1)

/-- A successful prefix and streamed tail reconstruct one list; exact prefix lengths
align source offsets. -/
theorem seeded_stream (path : ResponsePath) (count : Nat)
    {initial : Completion (List ResponseValue)}
    {tail : List (Result ResponseValue × Work)}
    {basicInitial basicTail : Result (List ResponseValue)}
    (hi : SeededReconstructs (items path 0) (itemCursors path 0) basicInitial initial)
    (ht : SeededItemsReconstructs path count basicTail tail) (data : List ResponseValue)
    (errors : Nat) (he : initial.result = .ok (data, errors))
    (hactual : data.length = count)
    (hlen : ∀ data, basicInitial = .ok (data, 0) → data.length = count)
    (node : DeliveryNode) (hn : node.path = path)
    : SeededReconstructs (value path) (listCursors path)
        (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
          (GraphQL.Execution.Result.combine List.append basicInitial basicTail))
        {
          initial.catchNull ResponseValue.list with
            work :=
              .append (initial.catchNull ResponseValue.list).work (.stream node tail)
        } := by
  refine ⟨by simp [Completion.catchNull, he, BasicErrors.PositiveFailure], ?_⟩
  intro hs
  simp only [CompletionSuccess, Completion.catchNull, he, Except.ok.injEq,
    Prod.mk.injEq, exists_eq_left', WorkSuccess] at hs
  obtain ⟨rfl, hsi, hst⟩ := hs
  obtain ⟨first, sp, hp, hwp, hpp, hseedp⟩ := hi.reconstruct ⟨⟨data, he⟩, hsi⟩
  obtain ⟨rest, st, hr, hwr, hpr, hseedt⟩ := ht hst
  refine ⟨.list (first ++ rest), sp ++ st, ?_, ?_, ?_, ?_⟩
  · simp [hp, hr, GraphQL.Execution.Result.combine, GraphQL.Execution.catchBubbleAsNull]
  · simp only [Completion.catchNull, he]
    exact .append hwp (.stream (hn ▸ hwr))
  · have hall := (hpp.append hpr).cons (path, Atom.list)
    simpa only [Completion.catchNull, he, result, value, List.flatten_append, items_append,
      Nat.zero_add, hlen first hp, List.cons_append, List.append_assoc] using hall
  · intro hn'
    simp only [Completion.catchNull, he, result, value, List.flatten_append,
      List.cons_append, List.map_cons, List.nodup_cons] at hn'
    have hp' : (((items path 0 data ++ sp.flatten) ++ st.flatten).map Prod.fst).Nodup := by
      simpa only [List.append_assoc] using hn'.2
    have hparts := List.nodup_append.mp (by simpa only [List.map_append] using hp')
    have hfirst := hseedp (by simpa only [he, result, List.map_append] using hparts.1)
    simp only [he, resultCursors] at hfirst
    have hlast : WorkCursorSeed (listCursors path (.list data)) (.stream node tail) (entryPaths st) := by
      apply WorkCursorSeed.stream (index := count)
      · simp [cursorAt, listCursors, hn, hactual]
      · exact hn ▸ hseedt hparts.2.1
    simpa only [Completion.catchNull, he, resultCursors, entryPaths, List.map_append]
      using WorkCursorSeed.append (hfirst.extend (list_cursors_extend path data)) hlast

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
