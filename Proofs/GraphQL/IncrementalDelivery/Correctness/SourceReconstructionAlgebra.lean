import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedCursorSeeds

/-! Typed reconstruction and payload cursor seeds share one source witness.
The seed condition is guarded by uniqueness of the reconstructed positions;
ordinary basic-response uniqueness discharges it at the root. This permits the
algebra itself to remain valid for arbitrary, possibly duplicate field groups.
-/

namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open TypedResponse
open MixedPaths (WorkCursorSeed ItemCursorSeed resultCursors CursorHistory)
open ResponsePositions (Cursors listCursors fieldCursors itemCursors)

/-- Forget entry tags in each typed slice while preserving slice boundaries. -/
def entryPaths (slices : List (List Entry)) : List (List ResponsePath) :=
  slices.map (List.map Prod.fst)

/-- Unique reconstructed paths require the same slices to have payload-derived cursor
seeds. -/
def SeedGuard (entries : α → List Entry) (cursors : α → Cursors)
    (completed : Completion α) (slices : List (List Entry))
    : Prop :=
  ((result entries completed.result ++ slices.flatten).map Prod.fst).Nodup
  → WorkCursorSeed (resultCursors cursors completed.result) completed.work
      (entryPaths slices)

/-- Successful completion reconstructs basic typed entries with the same seeded source
witness. -/
structure SeededReconstructs (entries : α → List Entry) (cursors : α → Cursors)
    (basic : Result α) (completed : Completion α)
    : Prop where
  positive : BasicErrors.PositiveFailure completed.result
  reconstruct
    : CompletionSuccess completed
      → ∃ data slices,
          basic = .ok (data, 0)
          ∧ WorkEntries completed.work slices
          ∧ (result entries completed.result ++ slices.flatten).Perm (entries data)
          ∧ SeedGuard entries cursors completed slices

/-- Successful deferred work reconstructs a basic field partition with
ambient-independent seeds. -/
def SeededWorkReconstructs (path : ResponsePath)
    (basic : Result (List (Name × ResponseValue))) (work : Work)
    : Prop :=
  WorkSuccess work
  → ∃ data slices,
      basic = .ok (data, 0)
      ∧ WorkEntries work slices
      ∧ slices.flatten.Perm (fields path data)
      ∧ (∀ cursors,
          (slices.flatten.map Prod.fst).Nodup
          → WorkCursorSeed cursors work (entryPaths slices))

/-- Successful streamed items reconstruct a basic list suffix with its actual absolute
offset. -/
def SeededItemsReconstructs (path : ResponsePath) (index : Nat)
    (basic : Result (List ResponseValue)) (streamed : List (Result ResponseValue × Work))
    : Prop :=
  ItemsSuccess streamed
  → ∃ data slices,
      basic = .ok (data, 0)
      ∧ ItemEntries path index streamed slices
      ∧ slices.flatten.Perm (items path index data)
      ∧ ((slices.flatten.map Prod.fst).Nodup
          → ItemCursorSeed path index streamed (entryPaths slices))

/-- Field-result tag erasure equals source field paths, by result cases. -/
theorem result_fields_paths (path : ResponsePath)
    (completed : Result (List (Name × ResponseValue)))
    : (result (fields path) completed).map Prod.fst
      = DeliveryPaths.result (DeliveryPaths.fields true path) completed := by
  cases completed <;> simp [result, DeliveryPaths.result, fields_paths]

/-- Value-result tag erasure equals source value paths, by result cases. -/
theorem result_value_paths (path : ResponsePath) (completed : Result ResponseValue)
    : (result (value path) completed).map Prod.fst
      = DeliveryPaths.result (DeliveryPaths.value true path) completed := by
  cases completed <;> simp [result, DeliveryPaths.result, value_paths]

/-- Every object cursor names a contributed container path, by cursor provenance. -/
theorem fieldCursors_history (path : ResponsePath) (data : List (Name × ResponseValue))
    : CursorHistory (fieldCursors path data) ((fields path data).map Prod.fst) := by
  simpa only [fields_paths] using MixedPaths.fieldCursors_positions path data

/-- Every value cursor names a contributed container path, by cursor provenance. -/
theorem listCursors_history (path : ResponsePath) (data : ResponseValue)
    : CursorHistory (listCursors path data) ((value path data).map Prod.fst) := by
  simpa only [value_paths] using MixedPaths.listCursors_positions path data

/-- Every item cursor names a contributed container path, by cursor provenance. -/
theorem itemCursors_history (path : ResponsePath) (index : Nat)
    (data : List ResponseValue)
    : CursorHistory (itemCursors path index data)
        ((items path index data).map Prod.fst) := by
  simpa only [items_paths] using MixedPaths.itemCursors_positions path index data

/-- Reordering four disjoint entry portions preserves each needed uniqueness
certificate. -/
theorem shuffle_nodup {a b c d : List Entry}
    (h : (((a ++ b) ++ (c ++ d)).map Prod.fst).Nodup)
    : ((a ++ c).map Prod.fst).Nodup
      ∧ ((b ++ d).map Prod.fst).Nodup
      ∧ ((a ++ b).map Prod.fst).Nodup := by
  have hp : ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
    simpa only [List.append_assoc]
      using ((List.perm_append_comm (l₁ := b) (l₂ := c)).append_left a).append_right d
  have h' := (List.nodup_append.mp (by simpa only [List.map_append] using (hp.map Prod.fst).nodup_iff.mp h))
  exact ⟨
    by simpa only [List.map_append] using h'.1,
    by simpa only [List.map_append] using h'.2.1,
    (List.nodup_append.mp (by simpa only [List.map_append] using h)).1
  ⟩

/-- Wrapping one completed value as an object field preserves reconstruction and seeds. -/
theorem seeded_field (path : ResponsePath) (name : Name)
    {completed : Completion ResponseValue} {basic : Result ResponseValue}
    (h
      : SeededReconstructs (value (path ++ [.field name]))
          (listCursors (path ++ [.field name])) basic completed)
    : SeededReconstructs (fields path) (fieldCursors path) (singleFieldResult name basic)
        (completed.map (fun data => [(name, data)])) := by
  refine ⟨?_, ?_⟩
  · have hp := BasicErrors.field name completed.result h.positive
    cases he : completed.result <;> simpa [Completion.map, he, singleFieldResult, Completion.error] using hp
  · intro hs
    cases he : completed.result with
    | error errors => simp [CompletionSuccess, Completion.map, he, Completion.error] at hs
    | ok data =>
        rcases data with ⟨data, errors⟩
        simp only [CompletionSuccess, Completion.map, he, Except.ok.injEq,
          Prod.mk.injEq, exists_eq_left'] at hs
        rcases hs with ⟨rfl, hw⟩
        obtain ⟨data', slices, hd', hsw, hp, hseed⟩ := h.reconstruct ⟨⟨data, he⟩, hw⟩
        refine ⟨[(name, data')], slices, by simp [hd', singleFieldResult], ?_, ?_, ?_⟩
        · simpa only [Completion.map, he] using hsw
        · simpa [Completion.map, he, result, fields] using hp
        · simpa [SeedGuard, Completion.map, he, result, fields, resultCursors,
            fieldCursors] using hseed

/-- Nullable catching preserves successful reconstruction; positive failures cannot
satisfy success. -/
theorem seeded_catchNull {entries : α → List Entry} {cursors : α → Cursors}
    {wrap : α → ResponseValue} (path : ResponsePath) (atom : Atom)
    (hw : ∀ data, value path (wrap data) = (path, atom) :: entries data)
    (hcursors
      : ∀ data, MixedPaths.CursorExtends (cursors data) (listCursors path (wrap data)))
    {completed : Completion α} {basic : Result α}
    (h : SeededReconstructs entries cursors basic completed)
    : SeededReconstructs (value path) (listCursors path)
        (GraphQL.Execution.catchBubbleAsNull wrap basic) (completed.catchNull wrap) := by
  refine ⟨?_, ?_⟩
  · cases he : completed.result <;> simp [BasicErrors.PositiveFailure, Completion.catchNull, he]
  · intro hs
    cases he : completed.result with
    | error errors =>
        have hp := h.positive errors he
        simp [CompletionSuccess, Completion.catchNull, he] at hs
        omega
    | ok data =>
        rcases data with ⟨data, errors⟩
        simp only [CompletionSuccess, Completion.catchNull, he, Except.ok.injEq,
          Prod.mk.injEq, exists_eq_left'] at hs
        rcases hs with ⟨rfl, hs⟩
        obtain ⟨data', slices, hd', hsw, hp, hseed⟩ := h.reconstruct ⟨⟨data, he⟩, hs⟩
        refine ⟨
          wrap data',
          slices,
          by simp [hd', GraphQL.Execution.catchBubbleAsNull],
          ?_,
          ?_,
          ?_
        ⟩
        · simpa only [Completion.catchNull, he] using hsw
        · simpa [Completion.catchNull, he, result, hw] using hp.cons (path, atom)
        · intro hn
          simp only [Completion.catchNull, he, result, hw, List.cons_append,
            List.map_cons, List.nodup_cons] at hn
          have hseed' := hseed (by simpa only [he, result] using hn.2)
          simpa only [Completion.catchNull, he, resultCursors]
            using hseed'.extend (by simpa only [he, resultCursors] using hcursors data)

/-- Non-null completion preserves successful reconstruction, using typed root tags to
exclude null. -/
theorem seeded_nonNull (path : ResponsePath)
    {completed : Completion ResponseValue} {basic : Result ResponseValue}
    (h : SeededReconstructs (value path) (listCursors path) basic completed)
    : SeededReconstructs (value path) (listCursors path)
        (nonNullCompletion basic) completed.nonNull := by
  refine ⟨?_, ?_⟩
  · have hp := BasicErrors.nonNull completed.result h.positive
    unfold Completion.nonNull
    split <;> rename_i he <;> simpa [Completion.error, he] using hp
  · intro hs
    cases he : completed.result with
    | error errors =>
        simp [CompletionSuccess, Completion.nonNull, he, nonNullCompletion, Completion.error] at hs
    | ok data =>
        rcases data with ⟨data, errors⟩
        cases data with
        | null =>
            simp [CompletionSuccess, Completion.nonNull, he, nonNullCompletion, Completion.error] at hs
        | scalar text | object _ | list _ =>
            simp only [CompletionSuccess, Completion.nonNull, he, nonNullCompletion,
              Except.ok.injEq, Prod.mk.injEq, exists_eq_left'] at hs
            rcases hs with ⟨rfl, hs⟩
            obtain ⟨data', slices, hd', hsw, hp, hseed⟩ := h.reconstruct ⟨⟨_, he⟩, hs⟩
            have hn : data' ≠ .null := by
              intro hn
              rw [hn] at hp
              have hn' := null_of_perm path _ slices.flatten (by simpa [he, result] using hp)
              contradiction
            refine ⟨data', slices, ?_, ?_, ?_, ?_⟩
            · cases data' <;> simp_all [nonNullCompletion]
            · simpa [Completion.nonNull, he, nonNullCompletion] using hsw
            · simpa [Completion.nonNull, he, nonNullCompletion, result] using hp
            · simpa [SeedGuard, Completion.nonNull, he, nonNullCompletion] using hseed

/-- Pure values reconstruct themselves and require no work or cursor seed. -/
theorem seeded_pure (entries : α → List Entry) (cursors : α → Cursors) (data : α)
    : SeededReconstructs entries cursors (.ok (data, 0)) (.pure data) := by
  refine ⟨by simp [BasicErrors.PositiveFailure, Completion.pure], ?_⟩
  intro _
  exact ⟨data, [], rfl, .empty, by simp [Completion.pure, result], fun _ => .empty⟩

/-- A positive bubbling error cannot meet the internal successful-completion premise. -/
theorem seeded_error (entries : α → List Entry) (cursors : α → Cursors)
    (basic : Result α) (errors : Nat) (h : 0 < errors)
    : SeededReconstructs entries cursors basic (.error errors) := by
  refine ⟨by simpa [BasicErrors.PositiveFailure, Completion.error] using h, ?_⟩
  simp [CompletionSuccess, Completion.error]

/-- A counted field error cannot meet the internal successful-completion premise. -/
theorem seeded_failedField (path : ResponsePath) (name : Name) (fieldType : TypeRef)
    (basic : Result (List (Name × ResponseValue)))
    : SeededReconstructs (fields path) (fieldCursors path) basic
        {result := singleFieldResult name (handleFieldError fieldType)} := by
  refine ⟨?_, ?_⟩
  · cases fieldType <;> simp [BasicErrors.PositiveFailure, singleFieldResult, handleFieldError]
  · cases fieldType <;> simp [CompletionSuccess, singleFieldResult, handleFieldError]

/-- Combining successful completions preserves typed reconstruction and seeds;
disjointness licenses cursor extension. -/
theorem seeded_combine {pa : α → List Entry} {pb : β → List Entry} {pc : γ → List Entry}
    {ca : α → Cursors} {cb : β → Cursors} {cc : γ → Cursors}
    {f : α → β → γ} {left : Completion α} {right : Completion β}
    {basicLeft : Result α} {basicRight : Result β}
    (hf : ∀ a b, pc (f a b) = pa a ++ pb b)
    (hfc : ∀ a b, cc (f a b) = ca a ++ cb b)
    (hca : ∀ a, CursorHistory (ca a) ((pa a).map Prod.fst))
    (hcb : ∀ b, CursorHistory (cb b) ((pb b).map Prod.fst))
    (hl : SeededReconstructs pa ca basicLeft left)
    (hr : SeededReconstructs pb cb basicRight right)
    : SeededReconstructs pc cc (GraphQL.Execution.Result.combine f basicLeft basicRight)
        (Completion.combine f left right) := by
  refine ⟨?_, ?_⟩
  · have hp := BasicErrors.combine f left.result right.result hl.positive hr.positive
    cases he : left.result <;> cases hre : right.result <;>
      simpa [Completion.combine, he, hre, GraphQL.Execution.Result.combine, Completion.error] using hp
  · intro hs
    cases he : left.result with
    | error errors =>
        cases hre : right.result <;>
          simp [CompletionSuccess, Completion.combine, he, hre, GraphQL.Execution.Result.combine, Completion.error] at hs
    | ok leftData =>
        rcases leftData with ⟨a, ea⟩
        cases hre : right.result with
        | error errors =>
            simp [CompletionSuccess, Completion.combine, he, hre, GraphQL.Execution.Result.combine, Completion.error] at hs
        | ok rightData =>
            rcases rightData with ⟨b, eb⟩
            simp only [CompletionSuccess, Completion.combine, he, hre,
              GraphQL.Execution.Result.combine, Except.ok.injEq, Prod.mk.injEq,
              exists_eq_left', WorkSuccess] at hs
            have hea : ea = 0 := by omega
            have heb : eb = 0 := by omega
            subst ea; subst eb
            obtain ⟨a', sa, ha', hsa, hpa, hsea⟩ := hl.reconstruct ⟨⟨a, he⟩, hs.2.1⟩
            obtain ⟨b', sb, hb', hsb, hpb, hseb⟩ := hr.reconstruct ⟨⟨b, hre⟩, hs.2.2⟩
            refine ⟨
              f a' b',
              sa ++ sb,
              by simp [ha', hb', GraphQL.Execution.Result.combine],
              ?_,
              ?_,
              ?_
            ⟩
            · simpa only [Completion.combine, he, hre, GraphQL.Execution.Result.combine]
                using WorkEntries.combine hsa hsb
            · have hp := hpa.append hpb
              simp only [he, hre, result] at hp
              simp only [Completion.combine, he, hre, GraphQL.Execution.Result.combine, result, hf, List.flatten_append]
              apply List.Perm.trans _ hp
              simpa only [List.append_assoc]
                using ((List.perm_append_comm (l₁ := pb b) (l₂ := sa.flatten)).append_left
                        (pa a)).append_right
                  sb.flatten
            · intro hn
              simp only [Completion.combine, he, hre, GraphQL.Execution.Result.combine, result,
                hf, List.flatten_append] at hn
              obtain ⟨hna, hnb, hnc⟩ := shuffle_nodup hn
              have hsa' := hsea (by simpa only [he, result] using hna)
              have hsb' := hseb (by simpa only [hre, result] using hnb)
              simp only [he, hre, resultCursors] at hsa' hsb'
              have hsb'' : WorkCursorSeed (ca a ++ cb b) right.work (entryPaths sb) := by
                apply hsb'.extend
                apply MixedPaths.CursorExtends.prepend
                intro entry hem index hc
                exact (List.nodup_append.mp (by simpa only [List.map_append] using hnc)).2.2
                  _ (hca a entry hem) _ ((hcb b).lookup hc) rfl
              simpa only [Completion.combine, he, hre, GraphQL.Execution.Result.combine,
                resultCursors, hfc, entryPaths, List.map_append]
                using WorkCursorSeed.combine (hsa'.append_cursors (cb b)) hsb''

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
