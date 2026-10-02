import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceAttachments

/-! Completion combinators preserve shared cursor, ownership, and attachment witnesses. -/

namespace GraphQL.IncrementalDelivery.Correctness.SourceAttachments

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.MixedPaths
open DeliveryPaths
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)
open TypedResponse (Entry Atom)

/-- Errors have no attachment obligations, witnessed by empty work and slices. -/
theorem attached_error (available : List Entry) (entries : α → List Entry)
    (paths : α → List ResponsePath) (cursors : α → Cursors)
    (scope : ResponsePath → Prop) (errors : Nat)
    : OwnedAttachedCompletion available entries paths cursors scope
        (Completion.error errors) :=
  ⟨seeded_error _ _ _ _, [], .empty, .empty⟩

/-- Pure completions retain owned paths and have empty attachment witnesses. -/
theorem attached_pure {available : List Entry} {entries : α → List Entry}
    {paths : α → List ResponsePath} {cursors : α → Cursors}
    {scope : ResponsePath → Prop} {data : α} (h : Owns scope (paths data))
    : OwnedAttachedCompletion available entries paths cursors scope
        (Completion.pure data) :=
  ⟨seeded_pure h, [], .empty, .empty⟩

/-- Combining disjoint completions preserves attachments, by extending both ambient
contexts and combining their compatible cursor seeds. -/
theorem attached_combine {available : List Entry} {ea : α → List Entry}
    {eb : β → List Entry} {ec : γ → List Entry}
    {pa : α → List ResponsePath} {pb : β → List ResponsePath}
    {pc : γ → List ResponsePath} {ca : α → Cursors} {cb : β → Cursors}
    {cc : γ → Cursors} {f : α → β → γ} {sa sb sc : ResponsePath → Prop}
    {left : Completion α} {right : Completion β}
    (hf : ∀a b, pc (f a b) = pa a ++ pb b)
    (hc : ∀a b, cc (f a b) = ca a ++ cb b)
    (he : ∀a b, ec (f a b) = ea a ++ eb b)
    (hca : ∀a, CursorHistory (ca a) (pa a)) (hcb : ∀b, CursorHistory (cb b) (pb b))
    (hl : OwnedAttachedCompletion available ea pa ca sa left)
    (hr : OwnedAttachedCompletion available eb pb cb sb right)
    (hd : ∀p, sa p → sb p → False) (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : OwnedAttachedCompletion available ec pc cc sc
        (Completion.combine f left right) := by
  refine ⟨seeded_combine hf hc hca hcb hl.1 hr.1 hd hls hrs, ?_⟩
  cases hel : left.result with
  | error errors =>
      cases her : right.result <;> simp only [Completion.combine, hel, her,
        GraphQL.Execution.Result.combine]
      all_goals exact ⟨[], .empty, .empty⟩
  | ok leftData =>
      rcases leftData with ⟨a, x⟩
      cases her : right.result with
      | error errors =>
          simp only [Completion.combine, hel, her, GraphQL.Execution.Result.combine]
          exact ⟨[], .empty, .empty⟩
      | ok rightData =>
          rcases rightData with ⟨b, y⟩
          obtain ⟨sl, hsl, hol⟩ := hl.1
          obtain ⟨sr, hsr, hor⟩ := hr.1
          have hal := hl.2.at hsl
          have har := hr.2.at hsr
          simp only [hel, her, resultCursors] at hsl hsr
          simp only [hel, her, result] at hol hor
          simp only [hel, her, TypedResponse.result] at hal har
          have hext : CursorExtends (cb b) (ca a ++ cb b) := by
            apply CursorExtends.prepend
            intro entry hm index hh
            exact hd entry.1 (hol.2 _ (List.mem_append_left _ (hca a entry hm)))
              (hor.2 _ (List.mem_append_left _ ((hcb b).lookup hh)))
          refine ⟨sl ++ sr, ?_, ?_⟩
          · simpa only [Completion.combine, hel, her, GraphQL.Execution.Result.combine,
              resultCursors, hc] using WorkCursorSeed.combine
                (hsl.append_cursors (cb b)) (hsr.extend hext)
          · simp only [Completion.combine, hel, her, GraphQL.Execution.Result.combine,
              TypedResponse.result, he]
            refine .combine (hal.mono ?_) (har.mono ?_)
            · intro entry hh
              rcases List.mem_append.mp hh with hh | hh
              · exact List.mem_append_left _ hh
              · exact List.mem_append_right _ (List.mem_append_left _ hh)
            · intro entry hh
              rcases List.mem_append.mp hh with hh | hh
              · exact List.mem_append_left _ hh
              · exact List.mem_append_right _ (List.mem_append_right _ hh)

/-- Mapping preserves attachments when entry, path, and cursor projections agree;
the same slices witness the successful branch. -/
theorem attached_map {available : List Entry} {ea : α → List Entry} {eb : β → List Entry}
    {pa : α → List ResponsePath} {pb : β → List ResponsePath}
    {ca : α → Cursors} {cb : β → Cursors} {f : α → β}
    {scope : ResponsePath → Prop} {completed : Completion α}
    (hf : ∀a, pb (f a) = pa a) (hc : ∀a, cb (f a) = ca a) (he : ∀a, eb (f a) = ea a)
    (h : OwnedAttachedCompletion available ea pa ca scope completed)
    : OwnedAttachedCompletion available eb pb cb scope (completed.map f) := by
  refine ⟨seeded_map hf hc h.1, ?_⟩
  cases hr : completed.result with
  | error errors =>
      simp only [Completion.map, hr]; exact ⟨[], .empty, .empty⟩
  | ok data =>
      obtain ⟨s, hs, ha⟩ := h.2
      refine ⟨s, ?_, ?_⟩
      · simpa only [Completion.map, hr, resultCursors, hc] using hs
      · simpa only [Completion.map, hr, TypedResponse.result, he] using ha

/-- Nullable wrapping supplies the parent container for successful child work;
error branches discard work, and cursor extension preserves the shared seed. -/
theorem attached_catchNull {available : List Entry} {ea : α → List Entry}
    {pa : α → List ResponsePath} {ca : α → Cursors} {wrap : α → ResponseValue}
    {scope : ResponsePath → Prop} {path : ResponsePath} {atom : Atom}
    {completed : Completion α}
    (hf : ∀a, value true path (wrap a) = [path] ++ pa a)
    (hc : ∀a, (∀p ∈ pa a, p ≠ path) → CursorExtends (ca a) (listCursors path (wrap a)))
    (he : ∀a, TypedResponse.value path (wrap a) = (path, atom) :: ea a)
    (h : OwnedAttachedCompletion (available ++ [(path, atom)]) ea pa ca scope completed)
    (hs : ∀p, scope p → Below path p) (hn : ∀p, scope p → p ≠ path)
    : OwnedAttachedCompletion available (TypedResponse.value path)
        (value true path) (listCursors path) (Below path) (completed.catchNull wrap) := by
  refine ⟨seeded_catchNull hf hc h.1 hs hn, ?_⟩
  cases hr : completed.result with
  | error errors =>
      simp only [Completion.catchNull, hr]; exact ⟨[], .empty, .empty⟩
  | ok data =>
      obtain ⟨s, hseed, ho⟩ := h.1
      have ha := h.2.at hseed
      simp only [hr, resultCursors] at hseed
      simp only [hr, result] at ho
      refine ⟨s, ?_, ?_⟩
      · simpa only [Completion.catchNull, hr, resultCursors]
          using hseed.extend
            (hc data.1 (fun p hp => hn p (ho.2 p (List.mem_append_left _ hp))))
      · simpa only [Completion.catchNull, hr, TypedResponse.result, he, List.append_assoc,
          List.singleton_append] using ha

/-- Non-null completion preserves attachments, by separating null/error branches
from unchanged successful values. -/
theorem attached_nonNull {available : List Entry} {path : ResponsePath}
    {completed : Completion ResponseValue}
    (h
      : OwnedAttachedCompletion available (TypedResponse.value path)
          (value true path) (listCursors path) (Below path) completed)
    : OwnedAttachedCompletion available (TypedResponse.value path)
        (value true path) (listCursors path) (Below path) completed.nonNull := by
  refine ⟨seeded_nonNull h.1, ?_⟩
  cases he : completed.result with
  | error errors =>
      simp only [Completion.nonNull, he, nonNullCompletion, GraphQL.Execution.nonNullCompletion]
      exact ⟨[], .empty, .empty⟩
  | ok data =>
      rcases data with ⟨data, errors⟩
      cases data <;> simp only [Completion.nonNull, he, nonNullCompletion, GraphQL.Execution.nonNullCompletion]
      · exact ⟨[], .empty, .empty⟩
      all_goals
        obtain ⟨s, hs, ha⟩ := h.2
        exact ⟨s, by simpa only [he] using hs, by simpa only [he] using ha⟩

/-- Wrapping a completion as deferred work attaches it to the given ambient object;
its payload supplies the entries needed by its child work. -/
theorem OwnedAttachedCompletion.executionGroup {available : List Entry}
    {path : ResponsePath} {scope : ResponsePath → Prop}
    {completed : Completion (List (Name × ResponseValue))}
    (h
      : OwnedAttachedCompletion available (TypedResponse.fields path)
          (fields true path) (fieldCursors path) scope completed)
    (groups : List DeferredFragment) (ha : (path, Atom.object) ∈ available)
    : OwnedAttachedWork available scope
        (.executionGroup groups path completed.result completed.work) := by
  refine ⟨h.1.executionGroup groups, ?_⟩
  obtain ⟨s, hs, hc⟩ := h.2
  exact ⟨_, fun _ => .executionGroup hs, .executionGroup ha hc⟩

/-- Disjoint attached work combines by concatenating its shared slice witnesses. -/
theorem attached_work_combine {available : List Entry} {sa sb sc : ResponsePath → Prop}
    {left right : Work} (hl : OwnedAttachedWork available sa left)
    (hr : OwnedAttachedWork available sb right)
    (hd : ∀p, sa p → sb p → False) (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : OwnedAttachedWork available sc (.combine left right) := by
  refine ⟨seeded_work_combine hl.1 hr.1 hd hls hrs, ?_⟩
  obtain ⟨sl, hsl, hal⟩ := hl.2
  obtain ⟨sr, hsr, har⟩ := hr.2
  exact ⟨sl ++ sr, fun c => .combine (hsl c) (hsr c), .combine hal har⟩

/-- Combining disjoint work preserves completion attachments, by ambient monotonicity. -/
theorem attached_combineWork {available : List Entry} {ea : α → List Entry}
    {pa : α → List ResponsePath} {ca : α → Cursors}
    {sa sb sc : ResponsePath → Prop} {completed : Completion α} {work : Work}
    (hl : OwnedAttachedCompletion available ea pa ca sa completed)
    (hr : OwnedAttachedWork available sb work)
    (hd : ∀p, sa p → sb p → False) (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : OwnedAttachedCompletion available ea pa ca sc
        {completed with work := .combine completed.work work} := by
  refine ⟨seeded_combineWork hl.1 hr.1 hd hls hrs, ?_⟩
  obtain ⟨sl, hsl, hal⟩ := hl.2
  obtain ⟨sr, hsr, har⟩ := hr.2
  exact ⟨sl ++ sr, .combine hsl (hsr _),
    .combine hal (har.mono (fun _ => List.mem_append_left _))⟩

/-- Prepending a completed item preserves attachments, using its payload as the
child context and the next index for the remaining items. -/
theorem attached_items_cons {available : List Entry} {path : ResponsePath} {index : Nat}
    {sa sb sc : ResponsePath → Prop} {completed : Completion ResponseValue}
    {items : List (Result ResponseValue × Work)}
    (hl
      : OwnedAttachedCompletion available
          (TypedResponse.value (path ++ [.index index]))
          (value true (path ++ [.index index])) (listCursors (path ++ [.index index])) sa
          completed)
    (hr : OwnedAttachedItems available path (index + 1) sb items)
    (hd : ∀p, sa p → sb p → False) (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : OwnedAttachedItems available path index sc
        ((completed.result, completed.work) :: items) := by
  refine ⟨seeded_items_cons hl.1 hr.1 hd hls hrs, ?_⟩
  obtain ⟨sl, hsl, hal⟩ := hl.2
  obtain ⟨sr, hsr, har⟩ := hr.2
  exact ⟨_, .cons hsl hsr, .cons hal har⟩

/-- Failed fields have no work to attach, witnessed by empty slices. -/
theorem attached_failedField (available : List Entry) (path : ResponsePath)
    (name : Name) (fieldType : TypeRef)
    : OwnedAttachedCompletion available (TypedResponse.fields path)
        (fields true path) (fieldCursors path) (Below (path ++ [.field name]))
        {result := singleFieldResult name (handleFieldError fieldType)} :=
  ⟨seeded_failedField _ _ _, [], .empty, .empty⟩

/-- Distinct field groups combine attached completions, by disjoint field scopes. -/
theorem attached_combine_fields {available : List Entry} {path : ResponsePath}
    {leftNames rightNames : List Name}
    {left right : Completion (List (Name × ResponseValue))}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl
      : OwnedAttachedCompletion available (TypedResponse.fields path)
          (fields true path) (fieldCursors path) (UnderFields path leftNames) left)
    (hr
      : OwnedAttachedCompletion available (TypedResponse.fields path)
          (fields true path) (fieldCursors path) (UnderFields path rightNames) right)
    : OwnedAttachedCompletion available (TypedResponse.fields path)
        (fields true path) (fieldCursors path)
        (UnderFields path (leftNames ++ rightNames))
        (Completion.combine List.append left right) := by
  apply attached_combine (fields_append true path) (fieldCursors_append path)
    (TypedResponse.fields_append path)
    (fieldCursors_positions path) (fieldCursors_positions path) hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

/-- Distinct field groups combine attached work, by disjoint field scopes. -/
theorem attached_work_combine_fields {available : List Entry} {path : ResponsePath}
    {leftNames rightNames : List Name} {left right : Work}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl : OwnedAttachedWork available (UnderFields path leftNames) left)
    (hr : OwnedAttachedWork available (UnderFields path rightNames) right)
    : OwnedAttachedWork available (UnderFields path (leftNames ++ rightNames))
        (.combine left right) := by
  apply attached_work_combine hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

/-- Combining work from distinct field groups preserves attachments, by scope
separation.
-/
theorem attached_combineWork_fields {available : List Entry} {path : ResponsePath}
    {leftNames rightNames : List Name}
    {completed : Completion (List (Name × ResponseValue))} {work : Work}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl
      : OwnedAttachedCompletion available (TypedResponse.fields path)
          (fields true path) (fieldCursors path) (UnderFields path leftNames) completed)
    (hr : OwnedAttachedWork available (UnderFields path rightNames) work)
    : OwnedAttachedCompletion available (TypedResponse.fields path)
        (fields true path) (fieldCursors path)
        (UnderFields path (leftNames ++ rightNames))
        {completed with work := .combine completed.work work} := by
  apply attached_combineWork hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

/-- An item and its later siblings have disjoint scopes; the cons rule combines
their attachment witnesses at consecutive response indices. -/
theorem attached_items_cons_underItems {available : List Entry} {path : ResponsePath}
    {index : Nat} {head : Completion ResponseValue}
    {tail : List (Result ResponseValue × Work)}
    (hh
      : OwnedAttachedCompletion available
          (TypedResponse.value (path ++ [.index index]))
          (value true (path ++ [.index index])) (listCursors (path ++ [.index index]))
          (Below (path ++ [.index index])) head)
    (ht
      : OwnedAttachedItems available path (index + 1) (UnderItems path (index + 1)) tail)
    : OwnedAttachedItems available path index (UnderItems path index)
        ((head.result, head.work) :: tail) := by
  apply attached_items_cons hh ht
  · exact fun _ => underItems_disjoint
  · exact fun _ hp => ⟨index, Nat.le_refl _, hp⟩
  · intro p ⟨next, hn, hp⟩
    exact ⟨next, by omega, hp⟩

/-- A streamed suffix attaches to the initial list container; initial length fixes
the shared starting cursor, and monotonicity retains all ambient entries. -/
theorem attached_streamPrefix {available : List Entry} {path : ResponsePath}
    {finish start : Nat} {initial : Completion (List ResponseValue)}
    {data : List ResponseValue} {errors : Nat} {node : DeliveryNode}
    {items : List (Result ResponseValue × Work)}
    (hi
      : OwnedAttachedCompletion (available ++ [(path, Atom.list)])
          (TypedResponse.items path 0) (DeliveryPaths.items true path 0)
          (itemCursors path 0) (UnderItemRange path 0 finish) initial)
    (he : initial.result = .ok (data, errors)) (hb : finish ≤ start)
    (hlen : data.length = start) (hp : node.path = path)
    (ht
      : OwnedAttachedItems (available ++ [(path, Atom.list)]) path start
          (UnderItems path start) items)
    : OwnedAttachedCompletion available (TypedResponse.value path)
        (value true path) (listCursors path) (Below path)
        {
          initial.catchNull ResponseValue.list with
            work :=
              .combine (initial.catchNull ResponseValue.list).work (.stream node items)
        } := by
  refine ⟨seeded_streamPrefix hi.1 he hb hlen hp ht.1, ?_⟩
  obtain ⟨sl, hsl, hol⟩ := hi.1
  have hal := hi.2.at hsl
  obtain ⟨sr, hsr, har⟩ := ht.2
  simp only [he, resultCursors] at hsl
  simp only [he, result] at hol
  have hn : ∀p ∈ DeliveryPaths.items true path 0 data, p ≠ path := by
    intro p hh
    obtain ⟨index, _, _, hbelow⟩ := hol.2 p (List.mem_append_left _ hh)
    exact below_child_ne hbelow
  refine ⟨sl ++ sr, ?_, ?_⟩
  · apply WorkCursorSeed.combine
    · simpa only [Completion.catchNull, he, resultCursors]
        using hsl.extend (cursorExtends_list_items path data hn)
    · apply WorkCursorSeed.stream (index := start)
      · simp [Completion.catchNull, he, resultCursors, listCursors, cursorAt, hp, hlen]
      · simpa only [hp] using hsr
  · simp only [Completion.catchNull, he, TypedResponse.result, TypedResponse.value]
    refine .combine ?_ (.stream (index := start) ?_ ?_)
    · simpa only [he, TypedResponse.result, List.append_assoc, List.singleton_append] using hal
    · simp [hp]
    · have hh :=
        har.mono
          (right := available ++ (path, Atom.list) :: TypedResponse.items path 0 data)
          (by
            intro entry hh; simpa only [List.mem_append, List.mem_singleton,
              List.mem_cons]
              using Or.elim (List.mem_append.mp hh) Or.inl
                (fun he => Or.inr (Or.inl (List.mem_singleton.mp he))))
      simpa only [hp] using hh

end GraphQL.IncrementalDelivery.Correctness.SourceAttachments
