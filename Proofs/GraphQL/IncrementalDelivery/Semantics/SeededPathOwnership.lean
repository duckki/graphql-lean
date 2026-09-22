import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedCursorSeeds
import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedPathOwnership

/-! Shared witnesses for cursor seeding and ownership. Keeping both properties on
the same slices avoids choosing unrelated existential stream offsets.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedPaths

open GraphQL.IncrementalDelivery.Execution
open DeliveryPaths
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)

def SeedOwnsCompletion (paths : α → List ResponsePath) (cursors : α → Cursors)
    (scope : ResponsePath → Prop) (completed : Completion α)
    : Prop :=
  ∃ slices,
    WorkCursorSeed (resultCursors cursors completed.result) completed.work slices
    ∧ Owns scope (result paths completed.result ++ slices.flatten)

def SeedOwnsWork (scope : ResponsePath → Prop) (work : Work) : Prop :=
  ∃ slices, (∀ cursors, WorkCursorSeed cursors work slices) ∧ Owns scope slices.flatten

def SeedOwnsItems (path : ResponsePath) (index : Nat) (scope : ResponsePath → Prop)
    (items : List (Result ResponseValue × Work))
    : Prop :=
  ∃ slices, ItemCursorSeed path index items slices ∧ Owns scope slices.flatten

theorem SeedOwnsCompletion.owns {paths : α → List ResponsePath} {cursors : α → Cursors}
    {scope : ResponsePath → Prop} {completed : Completion α}
    (h : SeedOwnsCompletion paths cursors scope completed)
    : OwnsCompletion true paths scope completed := by
  obtain ⟨s, hs, ho⟩ := h
  exact ⟨s, hs.slices, ho⟩

theorem SeedOwnsCompletion.mono {paths : α → List ResponsePath} {cursors : α → Cursors}
    {left right : ResponsePath → Prop} {completed : Completion α}
    (h : SeedOwnsCompletion paths cursors left completed) (hs : ∀p, left p → right p)
    : SeedOwnsCompletion paths cursors right completed := by
  obtain ⟨s, hw, ho⟩ := h
  exact ⟨s, hw, ho.mono hs⟩

theorem seeded_error (paths : α → List ResponsePath) (cursors : α → Cursors)
    (scope : ResponsePath → Prop) (errors : Nat)
    : SeedOwnsCompletion paths cursors scope (Completion.error errors) :=
  ⟨[], .empty, owns_nil _⟩

theorem seeded_pure {paths : α → List ResponsePath} {cursors : α → Cursors}
    {scope : ResponsePath → Prop} {data : α} (h : Owns scope (paths data))
    : SeedOwnsCompletion paths cursors scope (Completion.pure data) :=
  ⟨[], .empty, by simpa [Completion.pure, result] using h⟩

theorem seeded_combine {pa : α → List ResponsePath} {pb : β → List ResponsePath}
    {pc : γ → List ResponsePath} {ca : α → Cursors} {cb : β → Cursors}
    {cc : γ → Cursors} {f : α → β → γ} {sa sb sc : ResponsePath → Prop}
    {left : Completion α} {right : Completion β}
    (hf : ∀a b, pc (f a b) = pa a ++ pb b)
    (hc : ∀a b, cc (f a b) = ca a ++ cb b)
    (hca : ∀a, CursorHistory (ca a) (pa a))
    (hcb : ∀b, CursorHistory (cb b) (pb b))
    (hl : SeedOwnsCompletion pa ca sa left) (hr : SeedOwnsCompletion pb cb sb right)
    (hd : ∀p, sa p → sb p → False)
    (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : SeedOwnsCompletion pc cc sc (Completion.combine f left right) := by
  cases he : left.result with
  | error errors =>
      cases hre : right.result <;>
        simp [Completion.combine, he, hre, GraphQL.Execution.Result.combine, seeded_error]
  | ok leftData =>
      rcases leftData with ⟨a, ea⟩
      cases hre : right.result with
      | error errors =>
          simp [Completion.combine, he, hre, GraphQL.Execution.Result.combine, seeded_error]
      | ok rightData =>
          rcases rightData with ⟨b, eb⟩
          obtain ⟨sl, hsl, hol⟩ := hl
          obtain ⟨sr, hsr, hor⟩ := hr
          simp only [he, hre, resultCursors] at hsl hsr
          simp only [he, hre, result] at hol hor
          have hext : CursorExtends (cb b) (ca a ++ cb b) := by
            apply CursorExtends.prepend
            intro entry hm index hh
            exact hd entry.1 (hol.2 _ (List.mem_append_left _ (hca a entry hm)))
              (hor.2 _ (List.mem_append_left _ ((hcb b).lookup hh)))
          have ho := owns_append hol hor hd hls hrs
          refine ⟨sl ++ sr, ?_, ?_⟩
          · simpa only [Completion.combine, he, hre, GraphQL.Execution.Result.combine,
              resultCursors, hc] using WorkCursorSeed.combine
                (hsl.append_cursors (cb b)) (hsr.extend hext)
          · simp only [Completion.combine, he, hre, GraphQL.Execution.Result.combine,
              result, hf, List.flatten_append]
            apply ho.perm
            simpa only [List.append_assoc]
              using ((List.perm_append_comm (l₁ := pb b) (l₂ := sl.flatten)).append_left
                      (pa a)).append_right
                sr.flatten

theorem seeded_map {pa : α → List ResponsePath} {pb : β → List ResponsePath}
    {ca : α → Cursors} {cb : β → Cursors} {f : α → β}
    {scope : ResponsePath → Prop} {completed : Completion α}
    (hf : ∀a, pb (f a) = pa a) (hc : ∀a, cb (f a) = ca a)
    (h : SeedOwnsCompletion pa ca scope completed)
    : SeedOwnsCompletion pb cb scope (completed.map f) := by
  cases he : completed.result with
  | error errors => simp [Completion.map, he, seeded_error]
  | ok data =>
      rcases data with ⟨data, errors⟩
      obtain ⟨s, hs, ho⟩ := h
      refine ⟨s, ?_, ?_⟩
      · simpa only [Completion.map, he, resultCursors, hc] using hs
      · simpa only [Completion.map, he, result, hf] using ho

theorem seeded_catchNull {pa : α → List ResponsePath} {ca : α → Cursors}
    {wrap : α → ResponseValue} {scope : ResponsePath → Prop} {path : ResponsePath}
    {completed : Completion α}
    (hf : ∀a, value true path (wrap a) = [path] ++ pa a)
    (hc : ∀a, (∀p ∈ pa a, p ≠ path) → CursorExtends (ca a) (listCursors path (wrap a)))
    (h : SeedOwnsCompletion pa ca scope completed)
    (hs : ∀p, scope p → Below path p) (hn : ∀p, scope p → p ≠ path)
    : SeedOwnsCompletion (value true path) (listCursors path) (Below path)
        (completed.catchNull wrap) := by
  cases he : completed.result with
  | error errors =>
      refine ⟨[], ?_, ?_⟩
      · simp only [Completion.catchNull, he]; exact .empty
      · simpa only [Completion.catchNull, he, result, value, List.flatten_nil,
          List.append_nil]
          using owns_singleton (below_self path)
  | ok data =>
      rcases data with ⟨data, errors⟩
      obtain ⟨s, hw, ho⟩ := h
      simp only [he, resultCursors] at hw
      simp only [he, result] at ho
      refine ⟨s, ?_, ?_⟩
      · simpa only [Completion.catchNull, he, resultCursors]
          using hw.extend
            (hc data (fun p hp => hn p (ho.2 p (List.mem_append_left _ hp))))
      · simp only [Completion.catchNull, he, result, hf, List.append_assoc]
        exact owns_append (owns_singleton (rfl : path = path)) ho
          (fun p hp hh => hn p hh hp.symm)
          (fun _ hp => hp ▸ below_self _) hs

theorem seeded_nonNull {path : ResponsePath} {completed : Completion ResponseValue}
    (h : SeedOwnsCompletion (value true path) (listCursors path) (Below path) completed)
    : SeedOwnsCompletion (value true path) (listCursors path) (Below path)
        completed.nonNull := by
  cases he : completed.result with
  | error errors =>
      simp [Completion.nonNull, he, nonNullCompletion,
        GraphQL.Execution.nonNullCompletion, seeded_error]
  | ok data =>
      rcases data with ⟨data, errors⟩
      cases data <;>
        simp only [Completion.nonNull, he, nonNullCompletion, GraphQL.Execution.nonNullCompletion]
      · exact seeded_error _ _ _ _
      all_goals
        obtain ⟨s, hw, ho⟩ := h
        exact ⟨s, by simpa only [he] using hw, by simpa only [he] using ho⟩

theorem SeedOwnsCompletion.executionGroup {path : ResponsePath}
    {scope : ResponsePath → Prop} {completed : Completion (List (Name × ResponseValue))}
    (h : SeedOwnsCompletion (fields true path) (fieldCursors path) scope completed)
    (groups : List DeferredFragment)
    : SeedOwnsWork scope
        (.executionGroup groups path completed.result completed.work) := by
  obtain ⟨s, hw, ho⟩ := h
  exact ⟨_, fun _ => .executionGroup hw, by simpa only [List.flatten_cons] using ho⟩

theorem seeded_work_combine {sa sb sc : ResponsePath → Prop} {left right : Work}
    (hl : SeedOwnsWork sa left) (hr : SeedOwnsWork sb right)
    (hd : ∀p, sa p → sb p → False) (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : SeedOwnsWork sc (.combine left right) := by
  obtain ⟨sl, hsl, hol⟩ := hl
  obtain ⟨sr, hsr, hor⟩ := hr
  exact ⟨
    sl ++ sr,
    fun c => .combine (hsl c) (hsr c),
    by simpa only [List.flatten_append] using owns_append hol hor hd hls hrs
  ⟩

theorem seeded_combineWork {pa : α → List ResponsePath} {ca : α → Cursors}
    {sa sb sc : ResponsePath → Prop} {completed : Completion α} {work : Work}
    (hl : SeedOwnsCompletion pa ca sa completed) (hr : SeedOwnsWork sb work)
    (hd : ∀p, sa p → sb p → False) (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : SeedOwnsCompletion pa ca sc
        {completed with work := .combine completed.work work} := by
  obtain ⟨sl, hsl, hol⟩ := hl
  obtain ⟨sr, hsr, hor⟩ := hr
  exact ⟨
    sl ++ sr,
    .combine hsl (hsr _),
    by
      simpa only [List.flatten_append, List.append_assoc]
        using owns_append hol hor hd hls hrs
  ⟩

theorem fieldCursors_append (path : ResponsePath)
    (left right : List (Name × ResponseValue))
    : fieldCursors path (left ++ right)
      = fieldCursors path left ++ fieldCursors path right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp [fieldCursors, ih, List.append_assoc]

theorem seeded_combine_fields {path : ResponsePath} {leftNames rightNames : List Name}
    {left right : Completion (List (Name × ResponseValue))}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl
      : SeedOwnsCompletion (fields true path) (fieldCursors path)
          (UnderFields path leftNames) left)
    (hr
      : SeedOwnsCompletion (fields true path) (fieldCursors path)
          (UnderFields path rightNames) right)
    : SeedOwnsCompletion (fields true path) (fieldCursors path)
        (UnderFields path (leftNames ++ rightNames))
        (Completion.combine List.append left right) := by
  apply seeded_combine (fields_append true path) (fieldCursors_append path)
    (fieldCursors_positions path) (fieldCursors_positions path) hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem seeded_work_combine_fields {path : ResponsePath}
    {leftNames rightNames : List Name} {left right : Work}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl : SeedOwnsWork (UnderFields path leftNames) left)
    (hr : SeedOwnsWork (UnderFields path rightNames) right)
    : SeedOwnsWork (UnderFields path (leftNames ++ rightNames))
        (.combine left right) := by
  apply seeded_work_combine hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem seeded_combineWork_fields {path : ResponsePath} {leftNames rightNames : List Name}
    {completed : Completion (List (Name × ResponseValue))} {work : Work}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl
      : SeedOwnsCompletion (fields true path) (fieldCursors path)
          (UnderFields path leftNames) completed)
    (hr : SeedOwnsWork (UnderFields path rightNames) work)
    : SeedOwnsCompletion (fields true path) (fieldCursors path)
        (UnderFields path (leftNames ++ rightNames))
        {completed with work := .combine completed.work work} := by
  apply seeded_combineWork hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem seeded_failedField (path : ResponsePath) (name : Name) (fieldType : TypeRef)
    : SeedOwnsCompletion (fields true path) (fieldCursors path)
        (Below (path ++ [.field name]))
        {result := singleFieldResult name (handleFieldError fieldType)} := by
  refine ⟨[], .empty, ?_⟩
  cases fieldType <;>
    simp only [singleFieldResult, handleFieldError, GraphQL.Execution.singleFieldResult,
      GraphQL.Execution.handleFieldError, result, fields, value, List.flatten_nil, List.append_nil] <;>
    first | exact owns_nil _ | exact owns_singleton (below_self _)

theorem seeded_items_cons {path : ResponsePath} {index : Nat}
    {sa sb sc : ResponsePath → Prop} {completed : Completion ResponseValue}
    {items : List (Result ResponseValue × Work)}
    (hl
      : SeedOwnsCompletion (value true (path ++ [.index index]))
          (listCursors (path ++ [.index index])) sa completed)
    (hr : SeedOwnsItems path (index + 1) sb items)
    (hd : ∀p, sa p → sb p → False) (hls : ∀p, sa p → sc p) (hrs : ∀p, sb p → sc p)
    : SeedOwnsItems path index sc ((completed.result, completed.work) :: items) := by
  obtain ⟨sl, hsl, hol⟩ := hl
  obtain ⟨sr, hsr, hor⟩ := hr
  exact ⟨
    _,
    .cons hsl hsr,
    by
      simpa only [List.flatten_cons, List.flatten_append, List.append_assoc]
        using owns_append hol hor hd hls hrs
  ⟩

theorem cursorExtends_list_items (path : ResponsePath) (data : List ResponseValue)
    (h : ∀p ∈ items true path 0 data, p ≠ path)
    : CursorExtends (itemCursors path 0 data) (listCursors path (.list data)) := by
  change CursorExtends (itemCursors path 0 data) ([(path, data.length)] ++ itemCursors path 0 data)
  apply CursorExtends.prepend
  intro entry he index hc
  obtain rfl := List.mem_singleton.mp he
  exact h _ ((itemCursors_positions path 0 data).lookup hc) rfl

theorem seeded_items_cons_underItems {path : ResponsePath} {index : Nat}
    {head : Completion ResponseValue} {tail : List (Result ResponseValue × Work)}
    (hh
      : SeedOwnsCompletion (value true (path ++ [.index index]))
          (listCursors (path ++ [.index index])) (Below (path ++ [.index index])) head)
    (ht : SeedOwnsItems path (index + 1) (UnderItems path (index + 1)) tail)
    : SeedOwnsItems path index (UnderItems path index)
        ((head.result, head.work) :: tail) := by
  apply seeded_items_cons hh ht
  · exact fun _ => underItems_disjoint
  · exact fun _ hp => ⟨index, Nat.le_refl _, hp⟩
  · intro p ⟨next, hn, hp⟩
    exact ⟨next, by omega, hp⟩

theorem seeded_streamPrefix {path : ResponsePath} {finish start : Nat}
    {initial : Completion (List ResponseValue)} {data : List ResponseValue}
    {errors : Nat} {node : DeliveryNode} {items : List (Result ResponseValue × Work)}
    (hi
      : SeedOwnsCompletion (DeliveryPaths.items true path 0) (itemCursors path 0)
          (UnderItemRange path 0 finish) initial)
    (he : initial.result = .ok (data, errors)) (hb : finish ≤ start)
    (hlen : data.length = start) (hp : node.path = path)
    (ht : SeedOwnsItems path start (UnderItems path start) items)
    : SeedOwnsCompletion (value true path) (listCursors path) (Below path)
        {
          initial.catchNull ResponseValue.list with
            work :=
              .combine (initial.catchNull ResponseValue.list).work (.stream node items)
        } := by
  obtain ⟨sl, hsl, hol⟩ := hi
  obtain ⟨sr, hsr, hor⟩ := ht
  simp only [he, resultCursors] at hsl
  simp only [he, result] at hol
  have hn : ∀p ∈ DeliveryPaths.items true path 0 data, p ≠ path := by
    intro p hp
    obtain ⟨index, _, _, hbelow⟩ := hol.2 p (List.mem_append_left _ hp)
    exact below_child_ne hbelow
  have hprefix : Owns (fun p => p = path ∨ UnderItemRange path 0 finish p)
      ([path] ++ (DeliveryPaths.items true path 0 data ++ sl.flatten)) := by
    apply owns_append (owns_singleton (rfl : path = path)) hol
    · intro p hp hrange
      obtain ⟨index, _, _, hbelow⟩ := hrange
      exact below_child_ne hbelow hp.symm
    · exact fun _ hp => Or.inl hp.symm
    · exact fun _ => Or.inr
  refine ⟨sl ++ sr, ?_, ?_⟩
  · apply WorkCursorSeed.combine
    · simpa only [Completion.catchNull, he, resultCursors]
        using hsl.extend (cursorExtends_list_items path data hn)
    · apply WorkCursorSeed.stream (index := start)
      · simp [Completion.catchNull, he, resultCursors, listCursors, cursorAt, hp, hlen]
      · simpa only [hp] using hsr
  · simp only [Completion.catchNull, he, result, value, List.flatten_append, List.append_assoc]
    have ho : Owns (Below path)
        (([path] ++ (DeliveryPaths.items true path 0 data ++ sl.flatten)) ++ sr.flatten) := by
      apply owns_append hprefix hor
      · intro p hprefix htail
        rcases hprefix with hroot | ⟨left, _, hl, hleft⟩
        · exact underItems_ne htail hroot
        · obtain ⟨right, hr, hright⟩ := htail
          have heq := below_children_eq hleft hright
          cases heq
          omega
      · intro p hprefix
        rcases hprefix with hroot | ⟨index, _, _, hbelow⟩
        · subst p; exact below_self _
        · exact below_child hbelow
      · exact fun _ => underItems_below
    simpa only [List.append_assoc, ↓reduceIte] using ho

end GraphQL.IncrementalDelivery.Semantics.MixedPaths
