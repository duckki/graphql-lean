import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedPathSlices
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedPaths

/-! Ownership algebra for mixed-work slice witnesses. Every combination preserves
the exact work tree; only the ghost indexes of stream slices are existential.
Disjoint scopes separate sibling fields and bounded ordinary/streamed list ranges.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedPaths

open GraphQL.IncrementalDelivery.Execution
open DeliveryPaths

theorem ownsWork_empty (containers : Bool) (scope : ResponsePath → Prop)
    : OwnsWork containers scope .empty :=
  ⟨[], .empty, owns_nil _⟩

theorem OwnsWork.mono {containers : Bool} {left right : ResponsePath → Prop} {work : Work}
    (h : OwnsWork containers left work) (hs : ∀ path, left path → right path)
    : OwnsWork containers right work := by
  obtain ⟨slices, hw, ho⟩ := h
  exact ⟨slices, hw, ho.mono hs⟩

theorem OwnsCompletion.mono {containers : Bool} {paths : α → List ResponsePath}
    {left right : ResponsePath → Prop} {completed : Completion α}
    (h : OwnsCompletion containers paths left completed)
    (hs : ∀ path, left path → right path)
    : OwnsCompletion containers paths right completed := by
  obtain ⟨slices, hw, ho⟩ := h
  exact ⟨slices, hw, ho.mono hs⟩

theorem OwnsItems.mono {containers : Bool} {path : ResponsePath} {index : Nat}
    {left right : ResponsePath → Prop} {items : List (Result ResponseValue × Work)}
    (h : OwnsItems containers path index left items) (hs : ∀ path, left path → right path)
    : OwnsItems containers path index right items := by
  obtain ⟨slices, hw, ho⟩ := h
  exact ⟨slices, hw, ho.mono hs⟩

theorem ownsWork_append {containers : Bool} {sa sb sc : ResponsePath → Prop}
    {left right : Work} (hl : OwnsWork containers sa left)
    (hr : OwnsWork containers sb right) (hd : ∀ path, sa path → sb path → False)
    (hls : ∀ path, sa path → sc path) (hrs : ∀ path, sb path → sc path)
    : OwnsWork containers sc (.append left right) := by
  obtain ⟨sl, hsl, hol⟩ := hl
  obtain ⟨sr, hsr, hor⟩ := hr
  exact ⟨
    sl ++ sr,
    .append hsl hsr,
    by simpa only [List.flatten_append] using owns_append hol hor hd hls hrs
  ⟩

theorem ownsCompletion_error (containers : Bool) (paths : α → List ResponsePath)
    (scope : ResponsePath → Prop) (errors : Nat)
    : OwnsCompletion containers paths scope (Completion.error errors) :=
  ⟨[], .empty, owns_nil _⟩

theorem ownsCompletion_pure {containers : Bool} {paths : α → List ResponsePath}
    {scope : ResponsePath → Prop} {data : α} (h : Owns scope (paths data))
    : OwnsCompletion containers paths scope (Completion.pure data) :=
  ⟨
    [],
    .empty,
    by simpa only [Completion.pure, result, List.flatten_nil, List.append_nil] using h
  ⟩

theorem ownsCompletion_combine {containers : Bool} {pa : α → List ResponsePath}
    {pb : β → List ResponsePath} {pc : γ → List ResponsePath} {f : α → β → γ}
    {sa sb sc : ResponsePath → Prop} {left : Completion α} {right : Completion β}
    (hf : ∀ a b, pc (f a b) = pa a ++ pb b) (hl : OwnsCompletion containers pa sa left)
    (hr : OwnsCompletion containers pb sb right) (hd : ∀ path, sa path → sb path → False)
    (hls : ∀ path, sa path → sc path) (hrs : ∀ path, sb path → sc path)
    : OwnsCompletion containers pc sc (Completion.combine f left right) := by
  cases he : left.result with
  | error errors =>
      cases hre : right.result <;>
        simp [Completion.combine, he, hre, GraphQL.Execution.Result.combine, ownsCompletion_error]
  | ok leftData =>
      rcases leftData with ⟨a, ea⟩
      cases hre : right.result with
      | error errors =>
          simp [Completion.combine, he, hre, GraphQL.Execution.Result.combine, ownsCompletion_error]
      | ok rightData =>
          rcases rightData with ⟨b, eb⟩
          obtain ⟨sl, hsl, hol⟩ := hl
          obtain ⟨sr, hsr, hor⟩ := hr
          have ho := owns_append hol hor hd hls hrs
          simp only [he, hre, result] at ho
          refine ⟨sl ++ sr, ?_, ?_⟩
          · simpa only [Completion.combine, he, hre, GraphQL.Execution.Result.combine]
              using WorkSlices.append hsl hsr
          · simp only [Completion.combine, he, hre, GraphQL.Execution.Result.combine,
              result, hf, List.flatten_append]
            apply ho.perm
            simpa only [List.append_assoc]
              using ((List.perm_append_comm (l₁ := pb b) (l₂ := sl.flatten)).append_left
                      (pa a)).append_right
                sr.flatten

theorem ownsCompletion_map {containers : Bool} {pa : α → List ResponsePath}
    {pb : β → List ResponsePath} {f : α → β} {scope : ResponsePath → Prop}
    {completed : Completion α} (hf : ∀ a, pb (f a) = pa a)
    (h : OwnsCompletion containers pa scope completed)
    : OwnsCompletion containers pb scope (completed.map f) := by
  cases he : completed.result with
  | error errors => simp [Completion.map, he, ownsCompletion_error]
  | ok data =>
      rcases data with ⟨data, errors⟩
      obtain ⟨slices, hw, ho⟩ := h
      refine ⟨slices, by simpa only [Completion.map, he] using hw, ?_⟩
      simpa only [Completion.map, he, result, hf] using ho

theorem ownsCompletion_catchNull {containers : Bool} {pa : α → List ResponsePath}
    {wrap : α → ResponseValue} {scope : ResponsePath → Prop} {path : ResponsePath}
    {completed : Completion α}
    (hf
      : ∀ a, value containers path (wrap a) = (if containers then [path] else []) ++ pa a)
    (h : OwnsCompletion containers pa scope completed)
    (hs : ∀ p, scope p → Below path p) (hn : ∀ p, scope p → p ≠ path)
    : OwnsCompletion containers (value containers path) (Below path)
        (completed.catchNull wrap) := by
  cases he : completed.result with
  | error errors =>
      refine ⟨[], ?_, ?_⟩
      · simp only [Completion.catchNull, he]
        exact .empty
      · simpa only [Completion.catchNull, he, result, value, List.flatten_nil,
          List.append_nil]
          using owns_singleton (below_self path)
  | ok data =>
      rcases data with ⟨data, errors⟩
      obtain ⟨slices, hw, ho⟩ := h
      refine ⟨slices, by simpa only [Completion.catchNull, he] using hw, ?_⟩
      simp only [Completion.catchNull, he, result, hf, List.append_assoc]
      simp only [he, result] at ho
      cases containers with
      | false => simpa using ho.mono hs
      | true =>
          apply owns_append (owns_singleton (rfl : path = path)) ho
          · intro p hp hc
            exact hn p hc hp.symm
          · intro p hp
            subst p
            exact below_self path
          · exact hs

theorem ownsCompletion_nonNull {containers : Bool} {path : ResponsePath}
    {completed : Completion ResponseValue}
    (h : OwnsCompletion containers (value containers path) (Below path) completed)
    : OwnsCompletion containers (value containers path) (Below path)
        completed.nonNull := by
  cases he : completed.result with
  | error errors =>
      simp [Completion.nonNull, he, nonNullCompletion,
        GraphQL.Execution.nonNullCompletion, ownsCompletion_error]
  | ok data =>
      rcases data with ⟨data, errors⟩
      cases data <;>
        simp only [Completion.nonNull, he, nonNullCompletion, GraphQL.Execution.nonNullCompletion]
      · exact ownsCompletion_error _ _ _ _
      all_goals
        obtain ⟨slices, hw, ho⟩ := h
        exact ⟨slices, hw, by simpa only [he] using ho⟩

theorem OwnsCompletion.deferred {containers : Bool} {path : ResponsePath}
    {scope : ResponsePath → Prop} {completed : Completion (List (Name × ResponseValue))}
    (h : OwnsCompletion containers (fields containers path) scope completed)
    (groups : List DeferredFragment)
    : OwnsWork containers scope
        (.deferred groups path completed.result completed.work) := by
  obtain ⟨slices, hw, ho⟩ := h
  exact ⟨_, .deferred hw, by simpa only [List.flatten_cons] using ho⟩

theorem ownsCompletion_appendWork {containers : Bool} {paths : α → List ResponsePath}
    {sa sb sc : ResponsePath → Prop} {completed : Completion α} {work : Work}
    (hl : OwnsCompletion containers paths sa completed) (hr : OwnsWork containers sb work)
    (hd : ∀ path, sa path → sb path → False)
    (hls : ∀ path, sa path → sc path) (hrs : ∀ path, sb path → sc path)
    : OwnsCompletion containers paths sc
        {completed with work := .append completed.work work} := by
  obtain ⟨sl, hsl, hol⟩ := hl
  obtain ⟨sr, hsr, hor⟩ := hr
  exact ⟨
    sl ++ sr,
    .append hsl hsr,
    by
      simpa only [List.flatten_append, List.append_assoc]
        using owns_append hol hor hd hls hrs
  ⟩

theorem ownsCompletion_combine_fields {containers : Bool} {path : ResponsePath}
    {leftNames rightNames : List Name}
    {left right : Completion (List (Name × ResponseValue))}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl
      : OwnsCompletion containers (fields containers path) (UnderFields path leftNames)
          left)
    (hr
      : OwnsCompletion containers (fields containers path) (UnderFields path rightNames)
          right)
    : OwnsCompletion containers (fields containers path)
        (UnderFields path (leftNames ++ rightNames))
        (Completion.combine List.append left right) := by
  apply ownsCompletion_combine (fields_append containers path) hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem ownsWork_append_fields {containers : Bool} {path : ResponsePath}
    {leftNames rightNames : List Name} {left right : Work}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl : OwnsWork containers (UnderFields path leftNames) left)
    (hr : OwnsWork containers (UnderFields path rightNames) right)
    : OwnsWork containers (UnderFields path (leftNames ++ rightNames))
        (.append left right) := by
  apply ownsWork_append hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem ownsCompletion_appendWork_fields {containers : Bool} {path : ResponsePath}
    {leftNames rightNames : List Name}
    {completed : Completion (List (Name × ResponseValue))} {work : Work}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl
      : OwnsCompletion containers (fields containers path) (UnderFields path leftNames)
          completed)
    (hr : OwnsWork containers (UnderFields path rightNames) work)
    : OwnsCompletion containers (fields containers path)
        (UnderFields path (leftNames ++ rightNames))
        {completed with work := .append completed.work work} := by
  apply ownsCompletion_appendWork hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem ownsCompletion_failedField (containers : Bool) (path : ResponsePath)
    (name : Name) (fieldType : TypeRef)
    : OwnsCompletion containers (fields containers path) (Below (path ++ [.field name]))
        {result := singleFieldResult name (handleFieldError fieldType)} := by
  refine ⟨[], .empty, ?_⟩
  cases fieldType <;>
    simp only [singleFieldResult, handleFieldError, GraphQL.Execution.singleFieldResult,
      GraphQL.Execution.handleFieldError, result, fields, value, List.flatten_nil, List.append_nil] <;>
    first | exact owns_nil _ | exact owns_singleton (below_self _)

theorem ownsItems_nil (containers : Bool) (path : ResponsePath) (index : Nat)
    (scope : ResponsePath → Prop)
    : OwnsItems containers path index scope [] :=
  ⟨[], .nil, owns_nil _⟩

theorem ownsItems_cons {containers : Bool} {path : ResponsePath} {index : Nat}
    {sa sb sc : ResponsePath → Prop} {completed : Completion ResponseValue}
    {items : List (Result ResponseValue × Work)}
    (hl
      : OwnsCompletion containers (value containers (path ++ [.index index])) sa
          completed)
    (hr : OwnsItems containers path (index + 1) sb items)
    (hd : ∀ p, sa p → sb p → False)
    (hls : ∀ p, sa p → sc p) (hrs : ∀ p, sb p → sc p)
    : OwnsItems containers path index sc
        ((completed.result, completed.work) :: items) := by
  obtain ⟨sl, hsl, hol⟩ := hl
  obtain ⟨sr, hsr, hor⟩ := hr
  exact ⟨
    _,
    .cons hsl hsr,
    by
      simpa only [List.flatten_cons, List.flatten_append, List.append_assoc]
        using owns_append hol hor hd hls hrs
  ⟩

theorem OwnsItems.stream {containers : Bool} {node : DeliveryNode} {index : Nat}
    {scope : ResponsePath → Prop} {items : List (Result ResponseValue × Work)}
    (h : OwnsItems containers node.path index scope items)
    : OwnsWork containers scope (.stream node items) := by
  obtain ⟨slices, hi, ho⟩ := h
  exact ⟨slices, .stream hi, ho⟩

end GraphQL.IncrementalDelivery.Semantics.MixedPaths
