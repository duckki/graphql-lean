import Proofs.GraphQL.IncrementalDelivery.Semantics.DeliveryPaths
import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning

/-! Separation lemmas for absolute response positions, including nested work. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution
open DeliveryPaths

/-- The scope records where *all* initial and future positions of a completion live. -/
def Owns (scope : ResponsePath → Prop) (paths : List ResponsePath) : Prop :=
  paths.Nodup ∧ ∀ path ∈ paths, scope path

def Below (base path : ResponsePath) : Prop := ∃ suffix, path = base ++ suffix

def UnderFields (base : ResponsePath) (names : List Name) (path : ResponsePath) : Prop :=
  ∃ name ∈ names, Below (base ++ [.field name]) path

def UnderItems (base : ResponsePath) (start : Nat) (path : ResponsePath) : Prop :=
  ∃ index, start ≤ index ∧ Below (base ++ [.index index]) path

theorem owns_nil (scope : ResponsePath → Prop) : Owns scope [] := by
  simp [Owns]

theorem owns_singleton {scope : ResponsePath → Prop} {path : ResponsePath}
    (h : scope path)
    : Owns scope [path] := by simpa [Owns] using h

theorem Owns.mono {left right : ResponsePath → Prop} {paths : List ResponsePath}
    (h : Owns left paths) (hs : ∀ path, left path → right path)
    : Owns right paths :=
  ⟨h.1, fun path hp => hs path (h.2 path hp)⟩

theorem Owns.perm {scope : ResponsePath → Prop} {left right : List ResponsePath}
    (h : Owns scope left) (hp : right.Perm left)
    : Owns scope right :=
  ⟨hp.nodup_iff.mpr h.1, fun path hm => h.2 path (hp.mem_iff.mp hm)⟩

theorem owns_append {left right scope : ResponsePath → Prop} {xs ys : List ResponsePath}
    (hx : Owns left xs) (hy : Owns right ys)
    (hd : ∀ path, left path → right path → False)
    (hl : ∀ path, left path → scope path) (hr : ∀ path, right path → scope path)
    : Owns scope (xs ++ ys) := by
  refine ⟨List.nodup_append.mpr ⟨hx.1, hy.1, ?_⟩, ?_⟩
  · intro a ha b hb hab
    subst b
    exact hd a (hx.2 a ha) (hy.2 a hb)
  · intro path hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hl path (hx.2 path hp)
    · exact hr path (hy.2 path hp)

theorem below_self (path : ResponsePath) : Below path path := ⟨[], by simp⟩

theorem below_child {base path : ResponsePath} {segment : ResponsePathSegment}
    (h : Below (base ++ [segment]) path)
    : Below base path := by
  rcases h with ⟨suffix, rfl⟩
  exact ⟨segment :: suffix, by simp⟩

theorem below_child_ne {base path : ResponsePath} {segment : ResponsePathSegment}
    (h : Below (base ++ [segment]) path)
    : path ≠ base := by
  rcases h with ⟨suffix, rfl⟩
  intro he
  have := congrArg List.length he
  simp at this

theorem below_children_eq {base path : ResponsePath} {left right : ResponsePathSegment}
    (hl : Below (base ++ [left]) path) (hr : Below (base ++ [right]) path)
    : left = right := by
  rcases hl with ⟨ls, hl⟩
  rcases hr with ⟨rs, hr⟩
  have he : left :: ls = right :: rs := by
    apply List.append_cancel_left (as := base)
    simpa using hl.symm.trans hr
  exact (List.cons.inj he).1

theorem underFields_below {base path : ResponsePath} {names : List Name}
    (h : UnderFields base names path)
    : Below base path := by
  rcases h with ⟨_, _, h⟩
  exact below_child h

theorem underFields_ne {base path : ResponsePath} {names : List Name}
    (h : UnderFields base names path)
    : path ≠ base := by
  rcases h with ⟨_, _, h⟩
  exact below_child_ne h

theorem underFields_mono {base path : ResponsePath} {left right : List Name}
    (hs : ∀ name ∈ left, name ∈ right) (h : UnderFields base left path)
    : UnderFields base right path := by
  rcases h with ⟨name, hn, hp⟩
  exact ⟨name, hs name hn, hp⟩

theorem underFields_disjoint {base path : ResponsePath} {left right : List Name}
    (hd : ∀ name ∈ left, name ∉ right)
    (hl : UnderFields base left path) (hr : UnderFields base right path)
    : False := by
  rcases hl with ⟨ln, hln, hl⟩
  rcases hr with ⟨rn, hrn, hr⟩
  have he := below_children_eq hl hr
  cases he
  exact hd ln hln hrn

theorem underItems_below {base path : ResponsePath} {start : Nat}
    (h : UnderItems base start path)
    : Below base path := by
  rcases h with ⟨_, _, h⟩
  exact below_child h

theorem underItems_ne {base path : ResponsePath} {start : Nat}
    (h : UnderItems base start path)
    : path ≠ base := by
  rcases h with ⟨_, _, h⟩
  exact below_child_ne h

theorem underItems_disjoint {base path : ResponsePath} {index : Nat}
    (hl : Below (base ++ [.index index]) path)
    (hr : UnderItems base (index + 1) path)
    : False := by
  rcases hr with ⟨next, hn, hr⟩
  have he := below_children_eq hl hr
  cases he
  omega

@[simp]
theorem fields_append (containers : Bool) (path : ResponsePath)
    (left right : List (Name × ResponseValue))
    : fields containers path (left ++ right)
      = fields containers path left ++ fields containers path right := by
  induction left with
  | nil => rfl
  | cons head rest ih => simp [fields, ih, List.append_assoc]

def OwnsCompletion (containers : Bool) (paths : α → List ResponsePath)
    (scope : ResponsePath → Prop) (completed : Completion α)
    : Prop :=
  Owns scope (completion containers paths completed)

theorem ownsCompletion_error (containers : Bool) (paths : α → List ResponsePath)
    (scope : ResponsePath → Prop) (errors : Nat)
    : OwnsCompletion containers paths scope (Completion.error errors) :=
  owns_nil _

theorem ownsCompletion_pure {containers : Bool} {paths : α → List ResponsePath}
    {scope : ResponsePath → Prop} {data : α} (h : Owns scope (paths data))
    : OwnsCompletion containers paths scope (Completion.pure data) := by
  simpa [OwnsCompletion, completion, result, Completion.pure, work] using h

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
        simp [Completion.combine, he, hre, GraphQL.Execution.Result.combine,
          ownsCompletion_error]
  | ok leftData =>
      rcases leftData with ⟨a, ea⟩
      cases hre : right.result with
      | error errors =>
          simp [Completion.combine, he, hre, GraphQL.Execution.Result.combine,
            ownsCompletion_error]
      | ok rightData =>
          rcases rightData with ⟨b, eb⟩
          have h := owns_append hl hr hd hls hrs
          simp only [OwnsCompletion, completion, he, hre, result] at h ⊢
          simp only [Completion.combine, he, hre, GraphQL.Execution.Result.combine,
            work, hf]
          apply h.perm
          simpa [List.append_assoc]
            using ((List.perm_append_comm (l₁ := pb b)
                      (l₂ := work containers left.work)).append_left
                    (pa a)).append_right
              (work containers right.work)

theorem ownsCompletion_map {containers : Bool} {pa : α → List ResponsePath}
    {pb : β → List ResponsePath} {f : α → β} {scope : ResponsePath → Prop}
    {completed : Completion α} (hf : ∀ a, pb (f a) = pa a)
    (h : OwnsCompletion containers pa scope completed)
    : OwnsCompletion containers pb scope (completed.map f) := by
  cases he : completed.result with
  | error errors => simp [Completion.map, he, ownsCompletion_error]
  | ok data =>
      rcases data with ⟨data, errors⟩
      simpa [OwnsCompletion, completion, Completion.map, he, result, hf] using h

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
      simpa [OwnsCompletion, completion, Completion.catchNull, he, result, value, work]
        using owns_singleton (below_self path)
  | ok data =>
      rcases data with ⟨data, errors⟩
      change Owns _ _
      simp only [completion, Completion.catchNull, he, result, hf, List.append_assoc]
      simp only [OwnsCompletion, completion, he, result] at h
      cases containers with
      | false => simpa using h.mono hs
      | true =>
          apply owns_append (owns_singleton (rfl : path = path)) h
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
        simp only [Completion.nonNull, he, nonNullCompletion,
          GraphQL.Execution.nonNullCompletion]
      · exact ownsCompletion_error _ _ _ _
      all_goals simpa [OwnsCompletion, completion, he] using h

end GraphQL.IncrementalDelivery.Semantics
