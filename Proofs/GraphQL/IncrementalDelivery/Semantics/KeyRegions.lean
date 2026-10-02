import Proofs.GraphQL.IncrementalDelivery.Semantics.KeyRoles

/-! Stream boundaries partition execution-key regions. Deferred keys, including
ancestor placeholders, may repeat inside one region; different regions must be
disjoint. Allocation intervals compose computations without forbidding inherited
defer-key reuse in the common root region.
-/

namespace GraphQL.IncrementalDelivery.Semantics.KeyRegions

open GraphQL.IncrementalDelivery.Execution

def Disjoint (left right : List Nat) : Prop := ∀ key ∈ left, key ∉ right

def rootKeys : Work → List Nat
  | .empty => []
  | .combine left right => rootKeys left ++ rootKeys right
  | .executionGroup groups _ _ children =>
      groups.flatMap KeyRoles.fragmentKeys ++ rootKeys children
  | .stream node _ => [node.key]

def hiddenRegions : Work → List (List Nat)
  | .empty => []
  | .combine left right => hiddenRegions left ++ hiddenRegions right
  | .executionGroup _ _ _ children => hiddenRegions children
  | .stream _ items => items.flatMap (fun item => rootKeys item.2 :: hiddenRegions item.2)
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def regions (work : Work) : List (List Nat) := rootKeys work :: hiddenRegions work

def allKeys (work : Work) : List Nat := rootKeys work ++ (hiddenRegions work).flatten

def WorkSeparated (work : Work) : Prop := (regions work).Pairwise Disjoint

structure Output (inherited : List Nat) (start finish : Nat) (work : Work) : Prop where
  monotone : start ≤ finish
  separated : WorkSeparated work
  bounded : ∀ key ∈ allKeys work, key < finish
  root : ∀ key ∈ rootKeys work, key ∈ inherited ∨ start ≤ key
  hidden : ∀ region ∈ hiddenRegions work, ∀ key ∈ region, start ≤ key

def itemRegions (items : List (Result ResponseValue × Work)) : List (List Nat) :=
  items.flatMap (fun item => regions item.2)

structure ItemsOutput (start finish : Nat) (items : List (Result ResponseValue × Work))
    : Prop where
  monotone : start ≤ finish
  separated : (itemRegions items).Pairwise Disjoint
  bounds : ∀ region ∈ itemRegions items, ∀ key ∈ region, start ≤ key ∧ key < finish

theorem Disjoint.symm {left right : List Nat} (h : Disjoint left right)
    : Disjoint right left :=
  fun key hr hl => h key hl hr

theorem Disjoint.mono {left right smallLeft smallRight : List Nat}
    (h : Disjoint left right) (hl : smallLeft.Subset left) (hr : smallRight.Subset right)
    : Disjoint smallLeft smallRight :=
  fun key hleft hright => h key (hl hleft) (hr hright)

theorem Disjoint.append_left {left middle right : List Nat}
    (hl : Disjoint left right) (hm : Disjoint middle right)
    : Disjoint (left ++ middle) right := by
  intro key hk
  exact (List.mem_append.mp hk).elim (hl key) (hm key)

theorem Disjoint.append_right {left middle right : List Nat}
    (hm : Disjoint left middle) (hr : Disjoint left right)
    : Disjoint left (middle ++ right) :=
  (hm.symm.append_left hr.symm).symm

theorem separated_iff (work : Work)
    : WorkSeparated work
      ↔ (∀ region ∈ hiddenRegions work, Disjoint (rootKeys work) region)
        ∧ (hiddenRegions work).Pairwise Disjoint :=
  List.pairwise_cons

theorem separated_merge (leftRoot rightRoot : List Nat)
    (leftHidden rightHidden : List (List Nat))
    (hl : (leftRoot :: leftHidden).Pairwise Disjoint)
    (hr : (rightRoot :: rightHidden).Pairwise Disjoint)
    (hlr : ∀ region ∈ rightHidden, Disjoint leftRoot region)
    (hrl : ∀ region ∈ leftHidden, Disjoint rightRoot region)
    (hh : ∀ left ∈ leftHidden, ∀ right ∈ rightHidden, Disjoint left right)
    : ((leftRoot ++ rightRoot) :: (leftHidden ++ rightHidden)).Pairwise Disjoint := by
  have hl' := List.pairwise_cons.mp hl
  have hr' := List.pairwise_cons.mp hr
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_append.mpr ⟨hl'.2, hr'.2, hh⟩⟩
  intro region hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (hl'.1 region hm).append_left (hrl region hm)
  · exact (hlr region hm).append_left (hr'.1 region hm)

theorem rootKeys_subset_allKeys (work : Work) : (rootKeys work).Subset (allKeys work) :=
  List.subset_append_left _ _

theorem hiddenRegion_subset_allKeys (work : Work) {region : List Nat}
    (hr : region ∈ hiddenRegions work)
    : region.Subset (allKeys work) :=
  fun _ hk => List.mem_append_right _ (List.mem_flatten.mpr ⟨region, hr, hk⟩)

theorem region_subset_allKeys (work : Work) {region : List Nat}
    (hr : region ∈ regions work)
    : region.Subset (allKeys work) := by
  rcases List.mem_cons.mp hr with rfl | hr
  · exact rootKeys_subset_allKeys work
  · exact hiddenRegion_subset_allKeys work hr

theorem mem_allKeys_combine (left right : Work) (key : Nat)
    : key ∈ allKeys (.combine left right) ↔ key ∈ allKeys left ∨ key ∈ allKeys right := by
  simp only [allKeys, rootKeys, hiddenRegions, List.flatten_append, List.mem_append]
  simp only [or_assoc, or_left_comm]

theorem Output.root_bounded {inherited : List Nat} {start finish : Nat} {work : Work}
    (h : Output inherited start finish work) {key : Nat} (hk : key ∈ rootKeys work)
    : key < finish :=
  h.bounded key (rootKeys_subset_allKeys work hk)

theorem Output.hidden_bounded {inherited : List Nat} {start finish : Nat} {work : Work}
    (h : Output inherited start finish work) {region : List Nat}
    (hr : region ∈ hiddenRegions work) {key : Nat} (hk : key ∈ region)
    : key < finish :=
  h.bounded key (hiddenRegion_subset_allKeys work hr hk)

theorem Output.empty (inherited : List Nat) {start finish : Nat} (h : start ≤ finish)
    : Output inherited start finish .empty :=
  ⟨
    h,
    by simp [WorkSeparated, regions, rootKeys, hiddenRegions],
    by simp [allKeys, rootKeys, hiddenRegions],
    by simp [rootKeys],
    by simp [hiddenRegions]
  ⟩

theorem Output.widen_finish {inherited : List Nat} {start finish upper : Nat}
    {work : Work} (h : Output inherited start finish work) (hu : finish ≤ upper)
    : Output inherited start upper work :=
  ⟨
    Nat.le_trans h.monotone hu,
    h.separated,
    fun key hk => Nat.lt_of_lt_of_le (h.bounded key hk) hu,
    h.root,
    h.hidden
  ⟩

theorem Output.rebase {inherited nextInherited : List Nat} {start nextStart finish : Nat}
    {work : Work} (h : Output nextInherited nextStart finish work)
    (hs : start ≤ nextStart) (hi : ∀ key ∈ nextInherited, key ∈ inherited ∨ start ≤ key)
    : Output inherited start finish work := by
  refine ⟨Nat.le_trans hs h.monotone, h.separated, h.bounded, ?_, ?_⟩
  · intro key hk
    exact (h.root key hk).elim (hi key) (fun hkey => Or.inr (Nat.le_trans hs hkey))
  · intro region hr key hk
    exact Nat.le_trans hs (h.hidden region hr key hk)

theorem Output.append {inherited : List Nat} {start middle finish : Nat}
    {left right : Work} (hl : Output inherited start middle left)
    (hr : Output inherited middle finish right) (hi : ∀ key ∈ inherited, key < start)
    : Output inherited start finish (.combine left right) := by
  refine ⟨Nat.le_trans hl.monotone hr.monotone, ?_, ?_, ?_, ?_⟩
  · simp only [WorkSeparated, regions, rootKeys, hiddenRegions]
    apply separated_merge _ _ _ _ hl.separated hr.separated
    · intro region hm key hk hregion
      have := hl.root_bounded hk
      have := hr.hidden region hm key hregion
      omega
    · intro region hm key hk hregion
      rcases hr.root key hk with hk | hk
      · have := hi key hk
        have := hl.hidden region hm key hregion
        omega
      · have := hl.hidden_bounded hm hregion
        omega
    · intro leftRegion hlr rightRegion hrr key hleft hright
      have := hl.hidden_bounded hlr hleft
      have := hr.hidden rightRegion hrr key hright
      omega
  · intro key hk
    rcases (mem_allKeys_combine left right key).mp hk with hk | hk
    · exact Nat.lt_of_lt_of_le (hl.bounded key hk) hr.monotone
    · exact hr.bounded key hk
  · intro key hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hl.root key hk
    · exact (hr.root key hk).elim Or.inl (fun hkey => Or.inr (Nat.le_trans hl.monotone hkey))
  · intro region hm key hk
    rw [hiddenRegions] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hl.hidden region hm key hk
    · exact Nat.le_trans hl.monotone (hr.hidden region hm key hk)

theorem Output.executionGroup {inherited : List Nat} {start finish : Nat}
    {children : Work} (h : Output inherited start finish children)
    (groups : List DeferredFragment) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue)))
    (hg : (groups.flatMap KeyRoles.fragmentKeys).Subset inherited)
    (hi : ∀ key ∈ inherited, key < start)
    : Output inherited start finish (.executionGroup groups path result children) := by
  refine ⟨h.monotone, ?_, ?_, ?_, ?_⟩
  · have hs := (separated_iff children).mp h.separated
    apply (separated_iff _).mpr
    simp only [rootKeys, hiddenRegions]
    refine ⟨?_, hs.2⟩
    intro region hr
    apply Disjoint.append_left _ (hs.1 region hr)
    intro key hk hregion
    have := hi key (hg hk)
    have := h.hidden region hr key hregion
    omega
  · intro key hk
    simp only [allKeys, rootKeys, hiddenRegions, List.mem_append, or_assoc] at hk
    rcases hk with hk | hk
    · exact Nat.lt_of_lt_of_le (hi key (hg hk)) h.monotone
    · exact h.bounded key (List.mem_append.mpr hk)
  · intro key hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl (hg hk)
    · exact h.root key hk
  · simpa only [hiddenRegions] using h.hidden

theorem Output.all_fresh {start finish : Nat} {work : Work}
    (h : Output [] start finish work) (key : Nat) (hk : key ∈ allKeys work)
    : start ≤ key ∧ key < finish := by
  refine ⟨?_, h.bounded key hk⟩
  rcases List.mem_append.mp hk with hk | hk
  · simpa using h.root key hk
  · obtain ⟨region, hr, hk⟩ := List.mem_flatten.mp hk
    exact h.hidden region hr key hk

theorem ItemsOutput.empty {start finish : Nat} (h : start ≤ finish)
    : ItemsOutput start finish [] :=
  ⟨h, by simp [itemRegions], by simp [itemRegions]⟩

theorem ItemsOutput.widen {start finish lower upper : Nat}
    {items : List (Result ResponseValue × Work)} (h : ItemsOutput start finish items)
    (hl : lower ≤ start) (hu : finish ≤ upper)
    : ItemsOutput lower upper items :=
  ⟨
    Nat.le_trans hl (Nat.le_trans h.monotone hu),
    h.separated,
    fun region hr key hk =>
      ⟨
        Nat.le_trans hl (h.bounds region hr key hk).1,
        Nat.lt_of_lt_of_le (h.bounds region hr key hk).2 hu
      ⟩
  ⟩

theorem ItemsOutput.cons {start middle finish : Nat} {children : Work}
    {items : List (Result ResponseValue × Work)} (head : Output [] start middle children)
    (tail : ItemsOutput middle finish items) (result : Result ResponseValue)
    : ItemsOutput start finish ((result, children) :: items) := by
  refine ⟨Nat.le_trans head.monotone tail.monotone, ?_, ?_⟩
  · simp only [itemRegions, List.flatMap_cons]
    apply List.pairwise_append.mpr
    refine ⟨head.separated, tail.separated, ?_⟩
    intro left hl right hr key hleft hright
    have := head.bounded key (region_subset_allKeys children hl hleft)
    have := (tail.bounds right hr key hright).1
    omega
  · intro region hm key hk
    rcases List.mem_append.mp hm with hm | hm
    · have hh := head.all_fresh key (region_subset_allKeys children hm hk)
      exact ⟨hh.1, Nat.lt_of_lt_of_le hh.2 tail.monotone⟩
    · have hh := tail.bounds region hm key hk
      exact ⟨Nat.le_trans head.monotone hh.1, hh.2⟩

theorem Output.stream (inherited : List Nat) (node : DeliveryNode)
    {finish : Nat} {items : List (Result ResponseValue × Work)}
    (h : ItemsOutput (node.key + 1) finish items)
    : Output inherited node.key finish (.stream node items) := by
  refine ⟨by have := h.monotone; omega, ?_, ?_, ?_, ?_⟩
  · apply (separated_iff _).mpr
    simp only [rootKeys, hiddenRegions]
    refine ⟨?_, h.separated⟩
    intro region hr key hk hregion
    obtain rfl := List.mem_singleton.mp hk
    have := (h.bounds region hr node.key hregion).1
    omega
  · intro key hk
    simp only [allKeys, rootKeys, hiddenRegions, List.mem_append, List.mem_singleton] at hk
    rcases hk with rfl | hk
    · exact h.monotone
    · obtain ⟨region, hr, hk⟩ := List.mem_flatten.mp hk
      exact (h.bounds region hr key hk).2
  · intro key hk
    obtain rfl := List.mem_singleton.mp hk
    exact Or.inr (Nat.le_refl _)
  · intro region hr key hk
    rw [hiddenRegions] at hr
    have := (h.bounds region hr key hk).1
    omega

end GraphQL.IncrementalDelivery.Semantics.KeyRegions
