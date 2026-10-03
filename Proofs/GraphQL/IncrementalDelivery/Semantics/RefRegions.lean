import Proofs.GraphQL.IncrementalDelivery.Semantics.RefRoles

/-! Stream boundaries partition execution-ref regions. Deferred refs, including
ancestor placeholders, may repeat inside one region; different regions must be
disjoint. Allocation intervals compose computations without forbidding inherited
defer-ref reuse in the common root region.
-/

namespace GraphQL.IncrementalDelivery.Semantics.RefRegions

open GraphQL.IncrementalDelivery.Execution

def Disjoint (left right : List Nat) : Prop := ∀ ref ∈ left, ref ∉ right

def rootRefs : Work → List Nat
  | .empty => []
  | .combine left right => rootRefs left ++ rootRefs right
  | .executionGroup groups _ _ children =>
      groups.flatMap RefRoles.fragmentRefs ++ rootRefs children
  | .stream node _ => [node.ref]

def hiddenRegions : Work → List (List Nat)
  | .empty => []
  | .combine left right => hiddenRegions left ++ hiddenRegions right
  | .executionGroup _ _ _ children => hiddenRegions children
  | .stream _ items => items.flatMap (fun item => rootRefs item.2 :: hiddenRegions item.2)
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def regions (work : Work) : List (List Nat) := rootRefs work :: hiddenRegions work

def allRefs (work : Work) : List Nat := rootRefs work ++ (hiddenRegions work).flatten

def WorkSeparated (work : Work) : Prop := (regions work).Pairwise Disjoint

structure Output (inherited : List Nat) (start finish : Nat) (work : Work) : Prop where
  monotone : start ≤ finish
  separated : WorkSeparated work
  bounded : ∀ ref ∈ allRefs work, ref < finish
  root : ∀ ref ∈ rootRefs work, ref ∈ inherited ∨ start ≤ ref
  hidden : ∀ region ∈ hiddenRegions work, ∀ ref ∈ region, start ≤ ref

def itemRegions (items : List (Result ResponseValue × Work)) : List (List Nat) :=
  items.flatMap (fun item => regions item.2)

structure ItemsOutput (start finish : Nat) (items : List (Result ResponseValue × Work))
    : Prop where
  monotone : start ≤ finish
  separated : (itemRegions items).Pairwise Disjoint
  bounds : ∀ region ∈ itemRegions items, ∀ ref ∈ region, start ≤ ref ∧ ref < finish

theorem Disjoint.symm {left right : List Nat} (h : Disjoint left right)
    : Disjoint right left :=
  fun ref hr hl => h ref hl hr

theorem Disjoint.mono {left right smallLeft smallRight : List Nat}
    (h : Disjoint left right) (hl : smallLeft.Subset left) (hr : smallRight.Subset right)
    : Disjoint smallLeft smallRight :=
  fun ref hleft hright => h ref (hl hleft) (hr hright)

theorem Disjoint.append_left {left middle right : List Nat}
    (hl : Disjoint left right) (hm : Disjoint middle right)
    : Disjoint (left ++ middle) right := by
  intro ref hk
  exact (List.mem_append.mp hk).elim (hl ref) (hm ref)

theorem Disjoint.append_right {left middle right : List Nat}
    (hm : Disjoint left middle) (hr : Disjoint left right)
    : Disjoint left (middle ++ right) :=
  (hm.symm.append_left hr.symm).symm

theorem separated_iff (work : Work)
    : WorkSeparated work
      ↔ (∀ region ∈ hiddenRegions work, Disjoint (rootRefs work) region)
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

theorem rootRefs_subset_allRefs (work : Work) : (rootRefs work).Subset (allRefs work) :=
  List.subset_append_left _ _

theorem hiddenRegion_subset_allRefs (work : Work) {region : List Nat}
    (hr : region ∈ hiddenRegions work)
    : region.Subset (allRefs work) :=
  fun _ hk => List.mem_append_right _ (List.mem_flatten.mpr ⟨region, hr, hk⟩)

theorem region_subset_allRefs (work : Work) {region : List Nat}
    (hr : region ∈ regions work)
    : region.Subset (allRefs work) := by
  rcases List.mem_cons.mp hr with rfl | hr
  · exact rootRefs_subset_allRefs work
  · exact hiddenRegion_subset_allRefs work hr

theorem mem_allRefs_combine (left right : Work) (ref : NodeRef)
    : ref ∈ allRefs (.combine left right) ↔ ref ∈ allRefs left ∨ ref ∈ allRefs right := by
  simp only [allRefs, rootRefs, hiddenRegions, List.flatten_append, List.mem_append]
  simp only [or_assoc, or_left_comm]

theorem Output.root_bounded {inherited : List Nat} {start finish : Nat} {work : Work}
    (h : Output inherited start finish work) {ref : NodeRef} (hk : ref ∈ rootRefs work)
    : ref < finish :=
  h.bounded ref (rootRefs_subset_allRefs work hk)

theorem Output.hidden_bounded {inherited : List Nat} {start finish : Nat} {work : Work}
    (h : Output inherited start finish work) {region : List Nat}
    (hr : region ∈ hiddenRegions work) {ref : NodeRef} (hk : ref ∈ region)
    : ref < finish :=
  h.bounded ref (hiddenRegion_subset_allRefs work hr hk)

theorem Output.empty (inherited : List Nat) {start finish : Nat} (h : start ≤ finish)
    : Output inherited start finish .empty :=
  ⟨
    h,
    by simp [WorkSeparated, regions, rootRefs, hiddenRegions],
    by simp [allRefs, rootRefs, hiddenRegions],
    by simp [rootRefs],
    by simp [hiddenRegions]
  ⟩

theorem Output.widen_finish {inherited : List Nat} {start finish upper : Nat}
    {work : Work} (h : Output inherited start finish work) (hu : finish ≤ upper)
    : Output inherited start upper work :=
  ⟨
    Nat.le_trans h.monotone hu,
    h.separated,
    fun ref hk => Nat.lt_of_lt_of_le (h.bounded ref hk) hu,
    h.root,
    h.hidden
  ⟩

theorem Output.rebase {inherited nextInherited : List Nat} {start nextStart finish : Nat}
    {work : Work} (h : Output nextInherited nextStart finish work)
    (hs : start ≤ nextStart) (hi : ∀ ref ∈ nextInherited, ref ∈ inherited ∨ start ≤ ref)
    : Output inherited start finish work := by
  refine ⟨Nat.le_trans hs h.monotone, h.separated, h.bounded, ?_, ?_⟩
  · intro ref hk
    exact (h.root ref hk).elim (hi ref) (fun href => Or.inr (Nat.le_trans hs href))
  · intro region hr ref hk
    exact Nat.le_trans hs (h.hidden region hr ref hk)

theorem Output.append {inherited : List Nat} {start middle finish : Nat}
    {left right : Work} (hl : Output inherited start middle left)
    (hr : Output inherited middle finish right) (hi : ∀ ref ∈ inherited, ref < start)
    : Output inherited start finish (.combine left right) := by
  refine ⟨Nat.le_trans hl.monotone hr.monotone, ?_, ?_, ?_, ?_⟩
  · simp only [WorkSeparated, regions, rootRefs, hiddenRegions]
    apply separated_merge _ _ _ _ hl.separated hr.separated
    · intro region hm ref hk hregion
      exact Nat.not_lt_of_ge (hr.hidden region hm ref hregion) (hl.root_bounded hk)
    · intro region hm ref hk hregion
      rcases hr.root ref hk with hk | hk
      · exact Nat.not_lt_of_ge (hl.hidden region hm ref hregion) (hi ref hk)
      · exact Nat.not_lt_of_ge hk (hl.hidden_bounded hm hregion)
    · intro leftRegion hlr rightRegion hrr ref hleft hright
      exact Nat.not_lt_of_ge (hr.hidden rightRegion hrr ref hright)
        (hl.hidden_bounded hlr hleft)
  · intro ref hk
    rcases (mem_allRefs_combine left right ref).mp hk with hk | hk
    · exact Nat.lt_of_lt_of_le (hl.bounded ref hk) hr.monotone
    · exact hr.bounded ref hk
  · intro ref hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hl.root ref hk
    · exact (hr.root ref hk).elim Or.inl (fun href => Or.inr (Nat.le_trans hl.monotone href))
  · intro region hm ref hk
    rw [hiddenRegions] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hl.hidden region hm ref hk
    · exact Nat.le_trans hl.monotone (hr.hidden region hm ref hk)

theorem Output.executionGroup {inherited : List Nat} {start finish : Nat}
    {children : Work} (h : Output inherited start finish children)
    (groups : List DeferredFragment) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue)))
    (hg : (groups.flatMap RefRoles.fragmentRefs).Subset inherited)
    (hi : ∀ ref ∈ inherited, ref < start)
    : Output inherited start finish (.executionGroup groups path result children) := by
  refine ⟨h.monotone, ?_, ?_, ?_, ?_⟩
  · have hs := (separated_iff children).mp h.separated
    apply (separated_iff _).mpr
    simp only [rootRefs, hiddenRegions]
    refine ⟨?_, hs.2⟩
    intro region hr
    apply Disjoint.append_left _ (hs.1 region hr)
    intro ref hk hregion
    have := hi ref (hg hk)
    have := h.hidden region hr ref hregion
    omega
  · intro ref hk
    simp only [allRefs, rootRefs, hiddenRegions, List.mem_append, or_assoc] at hk
    rcases hk with hk | hk
    · exact Nat.lt_of_lt_of_le (hi ref (hg hk)) h.monotone
    · exact h.bounded ref (List.mem_append.mpr hk)
  · intro ref hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl (hg hk)
    · exact h.root ref hk
  · simpa only [hiddenRegions] using h.hidden

theorem Output.all_fresh {start finish : Nat} {work : Work}
    (h : Output [] start finish work) (ref : NodeRef) (hk : ref ∈ allRefs work)
    : start ≤ ref ∧ ref < finish := by
  refine ⟨?_, h.bounded ref hk⟩
  rcases List.mem_append.mp hk with hk | hk
  · simpa using h.root ref hk
  · obtain ⟨region, hr, hk⟩ := List.mem_flatten.mp hk
    exact h.hidden region hr ref hk

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
    fun region hr ref hk =>
      ⟨
        Nat.le_trans hl (h.bounds region hr ref hk).1,
        Nat.lt_of_lt_of_le (h.bounds region hr ref hk).2 hu
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
    intro left hl right hr ref hleft hright
    have := head.bounded ref (region_subset_allRefs children hl hleft)
    have := (tail.bounds right hr ref hright).1
    omega
  · intro region hm ref hk
    rcases List.mem_append.mp hm with hm | hm
    · have hh := head.all_fresh ref (region_subset_allRefs children hm hk)
      exact ⟨hh.1, Nat.lt_of_lt_of_le hh.2 tail.monotone⟩
    · have hh := tail.bounds region hm ref hk
      exact ⟨Nat.le_trans head.monotone hh.1, hh.2⟩

theorem Output.stream (inherited : List Nat) (node : DeliveryNode)
    {finish : Nat} {items : List (Result ResponseValue × Work)}
    (h : ItemsOutput (node.ref + 1) finish items)
    : Output inherited node.ref finish (.stream node items) := by
  refine ⟨by have := h.monotone; omega, ?_, ?_, ?_, ?_⟩
  · apply (separated_iff _).mpr
    simp only [rootRefs, hiddenRegions]
    refine ⟨?_, h.separated⟩
    intro region hr ref hk hregion
    obtain rfl := List.mem_singleton.mp hk
    have := (h.bounds region hr node.ref hregion).1
    omega
  · intro ref hk
    simp only [allRefs, rootRefs, hiddenRegions, List.mem_append, List.mem_singleton] at hk
    rcases hk with rfl | hk
    · exact h.monotone
    · obtain ⟨region, hr, hk⟩ := List.mem_flatten.mp hk
      exact (h.bounds region hr ref hk).2
  · intro ref hk
    obtain rfl := List.mem_singleton.mp hk
    exact Or.inr (Nat.le_refl _)
  · intro region hr ref hk
    rw [hiddenRegions] at hr
    have := (h.bounds region hr ref hk).1
    omega

end GraphQL.IncrementalDelivery.Semantics.RefRegions
