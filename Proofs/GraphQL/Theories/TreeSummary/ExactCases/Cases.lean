import GraphQL.Theories.TreeSummary.ExactCases

/-! Exactness of symbolic runtime-type regions. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

private def RegionsExact (scope : PossibleTypes)
    (conditions : List PossibleTypes) (regions : List PossibleTypeRegion)
    : Prop :=
  (∀ region,
    region ∈ regions -> region ≠ [] ∧ ∀ typeName, typeName ∈ region -> typeName ∈ scope)
  ∧ (∀ typeName,
      typeName ∈ scope
      -> ∃ region,
          (region ∈ regions ∧ typeName ∈ region)
          ∧ ∀ candidate, candidate ∈ regions ∧ typeName ∈ candidate -> candidate = region)
  ∧ (∀ region,
      region ∈ regions
      -> ∀ left,
          left ∈ region
          -> ∀ right,
              right ∈ region
              -> ∀ allowed,
                  allowed ∈ conditions -> allowed.contains left = allowed.contains right)

private def splitRegionFor (region allowed : PossibleTypeRegion) (typeName : Name)
    : PossibleTypeRegion :=
  if allowed.contains typeName then
    region.filter allowed.contains
  else
    region.filter fun candidate => !allowed.contains candidate

private theorem mem_splitRegionFor (region allowed : PossibleTypeRegion)
    {typeName : Name} (hmem : typeName ∈ region)
    : typeName ∈ splitRegionFor region allowed typeName := by
  unfold splitRegionFor
  by_cases hallowed : typeName ∈ allowed
  · have hcontains : allowed.contains typeName = true :=
      List.contains_iff_mem.mpr hallowed
    rw [hcontains]
    exact List.mem_filter.mpr ⟨hmem, hcontains⟩
  · have hcontains : allowed.contains typeName = false := by
      exact Bool.eq_false_iff.mpr fun htrue =>
        hallowed (List.contains_iff_mem.mp htrue)
    rw [hcontains]
    exact List.mem_filter.mpr ⟨hmem, by rw [hcontains]; rfl⟩

private theorem splitRegionFor_mem_splitPossibleTypeRegion
    (region allowed : PossibleTypeRegion) {typeName : Name}
    (hmem : typeName ∈ region)
    : splitRegionFor region allowed typeName
      ∈ splitPossibleTypeRegion region allowed := by
  by_cases hallowed : typeName ∈ allowed
  · have hcontains : allowed.contains typeName = true :=
      List.contains_iff_mem.mpr hallowed
    have hincluded : (region.filter allowed.contains).isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr <|
        List.ne_nil_of_mem (List.mem_filter.mpr ⟨hmem, hcontains⟩)
    unfold splitRegionFor
    rw [hcontains]
    unfold splitPossibleTypeRegion
    dsimp only
    rw [hincluded]
    simp
  · have hcontains : allowed.contains typeName = false := by
      exact Bool.eq_false_iff.mpr fun htrue =>
        hallowed (List.contains_iff_mem.mp htrue)
    have hexcluded :
        (region.filter fun candidate => !allowed.contains candidate).isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr <|
        List.ne_nil_of_mem
          (List.mem_filter.mpr ⟨hmem, by rw [hcontains]; rfl⟩)
    unfold splitRegionFor
    rw [hcontains]
    unfold splitPossibleTypeRegion
    dsimp only
    rw [hexcluded]
    exact List.mem_append_right _ (by simp)

private theorem mem_of_mem_splitPossibleTypeRegion
    (region allowed candidate : PossibleTypeRegion)
    (hcandidate : candidate ∈ splitPossibleTypeRegion region allowed)
    {typeName : Name} (hmem : typeName ∈ candidate)
    : typeName ∈ region := by
  simp only [splitPossibleTypeRegion] at hcandidate
  cases hincluded : (region.filter allowed.contains).isEmpty with
  | false =>
      cases hexcluded
            : (region.filter fun candidate => !allowed.contains candidate).isEmpty with
      | false =>
          simp only [hincluded, hexcluded, Bool.false_eq_true, if_false,
            List.mem_append, List.mem_singleton] at hcandidate
          rcases hcandidate with rfl | rfl <;>
            exact (List.mem_filter.mp hmem).1
      | true =>
          simp only [hincluded, hexcluded, Bool.false_eq_true, if_false, if_true,
            List.append_nil, List.mem_singleton] at hcandidate
          subst candidate
          exact (List.mem_filter.mp hmem).1
  | true =>
      cases hexcluded
            : (region.filter fun candidate => !allowed.contains candidate).isEmpty with
      | false =>
          simp only [hincluded, hexcluded, if_true, Bool.false_eq_true, if_false,
            List.nil_append, List.mem_singleton] at hcandidate
          subst candidate
          exact (List.mem_filter.mp hmem).1
      | true =>
          simp only [hincluded, hexcluded, if_true, List.append_nil] at hcandidate
          contradiction

private theorem eq_splitRegionFor_of_mem_splitPossibleTypeRegion
    (region allowed candidate : PossibleTypeRegion)
    (hcandidate : candidate ∈ splitPossibleTypeRegion region allowed)
    {typeName : Name} (hmem : typeName ∈ candidate)
    : candidate = splitRegionFor region allowed typeName := by
  simp only [splitPossibleTypeRegion] at hcandidate
  cases hincluded : (region.filter allowed.contains).isEmpty with
  | false =>
      cases hexcluded
            : (region.filter fun candidate => !allowed.contains candidate).isEmpty with
      | false =>
          simp only [hincluded, hexcluded, Bool.false_eq_true, if_false,
            List.mem_append, List.mem_singleton] at hcandidate
          rcases hcandidate with rfl | rfl
          · have hcontains := (List.mem_filter.mp hmem).2
            unfold splitRegionFor
            rw [hcontains]
            simp
          · have hnot := (List.mem_filter.mp hmem).2
            have hcontains : allowed.contains typeName = false := by
              cases hvalue : allowed.contains typeName <;> simp_all
            unfold splitRegionFor
            rw [hcontains]
            simp
      | true =>
          simp only [hincluded, hexcluded, Bool.false_eq_true, if_false, if_true,
            List.append_nil, List.mem_singleton] at hcandidate
          subst candidate
          have hcontains := (List.mem_filter.mp hmem).2
          unfold splitRegionFor
          rw [hcontains]
          simp
  | true =>
      cases hexcluded
            : (region.filter fun candidate => !allowed.contains candidate).isEmpty with
      | false =>
          simp only [hincluded, hexcluded, if_true, Bool.false_eq_true, if_false,
            List.nil_append, List.mem_singleton] at hcandidate
          subst candidate
          have hnot := (List.mem_filter.mp hmem).2
          have hcontains : allowed.contains typeName = false := by
            cases hvalue : allowed.contains typeName <;> simp_all
          unfold splitRegionFor
          rw [hcontains]
          simp
      | true =>
          simp only [hincluded, hexcluded, if_true, List.append_nil] at hcandidate
          contradiction

private theorem splitPossibleTypeRegion_nonempty
    (region allowed candidate : PossibleTypeRegion)
    (hcandidate : candidate ∈ splitPossibleTypeRegion region allowed)
    : candidate ≠ [] := by
  simp only [splitPossibleTypeRegion] at hcandidate
  cases hincluded : (region.filter allowed.contains).isEmpty with
  | false =>
      cases hexcluded
            : (region.filter fun candidate => !allowed.contains candidate).isEmpty with
      | false =>
          simp only [hincluded, hexcluded, Bool.false_eq_true, if_false,
            List.mem_append, List.mem_singleton] at hcandidate
          rcases hcandidate with rfl | rfl
          · exact List.isEmpty_eq_false_iff.mp hincluded
          · exact List.isEmpty_eq_false_iff.mp hexcluded
      | true =>
          simp only [hincluded, hexcluded, Bool.false_eq_true, if_false, if_true,
            List.append_nil, List.mem_singleton] at hcandidate
          subst candidate
          exact List.isEmpty_eq_false_iff.mp hincluded
  | true =>
      cases hexcluded
            : (region.filter fun candidate => !allowed.contains candidate).isEmpty with
      | false =>
          simp only [hincluded, hexcluded, if_true, Bool.false_eq_true, if_false,
            List.nil_append, List.mem_singleton] at hcandidate
          subst candidate
          exact List.isEmpty_eq_false_iff.mp hexcluded
      | true =>
          simp only [hincluded, hexcluded, if_true, List.append_nil] at hcandidate
          contradiction

private theorem splitPossibleTypeRegion_condition_constant
    (region allowed candidate : PossibleTypeRegion)
    (hcandidate : candidate ∈ splitPossibleTypeRegion region allowed)
    {left right : Name} (hleft : left ∈ candidate) (hright : right ∈ candidate)
    : allowed.contains left = allowed.contains right := by
  have heq := eq_splitRegionFor_of_mem_splitPossibleTypeRegion region allowed candidate
    hcandidate hleft
  subst candidate
  unfold splitRegionFor at hright
  cases hallowed : allowed.contains left <;> simp_all

private theorem refinePossibleTypeRegions_exact
    (scope : PossibleTypes) (conditions : List PossibleTypes)
    (regions : List PossibleTypeRegion) (allowed : PossibleTypes)
    (hexact : RegionsExact scope conditions regions)
    : RegionsExact scope (conditions ++ [allowed])
        (refinePossibleTypeRegions allowed regions) := by
  rcases hexact with ⟨hregions, hcover, huniform⟩
  constructor
  · intro candidate hcandidate
    rw [refinePossibleTypeRegions] at hcandidate
    rcases List.mem_flatMap.mp hcandidate with
      ⟨region, hregion, hcandidate⟩
    refine ⟨splitPossibleTypeRegion_nonempty region allowed candidate hcandidate, ?_⟩
    intro typeName hmem
    exact (hregions region hregion).2 typeName
      (mem_of_mem_splitPossibleTypeRegion region allowed candidate hcandidate hmem)
  constructor
  · intro typeName hscope
    obtain ⟨region, ⟨hregion, hmem⟩, hunique⟩ := hcover typeName hscope
    let candidate := splitRegionFor region allowed typeName
    refine ⟨candidate, ?_, ?_⟩
    · constructor
      · rw [refinePossibleTypeRegions]
        exact List.mem_flatMap.mpr
          ⟨region, hregion,
            splitRegionFor_mem_splitPossibleTypeRegion region allowed hmem⟩
      · exact mem_splitRegionFor region allowed hmem
    · intro other hother
      rcases hother with ⟨hotherRegion, hotherMem⟩
      rw [refinePossibleTypeRegions] at hotherRegion
      rcases List.mem_flatMap.mp hotherRegion with
        ⟨parent, hparent, hotherSplit⟩
      have hparentMem := mem_of_mem_splitPossibleTypeRegion parent allowed other
        hotherSplit hotherMem
      have hparentEq := hunique parent ⟨hparent, hparentMem⟩
      subst parent
      exact eq_splitRegionFor_of_mem_splitPossibleTypeRegion region allowed other
        hotherSplit hotherMem
  · intro candidate hcandidate left hleft right hright condition hcondition
    rw [refinePossibleTypeRegions] at hcandidate
    rcases List.mem_flatMap.mp hcandidate with
      ⟨region, hregion, hcandidate⟩
    rw [List.mem_append] at hcondition
    rcases hcondition with hprevious | hnew
    · exact huniform region hregion left
        (mem_of_mem_splitPossibleTypeRegion region allowed candidate hcandidate hleft)
        right
        (mem_of_mem_splitPossibleTypeRegion region allowed candidate hcandidate hright)
        condition hprevious
    · simp only [List.mem_singleton] at hnew
      subst condition
      exact splitPossibleTypeRegion_condition_constant region allowed candidate
        hcandidate hleft hright

private theorem possibleTypeRegions_fold_exact
    (scope : PossibleTypes) (processed conditions : List PossibleTypes)
    (regions : List PossibleTypeRegion)
    (hexact : RegionsExact scope processed regions)
    : RegionsExact scope (processed ++ conditions)
        (conditions.foldl
          (fun current allowed => refinePossibleTypeRegions allowed current)
          regions) := by
  induction conditions generalizing processed regions with
  | nil => simpa using hexact
  | cons allowed rest ih =>
      rw [List.foldl_cons]
      have hrefined :=
        refinePossibleTypeRegions_exact scope processed regions allowed hexact
      have hrest := ih (processed ++ [allowed])
        (refinePossibleTypeRegions allowed regions) hrefined
      simpa [List.append_assoc] using hrest

theorem possibleTypeRegions_exact (scope : PossibleTypes)
    (conditions : List PossibleTypes)
    : PossibleTypeRegionsExact scope conditions := by
  unfold PossibleTypeRegionsExact
  change RegionsExact scope conditions (possibleTypeRegions scope conditions)
  unfold possibleTypeRegions
  have hinitial : RegionsExact scope [] (if scope.isEmpty then [] else [scope]) := by
    by_cases hempty : scope = []
    · subst scope
      simp [RegionsExact]
    · have hscope : scope.isEmpty = false :=
        List.isEmpty_eq_false_iff.mpr hempty
      constructor
      · simp [hscope, hempty]
      constructor
      · intro typeName hmem
        refine ⟨scope, by simp [hscope, hmem], ?_⟩
        intro candidate hcandidate
        simpa [hscope] using hcandidate.1
      · simp [hscope]
  exact possibleTypeRegions_fold_exact scope [] conditions
    (if scope.isEmpty then [] else [scope]) hinitial

-- Every exact-case-tree step receives the exact type partition induced by the current
-- branches of all simultaneously active syntactic trees. This is the case-level witness
-- used by the execution-equivalence proof.
theorem CaseForest.typeRegions_exact (tree : CaseForest) (scope : PossibleTypes)
    : PossibleTypeRegionsExact scope tree.typeBranchPossibleTypes := by
  exact possibleTypeRegions_exact scope tree.typeBranchPossibleTypes

end ExactCases
end TreeSummary
end GraphQL
