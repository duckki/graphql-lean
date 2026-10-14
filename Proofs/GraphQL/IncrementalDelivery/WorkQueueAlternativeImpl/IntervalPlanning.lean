import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CanonicalPlanning

/-! The native planner's sorted interval sweep, with stable collector-order deletion.
The certificate describes a positive, separating, nested half-open index and its relation
to the same input's ancestry. It does not assume filtering or plan equality. Construction
by the native parent-forest traversal and string-key serialization remain separate.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.IntervalPlanning

open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Independent index certificate and one-pass selected-usage sweep
-----------------------------------------------------------------------------------------

structure Interval where
  start : Nat
  stop : Nat
deriving Repr, DecidableEq

abbrev Index := Nat → Interval

def usageKeys (fields : List FieldDetails) : List Nat :=
  ((fields.filterMap FieldDetails.deferUsage).map DeferUsage.ref).eraseDups

/-- These are index properties, not the desired output equality. The certificate is
local to selected identities; a runtime builds one immutable index for the whole plan.
-/
structure ValidIntervals (index : Index) (keys : List Nat) : Prop where
  positive : ∀ key ∈ keys, (index key).start < (index key).stop
  separates : ∀ a ∈ keys, ∀ b ∈ keys, (index a).start = (index b).start → a = b
  nested
    : ∀ a ∈ keys,
      ∀ b ∈ keys,
        (index a).start < (index b).start
        → (index b).start < (index a).stop
        → (index b).stop ≤ (index a).stop

structure IndexFor (index : Index) (fields : List FieldDetails) : Prop where
  intervals : ValidIntervals index (usageKeys fields)
  ancestry
    : ∀ usage ∈ fields.filterMap FieldDetails.deferUsage,
      ∀ owner ∈ usageKeys fields,
        owner ∈ usage.ancestors
        ↔ (index owner).start < (index usage.ref).start
          ∧ (index usage.ref).start < (index owner).stop

def orderedKeys (index : Index) (keys : List Nat) : List Nat :=
  keys.mergeSort (fun a b => decide ((index a).start ≤ (index b).start))

/-- Nat barrier=0 represents the native initial -1: preorder starts are nonnegative.
Skipped intervals never extend the barrier in the actual algorithm.
-/
def sweep (index : Index) (barrier : Nat) : List Nat → List Nat
  | [] => []
  | key :: rest =>
      if (index key).start < barrier then
        sweep index barrier rest
      else
        key :: sweep index (index key).stop rest

/-- Sorting is used only for membership decisions. Deleting from the original ordered
set, not returning the sweep order, retains the first partition's owner representative.
-/
def filteredUsages (index : Index) (fields : List FieldDetails) : List Nat :=
  if fields.any (fun field => field.deferUsage.isNone) then
    []
  else
    let keys := usageKeys fields
    let retained := sweep index 0 (orderedKeys index keys)
    keys.filter retained.contains

def IndexedFilterOptimization : Prop :=
  ∀ index fields,
    IndexFor index fields → filteredUsages index fields = getFilteredDeferUsageSet fields

/-- Numeric observer of the native members.join(',') input, not its string encoding. -/
def tupleKey (index : Index) (fields : List FieldDetails) : List Nat :=
  if fields.any (fun field => field.deferUsage.isNone) then
    []
  else
    (sweep index 0 (orderedKeys index (usageKeys fields))).map
      (fun key => (index key).start)

def TupleKeyOptimization : Prop :=
  ∀ index fields,
    IndexFor index fields
    → tupleKey index fields
      = CanonicalPlanning.partitionKey
          ((getFilteredDeferUsageSet fields).map (fun key => (index key).start))

def step (index : Index) (parent : List Nat) (plan : CanonicalPlanning.KeyedPlan)
    (group : Name × List FieldDetails)
    : CanonicalPlanning.KeyedPlan :=
  let usages := filteredUsages index group.2
  if deferUsageSetsEquivalent usages parent then
    { plan with immediate := plan.immediate ++ [group] }
  else
    {
      plan with
        partitions := CanonicalPlanning.addPartition usages group plan.partitions
    }

def buildPlan (index : Index) (groups : CollectedFieldsMap) (parent : List Nat := [])
    : CanonicalPlanning.KeyedPlan :=
  groups.foldl (step index parent) {}

/-- Checked reduction from one same-plan interval/ancestry certificate. Native index
construction remains an open leaf, rather than an assumed public execution law.
-/
def IndexedPlanningOptimization : Prop :=
  ∀ index groups parent,
    (∀ group ∈ groups, IndexFor index group.2)
    → let observed := buildPlan index groups parent
      observed.project = buildExecutionPlan groups parent
      ∧ CanonicalPlanning.KeysMatch observed.partitions
      ∧ (observed.partitions.map CanonicalPlanning.KeyedPartition.key).Nodup

-----------------------------------------------------------------------------------------
-- A skipped descendant cannot extend the last retained subtree's barrier
-----------------------------------------------------------------------------------------

private theorem sweep_mem (index : Index) (barrier : Nat) (keys : List Nat)
    (ordered : keys.Pairwise (fun a b => (index a).start < (index b).start))
    (positive : ∀ key ∈ keys, (index key).start < (index key).stop)
    (nested
      : ∀ a ∈ keys,
        ∀ b ∈ keys,
          (index a).start < (index b).start
          → (index b).start < (index a).stop
          → (index b).stop ≤ (index a).stop)
    (bounded : ∀ key ∈ keys, (index key).start < barrier → (index key).stop ≤ barrier)
    (key : Nat)
    : key ∈ sweep index barrier keys
      ↔ key ∈ keys
        ∧ barrier ≤ (index key).start
        ∧ ∀ owner ∈ keys,
            ¬ ((index owner).start < (index key).start
                ∧ (index key).start < (index owner).stop) := by
  induction keys generalizing barrier with
  | nil => simp [sweep]
  | cons head rest ih =>
      obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
      have restPositive : ∀ item ∈ rest, (index item).start < (index item).stop :=
        fun item member => positive item (List.mem_cons_of_mem _ member)
      have restNested : ∀ a ∈ rest, ∀ b ∈ rest,
          (index a).start < (index b).start → (index b).start < (index a).stop
            → (index b).stop ≤ (index a).stop :=
        fun a ha b hb => nested a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
      by_cases skipped : (index head).start < barrier
      · have headBound := bounded head (by simp) skipped
        have next := ih barrier tail restPositive restNested
          (fun item member => bounded item (List.mem_cons_of_mem _ member))
        simp only [sweep, skipped, ↓reduceIte, next, List.mem_cons]
        constructor
        · rintro ⟨member, uncovered, remaining⟩
          refine ⟨Or.inr member, uncovered, ?_⟩
          intro owner present
          rcases present with rfl | present
          · omega
          · exact remaining owner present
        · rintro ⟨member, uncovered, remaining⟩
          refine ⟨?_, uncovered, fun owner present => remaining owner (Or.inr present)⟩
          rcases member with rfl | member
          · omega
          · exact member
      · have newBound : ∀ item ∈ rest,
            (index item).start < (index head).stop → (index item).stop ≤ (index head).stop :=
          fun item member => nested head (by simp) item (by simp [member]) (before item member)
        have next := ih (index head).stop tail restPositive restNested newBound
        have headPositive := positive head (by simp)
        simp only [sweep, skipped, ↓reduceIte, List.mem_cons, next]
        constructor
        · rintro (rfl | ⟨member, uncovered, remaining⟩)
          · refine ⟨Or.inl rfl, by omega, ?_⟩
            intro owner present
            rcases present with rfl | present
            · omega
            · have after := before owner present; omega
          · refine ⟨Or.inr member, by omega, ?_⟩
            intro owner present
            rcases present with rfl | present
            · omega
            · exact remaining owner present
        · rintro ⟨rfl | member, uncovered, remaining⟩
          · exact Or.inl rfl
          · refine Or.inr ⟨member, ?_, fun owner present => remaining owner (Or.inr present)⟩
            have after := before key member
            have outside := remaining head (Or.inl rfl)
            omega

-----------------------------------------------------------------------------------------
-- Sorting derives strict preorder order from identity separation
-----------------------------------------------------------------------------------------

private theorem strictOrder (index : Index) (keys : List Nat)
    (ordered : keys.Pairwise (fun a b => (index a).start ≤ (index b).start))
    (unique : keys.Nodup)
    (separates : ∀ a ∈ keys, ∀ b ∈ keys, (index a).start = (index b).start → a = b)
    : keys.Pairwise (fun a b => (index a).start < (index b).start) := by
  induction keys with
  | nil => simp
  | cons head rest ih =>
      obtain ⟨before, tail⟩ := List.pairwise_cons.mp ordered
      obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
      rw [List.pairwise_cons]
      refine ⟨?_, ih tail restUnique (fun a ha b hb =>
        separates a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
      intro item member
      have le := before item member
      have ne : (index head).start ≠ (index item).start := by
        intro same
        exact absent (separates head (by simp) item (by simp [member]) same ▸ member)
      omega

private theorem orderedKeys_strict (index : Index) (keys : List Nat) (unique : keys.Nodup)
    (separates : ∀ a ∈ keys, ∀ b ∈ keys, (index a).start = (index b).start → a = b)
    : (orderedKeys index keys).Pairwise
        (fun a b => (index a).start < (index b).start) := by
  have sorted := List.pairwise_mergeSort (le := fun a b => decide ((index a).start ≤ (index b).start))
    (by intro a b c ab bc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) keys
  apply strictOrder index _ (by simpa only [orderedKeys, decide_eq_true_eq] using sorted)
    ((List.mergeSort_perm _ _).symm.nodup unique)
  simpa only [orderedKeys, List.mem_mergeSort] using separates

private theorem usageKeys_nodup (fields : List FieldDetails)
    : (usageKeys fields).Nodup := by
  have unique := CanonicalPlanning.partitionKey_nodup
    ((fields.filterMap FieldDetails.deferUsage).map DeferUsage.ref)
  exact (List.mergeSort_perm _ _).nodup unique

private theorem sweep_sublist (index : Index) (barrier : Nat) (keys : List Nat)
    : List.Sublist (sweep index barrier keys) keys := by
  induction keys generalizing barrier with
  | nil => exact List.Sublist.refl []
  | cons key rest ih =>
      simp only [sweep]
      split
      · exact (ih barrier).cons key
      · exact (ih (index key).stop).cons_cons key

private theorem filtered_sweep_members (index : Index) (fields : List FieldDetails)
    (deferred : fields.any (fun field => field.deferUsage.isNone) ≠ true) (key : Nat)
    : key ∈ filteredUsages index fields
      ↔ key ∈ sweep index 0 (orderedKeys index (usageKeys fields)) := by
  simp only [filteredUsages, deferred, Bool.false_eq_true, ↓reduceIte,
    List.mem_filter, List.contains_iff_mem]
  constructor
  · exact And.right
  · intro present
    have selected := (sweep_sublist index 0 _).subset present
    exact ⟨by simpa only [orderedKeys, List.mem_mergeSort] using selected, present⟩

private theorem filtered_memKeys (index : Index) (fields : List FieldDetails) (key : Nat)
    (present : key ∈ filteredUsages index fields)
    : key ∈ usageKeys fields := by
  unfold filteredUsages at present
  split at present
  · simp at present
  · exact (List.mem_filter.mp present).1

-----------------------------------------------------------------------------------------
-- Same-input ancestry decides exactly the stable original-order deletion
-----------------------------------------------------------------------------------------

theorem IndexedFilterOptimization_holds : IndexedFilterOptimization := by
  intro index fields certificate
  unfold filteredUsages getFilteredDeferUsageSet
  split
  · rfl
  · apply List.filter_congr
    intro key present
    have ordered := orderedKeys_strict index (usageKeys fields) (usageKeys_nodup fields)
      certificate.intervals.separates
    have observed := sweep_mem index 0 (orderedKeys index (usageKeys fields)) ordered
      (by simpa only [orderedKeys, List.mem_mergeSort] using certificate.intervals.positive)
      (by simpa only [orderedKeys, List.mem_mergeSort] using certificate.intervals.nested)
      (by intro item member impossible; omega) key
    have keySource : ∃ usage ∈ fields.filterMap FieldDetails.deferUsage, usage.ref = key := by
      simpa only [usageKeys, List.mem_eraseDups, List.mem_map] using present
    apply Bool.eq_iff_iff.mpr
    change (sweep index 0 (orderedKeys index (usageKeys fields))).contains key = true ↔
      (!((fields.filterMap FieldDetails.deferUsage).any (fun usage => usage.ref == key
        && usage.ancestors.any (usageKeys fields).contains))) = true
    rw [List.contains_iff_mem, observed]
    simp only [orderedKeys, List.mem_mergeSort, Nat.zero_le, true_and, Bool.not_eq_true',
      Bool.eq_false_iff]
    constructor
    · rintro ⟨_, noAncestor⟩ dominated
      obtain ⟨usage, member, dominated⟩ := List.any_eq_true.mp dominated
      simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
        List.contains_iff_mem] at dominated
      obtain ⟨equal, ancestor, ancestorMember, selected⟩ := dominated
      have overlaps := (certificate.ancestry usage member ancestor selected).1 ancestorMember
      exact noAncestor ancestor selected (equal ▸ overlaps)
    · intro noAncestor
      refine ⟨present, ?_⟩
      intro owner selected overlaps
      obtain ⟨usage, member, equal⟩ := keySource
      have ancestor := (certificate.ancestry usage member owner selected).2 (equal ▸ overlaps)
      apply noAncestor
      apply List.any_eq_true.mpr
      refine ⟨usage, member, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem]
      exact ⟨equal, owner, ancestor, selected⟩

theorem TupleKeyOptimization_holds : TupleKeyOptimization := by
  intro index fields certificate
  by_cases immediate : fields.any (fun field => field.deferUsage.isNone) = true
  · simp [tupleKey, getFilteredDeferUsageSet, immediate, CanonicalPlanning.partitionKey]
  · have ordered := orderedKeys_strict index (usageKeys fields) (usageKeys_nodup fields)
      certificate.intervals.separates
    have sorted : ((sweep index 0 (orderedKeys index (usageKeys fields))).map
        (fun key => (index key).start)).Pairwise (fun a b => a < b) :=
      List.pairwise_map.mpr (ordered.sublist (sweep_sublist index 0 _))
    have same : CanonicalPlanning.partitionKey
        ((filteredUsages index fields).map (fun key => (index key).start))
        = CanonicalPlanning.partitionKey
          ((sweep index 0 (orderedKeys index (usageKeys fields))).map
            (fun key => (index key).start)) := by
      apply (CanonicalPlanning.partitionKey_eq_iff _ _).2
      intro ordinal
      simp only [List.mem_map, filtered_sweep_members index fields immediate]
    have normalized := CanonicalPlanning.partitionKey_eq_self _
      (sorted.imp (fun less => Nat.ne_of_lt less)) (sorted.imp (fun less => Nat.le_of_lt less))
    rw [← IndexedFilterOptimization_holds index fields certificate, same, normalized]
    simp only [tupleKey, immediate, Bool.false_eq_true, ↓reduceIte]

/-- Local index validity alone cannot justify comparisons between two field sets.
The native same-plan index must also separate identities across that comparison.
-/
theorem tupleKey_eq_iff (index : Index) (left right : List FieldDetails)
    (leftIndex : IndexFor index left) (rightIndex : IndexFor index right)
    (separates
      : ∀ a ∈ usageKeys left,
        ∀ b ∈ usageKeys right, (index a).start = (index b).start → a = b)
    : tupleKey index left = tupleKey index right
      ↔ deferUsageSetsEquivalent (getFilteredDeferUsageSet left)
          (getFilteredDeferUsageSet right)
        = true := by
  rw [TupleKeyOptimization_holds index left leftIndex,
    TupleKeyOptimization_holds index right rightIndex]
  apply CanonicalPlanning.partitionKey_recode_iff
  intro a ha b hb same
  apply separates a (filtered_memKeys index left a ?_) b (filtered_memKeys index right b ?_) same
  · simpa only [IndexedFilterOptimization_holds index left leftIndex] using ha
  · simpa only [IndexedFilterOptimization_holds index right rightIndex] using hb

-----------------------------------------------------------------------------------------
-- One same-run plan with both indexed filtering and canonical partition lookup
-----------------------------------------------------------------------------------------

private theorem fold_eq (index : Index) (groups : CollectedFieldsMap) (parent : List Nat)
    (plan : CanonicalPlanning.KeyedPlan)
    (certified : ∀ group ∈ groups, IndexFor index group.2)
    : groups.foldl (step index parent) plan
      = groups.foldl (CanonicalPlanning.KeyedPlan.step parent) plan := by
  induction groups generalizing plan with
  | nil => rfl
  | cons group rest ih =>
      have head := IndexedFilterOptimization_holds index group.2 (certified group (by simp))
      rw [List.foldl_cons, List.foldl_cons,
        ih _ (fun item member => certified item (List.mem_cons_of_mem _ member))]
      simp only [step, CanonicalPlanning.KeyedPlan.step, head]

theorem IndexedPlanningOptimization_holds : IndexedPlanningOptimization := by
  intro index groups parent certified
  have same : buildPlan index groups parent = CanonicalPlanning.buildPlan groups parent :=
    fold_eq index groups parent {} certified
  rw [same]
  exact CanonicalPlanning.CanonicalPartitionOptimization_holds groups parent

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.IntervalPlanning
