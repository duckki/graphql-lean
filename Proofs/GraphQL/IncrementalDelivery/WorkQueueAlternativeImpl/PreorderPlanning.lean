import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IntervalPlanning

/-! A finite immutable parent forest constructs the planner's half-open preorder index.
The forest is an input observer, not another public execution representation. Native
parent discovery, object identity, explicit-stack correspondence and serialization are
still separate from this structural construction.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PreorderPlanning

open GraphQL.IncrementalDelivery.Execution
open IntervalPlanning

-----------------------------------------------------------------------------------------
-- Structural finite forest and the enter/exit ordinal observer
-----------------------------------------------------------------------------------------

inductive Forest where
  | empty
  | node (key : Nat) (children rest : Forest)
deriving Repr

def Forest.keys : Forest → List Nat
  | .empty => []
  | .node key children rest => key :: (children.keys ++ rest.keys)

structure Entry where
  usage : DeferUsage
  interval : Interval
deriving Repr

/-- Enter assigns one ordinal; exit observes the ordinal after every child subtree.
Rest roots start at that exit ordinal. Parent lists are nearest-first, as in Execution.
-/
def Forest.encode (base : Nat) (parents : List Nat) : Forest → List Entry
  | .empty => []
  | .node key children rest =>
      ⟨{ ref := key, ancestors := parents }, ⟨base, base + 1 + children.keys.length⟩⟩
      :: (children.encode (base + 1) (key :: parents)
          ++ rest.encode (base + 1 + children.keys.length) parents)

/-- Keyed lookup observer, not a proposed native list-backed index. Ports retain their
Map and enter/exit counter; subtree sizes here observe the same mathematical exit ordinal.
-/
def makeIndex (entries : List Entry) (key : Nat) : Interval :=
  ((entries.find? (fun entry => entry.usage.ref == key)).map Entry.interval).getD ⟨0, 0⟩

def PreorderIndexConstruction : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → let entries := forest.encode 0 []
      let index := makeIndex entries
      (∀ entry ∈ entries, index entry.usage.ref = entry.interval)
      ∧ ValidIntervals index forest.keys
      ∧ ∀ entry ∈ entries,
        ∀ owner ∈ forest.keys,
          owner ∈ entry.usage.ancestors
          ↔ (index owner).start < (index entry.usage.ref).start
            ∧ (index entry.usage.ref).start < (index owner).stop

/-- Only identity/ancestry correspondence is required; labels and all field details
stay in the original input rather than being rebuilt from this forest observer.
-/
def FieldsFromForest (forest : Forest) (fields : List FieldDetails) : Prop :=
  ∀ usage ∈ fields.filterMap FieldDetails.deferUsage,
    ∃ entry ∈ forest.encode 0 [],
      entry.usage.ref = usage.ref ∧ entry.usage.ancestors = usage.ancestors

def ForestPlanningOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ groups parent,
        (∀ group ∈ groups, FieldsFromForest forest group.2)
        → let observed :=
            IntervalPlanning.buildPlan (makeIndex (forest.encode 0 [])) groups parent
          observed.project = buildExecutionPlan groups parent
          ∧ CanonicalPlanning.KeysMatch observed.partitions
          ∧ (observed.partitions.map CanonicalPlanning.KeyedPartition.key).Nodup

-----------------------------------------------------------------------------------------
-- Constructed entries keep identities, bounds and exact parent-context information
-----------------------------------------------------------------------------------------

theorem Forest.encode_keys (forest : Forest) (base : Nat) (parents : List Nat)
    : (forest.encode base parents).map (fun entry => entry.usage.ref) = forest.keys := by
  induction forest generalizing base parents with
  | empty => rfl
  | node key children rest childIH restIH =>
      simp [Forest.encode, Forest.keys, childIH, restIH]

theorem Forest.encode_length (forest : Forest) (base : Nat) (parents : List Nat)
    : (forest.encode base parents).length = forest.keys.length := by
  rw [← List.length_map (fun entry => entry.usage.ref), forest.encode_keys]

private theorem Forest.encode_bounds (forest : Forest) (base : Nat) (parents : List Nat)
    : ∀ entry ∈ forest.encode base parents,
        base ≤ entry.interval.start
        ∧ entry.interval.start < entry.interval.stop
        ∧ entry.interval.stop ≤ base + forest.keys.length := by
  induction forest generalizing base parents with
  | empty => simp [Forest.encode]
  | node key children rest childIH restIH =>
      intro entry present
      simp only [Forest.encode, List.mem_cons, List.mem_append] at present
      rcases present with rfl | present | present
      · simp only [Forest.keys, List.length_cons, List.length_append]
        omega
      · have bounds := childIH (base + 1) (key :: parents) entry present
        simp only [Forest.keys, List.length_cons, List.length_append]
        omega
      · have bounds := restIH (base + 1 + children.keys.length) parents entry present
        simp only [Forest.keys, List.length_cons, List.length_append]
        omega

private theorem Forest.encode_extends (forest : Forest) (base : Nat) (parents : List Nat)
    : ∀ entry ∈ forest.encode base parents, parents.Subset entry.usage.ancestors := by
  induction forest generalizing base parents with
  | empty => simp [Forest.encode]
  | node key children rest childIH restIH =>
      intro entry present owner inherited
      simp only [Forest.encode, List.mem_cons, List.mem_append] at present
      rcases present with rfl | present | present
      · exact inherited
      · exact childIH _ _ entry present (List.mem_cons_of_mem key inherited)
      · exact restIH _ _ entry present inherited

private theorem Forest.encode_ancestor_source (forest : Forest) (base : Nat)
    (parents : List Nat)
    : ∀ entry ∈ forest.encode base parents,
        entry.usage.ancestors.Subset (parents ++ forest.keys) := by
  induction forest generalizing base parents with
  | empty => simp [Forest.encode]
  | node key children rest childIH restIH =>
      intro entry present owner ancestor
      simp only [Forest.encode, List.mem_cons, List.mem_append] at present
      rcases present with rfl | present | present
      · exact List.mem_append_left _ ancestor
      · have source := childIH _ _ entry present ancestor
        simp only [List.mem_append, List.mem_cons] at source
        simp only [Forest.keys, List.mem_append, List.mem_cons]
        rcases source with (rfl | inherited) | internal
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl inherited
        · exact Or.inr (Or.inr (Or.inl internal))
      · have source := restIH _ _ entry present ancestor
        simp only [List.mem_append] at source
        simp only [Forest.keys, List.mem_append, List.mem_cons]
        rcases source with inherited | internal
        · exact Or.inl inherited
        · exact Or.inr (Or.inr (Or.inr internal))

private theorem Forest.encode_memberKey (forest : Forest) (base : Nat)
    (parents : List Nat) (entry : Entry) (present : entry ∈ forest.encode base parents)
    : entry.usage.ref ∈ forest.keys := by
  rw [← forest.encode_keys base parents]
  exact List.mem_map.mpr ⟨entry, present, rfl⟩

private theorem Forest.encode_absentAncestor (forest : Forest) (base : Nat)
    (parents : List Nat) (owner : Nat) (notParent : owner ∉ parents)
    (notKey : owner ∉ forest.keys) (entry : Entry)
    (present : entry ∈ forest.encode base parents)
    : owner ∉ entry.usage.ancestors := by
  intro ancestor
  rcases List.mem_append.mp (forest.encode_ancestor_source base parents entry present ancestor)
    with inherited | internal
  · exact notParent inherited
  · exact notKey internal

-----------------------------------------------------------------------------------------
-- Preorder starts separate entries; overlapping later entries stay inside the subtree
-----------------------------------------------------------------------------------------

private theorem Forest.encode_separates (forest : Forest) (base : Nat)
    (parents : List Nat)
    : ∀ a ∈ forest.encode base parents,
      ∀ b ∈ forest.encode base parents,
        a.interval.start = b.interval.start → a.usage.ref = b.usage.ref := by
  induction forest generalizing base parents with
  | empty => simp [Forest.encode]
  | node key children rest childIH restIH =>
      intro a ha b hb same
      simp only [Forest.encode, List.mem_cons, List.mem_append] at ha hb
      rcases ha with rfl | ha | ha <;> rcases hb with rfl | hb | hb
      · rfl
      · have bounds := children.encode_bounds _ _ b hb; simp only at same; omega
      · have bounds := rest.encode_bounds _ _ b hb; simp only at same; omega
      · have bounds := children.encode_bounds _ _ a ha; simp only at same; omega
      · exact childIH _ _ a ha b hb same
      · have left := children.encode_bounds _ _ a ha
        have right := rest.encode_bounds _ _ b hb
        omega
      · have bounds := rest.encode_bounds _ _ a ha; simp only at same; omega
      · have left := rest.encode_bounds _ _ a ha
        have right := children.encode_bounds _ _ b hb
        omega
      · exact restIH _ _ a ha b hb same

private theorem Forest.encode_nested (forest : Forest) (base : Nat) (parents : List Nat)
    : ∀ a ∈ forest.encode base parents,
      ∀ b ∈ forest.encode base parents,
        a.interval.start < b.interval.start
        → b.interval.start < a.interval.stop
        → b.interval.stop ≤ a.interval.stop := by
  induction forest generalizing base parents with
  | empty => simp [Forest.encode]
  | node key children rest childIH restIH =>
      intro a ha b hb before inside
      simp only [Forest.encode, List.mem_cons, List.mem_append] at ha hb
      rcases ha with rfl | ha | ha <;> rcases hb with rfl | hb | hb
      · simp only at before; omega
      · exact (children.encode_bounds _ _ b hb).2.2
      · have bounds := rest.encode_bounds _ _ b hb; simp only at inside; omega
      · have bounds := children.encode_bounds _ _ a ha; simp only at before; omega
      · exact childIH _ _ a ha b hb before inside
      · have left := children.encode_bounds _ _ a ha
        have right := rest.encode_bounds _ _ b hb
        omega
      · have bounds := rest.encode_bounds _ _ a ha; simp only at before; omega
      · have left := rest.encode_bounds _ _ a ha
        have right := children.encode_bounds _ _ b hb
        omega
      · exact restIH _ _ a ha b hb before inside

-----------------------------------------------------------------------------------------
-- Forest structure, not an assumed filter result, supplies proper-ancestor intervals
-----------------------------------------------------------------------------------------

private theorem Forest.encode_ancestry (forest : Forest) (base : Nat) (parents : List Nat)
    (unique : forest.keys.Nodup) (external : ∀ key ∈ forest.keys, key ∉ parents)
    : ∀ a ∈ forest.encode base parents,
      ∀ b ∈ forest.encode base parents,
        a.usage.ref ∈ b.usage.ancestors
        ↔ a.interval.start < b.interval.start ∧ b.interval.start < a.interval.stop := by
  induction forest generalizing base parents with
  | empty => simp [Forest.encode]
  | node key children rest childIH restIH =>
      obtain ⟨headAbsent, tailUnique⟩ := List.nodup_cons.mp unique
      obtain ⟨childUnique, restUnique, disjoint⟩ := List.nodup_append.mp tailUnique
      have headNotParent := external key (by simp [Forest.keys])
      have childExternal : ∀ item ∈ children.keys, item ∉ key :: parents := by
        intro item member inherited
        rcases List.mem_cons.mp inherited with rfl | inherited
        · exact headAbsent (List.mem_append_left _ member)
        · exact external item (by simp [Forest.keys, member]) inherited
      have restExternal : ∀ item ∈ rest.keys, item ∉ parents :=
        fun item member => external item (by simp [Forest.keys, member])
      intro a ha b hb
      simp only [Forest.encode, List.mem_cons, List.mem_append] at ha hb
      rcases ha with rfl | ha | ha <;> rcases hb with rfl | hb | hb
      · simp [headNotParent]
      · have inherited := children.encode_extends _ _ b hb (by simp : key ∈ key :: parents)
        have bounds := children.encode_bounds _ _ b hb
        simp only [inherited, true_iff]
        omega
      · have absent := rest.encode_absentAncestor _ _ key headNotParent
          (fun present => headAbsent (List.mem_append_right _ present)) b hb
        have bounds := rest.encode_bounds _ _ b hb
        simp only [absent, false_iff]
        omega
      · have selected := children.encode_memberKey _ _ a ha
        have absent : a.usage.ref ∉ parents :=
          fun present => childExternal _ selected (List.mem_cons_of_mem _ present)
        have bounds := children.encode_bounds _ _ a ha
        simp only [absent, false_iff]
        omega
      · exact childIH _ _ childUnique childExternal a ha b hb
      · have selected := children.encode_memberKey _ _ a ha
        have absent := rest.encode_absentAncestor _ _ a.usage.ref
          (fun present => childExternal _ selected (List.mem_cons_of_mem _ present))
          (fun present => disjoint _ selected _ present rfl) b hb
        have left := children.encode_bounds _ _ a ha
        have right := rest.encode_bounds _ _ b hb
        simp only [absent, false_iff]
        omega
      · have selected := rest.encode_memberKey _ _ a ha
        have absent := restExternal _ selected
        have bounds := rest.encode_bounds _ _ a ha
        simp only [absent, false_iff]
        omega
      · have selected := rest.encode_memberKey _ _ a ha
        have notParent : a.usage.ref ∉ key :: parents := by
          intro member
          rcases List.mem_cons.mp member with same | member
          · exact headAbsent (List.mem_append_right _ (same ▸ selected))
          · exact restExternal _ selected member
        have absent := children.encode_absentAncestor _ _ a.usage.ref notParent
          (fun present => disjoint _ present _ selected rfl) b hb
        have left := rest.encode_bounds _ _ a ha
        have right := children.encode_bounds _ _ b hb
        simp only [absent, false_iff]
        omega
      · exact restIH _ _ restUnique restExternal a ha b hb

-----------------------------------------------------------------------------------------
-- Exact keyed lookup and the joint constructed certificate
-----------------------------------------------------------------------------------------

theorem find_entry (entries : List Entry)
    (unique : (entries.map (fun entry => entry.usage.ref)).Nodup)
    (entry : Entry) (present : entry ∈ entries)
    : entries.find? (fun candidate => candidate.usage.ref == entry.usage.ref)
      = some entry := by
  induction entries with
  | nil => simp at present
  | cons head rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp present with rfl | present
      · simp
      · have different : head.usage.ref ≠ entry.usage.ref := by
          intro same
          exact absent (List.mem_map.mpr ⟨entry, present, same.symm⟩)
        simp [different, ih tailUnique present]

theorem makeIndex_entry (entries : List Entry)
    (unique : (entries.map (fun entry => entry.usage.ref)).Nodup)
    (entry : Entry) (present : entry ∈ entries)
    : makeIndex entries entry.usage.ref = entry.interval := by
  simp [makeIndex, find_entry entries unique entry present]

theorem PreorderIndexConstruction_holds : PreorderIndexConstruction := by
  intro forest unique
  have encodedUnique : ((forest.encode 0 []).map (fun entry => entry.usage.ref)).Nodup := by
    simpa only [Forest.encode_keys] using unique
  have lookup := makeIndex_entry (forest.encode 0 []) encodedUnique
  have source : ∀ key ∈ forest.keys, ∃ entry ∈ forest.encode 0 [], entry.usage.ref = key := by
    intro key present
    rw [← forest.encode_keys 0 []] at present
    exact List.mem_map.mp present
  refine ⟨lookup, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro key present
    obtain ⟨entry, member, rfl⟩ := source key present
    rw [lookup entry member]
    exact (forest.encode_bounds 0 [] entry member).2.1
  · intro a ha b hb same
    obtain ⟨left, leftMember, rfl⟩ := source a ha
    obtain ⟨right, rightMember, rfl⟩ := source b hb
    rw [lookup left leftMember, lookup right rightMember] at same
    exact forest.encode_separates 0 [] left leftMember right rightMember same
  · intro a ha b hb before inside
    obtain ⟨left, leftMember, rfl⟩ := source a ha
    obtain ⟨right, rightMember, rfl⟩ := source b hb
    rw [lookup left leftMember, lookup right rightMember] at *
    exact forest.encode_nested 0 [] left leftMember right rightMember before inside
  · intro entry member owner selected
    obtain ⟨parent, parentMember, rfl⟩ := source owner selected
    rw [lookup entry member, lookup parent parentMember]
    exact forest.encode_ancestry 0 [] unique (by simp) parent parentMember entry member

theorem forest_index_bounds (forest : Forest) (unique : forest.keys.Nodup)
    (key : Nat) (present : key ∈ forest.keys)
    : let span := makeIndex (forest.encode 0 []) key
      span.start < span.stop ∧ span.stop ≤ forest.keys.length := by
  obtain ⟨entry, member, rfl⟩ := by
    simpa only [← forest.encode_keys 0 [], List.mem_map] using present
  rw [(PreorderIndexConstruction_holds forest unique).1 entry member]
  simpa only [Nat.zero_add] using (forest.encode_bounds 0 [] entry member).2

-----------------------------------------------------------------------------------------
-- Same forest supplies each group's ancestry certificate and cross-group separation
-----------------------------------------------------------------------------------------

private theorem FieldsFromForest.keys_subset (forest : Forest)
    (fields : List FieldDetails) (fromForest : FieldsFromForest forest fields)
    : (usageKeys fields).Subset forest.keys := by
  intro key present
  obtain ⟨usage, member, rfl⟩ := by
    simpa only [usageKeys, List.mem_eraseDups, List.mem_map] using present
  obtain ⟨entry, entryMember, equal, _⟩ := fromForest usage member
  rw [← equal]
  exact forest.encode_memberKey 0 [] entry entryMember

theorem FieldsFromForest.indexFor (forest : Forest) (unique : forest.keys.Nodup)
    (fields : List FieldDetails) (fromForest : FieldsFromForest forest fields)
    : IndexFor (makeIndex (forest.encode 0 [])) fields := by
  obtain ⟨_, intervals, ancestry⟩ := PreorderIndexConstruction_holds forest unique
  have subset := fromForest.keys_subset forest fields
  constructor
  · exact ⟨fun key member => intervals.positive key (subset member),
      fun a ha b hb => intervals.separates a (subset ha) b (subset hb),
      fun a ha b hb => intervals.nested a (subset ha) b (subset hb)⟩
  · intro usage member owner selected
    obtain ⟨entry, entryMember, keyEq, ancestorsEq⟩ := fromForest usage member
    rw [← keyEq, ← ancestorsEq]
    exact ancestry entry entryMember owner (subset selected)

theorem ForestPlanningOptimization_holds : ForestPlanningOptimization := by
  intro forest unique groups parent fromForest
  apply IndexedPlanningOptimization_holds
  intro group member
  exact (fromForest group member).indexFor forest unique group.2

/-- Cross-group ordinal separation is now derived from the one constructed forest,
not supplied separately for each tuple-key comparison.
-/
theorem forest_tupleKey_eq_iff (forest : Forest) (unique : forest.keys.Nodup)
    (left right : List FieldDetails)
    (leftFrom : FieldsFromForest forest left) (rightFrom : FieldsFromForest forest right)
    : tupleKey (makeIndex (forest.encode 0 [])) left
        = tupleKey (makeIndex (forest.encode 0 [])) right
      ↔ deferUsageSetsEquivalent (getFilteredDeferUsageSet left)
          (getFilteredDeferUsageSet right)
        = true := by
  apply tupleKey_eq_iff _ _ _ (leftFrom.indexFor forest unique left) (rightFrom.indexFor forest unique right)
  intro a ha b hb
  exact (PreorderIndexConstruction_holds forest unique).2.1.separates
    a (leftFrom.keys_subset forest left ha) b (rightFrom.keys_subset forest right hb)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PreorderPlanning
