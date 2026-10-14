import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerFieldMaps

/-! Finite immutable parent discovery. Each fresh node is inserted before reading its
parent; known nodes stop the walk. Fuel is a termination observer, not a native budget.
Map/reference correspondence and assembling these nodes into ordered children remain
separate from the exact discovered identity domain proved here.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ParentDiscovery

open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Parent lookup, fresh-node walk and insertion-order observations
-----------------------------------------------------------------------------------------

abbrev Parents := Nat → Option Nat

def Decreasing (parent : Parents) (height : Nat → Nat) : Prop :=
  ∀ key ancestor, parent key = some ancestor → height ancestor < height key

def ParentClosed (parent : Parents) (keys : List Nat) : Prop :=
  ∀ key ∈ keys, ∀ ancestor, parent key = some ancestor → ancestor ∈ keys

inductive Reachable (parent : Parents) (seeds : List Nat) : Nat → Prop where
  | seed (key : Nat) (present : key ∈ seeds) : Reachable parent seeds key
  | ancestor (key ancestor : Nat) (child : Reachable parent seeds key)
    (edge : parent key = some ancestor)
    : Reachable parent seeds ancestor

structure Result where
  nodes : List Nat
  finished : Bool := true
  parentReads : Nat := 0
  probes : Nat := 0
deriving Repr

/-- Known nodes do not read another parent. Fresh nodes append before following the
immutable parent edge; this is the native Map's insertion observation, not a List port.
-/
def walk (parent : Parents) : Nat → Option Nat → List Nat → Result
  | _, none, seen => ⟨seen, true, 0, 0⟩
  | 0, some _, seen => ⟨seen, false, 0, 0⟩
  | fuel + 1, some key, seen =>
      if seen.contains key then
        ⟨seen, true, 0, 1⟩
      else
        let tail := walk parent fuel (parent key) (seen ++ [key])
        { tail with parentReads := tail.parentReads + 1, probes := tail.probes + 1 }

def discoverFrom (parent : Parents) (height : Nat → Nat) : List Nat → List Nat → Result
  | [], seen => ⟨seen, true, 0, 0⟩
  | key :: rest, seen =>
      let head := walk parent (height key + 1) (some key) seen
      let tail := discoverFrom parent height rest head.nodes
      {
        tail with
          finished := head.finished && tail.finished
          parentReads := head.parentReads + tail.parentReads
          probes := head.probes + tail.probes
      }

def discover (parent : Parents) (height : Nat → Nat) (seeds : List Nat) : Result :=
  discoverFrom parent height seeds []

def ParentDiscoveryOptimization : Prop :=
  ∀ parent height,
    Decreasing parent height
    → ∀ seeds,
        let observed := discover parent height seeds
        observed.finished = true
        ∧ observed.nodes.Nodup
        ∧ ParentClosed parent observed.nodes
        ∧ (∀ key, key ∈ observed.nodes ↔ Reachable parent seeds key)
        ∧ observed.parentReads = observed.nodes.length
        ∧ observed.probes ≤ observed.nodes.length + seeds.length

-----------------------------------------------------------------------------------------
-- Even a partial walk inserts each fresh node once and preserves prior insertion order
-----------------------------------------------------------------------------------------

private theorem walk_counts (parent : Parents) (fuel : Nat) (current : Option Nat)
    (seen : List Nat) (unique : seen.Nodup)
    : let observed := walk parent fuel current seen
      seen.Sublist observed.nodes
      ∧ observed.nodes.Nodup
      ∧ observed.parentReads + seen.length = observed.nodes.length
      ∧ observed.probes ≤ observed.parentReads + 1 := by
  induction fuel generalizing current seen with
  | zero => cases current <;> simp [walk, unique]
  | succ fuel ih =>
      cases current with
      | none => simp [walk, unique]
      | some key =>
          by_cases known : key ∈ seen
          · simp [walk, known, unique]
          · have freshUnique : (seen ++ [key]).Nodup := by
              apply List.nodup_append.mpr
              refine ⟨unique, by simp, ?_⟩
              intro a ha b hb equal
              have bEq := List.mem_singleton.mp hb
              exact known ((equal.trans bEq) ▸ ha)
            obtain ⟨priorOrder, nextUnique, reads, probes⟩ := ih (parent key) (seen ++ [key]) freshUnique
            simp only [walk, List.contains_iff_mem, known, ↓reduceIte]
            refine ⟨(List.sublist_append_left seen [key]).trans priorOrder, nextUnique, ?_, ?_⟩
            · simp only [List.length_append, List.length_singleton] at reads
              omega
            · omega

-----------------------------------------------------------------------------------------
-- A completed walk closes every newly inserted edge; old closure licenses early stop
-----------------------------------------------------------------------------------------

private theorem walk_preserves (parent : Parents) (fuel : Nat) (current : Option Nat)
    (seen : List Nat)
    : seen.Subset (walk parent fuel current seen).nodes := by
  induction fuel generalizing current seen with
  | zero => cases current <;> exact fun _ member => member
  | succ fuel ih =>
      cases current with
      | none => exact fun _ member => member
      | some key =>
          simp only [walk]
          split
          · exact fun _ member => member
          · intro node member
            exact ih (parent key) (seen ++ [key]) (List.mem_append_left _ member)

private theorem walk_finished (parent : Parents) (fuel : Nat) (current : Option Nat)
    (seen : List Nat) (finished : (walk parent fuel current seen).finished = true)
    : (∀ key, current = some key → key ∈ (walk parent fuel current seen).nodes)
      ∧ (∀ key ∈ (walk parent fuel current seen).nodes,
          key ∉ seen
          → ∀ ancestor,
              parent key = some ancestor
              → ancestor ∈ (walk parent fuel current seen).nodes) := by
  induction fuel generalizing current seen with
  | zero =>
      cases current with
      | none =>
          refine ⟨by simp, ?_⟩
          intro key present absent
          exact False.elim (absent present)
      | some key => simp [walk] at finished
  | succ fuel ih =>
      cases current with
      | none =>
          refine ⟨by simp, ?_⟩
          intro key present absent
          exact False.elim (absent present)
      | some key =>
          by_cases known : key ∈ seen
          · simp only [walk, List.contains_iff_mem, known, ↓reduceIte]
            refine ⟨by simpa using known, ?_⟩
            intro node present absent
            exact False.elim (absent present)
          · simp only [walk, List.contains_iff_mem, known, ↓reduceIte] at *
            obtain ⟨currentCovered, edges⟩ := ih (parent key) (seen ++ [key]) finished
            have priorOrder := walk_preserves parent fuel (parent key) (seen ++ [key])
            refine ⟨?_, ?_⟩
            · intro other equal
              cases equal
              exact priorOrder (by simp)
            · intro other present fresh ancestor edge
              by_cases same : other = key
              · exact currentCovered ancestor (same ▸ edge)
              · apply edges other present
                · simpa [same] using fresh
                · exact edge

private theorem walk_finishes (parent : Parents) (height : Nat → Nat)
    (decreasing : Decreasing parent height) (fuel : Nat) (current : Option Nat)
    (seen : List Nat) (enough : ∀ key, current = some key → height key < fuel)
    : (walk parent fuel current seen).finished = true := by
  induction fuel generalizing current seen with
  | zero =>
      cases current with
      | none => rfl
      | some key => have impossible := enough key rfl; omega
  | succ fuel ih =>
      cases current with
      | none => rfl
      | some key =>
          simp only [walk]
          split
          · rfl
          · apply ih
            intro ancestor edge
            have smaller := decreasing key ancestor edge
            have bound := enough key rfl
            omega

private theorem walk_reachable (parent : Parents) (seeds : List Nat) (fuel : Nat)
    (current : Option Nat) (seen : List Nat)
    (prior : ∀ key ∈ seen, Reachable parent seeds key)
    (currentIn : ∀ key, current = some key → Reachable parent seeds key)
    : ∀ key ∈ (walk parent fuel current seen).nodes, Reachable parent seeds key := by
  induction fuel generalizing current seen with
  | zero => cases current <;> exact prior
  | succ fuel ih =>
      cases current with
      | none => exact prior
      | some key =>
          simp only [walk]
          split
          · exact prior
          · apply ih
            · intro node member
              simp only [List.mem_append, List.mem_singleton] at member
              rcases member with member | rfl
              · exact prior node member
              · exact currentIn node rfl
            · intro ancestor edge
              exact .ancestor key ancestor (currentIn key rfl) edge

-----------------------------------------------------------------------------------------
-- Same discovery fold constructs closure, exact identities and operation counts
-----------------------------------------------------------------------------------------

private theorem discover_invariants (parent : Parents) (height : Nat → Nat)
    (decreasing : Decreasing parent height) (seeds seen : List Nat)
    (unique : seen.Nodup) (closed : ParentClosed parent seen)
    : let observed := discoverFrom parent height seeds seen
      observed.finished = true
      ∧ seen.Sublist observed.nodes
      ∧ observed.nodes.Nodup
      ∧ ParentClosed parent observed.nodes
      ∧ seeds.Subset observed.nodes
      ∧ observed.parentReads + seen.length = observed.nodes.length
      ∧ observed.probes ≤ observed.parentReads + seeds.length := by
  induction seeds generalizing seen with
  | nil =>
      refine ⟨
        rfl,
        List.Sublist.refl _,
        unique,
        closed,
        ?_,
        by simp [discoverFrom],
        by simp [discoverFrom]
      ⟩
      exact fun _ member => False.elim (List.not_mem_nil member)
  | cons key rest ih =>
      let head := walk parent (height key + 1) (some key) seen
      have finished : head.finished = true := walk_finishes parent height decreasing _ _ seen (by simp)
      obtain ⟨priorOrder, nextUnique, reads, probes⟩ := walk_counts parent (height key + 1) (some key) seen unique
      obtain ⟨covers, newEdges⟩ := walk_finished parent (height key + 1) (some key) seen finished
      have nextClosed : ParentClosed parent head.nodes := by
        intro node present ancestor edge
        by_cases old : node ∈ seen
        · exact priorOrder.subset (closed node old ancestor edge)
        · exact newEdges node present old ancestor edge
      obtain ⟨tailFinished, tailExtends, tailUnique, tailClosed, tailCovers, tailReads, tailProbes⟩ :=
        ih head.nodes nextUnique nextClosed
      refine ⟨?_, priorOrder.trans tailExtends, tailUnique, tailClosed, ?_, ?_, ?_⟩
      · change (head.finished && (discoverFrom parent height rest head.nodes).finished) = true
        rw [finished, tailFinished]
        rfl
      · intro node member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact tailExtends.subset (covers node rfl)
        · exact tailCovers member
      · dsimp only [discoverFrom, head] at *
        omega
      · dsimp only [discoverFrom, head] at *
        simp only [List.length_cons]
        omega

private theorem discover_reachable (parent : Parents) (height : Nat → Nat)
    (allSeeds seeds seen : List Nat) (seedIn : seeds.Subset allSeeds)
    (prior : ∀ key ∈ seen, Reachable parent allSeeds key)
    : ∀ key ∈ (discoverFrom parent height seeds seen).nodes,
        Reachable parent allSeeds key := by
  induction seeds generalizing seen with
  | nil => exact prior
  | cons key rest ih =>
      apply ih _ (fun _ member => seedIn (List.mem_cons_of_mem _ member))
      apply walk_reachable
      · exact prior
      · intro node same
        have equal : key = node := Option.some.inj same
        rw [← equal]
        exact .seed key (seedIn (by simp))

theorem ParentDiscoveryOptimization_holds : ParentDiscoveryOptimization := by
  intro parent height decreasing seeds
  dsimp only [discover]
  obtain ⟨finished, _, unique, closed, seedsCovered, reads, probes⟩ :=
    discover_invariants parent height decreasing seeds [] (by simp) (by simp [ParentClosed])
  refine ⟨finished, unique, closed, ?_, ?_, ?_⟩
  · intro key
    constructor
    · exact discover_reachable parent height seeds seeds [] (fun _ member => member) (by simp) key
    · intro reachable
      induction reachable with
      | seed node present => exact seedsCovered present
      | ancestor node ancestor _ edge covered => exact closed node covered ancestor edge
  · simpa using reads
  · have readEq : (discoverFrom parent height seeds []).parentReads
        = (discoverFrom parent height seeds []).nodes.length := by simpa using reads
    rw [readEq] at probes
    exact probes

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ParentDiscovery
