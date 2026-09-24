import GraphQL.IncrementalDelivery.WorkScheduler

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Selecting an effective publication owner
-----------------------------------------------------------------------------------------

/-- A proof-facing raw shared-task value retains its contributing groups until
publication ownership is selected. It is not part of the public execution model.
-/
structure SharedGroupValue where
  value : GroupValue
  contributors : List DeliveryNode
deriving Repr

/-- Select a longest-path open contributor, starting with an open contributing provisional
owner. Strict improvement preserves that owner on ties, then the first longer candidate.
This proof-facing adapter models publisher-side selection without allocating wire IDs.
-/
def selectGroupOwner (openKeys : List Nat) (provisional : DeliveryNode)
    : List DeliveryNode → DeliveryNode
  | [] => provisional
  | candidate :: rest =>
      let selected :=
        if candidate.key ∈ openKeys ∧ provisional.path.length < candidate.path.length then
          candidate
        else
          provisional
      selectGroupOwner openKeys selected rest

/-- Project a raw GROUP_VALUES event to spec-facing publications. Different shared values
may select different owners, so each becomes one event in the same work batch. Payloads,
errors, and value order are unchanged; this step emits no notices or completions.
-/
def normalizeGroupValues (openKeys : List Nat) (provisional : DeliveryNode)
    (values : List SharedGroupValue)
    : List WorkEvent :=
  values.map
    fun shared =>
      .groupValues (selectGroupOwner openKeys provisional shared.contributors)
        [shared.value]

/-- Selection returns the provisional owner or an open listed contributor. Witness:
induction over the candidates, retaining provenance whenever a longer path replaces it.
-/
theorem selectGroupOwner_mem (openKeys : List Nat) (provisional : DeliveryNode)
    (contributors : List DeliveryNode)
    : selectGroupOwner openKeys provisional contributors = provisional
      ∨ selectGroupOwner openKeys provisional contributors ∈ contributors
        ∧ (selectGroupOwner openKeys provisional contributors).key ∈ openKeys := by
  induction contributors generalizing provisional with
  | nil => exact Or.inl rfl
  | cons candidate rest ih =>
      simp only [selectGroupOwner]
      split
      · rename_i longer
        rcases ih candidate with same | selected
        · exact Or.inr ⟨by simp [same], by simpa only [same] using longer.1⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ selected.1, selected.2⟩
      · rcases ih provisional with same | selected
        · exact Or.inl same
        · exact Or.inr ⟨List.mem_cons_of_mem _ selected.1, selected.2⟩

/-- Selection never shortens the provisional owner's path. Witness: every replacement
strictly increases path length.
-/
theorem selectGroupOwner_ge (openKeys : List Nat) (provisional : DeliveryNode)
    (contributors : List DeliveryNode)
    : provisional.path.length
      ≤ (selectGroupOwner openKeys provisional contributors).path.length := by
  induction contributors generalizing provisional with
  | nil => exact Nat.le_refl _
  | cons candidate rest ih =>
      simp only [selectGroupOwner]
      split
      · rename_i longer
        exact Nat.le_trans (Nat.le_of_lt longer.2) (ih candidate)
      · exact ih provisional

/-- Every open listed contributor is no deeper than the selected owner. Witness: list
induction, comparing the head before recursively maximizing the remaining candidates.
-/
theorem selectGroupOwner_max (openKeys : List Nat) (provisional : DeliveryNode)
    (contributors : List DeliveryNode) (other : DeliveryNode)
    (member : other ∈ contributors) (opened : other.key ∈ openKeys)
    : other.path.length
      ≤ (selectGroupOwner openKeys provisional contributors).path.length := by
  induction contributors generalizing provisional with
  | nil => simp at member
  | cons candidate rest ih =>
      simp only [selectGroupOwner]
      split
      · rcases List.mem_cons.mp member with rfl | member
        · exact selectGroupOwner_ge openKeys other rest
        · exact ih candidate member
      · rename_i unchanged
        rcases List.mem_cons.mp member with rfl | member
        · have bounded : other.path.length ≤ provisional.path.length :=
            Nat.le_of_not_gt (fun smaller => unchanged ⟨opened, smaller⟩)
          exact Nat.le_trans bounded (selectGroupOwner_ge openKeys provisional rest)
        · exact ih provisional member

/-- An already longest provisional owner is unchanged, including all equal-length ties.
Witness: no candidate satisfies the strict replacement test.
-/
theorem selectGroupOwner_eq_of_max (openKeys : List Nat) (provisional : DeliveryNode)
    (contributors : List DeliveryNode)
    (greatest
      : ∀ other ∈ contributors,
          other.key ∈ openKeys → other.path.length ≤ provisional.path.length)
    : selectGroupOwner openKeys provisional contributors = provisional := by
  induction contributors with
  | nil => rfl
  | cons candidate rest ih =>
      have unchanged : ¬(candidate.key ∈ openKeys ∧
          provisional.path.length < candidate.path.length) := by
        intro longer
        exact Nat.not_lt_of_ge (greatest candidate (by simp) longer.1) longer.2
      simp only [selectGroupOwner, ite_eq_right unchanged]
      exact ih (fun other member => greatest other (List.mem_cons_of_mem _ member))

/-- Owner normalization retains every data/error payload in order. Witness: mapping each
shared value to exactly one singleton publication, without filtering or copying values.
-/
theorem normalizeGroupValues_payloads (openKeys : List Nat) (provisional : DeliveryNode)
    (values : List SharedGroupValue)
    : (normalizeGroupValues openKeys provisional values).flatMap
        (fun event =>
          match event with
          | .groupValues _ payloads => payloads
          | _ => [])
      = values.map SharedGroupValue.value := by
  induction values with
  | nil => rfl
  | cons shared rest ih => simp_all [normalizeGroupValues]

/-- Normalization creates no notice or closure. Witness: all projected events are value
publications; raw control events can pass through without changing lifecycle accounting.
-/
theorem normalizeGroupValues_notices (openKeys : List Nat) (provisional : DeliveryNode)
    (values : List SharedGroupValue)
    : pendingKeys (normalizeGroupValues openKeys provisional values) = []
      ∧ completedKeys (normalizeGroupValues openKeys provisional values) = [] := by
  simp [pendingKeys, completedKeys, normalizeGroupValues, List.flatMap_map,
    eventPending, eventCompleted]

/-- A provisional available owner becomes a permitted effective owner when the supplied
open contributors exactly cover the available choices. Witness: executable maximum
selection, not an assumption that the provisional owner already has a longest path.
-/
theorem selectGroupOwner_owner
    {work initial events failed owners openKeys provisional contributors}
    (available : AvailableOwner work initial events failed owners provisional)
    (sound
      : ∀ node ∈ contributors,
          node.key ∈ openKeys → AvailableOwner work initial events failed owners node)
    (complete
      : ∀ node,
          AvailableOwner work initial events failed owners node
          → node ∈ contributors ∧ node.key ∈ openKeys)
    : Owner work initial events failed owners
        (selectGroupOwner openKeys provisional contributors) := by
  constructor
  · rcases selectGroupOwner_mem openKeys provisional contributors with same | selected
    · simpa only [same] using available
    · exact sound _ selected.1 selected.2
  · intro other active
    obtain ⟨member, opened⟩ := complete other active
    exact selectGroupOwner_max openKeys provisional contributors other member opened

/-- Normalizing one ready raw object publication satisfies the existing event rule.
Witness: retain its task, payload, and readiness; derive only its effective owner using
complete contributor metadata. No additional publication or lifecycle premise is assumed.
-/
theorem normalized_groupValues_allowed
    {work initial matching before failed owners producer value openKeys provisional
      contributors}
    (known
      : TaskAt work (matching before.length) owners producer
          (.object value.path (.ok (value.data, value.errors))))
    (ready : CanPublish work matching before failed (matching before.length) producer)
    (available : AvailableOwner work initial before failed owners provisional)
    (sound
      : ∀ node ∈ contributors,
          node.key ∈ openKeys → AvailableOwner work initial before failed owners node)
    (complete
      : ∀ node,
          AvailableOwner work initial before failed owners node
          → node ∈ contributors ∧ node.key ∈ openKeys)
    : EventAllowed work initial matching before failed
        (.groupValues (selectGroupOwner openKeys provisional contributors) [value]) := by
  exact ⟨owners, producer, value.path, value.data, value.errors, rfl, known, ready,
    selectGroupOwner_owner available sound complete⟩

end GraphQL.IncrementalDelivery.WorkScheduler
