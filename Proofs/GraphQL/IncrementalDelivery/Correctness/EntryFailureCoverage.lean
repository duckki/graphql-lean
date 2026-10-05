import Proofs.GraphQL.IncrementalDelivery.Correctness.OrdinaryFailureAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReferenceNullPositions

/-! Typed-entry algebra for mixed response coverage, retaining ordinary null evidence. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics
open TypedResponse (Atom Entry)

-----------------------------------------------------------------------------------------
-- Typed entries retain null tags until the final reference-response lookup
-----------------------------------------------------------------------------------------

/-- Scalar/null atoms always introduce positions; container atoms do so when requested.
This is the typed-entry counterpart of `ResponsePositions.value`'s container flag.
-/
def TypedResponse.Atom.visible (containers : Bool) : Atom → Bool
  | .null | .scalar _ => true
  | .object | .list => containers

/-- Forget tags after selecting the requested leaf/container entries.
Entry order and multiplicity are preserved; no uniqueness assumption is made here.
-/
def visibleEntryPaths (containers : Bool) (entries : List Entry) : List ResponsePath :=
  (entries.filter (fun entry => entry.2.visible containers)).map Prod.fst

/-- A typed reference entry is available or explained by a real failed task.
Null tags license the ancestor-bubbling branch locally, before looking up that null in
the assembled reference response. `available` may contain initial and future positions.
-/
def EntryExplained (available : List ResponsePath) (work : Work) (entry : Entry) : Prop :=
  entry.1 ∈ available
  ∨ ∃ occurrence owners producer payload,
      TaskAt work occurrence owners producer payload
      ∧ payload.failure.isSome = true
      ∧ (payload.path.IsPrefix entry.1 ∨ entry.2 = .null ∧ entry.1.IsPrefix payload.path)

/-- Every visible typed reference entry has a data or retained-failure explanation.
Invisible containers impose no leaf-only coverage obligation.
-/
def EntriesCovered (containers : Bool) (reference : List Entry)
    (available : List ResponsePath) (work : Work)
    : Prop :=
  ∀ entry ∈ reference,
    entry.2.visible containers = true → EntryExplained available work entry

-----------------------------------------------------------------------------------------
-- Visible typed paths are exactly the public response positions
-----------------------------------------------------------------------------------------

/-- Filtering typed-entry tags distributes over concatenated inventories.
Witness: filter/map append equations; nulls and container choices are unchanged.
-/
theorem visibleEntryPaths_append (containers : Bool) (left right : List Entry)
    : visibleEntryPaths containers (left ++ right)
      = visibleEntryPaths containers left ++ visibleEntryPaths containers right := by
  simp [visibleEntryPaths]

mutual
  /-- Visible typed value paths equal public value positions, including null leaves.
  Witness: response-value descent, retaining or excluding each container's own entry.
  -/
  theorem visibleEntryPaths_value (containers : Bool) (path : ResponsePath)
      (data : ResponseValue)
      : visibleEntryPaths containers (TypedResponse.value path data)
        = ResponsePositions.value containers path data := by
    cases data with
    | null | scalar _ => simp [TypedResponse.value, visibleEntryPaths, Atom.visible,
        ResponsePositions.value]
    | object fields =>
        cases containers with
        | false =>
            simpa [TypedResponse.value, visibleEntryPaths, Atom.visible,
              ResponsePositions.value] using visibleEntryPaths_fields false path fields
        | true =>
            simpa [TypedResponse.value, visibleEntryPaths, Atom.visible,
              ResponsePositions.value] using congrArg (List.cons path)
                (visibleEntryPaths_fields true path fields)
    | list values =>
        cases containers with
        | false =>
            simpa [TypedResponse.value, visibleEntryPaths, Atom.visible,
              ResponsePositions.value] using visibleEntryPaths_items false path 0 values
        | true =>
            simpa [TypedResponse.value, visibleEntryPaths, Atom.visible,
              ResponsePositions.value] using congrArg (List.cons path)
                (visibleEntryPaths_items true path 0 values)
  termination_by sizeOf data

  /-- Visible typed field paths equal public response-alias positions.
  Witness: field-list descent and the same value projection for every subtree.
  -/
  theorem visibleEntryPaths_fields (containers : Bool) (path : ResponsePath)
      (fields : List (Name × ResponseValue))
      : visibleEntryPaths containers (TypedResponse.fields path fields)
        = ResponsePositions.fields containers path fields := by
    cases fields with
    | nil => rfl
    | cons field rest =>
        obtain ⟨name, data⟩ := field
        simp only [TypedResponse.fields, visibleEntryPaths_append, ResponsePositions.fields]
        rw [visibleEntryPaths_value containers (path ++ [ResponsePathSegment.field name]) data,
          visibleEntryPaths_fields containers path rest]
  termination_by sizeOf fields

  /-- Visible typed item paths equal public indexed positions at the same absolute offset.
  Witness: item-list descent, retaining its increasing starting index.
  -/
  theorem visibleEntryPaths_items (containers : Bool) (path : ResponsePath) (index : Nat)
      (values : List ResponseValue)
      : visibleEntryPaths containers (TypedResponse.items path index values)
        = ResponsePositions.items containers path index values := by
    cases values with
    | nil => rfl
    | cons value rest =>
        simp only [TypedResponse.items, visibleEntryPaths_append, ResponsePositions.items]
        rw [visibleEntryPaths_value containers (path ++ [ResponsePathSegment.index index]) value,
          visibleEntryPaths_items containers path (index + 1) rest]
  termination_by sizeOf values
end

/-- A visible path has a witnessed typed entry, including its unchanged null/scalar tag.
Witness: membership inversion through filter and map; duplicate paths remain permitted.
-/
theorem mem_visibleEntryPaths_iff {containers path entries}
    : path ∈ visibleEntryPaths containers entries
      ↔ ∃ entry ∈ entries, entry.2.visible containers = true ∧ entry.1 = path := by
  simp only [visibleEntryPaths, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨entry, ⟨member, visible⟩, same⟩
    exact ⟨entry, member, visible, same⟩
  · rintro ⟨entry, member, visible, same⟩
    exact ⟨entry, ⟨member, visible⟩, same⟩

-----------------------------------------------------------------------------------------
-- Entry coverage composes without referring to an enclosing response lookup
-----------------------------------------------------------------------------------------

/-- Growing the available data inventory preserves an entry's explanation.
Witness: membership monotonicity; retained failure evidence stays exactly the same.
-/
theorem EntryExplained.available_mono {available other work entry}
    (explained : EntryExplained available work entry) (included : available.Subset other)
    : EntryExplained other work entry := by
  rcases explained with delivered | failed
  · exact Or.inl (included delivered)
  · exact Or.inr failed

/-- Combining work preserves the left component's typed failure explanation.
Witness: payload-preserving task embedding; data availability and null tags are fixed.
-/
theorem EntryExplained.combine_left {available work entry}
    (explained : EntryExplained available work entry) (right : Work)
    : EntryExplained available (.combine work right) entry := by
  rcases explained with delivered | failed
  · exact Or.inl delivered
  · obtain ⟨occurrence, owners, producer, payload, known, fails, related⟩ := failed
    obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_combine_left known right
    exact Or.inr ⟨occurrence, owners, producer, payload, embedded, fails, related⟩

/-- Combining work preserves the right component's typed failure explanation.
Witness: payload-preserving task embedding at the right structural edge.
-/
theorem EntryExplained.combine_right {available work entry}
    (explained : EntryExplained available work entry) (left : Work)
    : EntryExplained available (.combine left work) entry := by
  rcases explained with delivered | failed
  · exact Or.inl delivered
  · obtain ⟨occurrence, owners, producer, payload, known, fails, related⟩ := failed
    obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_combine_right known left
    exact Or.inr ⟨occurrence, owners, producer, payload, embedded, fails, related⟩

/-- Reference-entry permutation preserves coverage, including nullable counted errors.
Witness: membership equivalence; no enclosing null lookup or duplicate-path assumption
is needed until the final public-response bridge.
-/
theorem EntriesCovered.perm {containers reference other available work}
    (covered : EntriesCovered containers reference available work)
    (permuted : reference.Perm other)
    : EntriesCovered containers other available work := by
  intro entry member visible
  exact covered entry (permuted.mem_iff.mpr member) visible

/-- Appended reference entries are covered exactly when both parts are covered.
Witness: list membership in each part, with the same available inventory and work.
-/
theorem EntriesCovered.append_iff {containers left right available work}
    : EntriesCovered containers (left ++ right) available work
      ↔ EntriesCovered containers left available work
        ∧ EntriesCovered containers right available work := by
  constructor
  · intro covered
    exact ⟨fun entry member => covered entry (List.mem_append_left _ member),
      fun entry member => covered entry (List.mem_append_right _ member)⟩
  · rintro ⟨leftCovered, rightCovered⟩ entry member visible
    rcases List.mem_append.mp member with left | right
    · exact leftCovered entry left visible
    · exact rightCovered entry right visible

-----------------------------------------------------------------------------------------
-- Nullable failure comparison supplies actual local null-entry coverage
-----------------------------------------------------------------------------------------

/-- An ordinary null entry is initially null or has a real retained descendant failure.
Witness: reverse null reflection; forward bubbling preservation rules out an initial
bubble against the successful ordinary null. Counts and child work remain unrestricted.
-/
theorem nullEntry_explained {path ordinary} {initial : Completion ResponseValue}
    (preserved : InitialFailures.BubblesPreserved ordinary initial.result)
    (reflected : OrdinaryFailures.ValueFailuresExplained path ordinary initial)
    (errors : Nat) (isNull : ordinary = .ok (.null, errors))
    (containers : Bool) (extra : List ResponsePath)
    : EntryExplained
        (DeliveryPaths.result (ResponsePositions.value containers path) initial.result
          ++ extra)
        initial.work (path, .null) := by
  rcases reflected.2 errors isNull with initialFailed | initialNull | retained
  · obtain ⟨count, initialFailed⟩ := initialFailed
    obtain ⟨count, ordinaryFailed⟩ := preserved count initialFailed
    simp [isNull] at ordinaryFailed
  · obtain ⟨count, initialNull⟩ := initialNull
    exact Or.inl (by simp [initialNull, DeliveryPaths.result, ResponsePositions.value])
  · obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := retained
    exact Or.inr ⟨occurrence, owners, producer, payload, known, fails, Or.inr ⟨rfl, below⟩⟩

-----------------------------------------------------------------------------------------
-- Final bridge to the existing public-reference comparison
-----------------------------------------------------------------------------------------

/-- Typed entry coverage implies the path-based prepared response comparison.
Witness: visible-entry projection and actual null lookup in the unique ordinary
reference. Only this bridge requires reference-path uniqueness; local algebra does not.
-/
theorem EntriesCovered.to_prepared {containers reference response work}
    (covered
      : EntriesCovered containers (TypedResponse.value [] reference)
          (ResponsePositions.value containers [] response.data
            ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                  work).flatMap
                (SourceTask.positions containers)) work)
    (unique : ((TypedResponse.value [] reference).map Prod.fst).Nodup)
    : PreparedResponseCovers reference response work containers := by
  intro path member
  rw [← visibleEntryPaths_value] at member
  obtain ⟨entry, member, visible, same⟩ := mem_visibleEntryPaths_iff.mp member
  rcases covered entry member visible with delivered | failed
  · exact Or.inl (same ▸ delivered)
  · obtain ⟨occurrence, owners, producer, payload, known, fails, related⟩ := failed
    rcases related with below | ancestor
    · exact Or.inr ⟨occurrence, owners, producer, payload, known, fails,
        Or.inl (same ▸ below)⟩
    · have isNull : reference.isNullAt entry.1 = true := by
        apply TypedResponse.isNullAt_of_null_entry _ _ _ unique
        simpa only [← ancestor.1] using member
      exact Or.inr ⟨occurrence, owners, producer, payload, known, fails,
        Or.inr ⟨same ▸ isNull, same ▸ ancestor.2⟩⟩

end GraphQL.IncrementalDelivery.Correctness
