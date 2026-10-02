import Proofs.GraphQL.IncrementalDelivery.Correctness.AbsolutePositions
import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedCursorAgreement

/-! Absolute object/item atoms replay the data effects of the client merger. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

/-- Apply one absolute object payload or append one item; IDs have already been
resolved.
-/
def PositionAtom.apply (atom : PositionAtom) (data : ResponseValue)
    : Option ResponseValue :=
  match atom with
  | .object path incoming =>
      ResponseMerging.modifyAtPath path
        (fun value =>
          match value with
          | .object existing =>
              some (.object (ResponseMerging.putFields existing incoming))
          | _ => none) data
  | .item path incoming =>
      ResponseMerging.modifyAtPath path
        (fun value =>
          match value with
          | .list existing => some (.list (existing ++ [incoming]))
          | _ => none) data

/-- Replay only the supplied absolute atoms, in their observed order. -/
def applyAtoms (atoms : List PositionAtom) (data : ResponseValue)
    : Option ResponseValue :=
  atoms.foldlM (fun data atom => atom.apply data) data

/-- Atom concatenation composes data effects, by the monadic fold append identity. -/
theorem applyAtoms_append (left right : List PositionAtom) (data : ResponseValue)
    : applyAtoms (left ++ right) data
      = (applyAtoms left data).bind (applyAtoms right) := by
  rw [applyAtoms, List.foldlM_append]
  rfl

/-- Replacing an existing named field keeps that field available at its new value.
Witness: list induction, preserving the first matching name.
-/
theorem replaced_fields_find (name : Name) (updated : ResponseValue)
    {fields : List (Name × ResponseValue)} {old}
    (found : fields.find? (fun field => field.1 == name) = some old)
    : (fields.map (fun field => if field.1 == name then (name, updated) else field)).find?
        (fun field => field.1 == name)
      = some (name, updated) := by
  induction fields with
  | nil => simp at found
  | cons field rest ih =>
      by_cases same : field.1 = name
      · simp only [List.map_cons, List.find?_cons, same, beq_self_eq_true, ↓reduceIte]
      · simp only [List.map_cons, List.find?_cons, beq_eq_false_iff_ne.mpr same,
          Bool.false_eq_true, ↓reduceIte] at found ⊢
        exact ih found

/-- A second replacement at the same field supersedes the first, by pointwise cases. -/
theorem replaced_fields_twice (name : Name) (first second : ResponseValue)
    (fields : List (Name × ResponseValue))
    : (fields.map (fun field => if field.1 == name then (name, first) else field)).map
        (fun field => if field.1 == name then (name, second) else field)
      = fields.map (fun field => if field.1 == name then (name, second) else field) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro field _
  by_cases same : field.1 = name <;> simp [same]

/-- Two modifications at the same absolute path compose at that path, without changing
the ancestors. Witness: path induction through named-field replacement and indexed set.
-/
theorem modifyAtPath_bind (path : ResponsePath) (data : ResponseValue)
    (first second : ResponseValue → Option ResponseValue)
    : (ResponseMerging.modifyAtPath path first data).bind
        (ResponseMerging.modifyAtPath path second)
      = ResponseMerging.modifyAtPath path (fun value => (first value).bind second)
          data := by
  induction path generalizing data with
  | nil => rfl
  | cons segment rest ih =>
      cases segment with
      | field name =>
          cases data <;> try rfl
          case object fields =>
            cases found : fields.find? (fun field => field.1 == name) with
            | none => simp [ResponseMerging.modifyAtPath, found]
            | some old =>
                have composition := ih old.2
                cases head : ResponseMerging.modifyAtPath rest first old.2 with
                | none =>
                    simp only [ResponseMerging.modifyAtPath, found, Option.bind_eq_bind, Option.bind_some,
                      Option.bind_none, Option.pure_def, ← composition, head]
                | some updated =>
                    have next := replaced_fields_find name updated found
                    cases tail : ResponseMerging.modifyAtPath rest second updated <;>
                      simp only [ResponseMerging.modifyAtPath, found, Option.bind_eq_bind, Option.bind_some,
                        Option.bind_none, Option.pure_def, ← composition, head, next,
                        tail, replaced_fields_twice]
      | index index =>
          cases data <;> try rfl
          case list items =>
            cases found : items[index]? with
            | none => simp [ResponseMerging.modifyAtPath, found]
            | some old =>
                have bound := (List.getElem?_eq_some_iff.mp found).choose
                have composition := ih old
                cases head : ResponseMerging.modifyAtPath rest first old with
                | none =>
                    simp only [ResponseMerging.modifyAtPath, found, Option.bind_eq_bind, Option.bind_some,
                      Option.bind_none, Option.pure_def, ← composition, head]
                | some updated =>
                    cases tail : ResponseMerging.modifyAtPath rest second updated <;>
                      simp only [ResponseMerging.modifyAtPath, found, Option.bind_eq_bind, Option.bind_some,
                        Option.bind_none, Option.pure_def, ← composition, head,
                        List.getElem?_set_self, bound, tail, List.set_set]

/-- Repeated item appends at one path equal one nonempty list patch. Witness: fold
induction and same-path modification composition; nonemptiness avoids a spurious
parent traversal for an empty atom sequence.
-/
theorem applyAtoms_items (path : ResponsePath) (items : List ResponseValue)
    (nonempty : items ≠ []) (data : ResponseValue)
    : applyAtoms (items.map (PositionAtom.item path)) data
      = ResponseMerging.modifyAtPath path
          (fun value =>
            match value with
            | .list existing => some (.list (existing ++ items))
            | _ => none) data := by
  induction items generalizing data with
  | nil => exact False.elim (nonempty rfl)
  | cons head rest ih =>
      cases rest with
      | nil => simp [applyAtoms, PositionAtom.apply]
      | cons next tail =>
          simp only [List.map_cons, applyAtoms, List.foldlM_cons]
          change ((PositionAtom.item path head).apply data).bind
            (applyAtoms ((next :: tail).map (PositionAtom.item path))) = _
          have restEq := funext (fun current => ih (by simp) current)
          simp only [restEq, PositionAtom.apply, modifyAtPath_bind]
          apply congrArg (fun f => ResponseMerging.modifyAtPath path f data)
          funext value
          cases value <;> simp [List.append_assoc]

end GraphQL.IncrementalDelivery.Correctness
