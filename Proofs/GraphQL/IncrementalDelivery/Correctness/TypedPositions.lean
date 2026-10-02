import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedResponse

/-! Forgetting typed atoms recovers both public response-position modes. -/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse
open GraphQL.IncrementalDelivery.Execution

/-- Keep scalar/null paths and optionally container paths while forgetting their tags. -/
def entryPath (containers : Bool) (entry : Entry) : Option ResponsePath :=
  match entry.2 with
  | .null | .scalar _ => some entry.1
  | .object | .list => if containers then some entry.1 else none

mutual
  /-- Optional tag erasure recovers value positions, by mutual structural descent. -/
  theorem value_entryPaths (containers : Bool) (path : ResponsePath)
      (data : ResponseValue)
      : (value path data).filterMap (entryPath containers)
        = DeliveryPaths.value containers path data := by
    cases data with
    | null => rfl
    | scalar text => rfl
    | object data => cases containers <;>
        simp [value, entryPath, DeliveryPaths.value, fields_entryPaths]
    | list data => cases containers <;>
        simp [value, entryPath, DeliveryPaths.value, items_entryPaths]

  /-- Optional tag erasure recovers field positions, by object-list descent. -/
  theorem fields_entryPaths (containers : Bool) (path : ResponsePath)
      (data : List (Name × ResponseValue))
      : (fields path data).filterMap (entryPath containers)
        = DeliveryPaths.fields containers path data := by
    cases data with
    | nil => rfl
    | cons head rest =>
        simp [fields, DeliveryPaths.fields, value_entryPaths, fields_entryPaths]

  /-- Optional tag erasure recovers indexed item positions, by item-list descent. -/
  theorem items_entryPaths (containers : Bool) (path : ResponsePath) (index : Nat)
      (data : List ResponseValue)
      : (items path index data).filterMap (entryPath containers)
        = DeliveryPaths.items containers path index data := by
    cases data with
    | nil => rfl
    | cons head rest =>
        simp [items, DeliveryPaths.items, value_entryPaths, items_entryPaths]
end

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
