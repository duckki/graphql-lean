import GraphQL.Operation
import GraphQL.Execution

/-! Structural response measures shared by recursive execution theories. -/

namespace GraphQL

-- Response-field boundaries along one selection path. Inline fragments do not consume
-- execution or query-inclusion fuel by themselves.
mutual
  def selectionResponseDepth : Selection -> Nat
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetResponseDepth selectionSet + 1
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetResponseDepth selectionSet

  def selectionSetResponseDepth : List Selection -> Nat
    | [] => 0
    | selection :: rest =>
        max (selectionResponseDepth selection) (selectionSetResponseDepth rest)
end

namespace Execution
namespace ResponseValue

-- Counts value nodes. Object fields contribute the size of their values; the object node
-- itself supplies the strict decrease needed when descending into a field.
mutual
  def structuralSize : ResponseValue -> Nat
    | .null => 1
    | .scalar _ => 1
    | .object fields => 1 + fieldListStructuralSize fields
    | .list values => 1 + valueListStructuralSize values

  def fieldListStructuralSize : List (Name × ResponseValue) -> Nat
    | [] => 0
    | (_name, value) :: fields => structuralSize value + fieldListStructuralSize fields

  def valueListStructuralSize : List ResponseValue -> Nat
    | [] => 0
    | value :: values => structuralSize value + valueListStructuralSize values
end

end ResponseValue
end Execution

-----------------------------------------------------------------------------------------
-- Termination theorems only
-----------------------------------------------------------------------------------------

namespace Execution
namespace ResponseValue

theorem structuralSize_lt_of_object_field_mem {name : Name} {value : ResponseValue}
    {fields : List (Name × ResponseValue)}
    (member : (name, value) ∈ fields)
    : value.structuralSize < (ResponseValue.object fields).structuralSize := by
  induction fields with
  | nil => simp at member
  | cons field fields ih =>
      rcases field with ⟨fieldName, fieldValue⟩
      rcases List.mem_cons.mp member with h | h
      · have hvalue : value = fieldValue := congrArg Prod.snd h
        rw [hvalue]
        change fieldValue.structuralSize
          < 1 + (fieldValue.structuralSize + ResponseValue.fieldListStructuralSize fields)
        omega
      · have hlt := ih h
        change value.structuralSize
            < 1 + ResponseValue.fieldListStructuralSize fields
          at hlt
        change value.structuralSize
          < 1 + (fieldValue.structuralSize + ResponseValue.fieldListStructuralSize fields)
        omega

private theorem size_lt_list_head (value : ResponseValue) (values : List ResponseValue)
    : value.structuralSize < (ResponseValue.list (value :: values)).structuralSize := by
  simp [ResponseValue.structuralSize, ResponseValue.valueListStructuralSize]
  omega

private theorem size_lt_list_tail (value : ResponseValue) (values : List ResponseValue)
    : (ResponseValue.list values).structuralSize
      < (ResponseValue.list (value :: values)).structuralSize := by
  cases value <;>
    simp [ResponseValue.structuralSize, ResponseValue.valueListStructuralSize] <;>
    omega

theorem structuralSize_lt_of_list_get? {value : ResponseValue} {index : Nat}
    {values : List ResponseValue}
    (found : values[index]? = some value)
    : value.structuralSize < (ResponseValue.list values).structuralSize := by
  induction values generalizing index with
  | nil => simp at found
  | cons head values ih =>
      cases index with
      | zero =>
          simp at found
          subst value
          exact size_lt_list_head head values
      | succ index =>
          simp at found
          exact Nat.lt_trans (ih found) (size_lt_list_tail head values)

end ResponseValue
end Execution

end GraphQL
