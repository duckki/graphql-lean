import GraphQL.Execution
import GraphQL.Theories.ResponseDepth

/-! Sufficiency of the public schema-aware execution fuel bound. -/

namespace GraphQL
namespace Execution

-- Proof-side execution requirement for a response depth. Each response-field boundary
-- may be followed by the schema's largest type-completion path.
def responseDepthFuelBound (schema : Schema) (depth : Nat) : Nat :=
  depth * (typeDefinitionsExecutionCompletionFuel schema.types + 1) + 1

theorem selectionSetResponseDepth_append (left right : List Selection)
    : selectionSetResponseDepth (left ++ right)
      = max (selectionSetResponseDepth left) (selectionSetResponseDepth right) := by
  induction left with
  | nil => simp [selectionSetResponseDepth]
  | cons selection rest ih =>
      simp [selectionSetResponseDepth, ih, Nat.max_assoc]

theorem fieldDefinitionsExecutionCompletionFuel_mem
    {field : FieldDefinition} {fields : List FieldDefinition}
    (hfield : field ∈ fields)
    : typeRefExecutionCompletionFuel field.outputType
      ≤ fieldDefinitionsExecutionCompletionFuel fields := by
  induction fields with
  | nil => simp at hfield
  | cons head rest ih =>
      rcases List.mem_cons.mp hfield with rfl | hrest
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)

theorem typeDefinitionsExecutionCompletionFuel_object_mem
    {objectType : ObjectType} {types : List TypeDefinition}
    (hobject : TypeDefinition.object objectType ∈ types)
    : fieldDefinitionsExecutionCompletionFuel objectType.fields
      ≤ typeDefinitionsExecutionCompletionFuel types := by
  induction types with
  | nil => simp at hobject
  | cons head rest ih =>
      rcases List.mem_cons.mp hobject with hhead | hrest
      · subst head
        exact Nat.le_max_left _ _
      · cases head <;>
          simp only [typeDefinitionsExecutionCompletionFuel]
        all_goals first
          | exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)
          | exact ih hrest

theorem typeDefinitionsExecutionCompletionFuel_interface_mem
    {interfaceType : InterfaceType} {types : List TypeDefinition}
    (hinterface : TypeDefinition.interface interfaceType ∈ types)
    : fieldDefinitionsExecutionCompletionFuel interfaceType.fields
      ≤ typeDefinitionsExecutionCompletionFuel types := by
  induction types with
  | nil => simp at hinterface
  | cons head rest ih =>
      rcases List.mem_cons.mp hinterface with hhead | hrest
      · subst head
        exact Nat.le_max_left _ _
      · cases head <;>
          simp only [typeDefinitionsExecutionCompletionFuel]
        all_goals first
          | exact Nat.le_trans (ih hrest) (Nat.le_max_right _ _)
          | exact ih hrest

theorem lookupField_executionCompletionFuel_le
    (schema : Schema) {parentType fieldName : Name}
    {fieldDefinition : FieldDefinition}
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    : typeRefExecutionCompletionFuel fieldDefinition.outputType
      ≤ typeDefinitionsExecutionCompletionFuel schema.types := by
  unfold Schema.lookupField at hlookup
  cases htype : schema.lookupType parentType with
  | none => simp [htype] at hlookup
  | some typeDefinition =>
      simp only [htype, Option.bind_eq_bind] at hlookup
      have htypeMem : typeDefinition ∈ schema.allTypes := by
        exact List.mem_of_find?_eq_some htype
      unfold Schema.allTypes at htypeMem
      rcases typeDefinition with scalar | scalar | objectType | interfaceType |
          unionType | enumType | inputObjectType
      all_goals simp only [TypeDefinition.fields?] at hlookup
      · cases hlookup
      · cases hlookup
      · have hfield : fieldDefinition ∈ objectType.fields :=
          List.mem_of_find?_eq_some hlookup
        have hobject : TypeDefinition.object objectType ∈ schema.types := by
          simpa [Schema.builtinScalarDefinitions] using htypeMem
        exact Nat.le_trans
          (fieldDefinitionsExecutionCompletionFuel_mem hfield)
          (typeDefinitionsExecutionCompletionFuel_object_mem hobject)
      · have hfield : fieldDefinition ∈ interfaceType.fields :=
          List.mem_of_find?_eq_some hlookup
        have hinterface : TypeDefinition.interface interfaceType ∈ schema.types := by
          simpa [Schema.builtinScalarDefinitions] using htypeMem
        exact Nat.le_trans
          (fieldDefinitionsExecutionCompletionFuel_mem hfield)
          (typeDefinitionsExecutionCompletionFuel_interface_mem hinterface)
      · cases hlookup
      · cases hlookup
      · cases hlookup

-- Fuel sufficient to finish a value at the current response depth after its field
-- resolver has consumed one unit of the surrounding selection-set fuel.
def valueCompletionFuelBound (schema : Schema) (depth : Nat) (fieldType : TypeRef)
    : Nat :=
  (depth - 1) * (typeDefinitionsExecutionCompletionFuel schema.types + 1)
  + typeRefExecutionCompletionFuel fieldType
  + 1

theorem valueCompletionFuelBound_le_after_field
    (schema : Schema) (depth completionFuel : Nat) (fieldType : TypeRef)
    (hdepth : 0 < depth)
    (htype
      : typeRefExecutionCompletionFuel fieldType
        ≤ typeDefinitionsExecutionCompletionFuel schema.types)
    (hfuel : responseDepthFuelBound schema depth ≤ completionFuel + 1)
    : valueCompletionFuelBound schema depth fieldType ≤ completionFuel := by
  let schemaFuel := typeDefinitionsExecutionCompletionFuel schema.types
  have hdepthEq : depth = (depth - 1) + 1 := by omega
  have hmul :
      depth * (schemaFuel + 1)
        = (depth - 1) * (schemaFuel + 1) + (schemaFuel + 1) := by
    calc
      depth * (schemaFuel + 1) = ((depth - 1) + 1) * (schemaFuel + 1) :=
        congrArg (fun value => value * (schemaFuel + 1)) hdepthEq
      _ = (depth - 1) * (schemaFuel + 1) + (schemaFuel + 1) := by
        simp [Nat.add_mul]
  have hmiddle :
      (depth - 1) * (schemaFuel + 1)
          + typeRefExecutionCompletionFuel fieldType + 1
        ≤ depth * (schemaFuel + 1) := by
    rw [hmul]
    omega
  exact Nat.le_trans hmiddle (by
    unfold responseDepthFuelBound at hfuel
    change depth * (schemaFuel + 1) + 1 ≤ completionFuel + 1 at hfuel
    omega)

theorem responseDepthFuelBound_le_of_value_named
    (schema : Schema) (depth fuel : Nat) (typeName : Name)
    (hvalue : valueCompletionFuelBound schema depth (.named typeName) ≤ fuel + 1)
    : responseDepthFuelBound schema (depth - 1) ≤ fuel := by
  unfold valueCompletionFuelBound typeRefExecutionCompletionFuel at hvalue
  unfold responseDepthFuelBound
  omega

theorem valueCompletionFuelBound_inner_list
    (schema : Schema) (depth fuel : Nat) (inner : TypeRef)
    (hvalue : valueCompletionFuelBound schema depth (.list inner) ≤ fuel + 1)
    : valueCompletionFuelBound schema depth inner ≤ fuel := by
  simp only [valueCompletionFuelBound, typeRefExecutionCompletionFuel] at hvalue ⊢
  omega

theorem valueCompletionFuelBound_inner_nonNull
    (schema : Schema) (depth : Nat) (inner : TypeRef)
    : valueCompletionFuelBound schema depth (.nonNull inner)
      = valueCompletionFuelBound schema depth inner := by
  simp [valueCompletionFuelBound, typeRefExecutionCompletionFuel]

mutual
  theorem selectionResponseDepth_le_size (selection : Selection)
      : selectionResponseDepth selection ≤ selection.size := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        simp only [selectionResponseDepth, Selection.size]
        simpa [Nat.add_comm] using
          Nat.add_le_add_right (selectionSetResponseDepth_le_size selectionSet) 1
    | inlineFragment typeCondition directives selectionSet =>
        simp only [selectionResponseDepth, Selection.size]
        simpa [Nat.add_comm] using
          Nat.le_succ_of_le (selectionSetResponseDepth_le_size selectionSet)

  theorem selectionSetResponseDepth_le_size (selectionSet : List Selection)
      : selectionSetResponseDepth selectionSet ≤ SelectionSet.size selectionSet := by
    cases selectionSet with
    | nil => exact Nat.le_refl _
    | cons selection rest =>
        simp only [selectionSetResponseDepth, SelectionSet.size]
        exact Nat.max_le.mpr
          ⟨Nat.le_trans (selectionResponseDepth_le_size selection)
              (Nat.le_add_right _ _),
            Nat.le_trans (selectionSetResponseDepth_le_size rest)
              (Nat.le_add_left _ _)⟩
end

theorem doesNotExhaustFuel (schema : Schema) (operation : Operation)
    : responseDepthFuelBound schema (selectionSetResponseDepth operation.selectionSet)
      ≤ executeQueryFuelBound schema operation := by
  unfold responseDepthFuelBound executeQueryFuelBound Operation.size
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _
      (selectionSetResponseDepth_le_size operation.selectionSet)) 1

end Execution
end GraphQL
