import Proofs.GraphQL.IncrementalDelivery.Semantics.PathOwnership
import Proofs.GraphQL.Execution.FieldGroups
import Proofs.GraphQL.Execution.DuplicateFields

/-! Field collection and planning provide the unique sibling names used for separation. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution
open DeliveryPaths

variable {ObjectRef : Type}

def GroupsUnique (groups : CollectedFieldsMap) : Prop := (groups.map Prod.fst).Nodup

theorem collectFields_unique (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (usage : Option DeferUsage)
    : RunEnsures (fun collection => GroupsUnique collection.fields)
        (collectFields schema variables parentType source selections usage) := by
  intro state
  have he := congrArg (List.map Prod.fst)
    (collectFields_erase schema variables parentType source selections usage state)
  simp only [eraseGroups, List.map_map, eraseGroup, Function.comp_def] at he
  unfold GroupsUnique
  rw [he]
  exact (GraphQL.Execution.FieldGroups.executableGroupNamesNodup_iff_map_fst_nodup _).mp
    (GraphQL.NormalForm.collectFields_namesNodup _ _ _ _ _)

theorem collectSubfields_unique (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    : RunEnsures (fun collection => GroupsUnique collection.fields)
        (collectSubfields schema variables parentType source fields) := by
  intro state
  have he := congrArg (List.map Prod.fst)
    (collectSubfields_erase schema variables parentType source fields state)
  simp only [eraseGroups, List.map_map, eraseGroup, Function.comp_def] at he
  unfold GroupsUnique
  rw [he]
  exact (GraphQL.Execution.FieldGroups.executableGroupNamesNodup_iff_map_fst_nodup _).mp
    (GraphQL.Execution.DuplicateFields.collectSubfields_namesNodup _ _ _ _ _)

theorem owns_fields_append {path : ResponsePath} {left right : List Name}
    {xs ys : List ResponsePath} (hn : (left ++ right).Nodup)
    (hl : Owns (UnderFields path left) xs) (hr : Owns (UnderFields path right) ys)
    : Owns (UnderFields path (left ++ right)) (xs ++ ys) := by
  apply owns_append hl hr
  · intro p hpl hpr
    apply underFields_disjoint (fun n hnl hnr =>
      (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem ownsCompletion_combine_fields {containers : Bool} {path : ResponsePath}
    {leftNames rightNames : List Name}
    {left right : Completion (List (Name × ResponseValue))}
    (hn : (leftNames ++ rightNames).Nodup)
    (hl
      : OwnsCompletion containers (fields containers path) (UnderFields path leftNames)
          left)
    (hr
      : OwnsCompletion containers (fields containers path) (UnderFields path rightNames)
          right)
    : OwnsCompletion containers (fields containers path)
        (UnderFields path (leftNames ++ rightNames))
        (Completion.combine List.append left right) := by
  apply ownsCompletion_combine (fields_append containers path) hl hr
  · exact fun p hpl hpr => underFields_disjoint
      (fun n hnl hnr => (List.nodup_append.mp hn).2.2 n hnl n hnr rfl) hpl hpr
  · exact fun _ => underFields_mono (fun _ => List.mem_append_left _)
  · exact fun _ => underFields_mono (fun _ => List.mem_append_right _)

theorem ownsCompletion_failedField (containers : Bool) (path : ResponsePath)
    (name : Name) (fieldType : TypeRef)
    : OwnsCompletion containers (fields containers path) (Below (path ++ [.field name]))
        { result := singleFieldResult name (handleFieldError fieldType) } := by
  cases fieldType <;>
    simp only [singleFieldResult, handleFieldError, GraphQL.Execution.singleFieldResult,
      GraphQL.Execution.handleFieldError, OwnsCompletion, completion, result, work,
      fields, value, List.append_nil] <;>
    first | exact owns_nil _ | exact owns_singleton (below_self _)

end GraphQL.IncrementalDelivery.Semantics
