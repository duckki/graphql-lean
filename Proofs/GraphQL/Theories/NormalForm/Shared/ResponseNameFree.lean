import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes

/-!
Response-name-free structural facts shared by NormalForm proof modules.
-/

namespace GraphQL

namespace NormalForm

mutual
  -- Helper predicate: one selection cannot contribute a field with the given response
  -- name in the current type scope.
  def selectionResponseNameFree (schema : Schema) (parentType responseName : Name)
      : Selection -> Prop
    | .field selectionResponseName _fieldName _arguments _directives _selectionSet =>
        selectionResponseName ≠ responseName
    | .inlineFragment none _directives selectionSet =>
        selectionSetResponseNameFree schema parentType responseName selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        schema.typesOverlapBool parentType typeCondition = true
        -> selectionSetResponseNameFree schema parentType responseName selectionSet

  def selectionSetResponseNameFree (schema : Schema)
      (parentType responseName : Name)
      (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> selectionResponseNameFree schema parentType responseName selection
end

theorem selectionSetResponseNameFree_nil (schema : Schema)
    (parentType responseName : Name)
    : selectionSetResponseNameFree schema parentType responseName [] := by
  unfold selectionSetResponseNameFree
  intro selection hselection
  simp at hselection

theorem selectionSetResponseNameFree_cons {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection}
    : selectionResponseNameFree schema parentType responseName selection
      -> selectionSetResponseNameFree schema parentType responseName selectionSet
      -> selectionSetResponseNameFree schema parentType responseName
          (selection :: selectionSet) := by
  unfold selectionSetResponseNameFree
  intro hselection hselectionSet candidate hcandidate
  cases hcandidate with
  | head =>
      exact hselection
  | tail _ htail =>
      exact hselectionSet candidate htail

theorem selectionSetResponseNameFree_head {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection}
    : selectionSetResponseNameFree schema parentType responseName
        (selection :: selectionSet)
      -> selectionResponseNameFree schema parentType responseName selection := by
  unfold selectionSetResponseNameFree
  intro hfree
  exact hfree selection (by simp)

theorem selectionSetResponseNameFree_tail {schema : Schema}
    {parentType responseName : Name} {selection : Selection}
    {selectionSet : List Selection}
    : selectionSetResponseNameFree schema parentType responseName
        (selection :: selectionSet)
      -> selectionSetResponseNameFree schema parentType responseName selectionSet := by
  unfold selectionSetResponseNameFree
  intro hfree candidate hcandidate
  exact hfree candidate (List.mem_cons_of_mem selection hcandidate)

theorem selectionSetResponseNameFree_append {schema : Schema}
    {parentType responseName : Name} {left right : List Selection}
    : selectionSetResponseNameFree schema parentType responseName left
      -> selectionSetResponseNameFree schema parentType responseName right
      -> selectionSetResponseNameFree schema parentType responseName (left ++ right) := by
  unfold selectionSetResponseNameFree
  intro hleft hright selection hselection
  rcases List.mem_append.mp hselection with hselection | hselection
  · exact hleft selection hselection
  · exact hright selection hselection

theorem withoutFieldSelectionsWithResponseName_responseNameFree (schema : Schema)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetResponseNameFree schema parentType responseName
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
  | [] => by
      simpa [withoutFieldSelectionsWithResponseName] using
        selectionSetResponseNameFree_nil schema parentType responseName
  | selection :: rest => by
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == responseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            exact withoutFieldSelectionsWithResponseName_responseNameFree schema
              parentType responseName rest
          · have hfalse : (fieldResponseName == responseName) = false := by
              cases hmatch : fieldResponseName == responseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse]
            apply selectionSetResponseNameFree_cons
            · simp [selectionResponseNameFree]
              intro heq
              subst fieldResponseName
              simp at hfalse
            · exact withoutFieldSelectionsWithResponseName_responseNameFree schema
                parentType responseName rest
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldSelectionsWithResponseName]
          apply selectionSetResponseNameFree_cons
          · cases typeCondition with
            | none =>
                simpa [selectionResponseNameFree] using
                  withoutFieldSelectionsWithResponseName_responseNameFree schema
                    parentType responseName selectionSet
            | some typeCondition =>
                simp [selectionResponseNameFree]
                intro _hoverlap
                exact withoutFieldSelectionsWithResponseName_responseNameFree schema
                  parentType responseName selectionSet
          · exact withoutFieldSelectionsWithResponseName_responseNameFree schema
              parentType responseName rest

theorem withoutFieldSelectionsWithResponseName_preserves_responseNameFree
    (schema : Schema) (removedResponseName : Name)
    (parentType responseName : Name)
    : ∀ selectionSet,
        selectionSetResponseNameFree schema parentType responseName selectionSet
        -> selectionSetResponseNameFree schema parentType responseName
            (withoutFieldSelectionsWithResponseName schema removedResponseName
              selectionSet)
  | [], hfree => by
      simpa [withoutFieldSelectionsWithResponseName] using hfree
  | selection :: rest, hfree => by
      have hselection := selectionSetResponseNameFree_head hfree
      have hrest := selectionSetResponseNameFree_tail hfree
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          by_cases hname : (fieldResponseName == removedResponseName) = true
          · simp [withoutFieldSelectionsWithResponseName, hname]
            exact withoutFieldSelectionsWithResponseName_preserves_responseNameFree
              schema removedResponseName parentType responseName rest hrest
          · have hfalse : (fieldResponseName == removedResponseName) = false := by
              cases hmatch : fieldResponseName == removedResponseName
              · rfl
              · contradiction
            simp [withoutFieldSelectionsWithResponseName, hfalse]
            exact selectionSetResponseNameFree_cons hselection
              (withoutFieldSelectionsWithResponseName_preserves_responseNameFree
                schema removedResponseName parentType responseName rest hrest)
      | inlineFragment typeCondition directives selectionSet =>
          simp [withoutFieldSelectionsWithResponseName]
          apply selectionSetResponseNameFree_cons
          · cases typeCondition with
            | none =>
                have hselectionSet :
                    selectionSetResponseNameFree schema parentType responseName
                      selectionSet := by
                  simpa [selectionResponseNameFree] using hselection
                simpa [selectionResponseNameFree] using
                  withoutFieldSelectionsWithResponseName_preserves_responseNameFree
                    schema removedResponseName parentType responseName
                    selectionSet hselectionSet
            | some typeCondition =>
                have hselectionSet :
                    schema.typesOverlapBool parentType typeCondition = true ->
                      selectionSetResponseNameFree schema parentType responseName
                        selectionSet := by
                  simpa [selectionResponseNameFree] using hselection
                simp [selectionResponseNameFree]
                intro hoverlap
                exact withoutFieldSelectionsWithResponseName_preserves_responseNameFree
                  schema removedResponseName parentType responseName
                  selectionSet (hselectionSet hoverlap)
          · exact withoutFieldSelectionsWithResponseName_preserves_responseNameFree
              schema removedResponseName parentType responseName rest hrest

end NormalForm

end GraphQL
