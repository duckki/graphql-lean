import GraphQL.Theories.NormalForm
import Lean.Elab.Tactic.SolveByElim

/-! Structural propagation of the type-name-free uniqueness domain. -/

namespace GraphQL.NormalForm

theorem selectionSetTypenameFree_nil : selectionSetTypenameFree [] := by
  simp [selectionSetTypenameFree]

theorem selectionSetTypenameFree_head {head : Selection} {tail : List Selection}
    (h : selectionSetTypenameFree (head :: tail))
    : selectionTypenameFree head := by
  unfold selectionSetTypenameFree at h
  exact h head (by simp)

theorem selectionSetTypenameFree_cons {head : Selection} {tail : List Selection}
    (hhead : selectionTypenameFree head) (htail : selectionSetTypenameFree tail)
    : selectionSetTypenameFree (head :: tail) := by
  unfold selectionSetTypenameFree at htail ⊢
  intro selection hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact hhead
  · exact htail selection hmem

theorem selectionSetTypenameFree_tail {head : Selection} {tail : List Selection}
    (h : selectionSetTypenameFree (head :: tail))
    : selectionSetTypenameFree tail := by
  unfold selectionSetTypenameFree at h ⊢
  intro selection hmem
  exact h selection (List.mem_cons_of_mem head hmem)

theorem selectionSetTypenameFree_fieldName {selections children : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} (h : selectionSetTypenameFree selections)
    (hmem
      : Selection.field responseName fieldName arguments directives children ∈ selections)
    : fieldName ≠ "__typename" := by
  unfold selectionSetTypenameFree at h
  have hfield := h _ hmem
  rw [selectionTypenameFree] at hfield
  exact hfield.1

theorem selectionSetTypenameFree_fieldChildren {selections children : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} (h : selectionSetTypenameFree selections)
    (hmem
      : Selection.field responseName fieldName arguments directives children ∈ selections)
    : selectionSetTypenameFree children := by
  unfold selectionSetTypenameFree at h
  have hfield := h _ hmem
  rw [selectionTypenameFree] at hfield
  exact hfield.2

theorem selectionSetTypenameFree_fragmentChildren {selections children : List Selection}
    {condition : Option Name} {directives : List DirectiveApplication}
    (h : selectionSetTypenameFree selections)
    (hmem : Selection.inlineFragment condition directives children ∈ selections)
    : selectionSetTypenameFree children := by
  unfold selectionSetTypenameFree at h
  simpa only [selectionTypenameFree] using h _ hmem

theorem selectionSetTypenameFree_append_left {left right : List Selection}
    (h : selectionSetTypenameFree (left ++ right))
    : selectionSetTypenameFree left := by
  unfold selectionSetTypenameFree at h ⊢
  intro selection hmem
  exact h selection (List.mem_append_left right hmem)

theorem selectionSetTypenameFree_append_right {left right : List Selection}
    (h : selectionSetTypenameFree (left ++ right))
    : selectionSetTypenameFree right := by
  unfold selectionSetTypenameFree at h ⊢
  intro selection hmem
  exact h selection (List.mem_append_right left hmem)

theorem selectionSetTypenameFree_append {left right : List Selection}
    (hleft : selectionSetTypenameFree left) (hright : selectionSetTypenameFree right)
    : selectionSetTypenameFree (left ++ right) := by
  unfold selectionSetTypenameFree at hleft hright ⊢
  intro selection hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft selection hmem
  · exact hright selection hmem

theorem selectionSetTypenameFree_field {children : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} (hname : fieldName ≠ "__typename")
    (hchildren : selectionSetTypenameFree children)
    : selectionSetTypenameFree
        [.field responseName fieldName arguments directives children] := by
  unfold selectionSetTypenameFree
  intro selection hmem
  cases List.mem_singleton.mp hmem
  simpa only [selectionTypenameFree] using And.intro hname hchildren

theorem selectionSetTypenameFree_fragment {children : List Selection}
    {condition : Option Name} {directives : List DirectiveApplication}
    (hchildren : selectionSetTypenameFree children)
    : selectionSetTypenameFree [.inlineFragment condition directives children] := by
  unfold selectionSetTypenameFree
  intro selection hmem
  cases List.mem_singleton.mp hmem
  simpa only [selectionTypenameFree] using hchildren

theorem selectionSetTypenameFree_flatten_mem {members : List (List Selection)}
    {selections : List Selection} (hfree : selectionSetTypenameFree members.flatten)
    (hmem : selections ∈ members)
    : selectionSetTypenameFree selections := by
  unfold selectionSetTypenameFree at hfree ⊢
  intro selection hselection
  exact hfree selection (List.mem_flatten.mpr ⟨selections, hmem, hselection⟩)

theorem selectionSetTypenameFree_flatten_cons {head : List Selection}
    {tail : List (List Selection)} (hhead : selectionSetTypenameFree head)
    (htail : selectionSetTypenameFree tail.flatten)
    : selectionSetTypenameFree (head :: tail).flatten := by
  simpa only [List.flatten_cons] using selectionSetTypenameFree_append hhead htail

end GraphQL.NormalForm

-- Default proof arguments in the separation helpers remain explicit logical premises.
-- This tactic derives them from the enclosing selection-set domain and membership facts.
macro "typename_free" : tactic =>
  `(tactic| first
    | assumption
    | solve_by_elim (maxDepth := 4)
        [GraphQL.NormalForm.selectionSetTypenameFree_nil,
         GraphQL.NormalForm.selectionSetTypenameFree_tail,
         GraphQL.NormalForm.selectionSetTypenameFree_flatten_mem,
         GraphQL.NormalForm.selectionSetTypenameFree_flatten_cons,
         GraphQL.NormalForm.selectionSetTypenameFree_fieldName,
         GraphQL.NormalForm.selectionSetTypenameFree_fieldChildren,
         GraphQL.NormalForm.selectionSetTypenameFree_fragmentChildren,
         GraphQL.NormalForm.selectionSetTypenameFree_append_left,
         GraphQL.NormalForm.selectionSetTypenameFree_append_right,
         GraphQL.NormalForm.selectionSetTypenameFree_append,
         GraphQL.NormalForm.selectionSetTypenameFree_field,
         GraphQL.NormalForm.selectionSetTypenameFree_fragment,
         List.mem_cons_self, List.mem_cons_of_mem, List.mem_singleton_self])
