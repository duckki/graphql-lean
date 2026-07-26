import GraphQL.Theories.NormalForm

/-!
Boolean-variable and boolCase facts for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem allBoolCases_nil : allBoolCases ([] : List BoolVar) = [[]] := by
  rfl

theorem BoolCase.lookup?_head_eq (varName : BoolVar) (value : Bool) (rest : BoolCase)
    : BoolCase.lookup? ((varName, value) :: rest) varName = some value := by
  simp [BoolCase.lookup?]

theorem directiveForBit_true (varName : BoolVar)
    : directiveForBit varName true = .include (.variable varName) := by
  simp [directiveForBit]

theorem directiveForBit_false (varName : BoolVar)
    : directiveForBit varName false = .skip (.variable varName) := by
  simp [directiveForBit]

theorem inputValueBooleanVariables_variable (varName : BoolVar)
    : inputValueBooleanVariables (.variable varName) = [varName] := by
  rfl

theorem directivesBooleanVariables_nil : directivesBooleanVariables [] = [] := by
  rfl

theorem boolVariableMem_eq_true_iff (varName : BoolVar)
    : ∀ variables, boolVariableMem varName variables = true ↔ varName ∈ variables
  | [] => by
      simp [boolVariableMem]
  | candidate :: rest => by
      by_cases hsame : candidate = varName
      · subst candidate
        simp [boolVariableMem]
      · have hbeq : (candidate == varName) = false := by
          simp [hsame]
        have hvarNeCandidate : varName ≠ candidate := by
          intro h
          exact hsame h.symm
        simp [boolVariableMem, hbeq,
          boolVariableMem_eq_true_iff varName rest, hvarNeCandidate]

theorem boolVariableMem_eq_false_iff (varName : BoolVar) (variables : List BoolVar)
    : boolVariableMem varName variables = false ↔ varName ∉ variables := by
  cases hmem : boolVariableMem varName variables with
  | false =>
      simp
      intro hin
      have htrue := (boolVariableMem_eq_true_iff varName variables).2 hin
      simp [hmem] at htrue
  | true =>
      simp
      exact (boolVariableMem_eq_true_iff varName variables).1 hmem

theorem dedupBoolVars_nodup : ∀ variables, (dedupBoolVars variables).Nodup
  | [] => by
      simp [dedupBoolVars]
  | varName :: rest => by
      have hrest := dedupBoolVars_nodup rest
      cases hmem : boolVariableMem varName (dedupBoolVars rest) with
      | true =>
          simpa [dedupBoolVars, hmem] using hrest
      | false =>
          have hnotMem :
              varName ∉ dedupBoolVars rest :=
            (boolVariableMem_eq_false_iff varName
              (dedupBoolVars rest)).1 hmem
          simp [dedupBoolVars, hmem, hnotMem, hrest]

theorem mem_dedupBoolVars_iff (varName : BoolVar)
    : ∀ variables, varName ∈ dedupBoolVars variables ↔ varName ∈ variables
  | [] => by
      simp [dedupBoolVars]
  | headVar :: rest => by
      have hrest := mem_dedupBoolVars_iff varName rest
      cases hmem : boolVariableMem headVar (dedupBoolVars rest) with
      | true =>
          have hheadInRestDedup :
              headVar ∈ dedupBoolVars rest :=
            (boolVariableMem_eq_true_iff headVar
              (dedupBoolVars rest)).1 hmem
          have hheadInRest : headVar ∈ rest := by
            exact (mem_dedupBoolVars_iff headVar rest).1
              hheadInRestDedup
          constructor
          · intro hvar
            have hvarRest : varName ∈ dedupBoolVars rest := by
              simpa [dedupBoolVars, hmem] using hvar
            exact List.mem_cons_of_mem headVar (hrest.1 hvarRest)
          · intro hvar
            have hvarRest : varName ∈ dedupBoolVars rest := by
              rcases List.mem_cons.mp hvar with hhead | htail
              · subst varName
                exact hheadInRestDedup
              · exact hrest.2 htail
            simpa [dedupBoolVars, hmem] using hvarRest
      | false =>
          have hheadNotInRestDedup :
              headVar ∉ dedupBoolVars rest :=
            (boolVariableMem_eq_false_iff headVar
              (dedupBoolVars rest)).1 hmem
          have hheadNotInRest : headVar ∉ rest := by
            intro hheadRest
            exact hheadNotInRestDedup
              ((mem_dedupBoolVars_iff headVar rest).2 hheadRest)
          simp [dedupBoolVars, hmem, hrest]

theorem mem_operationBoolVars_of_selectionSet (operation : Operation) (varName : BoolVar)
    : varName ∈ selectionSetBooleanVariables operation.selectionSet
      -> varName ∈ operationBoolVars operation := by
  intro hmem
  exact (mem_dedupBoolVars_iff varName
    (selectionSetBooleanVariables operation.selectionSet)).2 hmem

theorem directivesBooleanVariables_mem_selectionBooleanVariables_field
    (varName : BoolVar)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : varName ∈ directivesBooleanVariables directives
      -> varName
          ∈ selectionBooleanVariables
              (Selection.field responseName fieldName arguments directives
                selectionSet) := by
  intro hmem
  simp [selectionBooleanVariables, hmem]

theorem childSelectionSetBooleanVariables_mem_selectionBooleanVariables_field
    (varName : BoolVar)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : varName ∈ selectionSetBooleanVariables selectionSet
      -> varName
          ∈ selectionBooleanVariables
              (Selection.field responseName fieldName arguments directives
                selectionSet) := by
  intro hmem
  simp [selectionBooleanVariables, hmem]

theorem directivesBooleanVariables_mem_selectionBooleanVariables_inline
    (varName : BoolVar) (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : varName ∈ directivesBooleanVariables directives
      -> varName
          ∈ selectionBooleanVariables
              (Selection.inlineFragment typeCondition directives selectionSet) := by
  intro hmem
  simp [selectionBooleanVariables, hmem]

theorem childSelectionSetBooleanVariables_mem_selectionBooleanVariables_inline
    (varName : BoolVar) (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    : varName ∈ selectionSetBooleanVariables selectionSet
      -> varName
          ∈ selectionBooleanVariables
              (Selection.inlineFragment typeCondition directives selectionSet) := by
  intro hmem
  simp [selectionBooleanVariables, hmem]

theorem selectionBooleanVariables_mem_selectionSetBooleanVariables_head
    (varName : BoolVar) (selection : Selection)
    (rest : List Selection)
    : varName ∈ selectionBooleanVariables selection
      -> varName ∈ selectionSetBooleanVariables (selection :: rest) := by
  intro hmem
  simp [selectionSetBooleanVariables, hmem]

theorem selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
    (varName : BoolVar) (selection : Selection)
    (rest : List Selection)
    : varName ∈ selectionSetBooleanVariables rest
      -> varName ∈ selectionSetBooleanVariables (selection :: rest) := by
  intro hmem
  simp [selectionSetBooleanVariables, hmem]

theorem directivesBooleanVariables_mem_selectionSetBooleanVariables_field_head
    (varName : BoolVar)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : varName ∈ directivesBooleanVariables directives
      -> varName
          ∈ selectionSetBooleanVariables
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hmem
  exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
    varName
    (Selection.field responseName fieldName arguments directives selectionSet)
    rest
    (directivesBooleanVariables_mem_selectionBooleanVariables_field varName
      responseName fieldName arguments directives selectionSet hmem)

theorem directivesBooleanVariables_mem_selectionSetBooleanVariables_inline_head
    (varName : BoolVar) (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : varName ∈ directivesBooleanVariables directives
      -> varName
          ∈ selectionSetBooleanVariables
              (Selection.inlineFragment typeCondition directives selectionSet
                :: rest) := by
  intro hmem
  exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
    varName
    (Selection.inlineFragment typeCondition directives selectionSet)
    rest
    (directivesBooleanVariables_mem_selectionBooleanVariables_inline varName
      typeCondition directives selectionSet hmem)

theorem childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_field_head
    (varName : BoolVar)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : varName ∈ selectionSetBooleanVariables selectionSet
      -> varName
          ∈ selectionSetBooleanVariables
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hmem
  exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
    varName
    (Selection.field responseName fieldName arguments directives selectionSet)
    rest
    (childSelectionSetBooleanVariables_mem_selectionBooleanVariables_field
      varName responseName fieldName arguments directives selectionSet hmem)

theorem childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_inline_head
    (varName : BoolVar) (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : varName ∈ selectionSetBooleanVariables selectionSet
      -> varName
          ∈ selectionSetBooleanVariables
              (Selection.inlineFragment typeCondition directives selectionSet
                :: rest) := by
  intro hmem
  exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
    varName
    (Selection.inlineFragment typeCondition directives selectionSet)
    rest
    (childSelectionSetBooleanVariables_mem_selectionBooleanVariables_inline
      varName typeCondition directives selectionSet hmem)

theorem sourceSelectionSetVariables_field_child
    (operation : Operation)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (∀ varName,
        varName
          ∈ selectionSetBooleanVariables
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest)
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName ∈ selectionSetBooleanVariables selectionSet
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName
    (childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_field_head
      varName responseName fieldName arguments directives selectionSet rest
      hmem)

theorem sourceSelectionSetVariables_inline_child
    (operation : Operation) (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (∀ varName,
        varName
          ∈ selectionSetBooleanVariables
              (Selection.inlineFragment typeCondition directives selectionSet :: rest)
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName ∈ selectionSetBooleanVariables selectionSet
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName
    (childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_inline_head
      varName typeCondition directives selectionSet rest hmem)

theorem sourceSelectionSetVariables_tail
    (operation : Operation) (selection : Selection)
    (rest : List Selection)
    : (∀ varName,
        varName ∈ selectionSetBooleanVariables (selection :: rest)
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName ∈ selectionSetBooleanVariables rest
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName
    (selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
      varName selection rest hmem)

theorem selectionSetBooleanVariables_append (left right : List Selection)
    : selectionSetBooleanVariables (left ++ right)
      = selectionSetBooleanVariables left ++ selectionSetBooleanVariables right := by
  induction left with
  | nil =>
      simp [selectionSetBooleanVariables]
  | cons selection rest ih =>
      simp [selectionSetBooleanVariables, ih, List.append_assoc]

theorem sourceSelectionSetVariables_append_left
    (operation : Operation) (left right : List Selection)
    : (∀ varName,
        varName ∈ selectionSetBooleanVariables (left ++ right)
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName ∈ selectionSetBooleanVariables left
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName (by
    rw [selectionSetBooleanVariables_append]
    exact List.mem_append_left
      (selectionSetBooleanVariables right) hmem)

theorem sourceSelectionSetVariables_append_right
    (operation : Operation) (left right : List Selection)
    : (∀ varName,
        varName ∈ selectionSetBooleanVariables (left ++ right)
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName ∈ selectionSetBooleanVariables right
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName (by
    rw [selectionSetBooleanVariables_append]
    exact List.mem_append_right
      (selectionSetBooleanVariables left) hmem)

theorem selectionSetBooleanVariables_withoutFieldSelectionsWithResponseName_mem
    (schema : Schema) (responseName : Name) (varName : BoolVar)
    : ∀ selectionSet,
        varName
          ∈ selectionSetBooleanVariables
              (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        -> varName ∈ selectionSetBooleanVariables selectionSet
  | [], hmem => by
      simp [withoutFieldSelectionsWithResponseName, selectionSetBooleanVariables] at hmem
  | Selection.field fieldResponseName fieldName arguments directives
      selectionSet :: rest, hmem => by
      cases hresponse : fieldResponseName == responseName
      · have hmem' :
            varName ∈ selectionSetBooleanVariables
              (Selection.field fieldResponseName fieldName arguments
                directives selectionSet
                :: withoutFieldSelectionsWithResponseName schema responseName rest) := by
          simpa [withoutFieldSelectionsWithResponseName, hresponse] using hmem
        simp [selectionSetBooleanVariables, selectionBooleanVariables] at hmem' ⊢
        rcases hmem' with hdirective | hchild | hrest
        · exact Or.inl hdirective
        · exact Or.inr (Or.inl hchild)
        · exact Or.inr (Or.inr
            (selectionSetBooleanVariables_withoutFieldSelectionsWithResponseName_mem
              schema responseName varName rest hrest))
      · have hrest :
            varName ∈ selectionSetBooleanVariables
              (withoutFieldSelectionsWithResponseName schema responseName rest) := by
          simpa [withoutFieldSelectionsWithResponseName, hresponse] using hmem
        exact selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
          varName
          (Selection.field fieldResponseName fieldName arguments directives
            selectionSet)
          rest
          (selectionSetBooleanVariables_withoutFieldSelectionsWithResponseName_mem
            schema responseName varName rest hrest)
  | Selection.inlineFragment typeCondition directives selectionSet :: rest,
      hmem => by
      have hmem' :
          varName ∈ selectionSetBooleanVariables
            (Selection.inlineFragment typeCondition directives
              (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
              :: withoutFieldSelectionsWithResponseName schema responseName rest) := by
        simpa [withoutFieldSelectionsWithResponseName] using hmem
      simp [selectionSetBooleanVariables, selectionBooleanVariables] at hmem' ⊢
      rcases hmem' with hdirective | hchild | hrest
      · exact Or.inl hdirective
      · exact Or.inr (Or.inl
          (selectionSetBooleanVariables_withoutFieldSelectionsWithResponseName_mem
            schema responseName varName selectionSet hchild))
      · exact Or.inr (Or.inr
          (selectionSetBooleanVariables_withoutFieldSelectionsWithResponseName_mem
            schema responseName varName rest hrest))

theorem sourceSelectionSetVariables_withoutFieldSelectionsWithResponseName
    (operation : Operation) (schema : Schema) (responseName : Name)
    (selectionSet : List Selection)
    : (∀ varName,
        varName ∈ selectionSetBooleanVariables selectionSet
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName
            ∈ selectionSetBooleanVariables
                (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName
    (selectionSetBooleanVariables_withoutFieldSelectionsWithResponseName_mem schema
      responseName varName selectionSet hmem)

theorem selectionSubselectionsBooleanVariables_mem_selectionBooleanVariables
    (varName : BoolVar) (selection : Selection)
    : varName ∈ selectionSetBooleanVariables selection.subselections
      -> varName ∈ selectionBooleanVariables selection := by
  intro hmem
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      exact List.mem_append_right (directivesBooleanVariables directives)
        (by simpa [Selection.subselections] using hmem)
  | inlineFragment typeCondition directives selectionSet =>
      exact List.mem_append_right (directivesBooleanVariables directives)
        (by simpa [Selection.subselections] using hmem)

theorem mergeSelectionSetsBooleanVariables_mem_selectionSetBooleanVariables
    (varName : BoolVar)
    : ∀ selectionSet,
        varName ∈ selectionSetBooleanVariables (mergeSelectionSets selectionSet)
        -> varName ∈ selectionSetBooleanVariables selectionSet
  | [] => by
      simp [mergeSelectionSets, selectionSetBooleanVariables]
  | selection :: rest => by
      intro hmem
      have hmem' :
          varName ∈
            selectionSetBooleanVariables selection.subselections
              ++ selectionSetBooleanVariables (mergeSelectionSets rest) := by
        simpa [mergeSelectionSets, selectionSetBooleanVariables_append]
          using hmem
      rcases List.mem_append.mp hmem' with hhead | htail
      · exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
          varName selection rest
          (selectionSubselectionsBooleanVariables_mem_selectionBooleanVariables
            varName selection hhead)
      · exact selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
          varName selection rest
          (mergeSelectionSetsBooleanVariables_mem_selectionSetBooleanVariables
            varName rest htail)

theorem fieldSelectionsWithResponseNameInScope_variables_mem
    (schema : Schema) (parentType responseName : Name)
    (varName : BoolVar)
    : ∀ selectionSet,
        varName
          ∈ selectionSetBooleanVariables
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet)
        -> varName ∈ selectionSetBooleanVariables selectionSet := by
  intro selectionSet
  induction selectionSet using
    fieldSelectionsWithResponseNameInScope.induct schema parentType responseName with
  | case1 =>
      simp [fieldSelectionsWithResponseNameInScope, selectionSetBooleanVariables]
  | case2 rest selectionResponseName fieldName arguments directives
      fieldSelectionSet hname hrest =>
      intro hmem
      have hmem' :
          varName ∈
              selectionBooleanVariables
                (Selection.field selectionResponseName fieldName arguments
                  directives fieldSelectionSet)
            ∨ varName ∈ selectionSetBooleanVariables
                (fieldSelectionsWithResponseNameInScope schema parentType responseName
                  rest) := by
        simpa [fieldSelectionsWithResponseNameInScope, hname,
          selectionSetBooleanVariables] using hmem
      rcases hmem' with hhead | htail
      · exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
          varName
          (Selection.field selectionResponseName fieldName arguments directives
            fieldSelectionSet)
          rest hhead
      · exact selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
          varName
          (Selection.field selectionResponseName fieldName arguments directives
            fieldSelectionSet)
          rest (hrest htail)
  | case3 rest selectionResponseName fieldName arguments directives
      fieldSelectionSet hname hrest =>
      intro hmem
      have htail :
          varName ∈ selectionSetBooleanVariables
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              rest) := by
        simpa [fieldSelectionsWithResponseNameInScope, hname,
          selectionSetBooleanVariables] using hmem
      exact selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
        varName
        (Selection.field selectionResponseName fieldName arguments directives
          fieldSelectionSet)
        rest (hrest htail)
  | case4 rest directives fragmentSelectionSet hfragment hrest =>
      intro hmem
      have hmem' :
          varName ∈ selectionSetBooleanVariables
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                fragmentSelectionSet)
            ∨ varName ∈ selectionSetBooleanVariables
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest) := by
        have hmemAppend :
            varName ∈
              selectionSetBooleanVariables
                  (fieldSelectionsWithResponseNameInScope schema parentType responseName
                    fragmentSelectionSet)
                ++ selectionSetBooleanVariables
                  (fieldSelectionsWithResponseNameInScope schema parentType responseName
                    rest) := by
          simpa [fieldSelectionsWithResponseNameInScope,
            selectionSetBooleanVariables_append] using hmem
        exact List.mem_append.mp hmemAppend
      rcases hmem' with hfragmentVar | htail
      · exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
          varName
          (Selection.inlineFragment none directives fragmentSelectionSet)
          rest
          (childSelectionSetBooleanVariables_mem_selectionBooleanVariables_inline
            varName none directives fragmentSelectionSet
            (hfragment hfragmentVar))
      · exact selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
          varName
          (Selection.inlineFragment none directives fragmentSelectionSet)
          rest (hrest htail)
  | case5 rest typeCondition directives fragmentSelectionSet hoverlap hrest
      hfragment =>
      intro hmem
      have hmem' :
          varName ∈ selectionSetBooleanVariables
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                fragmentSelectionSet)
            ∨ varName ∈ selectionSetBooleanVariables
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest) := by
        have hmemAppend :
            varName ∈
              selectionSetBooleanVariables
                  (fieldSelectionsWithResponseNameInScope schema parentType responseName
                    fragmentSelectionSet)
                ++ selectionSetBooleanVariables
                  (fieldSelectionsWithResponseNameInScope schema parentType responseName
                    rest) := by
          simpa [fieldSelectionsWithResponseNameInScope, hoverlap,
            selectionSetBooleanVariables_append] using hmem
        exact List.mem_append.mp hmemAppend
      rcases hmem' with hfragmentVar | htail
      · exact selectionBooleanVariables_mem_selectionSetBooleanVariables_head
          varName
          (Selection.inlineFragment (some typeCondition) directives
            fragmentSelectionSet)
          rest
          (childSelectionSetBooleanVariables_mem_selectionBooleanVariables_inline
            varName (some typeCondition) directives fragmentSelectionSet
            (hfragment hfragmentVar))
      · exact selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
          varName
          (Selection.inlineFragment (some typeCondition) directives
            fragmentSelectionSet)
          rest (hrest htail)
  | case6 rest typeCondition directives fragmentSelectionSet hoverlap hrest =>
      intro hmem
      have htail :
          varName ∈ selectionSetBooleanVariables
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              rest) := by
        simpa [fieldSelectionsWithResponseNameInScope, hoverlap,
          selectionSetBooleanVariables] using hmem
      exact selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
        varName
        (Selection.inlineFragment (some typeCondition) directives
          fragmentSelectionSet)
        rest (hrest htail)

theorem mergeSelectionSets_fieldSelectionsWithResponseNameInScope_variables_mem
    (schema : Schema) (parentType responseName : Name)
    (varName : BoolVar) (selectionSet : List Selection)
    : varName
        ∈ selectionSetBooleanVariables
            (mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet))
      -> varName ∈ selectionSetBooleanVariables selectionSet := by
  intro hmem
  exact fieldSelectionsWithResponseNameInScope_variables_mem schema parentType
    responseName varName selectionSet
    (mergeSelectionSetsBooleanVariables_mem_selectionSetBooleanVariables
      varName
      (fieldSelectionsWithResponseNameInScope schema parentType responseName
        selectionSet)
      hmem)

theorem sourceSelectionSetVariables_field_merged
    (operation : Operation)
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (∀ varName,
        varName
          ∈ selectionSetBooleanVariables
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest)
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName
            ∈ selectionSetBooleanVariables
                (selectionSet
                  ++ mergeSelectionSets
                      (fieldSelectionsWithResponseNameInScope schema parentType
                        responseName rest))
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  have hmem' :
      varName ∈ selectionSetBooleanVariables selectionSet
        ∨ varName ∈ selectionSetBooleanVariables
          (mergeSelectionSets
            (fieldSelectionsWithResponseNameInScope schema parentType responseName
              rest)) := by
    have happend :
        varName ∈ selectionSetBooleanVariables selectionSet
          ++ selectionSetBooleanVariables
            (mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest)) := by
      simpa [selectionSetBooleanVariables_append] using hmem
    exact List.mem_append.mp happend
  rcases hmem' with hchild | hmerged
  · exact sourceSelectionSetVariables_field_child operation responseName
      fieldName arguments directives selectionSet rest hsourceVars varName
      hchild
  · exact sourceSelectionSetVariables_tail operation
      (Selection.field responseName fieldName arguments directives
        selectionSet)
      rest hsourceVars varName
      (mergeSelectionSets_fieldSelectionsWithResponseNameInScope_variables_mem schema
        parentType responseName varName rest hmerged)

theorem BoolCase.lookup?_mem_of_allBoolCases
    : ∀ {variables boolCase varName},
        boolCase ∈ allBoolCases variables
        -> varName ∈ variables
        -> ∃ value, BoolCase.lookup? boolCase varName = some value
  | [], boolCase, varName, hcase, hvar => by
      cases hvar
  | headVar :: restVars, boolCase, varName, hcase,
      hvar => by
      simp [allBoolCases] at hcase
      rcases hcase with hcase | hcase
      · rcases hcase with ⟨restCase, hrestCase,
          hcaseEq⟩
        subst boolCase
        rcases List.mem_cons.mp hvar with hhead | htail
        · subst headVar
          exact ⟨false, by simp [BoolCase.lookup?]⟩
        · have htailValue :=
            BoolCase.lookup?_mem_of_allBoolCases hrestCase htail
          rcases htailValue with ⟨value, hvalue⟩
          by_cases hsame : headVar = varName
          · subst headVar
            exact ⟨false, by simp [BoolCase.lookup?]⟩
          · exact ⟨value, by simp [BoolCase.lookup?, hsame, hvalue]⟩
      · rcases hcase with ⟨restCase, hrestCase,
          hcaseEq⟩
        subst boolCase
        rcases List.mem_cons.mp hvar with hhead | htail
        · subst headVar
          exact ⟨true, by simp [BoolCase.lookup?]⟩
        · have htailValue :=
            BoolCase.lookup?_mem_of_allBoolCases hrestCase htail
          rcases htailValue with ⟨value, hvalue⟩
          by_cases hsame : headVar = varName
          · subst headVar
            exact ⟨true, by simp [BoolCase.lookup?]⟩
          · exact ⟨value, by simp [BoolCase.lookup?, hsame, hvalue]⟩

theorem allBoolCases_complete
    : ∀ {variables} {f : BoolVar -> Option Bool},
        (∀ varName, varName ∈ variables -> ∃ value, f varName = some value)
        -> ∃ boolCase,
            boolCase ∈ allBoolCases variables
            ∧ ∀ varName,
                varName ∈ variables -> BoolCase.lookup? boolCase varName = f varName
  | [], f, _hcomplete => by
      exact ⟨[], by simp [allBoolCases]⟩
  | headVar :: restVars, f, hcomplete => by
      have hheadValue := hcomplete headVar (by simp)
      rcases hheadValue with ⟨headValue, hheadValue⟩
      have hrestComplete :
          ∀ varName, varName ∈ restVars ->
            ∃ value, f varName = some value := by
        intro varName hmem
        exact hcomplete varName (List.mem_cons_of_mem headVar hmem)
      rcases allBoolCases_complete hrestComplete with
        ⟨restCase, hrestMem, hrestEq⟩
      cases headValue with
      | false =>
          refine ⟨(headVar, false) :: restCase, ?_, ?_⟩
          · simp [allBoolCases]
            exact hrestMem
          · intro varName hmem
            rcases List.mem_cons.mp hmem with hhead | htail
            · subst varName
              simp [BoolCase.lookup?, hheadValue]
            · by_cases hsame : headVar = varName
              · subst headVar
                simp [BoolCase.lookup?, hheadValue]
              · simp [BoolCase.lookup?, hsame, hrestEq varName htail]
      | true =>
          refine ⟨(headVar, true) :: restCase, ?_, ?_⟩
          · simp [allBoolCases]
            exact hrestMem
          · intro varName hmem
            rcases List.mem_cons.mp hmem with hhead | htail
            · subst varName
              simp [BoolCase.lookup?, hheadValue]
            · by_cases hsame : headVar = varName
              · subst headVar
                simp [BoolCase.lookup?, hheadValue]
              · simp [BoolCase.lookup?, hsame, hrestEq varName htail]

theorem boolCase_pair_variable_mem_of_allBoolCases
    : ∀ {variables boolCase varName value},
        boolCase ∈ allBoolCases variables
        -> (varName, value) ∈ boolCase
        -> varName ∈ variables
  | [], boolCase, varName, value, hcase, hpair => by
      simp [allBoolCases] at hcase
      subst boolCase
      cases hpair
  | headVar :: restVars, boolCase, varName, value, hcase,
      hpair => by
      simp [allBoolCases] at hcase
      rcases hcase with hcase | hcase
      · rcases hcase with ⟨restCase, hrestCase,
          hcaseEq⟩
        subst boolCase
        simp at hpair
        rcases hpair with hhead | htail
        · simp [hhead.1]
        · exact List.mem_cons_of_mem headVar
            (boolCase_pair_variable_mem_of_allBoolCases
              hrestCase htail)
      · rcases hcase with ⟨restCase, hrestCase,
          hcaseEq⟩
        subst boolCase
        simp at hpair
        rcases hpair with hhead | htail
        · simp [hhead.1]
        · exact List.mem_cons_of_mem headVar
            (boolCase_pair_variable_mem_of_allBoolCases
              hrestCase htail)

theorem BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
    : ∀ {variables boolCase varName value},
        variables.Nodup
        -> boolCase ∈ allBoolCases variables
        -> (varName, value) ∈ boolCase
        -> BoolCase.lookup? boolCase varName = some value
  | [], boolCase, varName, value, _hnodup, hcase, hpair => by
      simp [allBoolCases] at hcase
      subst boolCase
      cases hpair
  | headVar :: restVars, boolCase, varName, value, hnodup, hcase,
      hpair => by
      simp [allBoolCases] at hcase
      have hnodupParts := List.nodup_cons.mp hnodup
      have hheadNotMem : headVar ∉ restVars := hnodupParts.1
      have hrestNodup : restVars.Nodup := hnodupParts.2
      rcases hcase with hcase | hcase
      · rcases hcase with ⟨restCase, hrestCase,
          hcaseEq⟩
        subst boolCase
        simp at hpair
        rcases hpair with hhead | htail
        · simp [BoolCase.lookup?, hhead.1, hhead.2]
        · have hvarInRest :
              varName ∈ restVars :=
            boolCase_pair_variable_mem_of_allBoolCases
              hrestCase htail
          have hneq : headVar ≠ varName := by
            intro heq
            subst varName
            exact hheadNotMem hvarInRest
          have htailValue :=
            BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
              hrestNodup hrestCase htail
          simp [BoolCase.lookup?, hneq, htailValue]
      · rcases hcase with ⟨restCase, hrestCase,
          hcaseEq⟩
        subst boolCase
        simp at hpair
        rcases hpair with hhead | htail
        · simp [BoolCase.lookup?, hhead.1, hhead.2]
        · have hvarInRest :
              varName ∈ restVars :=
            boolCase_pair_variable_mem_of_allBoolCases
              hrestCase htail
          have hneq : headVar ≠ varName := by
            intro heq
            subst varName
            exact hheadNotMem hvarInRest
          have htailValue :=
            BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
              hrestNodup hrestCase htail
          simp [BoolCase.lookup?, hneq, htailValue]

theorem allBoolCases_nodup
    : ∀ {variables : List BoolVar}, variables.Nodup -> (allBoolCases variables).Nodup
  | [], _hnodup => by
      simp [allBoolCases]
  | headVar :: restVars, hnodup => by
      have hnodupParts := List.nodup_cons.mp hnodup
      have hheadNotMem : headVar ∉ restVars := hnodupParts.1
      have hrestNodup : restVars.Nodup := hnodupParts.2
      have hrestCases := allBoolCases_nodup hrestNodup
      have hfalseNodup :
          ((allBoolCases restVars).map
            (fun boolCase => (headVar, false) :: boolCase)).Nodup := by
        exact List.Pairwise.map
          (fun boolCase => (headVar, false) :: boolCase)
          (by
            intro left right hne heq
            apply hne
            injection heq)
          hrestCases
      have htrueNodup :
          ((allBoolCases restVars).map
            (fun boolCase => (headVar, true) :: boolCase)).Nodup := by
        exact List.Pairwise.map
          (fun boolCase => (headVar, true) :: boolCase)
          (by
            intro left right hne heq
            apply hne
            injection heq)
          hrestCases
      have hdisjoint :
          ∀ boolCase,
            boolCase ∈
                (allBoolCases restVars).map
                  (fun boolCase => (headVar, false) :: boolCase) ->
            boolCase ∈
                (allBoolCases restVars).map
                  (fun boolCase => (headVar, true) :: boolCase) ->
              False := by
        intro boolCase hfalse htrue
        rcases List.mem_map.mp hfalse with
          ⟨falseRest, _hfalseRest, hfalseEq⟩
        rcases List.mem_map.mp htrue with
          ⟨trueRest, _htrueRest, htrueEq⟩
        subst boolCase
        simp at htrueEq
      simp [allBoolCases]
      exact List.nodup_append.mpr ⟨hfalseNodup, htrueNodup,
        by
          intro left hleft right hright heq
          subst right
          exact hdisjoint left hleft hright⟩

theorem boolCaseList_split_of_mem_nodup
    : ∀ {boolCases : List BoolCase} {boolCase : BoolCase},
        boolCases.Nodup
        -> boolCase ∈ boolCases
        -> ∃ before after,
            boolCases = before ++ boolCase :: after
            ∧ (∀ candidate, candidate ∈ before -> candidate ≠ boolCase)
            ∧ (∀ candidate, candidate ∈ after -> candidate ≠ boolCase)
  | [], boolCase, _hnodup, hmem => by
      cases hmem
  | head :: rest, boolCase, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      have hheadNotMem : head ∉ rest := hparts.1
      have hrestNodup : rest.Nodup := hparts.2
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst boolCase
        refine ⟨[], rest, by simp, ?_, ?_⟩
        · intro candidate hcandidate
          cases hcandidate
        · intro candidate hcandidate heq
          subst candidate
          exact hheadNotMem hcandidate
      · rcases boolCaseList_split_of_mem_nodup hrestNodup htail with
          ⟨before, after, hsplit, hbefore, hafter⟩
        refine ⟨head :: before, after, ?_, ?_, hafter⟩
        · simp [hsplit]
        · intro candidate hcandidate
          rcases List.mem_cons.mp hcandidate with hcandidate | hcandidate
          · subst candidate
            intro heq
            subst boolCase
            exact hheadNotMem htail
          · exact hbefore candidate hcandidate

theorem allBoolCases_split_case {variables : List BoolVar} {boolCase : BoolCase}
    : variables.Nodup
      -> boolCase ∈ allBoolCases variables
      -> ∃ before after,
          allBoolCases variables = before ++ boolCase :: after
          ∧ (∀ candidate, candidate ∈ before -> candidate ≠ boolCase)
          ∧ (∀ candidate, candidate ∈ after -> candidate ≠ boolCase) := by
  intro hnodup hmem
  exact boolCaseList_split_of_mem_nodup
    (allBoolCases_nodup hnodup) hmem

end CompleteNormalization

end NormalForm

end GraphQL
