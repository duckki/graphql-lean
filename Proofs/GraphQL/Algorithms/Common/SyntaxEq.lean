import GraphQL.Algorithms.Common

/-!
Reflexivity facts for common executable syntax equality helpers.
-/

namespace GraphQL

namespace Algorithms

mutual
  theorem inputValueEqBool_self
      : ∀ value : InputValue, inputValueEqBool value value = true
    | .null => rfl
    | .int value => by
        simp [inputValueEqBool]
    | .float value => by
        simp [inputValueEqBool]
    | .string value => by
        simp [inputValueEqBool]
    | .boolean value => by
        simp [inputValueEqBool]
    | .enum value => by
        simp [inputValueEqBool]
    | .list values => by
        simp [inputValueEqBool, inputValueListEqBool_self values]
    | .object fields => by
        simp [inputValueEqBool, inputObjectFieldsEqBool_self fields]
    | .variable name => by
        simp [inputValueEqBool]

  theorem inputValueListEqBool_self
      : ∀ values : List InputValue, inputValueListEqBool values values = true
    | [] => rfl
    | value :: values => by
        simp [inputValueListEqBool, inputValueEqBool_self value,
          inputValueListEqBool_self values]

  theorem inputObjectFieldsEqBool_self
      : ∀ fields : List (Name × InputValue), inputObjectFieldsEqBool fields fields = true
    | [] => rfl
    | (name, value) :: fields => by
        simp [inputObjectFieldsEqBool, inputValueEqBool_self value,
          inputObjectFieldsEqBool_self fields]
end

theorem argumentEqBool_self (argument : Argument)
    : argumentEqBool argument argument = true := by
  cases argument with
  | mk name value =>
      simp [argumentEqBool, inputValueEqBool_self]

theorem argumentListEqBool_self
    : ∀ arguments : List Argument, argumentListEqBool arguments arguments = true
  | [] => rfl
  | argument :: arguments => by
      simp [argumentListEqBool, argumentEqBool_self,
        argumentListEqBool_self arguments]

mutual
  theorem inputValueEqBool_eq
      : ∀ {left right : InputValue}, inputValueEqBool left right = true -> left = right
    | .null, .null, _h => rfl
    | .int left, .int right, h => by
        simp [inputValueEqBool] at h
        exact congrArg InputValue.int h
    | .float left, .float right, h => by
        simp [inputValueEqBool] at h
        exact congrArg InputValue.float h
    | .string left, .string right, h => by
        simp [inputValueEqBool] at h
        exact congrArg InputValue.string h
    | .boolean left, .boolean right, h => by
        simp [inputValueEqBool] at h
        exact congrArg InputValue.boolean h
    | .enum left, .enum right, h => by
        simp [inputValueEqBool] at h
        exact congrArg InputValue.enum h
    | .list left, .list right, h =>
        congrArg InputValue.list (inputValueListEqBool_eq h)
    | .object left, .object right, h =>
        congrArg InputValue.object (inputObjectFieldsEqBool_eq h)
    | .variable left, .variable right, h => by
        simp [inputValueEqBool] at h
        exact congrArg InputValue.variable h
    | .null, .int _, h => by simp [inputValueEqBool] at h
    | .null, .float _, h => by simp [inputValueEqBool] at h
    | .null, .string _, h => by simp [inputValueEqBool] at h
    | .null, .boolean _, h => by simp [inputValueEqBool] at h
    | .null, .enum _, h => by simp [inputValueEqBool] at h
    | .null, .list _, h => by simp [inputValueEqBool] at h
    | .null, .object _, h => by simp [inputValueEqBool] at h
    | .null, .variable _, h => by simp [inputValueEqBool] at h
    | .int _, .null, h => by simp [inputValueEqBool] at h
    | .int _, .float _, h => by simp [inputValueEqBool] at h
    | .int _, .string _, h => by simp [inputValueEqBool] at h
    | .int _, .boolean _, h => by simp [inputValueEqBool] at h
    | .int _, .enum _, h => by simp [inputValueEqBool] at h
    | .int _, .list _, h => by simp [inputValueEqBool] at h
    | .int _, .object _, h => by simp [inputValueEqBool] at h
    | .int _, .variable _, h => by simp [inputValueEqBool] at h
    | .float _, .null, h => by simp [inputValueEqBool] at h
    | .float _, .int _, h => by simp [inputValueEqBool] at h
    | .float _, .string _, h => by simp [inputValueEqBool] at h
    | .float _, .boolean _, h => by simp [inputValueEqBool] at h
    | .float _, .enum _, h => by simp [inputValueEqBool] at h
    | .float _, .list _, h => by simp [inputValueEqBool] at h
    | .float _, .object _, h => by simp [inputValueEqBool] at h
    | .float _, .variable _, h => by simp [inputValueEqBool] at h
    | .string _, .null, h => by simp [inputValueEqBool] at h
    | .string _, .int _, h => by simp [inputValueEqBool] at h
    | .string _, .float _, h => by simp [inputValueEqBool] at h
    | .string _, .boolean _, h => by simp [inputValueEqBool] at h
    | .string _, .enum _, h => by simp [inputValueEqBool] at h
    | .string _, .list _, h => by simp [inputValueEqBool] at h
    | .string _, .object _, h => by simp [inputValueEqBool] at h
    | .string _, .variable _, h => by simp [inputValueEqBool] at h
    | .boolean _, .null, h => by simp [inputValueEqBool] at h
    | .boolean _, .int _, h => by simp [inputValueEqBool] at h
    | .boolean _, .float _, h => by simp [inputValueEqBool] at h
    | .boolean _, .string _, h => by simp [inputValueEqBool] at h
    | .boolean _, .enum _, h => by simp [inputValueEqBool] at h
    | .boolean _, .list _, h => by simp [inputValueEqBool] at h
    | .boolean _, .object _, h => by simp [inputValueEqBool] at h
    | .boolean _, .variable _, h => by simp [inputValueEqBool] at h
    | .enum _, .null, h => by simp [inputValueEqBool] at h
    | .enum _, .int _, h => by simp [inputValueEqBool] at h
    | .enum _, .float _, h => by simp [inputValueEqBool] at h
    | .enum _, .string _, h => by simp [inputValueEqBool] at h
    | .enum _, .boolean _, h => by simp [inputValueEqBool] at h
    | .enum _, .list _, h => by simp [inputValueEqBool] at h
    | .enum _, .object _, h => by simp [inputValueEqBool] at h
    | .enum _, .variable _, h => by simp [inputValueEqBool] at h
    | .list _, .null, h => by simp [inputValueEqBool] at h
    | .list _, .int _, h => by simp [inputValueEqBool] at h
    | .list _, .float _, h => by simp [inputValueEqBool] at h
    | .list _, .string _, h => by simp [inputValueEqBool] at h
    | .list _, .boolean _, h => by simp [inputValueEqBool] at h
    | .list _, .enum _, h => by simp [inputValueEqBool] at h
    | .list _, .object _, h => by simp [inputValueEqBool] at h
    | .list _, .variable _, h => by simp [inputValueEqBool] at h
    | .object _, .null, h => by simp [inputValueEqBool] at h
    | .object _, .int _, h => by simp [inputValueEqBool] at h
    | .object _, .float _, h => by simp [inputValueEqBool] at h
    | .object _, .string _, h => by simp [inputValueEqBool] at h
    | .object _, .boolean _, h => by simp [inputValueEqBool] at h
    | .object _, .enum _, h => by simp [inputValueEqBool] at h
    | .object _, .list _, h => by simp [inputValueEqBool] at h
    | .object _, .variable _, h => by simp [inputValueEqBool] at h
    | .variable _, .null, h => by simp [inputValueEqBool] at h
    | .variable _, .int _, h => by simp [inputValueEqBool] at h
    | .variable _, .float _, h => by simp [inputValueEqBool] at h
    | .variable _, .string _, h => by simp [inputValueEqBool] at h
    | .variable _, .boolean _, h => by simp [inputValueEqBool] at h
    | .variable _, .enum _, h => by simp [inputValueEqBool] at h
    | .variable _, .list _, h => by simp [inputValueEqBool] at h
    | .variable _, .object _, h => by simp [inputValueEqBool] at h

  theorem inputValueListEqBool_eq
      : ∀ {left right : List InputValue},
          inputValueListEqBool left right = true -> left = right
    | [], [], _h => rfl
    | left :: lefts, right :: rights, h => by
        simp [inputValueListEqBool] at h
        rcases h with ⟨hhead, htail⟩
        cases inputValueEqBool_eq hhead
        cases inputValueListEqBool_eq htail
        rfl
    | [], _ :: _, h => by simp [inputValueListEqBool] at h
    | _ :: _, [], h => by simp [inputValueListEqBool] at h

  theorem inputObjectFieldsEqBool_eq
      : ∀ {left right : List (Name × InputValue)},
          inputObjectFieldsEqBool left right = true -> left = right
    | [], [], _h => rfl
    | (leftName, leftValue) :: lefts,
      (rightName, rightValue) :: rights, h => by
        cases hname : (leftName == rightName) <;>
          simp [inputObjectFieldsEqBool, hname] at h
        cases hvalue : inputValueEqBool leftValue rightValue <;>
          simp [hvalue] at h
        have hnameEq : leftName = rightName := beq_iff_eq.mp hname
        have hvalueEq : leftValue = rightValue := inputValueEqBool_eq hvalue
        have htailEq : lefts = rights := inputObjectFieldsEqBool_eq h
        cases hnameEq
        cases hvalueEq
        cases htailEq
        rfl
    | [], _ :: _, h => by simp [inputObjectFieldsEqBool] at h
    | _ :: _, [], h => by simp [inputObjectFieldsEqBool] at h
end

theorem argumentEqBool_eq {left right : Argument}
    : argumentEqBool left right = true -> left = right := by
  cases left with
  | mk leftName leftValue =>
      cases right with
      | mk rightName rightValue =>
          intro h
          simp [argumentEqBool] at h
          rcases h with ⟨hname, hvalue⟩
          have hvalueEq : leftValue = rightValue := inputValueEqBool_eq hvalue
          cases hname
          cases hvalueEq
          rfl

theorem argumentListEqBool_eq
    : ∀ {left right : List Argument}, argumentListEqBool left right = true -> left = right
  | [], [], _h => rfl
  | left :: lefts, right :: rights, h => by
      simp [argumentListEqBool] at h
      rcases h with ⟨hhead, htail⟩
      cases argumentEqBool_eq hhead
      cases argumentListEqBool_eq htail
      rfl
  | [], _ :: _, h => by simp [argumentListEqBool] at h
  | _ :: _, [], h => by simp [argumentListEqBool] at h

theorem directiveEqBool_self (directive : DirectiveApplication)
    : directiveEqBool directive directive = true := by
  cases directive with
  | skip ifArgument =>
      simp [directiveEqBool, inputValueEqBool_self]
  | «include» ifArgument =>
      simp [directiveEqBool, inputValueEqBool_self]

theorem directiveListEqBool_self
    : ∀ directives : List DirectiveApplication,
        directiveListEqBool directives directives = true
  | [] => rfl
  | directive :: directives => by
      simp [directiveListEqBool, directiveEqBool_self,
        directiveListEqBool_self directives]

theorem directiveEqBool_eq {left right : DirectiveApplication}
    : directiveEqBool left right = true -> left = right := by
  cases left with
  | skip leftValue =>
      cases right with
      | skip rightValue =>
          intro h
          have hvalue : leftValue = rightValue := inputValueEqBool_eq h
          cases hvalue
          rfl
      | «include» rightValue =>
          intro h
          simp [directiveEqBool] at h
  | «include» leftValue =>
      cases right with
      | skip rightValue =>
          intro h
          simp [directiveEqBool] at h
      | «include» rightValue =>
          intro h
          have hvalue : leftValue = rightValue := inputValueEqBool_eq h
          cases hvalue
          rfl

theorem directiveListEqBool_eq
    : ∀ {left right : List DirectiveApplication},
        directiveListEqBool left right = true -> left = right
  | [], [], _h => rfl
  | left :: lefts, right :: rights, h => by
      simp [directiveListEqBool] at h
      rcases h with ⟨hhead, htail⟩
      cases directiveEqBool_eq hhead
      cases directiveListEqBool_eq htail
      rfl
  | [], _ :: _, h => by simp [directiveListEqBool] at h
  | _ :: _, [], h => by simp [directiveListEqBool] at h

mutual
  theorem selectionEqBool_self (selection : Selection)
      : selectionEqBool selection selection = true := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        simp [selectionEqBool, argumentListEqBool_self,
          directiveListEqBool_self, selectionSetEqBool_self]
    | inlineFragment typeCondition directives selectionSet =>
        simp [selectionEqBool, directiveListEqBool_self,
          selectionSetEqBool_self]

  theorem selectionSetEqBool_self
      : ∀ selectionSet : List Selection,
          selectionSetEqBool selectionSet selectionSet = true
    | [] => rfl
    | selection :: selectionSet => by
        simp [selectionSetEqBool, selectionEqBool_self,
          selectionSetEqBool_self selectionSet]
end

mutual
  theorem selectionEqBool_eq {left right : Selection}
      : selectionEqBool left right = true -> left = right := by
    cases left with
    | field leftResponse leftName leftArguments leftDirectives leftSelections =>
        cases right with
        | field rightResponse rightName rightArguments rightDirectives rightSelections =>
            intro h
            have hresponse : leftResponse = rightResponse := by
              by_cases heq : leftResponse = rightResponse
              · exact heq
              · have hfalse : (leftResponse == rightResponse) = false := by
                  simpa [beq_eq_false_iff_ne] using heq
                simp [selectionEqBool, hfalse] at h
            have hname : leftName = rightName := by
              by_cases heq : leftName = rightName
              · exact heq
              · have hfalse : (leftName == rightName) = false := by
                  simpa [beq_eq_false_iff_ne] using heq
                simp [selectionEqBool, hresponse, hfalse] at h
            have harguments : argumentListEqBool leftArguments rightArguments = true := by
              cases hargs : argumentListEqBool leftArguments rightArguments
              · simp [selectionEqBool, hresponse, hname, hargs] at h
              · rfl
            have hdirectives :
                directiveListEqBool leftDirectives rightDirectives = true := by
              cases hdirs : directiveListEqBool leftDirectives rightDirectives
              · simp [selectionEqBool, hresponse, hname, harguments, hdirs] at h
              · rfl
            have hselections :
                selectionSetEqBool leftSelections rightSelections = true := by
              cases hsels : selectionSetEqBool leftSelections rightSelections
              · simp [selectionEqBool, hresponse, hname, harguments,
                  hdirectives, hsels] at h
              · rfl
            have hargumentsEq : leftArguments = rightArguments :=
              argumentListEqBool_eq harguments
            have hdirectivesEq : leftDirectives = rightDirectives :=
              directiveListEqBool_eq hdirectives
            have hselectionsEq : leftSelections = rightSelections :=
              selectionSetEqBool_eq hselections
            subst rightResponse
            subst rightName
            subst rightArguments
            subst rightDirectives
            subst rightSelections
            rfl
        | inlineFragment rightType rightDirectives rightSelections =>
            intro h
            simp only [selectionEqBool] at h
            nomatch h
    | inlineFragment leftType leftDirectives leftSelections =>
        cases right with
        | field rightResponse rightName rightArguments rightDirectives rightSelections =>
            intro h
            simp only [selectionEqBool] at h
            nomatch h
        | inlineFragment rightType rightDirectives rightSelections =>
            intro h
            have htype : leftType = rightType := by
              by_cases heq : leftType = rightType
              · exact heq
              · have hfalse : (leftType == rightType) = false := by
                  simpa [beq_eq_false_iff_ne] using heq
                simp [selectionEqBool, hfalse] at h
            have hdirectives :
                directiveListEqBool leftDirectives rightDirectives = true := by
              cases hdirs : directiveListEqBool leftDirectives rightDirectives
              · simp [selectionEqBool, htype, hdirs] at h
              · rfl
            have hselections :
                selectionSetEqBool leftSelections rightSelections = true := by
              cases hsels : selectionSetEqBool leftSelections rightSelections
              · simp [selectionEqBool, htype, hdirectives, hsels] at h
              · rfl
            have hdirectivesEq : leftDirectives = rightDirectives :=
              directiveListEqBool_eq hdirectives
            have hselectionsEq : leftSelections = rightSelections :=
              selectionSetEqBool_eq hselections
            subst rightType
            subst rightDirectives
            subst rightSelections
            rfl

  theorem selectionSetEqBool_eq
      : ∀ {left right : List Selection},
          selectionSetEqBool left right = true -> left = right
    | [], [], _h => rfl
    | left :: lefts, right :: rights, h => by
        simp [selectionSetEqBool] at h
        rcases h with ⟨hhead, htail⟩
        cases selectionEqBool_eq hhead
        cases selectionSetEqBool_eq htail
        rfl
    | [], _ :: _, h => by simp [selectionSetEqBool] at h
    | _ :: _, [], h => by simp [selectionSetEqBool] at h
end

end Algorithms

end GraphQL
