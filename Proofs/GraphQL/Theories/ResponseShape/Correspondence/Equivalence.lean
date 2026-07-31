import GraphQL.Theories.ResponseShape.Correspondence
import Proofs.GraphQL.Argument
import Proofs.GraphQL.Theories.ResponseShape.Validity

/-! Executable decision procedures and algebra for semantic response paths. -/

namespace GraphQL

namespace ResponseShape

/-- The executable path-step check decides semantic path-step equivalence. -/
@[simp]
theorem PathStep.semanticallyEquivalentBool_iff (left right : PathStep)
    : left.semanticallyEquivalentBool right = true
      ↔ left.SemanticallyEquivalent right := by
  simp [PathStep.semanticallyEquivalentBool,
    PathStep.SemanticallyEquivalent, argumentsEquivalentBool_iff]

/-- The executable path check decides pointwise semantic path equivalence. -/
@[simp]
theorem pathsSemanticallyEquivalentBool_iff
    : ∀ left right : List PathStep,
        pathsSemanticallyEquivalentBool left right = true
        ↔ PathsSemanticallyEquivalent left right
  | [], [] => by
      simp [pathsSemanticallyEquivalentBool, PathsSemanticallyEquivalent]
  | left :: leftRest, right :: rightRest => by
      simp only [pathsSemanticallyEquivalentBool,
        PathsSemanticallyEquivalent, Bool.and_eq_true]
      exact and_congr
        (PathStep.semanticallyEquivalentBool_iff left right)
        (pathsSemanticallyEquivalentBool_iff leftRest rightRest)
  | [], _right :: _rightRest => by
      simp [pathsSemanticallyEquivalentBool, PathsSemanticallyEquivalent]
  | _left :: _leftRest, [] => by
      simp [pathsSemanticallyEquivalentBool, PathsSemanticallyEquivalent]

/-- Semantic path-step equivalence has an executable decision procedure. -/
instance PathStep.instDecidableSemanticallyEquivalent (left right : PathStep)
    : Decidable (left.SemanticallyEquivalent right) :=
  decidable_of_iff (left.semanticallyEquivalentBool right = true)
    (PathStep.semanticallyEquivalentBool_iff left right)

/-- Pointwise semantic path equivalence has an executable decision procedure. -/
instance instDecidablePathsSemanticallyEquivalent (left right : List PathStep)
    : Decidable (PathsSemanticallyEquivalent left right) :=
  decidable_of_iff (pathsSemanticallyEquivalentBool left right = true)
    (pathsSemanticallyEquivalentBool_iff left right)

/-- Every concrete path step is semantically equivalent to itself. -/
theorem pathStep_semanticallyEquivalent_refl (step : PathStep)
    : step.SemanticallyEquivalent step := by
  exact ⟨rfl, rfl, rfl,
    Argument.argumentsEquivalent_refl step.field.arguments,
    rfl⟩

/-- Semantic path-step equivalence is symmetric. -/
theorem pathStep_semanticallyEquivalent_symm
    {left right : PathStep}
    (h : left.SemanticallyEquivalent right)
    : right.SemanticallyEquivalent left := by
  rcases h with
    ⟨hparent, hresponse, hfield, harguments, houtput⟩
  exact ⟨hparent.symm, hresponse.symm, hfield.symm,
    Argument.argumentsEquivalent_symm harguments, houtput.symm⟩

/-- Semantic path-step equivalence is transitive. -/
theorem pathStep_semanticallyEquivalent_trans
    {left middle right : PathStep}
    (hleft : left.SemanticallyEquivalent middle)
    (hright : middle.SemanticallyEquivalent right)
    : left.SemanticallyEquivalent right := by
  rcases hleft with
    ⟨hleftParent, hleftResponse, hleftField, hleftArguments, hleftOutput⟩
  rcases hright with
    ⟨hrightParent, hrightResponse, hrightField, hrightArguments,
      hrightOutput⟩
  exact ⟨hleftParent.trans hrightParent,
    hleftResponse.trans hrightResponse,
    hleftField.trans hrightField,
    Argument.argumentsEquivalent_trans hleftArguments hrightArguments,
    hleftOutput.trans hrightOutput⟩

/-- Semantic path equivalence is reflexive. -/
theorem pathsSemanticallyEquivalent_refl
    : ∀ path : List PathStep, PathsSemanticallyEquivalent path path
  | [] => by
      simp [PathsSemanticallyEquivalent]
  | step :: rest => by
      exact ⟨pathStep_semanticallyEquivalent_refl step,
        pathsSemanticallyEquivalent_refl rest⟩

/-- Semantic path equivalence is symmetric. -/
theorem pathsSemanticallyEquivalent_symm
    {left right : List PathStep}
    (h : PathsSemanticallyEquivalent left right)
    : PathsSemanticallyEquivalent right left := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => trivial
      | cons _right _rightRest => exact False.elim h
  | cons left leftRest ih =>
      cases right with
      | nil => exact False.elim h
      | cons right rightRest =>
          exact ⟨pathStep_semanticallyEquivalent_symm h.1, ih h.2⟩

/-- Semantic path equivalence is transitive. -/
theorem pathsSemanticallyEquivalent_trans
    {left middle right : List PathStep}
    (hleft : PathsSemanticallyEquivalent left middle)
    (hright : PathsSemanticallyEquivalent middle right)
    : PathsSemanticallyEquivalent left right := by
  induction left generalizing middle right with
  | nil =>
      cases middle with
      | nil =>
          cases right with
          | nil => trivial
          | cons _right _rightRest => exact False.elim hright
      | cons _middle _middleRest => exact False.elim hleft
  | cons left leftRest ih =>
      cases middle with
      | nil => exact False.elim hleft
      | cons middle middleRest =>
          cases right with
          | nil => exact False.elim hright
          | cons right rightRest =>
              exact ⟨pathStep_semanticallyEquivalent_trans hleft.1 hright.1,
                ih hleft.2 hright.2⟩

end ResponseShape

end GraphQL
