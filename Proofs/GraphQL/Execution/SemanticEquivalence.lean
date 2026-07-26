import GraphQL.Execution

/-! General laws for response equivalence modulo object-field ordering. -/

namespace GraphQL
namespace Execution

namespace ResponseValue

theorem semanticEquivalent_refl (value : ResponseValue)
    : semanticEquivalent value value := by
  rfl

theorem semanticEquivalent_symm {left right : ResponseValue}
    : semanticEquivalent left right -> semanticEquivalent right left := by
  exact Eq.symm

theorem semanticEquivalent_trans {left middle right : ResponseValue}
    : semanticEquivalent left middle
      -> semanticEquivalent middle right
      -> semanticEquivalent left right := by
  exact Eq.trans

theorem semanticEquivalent_of_eq {left right : ResponseValue}
    : left = right -> semanticEquivalent left right := by
  intro heq
  subst right
  rfl

end ResponseValue

namespace Response

theorem semanticEquivalent_refl (response : Response)
    : semanticEquivalent response response := by
  exact ⟨ResponseValue.semanticEquivalent_refl response.data, rfl⟩

theorem semanticEquivalent_symm {left right : Response}
    : semanticEquivalent left right -> semanticEquivalent right left := by
  intro hequivalent
  exact ⟨ResponseValue.semanticEquivalent_symm hequivalent.1,
    hequivalent.2.symm⟩

theorem semanticEquivalent_trans {left middle right : Response}
    : semanticEquivalent left middle
      -> semanticEquivalent middle right
      -> semanticEquivalent left right := by
  intro hleft hright
  exact ⟨ResponseValue.semanticEquivalent_trans hleft.1 hright.1,
    hleft.2.trans hright.2⟩

theorem semanticEquivalent_of_eq {left right : Response}
    : left = right -> semanticEquivalent left right := by
  intro heq
  subst right
  exact semanticEquivalent_refl left

end Response

end Execution
end GraphQL
