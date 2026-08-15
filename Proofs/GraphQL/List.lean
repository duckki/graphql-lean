/-! Generic list facts used by GraphQL proof modules. -/

namespace List.Perm

theorem flatMap {α β : Type}
    {left right : List α} (hperm : left.Perm right) (transform : α -> List β)
    : (left.flatMap transform).Perm (right.flatMap transform) := by
  induction hperm with
  | nil => exact List.Perm.refl []
  | cons head _tail ih =>
      simpa only [List.flatMap_cons] using ih.append_left (transform head)
  | swap first second rest =>
      simp only [List.flatMap_cons]
      simpa [List.append_assoc] using
        (List.perm_append_comm
          (l₁ := transform second) (l₂ := transform first)).append_right
            (rest.flatMap transform)
  | trans _ _ ihleft ihright => exact ihleft.trans ihright

end List.Perm
